import csv
import json
import math
import os
import random
import re
import tempfile
import time
from dataclasses import asdict, dataclass, fields
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from typing import Dict, List, Optional, Tuple

import requests
from bs4 import BeautifulSoup


BASE = "https://kolesa.kz"
MOTO_PATH = "/mototehnika/mototsikly"

# Город -> slug в URL kolesa.kz (аналогично krisha_parser.py; требует проверки при нестандартных городах)
CITIES = {
    "\u0410\u043b\u043c\u0430\u0442\u044b": "almaty",
    "\u0410\u0441\u0442\u0430\u043d\u0430": "astana",
    "\u0428\u044b\u043c\u043a\u0435\u043d\u0442": "shymkent",
    "\u0410\u043a\u0442\u043e\u0431\u0435": "aktobe",
    "\u041a\u0430\u0440\u0430\u0433\u0430\u043d\u0434\u0430": "karaganda",
    "\u0422\u0430\u0440\u0430\u0437": "taraz",
    "\u0410\u0442\u044b\u0440\u0430\u0443": "atyrau",
    "\u0423\u0441\u0442\u044c-\u041a\u0430\u043c\u0435\u043d\u043e\u0433\u043e\u0440\u0441\u043a": "ust-kamenogorsk",
    "\u041f\u0430\u0432\u043b\u043e\u0434\u0430\u0440": "pavlodar",
    "\u041a\u044b\u0437\u044b\u043b\u043e\u0440\u0434\u0430": "kyzylorda",
    "\u0421\u0435\u043c\u0435\u0439": "semei",
    "\u041a\u043e\u0441\u0442\u0430\u043d\u0430\u0439": "kostanai",
    "\u041a\u043e\u043a\u0448\u0435\u0442\u0430\u0443": "kokshetau",
    "\u0410\u043a\u0442\u0430\u0443": "aktau",
    "\u0423\u0440\u0430\u043b\u044c\u0441\u043a": "uralsk",
    "\u041f\u0435\u0442\u0440\u043e\u043f\u0430\u0432\u043b\u043e\u0432\u0441\u043a": "petropavlovsk",
    "\u0422\u0443\u0440\u043a\u0435\u0441\u0442\u0430\u043d": "turkestan",
    "\u0422\u0430\u043b\u0434\u044b\u043a\u043e\u0440\u0433\u0430\u043d": "taldykorgan",
    "\u042d\u043a\u0438\u0431\u0430\u0441\u0442\u0443\u0437": "ekibastuz",
    "\u0420\u0438\u0434\u0434\u0435\u0440": "ridder",
    "\u0420\u0443\u0434\u043d\u044b\u0439": "rudnyi",
}


@dataclass
class MotoRow:
    """Строка итоговой CSV-таблицы для объявления о продаже мотоцикла."""

    city: str = ""
    title: Optional[str] = None
    brand: Optional[str] = None
    model: Optional[str] = None
    year: Optional[int] = None
    price: Optional[int] = None
    price_text: Optional[str] = None
    moto_type: Optional[str] = None
    engine_cc: Optional[int] = None
    mileage_km: Optional[int] = None
    condition: Optional[str] = None
    color: Optional[str] = None
    customs_cleared: Optional[str] = None
    transmission: Optional[str] = None
    drive_type: Optional[str] = None
    owner: Optional[str] = None
    url: Optional[str] = None
    description: Optional[str] = None


class AccessBlocked(RuntimeError):
    """Ограничение доступа / антибот-проверка со стороны сайта."""

    def __init__(self, message: str, stop_run: bool = False):
        super().__init__(message)
        self.stop_run = stop_run


@dataclass(frozen=True)
class DelayPolicy:
    """Адаптивные паузы между HTTP-запросами."""

    initial_delay: float = 30.0
    min_delay: float = 15.0
    max_delay: float = 180.0
    success_window: int = 8

    def __post_init__(self):
        delays = (self.min_delay, self.initial_delay, self.max_delay)
        if (
            not all(math.isfinite(v) for v in delays)
            or not 0 < self.min_delay <= self.initial_delay <= self.max_delay
            or not isinstance(self.success_window, int)
            or self.success_window < 1
        ):
            raise ValueError("Нужны 0 < min_delay <= initial_delay <= max_delay и success_window >= 1")


class KolesaSession(requests.Session):
    """HTTP-сессия с паузами между запросами и замедлением при ошибках."""

    def __init__(
        self,
        delay_range: Optional[Tuple[float, float]] = None,
        delay_policy: Optional[DelayPolicy] = None,
    ):
        super().__init__()
        if delay_range is not None and delay_policy is not None:
            raise ValueError("Выберите delay_range или delay_policy")
        if delay_range is not None and (
            not all(math.isfinite(v) for v in delay_range)
            or not 0 <= delay_range[0] <= delay_range[1]
        ):
            raise ValueError("Нужны паузы 0 <= минимум <= максимум")
        self.delay_range = delay_range
        self.delay_policy = delay_policy or DelayPolicy()
        self.current_delay = delay_range[1] if delay_range is not None else self.delay_policy.initial_delay
        self.success_streak = 0
        self.next_request_at = 0.0
        self.block_retries_used = 0

    def slow_down(self):
        self.success_streak = 0
        if self.delay_range is None:
            self.current_delay = min(self.delay_policy.max_delay, self.current_delay * 2)

    def record_success(self):
        if self.delay_range is None:
            self.success_streak += 1
            if self.success_streak >= self.delay_policy.success_window:
                self.current_delay = max(self.delay_policy.min_delay, self.current_delay * 0.8)
                self.success_streak = 0

    def request(self, *args, **kwargs):
        time.sleep(max(0.0, self.next_request_at - time.monotonic()))
        server_wait = 0.0
        try:
            response = super().request(*args, **kwargs)
            server_wait = retry_after_seconds(response)
            if (
                response.status_code in (403, 418, 429, 468)
                or response.status_code >= 500
                or "/.safeline/" in response.text.lower()
                or server_wait > 0
            ):
                self.slow_down()
            elif 200 <= response.status_code < 300:
                self.record_success()
            else:
                self.success_streak = 0
            return response
        except requests.RequestException:
            # Keep the configured polite interval, but do not multiply it on
            # every timeout/connection failure. fetch_html owns the retry policy.
            self.success_streak = 0
            raise
        finally:
            delay = random.uniform(*self.delay_range) if self.delay_range is not None else self.current_delay
            self.next_request_at = time.monotonic() + max(delay, server_wait)


def make_session(
    delay_range: Optional[Tuple[float, float]] = None,
    delay_policy: Optional[DelayPolicy] = None,
) -> requests.Session:
    """Создаёт настроенную сессию для вежливого сбора страниц."""
    s = KolesaSession(delay_range, delay_policy)
    s.headers.update(
        {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0 Safari/537.36"
            ),
            "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Connection": "keep-alive",
        }
    )
    return s


def retry_after_seconds(response) -> float:
    """Разбирает заголовок Retry-After (число секунд или дату)."""
    value = response.headers.get("Retry-After", "")
    try:
        return max(0.0, float(value))
    except ValueError:
        try:
            dt = parsedate_to_datetime(value)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return max(0.0, (dt - datetime.now(timezone.utc)).total_seconds())
        except (ValueError, TypeError, OverflowError):
            return 0.0


def fetch_html(
    session: requests.Session,
    url: str,
    retries: int = 2,
    block_pause: float = 60.0,
    retry_blocked: bool = False,
) -> str:
    """Загружает HTML по URL; останавливается при 403/429/468 или антибот-странице."""
    if retries < 1 or block_pause < 0:
        raise ValueError("retries >= 1, block_pause >= 0")
    last_err = None
    for attempt in range(1, retries + 1):
        retry_wait = 0.0
        try:
            r = session.get(url, timeout=25)
        except requests.exceptions.ProxyError as e:
            raise RuntimeError(
                f"Proxy connection failed for {url}; check HTTP_PROXY/HTTPS_PROXY settings: {e}"
            ) from e
        except requests.RequestException as e:
            last_err = e
        else:
            blocked = r.status_code in (403, 418, 429, 468) or "/.safeline/" in r.text.lower()
            if blocked:
                retry_after = retry_after_seconds(r)
                if (
                    not retry_blocked
                    or getattr(session, "block_retries_used", 0) >= 1
                    or attempt == retries
                    or retry_after > block_pause
                ):
                    suffix = f"; Retry-After: {retry_after:.0f} с" if retry_after else ""
                    raise AccessBlocked(
                        f"HTTP {r.status_code}, проверка/ограничение доступа{suffix}: {url}",
                        stop_run=retry_after > block_pause,
                    )
                session.block_retries_used = 1
                time.sleep(block_pause)
                continue
            if r.status_code not in (500, 502, 503, 504):
                r.raise_for_status()
                return r.text
            last_err = RuntimeError(f"HTTP {r.status_code}: {url}")
            retry_wait = retry_after_seconds(r)
            if retry_wait > block_pause:
                raise AccessBlocked(f"HTTP {r.status_code}: сервер просит отложить сбор: {url}", stop_run=True)
        if attempt < retries:
            time.sleep(max(retry_wait, getattr(session, "current_delay", 10.0 * attempt)))
    raise RuntimeError(f"Не удалось загрузить {url}. Последняя ошибка: {last_err}") from last_err


def resolve_city(city: str) -> Tuple[str, str]:
    """Возвращает (читаемое имя города, slug для URL)."""
    slug = CITIES.get(city, city)
    if slug not in CITIES.values():
        raise ValueError(f"Неизвестный город {city!r}. Доступны: {', '.join(CITIES)}")
    city_name = next(name for name, value in CITIES.items() if value == slug)
    return city_name, slug


def build_listing_url(slug: str, page: int) -> str:
    """Формирует URL страницы выдачи мотоциклов по городу."""
    return f"{BASE}{MOTO_PATH}/{slug}/?page={page}"


def normalize_ad_url(href: str) -> str:
    """Приводит относительную ссылку объявления к полному URL без query-хвоста."""
    if href.startswith("//"):
        href = "https:" + href
    if href.startswith("/"):
        href = BASE + href
    return href.split("?")[0]


def clean_text(text: str) -> str:
    """Сжимает лишние пробелы и переносы строк."""
    return re.sub(r"\s+", " ", text).strip()


def extract_listing_rows(list_html: str, city: str = "") -> List[MotoRow]:
    """Parse every ordinary or VIP motorcycle card from one search-results page."""
    soup = BeautifulSoup(list_html, "html.parser")
    cards = soup.select(".a-card, .vip-card")
    if not cards:
        raise NotImplementedError("Listing cards were not found; the page markup may have changed.")

    def text(node) -> str:
        return clean_text(node.get_text(" ", strip=True)) if node else ""

    def integer(value: str) -> Optional[int]:
        digits = re.sub(r"\D", "", value or "")
        return int(digits) if digits else None

    rows: List[MotoRow] = []
    seen = set()
    for card in cards:
        link = card.select_one('a[href*="/a/show/"]')
        href = link.get("href") if link else None
        if not href:
            continue
        url = normalize_ad_url(href)
        if not re.fullmatch(r"https://kolesa\.kz/a/show/\d+", url) or url in seen:
            continue
        seen.add(url)

        title = text(card.select_one('[data-test="advert-title"] a, .a-card__title a, .vip-card__link, .vip-card__title a')) or None
        description = text(card.select_one(
            '[data-test="advert-description"], .a-card__description, .vip-card__description'
        )) or None
        price_text = text(card.select_one(
            '[data-test="a-card-price"], .a-card__price, .vip-card__price'
        )) or None
        region = text(card.select_one(
            '[data-test="region"], .a-card__param[data-test="region"], .vip-card__region'
        )) or city
        condition = text(card.select_one('[data-test="label-text"], .vip-card__label')) or None

        year_match = re.search(r"\b(19\d{2}|20\d{2})\s*(?:\u0433\.?|year)?\b", description or "", re.I)
        cc_match = re.search(
            r"\b(\d{2,4})\s*(?:\u0441\u043c(?:\u00b3|3|\^3))\b", description or "", re.I
        )
        mileage_match = re.search(
            r"\b([\d\s.,]+)\s*(?:\u0442\u044b\u0441\.?\s*)?\u043a\u043c\b",
            description or "", re.I
        )
        mileage = None
        if mileage_match:
            raw = mileage_match.group(1).replace(" ", "").replace(",", ".")
            try:
                factor = 1000 if re.search(r"\u0442\u044b\u0441", mileage_match.group(0), re.I) else 1
                mileage = int(float(raw) * factor)
            except ValueError:
                pass

        rows.append(MotoRow(
            city=region or "",
            title=title,
            brand=title.split()[0] if title else None,
            model=None,
            year=int(year_match.group(1)) if year_match else None,
            price=integer(price_text),
            price_text=price_text,
            moto_type="\u041c\u043e\u0442\u043e\u0446\u0438\u043a\u043b",
            engine_cc=int(cc_match.group(1)) if cc_match else None,
            mileage_km=mileage,
            condition=condition,
            url=url,
            description=description,
        ))
    return rows


def extract_listing_urls(list_html: str) -> List[str]:
    """Return unique ad URLs from listing cards."""
    return [row.url for row in extract_listing_rows(list_html) if row.url]


def extract_last_page(list_html: str) -> Optional[int]:
    """Read the last numbered page from pagination links, if present."""
    soup = BeautifulSoup(list_html, "html.parser")
    pages = []
    for link in soup.select('a[href*="page="]'):
        match = re.search(r"[?&]page=(\d+)", link.get("href", ""))
        if match:
            pages.append(int(match.group(1)))
    return max(pages) if pages else None


def parse_advert_page(page_html: str, url: str, city: str = "") -> MotoRow:
    """Разбирает страницу одного объявления о мотоцикле в MotoRow.

    Парсит реальные поля карточки объявления; отсутствующие на странице характеристики
    остаются пустыми, чтобы не подменять факты догадками.
    """
    soup = BeautifulSoup(page_html, "html.parser")
    if soup.select_one(".offer__error, .error-page") or not soup.select_one(".offer"):
        raise ValueError("Не найдена карточка объявления .offer (возможно, сохранена страница ошибки)")

    def text(selector: str) -> str:
        node = soup.select_one(selector)
        return clean_text(node.get_text(" ", strip=True)) if node else ""

    def number(value: str) -> Optional[int]:
        digits = re.sub(r"\D", "", value or "")
        return int(digits) if digits else None

    title = text(".offer__title, h1") or None
    price_text = text(".offer__price") or None
    price = number(price_text)
    year_match = re.search(r"\b(19\d{2}|20\d{2})\s*(?:г\.?|год)?\b", title or "")
    year = int(year_match.group(1)) if year_match else None

    # Марка берётся из хлебных крошек, если она указана; иначе — из заголовка.
    crumbs = [clean_text(x.get_text(" ", strip=True)) for x in soup.select(".breadcrumbs a")]
    brand = None
    for crumb in reversed(crumbs):
        if crumb.lower().startswith("мотоциклы ") and crumb.lower() != "мотоциклы":
            brand = crumb.split(" ", 1)[1].split(" " + chr(0x0432) + " ", 1)[0].strip()
            break
    if not brand and title:
        brand = title.split()[0]
    model = title
    if model and brand:
        model = re.sub(r"^" + re.escape(brand) + r"\s*", "", model, flags=re.I)
        model = re.sub(r"\s*\b(?:19\d{2}|20\d{2})\s*(?:г\.?|год)?\b.*$", "", model).strip() or None

    specs = {}
    for dl in soup.select(".offer__parameters dl"):
        dt, dd = dl.select_one("dt"), dl.select_one("dd")
        if dt and dd:
            specs[clean_text(dt.get_text(" ", strip=True)).rstrip(":").lower()] = clean_text(dd.get_text(" ", strip=True))
    status = text(".offer__parameters-mortgaged") or None
    description = text("[data-test='description-text'], .a-description__text") or None
    city_value = specs.get("город", "")
    detected_city = city_value.split(",")[0].strip() if city_value else city
    # Данные о моторе/пробеге иногда присутствуют только в тексте продавца.
    haystack = " ".join(x for x in (title or "", description or "") if x)
    cc_match = re.search(r"\b(\d{2,4})\s*(?:см(?:³|3|\^3)|куб(?:ов|\.?)?)\b", haystack, re.I)
    mileage_match = re.search(r"\b([\d\s.,]+)\s*(?:тыс\.?\s*)?км\b", haystack, re.I)
    mileage = None
    if mileage_match:
        raw = mileage_match.group(1).replace(" ", "").replace(",", ".")
        try:
            mileage = int(float(raw) * (1000 if "тыс" in mileage_match.group(0).lower() else 1))
        except ValueError:
            pass

    return MotoRow(
        city=detected_city or "", title=title, brand=brand, model=model, year=year,
        price=price, price_text=price_text, moto_type=specs.get("тип техники") or None,
        engine_cc=int(cc_match.group(1)) if cc_match else None, mileage_km=mileage,
        condition=status, color=specs.get("цвет") or None,
        customs_cleared=specs.get("растаможен") or specs.get("растаможка") or None,
        transmission=specs.get("коробка передач") or None,
        drive_type=specs.get("привод") or None, url=normalize_ad_url(url), description=description,
    )


def append_rows_to_csv(csv_path: str, rows: List[MotoRow]) -> None:
    """Дописывает строки MotoRow в CSV, проверяя соответствие столбцов."""
    fieldnames = [field.name for field in fields(MotoRow)]
    file_exists = os.path.exists(csv_path) and os.path.getsize(csv_path) > 0
    if file_exists:
        with open(csv_path, newline="", encoding="utf-8-sig") as f:
            if next(csv.reader(f), []) != fieldnames:
                raise ValueError("CSV имеет другой набор столбцов: выберите новый csv_path")
    with open(csv_path, "a", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        if not file_exists:
            writer.writeheader()
        writer.writerows(asdict(row) for row in rows)


def load_seen_urls(csv_path: str) -> set:
    """Читает уже сохранённые URL из CSV, чтобы пропускать их при повторном запуске."""
    if not os.path.exists(csv_path):
        return set()
    with open(csv_path, newline="", encoding="utf-8-sig") as f:
        return {row["url"] for row in csv.DictReader(f) if row.get("url")}


def load_pending(path: str) -> Dict[str, str]:
    """Загружает очередь отложенных URL объявлений."""
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as f:
        entries = json.load(f)
    pending = {}
    for item in entries:
        url = item["url"]
        if not re.fullmatch(r"https://kolesa\.kz/a/show/\d+", url):
            raise ValueError(f"Некорректный URL в очереди {path}")
        pending[url] = item.get("last_error", "")
    return pending


def save_pending(path: str, pending: Dict[str, str]) -> None:
    """Атомарно сохраняет очередь незавершённых URL."""
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            delete=False,
            dir=os.path.dirname(os.path.abspath(path)),
            prefix=".kolesa_pending_",
        ) as f:
            tmp_path = f.name
            json.dump(
                [{"url": url, "last_error": reason} for url, reason in pending.items()],
                f,
                ensure_ascii=False,
                indent=2,
            )
        os.replace(tmp_path, path)
    finally:
        if tmp_path and os.path.exists(tmp_path):
            os.unlink(tmp_path)


def parse_kolesa_moto(
    city: str,
    start_page: int = 1,
    end_page: int = 500,
    csv_path: Optional[str] = None,
    save_every: int = 10,
    max_empty_pages: int = 3,
    delay_range: Optional[Tuple[float, float]] = None,
    block_pause: float = 60.0,
    max_ads: Optional[int] = None,
    verbose: bool = False,
    delay_policy: Optional[DelayPolicy] = None,
    max_consecutive_blocks: int = 3,
) -> str:
    """Collect all listing cards for one city, saving available fields even when sparse."""
    city_name, slug = resolve_city(city)
    if (
        start_page < 1 or end_page < start_page or save_every < 1
        or max_empty_pages < 1 or block_pause < 0
        or max_consecutive_blocks < 1 or (max_ads is not None and max_ads < 1)
    ):
        raise ValueError("Check page range, limits, and delay settings.")

    csv_path = os.fspath(csv_path or os.path.join("data", f"kolesa_moto_{slug}.csv"))
    os.makedirs(os.path.dirname(os.path.abspath(csv_path)), exist_ok=True)
    append_rows_to_csv(csv_path, [])
    seen = {normalize_ad_url(url) for url in load_seen_urls(csv_path)}
    session = make_session(delay_range, delay_policy)
    total = skipped = errors = empty_in_row = 0
    status = "Page range processed"
    last_error = None

    try:
        page = start_page
        last_page = end_page
        while page <= last_page:
            list_url = build_listing_url(slug, page)
            if verbose:
                print(f"Loading listing page {page}: {list_url}", flush=True)
            try:
                list_html = fetch_html(session, list_url, block_pause=block_pause)
            except AccessBlocked as exc:
                status = f"Stopped by site access limit: {exc}"
                break
            except requests.HTTPError as exc:
                if exc.response is not None and exc.response.status_code == 404:
                    status = f"Reached end of listing at page {page}"
                    break
                errors += 1
                last_error = f"page {page}: {exc}"
                status = f"Stopped after HTTP error on listing page {page}"
                break
            except (requests.RequestException, RuntimeError) as exc:
                errors += 1
                last_error = f"page {page}: {exc}"
                status = f"Stopped after connection error on listing page {page}"
                break

            try:
                rows = extract_listing_rows(list_html, city=city_name)
            except NotImplementedError as exc:
                status = f"Could not recognize listing page: {exc}"
                break

            page_last = extract_last_page(list_html)
            if page_last is not None:
                last_page = min(last_page, max(page, page_last))

            if not rows:
                empty_in_row += 1
                if empty_in_row >= max_empty_pages:
                    status = f"Stopped after {max_empty_pages} empty pages"
                    break
            else:
                empty_in_row = 0
                new_rows = []
                for row in rows:
                    if row.url in seen:
                        skipped += 1
                        continue
                    if max_ads is not None and total + len(new_rows) >= max_ads:
                        break
                    new_rows.append(row)
                    seen.add(row.url)
                if new_rows:
                    append_rows_to_csv(csv_path, new_rows)
                    total += len(new_rows)

            if verbose:
                print(f"page {page}: saved {total}, skipped {skipped}, errors {errors}")
            if max_ads is not None and total >= max_ads:
                status = f"Reached limit of {max_ads} new listings"
                break
            if page >= last_page:
                break
            page += 1
    finally:
        session.close()

    details = f" Last error: {last_error}." if last_error else ""
    print(f"{status}. New listings: {total}, skipped: {skipped}, errors: {errors}. CSV: {csv_path}.{details}")
    return csv_path


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Kolesa.kz motorcycle listings to CSV")
    parser.add_argument("city", nargs="?", default="\u0410\u0441\u0442\u0430\u043d\u0430", help="city name or slug")
    parser.add_argument("--start-page", type=int, default=1)
    parser.add_argument("--end-page", type=int, default=500)
    parser.add_argument("--csv", dest="csv_path")
    parser.add_argument("--max-ads", type=int)
    args = parser.parse_args()
    parse_kolesa_moto(args.city, start_page=args.start_page, end_page=args.end_page,
                      csv_path=args.csv_path, max_ads=args.max_ads, verbose=True)

