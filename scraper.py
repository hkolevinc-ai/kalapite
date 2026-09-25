#!/usr/bin/env python3
"""Read kalapite.com and populate the supplied Temu workbook without rebuilding it."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import logging
import os
import re
import sys
import time
import unicodedata
from collections import OrderedDict, deque
from dataclasses import dataclass, field
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urljoin, urlsplit, urlunsplit
from zipfile import ZIP_DEFLATED, ZipFile

import requests
from bs4 import BeautifulSoup
from lxml import etree
from PIL import Image
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

LOG = logging.getLogger("kalapite")
BASE = "https://www.kalapite.com"
MAIN_NS = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
NS = "{" + MAIN_NS + "}"
CAPACITY = 5000
HEADER_ROW = 4
START_ROW = 5
BAD_CATEGORY = re.compile(
    r"оцветител|оксидни-бои|/добавки|консуматив|продукти-от-щампован-бетон|под-наем",
    re.I,
)
BAD_PRODUCT = re.compile(r"(лак за|пигмент|боя за|разредител|втвърдител|добавка за)", re.I)
NON_PRODUCT_TEXT = (
    "Стоки на обща стойност", "След като добавите продуктите", "Артикулът се изпраща",
)


def tidy(s: str) -> str:
    return re.sub(r"\s+", " ", s or "").strip()


def canonical(url: str) -> str:
    p = urlsplit(urljoin(BASE, url))
    path = quote(unquote(p.path), safe="/-._~")
    return urlunsplit(("https", "www.kalapite.com", path.rstrip("/") or "/", "", ""))


def money(raw: str) -> Decimal | None:
    m = re.search(r"(\d[\d\s.,]*)\s*€", tidy(raw))
    if not m:
        return None
    n = m.group(1).replace(" ", "").replace(",", ".")
    if n.count(".") > 1:
        n = n.replace(".", "", n.count(".") - 1)
    try:
        return Decimal(n)
    except InvalidOperation:
        return None


def amount(n: Decimal) -> str:
    return str(n.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def is_site_link(url: str) -> bool:
    return urlsplit(url).hostname in {"kalapite.com", "www.kalapite.com"}


def image_url(raw: str) -> str:
    """OpenCart uses /image/cache/...-500x500.jpg for thumbnails; use original."""
    url = canonical(raw)
    p = urlsplit(url)
    path = unquote(p.path).replace("/image/cache/", "/image/", 1)
    path = re.sub(r"-\d+x\d+(?=\.[a-zA-Z]{3,5}$)", "", path)
    return urlunsplit((p.scheme, p.netloc, quote(path, safe="/-._~"), "", ""))


def category_for(url: str, name: str = "") -> str | None:
    p = unquote(urlsplit(url).path).lower()
    title = name.lower()
    if BAD_CATEGORY.search(p) or BAD_PRODUCT.search(title):
        return None
    if "инструменти-за-щампован-бетон" in p:
        return "15539"
    if any(x in p for x in ("тротоарни-настилки", "калъпи-за-градински-пътеки", "бордюри", "капаци-за-зид-и-колони", "калъпи-от-авс")):
        return "24795"
    if any(x in p for x in ("стенни-облицовки", "балюстри", "калъпи-от-гума", "щампи-за-под", "щампи-за-стена", "калъпи-от-стъклопласт")):
        return "39761"
    # Broad parent categories may contain non-molds; classify via detail text later.
    if "калъпи-и-добавки" in p or "щампи-и-консумативи" in p:
        return "39761" if re.search(r"калъп|щамп", title) else None
    return None


class Client:
    def __init__(self, delay: float):
        self.delay = delay
        self.last = 0.0
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "Mozilla/5.0 (compatible; catalog-import/1.0; +https://www.kalapite.com/)",
            "Accept-Language": "bg-BG,bg;q=0.9,en;q=0.7",
        })
        retry = Retry(total=3, backoff_factor=1.5, status_forcelist=[429, 500, 502, 503, 504])
        self.session.mount("https://", HTTPAdapter(max_retries=retry))

    def get(self, url: str) -> BeautifulSoup:
        wait = self.delay - (time.monotonic() - self.last)
        if wait > 0:
            time.sleep(wait)
        r = self.session.get(url, timeout=(12, 35))
        self.last = time.monotonic()
        r.raise_for_status()
        return BeautifulSoup(r.content, "html.parser")

    def image_info(self, url: str) -> tuple[int, int, int]:
        with self.session.get(url, timeout=(8, 20), stream=True) as r:
            r.raise_for_status()
            if not r.headers.get("content-type", "").lower().startswith("image/"):
                raise ValueError("URL does not return an image")
            content = bytearray()
            for block in r.iter_content(chunk_size=32768):
                content.extend(block)
                if len(content) > 3_200_000:
                    raise ValueError("Image exceeds 3 MB")
            with Image.open(io.BytesIO(content)) as im:
                width, height = im.size
            return width, height, len(content)


def discover(client: Client, issues: list[dict], max_products: int) -> OrderedDict[str, str]:
    soup = client.get(BASE + "/information/sitemap")
    title = next((x for x in soup.select(".tb_sitemap h2") if "Категории" in x.get_text()), None)
    if not title:
        raise RuntimeError("Категориите липсват от картата на сайта; спрете, вместо да върнете празен файл")
    sitemap_list = title.find_next("ul")
    seeds = []
    for a in sitemap_list.select('a[href]'):
        href = unquote(a["href"])
        if "/продукти/" not in href:
            continue
        if BAD_CATEGORY.search(href):
            issues.append(issue("EXCLUDED_CATEGORY", canonical(a["href"]),
                                "Няма подходяща категория в приложен Temu шаблон"))
            continue
        seeds.append(canonical(a["href"]))
    if not seeds:
        raise RuntimeError("Не бяха намерени категории с продукти")
    queue = deque(dict.fromkeys(seeds))
    seen_pages: set[str] = set()
    found: OrderedDict[str, str] = OrderedDict()
    while queue:
        current = queue.popleft()
        if current in seen_pages or len(seen_pages) >= 350:
            continue
        seen_pages.add(current)
        try:
            page = client.get(current)
        except requests.RequestException as exc:
            issues.append(issue("CATEGORY_ERROR", current, str(exc)))
            continue
        # Child categories in the main content, plus newly discovered descendants.
        content = page.select_one("#content") or page.select_one("main") or page
        prefix = unquote(urlsplit(current).path).rstrip("/") + "/"
        for a in content.select("h3 a[href]"):
            link = canonical(a["href"])
            if unquote(urlsplit(link).path).startswith(prefix) and not BAD_CATEGORY.search(unquote(link)):
                queue.append(link)
        for card in content.select(".product-thumb"):
            a = card.select_one("h4 a[href]")
            if a and is_site_link(a["href"]):
                link = canonical(a["href"])
                if link not in found:
                    found[link] = current
        for a in content.select(".pagination a[href]"):
            link = canonical(a["href"])
            # canonical() intentionally removes query strings; keep pagination query explicitly.
            parts = urlsplit(a["href"])
            page_num = parse_qs(parts.query).get("page", [""])[0]
            if page_num.isdecimal() and 1 < int(page_num) <= 100:
                queue.append(link + "?page=" + page_num)
        LOG.info("category %d | products %d | %s", len(seen_pages), len(found), current)
        if max_products and len(found) >= max_products:
            break
    if not found:
        raise RuntimeError("Категориите са прочетени, но не са намерени продуктови карти")
    return found


@dataclass
class Product:
    url: str
    source_category: str
    category: str
    title: str
    sku: str
    price: Decimal
    list_price: Decimal | None
    manufacturer: str
    description: str
    specs: dict[str, str]
    images: list[str]
    variants: list[tuple[str, str, Decimal]] = field(default_factory=list)


def parse_product(soup: BeautifulSoup, url: str, source_category: str) -> tuple[Product | None, str]:
    info = soup.select_one(".product-info")
    title_el = soup.select_one("h1")
    if info is None or title_el is None:
        return None, "Продуктовата страница няма очакваното съдържание"
    title = tidy(title_el.get_text(" ", strip=True))
    category = category_for(source_category, title)
    if not category:
        return None, "Извън категориите на този Temu шаблон"
    facts = {}
    for dl in info.select("dl"):
        for dt in dl.select("dt"):
            dd = dt.find_next_sibling("dd")
            if dd:
                facts[tidy(dt.get_text(" ", strip=True)).rstrip(":")] = tidy(dd.get_text(" ", strip=True))
    status = facts.get("Наличност", "")
    if status and "в наличност" not in status.lower():
        return None, "Не е в наличност: " + status
    if not status:
        return None, "Не е обявена наличност"
    sku = facts.get("Код на продукта", "")
    if not sku:
        return None, "Липсва код на продукта"
    regular = info.select_one(".price-new") or info.select_one(".price-regular")
    price = money(regular.get_text(" ", strip=True)) if regular else None
    if price is None or price <= 0:
        return None, "Липсва валидна цена в EUR"
    old = info.select_one(".price-old")
    list_price = money(old.get_text(" ", strip=True)) if old else None
    if list_price is not None and list_price <= price:
        list_price = None

    body = info.select_one(".tb_product_description")
    specs = {}
    if body:
        for tr in body.select("tr"):
            tds = tr.find_all(["td", "th"], recursive=False)
            if len(tds) >= 2:
                k, v = (tidy(x.get_text(" ", strip=True)) for x in tds[:2])
                if k and v:
                    specs[k] = v
        lines = [tidy(x.get_text(" ", strip=True)) for x in body.find_all("p")]
        lines = [x for x in lines if x and not any(x.startswith(a) for a in NON_PRODUCT_TEXT)]
        description = " ".join(lines)
    else:
        description = ""
    details = " ".join(f"{k}: {v}." for k, v in specs.items())
    description = tidy((description + " " + details))[:2000] or title
    imgs = []
    for a in info.select(".tb_system_product_images a[href]"):
        href = a["href"]
        if "/image/" in href and re.search(r"\.(?:jpe?g|png|webp)(?:\?|$)", href, re.I):
            iurl = image_url(href)
            if iurl not in imgs:
                imgs.append(iurl)
    if not imgs:
        for img in info.select(".tb_system_product_images img[src]"):
            imgs.append(image_url(img["src"]))
    if not imgs:
        return None, "Липсва продуктова снимка"

    # These are actual order controls; dimension lists in text are NOT selectable variants.
    variants = []
    selectors = info.select("select[name^='option[']")
    if len(selectors) > 1 or info.select("input[name^='option['],textarea[name^='option[']"):
        return None, "Сложни опции за покупка: нужни са ръчна цена и снимки по вариант"
    if selectors:
        control = selectors[0]
        group = control.find_parent(class_=re.compile("form-group|option", re.I))
        label = tidy(group.find("label").get_text(" ", strip=True)) if group and group.find("label") else ""
        label_lower = label.lower()
        if "размер" in label_lower:
            theme = "Size"
        elif "цвят" in label_lower:
            theme = "Color"
        elif "модел" in label_lower:
            theme = "Model"
        else:
            return None, "Непозната опция за покупка: " + label
        for opt in control.select("option[value]"):
            if not opt["value"] or opt.has_attr("disabled"):
                continue
            variant_name = tidy(opt.get_text(" ", strip=True))
            extra = money(variant_name)
            delta = extra if "+" in variant_name else -(extra or 0) if "-" in variant_name and extra else Decimal(0)
            name = re.sub(r"\s*\([+-]\s*[\d.,]+\s*€\)\s*$", "", variant_name)
            variants.append((theme, name, price + delta))
        if not variants or len(variants) > 30:
            return None, "Неподдържан брой покупни варианти"
    return Product(url, source_category, category, title, sku, price, list_price,
                   facts.get("Производители", ""), description, specs, imgs[:10], variants), ""


def issue(kind: str, url: str, message: str, sku: str = "", row: int | str = "") -> dict:
    return {"type": kind, "sku": sku, "row": row, "url": url, "details": message}


def material_of(p: Product) -> str:
    blob = (p.description + " " + p.title).lower()
    choices = [
        ("силикон", "Silicone"), ("стъклопласт", "Fiberglass"),
        ("полиуретан", "Polyurethane"), ("полипропилен", "Plastic"),
        ("abs", "Plastic"), ("абс", "Plastic"), ("пластмас", "Plastic"),
        ("неръждаема стомана", "Stainless Steel"), ("стомана", "Steel"),
        ("алумини", "Aluminum"), ("дърво", "Wood"),
    ]
    result = next((v for k, v in choices if k in blob), "")
    if p.category == "39761" and result not in {"Silicone", "Plastic", "Steel", "Aluminum", "Stainless Steel", "Wood"}:
        return ""
    if p.category in {"15539", "15627"} and result == "Silicone":
        return ""
    return result


def product_code(sku: str, url: str) -> str:
    normalized = unicodedata.normalize("NFKD", sku)
    clean = re.sub(r"[^A-Z0-9]+", "-", normalized.upper()).strip("-")[:52]
    return "KALA-" + (clean or hashlib.sha1(url.encode()).hexdigest()[:12].upper())


def rows_for(p: Product, args: argparse.Namespace, issues: list[dict], seen_codes: set[str]) -> list[dict]:
    base = product_code(p.sku, p.url)
    if base in seen_codes:
        base += "-" + hashlib.sha1(p.url.encode()).hexdigest()[:7].upper()
    seen_codes.add(base)
    source_maker = p.manufacturer.casefold()
    manufacturer = args.manufacturer if source_maker in ("ilstart", "илстарт") else ""
    material = material_of(p)
    if not manufacturer:
        issues.append(issue("MANUFACTURER_REVIEW", p.url, f"Производител на сайта: {p.manufacturer or 'липсва'}", p.sku))
    if not material:
        issues.append(issue("MATERIAL_REVIEW", p.url, "Няма сигурна допустима стойност за материала", p.sku))
    if not all((args.package_weight_g, args.package_length_cm, args.package_width_cm, args.package_height_cm)):
        issues.append(issue("PACKAGE_DATA", p.url, "Проверете тегло и размери на опакован продукт", p.sku))
    issues.append(issue("STOCK_AND_ORIGIN", p.url, "Потвърдете реална наличност и държава на произход", p.sku))
    if len(p.images) == 1:
        issues.append(issue("IMAGE_REVIEW", p.url, "Една снимка; прегледайте размер, фон и допълнителни кадри", p.sku))
    if p.variants:
        issues.append(issue("VARIANT_REVIEW", p.url, "Потвърдете цена, наличност и снимки за всеки вариант", p.sku))
    variants = p.variants or [("Model", p.sku, p.price)]
    results = []
    for idx, (theme, variant_name, actual_price) in enumerate(variants, 1):
        sku_code = base if len(variants) == 1 else f"{base}-{idx}"
        if actual_price <= 0:
            issues.append(issue("VARIANT_PRICE", p.url, "Вариант с невалидна крайна цена", p.sku))
            continue
        col = {"Model": "GY", "Size": "GO", "Color": "GN"}[theme]
        title = p.title[:500]
        record = {
            "E": p.category, "G": "Normal product", "L": title, "M": base, "N": sku_code,
            "T": p.description, "U": (p.description[:700]), "GM": theme,
            col: variant_name[:100], "HL": str(args.stock_quantity),
            "HM": amount(actual_price * args.price_multiplier), "HN": p.url,
            "IF": args.shipping_template, "IG": args.handling_time,
            "IH": "I will ship this item myself", "IJ": args.country_of_origin,
            "KJ": p.sku, "KK": manufacturer,
        }
        if material:
            record["EP" if p.category == "39761" else "EX"] = material
        if p.category == "15539":
            record["FA"] = "Use Without Electricity"
        if p.list_price and not p.variants:
            record["HO"] = amount(p.list_price * args.price_multiplier)
        else:
            record["HP"] = "N/A"
        if args.package_weight_g:
            record["HQ"] = args.package_weight_g
        for c, value in zip(("HR", "HS", "HT"), (args.package_length_cm, args.package_width_cm, args.package_height_cm)):
            if value:
                record[c] = value
        for col_num, img in enumerate(p.images):
            record[excel_col(209 + col_num)] = img  # HA:HJ
            record[excel_col(27 + col_num)] = img  # AA:AJ
        results.append(record)
    return results


def excel_col(n: int) -> str:
    result = ""
    while n:
        n, rem = divmod(n - 1, 26)
        result = chr(65 + rem) + result
    return result


def column_number(c: str) -> int:
    n = 0
    for letter in c:
        n = n * 26 + ord(letter) - 64
    return n


def write_template(template: Path, output: Path, records: list[dict]):
    if START_ROW + len(records) - 1 > CAPACITY:
        raise ValueError(f"Продуктите ({len(records)}) надвишават капацитета от {CAPACITY-START_ROW+1} реда")
    # The template's 10 other sheets contain dropdowns, formulas, instructions and
    # conditional formatting. Replace only Template's XML sheet, retaining all ZIP parts.
    with ZipFile(template) as src:
        workbook = etree.fromstring(src.read("xl/workbook.xml"))
        rels = etree.fromstring(src.read("xl/_rels/workbook.xml.rels"))
        relationship = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"
        sheet = next((s for s in workbook.find(NS + "sheets") if s.get("name") == "Template"), None)
        if sheet is None:
            raise ValueError("Липсва лист Template")
        rid = sheet.get(relationship)
        target = next((r.get("Target") for r in rels if r.get("Id") == rid), None)
        if not target:
            raise ValueError("Липсва връзка към лист Template")
        sheet_file = target.lstrip("/") if target.startswith("/") else "xl/" + target
        root = etree.fromstring(src.read(sheet_file))
        data = root.find(NS + "sheetData")
        header = next((r for r in data if r.get("r") == str(HEADER_ROW)), None)
        reserved = next((r for r in data if r.get("r") == "3"), None)
        if header is None or reserved is None or not any(c.get("r") == "E3" for c in reserved):
            raise ValueError("Непознат Temu шаблон: защитеният ред или заглавията липсват")
        if not any(c.get("r") == "HM4" for c in header):
            raise ValueError("Шаблонът не съдържа познатите колони на Temu")
        categories = {
            "39761": "Arts, Crafts & Sewing / Crafting / Sculpture Supplies / Molding & Casting",
            "15539": "Tools & Home Improvement / Power & Hand Tools / Hand Tools / Masonry Tools / Forms / Outdoor Landscaping Stone Forms",
            "24795": "Patio, Lawn & Garden / Outdoor Décor / Hardscaping Materials / Outdoor Landscaping Stone Forms",
        }
        row_map = {int(r.get("r")): r for r in data if r.tag == NS + "row"}
        for offset, rec in enumerate(records):
            row_no = START_ROW + offset
            row = row_map.get(row_no)
            if row is None:
                row = etree.Element(NS + "row", r=str(row_no), spans="1:298")
                data.append(row)
            old_style = {c.get("r").rstrip("0123456789"): c.get("s") for c in row if c.tag == NS + "c" and c.get("s")}
            # Clear the preset demo values on row 5; preserve F's category lookup.
            for c in list(row):
                if c.tag == NS + "c" and c.get("r") != f"F{row_no}":
                    row.remove(c)
            cells = {c.get("r"): c for c in row if c.tag == NS + "c"}
            for col, val in rec.items():
                cell = etree.Element(NS + "c", r=f"{col}{row_no}")
                if old_style.get(col):
                    cell.set("s", old_style[col])
                if col in {"HL", "HM", "HO", "HQ", "HR", "HS", "HT"}:
                    cell.set("t", "n")
                    etree.SubElement(cell, NS + "v").text = str(val)
                else:
                    cell.set("t", "inlineStr")
                    is_node = etree.SubElement(cell, NS + "is")
                    etree.SubElement(is_node, NS + "t").text = str(val)
                cells[cell.get("r")] = cell
            # Keep formula and update its cached value so previews show the correct category.
            cached = cells.get(f"F{row_no}")
            if cached is not None:
                v = cached.find(NS + "v")
                if v is None:
                    v = etree.SubElement(cached, NS + "v")
                v.text = categories[rec["E"]]
            for c in list(row):
                if c.tag == NS + "c":
                    row.remove(c)
            for cell in sorted(cells.values(), key=lambda c: column_number(re.match(r"[A-Z]+", c.get("r")).group())):
                row.append(cell)
        output.parent.mkdir(parents=True, exist_ok=True)
        with ZipFile(output, "w") as dst:
            for item in src.infolist():
                raw = etree.tostring(root, xml_declaration=False, encoding="UTF-8") if item.filename == sheet_file else src.read(item.filename)
                dst.writestr(item, raw)


def env_decimal(name: str) -> str:
    raw = os.getenv(name, "").strip().replace(",", ".")
    if not raw:
        return ""
    value = Decimal(raw)
    if value <= 0:
        raise ValueError(f"{name} трябва да е положително число")
    return str(value)


def get_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--template", type=Path, default=Path("template.xlsx"))
    parser.add_argument("--output", type=Path, default=Path("results/kalapite-temu.xlsx"))
    parser.add_argument("--report", type=Path, default=Path("results/review.csv"))
    parser.add_argument("--max-products", type=int, default=int(os.getenv("MAX_PRODUCTS") or 0))
    args = parser.parse_args()
    args.price_multiplier = Decimal(os.getenv("PRICE_MULTIPLIER") or "1")
    args.stock_quantity = int(os.getenv("STOCK_QUANTITY") or "100")
    args.shipping_template = os.getenv("SHIPPING_TEMPLATE") or "Илстарт ЕООД"
    args.manufacturer = os.getenv("TEMU_MANUFACTURER") or "Ilstart"
    args.country_of_origin = os.getenv("COUNTRY_OF_ORIGIN") or "Bulgaria"
    args.handling_time = os.getenv("HANDLING_TIME") or "1 Day"
    args.delay = float(os.getenv("DELAY_SECONDS") or "0.6")
    for key in ("WEIGHT_G", "LENGTH_CM", "WIDTH_CM", "HEIGHT_CM"):
        setattr(args, "package_" + key.lower(), env_decimal("PACKAGE_" + key))
    if args.max_products < 0 or args.stock_quantity < 1 or args.price_multiplier <= 0 or args.delay < 0:
        parser.error("Невалидни настройки за брой, склад, множител или пауза")
    return args


def main():
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    args = get_args()
    issues: list[dict] = []
    records = []
    site = Client(args.delay)
    found = discover(site, issues, args.max_products)
    seen_codes: set[str] = set()
    successful_pages = 0
    for url, category in found.items():
        if args.max_products and successful_pages >= args.max_products:
            break
        try:
            soup = site.get(url)
            product, reason = parse_product(soup, url, category)
            successful_pages += 1
        except requests.RequestException as exc:
            issues.append(issue("PRODUCT_ERROR", url, str(exc)))
            continue
        if product is None:
            issues.append(issue("SKIPPED", url, reason))
            continue
        try:
            width, height, nbytes = site.image_info(product.images[0])
            if width < 800 or height < 800 or width != height or nbytes > 3_000_000:
                issues.append(issue("IMAGE_TOO_SMALL_OR_WRONG_FORMAT", url,
                                    f"Основна снимка {width}x{height}px, {nbytes} bytes; Temu иска квадрат ≥800x800px и ≤3MB",
                                    product.sku))
        except (requests.RequestException, ValueError, OSError) as exc:
            issues.append(issue("IMAGE_UNVERIFIED", url, f"Снимката не можа да се провери: {exc}", product.sku))
        first_row = START_ROW + len(records)
        new_records = rows_for(product, args, issues, seen_codes)
        for review in issues:
            if review["sku"] == product.sku and review["url"] == url and not review["row"]:
                review["row"] = first_row
        records.extend(new_records)
        LOG.info("product %d | rows %d | %s", successful_pages, len(records), product.sku)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    with args.report.open("w", encoding="utf-8-sig", newline="") as out:
        w = csv.DictWriter(out, fieldnames=["type", "sku", "row", "url", "details"])
        w.writeheader()
        for it in issues:
            w.writerow(it)
    summary = {"product_pages_found": len(found), "product_pages_read": successful_pages,
               "exported_sku_rows": len(records), "review_items": len(issues),
               "settings": {"quantity": args.stock_quantity,
                            "price_multiplier": str(args.price_multiplier)}}
    (args.report.parent / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    if not records:
        raise RuntimeError("Няма валидни записи; вижте review.csv и проверете достъпа до сайта")
    write_template(args.template, args.output, records)
    LOG.info("Done: %s (%s rows), review: %s", args.output, len(records), args.report)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, requests.RequestException) as exc:
        LOG.error("Scraper stopped: %s", exc)
        sys.exit(1)
