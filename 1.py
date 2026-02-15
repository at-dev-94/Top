import csv
import json
import os
import re
import hashlib
import threading
import xml.etree.ElementTree as ET
import zipfile
from queue import Queue
import tkinter as tk
from collections import deque
from datetime import datetime, timedelta
from tkinter import filedialog, ttk, messagebox
from urllib.parse import urljoin, urlparse

import pandas as pd
import requests
from bs4 import BeautifulSoup
from tqdm import tqdm


CATEGORY_CONFIG = [
    ("Annual", "01_Annual_Reports", "AnnualReport", [
        "annual report",
        "annual financial report",
        "appendix 4e",
        "full year results",
        "fy results",
        "financial statements",
        "annual financial statements",
    ]),
    ("Half", "02_Half_Year_Reports", "HalfYearReport", [
        "half-year",
        "half year",
        "interim report",
        "appendix 4d",
        "1h results",
        "half year results",
        "half-year financial report",
    ]),
    ("Quarterly", "03_Quarterly_Reports", "Quarterly", [
        "quarter",
        "quarterly",
        "quarterly activities",
        "activities report",
        "quarterly cashflow",
        "cash flow report",
        "appendix 5b",
        "quarterly report",
        "quarterly activities report",
    ]),
    ("Presentation", "04_Presentations", "Presentation", [
        "presentation",
        "investor",
        "conference",
        "results presentation",
        "investor day",
        "analyst",
        "investor presentation",
        "results deck",
    ]),
    ("Res&Res", "05_Resources_Reserves", "ReservesResources", [
        "resource",
        "reserve",
        "jorc",
        "mineral resource",
        "ore reserve",
        "resources and reserves",
        "resource and reserve",
    ]),
    ("Transcript", "06_Earnings_Calls_Transcripts", "Transcript", [
        "transcript",
        "earnings call",
        "webcast",
        "conference call",
        "results call",
        "earnings call transcript",
    ]),
]

OTHER_CATEGORY = ("Other", "07_Other_ASX_Releases", "Other")

INDEX_COLUMNS = [
    "Ticker",
    "Company",
    "Document category",
    "Document title",
    "Release date",
    "Period covered",
    "Source",
    "Source URL",
    "Saved file name",
    "Notes",
]

DOWNLOADABLE_EXTS = {
    ".pdf",
    ".doc",
    ".docx",
    ".xls",
    ".xlsx",
    ".ppt",
    ".pptx",
    ".zip",
    ".mp3",
    ".wav",
}


def load_config(path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def ensure_directories(output_root, tickers):
    os.makedirs(output_root, exist_ok=True)
    for ticker in tickers:
        ticker_dir = os.path.join(output_root, ticker)
        os.makedirs(ticker_dir, exist_ok=True)
        for _, folder, _, _ in CATEGORY_CONFIG:
            os.makedirs(os.path.join(ticker_dir, folder), exist_ok=True)
        os.makedirs(os.path.join(ticker_dir, OTHER_CATEGORY[1]), exist_ok=True)


def parse_date(value):
    if not value:
        return None
    if isinstance(value, (int, float)):
        return None
    value = str(value).strip()
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%d-%m-%Y", "%d/%m/%Y", "%Y-%m-%dT%H:%M:%S%z"):
        try:
            return datetime.strptime(value[:19], fmt).date().isoformat()
        except ValueError:
            continue
    try:
        return datetime.fromisoformat(value).date().isoformat()
    except ValueError:
        return None


def parse_date_from_text(text):
    if not text:
        return None
    text = text.strip()
    iso_match = re.search(r"(20\d{2})[-/](0[1-9]|1[0-2])[-/](0[1-9]|[12]\d|3[01])", text)
    if iso_match:
        return f"{iso_match.group(1)}-{iso_match.group(2)}-{iso_match.group(3)}"
    dm_match = re.search(r"(0[1-9]|[12]\d|3[01])[-/](0[1-9]|1[0-2])[-/](20\d{2})", text)
    if dm_match:
        return f"{dm_match.group(3)}-{dm_match.group(2)}-{dm_match.group(1)}"
    compact = re.search(r"(20\d{2})(0[1-9]|1[0-2])(0[1-9]|[12]\d|3[01])", text)
    if compact:
        return f"{compact.group(1)}-{compact.group(2)}-{compact.group(3)}"
    return None


def parse_period(title):
    if not title:
        return "NA"
    text = title.lower()

    annual_match = re.search(r"annual report.*\b(20\d{2})\b", text)
    if annual_match:
        return f"FY{annual_match.group(1)}"
    annual_match = re.search(r"\b(20\d{2})\b.*annual report", text)
    if annual_match:
        return f"FY{annual_match.group(1)}"

    fy_match = re.search(r"\bfy\s?20\d{2}\b", text)
    if fy_match:
        return fy_match.group(0).upper().replace(" ", "")

    fy_match = re.search(r"\b20\d{2}\b", text)
    if "full year" in text and fy_match:
        return f"FY{fy_match.group(0)}"

    half_match = re.search(r"\b(1h|h1|half year|half-year)\s?20\d{2}\b", text)
    if half_match:
        year_match = re.search(r"20\d{2}", half_match.group(0))
        if year_match:
            return f"1H{year_match.group(0)}"

    q_match = re.search(r"\b([1-4])q\s?20\d{2}\b", text)
    if q_match:
        return f"{q_match.group(1)}Q{q_match.group(0)[-4:]}"

    quarter_match = re.search(r"(march|june|september|december)\s+quarter\s+20\d{2}", text)
    if quarter_match:
        words = quarter_match.group(0).title().replace(" ", "_")
        return words.replace("Quarter", "Quarter")

    return "NA"


def slugify(text, max_length):
    if not text:
        return "Untitled"
    text = re.sub(r"[^\w\s-]", "", text, flags=re.ASCII).strip()
    text = re.sub(r"[\s-]+", "_", text)
    if len(text) > max_length:
        text = text[:max_length].rstrip("_")
    return text or "Untitled"


def classify_category(title):
    if not title:
        return OTHER_CATEGORY
    lower = title.lower()
    for cat in CATEGORY_CONFIG:
        if any(keyword in lower for keyword in cat[3]):
            return cat
    return OTHER_CATEGORY


def normalize_url(base, link):
    if not link:
        return ""
    return urljoin(base, link)


def is_allowed_domain(url, allowed_domains):
    try:
        hostname = urlparse(url).hostname or ""
    except ValueError:
        return False
    hostname = hostname.lower()
    return any(hostname == domain or hostname.endswith(f".{domain}") for domain in allowed_domains)


def extract_links(html, base_url):
    soup = BeautifulSoup(html, "html.parser")
    links = []
    for anchor in soup.find_all("a", href=True):
        href = anchor.get("href")
        text = anchor.get_text(" ", strip=True)
        links.append((normalize_url(base_url, href), text))
    return links


def guess_title(link_text, url):
    if link_text:
        return link_text
    parsed = urlparse(url)
    name = os.path.basename(parsed.path)
    name = re.sub(r"[_\-]+", " ", name)
    name = re.sub(r"\.\w+$", "", name)
    return name.strip() or "Untitled"


def detect_extension(url, content_type):
    if content_type and "pdf" in content_type.lower():
        return ".pdf"
    parsed = urlparse(url)
    ext = os.path.splitext(parsed.path)[1]
    if ext:
        return ext
    return ".pdf"


def fetch_asx_announcements(session, api_url, ticker, company_url=None, log_cb=None):
    url = api_url.format(ticker=ticker)
    headers = {
        "Accept": "application/json,text/plain,*/*",
    }
    if company_url:
        headers["Referer"] = company_url
    try:
        resp = session.get(url, timeout=45, headers=headers)
        resp.raise_for_status()
    except requests.RequestException as exc:
        status = getattr(getattr(exc, "response", None), "status_code", None)
        if status == 403:
            msg = (
                f"ASX API blocked (403) for {ticker}. "
                "Switch to Company Site Crawl or disable API mode."
            )
        else:
            msg = f"ASX API request failed for {ticker}: {exc}"
        if log_cb:
            log_cb(msg)
        else:
            print(msg)
        return []
    data = resp.json()
    if isinstance(data, dict):
        for key in ("data", "items", "announcements"):
            if key in data and isinstance(data[key], list):
                return data[key]
    if isinstance(data, list):
        return data
    return []


def extract_announcement_fields(item):
    title = item.get("headline") or item.get("title") or item.get("header") or ""
    date_val = item.get("date") or item.get("released_date") or item.get("release_date")
    url = item.get("document_url") or item.get("url") or item.get("link")
    return title, date_val, url


def download_content(session, url, timeout):
    resp = session.get(url, timeout=timeout, stream=True)
    resp.raise_for_status()
    return resp


def save_response_content(resp, path):
    with open(path, "wb") as fh:
        for chunk in resp.iter_content(chunk_size=8192):
            if chunk:
                fh.write(chunk)


def save_html_as_file(html, path):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(html)


def build_filename(ticker, doc_type, period, release_date, title, ext, max_length):
    title_slug = slugify(title, max_length)
    release_date = release_date or "NA"
    period = period or "NA"
    filename = f"{ticker}_{doc_type}_{period}_{release_date}_{title_slug}{ext}"
    if len(filename) > max_length:
        overflow = len(filename) - max_length
        title_slug = title_slug[:-overflow].rstrip("_") or "Untitled"
        filename = f"{ticker}_{doc_type}_{period}_{release_date}_{title_slug}{ext}"
    return filename


def compute_sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(8192), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_valid_pdf(path):
    try:
        with open(path, "rb") as fh:
            header = fh.read(5)
        return header == b"%PDF-"
    except OSError:
        return False


def is_duplicate(seen_urls, url):
    if not url:
        return True
    if url in seen_urls:
        return True
    seen_urls.add(url)
    return False


def filter_by_date(date_str, start_date, end_date):
    if not date_str:
        return False
    try:
        date_obj = datetime.strptime(date_str, "%Y-%m-%d").date()
    except ValueError:
        return False
    return start_date <= date_obj <= end_date


def add_na_notes(notes, release_date, period):
    parts = []
    if notes:
        parts.append(notes)
    if not release_date or release_date == "NA":
        parts.append("release date NA")
    if period == "NA":
        parts.append("period NA")
    return "; ".join(parts)


def load_source_list(csv_path):
    if not csv_path:
        return []
    rows = []
    with open(csv_path, "r", encoding="utf-8") as fh:
        reader = csv.DictReader(fh)
        for row in reader:
            rows.append(row)
    return rows


def crawl_company_sources(session, seed_urls, allowed_domains, max_depth, max_pages, timeout):
    visited = set()
    doc_links = []
    queue = deque([(url, 0) for url in seed_urls])

    while queue and len(visited) < max_pages:
        url, depth = queue.popleft()
        if url in visited:
            continue
        visited.add(url)

        try:
            resp = session.get(url, timeout=timeout)
            resp.raise_for_status()
        except Exception:
            continue

        content_type = resp.headers.get("Content-Type", "")
        if "text/html" not in content_type.lower():
            continue

        html = resp.text
        links = extract_links(html, url)
        for link_url, link_text in links:
            if not link_url:
                continue

            parsed = urlparse(link_url)
            ext = os.path.splitext(parsed.path)[1].lower()
            if ext in DOWNLOADABLE_EXTS:
                doc_links.append((link_url, link_text))
                continue

            if depth < max_depth and is_allowed_domain(link_url, allowed_domains):
                queue.append((link_url, depth + 1))

    return doc_links


def fetch_sitemap_links(session, base_url, timeout, max_urls):
    parsed = urlparse(base_url)
    if not parsed.scheme or not parsed.hostname:
        return []

    sitemap_candidates = [
        f"{parsed.scheme}://{parsed.hostname}/sitemap.xml",
        f"{parsed.scheme}://{parsed.hostname}/sitemap_index.xml",
    ]
    links = []

    for sitemap_url in sitemap_candidates:
        try:
            resp = session.get(sitemap_url, timeout=timeout)
            resp.raise_for_status()
        except Exception:
            continue

        try:
            root = ET.fromstring(resp.text)
        except ET.ParseError:
            continue

        for loc in root.iter():
            if loc.tag.endswith("loc") and loc.text:
                url = loc.text.strip()
                ext = os.path.splitext(urlparse(url).path)[1].lower()
                if ext in DOWNLOADABLE_EXTS:
                    links.append((url, os.path.basename(url)))
                    if len(links) >= max_urls:
                        return links
    return links


def discover_api_endpoints(session, page_url, timeout, max_endpoints, log_cb=None):
    def log(message):
        if log_cb:
            log_cb(message)
        else:
            print(message)

    try:
        resp = session.get(page_url, timeout=timeout)
        resp.raise_for_status()
    except Exception as exc:
        log(f"API discovery failed for {page_url}: {exc}")
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    text_blobs = [resp.text]
    for script in soup.find_all("script"):
        if script.get("src"):
            text_blobs.append(script.get("src"))
        if script.string:
            text_blobs.append(script.string)

    candidates = set()
    patterns = [
        r"https?://[^\s\"']+(?:wp-json|/api/|/graphql|/json|/rest/)[^\s\"']*",
        r"/wp-json[^\s\"']*",
        r"/api/[^\s\"']*",
        r"/graphql[^\s\"']*",
        r"/rest/[^\s\"']*",
        r"/json/[^\s\"']*",
    ]
    for blob in text_blobs:
        if not blob:
            continue
        for pattern in patterns:
            for match in re.findall(pattern, blob):
                candidates.add(normalize_url(page_url, match))

    endpoints = []
    for url in candidates:
        if len(endpoints) >= max_endpoints:
            break
        endpoints.append(url)
    if endpoints:
        log(f"API endpoints discovered from {page_url}: {len(endpoints)}")
    return endpoints


def extract_download_links_from_json(data, base_url):
    links = set()
    stack = [data]
    while stack:
        item = stack.pop()
        if isinstance(item, dict):
            for value in item.values():
                stack.append(value)
        elif isinstance(item, list):
            for value in item:
                stack.append(value)
        elif isinstance(item, str):
            if any(ext in item.lower() for ext in DOWNLOADABLE_EXTS):
                url = normalize_url(base_url, item)
                links.add(url)
    return [(url, os.path.basename(urlparse(url).path) or "Document") for url in links]


def fetch_api_links(session, api_url, timeout, max_docs, log_cb=None):
    def log(message):
        if log_cb:
            log_cb(message)
        else:
            print(message)

    try:
        resp = session.get(api_url, timeout=timeout)
        resp.raise_for_status()
        data = resp.json()
    except Exception as exc:
        log(f"API fetch failed for {api_url}: {exc}")
        return []

    links = extract_download_links_from_json(data, api_url)
    if len(links) > max_docs:
        links = links[:max_docs]
    if links:
        log(f"API documents found from {api_url}: {len(links)}")
    return links


def fetch_aru_financial_reports(session, page_url, timeout, log_cb=None):
    def log(message):
        if log_cb:
            log_cb(message)
        else:
            print(message)

    try:
        resp = session.get(page_url, timeout=timeout)
        resp.raise_for_status()
    except Exception as exc:
        log(f"ARU financial reports page fetch failed: {exc}")
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    links = []
    for anchor in soup.find_all("a", href=True):
        text = anchor.get_text(" ", strip=True)
        href = normalize_url(page_url, anchor.get("href"))
        if not href:
            continue
        lower_text = text.lower()
        lower_href = href.lower()
        if "annual report" in lower_text or "annual-report" in lower_href:
            ext = os.path.splitext(urlparse(href).path)[1].lower()
            if ext in DOWNLOADABLE_EXTS or ext == ".pdf":
                links.append((href, text or "Annual Report"))

    if links:
        log(f"ARU financial reports found: {len(links)}")
    return links


def fetch_aru_asx_announcements(session, year, timeout, log_cb=None):
    def log(message):
        if log_cb:
            log_cb(message)
        else:
            print(message)

    page_url = f"https://www.arultd.com/investor/asx-announcements/asx-announcements-{year}/"
    try:
        resp = session.get(page_url, timeout=timeout)
        resp.raise_for_status()
    except Exception as exc:
        log(f"ARU ASX announcements {year} page fetch failed: {exc}")
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    links = []
    for anchor in soup.find_all("a", href=True):
        text = anchor.get_text(" ", strip=True)
        href = normalize_url(page_url, anchor.get("href"))
        if not href:
            continue
        ext = os.path.splitext(urlparse(href).path)[1].lower()
        if ext in DOWNLOADABLE_EXTS:
            links.append((href, text or f"ASX Announcement {year}"))

    if links:
        log(f"ARU ASX announcements {year} found: {len(links)}")
    return links


def run_pipeline(config, log_cb=None):
    def log(message):
        if log_cb:
            log_cb(message)
        else:
            print(message)

    output_root = config["output_root"]
    tickers = config["tickers"]
    company_names = config["company_names"]
    api_url = config["asx_api_base"]
    source_list_csv = config.get("source_list_csv", "")
    company_sources = config.get("company_sources", {})
    use_asx_api = config.get("use_asx_api", True)
    crawl_max_depth = config.get("crawl_max_depth", 2)
    crawl_max_pages = config.get("crawl_max_pages", 600)
    use_sitemap = config.get("use_sitemap", False)
    sitemap_max_urls = config.get("sitemap_max_urls", 2000)
    auto_discover_api = config.get("auto_discover_api", True)
    api_max_endpoints = config.get("api_max_endpoints", 10)
    api_max_docs = config.get("api_max_docs", 500)
    allowed_domains_extra = config.get("allowed_domains_extra", [])
    save_html_pages = config.get("save_html_pages", True)
    archive_output = config.get("archive_output", True)
    archive_format = config.get("archive_format", "zip")
    user_agent = config.get("user_agent", "ASX-Disclosure-Bot/1.0")
    timeout = config.get("download_timeout_sec", 45)
    max_filename_length = config.get("max_filename_length", 160)
    dry_run = config.get("dry_run", False)

    start_date = datetime.strptime(config["date_from"], "%Y-%m-%d").date()
    end_date = datetime.strptime(config["date_to"], "%Y-%m-%d").date()

    ensure_directories(output_root, tickers)

    session = requests.Session()
    session.headers.update({"User-Agent": user_agent})

    index_rows = []
    qa_notes = []

    source_rows = load_source_list(source_list_csv)
    source_lookup = {}
    if source_rows:
        for row in source_rows:
            ticker = row.get("ticker", "").upper()
            if not ticker:
                continue
            source_lookup.setdefault(ticker, []).append(row)

    for ticker in tickers:
        seen_urls = set()
        seen_hashes = set()
        company = company_names.get(ticker, ticker)
        doc_count = 0

        if source_rows:
            announcements = source_lookup.get(ticker, [])
            iterable = announcements
        elif use_asx_api:
            try:
                company_url = (company_sources.get(ticker) or [None])[0]
                announcements = fetch_asx_announcements(
                    session,
                    api_url,
                    ticker,
                    company_url=company_url,
                    log_cb=log_cb,
                )
                iterable = announcements
            except requests.HTTPError as exc:
                status = getattr(exc.response, "status_code", None)
                log(f"ASX API error {status} for {ticker}. Skipping ASX API.")
                iterable = []
        else:
            iterable = []

        company_seed_urls = company_sources.get(ticker, [])
        allowed_domains = set(allowed_domains_extra)
        for seed in company_seed_urls:
            parsed = urlparse(seed)
            if parsed.hostname:
                allowed_domains.add(parsed.hostname.lower())

        for item in tqdm(iterable, desc=f"{ticker} ASX", unit="doc", disable=bool(log_cb)):
            if source_rows:
                title = item.get("title", "")
                date_val = item.get("date", "")
                url = item.get("source_url", "")
                source = item.get("source", "ASX")
                category_override = item.get("category", "")
                period_override = item.get("period", "")
            else:
                title, date_val, url = extract_announcement_fields(item)
                source = "ASX"
                category_override = ""
                period_override = ""

            release_date = parse_date(date_val)
            if not release_date or not filter_by_date(release_date, start_date, end_date):
                continue

            if is_duplicate(seen_urls, url):
                continue

            if category_override:
                category = next((c for c in CATEGORY_CONFIG if c[0].lower() == category_override.lower()), None)
                if category:
                    category_tuple = category
                elif category_override.lower() == "other":
                    category_tuple = OTHER_CATEGORY
                else:
                    category_tuple = classify_category(title)
            else:
                category_tuple = classify_category(title)

            category_name, folder_name, doc_type = category_tuple
            period = period_override or parse_period(title)
            ext = ".pdf"

            if not url:
                notes = "missing attachment url"
                filename = build_filename(ticker, doc_type, period, release_date, title, ext, max_filename_length)
                final_notes = add_na_notes(notes, release_date, period)
                index_rows.append([
                    ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
                ])
                continue

            if dry_run:
                filename = build_filename(ticker, doc_type, period, release_date, title, ext, max_filename_length)
                final_notes = add_na_notes("dry run", release_date, period)
                index_rows.append([
                    ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
                ])
                continue

            try:
                resp = download_content(session, url, timeout)
                content_type = resp.headers.get("Content-Type", "")
                ext = detect_extension(url, content_type)
                filename = build_filename(ticker, doc_type, period, release_date, title, ext, max_filename_length)
                save_path = os.path.join(output_root, ticker, folder_name, filename)
                save_response_content(resp, save_path)
                notes = ""
            except Exception as exc:
                notes = f"download failed: {exc}"
                filename = build_filename(ticker, doc_type, period, release_date, title, ext, max_filename_length)
                final_notes = add_na_notes(notes, release_date, period)
                index_rows.append([
                    ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
                ])
                continue

            if ext.lower() == ".pdf" and not is_valid_pdf(save_path):
                os.remove(save_path)
                final_notes = add_na_notes("invalid pdf", release_date, period)
                index_rows.append([
                    ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
                ])
                continue

            file_hash = compute_sha256(save_path)
            if file_hash in seen_hashes:
                os.remove(save_path)
                final_notes = add_na_notes("duplicate by hash", release_date, period)
                index_rows.append([
                    ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
                ])
                continue
            seen_hashes.add(file_hash)

            if ext.lower() in (".htm", ".html"):
                notes = "saved as html"

            final_notes = add_na_notes(notes, release_date, period)
            index_rows.append([
                ticker, company, category_name, title, release_date, period, source, url, filename, final_notes
            ])
            doc_count += 1

        doc_links = []
        if company_seed_urls:
            doc_links.extend(crawl_company_sources(
                session,
                company_seed_urls,
                allowed_domains,
                crawl_max_depth,
                crawl_max_pages,
                timeout,
            ))

        if auto_discover_api and company_seed_urls:
            for seed in company_seed_urls:
                endpoints = discover_api_endpoints(
                    session,
                    seed,
                    timeout,
                    api_max_endpoints,
                    log_cb=log_cb,
                )
                for endpoint in endpoints:
                    if not is_allowed_domain(endpoint, allowed_domains):
                        continue
                    doc_links.extend(fetch_api_links(
                        session,
                        endpoint,
                        timeout,
                        api_max_docs,
                        log_cb=log_cb,
                    ))

        if use_sitemap:
            seen_domains = set()
            for seed in company_seed_urls:
                parsed = urlparse(seed)
                if not parsed.hostname or parsed.hostname in seen_domains:
                    continue
                seen_domains.add(parsed.hostname)
                doc_links.extend(fetch_sitemap_links(
                    session,
                    f"{parsed.scheme}://{parsed.hostname}",
                    timeout,
                    sitemap_max_urls,
                ))

        if ticker == "ARU":
            doc_links.extend(fetch_aru_financial_reports(
                session,
                "https://www.arultd.com/investor/financial-reports",
                timeout,
                log_cb=log_cb,
            ))
            for year in range(2020, 2027):
                doc_links.extend(fetch_aru_asx_announcements(
                    session,
                    year,
                    timeout,
                    log_cb=log_cb,
                ))

        if doc_links:
            for link_url, link_text in tqdm(doc_links, desc=f"{ticker} Site", unit="doc", disable=bool(log_cb)):
                if is_duplicate(seen_urls, link_url):
                    continue

                title = guess_title(link_text, link_url)
                release_date = parse_date_from_text(link_text) or parse_date_from_text(link_url)
                if release_date and not filter_by_date(release_date, start_date, end_date):
                    continue

                category_tuple = classify_category(title)
                category_name, folder_name, doc_type = category_tuple
                period = parse_period(title)

                if not release_date:
                    release_date = "NA"

                ext = os.path.splitext(urlparse(link_url).path)[1].lower()
                if ext and ext not in DOWNLOADABLE_EXTS and ext not in (".htm", ".html", ".aspx"):
                    continue

                if dry_run:
                    filename = build_filename(ticker, doc_type, period, release_date, title, ext or ".pdf", max_filename_length)
                    final_notes = add_na_notes("dry run", release_date, period)
                    index_rows.append([
                        ticker, company, category_name, title, release_date, period, "Company Site", link_url, filename, final_notes
                    ])
                    continue

                try:
                    resp = download_content(session, link_url, timeout)
                    content_type = resp.headers.get("Content-Type", "")
                    ext = detect_extension(link_url, content_type)
                    if ext in (".htm", ".html") and not save_html_pages:
                        continue
                    filename = build_filename(ticker, doc_type, period, release_date, title, ext, max_filename_length)
                    save_path = os.path.join(output_root, ticker, folder_name, filename)
                    if ext in (".htm", ".html"):
                        save_html_as_file(resp.text, save_path)
                        notes = "saved as html"
                    else:
                        save_response_content(resp, save_path)
                        notes = ""
                except Exception as exc:
                    notes = f"download failed: {exc}"
                    filename = build_filename(ticker, doc_type, period, release_date, title, ext or ".pdf", max_filename_length)
                    final_notes = add_na_notes(notes, release_date, period)
                    index_rows.append([
                        ticker, company, category_name, title, release_date, period, "Company Site", link_url, filename, final_notes
                    ])
                    continue

                if ext.lower() == ".pdf" and not is_valid_pdf(save_path):
                    os.remove(save_path)
                    final_notes = add_na_notes("invalid pdf", release_date, period)
                    index_rows.append([
                        ticker, company, category_name, title, release_date, period, "Company Site", link_url, filename, final_notes
                    ])
                    continue

                file_hash = compute_sha256(save_path)
                if file_hash in seen_hashes:
                    os.remove(save_path)
                    final_notes = add_na_notes("duplicate by hash", release_date, period)
                    index_rows.append([
                        ticker, company, category_name, title, release_date, period, "Company Site", link_url, filename, final_notes
                    ])
                    continue
                seen_hashes.add(file_hash)

                index_rows.append([
                    ticker, company, category_name, title, release_date, period, "Company Site", link_url, filename, add_na_notes(notes, release_date, period)
                ])
                doc_count += 1

        qa_notes.append(
            f"{ticker}: ASX announcement list reviewed for 2020-2026, duplicates removed, missing items flagged in index."
        )
        qa_notes.append(f"{ticker}: Total documents saved: {doc_count}")

    index_df = pd.DataFrame(index_rows, columns=INDEX_COLUMNS)
    index_path = os.path.join(output_root, "Disclosures_Index.xlsx")
    index_df.to_excel(index_path, index=False)

    qa_path = os.path.join(output_root, "QA_Notes.txt")
    with open(qa_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(qa_notes))

    completion_path = os.path.join(output_root, "Completion_Log.txt")
    counts = {}
    for row in index_rows:
        counts[row[0]] = counts.get(row[0], 0) + 1
    with open(completion_path, "w", encoding="utf-8") as fh:
        for ticker in tickers:
            fh.write(f"{ticker}: {counts.get(ticker, 0)} documents\n")

    if archive_output:
        if archive_format != "zip":
            log("Archive format not supported; only zip is available.")
        else:
            archive_path = f"{output_root}.zip"
            with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
                for root_dir, _, files in os.walk(output_root):
                    for file_name in files:
                        full_path = os.path.join(root_dir, file_name)
                        rel_path = os.path.relpath(full_path, os.path.dirname(output_root))
                        zf.write(full_path, rel_path)
            log(f"Archive created: {archive_path}")

    log(f"Done. Output in: {output_root}")


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = os.path.join(script_dir, "config.json")
    config = load_config(config_path)
    run_pipeline(config)


def run_sample_nst():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = os.path.join(script_dir, "config.json")
    config = load_config(config_path)
    config["tickers"] = ["NST"]
    run_pipeline(config)


def launch_dashboard():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = os.path.join(script_dir, "config.json")
    base_config = load_config(config_path)

    root = tk.Tk()
    root.title("ASX Announcements Downloader")
    root.geometry("1200x760")

    log_queue = Queue()

    def enqueue_log(message):
        log_queue.put(message)

    def poll_log():
        while not log_queue.empty():
            msg = log_queue.get()
            log_text.configure(state="normal")
            log_text.insert("end", msg + "\n")
            log_text.see("end")
            log_text.configure(state="disabled")
        root.after(150, poll_log)

    def select_all():
        for var in ticker_vars.values():
            var.set(True)

    def select_none():
        for var in ticker_vars.values():
            var.set(False)

    def add_custom_ticker():
        value = custom_entry.get().strip().upper()
        if not value:
            return
        if value in ticker_vars:
            ticker_vars[value].set(True)
            return
        var = tk.BooleanVar(value=True)
        ticker_vars[value] = var
        cb = ttk.Checkbutton(ticker_frame, text=value, variable=var)
        row = len(ticker_vars) // 8
        col = len(ticker_vars) % 8
        cb.grid(row=row, column=col, padx=8, pady=4, sticky="w")

    def browse_output():
        folder = filedialog.askdirectory()
        if folder:
            output_var.set(folder)

    def run_download():
        selected = [t for t, var in ticker_vars.items() if var.get()]
        if mode_var.get() == "daily":
            selected = base_config.get("tickers", [])
        if not selected:
            messagebox.showwarning("No tickers", "Select at least one ticker.")
            return

        date_from = f"{from_year_var.get()}-{from_month_var.get()}-{from_day_var.get()}"
        date_to = f"{to_year_var.get()}-{to_month_var.get()}-{to_day_var.get()}"
        if mode_var.get() == "daily":
            today = datetime.now().date()
            date_to = today.isoformat()
            date_from = (today - timedelta(days=1)).isoformat()
        if not date_from or not date_to:
            messagebox.showwarning("Missing dates", "Enter both From and To dates.")
            return

        output_dir = output_var.get().strip()
        if not output_dir:
            messagebox.showwarning("Missing output", "Choose an output directory.")
            return

        use_asx = mode_var.get() in ("api", "daily")
        run_config = dict(base_config)
        run_config["tickers"] = selected
        run_config["date_from"] = date_from
        run_config["date_to"] = date_to
        run_config["output_root"] = output_dir
        run_config["use_asx_api"] = use_asx
        # Always include company URLs so site files are available to download.

        progress.start(10)
        run_button.config(state="disabled")
        status_var.set("Running...")

        def worker():
            try:
                enqueue_log(f"Starting: {', '.join(selected)}")
                enqueue_log("Company site sources enabled for downloads.")
                if mode_var.get() == "daily":
                    enqueue_log("Daily Feed mode: using today and yesterday.")
                run_pipeline(run_config, log_cb=enqueue_log)
            finally:
                progress.stop()
                run_button.config(state="normal")
                status_var.set("Download complete!")

        threading.Thread(target=worker, daemon=True).start()

    header = ttk.Label(root, text="ASX Announcements Downloader", font=("Segoe UI", 14, "bold"))
    header.pack(pady=10)

    mode_frame = ttk.LabelFrame(root, text="Download Mode")
    mode_frame.pack(fill="x", padx=12, pady=6)
    mode_var = tk.StringVar(value="api")
    ttk.Radiobutton(
        mode_frame,
        text="API Mode (5 most recent per company)",
        variable=mode_var,
        value="api",
    ).pack(anchor="w", padx=10, pady=2)
    ttk.Radiobutton(
        mode_frame,
        text="Daily Feed (today + yesterday, all companies)",
        variable=mode_var,
        value="daily",
    ).pack(anchor="w", padx=10, pady=2)
    ttk.Label(
        mode_frame,
        text="API mode fetches the 5 most recent announcements per selected company. Date filter applies to downloaded announcements.",
        font=("Segoe UI", 9),
        foreground="#555555",
    ).pack(anchor="w", padx=10, pady=2)

    ticker_frame = ttk.LabelFrame(root, text="Select Ticker Codes")
    ticker_frame.pack(fill="x", padx=12, pady=6)
    ticker_vars = {}
    for idx, ticker in enumerate(base_config.get("tickers", [])):
        var = tk.BooleanVar(value=True)
        ticker_vars[ticker] = var
        cb = ttk.Checkbutton(ticker_frame, text=ticker, variable=var)
        cb.grid(row=idx // 8, column=idx % 8, padx=8, pady=4, sticky="w")

    ticker_buttons = ttk.Frame(ticker_frame)
    ticker_buttons.grid(row=10, column=0, columnspan=8, pady=6, sticky="w")
    ttk.Button(ticker_buttons, text="Select All", command=select_all).pack(side="left", padx=4)
    ttk.Button(ticker_buttons, text="Select None", command=select_none).pack(side="left", padx=4)

    custom_frame = ttk.Frame(ticker_frame)
    custom_frame.grid(row=11, column=0, columnspan=8, pady=6, sticky="w")
    ttk.Label(custom_frame, text="Add custom:").pack(side="left")
    custom_entry = ttk.Entry(custom_frame, width=12)
    custom_entry.pack(side="left", padx=6)
    ttk.Button(custom_frame, text="Add", command=add_custom_ticker).pack(side="left")

    date_frame = ttk.LabelFrame(root, text="Date Range Filter (API Mode)")
    date_frame.pack(fill="x", padx=12, pady=6)
    from_label = ttk.Label(date_frame, text="From:")
    from_label.pack(side="left", padx=6)
    day_values = [f"{d:02d}" for d in range(1, 32)]
    month_values = [f"{m:02d}" for m in range(1, 13)]
    year_values = [str(y) for y in range(2020, 2027)]

    def split_date(value, fallback):
        try:
            dt = datetime.strptime(value, "%Y-%m-%d").date()
        except ValueError:
            dt = datetime.strptime(fallback, "%Y-%m-%d").date()
        return f"{dt.day:02d}", f"{dt.month:02d}", str(dt.year)

    from_day, from_month, from_year = split_date(base_config.get("date_from", "2020-01-01"), "2020-01-01")
    to_day, to_month, to_year = split_date(base_config.get("date_to", "2026-12-31"), "2026-12-31")

    from_day_var = tk.StringVar(value=from_day)
    from_month_var = tk.StringVar(value=from_month)
    from_year_var = tk.StringVar(value=from_year)
    to_day_var = tk.StringVar(value=to_day)
    to_month_var = tk.StringVar(value=to_month)
    to_year_var = tk.StringVar(value=to_year)

    def apply_date_range(start_date, end_date):
        from_day_var.set(f"{start_date.day:02d}")
        from_month_var.set(f"{start_date.month:02d}")
        from_year_var.set(str(start_date.year))
        to_day_var.set(f"{end_date.day:02d}")
        to_month_var.set(f"{end_date.month:02d}")
        to_year_var.set(str(end_date.year))

    def set_last_days(days):
        end_date = datetime.now().date()
        start_date = end_date - timedelta(days=days)
        apply_date_range(start_date, end_date)

    ttk.Combobox(date_frame, textvariable=from_day_var, values=day_values, width=3, state="readonly").pack(side="left")
    ttk.Label(date_frame, text="/").pack(side="left", padx=2)
    ttk.Combobox(date_frame, textvariable=from_month_var, values=month_values, width=3, state="readonly").pack(side="left")
    ttk.Label(date_frame, text="/").pack(side="left", padx=2)
    ttk.Combobox(date_frame, textvariable=from_year_var, values=year_values, width=6, state="readonly").pack(side="left")

    ttk.Label(date_frame, text="   To:").pack(side="left", padx=10)
    ttk.Combobox(date_frame, textvariable=to_day_var, values=day_values, width=3, state="readonly").pack(side="left")
    ttk.Label(date_frame, text="/").pack(side="left", padx=2)
    ttk.Combobox(date_frame, textvariable=to_month_var, values=month_values, width=3, state="readonly").pack(side="left")
    ttk.Label(date_frame, text="/").pack(side="left", padx=2)
    ttk.Combobox(date_frame, textvariable=to_year_var, values=year_values, width=6, state="readonly").pack(side="left")

    quick_frame = ttk.Frame(date_frame)
    quick_frame.pack(side="right", padx=8)
    ttk.Button(quick_frame, text="Last 7 days", width=12, command=lambda: set_last_days(7)).pack(side="left", padx=4)
    ttk.Button(quick_frame, text="Last 30 days", width=12, command=lambda: set_last_days(30)).pack(side="left", padx=4)
    ttk.Button(quick_frame, text="Last 90 days", width=12, command=lambda: set_last_days(90)).pack(side="left", padx=4)
    ttk.Button(quick_frame, text="Last 1 year", width=12, command=lambda: set_last_days(365)).pack(side="left", padx=4)

    output_frame = ttk.LabelFrame(root, text="Output Directory")
    output_frame.pack(fill="x", padx=12, pady=6)
    output_var = tk.StringVar(value=base_config.get("output_root", "ASX_Disclosures_2020-2026"))
    ttk.Entry(output_frame, textvariable=output_var, width=90).pack(side="left", padx=6, pady=6, fill="x", expand=True)
    ttk.Button(output_frame, text="Browse...", command=browse_output).pack(side="left", padx=6)

    run_frame = ttk.Frame(root)
    run_frame.pack(fill="x", padx=12, pady=6)
    run_button = ttk.Button(run_frame, text="Download Announcements", command=run_download)
    run_button.pack(side="top", pady=4)
    progress = ttk.Progressbar(run_frame, mode="indeterminate")
    progress.pack(side="top", padx=12, fill="x", expand=True)
    status_var = tk.StringVar(value="Ready")
    ttk.Label(run_frame, textvariable=status_var).pack(side="top", pady=2)

    log_frame = ttk.LabelFrame(root, text="Progress")
    log_frame.pack(fill="both", expand=True, padx=12, pady=8)
    log_text = tk.Text(log_frame, height=14, state="disabled", wrap="word")
    log_text.pack(side="left", fill="both", expand=True)
    scrollbar = ttk.Scrollbar(log_frame, command=log_text.yview)
    scrollbar.pack(side="right", fill="y")
    log_text.configure(yscrollcommand=scrollbar.set)

    poll_log()
    root.mainloop()


if __name__ == "__main__":
    import sys

    if "--sample-nst" in sys.argv:
        run_sample_nst()
    elif "--no-gui" in sys.argv:
        main()
    else:
        launch_dashboard()
