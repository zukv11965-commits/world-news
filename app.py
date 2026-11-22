"""
Світ за 5 хвилин — новини з усього світу з вибором мови (uk, ru, en, ...).

Запуск:
    pip install flask feedparser requests deep-translator
    python app.py            # http://localhost:8000

Необов'язково (кращий переклад від Claude):
    export ANTHROPIC_API_KEY="sk-ant-..."
"""
import calendar
import hashlib
import html
import json
import os
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from urllib.parse import quote

import feedparser
import requests
from flask import Flask, jsonify, render_template_string, request

REFRESH_MINUTES = 30      # як часто оновлювати
PER_FEED = 5              # скільки новин з кожної стрічки
PER_SECTION = 12          # скільки показувати в розділі
SUMMARIZE = bool(os.getenv("ANTHROPIC_API_KEY"))
MODEL = "claude-haiku-5-5"
DEFAULT_LANG = "uk"

# код мови -> (назва в списку, назва для Claude). Додавайте свої.
LANGS = {
    "uk": ("Українська", "Ukrainian"), "ru": ("Русский", "Russian"),
    "en": ("English", "English"), "pl": ("Polski", "Polish"),
    "de": ("Deutsch", "German"), "es": ("Español", "Spanish"),
    "fr": ("Français", "French"), "it": ("Italiano", "Italian"),
    "pt": ("Português", "Portuguese"), "nl": ("Nederlands", "Dutch"),
    "sv": ("Svenska", "Swedish"), "no": ("Norsk", "Norwegian"),
    "da": ("Dansk", "Danish"), "fi": ("Suomi", "Finnish"),
    "cs": ("Čeština", "Czech"), "sk": ("Slovenčina", "Slovak"),
    "hu": ("Magyar", "Hungarian"), "ro": ("Română", "Romanian"),
    "bg": ("Български", "Bulgarian"), "sr": ("Српски", "Serbian"),
    "hr": ("Hrvatski", "Croatian"), "sl": ("Slovenščina", "Slovenian"),
    "el": ("Ελληνικά", "Greek"), "lt": ("Lietuvių", "Lithuanian"),
    "lv": ("Latviešu", "Latvian"), "et": ("Eesti", "Estonian"),
    "be": ("Беларуская", "Belarusian"), "ka": ("ქართული", "Georgian"),
    "hy": ("Հայերեն", "Armenian"), "az": ("Azərbaycanca", "Azerbaijani"),
    "kk": ("Қазақша", "Kazakh"), "uz": ("Oʻzbekcha", "Uzbek"),
    "tr": ("Türkçe", "Turkish"), "ar": ("العربية", "Arabic"),
    "iw": ("עברית", "Hebrew"), "fa": ("فارسی", "Persian"),
    "ur": ("اردو", "Urdu"), "hi": ("हिन्दी", "Hindi"),
    "bn": ("বাংলা", "Bengali"), "ta": ("தமிழ்", "Tamil"),
    "te": ("తెలుగు", "Telugu"), "mr": ("मराठी", "Marathi"),
    "gu": ("ગુજરાતી", "Gujarati"), "pa": ("ਪੰਜਾਬੀ", "Punjabi"),
    "ne": ("नेपाली", "Nepali"), "si": ("සිංහල", "Sinhala"),
    "th": ("ไทย", "Thai"), "vi": ("Tiếng Việt", "Vietnamese"),
    "id": ("Bahasa Indonesia", "Indonesian"), "ms": ("Bahasa Melayu", "Malay"),
    "tl": ("Filipino", "Filipino"), "zh-CN": ("中文（简体）", "Simplified Chinese"),
    "zh-TW": ("中文（繁體）", "Traditional Chinese"), "ja": ("日本語", "Japanese"),
    "ko": ("한국어", "Korean"), "mn": ("Монгол", "Mongolian"),
    "km": ("ខ្មែរ", "Khmer"), "my": ("မြန်မာ", "Burmese"),
    "sw": ("Kiswahili", "Swahili"), "am": ("አማርኛ", "Amharic"),
    "af": ("Afrikaans", "Afrikaans"), "so": ("Soomaali", "Somali"),
    "ha": ("Hausa", "Hausa"), "yo": ("Yorùbá", "Yoruba"),
    "zu": ("isiZulu", "Zulu"),
    "sq": ("Shqip", "Albanian"), "eu": ("Euskara", "Basque"),
    "bs": ("Bosanski", "Bosnian"), "ca": ("Català", "Catalan"),
    "ceb": ("Cebuano", "Cebuano"), "ny": ("Chichewa", "Chichewa"),
    "co": ("Corsu", "Corsican"), "eo": ("Esperanto", "Esperanto"),
    "fy": ("Frysk", "Frisian"), "gl": ("Galego", "Galician"),
    "ht": ("Kreyòl ayisyen", "Haitian Creole"), "haw": ("ʻŌlelo Hawaiʻi", "Hawaiian"),
    "hmn": ("Hmoob", "Hmong"), "is": ("Íslenska", "Icelandic"),
    "ig": ("Igbo", "Igbo"), "ga": ("Gaeilge", "Irish"),
    "jw": ("Basa Jawa", "Javanese"), "kn": ("ಕನ್ನಡ", "Kannada"),
    "rw": ("Kinyarwanda", "Kinyarwanda"), "ku": ("Kurdî", "Kurdish"),
    "ky": ("Кыргызча", "Kyrgyz"), "lo": ("ລາວ", "Lao"),
    "la": ("Latina", "Latin"), "lb": ("Lëtzebuergesch", "Luxembourgish"),
    "mk": ("Македонски", "Macedonian"), "mg": ("Malagasy", "Malagasy"),
    "ml": ("മലയാളം", "Malayalam"), "mt": ("Malti", "Maltese"),
    "mi": ("Māori", "Maori"), "or": ("ଓଡ଼ିଆ", "Odia"),
    "ps": ("پښتو", "Pashto"), "sm": ("Gagana Samoa", "Samoan"),
    "gd": ("Gàidhlig", "Scots Gaelic"), "st": ("Sesotho", "Sesotho"),
    "sn": ("chiShona", "Shona"), "sd": ("سنڌي", "Sindhi"),
    "su": ("Basa Sunda", "Sundanese"), "tg": ("Тоҷикӣ", "Tajik"),
    "tt": ("Татарча", "Tatar"), "tk": ("Türkmençe", "Turkmen"),
    "ug": ("ئۇيغۇرچە", "Uyghur"), "cy": ("Cymraeg", "Welsh"),
    "xh": ("isiXhosa", "Xhosa"), "yi": ("ייִדיש", "Yiddish"),
}
RTL = {"ar", "iw", "fa", "ur", "ps", "sd", "ug", "yi"}   # мови справа наліво
_FIRST = ["uk", "ru", "en"]
LANGS_SORTED = {c: LANGS[c] for c in _FIRST + sorted(
    (c for c in LANGS if c not in _FIRST), key=lambda c: LANGS[c][1])}

# Тексти інтерфейсу (для інших мов беруться англійські)
UI = {
    "uk": dict(
        title="Світ за 5 хвилин",
        sub="Новини з усього світу, оновлюються автоматично.",
        upd="Оновлено", wait="Новини завантажуються. Оновіть сторінку за хвилину.",
        tr="Триває переклад, сторінка оновиться сама.",
        foot="Показуємо лише заголовки, короткі підсумки та посилання на джерела.",
        m="{n} хв тому", h="{n} год тому", d="{n} дн тому", sec={}),
    "ru": dict(
        title="Мир за 5 минут",
        sub="Новости со всего мира, обновляются автоматически.",
        upd="Обновлено", wait="Новости загружаются. Обновите страницу через минуту.",
        tr="Идёт перевод, страница обновится сама.",
        foot="Показываем только заголовки, краткие итоги и ссылки на источники.",
        m="{n} мин назад", h="{n} ч назад", d="{n} дн назад",
        sec={"Світ": "Мир", "Україна": "Украина", "Політика": "Политика",
             "Економіка": "Экономика", "Безпека": "Безопасность",
             "Азія": "Азия", "Близький Схід": "Ближний Восток",
             "Африка": "Африка", "Америка": "Америка",
             "Мови світу": "Языки мира"}),
    "en": dict(
        title="The World in 5 Minutes",
        sub="News from around the world, updated automatically.",
        upd="Updated", wait="Loading news. Refresh the page in a minute.",
        tr="Translating, the page will refresh itself.",
        foot="We show only headlines, short summaries and links to sources.",
        m="{n} min ago", h="{n} h ago", d="{n} d ago",
        sec={"Світ": "World", "Україна": "Ukraine", "Політика": "Politics",
             "Економіка": "Economy", "Безпека": "Security",
             "Азія": "Asia", "Близький Схід": "Middle East",
             "Африка": "Africa", "Америка": "Americas",
             "Мови світу": "World languages"}),
}

# Розділ -> список (назва джерела, RSS, мова джерела; без мови = англійська).
FEEDS = {
    "Світ": [
        ("BBC World", "http://feeds.bbci.co.uk/news/world/rss.xml"),
        ("Al Jazeera", "https://www.aljazeera.com/xml/rss/all.xml"),
        ("DW", "https://rss.dw.com/rdf/rss-en-all"),
        ("The Guardian", "https://www.theguardian.com/world/rss"),
    ],
    "Україна": [
        ("Укрінформ", "https://www.ukrinform.ua/rss/block-lastnews", "uk"),
        ("Європейська правда", "https://www.eurointegration.com.ua/rss/", "uk"),
        ("BBC Україна", "https://feeds.bbci.co.uk/ukrainian/rss.xml", "uk"),
    ],
    "Політика": [
        ("Politico EU", "https://www.politico.eu/feed/"),
        ("BBC Politics", "http://feeds.bbci.co.uk/news/politics/rss.xml"),
        ("NPR Politics", "https://feeds.npr.org/1014/rss.xml"),
    ],
    "Економіка": [
        ("BBC Business", "http://feeds.bbci.co.uk/news/business/rss.xml"),
        ("CNBC", "https://www.cnbc.com/id/100003114/device/rss/rss.html"),
    ],
    "Безпека": [
        ("BBC Europe", "http://feeds.bbci.co.uk/news/world/europe/rss.xml"),
        ("Defense News", "https://www.defensenews.com/arc/outboundfeeds/rss/?outputType=xml"),
    ],
    "Азія": [
        ("BBC Asia", "http://feeds.bbci.co.uk/news/world/asia/rss.xml"),
        ("SCMP", "https://www.scmp.com/rss/91/feed"),
        ("Japan Times", "https://www.japantimes.co.jp/feed/"),
    ],
    "Близький Схід": [
        ("BBC Middle East", "http://feeds.bbci.co.uk/news/world/middle_east/rss.xml"),
        ("Times of Israel", "https://www.timesofisrael.com/feed/"),
    ],
    "Африка": [
        ("BBC Africa", "http://feeds.bbci.co.uk/news/world/africa/rss.xml"),
        ("Mail & Guardian", "https://mg.co.za/feed/"),
    ],
    "Америка": [
        ("BBC US & Canada", "http://feeds.bbci.co.uk/news/world/us_and_canada/rss.xml"),
        ("BBC Latin America", "http://feeds.bbci.co.uk/news/world/latin_america/rss.xml"),
        ("NPR", "https://feeds.npr.org/1001/rss.xml"),
    ],
    "Мови світу": [
        ("BBC Mundo · ES", "https://feeds.bbci.co.uk/mundo/rss.xml", "es"),
        ("El País · ES", "https://feeds.elpais.com/mrss-s/pages/ep/site/elpais.com/portada", "es"),
        ("Le Monde · FR", "https://www.lemonde.fr/rss/une.xml", "fr"),
        ("France 24 · FR", "https://www.france24.com/fr/rss", "fr"),
        ("Tagesschau · DE", "https://www.tagesschau.de/index~rss2.xml", "de"),
        ("ANSA · IT", "https://www.ansa.it/sito/notizie/mondo/mondo_rss.xml", "it"),
        ("BBC Brasil · PT", "https://feeds.bbci.co.uk/portuguese/rss.xml", "pt"),
        ("BBC Türkçe · TR", "https://feeds.bbci.co.uk/turkce/rss.xml", "tr"),
        ("BBC Arabic · AR", "https://feeds.bbci.co.uk/arabic/rss.xml", "ar"),
        ("BBC Persian · FA", "https://feeds.bbci.co.uk/persian/rss.xml", "fa"),
        ("BBC Hindi · HI", "https://feeds.bbci.co.uk/hindi/rss.xml", "hi"),
        ("BBC Indonesia · ID", "https://feeds.bbci.co.uk/indonesia/rss.xml", "id"),
        ("BBC Korean · KO", "https://feeds.bbci.co.uk/korean/rss.xml", "ko"),
        ("BBC Chinese · ZH", "https://feeds.bbci.co.uk/zhongwen/simp/rss.xml", "zh-CN"),
        ("NHK · JA", "https://www3.nhk.or.jp/rss/news/cat6.xml", "ja"),
        ("BBC Russian · RU", "https://feeds.bbci.co.uk/russian/rss.xml", "ru"),
    ],
}

app = Flask(__name__)
STATE = {"updated": None, "sections": {}}
LOCK = threading.Lock()
TR = {}            # (мова, посилання) -> (заголовок, підсумок)
PENDING = set()    # мови, які зараз перекладаються
ACTIVE = {DEFAULT_LANG: time.time()}   # мова -> коли востаннє просили


def clean(text, limit=220):
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = re.sub(r"\s+", " ", html.unescape(text)).strip()
    return text if len(text) <= limit else text[: limit - 1].rsplit(" ", 1)[0] + "…"


FEED_ERRORS = {}   # джерело -> остання помилка
FEED_UA = "Mozilla/5.0 (compatible; WorldNewsBot/1.0)"


def read_feed(source, url):
    """Завантажує одну стрічку з таймаутом, щоб одне джерело не зависало все."""
    try:
        r = requests.get(url, headers={"User-Agent": FEED_UA}, timeout=12)
        r.raise_for_status()
        FEED_ERRORS.pop(source, None)
        return feedparser.parse(r.content).entries
    except Exception as exc:
        FEED_ERRORS[source] = str(exc)[:90]
        print(f"[feed error] {source}: {exc}")
        return []


def fetch_section(feeds):
    with ThreadPoolExecutor(8) as pool:
        results = list(pool.map(lambda f: read_feed(f[0], f[1]), feeds))
    items, seen = [], set()
    for feed, entries in zip(feeds, results):
        source = feed[0]
        src = feed[2] if len(feed) > 2 else "en"
        for e in entries[:PER_FEED]:
            title = clean(e.get("title"), 160)
            link = e.get("link")
            key = re.sub(r"\W+", "", title.lower())[:60]
            if not title or not link or key in seen:
                continue
            seen.add(key)
            ts = e.get("published_parsed") or e.get("updated_parsed")
            items.append({
                "title": title,
                "snippet": clean(e.get("summary")),
                "link": link,
                "source": source,
                "src": src,
                "ts": calendar.timegm(ts) if ts else 0,
            })
    items.sort(key=lambda x: x["ts"], reverse=True)
    return items[:max(PER_SECTION, len(feeds) * 2)]


# ---------- переклад ----------

def translate_claude(items, lang):
    """Переклад через Claude (потрібен ключ), пачками по 15."""
    name = LANGS[lang][1]
    for start in range(0, len(items), 15):
        chunk = items[start:start + 15]
        payload = [{"i": i, "title": n["title"], "text": n["snippet"]}
                   for i, n in enumerate(chunk)]
        r = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key": os.environ["ANTHROPIC_API_KEY"],
                     "anthropic-version": "2023-06-01",
                     "content-type": "application/json"},
            json={"model": MODEL, "max_tokens": 4000,
                  "system": (f"You are a news editor. Texts may be in any language. "
                             f"For each item write a headline in {name} (max 90 chars) "
                             f"and a one-sentence summary in {name}, neutral, nothing "
                             f"invented. If already in {name}, keep it. Reply with "
                             'JSON only: [{"i":0,"title":"...","summary":"..."}].'),
                  "messages": [{"role": "user",
                                "content": json.dumps(payload, ensure_ascii=False)}]},
            timeout=120)
        r.raise_for_status()
        raw = re.sub(r"\x60{3}(?:json)?", "", r.json()["content"][0]["text"]).strip()
        for row in json.loads(raw):
            n = chunk[row["i"]]
            if row.get("title"):
                TR[(lang, n["link"])] = (row["title"], row.get("summary", ""))


UI["uk"]["fail"] = "Переклад тимчасово недоступний, повторимо за кілька хвилин."
UI["ru"]["fail"] = "Перевод временно недоступен, повторим через несколько минут."
UI["en"]["fail"] = "Translation is temporarily unavailable, retrying in a few minutes."

RATE_LOCK = threading.Lock()
LAST_CALL = [0.0]
LAST_ERROR = [""]
FAIL_AT = {}      # мова -> коли востаннє не вдалося перекласти
GT_URL = "https://translate.googleapis.com/translate_a/single"
GT_HEADERS = {"User-Agent": "Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 "
                            "(KHTML, like Gecko) Chrome/120 Mobile Safari/537.36"}


def throttle(gap=0.6):
    """Не частіше ~1.5 запиту на секунду, щоб Google не блокував."""
    with RATE_LOCK:
        wait = LAST_CALL[0] + gap - time.time()
        if wait > 0:
            time.sleep(wait)
        LAST_CALL[0] = time.time()


def gt_call(text, lang, src="auto"):
    """Один запит до безкоштовного Google Translate."""
    last = None
    for attempt in range(4):
        try:
            throttle()
            r = requests.get(GT_URL, headers=GT_HEADERS, timeout=25,
                             params={"client": "gtx", "sl": src, "tl": lang,
                                     "dt": "t", "q": text})
            r.raise_for_status()
            return "".join(seg[0] for seg in r.json()[0] if seg and seg[0])
        except Exception as exc:
            last = exc
            LAST_ERROR[0] = f"{lang}: {str(exc)[:100]}"
            print(f"[translate error] {LAST_ERROR[0]}")
            time.sleep(3 * (attempt + 1))
    raise RuntimeError(str(last))


def gt_batch(texts, lang, src="auto"):
    """Перекладає багато рядків за кілька запитів. Віддає (номер, переклад)."""
    chunks, cur, size = [], [], 0
    for i, t in enumerate(texts):
        enc = len(quote(t))
        if cur and (len(cur) >= 25 or size + enc > 5000):
            chunks.append(cur)
            cur, size = [], 0
        cur.append(i)
        size += enc
    if cur:
        chunks.append(cur)
    for idx in chunks:
        res = gt_call("\n".join(texts[i] for i in idx), lang, src).split("\n")
        if len(res) == len(idx):
            for i, text in zip(idx, res):
                if text.strip():
                    yield i, text.strip()
        else:  # рядки злиплися: перекладаємо по одному
            for i in idx:
                text = gt_call(texts[i], lang, src).strip()
                if text:
                    yield i, text


def translate_free(items, lang):
    """Спочатку заголовки (швидко), потім описи. Мова джерела відома заздалегідь."""
    todo = []
    for n in items:
        if n.get("src", "en") == lang:
            TR[(lang, n["link"])] = (n["title"], n["snippet"])
        else:
            todo.append(n)
    groups = {}
    for n in todo:
        groups.setdefault(n.get("src", "en"), []).append(n)
    for src, group in groups.items():
        for i, text in gt_batch([n["title"] for n in group], lang, src):
            TR[(lang, group[i]["link"])] = (text, group[i]["snippet"])
    for src, group in groups.items():
        part = [n for n in group if n["snippet"] and (lang, n["link"]) in TR]
        for i, text in gt_batch([n["snippet"] for n in part], lang, src):
            key = (lang, part[i]["link"])
            TR[key] = (TR[key][0], text)
    for n in todo:
        TR.setdefault((lang, n["link"]), (n["title"], n["snippet"]))


UI_TR = {}
UI_KEYS = ["title", "sub", "upd", "wait", "tr", "foot"]


def get_ui(lang):
    return UI.get(lang) or UI_TR.get(lang) or UI["en"]


def translate_ui(lang):
    """Інтерфейс для мов, яких немає в UI: один запит."""
    if lang in UI or lang in UI_TR:
        return
    en = UI["en"]
    secs = list(en["sec"].items())
    texts = [en[k] for k in UI_KEYS] + [name for _, name in secs]
    res = dict(gt_batch(texts, lang, "en"))
    if not res.get(0):
        return
    ui = {k: res.get(i) or en[k] for i, k in enumerate(UI_KEYS)}
    ui["sec"] = {ua: res.get(len(UI_KEYS) + j) or name
                 for j, (ua, name) in enumerate(secs)}
    UI_TR[lang] = ui


def all_items():
    with LOCK:
        return [n for sec in STATE["sections"].values() for n in sec]


def translate_lang(lang):
    try:
        translate_ui(lang)
        todo = [n for n in all_items() if (lang, n["link"]) not in TR]
        if SUMMARIZE and todo:
            try:
                translate_claude(todo, lang)
            except Exception as exc:
                print(f"[claude error] {exc}")
        rest = [n for n in todo if (lang, n["link"]) not in TR]
        if rest:
            translate_free(rest, lang)
        FAIL_AT.pop(lang, None)
        print(f"[ok] переклад {lang} готовий")
    except Exception as exc:
        FAIL_AT[lang] = time.time()
        print(f"[translate failed] {lang}: {exc}")
    finally:
        with LOCK:
            PENDING.discard(lang)


def start_translate(lang):
    """Запускає переклад у фоні, якщо є що перекладати."""
    with LOCK:
        if lang in PENDING:
            return
        if time.time() - FAIL_AT.get(lang, 0) < 120:
            return
        missing = (lang not in UI and lang not in UI_TR) or any(
            (lang, n["link"]) not in TR
            for sec in STATE["sections"].values() for n in sec)
        if not missing:
            return
        PENDING.add(lang)
    threading.Thread(target=translate_lang, args=(lang,), daemon=True).start()


# ---------- оновлення ----------

def refresh():
    for name, feeds in FEEDS.items():
        items = fetch_section(feeds)
        with LOCK:
            STATE["sections"] = {**STATE["sections"],
                                 name: items or STATE["sections"].get(name, [])}
            STATE["updated"] = datetime.now(timezone.utc)
    print(f"[ok] оновлено {datetime.now():%H:%M}")
    now = time.time()
    for lang, last in list(ACTIVE.items()):
        if lang == DEFAULT_LANG or now - last < 12 * 3600:
            start_translate(lang)


def loop():
    while True:
        try:
            refresh()
        except Exception as exc:
            print(f"[loop error] {exc}")
        time.sleep(REFRESH_MINUTES * 60)


# ---------- сторінка ----------

PAGE = """<!doctype html>
<html lang="{{ lang }}" dir="{{ 'rtl' if lang in rtl else 'ltr' }}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
{% if pending or failed %}<meta http-equiv="refresh" content="20">{% endif %}
<title>{{ ui.title }}</title>
<script>
try{if(!location.search&&localStorage.lang)location.replace('?lang='+localStorage.lang+location.hash)}catch(e){}
</script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Source+Serif+4:wght@400;600;700&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--bg:#f3f5f8;--card:#fff;--ink:#16202e;--mute:#5d6b7e;--line:#d9dfe8;--accent:#1f4fd8}
@media (prefers-color-scheme:dark){:root{--bg:#10151d;--card:#18202b;--ink:#e8edf4;--mute:#93a1b5;--line:#2a3544;--accent:#7ea2ff}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.5 Inter,system-ui,sans-serif}
header{padding:24px 20px 12px;max-width:820px;margin:auto}
.top{display:flex;justify-content:flex-end}
select{background:var(--card);color:var(--ink);border:1px solid var(--line);border-radius:8px;padding:6px 10px;font:500 14px Inter,system-ui,sans-serif}
h1{font:700 clamp(30px,6vw,46px)/1.05 "Source Serif 4",Georgia,serif;margin:10px 0 6px}
.sub{color:var(--mute);font-size:14px}
.note{margin-top:10px;padding:8px 12px;border-radius:8px;background:var(--card);border:1px solid var(--line);font-size:14px}
nav{position:sticky;top:0;background:var(--bg);border-bottom:1px solid var(--line);z-index:5}
nav div{max-width:820px;margin:auto;display:flex;gap:6px;overflow-x:auto;padding:10px 20px}
nav button{border:1px solid var(--line);background:var(--card);color:var(--ink);padding:7px 14px;border-radius:999px;font:500 14px Inter,system-ui,sans-serif;cursor:pointer;white-space:nowrap}
nav button[aria-pressed=true]{background:var(--accent);border-color:var(--accent);color:#fff}
nav button:focus-visible,select:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
main{max-width:820px;margin:auto;padding:8px 20px 60px}
section{display:none}section.on{display:block}
article{padding:18px 0;border-bottom:1px solid var(--line)}
article h2{font:600 20px/1.3 "Source Serif 4",Georgia,serif;margin:0 0 6px}
article h2 a{color:inherit;text-decoration:none}
article h2 a:hover{color:var(--accent)}
article p{margin:0 0 6px}
.meta{font-size:13px;color:var(--mute)}
.empty{padding:40px 0;color:var(--mute)}
footer{max-width:820px;margin:auto;padding:0 20px 40px;color:var(--mute);font-size:13px}
</style>
</head>
<body>
<header>
  <div class="top">
    <select id="lang" aria-label="Language">
      {% for code, (label, _) in langs.items() %}<option value="{{ code }}" {{ 'selected' if code == lang }}>{{ label }}</option>{% endfor %}
    </select>
  </div>
  <h1>{{ ui.title }}</h1>
  <div class="sub">{{ ui.sub }} {% if updated %}{{ ui.upd }} {{ updated }} (UTC).{% endif %}</div>
  {% if pending %}<div class="note">{{ ui.tr }} ({{ progress }})</div>{% elif failed %}<div class="note">{{ ui.fail or 'Translation is temporarily unavailable, retrying soon.' }}</div>{% endif %}
</header>
<nav><div id="tabs">
  {% for name in sections %}<button aria-pressed="{{ 'true' if loop.first else 'false' }}" data-t="{{ loop.index0 }}">{{ ui.sec.get(name, name) }}</button>{% endfor %}
</div></nav>
<main>
{% for name, items in sections.items() %}
<section class="{{ 'on' if loop.first }}" id="s{{ loop.index0 }}">
  {% if not items %}<div class="empty">{{ ui.wait }}</div>{% endif %}
  {% for n in items %}
  <article>
    <h2><a href="{{ n.link }}" target="_blank" rel="noopener">{{ n.t }}</a></h2>
    <p>{{ n.s }}</p>
    <div class="meta">{{ n.source }}{% if n.when %} · {{ n.when }}{% endif %}</div>
  </article>
  {% endfor %}
</section>
{% endfor %}
</main>
<footer>{{ ui.foot }}</footer>
<script>
const tabs=[...document.querySelectorAll('#tabs button')],secs=[...document.querySelectorAll('section')];
function show(i){tabs.forEach((x,k)=>x.setAttribute('aria-pressed',k==i));secs.forEach((s,k)=>s.classList.toggle('on',k==i))}
tabs.forEach((b,i)=>b.onclick=()=>{show(i);history.replaceState(null,'','#'+i)});
const h=parseInt(location.hash.slice(1));if(h>=0&&h<tabs.length)show(h);
document.getElementById('lang').onchange=e=>{try{localStorage.lang=e.target.value}catch(x){}
location.href='?lang='+e.target.value+location.hash};
</script>
</body></html>"""


def ago(ts, ui):
    mins = int((time.time() - ts) / 60)
    if mins < 60:
        return ui["m"].format(n=max(mins, 1))
    if mins < 1440:
        return ui["h"].format(n=mins // 60)
    return ui["d"].format(n=mins // 1440)


def stamp(ts, ui):
    if "m" in ui:
        return ago(ts, ui)
    return datetime.fromtimestamp(ts, timezone.utc).strftime("%d.%m %H:%M UTC")


@app.route("/")
def index():
    lang = request.args.get("lang", DEFAULT_LANG)
    if lang not in LANGS:
        lang = DEFAULT_LANG
    ACTIVE[lang] = time.time()
    start_translate(lang)
    ui = get_ui(lang)
    with LOCK:
        raw = {k: list(v) for k, v in STATE["sections"].items()}
        updated = STATE["updated"].strftime("%d.%m %H:%M") if STATE["updated"] else None
        pending = lang in PENDING
    sections = {}
    for name, items in raw.items():
        rows = []
        for n in items:
            t, s = TR.get((lang, n["link"]), (n["title"], n["snippet"]))
            rows.append(dict(n, t=t, s=s, when=stamp(n["ts"], ui) if n["ts"] else ""))
        sections[name] = rows
    if not sections:
        sections = {k: [] for k in FEEDS}
    total = sum(len(v) for v in raw.values())
    done = sum(1 for v in raw.values() for n in v if (lang, n["link"]) in TR)
    failed = (not pending) and time.time() - FAIL_AT.get(lang, 0) < 300
    return render_template_string(PAGE, sections=sections, updated=updated, ui=ui,
                                  lang=lang, langs=LANGS_SORTED, pending=pending, rtl=RTL,
                                  progress=f"{done}/{total}", failed=failed)


@app.route("/status")
def status():
    items = all_items()
    langs = {l: {"done": sum((l, n["link"]) in TR for n in items),
                 "total": len(items), "pending": l in PENDING}
             for l in list(ACTIVE)}
    return jsonify(items=len(items), langs=langs, last_error=LAST_ERROR[0],
                   feed_errors=FEED_ERRORS,
                   updated=str(STATE["updated"]))


@app.route("/api/news")
def api():
    with LOCK:
        return jsonify(STATE["sections"])


# ---------- Telegram-бот (працює, якщо задано змінну BOT_TOKEN) ----------
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
BOT_SECRET = hashlib.sha256(BOT_TOKEN.encode()).hexdigest()[:24] if BOT_TOKEN else ""
BOT_LANGS = ["uk", "ru", "en", "pl", "de", "es", "fr", "it", "tr", "ar", "zh-CN", "ja"]
SEC_NAMES = list(FEEDS)   # порядок розділів


def tg(method, **params):
    if not BOT_TOKEN:
        return None
    try:
        r = requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}",
                          json=params, timeout=15)
        return r.json()
    except Exception as exc:
        print(f"[telegram error] {exc}")
        return None


def tg_menu(lang):
    ui = get_ui(lang)
    names = [ui.get("sec", {}).get(n, n) for n in SEC_NAMES]
    rows = []
    for i in range(0, len(names), 2):
        rows.append([{"text": names[j], "callback_data": f"n|{lang}|{j}"}
                     for j in range(i, min(i + 2, len(names)))])
    rows.append([{"text": "🌐 " + LANGS[lang][0], "callback_data": f"l|{lang}"}])
    text = f"<b>{html.escape(ui['title'])}</b>\n{html.escape(ui['sub'])}"
    return text, {"inline_keyboard": rows}


def tg_langs():
    rows, row = [], []
    for code in BOT_LANGS:
        row.append({"text": LANGS[code][0], "callback_data": f"m|{code}"})
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    return "🌐 Language / Мова", {"inline_keyboard": rows}


def tg_news(lang, idx):
    ACTIVE[lang] = time.time()
    start_translate(lang)
    ui = get_ui(lang)
    name = ui.get("sec", {}).get(SEC_NAMES[idx], SEC_NAMES[idx])
    with LOCK:
        items = list(STATE["sections"].get(SEC_NAMES[idx], []))[:8]
    back = {"inline_keyboard": [[{"text": "⬅", "callback_data": f"m|{lang}"}]]}
    if not items:
        return html.escape(ui["wait"]), back
    lines = []
    for n in items:
        title = TR.get((lang, n["link"]), (n["title"], ""))[0]
        lines.append(f'• <a href="{html.escape(n["link"], quote=True)}">'
                     f'{html.escape(title)}</a> <i>{html.escape(n["source"])}</i>')
    return f"<b>{html.escape(name)}</b>\n\n" + "\n\n".join(lines), back


def tg_handle(upd):
    msg, cb = upd.get("message"), upd.get("callback_query")
    if msg:
        code = ((msg.get("from") or {}).get("language_code") or "").split("-")[0]
        lang = code if code in LANGS else DEFAULT_LANG
        ACTIVE[lang] = time.time()
        start_translate(lang)
        text, markup = tg_menu(lang)
        tg("sendMessage", chat_id=msg["chat"]["id"], text=text, parse_mode="HTML",
           reply_markup=markup, link_preview_options={"is_disabled": True})
    elif cb:
        tg("answerCallbackQuery", callback_query_id=cb["id"])
        parts = (cb.get("data") or "").split("|")
        kind = parts[0]
        lang = parts[1] if len(parts) > 1 and parts[1] in LANGS else DEFAULT_LANG
        if kind == "n" and len(parts) > 2 and parts[2].isdigit() and int(parts[2]) < len(SEC_NAMES):
            text, markup = tg_news(lang, int(parts[2]))
        elif kind == "l":
            text, markup = tg_langs()
        else:
            ACTIVE[lang] = time.time()
            start_translate(lang)
            text, markup = tg_menu(lang)
        tg("editMessageText", chat_id=cb["message"]["chat"]["id"],
           message_id=cb["message"]["message_id"], text=text, parse_mode="HTML",
           reply_markup=markup, link_preview_options={"is_disabled": True})


@app.route("/tg/<secret>", methods=["POST"])
def tg_hook(secret):
    if not BOT_TOKEN or secret != BOT_SECRET:
        return "no", 403
    try:
        tg_handle(request.get_json(force=True, silent=True) or {})
    except Exception as exc:
        print(f"[telegram error] {exc}")
    return "ok"


@app.route("/tg-setup")
def tg_setup():
    if not BOT_TOKEN:
        return "Додайте змінну BOT_TOKEN у Render (Environment) і відкрийте цю сторінку ще раз.", 400
    url = request.host_url.replace("http://", "https://") + "tg/" + BOT_SECRET
    return jsonify(tg("setWebhook", url=url, allowed_updates=["message", "callback_query"]))


threading.Thread(target=loop, daemon=True).start()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", 8000)))
