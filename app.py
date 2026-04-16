import html as html_std
import json
import os
import random
import re
import smtplib
import threading
import unicodedata
import sqlite3
import ssl
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from concurrent.futures import ThreadPoolExecutor
from email.message import EmailMessage
from flask import Flask, jsonify, make_response, request, render_template, g
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATABASE = os.path.join(BASE_DIR, 'data', 'amenah.db')
SCHEMA_FILE = os.path.join(BASE_DIR, 'sql', 'schema.sql')
MYSQL_HOST = (os.environ.get('MYSQL_HOST') or '').strip()
USE_MYSQL = bool(MYSQL_HOST) and (os.environ.get('AMENAH_USE_SQLITE') or '').strip() not in ('1', 'true', 'yes')

def _mysql_connect():
    try:
        import pymysql
        from pymysql.cursors import DictCursor
    except ImportError as e:
        raise RuntimeError('MYSQL_HOST est défini mais pymysql est absent. Installez : pip install pymysql') from e
    dbname = (os.environ.get('MYSQL_DATABASE') or os.environ.get('MYSQL_DB') or 'amenah').strip()
    return pymysql.connect(host=MYSQL_HOST, user=(os.environ.get('MYSQL_USER') or 'root').strip(), password=os.environ.get('MYSQL_PASSWORD') or '', database=dbname, charset='utf8mb4', cursorclass=DictCursor)

def get_db():
    if 'db' not in g:
        if USE_MYSQL:
            g.db = _mysql_connect()
        else:
            os.makedirs(os.path.dirname(DATABASE), exist_ok=True)
            g.db = sqlite3.connect(DATABASE)
            g.db.row_factory = sqlite3.Row
    return g.db

def db_exec(db, sql, params=None):
    params = params or ()
    if USE_MYSQL:
        sql = sql.replace('?', '%s')
        cur = db.cursor()
        cur.execute(sql, params)
        return cur
    return db.execute(sql, params)

def close_db(e=None):
    db = g.pop('db', None)
    if db is not None:
        db.close()

def _slugify_donation_slug(text: str) -> str:
    if not (text or '').strip():
        return 'organisme'
    s = unicodedata.normalize('NFKD', str(text))
    s = s.encode('ascii', 'ignore').decode('ascii')
    s = s.lower().strip()
    s = re.sub('[^a-z0-9]+', '-', s)
    s = re.sub('-+', '-', s).strip('-')
    return s[:80] if s else 'organisme'

def _unique_donation_slug(db, base: str) -> str:
    base = (base or 'organisme')[:80]
    n = 0
    while n < 60:
        cand = base if n == 0 else f'{base}-{n}'
        cur = db_exec(db, 'SELECT 1 FROM donation_agencies WHERE slug = ?', (cand,))
        if not cur.fetchone():
            return cand
        n += 1
    return f'{base}-{random.randint(10000, 99999)}'

def _next_donation_sort_order(db):
    cur = db_exec(db, 'SELECT COALESCE(MAX(sort_order), 0) + 1 AS n FROM donation_agencies')
    row = cur.fetchone()
    if not row:
        return 1
    r = dict(row)
    return int(r.get('n') or 1)

def _generate_ean13() -> str:
    digits = [random.randint(0, 9) for _ in range(12)]
    s = sum((digits[i] * (1 if i % 2 == 0 else 3) for i in range(12)))
    check = (10 - s % 10) % 10
    return ''.join(map(str, digits)) + str(check)

def init_db():
    if USE_MYSQL:
        return
    os.makedirs(os.path.dirname(DATABASE), exist_ok=True)
    conn = sqlite3.connect(DATABASE)
    with open(SCHEMA_FILE, 'r', encoding='utf-8') as f:
        conn.executescript(f.read())
    try:
        conn.execute("ALTER TABLE waiting ADD COLUMN suggestion_type TEXT NOT NULL DEFAULT 'boycott'")
    except sqlite3.OperationalError as e:
        if 'duplicate column' not in str(e).lower():
            raise
    try:
        conn.execute('ALTER TABLE produits ADD COLUMN code_barre TEXT')
    except sqlite3.OperationalError as e:
        if 'duplicate column' not in str(e).lower():
            raise
    conn.commit()
    conn.close()
app = Flask(__name__, template_folder=os.path.join(BASE_DIR, 'templates'), static_folder=os.path.join(BASE_DIR, 'static'), static_url_path='/static')
app.teardown_appcontext(close_db)
with app.app_context():
    init_db()
FEEDBACK_EMAIL_DEFAULT_TO = 'amenah@amenah.com'
GAZA_NEWS_RSS = (('https://feeds.bbci.co.uk/news/world/middle_east/rss.xml', 'BBC News', False), ('https://www.aljazeera.com/xml/rss/all.xml', 'Al Jazeera', False))
GAZA_NEWS_TTL_SEC = 300
_gaza_news_cache: dict = {'t': 0.0, 'payload': None}
GAZA_KEYWORDS = ('gaza', 'rafah', 'palestin', 'palestinian', 'israel', 'israeli', 'west bank', 'jerusalem', 'hamas', 'idf', 'occupation', 'settler', 'netanyahu', 'al-aqsa', 'hebron', 'jenin', 'nablus')

def _fetch_rss_bytes(url: str) -> bytes:
    req = urllib.request.Request(url, headers={'User-Agent': 'AmenahGazaNews/1.0 (+https://github.com/)', 'Accept': 'application/rss+xml, application/xml, text/xml, */*'})
    with urllib.request.urlopen(req, timeout=20) as resp:
        return resp.read()

def _strip_tags(html: str) -> str:
    t = re.sub('<[^>]+>', ' ', html or '')
    t = html_std.unescape(re.sub('\\s+', ' ', t).strip())
    return t

def _img_from_description(desc: str):
    m = re.search('src=["\\\']([^"\\\']+)["\\\']', desc or '', re.I)
    if not m:
        return None
    return m.group(1).replace('&amp;', '&').strip()
_NS_CONTENT_ENCODED = '{http://purl.org/rss/1.0/modules/content/}encoded'
_OG_IMAGE_RES = (re.compile('property=["\\\']og:image["\\\']\\s+content=["\\\']([^"\\\']+)["\\\']', re.I), re.compile('content=["\\\']([^"\\\']+)["\\\']\\s+property=["\\\']og:image["\\\']', re.I))
_og_image_cache = {}
_og_lock = threading.Lock()

def _fetch_og_image(page_url: str):
    try:
        req = urllib.request.Request(page_url, headers={'User-Agent': 'Mozilla/5.0 (compatible; AmenahNews/1.1)'})
        with urllib.request.urlopen(req, timeout=12) as resp:
            chunk = resp.read(200000)
        text = chunk.decode('utf-8', 'replace')
        for rx in _OG_IMAGE_RES:
            m = rx.search(text)
            if m:
                return html_std.unescape(m.group(1).strip())
    except Exception:
        pass
    return None

def _enrich_news_images_missing(items, max_fetch=20, workers=5):
    need = [it for it in items if not it.get('image')][:max_fetch]
    if not need:
        return

    def fill_one(it):
        url = (it.get('link') or '').strip()
        if not url:
            return
        with _og_lock:
            if url in _og_image_cache:
                got = _og_image_cache[url]
                if got:
                    it['image'] = got
                return
        img = _fetch_og_image(url)
        with _og_lock:
            _og_image_cache[url] = img
        if img:
            it['image'] = img
    with ThreadPoolExecutor(max_workers=workers) as pool:
        pool.map(fill_one, need)

def _parse_rss_items(xml_bytes, source_label, take_all):
    try:
        root = ET.fromstring(xml_bytes)
    except ET.ParseError:
        return []
    channel = root.find('channel')
    if channel is None:
        return []
    ns_media = '{http://search.yahoo.com/mrss/}'
    out = []
    for item in channel.findall('item'):
        title_el = item.find('title')
        raw_title = ''.join(title_el.itertext()).strip() if title_el is not None else ''
        title = _strip_tags(raw_title) or (item.findtext('title') or '').strip()
        title = html_std.unescape(title)
        link = (item.findtext('link') or '').strip()
        if not title or not link:
            continue
        pub = (item.findtext('pubDate') or '').strip()
        desc = (item.findtext('description') or '').strip()
        summary = _strip_tags(desc)
        if len(summary) > 280:
            summary = summary[:277] + '…'
        img = _img_from_description(desc)
        if not img:
            enc = item.find(_NS_CONTENT_ENCODED)
            if enc is not None and enc.text:
                img = _img_from_description(enc.text)
        if not img:
            for thumb in item.findall(f'{ns_media}thumbnail'):
                u = thumb.get('url')
                if u:
                    img = u.strip()
                    break
        if not img:
            enc_el = item.find('enclosure')
            if enc_el is not None:
                typ = (enc_el.get('type') or '').lower()
                if typ.startswith('image/') and enc_el.get('url'):
                    img = enc_el.get('url').strip()
        blob = (title + ' ' + summary).lower()
        if not take_all:
            if not any((k in blob for k in GAZA_KEYWORDS)):
                continue
            off_topic = ('ukraine', 'russia', 'putin', 'zelensky', 'moscow', 'kyiv', 'nato')
            if any((o in blob for o in off_topic)) and (not any((z in blob for z in ('gaza', 'palestin', 'israel', 'rafah', 'west bank', 'jerusalem', 'hamas')))):
                continue
        dt_iso = None
        if pub:
            try:
                dt = parsedate_to_datetime(pub)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                dt_iso = dt.isoformat()
            except (TypeError, ValueError, OverflowError):
                dt_iso = None
        out.append({'title': title, 'link': link, 'source': source_label, 'published_at': dt_iso, 'summary': summary or None, 'image': img})
    return out

def _merge_gaza_news():
    merged = []
    for (url, label, take_all) in GAZA_NEWS_RSS:
        try:
            raw = _fetch_rss_bytes(url)
            merged.extend(_parse_rss_items(raw, label, take_all))
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            app.logger.warning('RSS indisponible %s : %s', url, e)
    seen = set()
    unique = []
    for it in merged:
        key = it['link'].split('?', 1)[0].rstrip('/')
        if key in seen:
            continue
        seen.add(key)
        unique.append(it)

    def sort_key(x):
        if x.get('published_at'):
            try:
                return x['published_at']
            except Exception:
                pass
        return ''
    unique.sort(key=sort_key, reverse=True)
    sliced = unique[:28]
    _enrich_news_images_missing(sliced)
    return sliced

@app.route('/api/gaza-news', methods=['GET'])
def gaza_news():
    now = time.monotonic()
    if _gaza_news_cache['payload'] is not None and now - _gaza_news_cache['t'] < GAZA_NEWS_TTL_SEC:
        return jsonify(_gaza_news_cache['payload'])
    try:
        items = _merge_gaza_news()
        payload = {'ok': True, 'items': items}
    except Exception:
        app.logger.exception('gaza_news')
        payload = {'ok': False, 'error': 'Impossible de charger les flux pour le moment.', 'items': []}
    _gaza_news_cache['t'] = now
    _gaza_news_cache['payload'] = payload
    return jsonify(payload)

def _send_feedback_email(message: str, feedback_id: int, created_at: str) -> bool:
    to_addr = (os.environ.get('FEEDBACK_EMAIL_TO') or FEEDBACK_EMAIL_DEFAULT_TO).strip()
    smtp_host = (os.environ.get('SMTP_HOST') or '').strip()
    if not smtp_host:
        app.logger.warning('Feedback id=%s enregistré mais SMTP_HOST absent : aucun e-mail envoyé.', feedback_id)
        return False
    smtp_port = int(os.environ.get('SMTP_PORT', '587'))
    smtp_user = (os.environ.get('SMTP_USER') or '').strip()
    smtp_password = os.environ.get('SMTP_PASSWORD') or ''
    use_tls = os.environ.get('SMTP_USE_TLS', '1').strip().lower() not in ('0', 'false', 'no', 'off')
    mail_from = (os.environ.get('SMTP_FROM') or smtp_user or 'noreply@amenah.com').strip()
    subject = f'[Amenah] Nouveau feedback #{feedback_id}'
    body = f'Un message a été envoyé depuis le formulaire Feedback du site.\n\nID : {feedback_id}\nDate (UTC) : {created_at}\n\n---\n{message}\n---\n'
    msg = EmailMessage()
    msg['Subject'] = subject
    msg['From'] = mail_from
    msg['To'] = to_addr
    msg.set_content(body, charset='utf-8')
    try:
        if smtp_port == 465:
            context = ssl.create_default_context()
            with smtplib.SMTP_SSL(smtp_host, smtp_port, context=context) as smtp:
                if smtp_user:
                    smtp.login(smtp_user, smtp_password)
                smtp.send_message(msg)
        else:
            with smtplib.SMTP(smtp_host, smtp_port, timeout=30) as smtp:
                smtp.ehlo()
                if use_tls:
                    smtp.starttls(context=ssl.create_default_context())
                    smtp.ehlo()
                if smtp_user:
                    smtp.login(smtp_user, smtp_password)
                smtp.send_message(msg)
        app.logger.info('E-mail feedback envoyé vers %s (id=%s).', to_addr, feedback_id)
        return True
    except Exception:
        app.logger.exception('Échec envoi e-mail feedback id=%s', feedback_id)
        return False

@app.before_request
def api_cors_preflight():
    if request.path.startswith('/api/') and request.method == 'OPTIONS':
        r = make_response('', 204)
        r.headers['Access-Control-Allow-Origin'] = '*'
        r.headers['Access-Control-Allow-Methods'] = 'GET, POST, OPTIONS'
        r.headers['Access-Control-Allow-Headers'] = 'Content-Type'
        return r

@app.after_request
def api_cors_headers(resp):
    if request.path.startswith('/api/'):
        resp.headers['Access-Control-Allow-Origin'] = '*'
    return resp

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/admin')
def admin():
    return render_template('admin.html')

@app.route('/api/suggestion', methods=['POST'])
def add_suggestion():
    data = request.get_json(silent=True) or {}
    nom = (data.get('nom') or '').strip()
    if not nom:
        return (jsonify({'ok': False, 'error': 'Le nom du produit est requis.'}), 400)
    categorie = (data.get('categorie') or '').strip() or None
    description = (data.get('description') or '').strip() or None
    lien_source = (data.get('lien_source') or '').strip() or None
    email_contact = (data.get('email_contact') or '').strip() or None
    st = (data.get('suggestion_type') or 'boycott').strip().lower()
    if st not in ('boycott', 'alternative'):
        st = 'boycott'
    now = datetime.utcnow().isoformat() + 'Z'
    db = get_db()
    cur = db_exec(db, "\n        INSERT INTO waiting (nom, categorie, description, lien_source, email_contact, created_at, statut, suggestion_type)\n        VALUES (?, ?, ?, ?, ?, ?, 'en_attente', ?)\n        ", (nom, categorie, description, lien_source, email_contact, now, st))
    db.commit()
    return jsonify({'ok': True, 'id': cur.lastrowid, 'storage': 'mysql' if USE_MYSQL else 'sqlite'})

@app.route('/api/waiting', methods=['GET'])
def list_waiting():
    db = get_db()
    cur = db_exec(db, 'SELECT id, nom, categorie, description, lien_source, email_contact, created_at, statut, suggestion_type FROM waiting ORDER BY id DESC')
    rows = cur.fetchall()
    return jsonify({'items': [dict(r) for r in rows]})

@app.route('/api/waiting/<int:item_id>/accepter', methods=['POST'])
def accepter(item_id):
    db = get_db()
    cur = db_exec(db, 'SELECT * FROM waiting WHERE id = ?', (item_id,))
    row = cur.fetchone()
    if not row:
        return (jsonify({'ok': False, 'error': 'Suggestion introuvable.'}), 404)
    r = dict(row)
    now = datetime.utcnow().isoformat() + 'Z'
    kind = (r.get('suggestion_type') or 'boycott').lower()
    if kind == 'alternative':
        db_exec(db, '\n            INSERT INTO produit_alternatives (nom, categorie, description, lien_source, created_at)\n            VALUES (?, ?, ?, ?, ?)\n            ', (r['nom'], r['categorie'], r['description'], r['lien_source'], now))
    else:
        db_exec(db, '\n            INSERT INTO produits (nom, categorie, description, lien_source, accepted_from_waiting_id, created_at, code_barre)\n            VALUES (?, ?, ?, ?, ?, ?, ?)\n            ', (r['nom'], r['categorie'], r['description'], r['lien_source'], item_id, now, _generate_ean13()))
    db_exec(db, 'DELETE FROM waiting WHERE id = ?', (item_id,))
    db.commit()
    return jsonify({'ok': True})

@app.route('/api/waiting/<int:item_id>/refuser', methods=['POST'])
def refuser(item_id):
    db = get_db()
    cur = db_exec(db, 'DELETE FROM waiting WHERE id = ?', (item_id,))
    db.commit()
    if cur.rowcount == 0:
        return (jsonify({'ok': False, 'error': 'Suggestion introuvable.'}), 404)
    return jsonify({'ok': True})

@app.route('/api/produits', methods=['GET'])
def list_produits():
    db = get_db()
    cur = db_exec(db, 'SELECT id, nom, categorie, description, lien_source, created_at, code_barre FROM produits ORDER BY id DESC')
    rows = cur.fetchall()
    return jsonify({'items': [dict(r) for r in rows]})

@app.route('/api/produit-alternatives', methods=['GET'])
def list_produit_alternatives():
    db = get_db()
    cur = db_exec(db, 'SELECT id, nom, categorie, description, lien_source, created_at FROM produit_alternatives ORDER BY id DESC')
    rows = cur.fetchall()
    return jsonify({'items': [dict(r) for r in rows]})

@app.route('/api/donation-suggestions', methods=['GET', 'POST'])
def donation_suggestions():
    db = get_db()
    if request.method == 'GET':
        try:
            cur = db_exec(db, 'SELECT id, nom, description, lien_source, email_contact, created_at, statut FROM donation_suggestions ORDER BY id DESC')
            rows = cur.fetchall()
            return jsonify({'ok': True, 'items': [dict(r) for r in rows]})
        except Exception:
            app.logger.exception('donation_suggestions list')
            return jsonify({'ok': False, 'error': 'Table donation_suggestions indisponible.', 'items': []})
    data = request.get_json(silent=True) or {}
    nom = (data.get('nom') or '').strip()
    if not nom:
        return (jsonify({'ok': False, 'error': 'Le nom de l’organisme ou de la personne est requis.'}), 400)
    description = (data.get('description') or '').strip() or None
    lien_source = (data.get('lien_source') or '').strip() or None
    email_contact = (data.get('email_contact') or '').strip() or None
    now = datetime.utcnow().isoformat() + 'Z'
    try:
        cur = db_exec(db, "\n            INSERT INTO donation_suggestions (nom, description, lien_source, email_contact, created_at, statut)\n            VALUES (?, ?, ?, ?, ?, 'en_attente')\n            ", (nom, description, lien_source, email_contact, now))
        db.commit()
    except Exception:
        app.logger.exception('donation_suggestions insert')
        return (jsonify({'ok': False, 'error': 'Enregistrement impossible (table donation_suggestions manquante ?).'}), 500)
    return jsonify({'ok': True, 'id': cur.lastrowid, 'storage': 'mysql' if USE_MYSQL else 'sqlite'})

@app.route('/api/donation-suggestions/<int:item_id>/accepter', methods=['POST'])
def accepter_donation_suggestion(item_id):
    db = get_db()
    cur = db_exec(db, 'SELECT * FROM donation_suggestions WHERE id = ? AND statut = ?', (item_id, 'en_attente'))
    row = cur.fetchone()
    if not row:
        return (jsonify({'ok': False, 'error': 'Suggestion introuvable ou déjà traitée.'}), 404)
    r = dict(row)
    nom = (r.get('nom') or '').strip()
    if not nom:
        return (jsonify({'ok': False, 'error': 'Nom manquant.'}), 400)
    desc = (r.get('description') or '').strip()
    raw_lien = (r.get('lien_source') or '').strip()
    if raw_lien and (not (raw_lien.startswith('http://') or raw_lien.startswith('https://'))):
        raw_lien = ''
    donate_url = raw_lien if raw_lien else '#'
    card_summary = desc if len(desc) <= 400 else desc[:397] + '…'
    if not card_summary:
        card_summary = nom[:400]
    body_text = desc + '\n\n— Fiche créée à partir d’une suggestion sur le site.' if desc else 'Cette fiche provient d’une suggestion d’utilisateur·rice. Complétez les textes, le logo et l’image d’en-tête dans la base de données si besoin.'
    base_slug = _slugify_donation_slug(nom)
    slug = _unique_donation_slug(db, base_slug)
    sort_order = _next_donation_sort_order(db)
    try:
        db_exec(db, "\n            INSERT INTO donation_agencies (\n                slug, name, card_summary, body_text, hero_image_url, logo_url, gallery_json, donate_url, sort_order\n            )\n            VALUES (?, ?, ?, ?, NULL, NULL, '[]', ?, ?)\n            ", (slug, nom, card_summary, body_text, donate_url, sort_order))
        db_exec(db, 'DELETE FROM donation_suggestions WHERE id = ?', (item_id,))
        db.commit()
    except Exception:
        app.logger.exception('accepter_donation_suggestion')
        db.rollback()
        return (jsonify({'ok': False, 'error': 'Impossible d’enregistrer l’organisme (conflit ou base indisponible).'}), 500)
    return jsonify({'ok': True, 'slug': slug})

@app.route('/api/donation-suggestions/<int:item_id>/refuser', methods=['POST'])
def refuser_donation_suggestion(item_id):
    db = get_db()
    cur = db_exec(db, 'DELETE FROM donation_suggestions WHERE id = ?', (item_id,))
    db.commit()
    rc = getattr(cur, 'rowcount', 0) or 0
    if rc == 0:
        return (jsonify({'ok': False, 'error': 'Suggestion introuvable.'}), 404)
    return jsonify({'ok': True})

@app.route('/api/donation-agencies', methods=['GET'])
def list_donation_agencies():
    db = get_db()
    try:
        cur = db_exec(db, 'SELECT slug, name, card_summary, body_text, hero_image_url, logo_url, gallery_json, donate_url, sort_order FROM donation_agencies ORDER BY sort_order ASC, id ASC')
        rows = cur.fetchall()
    except Exception:
        app.logger.exception('donation_agencies table missing or query error')
        return jsonify({'ok': False, 'error': 'Table donation_agencies indisponible.', 'items': []})
    out = []
    for r in rows:
        d = dict(r)
        raw_g = (d.pop('gallery_json', None) or '').strip()
        try:
            gallery = json.loads(raw_g) if raw_g else []
            if not isinstance(gallery, list):
                gallery = []
        except json.JSONDecodeError:
            gallery = []
        d['gallery'] = gallery
        out.append(d)
    return jsonify({'ok': True, 'items': out})

@app.route('/api/feedback', methods=['POST'])
def add_feedback():
    data = request.get_json(silent=True) or {}
    message = (data.get('message') or '').strip()
    if not message:
        return (jsonify({'ok': False, 'error': 'Message is required.'}), 400)
    now = datetime.utcnow().isoformat() + 'Z'
    db = get_db()
    cur = db_exec(db, 'INSERT INTO feedback (message, created_at) VALUES (?, ?)', (message, now))
    db.commit()
    fid = cur.lastrowid
    email_sent = _send_feedback_email(message, fid, now)
    return jsonify({'ok': True, 'id': fid, 'email_sent': email_sent})

def _run_server():
    port = int(os.environ.get('PORT', '8080'))
    host = os.environ.get('FLASK_HOST', '127.0.0.1')
    print(f'\n  → Ouvre le site : http://{host}:{port}/')
    if USE_MYSQL:
        dbn = (os.environ.get('MYSQL_DATABASE') or os.environ.get('MYSQL_DB') or 'amenah').strip()
        print(f'  → Base de données : MySQL « {dbn} » sur {MYSQL_HOST}\n')
    else:
        if MYSQL_HOST:
            print(f'  → AMENAH_USE_SQLITE=1 : utilisation de SQLite malgré MYSQL_HOST.\n  → Base de données : SQLite (fichier {DATABASE})\n')
        else:
            print(f'  → Base de données : SQLite (fichier {DATABASE})\n')
        print('     Les suggestions vont dans ce fichier, pas dans MySQL/phpMyAdmin.\n     Pour MySQL : importez sql/schema_mysql.sql, puis définissez MYSQL_HOST, etc.\n')
    try:
        app.run(debug=True, host=host, port=port, use_reloader=True)
    except OSError as e:
        if getattr(e, 'winerror', None) == 10048 or 'address' in str(e).lower():
            print('\n  Le port', port, 'est déjà utilisé. Ferme l’autre terminal Flask, ou lance avec une autre porte, par ex. :\n     set PORT=5000\n     python app.py\n')
        raise
if __name__ == '__main__':
    _run_server()
