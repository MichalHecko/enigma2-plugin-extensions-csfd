# -*- coding: utf-8 -*-
#
# CSFDClient - nahrada za CSFDAndroidClient
#
# Povodny klient komunikoval s android-api.csfd.cz cez OAuth1. Toto API bolo
# odstavene (HTTP 412 "Required application version is 3.0.0 or higher").
# Tento klient ziskava data scrapovanim verejneho webu https://www.csfd.cz
# (rovnaky vzor ako plugin CSFDLite) a zostavuje rovnaku JSON strukturu,
# aku ocakava CSFDParser.py / CSFD.py.
#
# Web csfd.cz je chraneny anti-bot vyzvou "Anubis" (proof-of-work). Klient ju
# riesi v cistom Pythone (hashlib sha256) a udrzuje si cookie session.

import re
import json
import time
import hashlib
import traceback

try:
	import html as _htmlmod
	def _unescape(s):
		return _htmlmod.unescape(s)
except Exception:
	try:
		from HTMLParser import HTMLParser as _HP
		_hp = _HP()
		def _unescape(s):
			return _hp.unescape(s)
	except Exception:
		def _unescape(s):
			return s

try:
	from urllib.parse import quote_plus, quote, urlencode
except Exception:
	from urllib import quote_plus, quote, urlencode

import requests
try:
	from requests.packages.urllib3.util.retry import Retry
	from requests.adapters import HTTPAdapter
except Exception:
	Retry = None
	HTTPAdapter = None

# ---- enigma prostredie (defenzivne, aby sa dal modul testovat aj samostatne) ----
try:
	from .CSFDLog import LogCSFD
except Exception:
	class _L:
		def WriteToFile(self, *a, **k):
			pass
	LogCSFD = _L()

try:
	from .CSFDSettings2 import config
except Exception:
	config = None

try:
	from .CSFDTools import internet_on
except Exception:
	def internet_on():
		return True


CSFD_WEB = 'https://www.csfd.cz'
IMG_HOST = 'https://image.pmgstatic.com'

BROWSER_HEADERS = {
	'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64; rv:109.0) Gecko/20100101 Firefox/116.0',
	'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
	'Accept-Language': 'cs,sk;q=0.8,en;q=0.6',
}

# csfd farba hodnotenia (ikona) -> rating_category ocakavana pluginom
# '0' nic, '1' cervena (>=70%), '2' modra (30-69%), '3' cierna (<30%)
_RATING_COLOR_MAP = {
	'red': '1',
	'blue': '2',
	'grey': '3',
	'gray': '3',
	'black': '3',
	'lightgrey': '0',
	'lightgray': '0',
}

# csfd popis tvorcov -> kluc ocakavany CSFDParser.parserGetCreatorList
_CREATOR_MAP = {
	u'režie': 'directors',
	u'réžia': 'directors',
	u'předloha': 'authors',
	u'předloha:': 'authors',
	u'scénář': 'screenwriters',
	u'kamera': 'cinematographers',
	u'hudba': 'composers',
	u'produkce': 'production',
	u'casting': 'production',
	u'střih': 'edit',
	u'zvuk': 'sound',
	u'scénografie': 'scenographies',
	u'masky': 'masks',
	u'kostýmy': 'costumes',
	u'hrají': 'actors',
	u'účinkují': 'performer',
}

_ALL_CREATOR_KEYS = ('directors', 'authors', 'screenwriters', 'cinematographers',
	'composers', 'production', 'edit', 'sound', 'scenographies', 'masks',
	'costumes', 'actors', 'performer')

# csfd typ (retazec) -> retazec ocakavany MovieType.strToId
_TYPE_MAP = {
	u'seriál': u'seriál',
	u'série': u'série',
	u'epizoda': u'epizoda',
	u'pořad': u'pořad',
	u'tv film': u'TV film',
	u'tv seriál': u'seriál',
	u'video film': u'video film',
	u'koncert': u'koncert',
}


def _timeout():
	try:
		return config.misc.CSFD.DownloadTimeOut.getValue()
	except Exception:
		return 20


def _strip_tags(text):
	if not text:
		return ''
	text = re.sub(r'<[^>]+>', '', text)
	text = _unescape(text)
	return text.strip()


def _norm_img(url, size='w420'):
	if not url:
		return None
	url = url.strip()
	if url.startswith('//'):
		url = 'https:' + url
	# preved csfd cache velkost na pozadovanu (w140 -> wXXX)
	url = re.sub(r'/cache/resized/w\d+(h\d+)?/', '/cache/resized/%s/' % size, url)
	if url.startswith('/files') or url.startswith('/cache'):
		url = IMG_HOST + url
	return url


def _img_src(tag):
	# ČSFD lazy-loaduje obrazky: realna URL je v data-src/srcset, src byva base64 placeholder
	for attr in ('data-src', 'data-srcset', 'srcset'):
		m = re.search(r'%s="([^"]+)"' % attr, tag)
		if m:
			return m.group(1).split(',')[0].strip().split(' ')[0]
	m = re.search(r'src="([^"]+)"', tag)
	if m and not m.group(1).startswith('data:'):
		return m.group(1)
	return None  # empty-image placeholder -> film nema poster


def _split_name(fullname):
	fullname = _strip_tags(fullname)
	parts = fullname.split()
	if len(parts) == 0:
		return {'firstname': '', 'surname': ''}
	if len(parts) == 1:
		return {'firstname': '', 'surname': parts[0]}
	return {'firstname': ' '.join(parts[:-1]), 'surname': parts[-1]}


def _make_datetime(date_str):
	# vstup "13.04.2003" alebo "13.4.2003 21:55" -> "2003-04-13 21:55" + 15 znakov
	# CSFDParser robi inserted_datetime[:-15] a ocakava "YYYY-MM-DD HH:MM"
	date_str = (date_str or '').strip()
	m = re.match(r'(\d{1,2})\.\s*(\d{1,2})\.\s*(\d{4})(?:\s+(\d{1,2}):(\d{2}))?', date_str)
	if not m:
		iso = '1970-01-01 00:00'
	else:
		d, mo, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
		hh = int(m.group(4)) if m.group(4) else 0
		mm = int(m.group(5)) if m.group(5) else 0
		iso = '%04d-%02d-%02d %02d:%02d' % (y, mo, d, hh, mm)
	return iso + ':00.000000+0100'


# ######################################################################################

class CSFDClient:
	def __init__(self, login_token=None):
		self.logged_user = None
		self.logged_user_id = None
		self.session = requests.Session()
		self.session.headers.update(BROWSER_HEADERS)
		if Retry is not None and HTTPAdapter is not None:
			try:
				ad = HTTPAdapter(max_retries=Retry(total=2, backoff_factor=0.2))
				self.session.mount('http://', ad)
				self.session.mount('https://', ad)
			except Exception:
				pass

	# --------------------------------------------------------------------------
	# Anubis proof-of-work + HTTP GET
	# --------------------------------------------------------------------------
	def _solve_anubis(self, html_text):
		try:
			m = re.search(r'id="anubis_challenge"[^>]*>\s*(\{.*?\})\s*</script>', html_text, re.DOTALL)
			if not m:
				return False
			ch = json.loads(m.group(1))
			rd = ch['challenge']['randomData']
			cid = ch['challenge']['id']
			diff = int(ch['rules']['difficulty'])
			prefix = '0' * diff
			nonce = 0
			t0 = time.time()
			while True:
				h = hashlib.sha256((rd + str(nonce)).encode('utf-8')).hexdigest()
				if h[:diff] == prefix:
					break
				nonce += 1
				if nonce > 5000000:
					return False
			params = {
				'id': cid,
				'response': h,
				'nonce': nonce,
				'redir': CSFD_WEB + '/',
				'elapsedTime': int((time.time() - t0) * 1000) or 500,
			}
			url = CSFD_WEB + '/.within.website/x/cmd/anubis/api/pass-challenge?' + urlencode(params)
			self.session.get(url, timeout=_timeout(), allow_redirects=True)
			LogCSFD.WriteToFile('[CSFD] Anubis vyreseny (nonce=%d)\n' % nonce, 2)
			return True
		except Exception:
			LogCSFD.WriteToFile('[CSFD] Anubis chyba:\n%s\n' % traceback.format_exc(), 2)
			return False

	def _get(self, url):
		if url.startswith('/'):
			url = CSFD_WEB + url
		try:
			r = self.session.get(url, timeout=_timeout(), allow_redirects=True)
		except Exception:
			LogCSFD.WriteToFile('[CSFD] _get vynimka:\n%s\n' % traceback.format_exc(), 2)
			return None

		# DEBUG: Zologovanie obsahu stiahnuteho HTML
		# LogCSFD.WriteToFile('[CSFD] _get - %s -> status %d, len %d\n%s\n' % (url, r.status_code, len(r.text), r.text), 2)

		if r.status_code == 200 and 'anubis_challenge' in r.text:
			if self._solve_anubis(r.text):
				try:
					r = self.session.get(url, timeout=_timeout(), allow_redirects=True)

					# DEBUG: Zologovanie obsahu stiahnuteho HTML
					# LogCSFD.WriteToFile('[CSFD] _get (po Anubis) - %s -> status %d, len %d\n%s\n' % (url, r.status_code, len(r.text), r.text), 2)
				except Exception:
					return None
			else:
				LogCSFD.WriteToFile('[CSFD] _get - Anubis challenge nevyreseny\n', 2)
				return None
		if r.status_code != 200:
			LogCSFD.WriteToFile('[CSFD] _get status %d pre %s\n' % (r.status_code, url), 2)
			return None
		return r

	def _get_html(self, url):
		r = self._get(url)
		return r.text if r is not None else None

	# --------------------------------------------------------------------------
	# Session / login (web scraping je anonymny)
	# --------------------------------------------------------------------------
	def is_logged(self):
		return False

	def login(self, username, password):
		return False

	def logout(self):
		self.logged_user = None
		self.logged_user_id = None

	def get_login_token(self):
		return ''

	def get_logged_user(self):
		return self.logged_user, self.logged_user_id

	def get_user_identity(self):
		return None

	def get_user_info(self, user_id=None):
		return {}

	def set_all_tv_stations(self):
		return

	def set_movie_rating(self, movie_id, rating):
		return None

	# --------------------------------------------------------------------------
	# pomocne parsovanie id
	# --------------------------------------------------------------------------
	def _film_id(self, movie_id):
		if movie_id is None:
			return None
		s = str(movie_id)
		if s.startswith('#movie#'):
			s = s[7:]
		m = re.match(r'(\d+)', s)
		return m.group(1) if m else s

	def _film_url(self, movie_id, sub='prehled'):
		fid = self._film_id(movie_id)
		return '%s/film/%s-film/%s/' % (CSFD_WEB, fid, sub)

	# --------------------------------------------------------------------------
	# VYHLADAVANIE
	# --------------------------------------------------------------------------
	def _parse_search_articles(self, block, default_type=''):
		res = []
		for art in re.findall(r'<article[^>]*>.*?</article>', block, re.DOTALL):
			mid = re.search(r'/film/(\d+)-[^"/]*/', art)
			if not mid:
				continue
			mname = re.search(r'film-title-name"[^>]*>(.*?)</a>', art, re.DOTALL)
			if not mname:
				continue
			name = _strip_tags(mname.group(1))
			color = ''
			mc = re.search(r'icon-rounded-square\s+(\w+)', art)
			if mc:
				color = mc.group(1)
			rating_category = _RATING_COLOR_MAP.get(color, '0')
			# rok + typ z film-title-info
			year = None
			ftype = default_type
			minfo = re.search(r'film-title-info">(.*?)</span>\s*</h3>', art, re.DOTALL)
			info_html = minfo.group(1) if minfo else art
			infos = re.findall(r'<span class="info">\(?([^<)]+)\)?</span>', info_html)
			for token in infos:
				token = token.strip()
				my = re.match(r'(\d{4})$', token)
				if my:
					year = int(my.group(1))
				elif token.lower() in _TYPE_MAP:
					ftype = _TYPE_MAP[token.lower()]
			res.append({
				'id': int(mid.group(1)),
				'name': name,
				'search_name': name,
				'year': year,
				'rating_category': rating_category,
				'type': ftype,
			})
		return res

	def search_by_name(self, name, offset=0, limit=30):
		html_text = self._get_html('/hledat/?q=' + quote_plus(name))
		if html_text is None:
			return {'http_error': 500, 'http_error_text': 'search download failed'}
		films = []
		# sekcia Filmy
		i_f = html_text.find(u'>Filmy<')
		i_s = html_text.find(u'>Seri')
		i_c = html_text.find(u'>Tvůrci<')
		if i_f < 0:
			i_f = 0
		films_block = html_text[i_f:(i_s if i_s > 0 else len(html_text))]
		series_block = html_text[i_s:(i_c if i_c > 0 else len(html_text))] if i_s > 0 else ''
		films += self._parse_search_articles(films_block, default_type='')
		films += self._parse_search_articles(series_block, default_type=u'seriál')
		# odstranenie duplicit podla id (zachovanie poradia)
		seen = set()
		uniq = []
		for f in films:
			if f['id'] in seen:
				continue
			seen.add(f['id'])
			uniq.append(f)
		return {'films': uniq}

	def autocomplete_by_name(self, name, offset=0, limit=30):
		return {'films': []}

	# --------------------------------------------------------------------------
	# DETAIL FILMU
	# --------------------------------------------------------------------------
	def _parse_creators(self, html_text):
		creators = {}
		for k in _ALL_CREATOR_KEYS:
			creators[k] = []
		block = html_text
		mm = re.search(r'<div class="creators"[^>]*>(.*?)</div>\s*(?:<div class="tabs"|<div class="box|</section)', html_text, re.DOTALL)
		if mm:
			block = mm.group(1)
		for h4, body in re.findall(r'<h4>(.*?)</h4>(.*?)(?=<h4>|</div>|$)', block, re.DOTALL):
			label = _strip_tags(h4).rstrip(':').strip().lower()
			key = _CREATOR_MAP.get(label)
			if not key:
				continue
			names = re.findall(r'<a [^>]*href="/tvurce/[^"]*"[^>]*>(.*?)</a>', body, re.DOTALL)
			for nm in names:
				creators[key].append(_split_name(nm))
		return creators

	def _parse_counts(self, html_text):
		def cnt(label):
			m = re.search(re.escape(label) + r'\s*(?:<span[^>]*>)?\s*\((\d+)\)', html_text)
			return int(m.group(1)) if m else 0
		return {
			'comment_count': cnt(u'Komentáře') or (1 if u'data-film-review' in html_text else 0),
			'trivia_count': cnt(u'Zajímavosti'),
			'photo_count': cnt(u'Galerie'),
			'video_count': cnt(u'Videa'),
			'related_films_count': 0,
			'similar_films_count': 0,
		}

	def _detect_type(self, html_text):
		# typ z hlavicky filmu, napr. <span class="type">(epizoda)</span>
		mt = re.search(r'film-header-name.*?<span class="type">\(?([^<)]+)\)?</span>', html_text, re.DOTALL)
		type_str = _strip_tags(mt.group(1)).lower() if mt else ''
		type_map_id = {
			u'seriál': (u'seriál', 12),
			u'série': (u'série', 10),
			u'epizoda': (u'epizoda', 11),
			u'pořad': (u'pořad', 13),
			u'tv film': (u'TV film', 2),
			u'video film': (u'video film', 1),
			u'film': (u'', 1),
		}
		for key, val in type_map_id.items():
			if key in type_str:
				return val[0], val[1]
		return u'', 1

	def get_movie_info(self, movie_id):
		return self._movie_info(movie_id)

	def _movie_info(self, movie_id):
		fid = self._film_id(movie_id)
		cached = getattr(self, '_movie_cache', None)
		if cached is not None and cached.get('id') == fid:
			return cached['data']
		html_text = self._get_html('/film/%s-film/prehled/' % fid)
		if html_text is None:
			return {'http_error': 500, 'http_error_text': 'movie download failed'}

		info = {}
		info['id'] = int(fid)

		# nazov
		mname = re.search(r'<div class="film-header-name">.*?<h1[^>]*>(.*?)</h1>', html_text, re.DOTALL)
		info['name'] = _strip_tags(mname.group(1)) if mname else ''

		# ostatne (originalne) nazvy
		morig = re.search(r'<ul class="film-names">(.*?)</ul>', html_text, re.DOTALL)
		if morig:
			names = re.findall(r'title="([^"]+)"[^>]*/>\s*([^<\n]+)', morig.group(1))
			if names:
				info['name_orig'] = _strip_tags(names[0][1])

		# typ / type_id
		type_str, type_id = self._detect_type(html_text)
		info['type'] = type_str
		info['type_id'] = type_id
		info['has_no_seasons'] = type_id not in (12, 13)

		# zaner
		mg = re.search(r'<div class="genres">(.*?)</div>', html_text, re.DOTALL)
		info['genre'] = [g.strip() for g in re.findall(r'<a [^>]*>(.*?)</a>', mg.group(1))] if mg else []

		# povod / rok / dlzka
		info['origin'] = []
		info['year'] = None
		info['length'] = ''
		mo = re.search(r'<div class="origin">(.*?)</div>', html_text, re.DOTALL)
		if mo:
			otext = _strip_tags(re.sub(r'<span[^>]*>', ' ', mo.group(1)))
			otext = re.sub(r'\s+', ' ', otext).strip()
			my = re.search(r'(\d{4})', otext)
			if my:
				info['year'] = int(my.group(1))
			ml = re.search(r'(\d+)\s*min', otext)
			if ml:
				info['length'] = ml.group(1)
			# krajina = cast pred rokom
			country = otext.split(str(info['year']))[0] if info['year'] else otext
			country = country.replace(u'\xa0', ' ').strip(' ,')
			if country:
				info['origin'] = [c.strip() for c in re.split(r'[,/]', country) if c.strip()]

		# hodnotenie (rating_average 0-100)
		info['rating_average'] = None
		mr = re.search(r'film-rating-average[^>]*>\s*([0-9]+)%', html_text)
		if mr:
			info['rating_average'] = int(mr.group(1))

		# plakat
		info['poster_url'] = None
		mp = re.search(r'film-posters">.*?(<img[^>]*>)', html_text, re.DOTALL)
		if mp:
			info['poster_url'] = _norm_img(_img_src(mp.group(1)))

		# obsah (plot)
		info['plot'] = {'text': '', 'source_name': ''}
		mplot = re.search(r'<div class="plot-full[^"]*">\s*<p>(.*?)</p>', html_text, re.DOTALL)
		if not mplot:
			mplot = re.search(r'<div class="plots-item">\s*<p>(.*?)</p>', html_text, re.DOTALL)
		if mplot:
			info['plot'] = {'text': _strip_tags(mplot.group(1)), 'source_name': 'CSFD.cz'}

		# zebricky (charts)
		info['charts'] = []
		for t in re.findall(r'/zebricky/[^"]*"[^>]*>\s*([^<]+?)\s*</a>', html_text):
			t = t.strip()
			if t and u'ebříčk' not in t:
				info['charts'].append({'title': t})

		# tv vysielanie
		info['tv_schedule'] = []

		# premiery
		info['releases'] = False

		# vlastne hodnotenie / povolenie hodnotit (len prihlaseny)
		info['rating'] = None
		info['rating_allowed'] = False

		# serial: root info (breadcrumb)
		mroot = re.search(r'<header class="film-header">\s*<h2>\s*<a href="/film/(\d+)-[^"]*"[^>]*>(.*?)</a>', html_text, re.DOTALL)
		if mroot:
			info['root_id'] = int(mroot.group(1))
			info['root_name'] = _strip_tags(mroot.group(2))

		# suhrny pocty
		info['summary'] = self._parse_counts(html_text)

		result = {'info': info}
		result['creators'] = self._parse_creators(html_text)

		# ulozime si HTML pre pripadne dalsie parsovanie related/similar
		result['_related'] = self._parse_related(html_text, u'Podobné')
		result['_similar'] = self._parse_related(html_text, u'Podobné')
		info['summary']['related_films_count'] = len(result['_related'])
		info['summary']['similar_films_count'] = len(result['_similar'])
		self._movie_cache = {'id': fid, 'data': result}
		return result

	def _parse_related(self, html_text, header_label):
		res = []
		mh = re.search(re.escape(header_label) + r'.*?</section>', html_text, re.DOTALL)
		block = mh.group(0) if mh else ''
		for art in re.findall(r'<article[^>]*>.*?</article>', block, re.DOTALL):
			mid = re.search(r'/film/(\d+)-[^"/]*/', art)
			mname = re.search(r'film-title-name"[^>]*>(.*?)</a>', art, re.DOTALL)
			if not mid or not mname:
				continue
			color = ''
			mc = re.search(r'icon-rounded-square\s+(\w+)', art)
			if mc:
				color = mc.group(1)
			year = None
			my = re.search(r'<span class="info">\(?(\d{4})\)?</span>', art)
			if my:
				year = int(my.group(1))
			res.append({
				'id': int(mid.group(1)),
				'name': _strip_tags(mname.group(1)),
				'year': year,
				'rating_category': _RATING_COLOR_MAP.get(color, '0'),
				'type': '',
			})
		return res

	def get_movie_related(self, movie_id, offset=0, limit=50):
		data = self._movie_info(movie_id)
		return {'related': data.get('_related', [])}

	def get_movie_similar(self, movie_id, offset=0, limit=50):
		data = self._movie_info(movie_id)
		return {'similar': data.get('_similar', [])}

	# --------------------------------------------------------------------------
	# KOMENTARE
	# --------------------------------------------------------------------------
	def get_movie_comments(self, movie_id, offset=0, limit=10):
		fid = self._film_id(movie_id)
		html_text = self._get_html('/film/%s-film/recenze/' % fid)
		if html_text is None:
			return {'comments': []}
		comments = []
		for art in re.findall(r'<article[^>]*data-film-review[^>]*>.*?</article>', html_text, re.DOTALL):
			mn = re.search(r'user-title-name"[^>]*>(.*?)</a>', art, re.DOTALL)
			nick = _strip_tags(mn.group(1)) if mn else ''
			ms = re.search(r'stars stars-(\d)', art)
			if ms:
				rating = int(ms.group(1)) * 20
			elif 'trash' in art:
				rating = 0
			else:
				rating = None
			mt = re.search(r'<span class="comment"[^>]*>(.*?)</span>', art, re.DOTALL)
			text = _strip_tags(mt.group(1)) if mt else ''
			md = re.search(r'<time[^>]*>(.*?)</time>', art, re.DOTALL)
			date = _strip_tags(md.group(1)) if md else ''
			comments.append({
				'text': text,
				'rating': rating,
				'inserted_datetime': _make_datetime(date),
				'user': {'nick': nick},
			})
		return {'comments': comments}

	# --------------------------------------------------------------------------
	# ZAUJIMAVOSTI (trivia)
	# --------------------------------------------------------------------------
	def get_movie_trivia(self, movie_id, offset=0, limit=10):
		fid = self._film_id(movie_id)
		html_text = self._get_html('/film/%s-film/zajimavosti/' % fid)
		if html_text is None:
			return {'trivia': []}
		trivia = []
		for art in re.findall(r'<article[^>]*article-trivia[^>]*>.*?</article>', html_text, re.DOTALL):
			for li in re.findall(r'<li>(.*?)</li>', art, re.DOTALL):
				mauth = re.search(r'span-more-small">\s*\(?\s*<a[^>]*href="/uzivatel/[^"]*"[^>]*>(.*?)</a>', li, re.DOTALL)
				nick = _strip_tags(mauth.group(1)) if mauth else ''
				text = _strip_tags(re.sub(r'<span class="span-more-small">.*?</span>', '', li, flags=re.DOTALL))
				if text:
					trivia.append({'text': text, 'source_user': {'nick': nick}})
		return {'trivia': trivia}

	# --------------------------------------------------------------------------
	# GALERIA (photos)
	# --------------------------------------------------------------------------
	def get_movie_photos(self, movie_id, offset=0, limit=20):
		fid = self._film_id(movie_id)
		html_text = self._get_html('/film/%s-film/galerie/' % fid)
		photos = []
		if html_text is not None:
			seen = set()
			for src in re.findall(r'(//image\.pmgstatic\.com[^"\' ]*?/files/images/film/photos/[^"\' ]+\.(?:jpg|webp))', html_text):
				u = _norm_img(src, 'w1080')
				if u in seen:
					continue
				seen.add(u)
				photos.append({'url': u, 'preview_image': {'url': _norm_img(src, 'w420')}})
		return {'photos': photos, 'images': photos}

	# --------------------------------------------------------------------------
	# VIDEA
	# --------------------------------------------------------------------------
	def get_movie_videos(self, movie_id, offset=0, limit=20):
		# priame URL videi su na csfd.cz sifrovane (api/video-player), tu ich
		# nevieme spolahlivo ziskat - vratime prazdny zoznam.
		return {'videos': []}

	# --------------------------------------------------------------------------
	# EPIZODY / SERIE
	# --------------------------------------------------------------------------
	def get_movie_episodes(self, movie_id, offset=0, limit=0):
		fid = self._film_id(movie_id)
		html_text = self._get_html('/film/%s-film/epizody/' % fid)
		seasons = []
		if html_text is not None:
			# kazda seria: odkaz /film/<fid>-slug/<sid>-serie-N/ (alebo -season-N)
			seen = set()
			for sm in re.finditer(r'<a[^>]+href="/film/%s-[^"]*?/(\d+)-(?:serie|season)-(\d+)/[^"]*"[^>]*>(.*?)</a>' % fid, html_text, re.DOTALL):
				sid = int(sm.group(1))
				if sid in seen:
					continue
				seen.add(sid)
				snum = int(sm.group(2))
				sname = _strip_tags(sm.group(3)) or (u'Série %d' % snum)
				seasons.append({
					'id': sid,
					'name': sname,
					'year': None,
					'rating_category': '0',
					'episodes': [{
						'id': sid,
						'name': sname,
						'year': None,
						'rating_category': '0',
						'position_code': 'S%02d' % snum,
					}],
				})
		return {'seasons': seasons}

	def get_creator_info(self, creator_id):
		return {}

	def get_video_types(self):
		return {}

	def get_tv_stations(self):
		return {'stations': []}

	# --------------------------------------------------------------------------
	# HLAVNY DISPATCHER (kompatibilny s povodnym API)
	# --------------------------------------------------------------------------
	def get_json_by_uri(self, uri, page=1, load_full=True):
		try:
			if uri.startswith('#search_movie#'):
				LogCSFD.WriteToFile('[CSFD] search: "%s"\n' % uri[14:], 2)
				return self.search_by_name(uri[14:], (page - 1) * 30, 30)

			elif uri.startswith('#movie#'):
				LogCSFD.WriteToFile('[CSFD] movie: "%s"\n' % uri[7:], 2)
				data = self._movie_info(uri[7:])
				if 'info' not in data:
					return data
				info = data['info']
				# doplnime root_info / parent_info ak ide o seriál/epizódu
				if load_full and 'root_id' in info:
					root = self._movie_info(info['root_id'])
					if 'info' in root:
						data['root_info'] = root['info']
				return data

			elif uri.startswith('#movie_photos#'):
				return self.get_movie_photos(uri[14:], (page - 1) * 20, 20)

			elif uri.startswith('#movie_videos#'):
				return self.get_movie_videos(uri[14:], (page - 1) * 20, 20)

			elif uri.startswith('#movie_comments#'):
				return self.get_movie_comments(uri[16:], (page - 1) * 10, 10)

			elif uri.startswith('#movie_trivia#'):
				return self.get_movie_trivia(uri[14:], (page - 1) * 10, 10)

			elif uri.startswith('#movie_premiere#'):
				return {}

			elif uri.startswith('#creator#'):
				return self.get_creator_info(uri[9:])

		except Exception:
			LogCSFD.WriteToFile('[CSFD] get_json_by_uri vynimka:\n%s\n' % traceback.format_exc(), 2)
			return {'internal_error': 'download error for uri: %s' % uri}

		return {'internal_error': 'unknown uri %s' % uri}


# ######################################################################################
# Modulovy singleton + tovarina (zachovane nazvy kvoli kompatibilite importov)

csfdClient = None


def CreateCSFDClient(ignore_checks=False, try_new_login=True):
	global csfdClient

	if csfdClient is None:
		LogCSFD.WriteToFile('[CSFD] CreateCSFDClient - vytvaram novu instanciu\n', 1)
		csfdClient = CSFDClient()

	return


# vytvorenie klienta pri importe
CreateCSFDClient()
