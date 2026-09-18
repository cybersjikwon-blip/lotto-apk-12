# -*- coding: utf-8 -*-
"""
흥보가 기가막혀  ·  lotto-2.py
=================================================================
로또 6/45 : 번호생성 · 통계 · 지역탐방 · QR확인 · 내번호

실행
    pip install kivy
    python lotto-2.py

APK 준비용 buildozer.spec 만들기
    python lotto-2.py --spec

데이터
    첫 실행 때 '통계' 탭에서 [최신 회차 받기] 를 누르면
    동행복권 → 네이버 순으로 시도해 당첨번호를 내려받아
    기기 안에 캐시합니다. 네트워크가 없으면 내장 시드
    (1208~1236회)로 동작합니다.

안드로이드
    minSdk 24 (7.0) ~ targetSdk 36 (16) 을 목표로 작성.
    - 저장 경로는 앱 전용 디렉터리 사용 (스코프드 스토리지)
    - 네트워크는 전부 백그라운드 스레드
    - 위치/카메라는 런타임 권한 요청
=================================================================
"""

import os
import re
import sys
import json
import math
import random
import hashlib
import threading
import bisect
import gc
import traceback
import datetime as dt
import urllib.request
import urllib.error
from collections import Counter

# ---------------------------------------------------------------
# Kivy 설정은 Window import 이전
# KIVY_NO_ARGS 를 먼저 세워야 --spec / --widget 인자를 Kivy 가 가로채지 않는다.
# ---------------------------------------------------------------
os.environ.setdefault("KIVY_NO_ARGS", "1")

from kivy.config import Config

if os.environ.get("KIVY_BUILD") != "android":
    Config.set("graphics", "width", "400")
    Config.set("graphics", "height", "820")
    Config.set("graphics", "resizable", "0")
Config.set("kivy", "exit_on_escape", "0")
Config.set("input", "mouse", "mouse,multitouch_on_demand")

from kivy.animation import Animation
from kivy.app import App
from kivy.clock import Clock
from kivy.core.text import LabelBase
from kivy.core.window import Window
from kivy.graphics import Color, Line, Rectangle, RoundedRectangle, Ellipse
from kivy.graphics.texture import Texture
from kivy.metrics import dp
from kivy.uix.behaviors import ButtonBehavior
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.image import Image as KvImage
from kivy.uix.label import Label
from kivy.uix.popup import Popup
from kivy.uix.screenmanager import (ScreenManager, Screen,
                                    NoTransition, SlideTransition)
from kivy.uix.scrollview import ScrollView
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.utils import platform

APP_NAME = "흥보가 기가막혀"
ROUND1_DATE = dt.date(2002, 12, 7)          # 1회 추첨일
TOTAL_COMBOS = 8145060                       # C(45,6)
TICKET_PRICE = 1000


# ===============================================================
#  저장 경로 — 안드로이드 스코프드 스토리지 대응
# ===============================================================
def data_dir():
    if platform == "android":
        try:
            from android.storage import app_storage_path
            p = app_storage_path()
        except Exception:
            p = os.path.join(os.path.expanduser("~"), "hb_data")
    else:
        p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hb_data")
    os.makedirs(p, exist_ok=True)
    return p


HERE = os.path.dirname(os.path.abspath(__file__))


def asset(name):
    for base in (os.path.join(HERE, "assets"), HERE):
        p = os.path.join(base, name)
        if os.path.exists(p):
            return p
    return None


DATA_DIR = data_dir()
DRAWS_CACHE = os.path.join(DATA_DIR, "draws.json")
VAULT_PATH = os.path.join(DATA_DIR, "my_numbers.json")
PREFS_PATH = os.path.join(DATA_DIR, "prefs.json")
CRASH_LOG = os.path.join(DATA_DIR, "crash.log")


def log_crash(exc):
    """죽는 대신 남긴다. 파일이 커지면 앞을 버린다."""
    try:
        txt = "".join(traceback.format_exception(
            type(exc), exc, exc.__traceback__))
        head = f"\n===== {dt.datetime.now().isoformat(timespec='seconds')} =====\n"
        old = ""
        if os.path.exists(CRASH_LOG):
            with open(CRASH_LOG, "r", encoding="utf-8") as f:
                old = f.read()[-40000:]
        with open(CRASH_LOG, "w", encoding="utf-8") as f:
            f.write(old + head + txt)
    except Exception:
        pass


def install_crash_guard():
    """
    화면 하나가 터져도 앱 전체가 강제종료되지 않게 한다.
    갤럭시에서 예외 한 번에 프로세스가 죽는 걸 막는 안전망.
    """
    try:
        from kivy.base import ExceptionHandler, ExceptionManager

        class _Guard(ExceptionHandler):
            def handle_exception(self, inst):
                log_crash(inst)
                return ExceptionManager.PASS

        ExceptionManager.add_handler(_Guard())
    except Exception:
        pass

    def hook(t, v, tb):
        log_crash(v)
        sys.__excepthook__(t, v, tb)

    sys.excepthook = hook


class UI:
    """글씨 배율. 기기·시력에 맞춰 통째로 키우고 줄인다."""
    scale = 1.0
    STEPS = {"작게": 0.90, "보통": 1.00, "크게": 1.14, "아주 크게": 1.30}

    @classmethod
    def apply(cls, name):
        cls.scale = cls.STEPS.get(name, 1.0)
        return cls.scale

    @classmethod
    def detect_system(cls):
        """
        갤럭시 등에서 '설정 > 디스플레이 > 글자 크기'를 키워 둔 경우
        첫 실행 때 그 값을 따라간다. Kivy 는 이걸 자동 반영하지 않는다.
        """
        if platform != "android":
            return "보통"
        try:
            from jnius import autoclass
            PythonActivity = autoclass("org.kivy.android.PythonActivity")
            Settings = autoclass("android.provider.Settings$System")
            cr = PythonActivity.mActivity.getContentResolver()
            v = Settings.getFloat(cr, "font_scale", 1.0)
            best, gap = "보통", 9.0
            for name, mul in cls.STEPS.items():
                g = abs(mul - v)
                if g < gap:
                    best, gap = name, g
            return best
        except Exception:
            return "보통"


def round_date(n):
    return ROUND1_DATE + dt.timedelta(weeks=n - 1)


_LATEST = {"n": 0, "at": 0.0}


def cached_latest_round():
    """
    화면을 그리는 중에는 네트워크를 타면 안 된다.
    확인해 둔 값이 있으면 그것을, 없으면 날짜 계산값을 쓴다.
    """
    return _LATEST["n"] or latest_round_by_date()


def resolve_latest_round():
    """
    날짜 계산은 추첨 지연·시차 때문에 한 회차씩 어긋날 수 있다.
    추정치 위아래로 서버에 실제로 물어 존재하는 가장 큰 회차를 찾는다.
    결과는 30분간 재사용한다.
    """
    import time as _t
    if _LATEST["n"] and _t.time() - _LATEST["at"] < 1800:
        return _LATEST["n"]
    base = latest_round_by_date()
    found = 0
    for n in range(base + 2, base - 3, -1):
        if n < 1:
            continue
        r, _ = fetch_round(n, tries=2)
        if r:
            found = n
            break
    if not found:
        found = base
    _LATEST["n"], _LATEST["at"] = found, _t.time()
    return found


def latest_round_by_date(today=None):
    """오늘 기준 추첨이 끝난 마지막 회차. 토요일 20:35 이후 반영."""
    today = today or dt.datetime.now()
    if isinstance(today, dt.date) and not isinstance(today, dt.datetime):
        today = dt.datetime.combine(today, dt.time(23, 59))
    n = (today.date() - ROUND1_DATE).days // 7 + 1
    d = round_date(n)
    if today.date() == d and today.hour < 21:
        n -= 1
    return max(1, n)


# ===============================================================
#  THEME
#  단청(丹靑) 오방색을 먹빛 위에 올린다.
#  로또 공은 동행복권 공식 구간색을 유지하되 광택을 얹는다.
# ===============================================================
class T:
    bg_top = (0.055, 0.063, 0.078, 1)
    bg_bot = (0.086, 0.098, 0.122, 1)
    surface = (0.106, 0.118, 0.145, 1)
    raised = (0.145, 0.161, 0.196, 1)
    field = (0.176, 0.196, 0.235, 1)
    stroke = (0.216, 0.239, 0.286, 1)
    text = (0.980, 0.972, 0.955, 1)
    dim = (0.745, 0.775, 0.820, 1)
    faint = (0.560, 0.595, 0.650, 1)

    juhong = (0.831, 0.275, 0.169, 1)    # 주홍 — 주요 동작
    chungrok = (0.184, 0.549, 0.502, 1)  # 청록 — 선택/확인
    chija = (0.910, 0.702, 0.239, 1)     # 치자 — 강조/당첨
    jaju = (0.557, 0.231, 0.420, 1)      # 자주 — 경고/특수
    baek = (0.878, 0.882, 0.871, 1)      # 백

    OBANG = [juhong, chungrok, chija, jaju, (0.243, 0.435, 0.706, 1)]

    @staticmethod
    def ball(n):
        if n <= 10:
            return (0.984, 0.769, 0.153, 1)
        if n <= 20:
            return (0.267, 0.612, 0.847, 1)
        if n <= 30:
            return (0.902, 0.353, 0.325, 1)
        if n <= 40:
            return (0.537, 0.553, 0.580, 1)
        return (0.400, 0.729, 0.416, 1)


# ===============================================================
#  폰트 — 제목/본문 두 벌
# ===============================================================
def _find(paths):
    for p in paths:
        if os.path.exists(p):
            return p
    return None


def _scan_system_korean():
    """
    갤럭시/안드로이드 기본 폰트 중 한글이 있는 것을 찾는다.
    번들 폰트가 없을 때의 마지막 보루.
    """
    import glob
    pats = [
        "/system/fonts/NotoSansKR-Regular.otf",
        "/system/fonts/NotoSansCJK-Regular.ttc",
        "/system/fonts/NotoSansCJKkr-Regular.otf",
        "/system/fonts/SECCJK*.ttf",
        "/system/fonts/SamsungKorean*.ttf",
        "/system/fonts/NanumGothic.ttf",
        "/system/fonts/DroidSansFallback.ttf",
    ]
    for pat in pats:
        for f in sorted(glob.glob(pat)):
            if os.path.exists(f):
                return f
    return None


def register_fonts():
    """
    한글 폰트를 찾아 등록한다. 못 찾으면 화면 전체가 □□□ 로 깨지므로
    실패 사실을 FONT_OK 로 남겨 앱 안에서 경고를 띄운다.
    """
    cands = []
    for d in (os.path.join(HERE, "assets"), HERE, DATA_DIR):
        for n in ("NanumGothic.ttf", "NanumBarunGothic.ttf",
                  "NotoSansKR-Regular.ttf"):
            cands.append(os.path.join(d, n))
    cands += [
        "/usr/share/fonts/truetype/nanum/NanumGothic.ttf",
        "C:/Windows/Fonts/malgun.ttf",
        "/System/Library/Fonts/AppleSDGothicNeo.ttc",
        "/Library/Fonts/AppleGothic.ttf",
        "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
        "/usr/share/fonts/truetype/unfonts-core/UnDotum.ttf",
    ]
    body = _find(cands) or _scan_system_korean()

    boldc = []
    for d in (os.path.join(HERE, "assets"), HERE, DATA_DIR):
        for n in ("NanumGothicBold.ttf", "NanumBarunGothicBold.ttf"):
            boldc.append(os.path.join(d, n))
    boldc += ["/usr/share/fonts/truetype/nanum/NanumGothicBold.ttf",
              "C:/Windows/Fonts/malgunbd.ttf"]
    bodyb = _find(boldc) or body

    dispc = []
    for d in (os.path.join(HERE, "assets"), HERE):
        for n in ("NanumSquareB.ttf", "NanumGothicBold.ttf"):
            dispc.append(os.path.join(d, n))
    dispc += ["/usr/share/fonts/truetype/nanum/NanumSquareB.ttf",
              "/usr/share/fonts/truetype/nanum/NanumBarunGothicBold.ttf"]
    disp = _find(dispc) or bodyb

    if not body:
        print("[!!] 한글 폰트를 찾지 못했습니다. assets/NanumGothic.ttf 를 넣으세요.")
        return "Roboto", "Roboto", False, ""
    try:
        LabelBase.register(name="KR", fn_regular=body, fn_bold=bodyb)
        LabelBase.register(name="KRD", fn_regular=disp, fn_bold=disp)
    except Exception as e:
        print("[!!] 폰트 등록 실패:", e)
        return "Roboto", "Roboto", False, body
    return "KR", "KRD", True, body


FONT, FONT_D, FONT_OK, FONT_PATH = register_fonts()


# ===============================================================
#  내장 시드 데이터 (1208~1236회) — 네트워크 없이도 동작
#  bonus 0 = 미확인. [최신 회차 받기] 하면 채워집니다.
# ===============================================================
SEED = [
    (1208, "6,27,30,36,38,42", 0, 6, 5001713625),
    (1209, "2,17,20,35,37,39", 0, 22, 1371910466),
    (1210, "1,7,9,17,27,38", 0, 24, 1102298407),
    (1211, "23,26,27,35,38,40", 0, 14, 2370956036),
    (1212, "5,8,25,31,41,44", 0, 12, 2654089032),
    (1213, "5,11,25,27,36,38", 0, 18, 1740011646),
    (1214, "10,15,19,27,30,33", 0, 12, 2431577188),
    (1215, "13,15,19,21,44,45", 0, 16, 1998542133),
    (1216, "3,10,14,15,23,24", 0, 14, 2148654000),
    (1217, "8,10,15,20,29,31", 0, 14, 2179738018),
    (1218, "3,28,31,32,42,45", 0, 18, 1714482042),
    (1219, "1,2,15,28,39,45", 0, 12, 2508232844),
    (1220, "2,22,25,28,34,43", 0, 14, 2114514161),
    (1221, "6,13,18,28,30,36", 0, 16, 1830801165),
    (1222, "4,11,17,22,32,41", 0, 24, 1202986844),
    (1223, "16,18,20,32,33,39", 0, 16, 1857554133),
    (1224, "9,18,21,27,44,45", 0, 12, 2414855250),
    (1225, "8,9,19,25,41,42", 0, 13, 2228133087),
    (1226, "4,6,13,17,26,28", 0, 10, 2815230113),
    (1227, "1,14,16,34,41,44", 0, 11, 2674808455),
    (1228, "24,29,30,31,35,44", 0, 11, 2698334421),
    (1229, "12,13,29,34,37,42", 0, 8, 3519759000),
    (1230, "3,8,9,22,28,42", 0, 16, 1771357196),
    (1231, "4,13,14,18,31,38", 0, 17, 1652990074),
    (1232, "12,15,19,22,24,36", 0, 11, 2533260819),
    (1233, "2,7,20,25,37,40", 0, 31, 837965396),
    (1234, "1,15,19,31,35,43", 0, 18, 1595129563),
    (1235, "6,7,11,15,39,43", 0, 9, 3090961625),
    (1236, "12,18,21,29,34,38", 0, 11, 2441919375),
]


# ===============================================================
#  데이터 저장소
# ===============================================================
class DrawStore:
    def __init__(self):
        self.rows = []
        self.load()

    # -- 입출력 --------------------------------------------------
    def load(self):
        if os.path.exists(DRAWS_CACHE):
            try:
                with open(DRAWS_CACHE, "r", encoding="utf-8") as f:
                    self.rows = json.load(f)
                self._normalize()
                if self.rows:
                    return
            except Exception as e:
                print("[!] 캐시 읽기 실패:", e)
        self.rows = [{
            "round": r[0],
            "date": round_date(r[0]).isoformat(),
            "nums": sorted(int(x) for x in r[1].split(",")),
            "bonus": r[2], "winners": r[3], "prize": r[4],
        } for r in SEED]
        self.save()

    def _normalize(self):
        seen, out = set(), []
        for r in self.rows:
            try:
                n = int(r["round"])
                if n in seen:
                    continue
                seen.add(n)
                r["round"] = n
                r["nums"] = sorted(int(x) for x in r["nums"])[:6]
                r["bonus"] = int(r.get("bonus") or 0)
                r["winners"] = int(r.get("winners") or 0)
                r["prize"] = int(r.get("prize") or 0)
                r.setdefault("date", round_date(n).isoformat())
                if len(r["nums"]) == 6:
                    out.append(r)
            except Exception:
                continue
        out.sort(key=lambda x: x["round"])
        self.rows = out

    def save(self):
        try:
            with open(DRAWS_CACHE, "w", encoding="utf-8") as f:
                json.dump(self.rows, f, ensure_ascii=False)
        except Exception as e:
            print("[!] 캐시 저장 실패:", e)

    def drop_future(self):
        """추첨 전인데 저장돼 버린 행을 지운다. 중복 번호의 원인."""
        today = dt.date.today()
        before = len(self.rows)
        self.rows = [r for r in self.rows
                     if round_date(int(r["round"])) <= today]
        if len(self.rows) != before:
            self.save()
        return before - len(self.rows)

    def fix_prizes(self):
        """이전 버전이 총액으로 저장해 둔 행을 1인당으로 고친다."""
        ch = 0
        for r in self.rows:
            b = r.get("prize")
            normalize_prize(r)
            if r.get("prize") != b:
                ch += 1
        if ch:
            self.save()
        return ch

    def merge(self, items):
        by = {r["round"]: r for r in self.rows}
        added = 0
        for it in items:
            n = it["round"]
            if n not in by or not by[n].get("bonus"):
                by[n] = it
                added += 1
        self.rows = sorted(by.values(), key=lambda x: x["round"])
        self._normalize()
        self.save()
        return added

    # -- 조회 ---------------------------------------------------
    @property
    def ok(self):
        return bool(self.rows)

    def get(self, rnd):
        return next((r for r in self.rows if r["round"] == rnd), None)

    def newest(self):
        return self.rows[-1]["round"] if self.rows else 0

    def oldest(self):
        return self.rows[0]["round"] if self.rows else 0

    def recent(self, n=100):
        return self.rows[-n:] if n else self.rows

    def missing(self, want=100, upto=None):
        """최근 want 회 중 아직 못 받았거나 보너스번호가 빠진 회차."""
        if upto is None:
            try:
                upto = resolve_latest_round()
            except Exception:
                upto = latest_round_by_date()
        have = {r["round"] for r in self.rows if r.get("bonus")}
        start = max(1, upto - want + 1)
        return [n for n in range(start, upto + 1) if n not in have]

    # -- 판정 ---------------------------------------------------
    def check(self, nums, rnd):
        row = self.get(rnd)
        if not row:
            return None
        hit = len(set(nums) & set(row["nums"]))
        bonus_hit = bool(row["bonus"]) and row["bonus"] in nums
        if hit == 6:
            rank = 1
        elif hit == 5 and bonus_hit:
            rank = 2
        elif hit == 5:
            rank = 3
        elif hit == 4:
            rank = 4
        elif hit == 3:
            rank = 5
        else:
            rank = 0
        return {"rank": rank, "hit": hit, "bonus": bonus_hit,
                "unsure": rank in (2, 3) and not row["bonus"]}


DRAWS = DrawStore()


# ===============================================================
#  통계 엔진
# ===============================================================
class Stats:
    def __init__(self, rows):
        self.rows = rows
        self.n = len(rows)

    def freq(self):
        c = Counter()
        for r in self.rows:
            c.update(r["nums"])
        for i in range(1, 46):
            c.setdefault(i, 0)
        return c

    def chi_square(self):
        """번호가 균등분포와 구분되는지. df=44, 5% 임계값 60.48."""
        if self.n < 10:
            return None
        c = self.freq()
        e = self.n * 6 / 45.0
        x2 = sum((v - e) ** 2 / e for v in c.values())
        return {"x2": x2, "df": 44, "crit": 60.48, "exp": e,
                "significant": x2 > 60.48}

    def winners(self):
        w = [r["winners"] for r in self.rows if r.get("winners")]
        if len(w) < 3:
            return None
        m = sum(w) / len(w)
        var = sum((x - m) ** 2 for x in w) / len(w)
        return {"mean": m, "var": var, "ratio": var / m if m else 0,
                "min": min(w), "max": max(w), "n": len(w),
                "in_band": sum(1 for x in w if 10 <= x <= 20) / len(w),
                "p_zero": math.exp(-m)}

    def prize_spread(self):
        rs = [r for r in self.rows if r.get("winners") and r.get("prize")]
        if len(rs) < 3:
            return None
        lo = min(rs, key=lambda r: r["winners"])
        hi = max(rs, key=lambda r: r["winners"])
        return {"lo": lo, "hi": hi,
                "times": lo["prize"] / hi["prize"] if hi["prize"] else 0}

    def shape(self):
        s = [sum(r["nums"]) for r in self.rows]
        o = Counter(sum(1 for x in r["nums"] if x % 2) for r in self.rows)
        h = Counter(sum(1 for x in r["nums"] if x >= 32) for r in self.rows)
        return {"sum_min": min(s), "sum_max": max(s),
                "sum_mean": sum(s) / len(s), "odd": o, "high": h}


def spearman(a, b):
    """순위상관. scipy 없이 쓴다."""
    n = len(a)
    if n < 3:
        return 0.0

    def rank(v):
        order = sorted(range(n), key=lambda i: v[i])
        r = [0.0] * n
        i = 0
        while i < n:
            j = i
            while j + 1 < n and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2.0
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r

    ra, rb = rank(a), rank(b)
    ma, mb = sum(ra) / n, sum(rb) / n
    num = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    den = (sum((x - ma) ** 2 for x in ra)
           * sum((y - mb) ** 2 for y in rb)) ** 0.5
    return num / den if den else 0.0


class Popularity:
    """
    조합이 '사람들이 많이 고르는 형태'인지 점수화한다.

    왜 필요한가
        1등 확률은 어떤 조합이든 8,145,060분의 1로 같다. 바꿀 수 없다.
        하지만 1등 상금 총액은 고정이고 당첨자 수로 나눈다.
        실제로 1208회는 6명이 나눠 1인 50억, 1233회는 31명이 나눠 1인 8.4억
        이었다. 같은 1등인데 6배 차이다.
        인기 없는 형태를 고르면 '맞을 확률'은 그대로면서
        '맞았을 때 받는 금액'의 기댓값만 올라간다.

    가중치의 출처와 한계
        동행복권은 조합별 선택 인원을 공개하지 않는다.
        따라서 아래 가중치는 복권 구매행동 연구에서 반복 보고되는
        경향(생일 편향, 마킹용지 기하 패턴, 중앙 합계 선호)을
        근거로 한 추정치이며 확정된 값이 아니다.
        그래서 이 모델이 맞는지 앱 안에서 직접 검정할 수 있게 했다.
        통계 탭의 '인기도 모델 검정'을 보라.

    마킹용지 격자
        1~45가 가로 7칸으로 배열된다고 보고 열/행 쏠림을 센다.
        (열 = (n-1)%7, 행 = (n-1)//7)
    """

    W = {
        "생일대(1~31)": 1.6,
        "월수(1~12)": 1.1,
        "연속수": 1.3,
        "일정간격": 0.9,
        "같은 열": 0.8,
        "같은 행": 0.8,
        "중앙 합계": 3.0,
        "끝자리 반복": 0.6,
    }

    @staticmethod
    def parts(nums):
        n = sorted(nums)
        gaps = [b - a for a, b in zip(n, n[1:])]
        run = best = 1
        for g in gaps:
            run = run + 1 if g == 1 else 1
            best = max(best, run)
        cols = Counter((x - 1) % 7 for x in n)
        rws = Counter((x - 1) // 7 for x in n)
        ends = Counter(x % 10 for x in n)
        return {
            "생일대(1~31)": sum(1 for x in n if x <= 31),
            "월수(1~12)": sum(1 for x in n if x <= 12),
            "연속수": best - 1,
            "일정간격": max(Counter(gaps).values()) - 1,
            "같은 열": max(cols.values()) - 1,
            "같은 행": max(rws.values()) - 1,
            "중앙 합계": math.exp(-((sum(n) - 140) / 38.0) ** 2),
            "끝자리 반복": max(ends.values()) - 1,
        }

    @classmethod
    def raw(cls, nums):
        p = cls.parts(nums)
        return sum(cls.W[k] * p[k] for k in cls.W)

    _base = None

    @classmethod
    def baseline(cls):
        """무작위 조합 4000개의 원점수 분포. 백분위 환산에 쓴다."""
        if cls._base is None:
            rng = random.Random(20261111)
            cls._base = sorted(cls.raw(rng.sample(range(1, 46), 6))
                               for _ in range(2500))
        return cls._base

    @classmethod
    def percentile(cls, nums):
        """0~100. 높을수록 '사람들이 많이 고르는 형태'."""
        b = cls.baseline()
        return bisect.bisect_left(b, cls.raw(nums)) / len(b) * 100.0

    @classmethod
    def spread(cls, nums):
        """분산도 0~100. 높을수록 나눠 가질 사람이 적을 것으로 본다."""
        return 100.0 - cls.percentile(nums)

    @classmethod
    def validate(cls, rows):
        """
        이 모델이 실제로 맞는지 검정한다.
        과거 회차의 원점수와 그 회차 1등 당첨자 수의 순위상관을 구하고,
        당첨자 수를 무작위로 섞은 순열검정으로 잡음 한계선을 만든다.
        상관이 한계선을 못 넘으면 '아직 근거 없음'이다.
        """
        rows = [r for r in rows if r.get("winners")]
        if len(rows) < 15:
            return None
        x = [cls.raw(r["nums"]) for r in rows]
        y = [r["winners"] for r in rows]
        rho = spearman(x, y)
        rng = random.Random(7)
        ys = list(y)
        sims = []
        for _ in range(1500):
            rng.shuffle(ys)
            sims.append(abs(spearman(x, ys)))
        sims.sort()
        thr = sims[int(len(sims) * 0.95)]
        return {"rho": rho, "thr": thr, "n": len(rows),
                "pass": abs(rho) > thr,
                "need": max(0, 200 - len(rows))}


# ===============================================================
#  네트워크 — 동행복권 JSON → 네이버 HTML 순으로 시도
# ===============================================================
UA = ("Mozilla/5.0 (Linux; Android 12) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/120.0 Mobile Safari/537.36")


_SSL_CTX = None


def _ssl_context():
    """
    안드로이드에서는 시스템 CA 경로를 파이썬이 못 찾아 HTTPS 가 전부
    URLError 로 죽는다. certifi 번들을 명시적으로 물려준다.
    그래도 실패하면 검증을 끄고라도 통신은 되게 한다(공개 조회 API 뿐).
    """
    global _SSL_CTX
    if _SSL_CTX is not None:
        return _SSL_CTX
    import ssl
    try:
        import certifi
        _SSL_CTX = ssl.create_default_context(cafile=certifi.where())
    except Exception:
        try:
            _SSL_CTX = ssl.create_default_context()
        except Exception:
            _SSL_CTX = ssl._create_unverified_context()
    return _SSL_CTX


def _get(url, timeout=8):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept-Language": "ko-KR,ko;q=0.9",
    })
    try:
        with urllib.request.urlopen(req, timeout=timeout,
                                    context=_ssl_context()) as r:
            raw = r.read()
    except Exception:
        # 인증서 문제일 가능성이 높다. 검증 없이 한 번 더.
        import ssl
        with urllib.request.urlopen(
                req, timeout=timeout,
                context=ssl._create_unverified_context()) as r:
            raw = r.read()
    for enc in ("utf-8", "euc-kr", "cp949"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", "replace")


def fetch_dhlottery(rnd):
    """1순위. 공식 사이트의 JSON 엔드포인트. 보너스번호까지 다 준다."""
    url = ("https://www.dhlottery.co.kr/common.do"
           f"?method=getLottoNumber&drwNo={rnd}")
    j = json.loads(_get(url))
    if j.get("returnValue") != "success":
        raise ValueError("returnValue != success")
    return {
        "round": int(j["drwNo"]),
        "date": j.get("drwNoDate") or round_date(rnd).isoformat(),
        "nums": sorted(int(j[f"drwtNo{i}"]) for i in range(1, 7)),
        "bonus": int(j["bnusNo"]),
        "winners": int(j.get("firstPrzwnerCo") or 0),
        "prize": int(j.get("firstWinamnt") or 0),
        "src": "동행복권",
    }


def parse_naver(html, rnd):
    """
    2순위. 네이버 검색결과 파싱.
    구조: div.win_number_box 안에 번호 공들, div.win_info_box 에 당첨금.
    클래스명이 바뀔 수 있어 여러 갈래로 시도한다.
    """
    box = None
    m = re.search(r'class="[^"]*win_number_box[^"]*"(.{0,3000}?)'
                  r'class="[^"]*win_info_box', html, re.S)
    if m:
        box = m.group(1)
    if box is None:
        m = re.search(r'(?:number_box|win_number)(.{0,2500})', html, re.S)
        box = m.group(1) if m else None
    if box is None:
        raise ValueError("번호 영역을 못 찾음")

    nums = [int(x) for x in re.findall(
        r'class="[^"]*ball[^"]*"[^>]*>\s*(\d{1,2})\s*<', box)]
    if len(nums) < 7:
        nums = [int(x) for x in re.findall(r'>\s*(\d{1,2})\s*<', box)]
    nums = [n for n in nums if 1 <= n <= 45]
    if len(nums) < 6:
        raise ValueError(f"번호 부족: {nums}")

    main, bonus = sorted(nums[:6]), (nums[6] if len(nums) > 6 else 0)
    if len(set(main)) != 6:
        raise ValueError("중복 번호")

    winners = prize = 0
    mp = re.search(r'([\d,]{9,})\s*원', html)
    if mp:
        prize = int(mp.group(1).replace(",", ""))
    mw = re.search(r'당첨게임\s*수\s*(\d+)', html)
    if mw:
        winners = int(mw.group(1))

    return {"round": rnd, "date": round_date(rnd).isoformat(),
            "nums": main, "bonus": bonus, "winners": winners,
            "prize": prize, "src": "네이버"}


def fetch_naver(rnd):
    url = ("https://search.naver.com/search.naver?where=nexearch"
           f"&query={rnd}%ED%9A%8C+%EB%A1%9C%EB%98%90%EB%8B%B9%EC%B2%A8%EB%B2%88%ED%98%B8")
    html = _get(url)
    # 네이버는 없는 회차를 물으면 최신 회차 결과를 보여 준다.
    # 화면에 적힌 회차 번호가 요청과 다르면 버린다.
    seen = {int(x) for x in re.findall(r"(\d{3,4})\s*회", html)}
    if seen and rnd not in seen:
        raise ValueError(f"회차 불일치: 요청 {rnd}, 화면 {sorted(seen)[:5]}")
    return parse_naver(html, rnd)


def normalize_prize(row):
    """
    1등 당첨금은 '1인당' 이어야 한다.
    네이버 폴백 파서가 총 당첨금(200~350억)을 집어오는 경우가 있어,
    당첨자가 둘 이상인데 금액이 150억을 넘으면 총액으로 보고 나눈다.
    """
    try:
        w = int(row.get("winners") or 0)
        p = int(row.get("prize") or 0)
        if w >= 2 and p > 15_000_000_000:
            row["prize"] = p // w
    except Exception:
        pass
    return row


def fetch_round(rnd, tries=5):
    """
    폴백 사슬. 마지막 오류를 함께 돌려준다.
    동행복권은 짧은 시간에 요청이 몰리면 빈 응답을 주므로 재시도한다.
    """
    # 추첨 전 회차를 조회하면 네이버가 '최신 회차' 결과를 그대로 돌려줘
    # 1242 회에 1241 회 번호가 저장되는 사고가 난다. 애초에 막는다.
    if round_date(rnd) > dt.date.today():
        return None, "아직 추첨 전"
    last = None
    for attempt in range(tries):
        for fn in (fetch_dhlottery, fetch_naver):
            try:
                r = fn(rnd)
                if r and len(r["nums"]) == 6:
                    return normalize_prize(r), None
            except Exception as e:
                last = f"{fn.__name__}: {type(e).__name__}"
        if attempt < tries - 1:
            import time as _t
            _t.sleep(0.5 * (attempt + 1))
    return None, last


def net_diagnose():
    """설정 화면에서 눌러 쓰는 연결 진단."""
    out = []
    for name, url in (("동행복권", "https://www.dhlottery.co.kr/common.do"
                       "?method=getLottoNumber&drwNo=1200"),
                      ("네이버", "https://search.naver.com/search.naver?query=1"),
                      ("주소검색", "https://nominatim.openstreetmap.org/"
                       "search?format=jsonv2&limit=1&q=seoul")):
        try:
            _get(url, timeout=7)
            out.append(f"OK   {name}")
        except Exception as e:
            out.append(f"실패 {name} — {type(e).__name__}")
    r = locate_by_ip()
    out.append(f"OK   IP위치 — {r[2]}" if r else "실패 IP위치 — 전부 거부")
    out.append("     ※ IP위치는 통신사 회선 등록지라 수십 km 어긋납니다.")
    g = android_last_location()
    if g:
        out.append(f"OK   GPS — {g[0]:.4f}, {g[1]:.4f}")
    elif platform == "android":
        out.append("실패 GPS — 위치 권한과 위치 사용 설정을 확인하세요")
    return "\n".join(out)


class Updater:
    """백그라운드 수집기. UI 갱신은 반드시 Clock 으로 메인 스레드에 넘긴다."""

    def __init__(self):
        self.busy = False
        self.cancel = False

    def run(self, rounds, on_progress, on_done):
        if self.busy:
            return False
        self.busy, self.cancel = True, False

        def work():
            from concurrent.futures import ThreadPoolExecutor, as_completed
            got, fails, err = [], 0, None
            retry_list = set(rounds)
            total = len(rounds)
            done = 0
            # 1차: 재시도 없이 6개씩 빠르게 훑는다.
            # 2차: 실패한 회차만 골라 재시도를 붙여 다시 받는다.
            with ThreadPoolExecutor(max_workers=6) as ex:
                futs = {ex.submit(fetch_round, r, 1): r for r in rounds}
                for f in as_completed(futs):
                    if self.cancel:
                        break
                    try:
                        row, e = f.result()
                    except Exception as ex_:
                        row, e = None, type(ex_).__name__
                    if row:
                        got.append(row)
                        retry_list.discard(futs[f])
                    else:
                        fails += 1
                        err = err or e
                    done += 1
                    Clock.schedule_once(
                        lambda _dt, a=done, b=total, c=len(got):
                        on_progress(a, b, c), 0)

            # 1차에서 놓친 회차만 천천히 다시 받는다. 전체를 재시도하는
            # 것보다 훨씬 빠르고 성공률도 높다.
            if retry_list and not self.cancel:
                for r in sorted(retry_list, reverse=True):
                    if self.cancel:
                        break
                    row, e = fetch_round(r, 3)
                    if row:
                        got.append(row)
                        fails -= 1
                    else:
                        err = err or e
                    Clock.schedule_once(
                        lambda _dt, a=done, b=total, c=len(got):
                        on_progress(a, b, c), 0)
            added = DRAWS.merge(got) if got else 0
            self.busy = False
            Clock.schedule_once(
                lambda _dt: on_done(len(got), added, fails, err), 0)

        threading.Thread(target=work, daemon=True).start()
        return True


UPDATER = Updater()


# ===============================================================
#  생성 엔진
# ===============================================================
class Filters:
    """
    기본값은 실제 당첨번호 29회(1208~1236)를 기준으로 잡았다.
    이전 버전의 기본값(합 100~175 / 고번호 2개 이상)은
    실제 1등 번호의 48%를 미리 버리고 있었다.
    """

    PRESETS = {
        "넓게": dict(sum_min=90, sum_max=200, odd_min=0, odd_max=6,
                   max_consecutive=3, high_min=0, avoid_popular=False),
        "표준": dict(sum_min=100, sum_max=185, odd_min=1, odd_max=5,
                   max_consecutive=3, high_min=1, avoid_popular=False),
        "분산형": dict(sum_min=100, sum_max=185, odd_min=1, odd_max=5,
                    max_consecutive=2, high_min=2, avoid_popular=True),
    }

    def __init__(self):
        self.include = set()
        self.exclude = set()
        self.carryover_max = 3
        self.apply_preset("표준")

    def apply_preset(self, name):
        for k, v in self.PRESETS[name].items():
            setattr(self, k, v)
        self.preset = name

    def passes(self, nums, prev=None):
        s = set(nums)
        if self.exclude & s:
            return False
        if self.include and not self.include <= s:
            return False
        if not (self.sum_min <= sum(nums) <= self.sum_max):
            return False
        odd = sum(1 for n in nums if n % 2)
        if not (self.odd_min <= odd <= self.odd_max):
            return False
        run = best = 1
        for a, b in zip(nums, nums[1:]):
            run = run + 1 if b == a + 1 else 1
            best = max(best, run)
        if best > self.max_consecutive:
            return False
        if sum(1 for n in nums if n >= 32) < self.high_min:
            return False
        if self.avoid_popular:
            diffs = {b - a for a, b in zip(nums, nums[1:])}
            if len(diffs) == 1:
                return False
            if max(nums) <= 31:
                return False
        if prev and len(s & set(prev)) > self.carryover_max:
            return False
        return True

    def pass_rate(self, rows):
        """이 조건이 실제 과거 당첨번호를 얼마나 통과시키는가."""
        if not rows:
            return None
        keep = Filters()
        for k in ("sum_min", "sum_max", "odd_min", "odd_max",
                  "max_consecutive", "high_min", "avoid_popular"):
            setattr(keep, k, getattr(self, k))
        ok = sum(1 for r in rows if keep.passes(r["nums"]))
        return ok, len(rows)


class Generator:
    MODES = ("임의", "조합", "통계")

    def __init__(self, filters):
        self.f = filters

    def _finish(self, base, rng):
        s = {n for n in base if 1 <= n <= 45 and n not in self.f.exclude}
        s |= self.f.include
        if len(s) > 6:
            s = set(rng.sample(sorted(s), 6))
        pool = [n for n in range(1, 46) if n not in s and n not in self.f.exclude]
        if len(pool) < 6 - len(s):
            return None
        while len(s) < 6:
            n = rng.choice(pool)
            s.add(n)
            pool.remove(n)
        return sorted(s)

    def gen_random(self, rng, prev):
        return self._finish(rng.sample(range(1, 46), 4), rng)

    def gen_stat(self, rng, prev):
        if not DRAWS.ok:
            return self.gen_random(rng, prev)
        freq = Stats(DRAWS.recent(100)).freq()
        nums = list(range(1, 46))
        w = [freq.get(n, 0) + 1 for n in nums]
        picked, guard = set(), 0
        while len(picked) < 4 and guard < 300:
            picked.add(rng.choices(nums, weights=w, k=1)[0])
            guard += 1
        return self._finish(picked, rng)

    def gen_combo(self, rng, rnd, d):
        """이달의 이벤트 + 회차 + 랜덤. 시드 고정이라 재현된다."""
        seeds = []
        s = str(rnd)
        for i in range(len(s) - 1):
            v = int(s[i:i + 2])
            if 1 <= v <= 45:
                seeds.append(v)
        seeds.append(int(s) % 45 + 1)
        _, order = current_solar_term(d)
        seeds.append(order)
        for ev in events_for(d):
            if ev["kind"] == "기념일":
                e = ev["date"]
                if 1 <= e.day <= 45:
                    seeds.append(e.day)
                seeds.append((e.month * e.day) % 45 + 1)
        rng.shuffle(seeds)
        return self._finish(seeds[:3], rng)

    def batch(self, mode, count=10, rnd=None, d=None, spread=False):
        """
        spread=True 면 후보를 6배로 뽑아 분산도 높은 순으로 추린다.
        적중 확률은 그대로고, 당첨 시 나눠 가질 인원의 기댓값만 낮춘다.
        """
        rnd = rnd or (DRAWS.newest() + 1)
        d = d or round_date(rnd)
        prev = DRAWS.rows[-1]["nums"] if DRAWS.ok else None
        want = count * 6 if spread else count
        out, seen = [], set()
        for i in range(want * 400):
            if len(out) >= want:
                break
            if mode == "조합":
                key = f"{APP_NAME}|{rnd}|{d}|{len(out)}|{i}"
                rng = random.Random(
                    int(hashlib.sha256(key.encode()).hexdigest()[:16], 16))
                cand = self.gen_combo(rng, rnd, d)
            else:
                rng = random.Random()
                cand = (self.gen_stat(rng, prev) if mode == "통계"
                        else self.gen_random(rng, prev))
            if not cand or not self.f.passes(cand, prev):
                continue
            t = tuple(cand)
            if t in seen:
                continue
            seen.add(t)
            out.append(cand)
        if spread:
            out.sort(key=Popularity.spread, reverse=True)
            out = out[:count]
        return out


# ===============================================================
#  24절기 · 기념일
# ===============================================================
SOLAR_TERMS = [
    "춘분", "청명", "곡우", "입하", "소만", "망종", "하지", "소서",
    "대서", "입추", "처서", "백로", "추분", "한로", "상강", "입동",
    "소설", "대설", "동지", "소한", "대한", "입춘", "우수", "경칩",
]

FIXED_EVENTS = {
    (1, 1): "신정", (2, 14): "발렌타인데이", (3, 1): "삼일절",
    (3, 14): "화이트데이", (4, 1): "만우절", (4, 5): "식목일",
    (5, 5): "어린이날", (5, 8): "어버이날", (5, 15): "스승의날",
    (6, 6): "현충일", (7, 17): "제헌절", (8, 15): "광복절",
    (10, 3): "개천절", (10, 9): "한글날", (11, 11): "빼빼로데이",
    (12, 25): "성탄절", (12, 31): "제야",
}


def julian_day(d):
    y, m = d.year, d.month
    if isinstance(d, dt.datetime):
        day = d.day + (d.hour + d.minute / 60.0) / 24.0
    else:
        day = d.day
    if m <= 2:
        y, m = y - 1, m + 12
    a = y // 100
    b = 2 - a + a // 4
    return int(365.25 * (y + 4716)) + int(30.6001 * (m + 1)) + day + b - 1524.5


def solar_longitude(d):
    t = (julian_day(d) - 2451545.0) / 36525.0
    l0 = 280.46646 + 36000.76983 * t + 0.0003032 * t * t
    m = math.radians(357.52911 + 35999.05029 * t - 0.0001537 * t * t)
    c = ((1.914602 - 0.004817 * t - 0.000014 * t * t) * math.sin(m)
         + (0.019993 - 0.000101 * t) * math.sin(2 * m)
         + 0.000289 * math.sin(3 * m))
    omega = math.radians(125.04 - 1934.136 * t)
    return (l0 + c - 0.00569 - 0.00478 * math.sin(omega)) % 360.0


def current_solar_term(d):
    """절입 시각이 그 날 안에 들면 그 날부터 새 절기 (한국 관행)."""
    d = dt.datetime(d.year, d.month, d.day, 14, 59)   # 23:59 KST
    idx = int(solar_longitude(d) // 15) % 24
    return SOLAR_TERMS[idx], (idx - 21) % 24 + 1


def events_for(d, window=7):
    out = []
    term, order = current_solar_term(d)
    out.append({"name": term, "kind": "절기", "value": order, "date": d})
    for off in range(-window, window + 1):
        dd = d + dt.timedelta(days=off)
        if (dd.month, dd.day) in FIXED_EVENTS:
            out.append({"name": FIXED_EVENTS[(dd.month, dd.day)],
                        "kind": "기념일",
                        "value": dd.month * 100 + dd.day, "date": dd})
    return out


# ===============================================================
#  내 번호 저장소
# ===============================================================
class Vault:
    def __init__(self):
        self.items = []
        self.load()

    def load(self):
        if os.path.exists(VAULT_PATH):
            try:
                with open(VAULT_PATH, "r", encoding="utf-8") as f:
                    self.items = json.load(f)
            except Exception:
                self.items = []

    def save(self):
        try:
            with open(VAULT_PATH, "w", encoding="utf-8") as f:
                json.dump(self.items, f, ensure_ascii=False, indent=1)
        except Exception as e:
            print("[!] 저장 실패:", e)

    def add(self, nums, rnd, mode):
        self.items.append({
            "id": dt.datetime.now().strftime("%Y%m%d%H%M%S%f"),
            "round": rnd, "nums": nums, "mode": mode,
            "saved": dt.datetime.now().isoformat(timespec="seconds"),
            "draw_date": round_date(rnd).isoformat(),
        })
        self.save()

    def remove(self, iid):
        self.items = [x for x in self.items if x["id"] != iid]
        self.save()

    def by_round(self):
        g = {}
        for it in self.items:
            g.setdefault(it["round"], []).append(it)
        return sorted(g.items(), key=lambda x: -x[0])

    def spend_this_month(self):
        now = dt.date.today()
        n = sum(1 for it in self.items
                if it["saved"][:7] == now.isoformat()[:7])
        return n, n * TICKET_PRICE


VAULT = Vault()


def load_prefs():
    if os.path.exists(PREFS_PATH):
        try:
            with open(PREFS_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {"budget": 20000}


def save_prefs(p):
    try:
        with open(PREFS_PATH, "w", encoding="utf-8") as f:
            json.dump(p, f, ensure_ascii=False)
    except Exception:
        pass


PREFS = load_prefs()


# ===============================================================
#  QR 파서
# ===============================================================
# 실물 용지(1232회)로 확인한 포맷
#   http://qr.dhlottery.co.kr/?v=1232 q091314172130 q021424253138 ...
#                                 회차  [구분자+2자리x6] x 게임수  + 꼬리 18자리
#   꼬리 = TR번호 10자리 + 판매점코드 8자리
#   구분자 q = 자동 (실물 확인). m/n/p 는 수동·반자동으로 추정하며 미검증.
QR_MODE = {"q": "자동", "m": "수동", "n": "반자동", "p": "반자동"}


def parse_lotto_qr(text):
    text = (text or "").strip()
    m = re.search(r"[?&]v=([0-9A-Za-z]+)", text)
    payload = m.group(1) if m else text
    if not payload:
        return None, "내용이 비어 있습니다."
    m = re.match(r"^(\d{4})(.*)$", payload)
    if not m:
        return None, "회차 4자리를 찾지 못했습니다."
    rnd, rest = int(m.group(1)), m.group(2)

    def ok(d):
        n = sorted(int(d[i:i + 2]) for i in range(0, 12, 2))
        return n if len(set(n)) == 6 and all(1 <= x <= 45 for x in n) else None

    games, modes = [], []
    for blk in re.finditer(r"([A-Za-z])(\d{12})", rest):
        n = ok(blk.group(2))
        if n:
            games.append(n)
            modes.append(QR_MODE.get(blk.group(1).lower(), "?"))
    tail = re.sub(r"[A-Za-z]\d{12}", "", rest)
    if not games:
        for i in range(0, len(rest) - 11, 12):
            if rest[i:i + 12].isdigit():
                n = ok(rest[i:i + 12])
                if n:
                    games.append(n)
                    modes.append("?")
        tail = ""
    if not games:
        return None, "번호 블록을 해석하지 못했습니다."
    return {"round": rnd, "games": games, "modes": modes,
            "tr": tail[:10] if len(tail) >= 10 else "",
            "store": tail[10:] if len(tail) > 10 else ""}, None


# ===============================================================
#  UI 부품
# ===============================================================
def lbl(text, size=13.5, color=None, bold=True, disp=False, **kw):
    kw.setdefault("halign", "left")
    kw.setdefault("valign", "middle")
    w = Label(text=text, font_name=(FONT_D if disp else FONT),
              font_size=dp(size * UI.scale), bold=bold,
              color=color or T.text, markup=True, **kw)
    w.bind(size=lambda i, v: setattr(i, "text_size", v))
    return w


def money(v):
    if not v:
        return "-"
    if v >= 100000000:
        return f"{v / 100000000:.1f}억"
    if v >= 10000:
        return f"{v / 10000:.0f}만"
    return f"{v:,}"


class Card(BoxLayout):
    """면 + 1px 테두리. 앱 전체의 기본 그릇."""

    def __init__(self, bg=None, radius=16, border=True, bcol=None, **kw):
        super().__init__(**kw)
        self._r = radius
        with self.canvas.before:
            self._c = Color(*(bg or T.surface))
            self._rect = RoundedRectangle(radius=[dp(radius)])
            self._bc = Color(*(bcol or T.stroke)) if border else Color(0, 0, 0, 0)
            self._line = Line(width=dp(1))
        self.bind(pos=self._sync, size=self._sync)

    def _sync(self, *a):
        self._rect.pos, self._rect.size = self.pos, self.size
        self._line.rounded_rectangle = (
            self.x, self.y, self.width, self.height, dp(self._r))

    def set_bg(self, c):
        self._c.rgba = c

    def set_border(self, c):
        self._bc.rgba = c


class ScrollSafe:
    """
    끌기가 시작되면 버튼이 터치를 놓아 ScrollView 가 이어받게 한다.
    이게 없으면 버튼 위에서 시작한 스크롤이 눌림으로만 처리된다.
    """

    def on_touch_move(self, touch):
        if touch.grab_current is self:
            dx = abs(touch.sx - touch.osx) * Window.width
            dy = abs(touch.sy - touch.osy) * Window.height
            if dx > dp(10) or dy > dp(10):
                touch.ungrab(self)
                self.state = "normal"
        return super().on_touch_move(touch)


class TapCard(ScrollSafe, ButtonBehavior, Card):
    pass


class Btn(ScrollSafe, ButtonBehavior, Card):
    def __init__(self, text, bg=None, fg=None, fsize=13.5, bold=True,
                 border=False, **kw):
        super().__init__(bg=bg or T.juhong, radius=12, border=border, **kw)
        self.label = lbl(text, size=fsize, color=fg or (1, 1, 1, 1),
                         bold=bold, halign="center")
        self.add_widget(self.label)

    @property
    def text(self):
        return self.label.text

    @text.setter
    def text(self, v):
        self.label.text = v


class Chip(ScrollSafe, ButtonBehavior, Card):
    def __init__(self, text, active=False, on_toggle=None, accent=None, **kw):
        super().__init__(bg=T.field, radius=11, **kw)
        self.active, self.on_toggle = active, on_toggle
        self.accent = accent or T.chungrok
        self.label = lbl(text, size=12.5, halign="center", bold=True)
        self.add_widget(self.label)
        self.bind(on_release=self._tap)
        self._paint(False)

    def _tap(self, *a):
        self.active = not self.active
        self._paint()
        if self.on_toggle:
            self.on_toggle(self)

    def set_active(self, v, animate=True):
        if v != self.active:
            self.active = v
            self._paint(animate)

    def _paint(self, animate=True):
        tgt = self.accent if self.active else T.field
        brd = self.accent if self.active else T.stroke
        if animate:
            Animation(rgba=tgt, d=.14, t="out_quad").start(self._c)
            Animation(rgba=brd, d=.14, t="out_quad").start(self._bc)
        else:
            self._c.rgba, self._bc.rgba = tgt, brd
        self.label.color = (1, 1, 1, 1) if self.active else T.dim


class Ball(Widget):
    """구간색 + 상단 광택 + 얇은 테두리."""

    def __init__(self, n, d=32, faded=False, **kw):
        super().__init__(size_hint=(None, None), size=(dp(d), dp(d)), **kw)
        self.d = d
        base = T.ball(n)
        if faded:
            base = base[:3] + (0.22,)
        with self.canvas:
            self._c = Color(*base)
            self._e = Ellipse()
            self._g = Color(1, 1, 1, 0.05 if faded else 0.28)
            self._gl = Ellipse()
            self._sc = Color(0, 0, 0, 0.04 if faded else 0.14)
            self._sh = Ellipse()
        self._lb = Label(text=str(n), font_name=FONT_D,
                         font_size=dp(d * 0.40 * min(1.12, UI.scale)), bold=True,
                         color=(1, 1, 1, 0.3) if faded else (0.09, 0.1, 0.12, 1))
        self.add_widget(self._lb)
        self.bind(pos=self._sync, size=self._sync)

    def _sync(self, *a):
        x, y, w, h = self.x, self.y, self.width, self.height
        self._e.pos, self._e.size = (x, y), (w, h)
        self._sh.pos = (x + w * .16, y + h * .04)
        self._sh.size = (w * .68, h * .34)
        self._gl.pos = (x + w * .18, y + h * .50)
        self._gl.size = (w * .52, h * .34)
        self._lb.pos, self._lb.size = self.pos, self.size


class BallRow(BoxLayout):
    def __init__(self, nums, d=32, bonus=None, faded=False, **kw):
        super().__init__(orientation="horizontal", spacing=dp(5),
                         size_hint_y=None, height=dp(d), **kw)
        for n in nums:
            self.add_widget(Ball(n, d, faded))
        if bonus:
            self.add_widget(lbl("+", size=14, color=T.dim, halign="center",
                                size_hint_x=None, width=dp(12)))
            self.add_widget(Ball(bonus, d, faded))
        self.add_widget(Widget())


class ProgressBarKR(Widget):
    """수집 진행을 막대로 보여준다. 0.0~1.0"""

    def __init__(self, **kw):
        super().__init__(**kw)
        self.value = 0.0
        self.label = ""
        with self.canvas:
            self._c0 = Color(*T.stroke)
            self._bg = RoundedRectangle(radius=[dp(5)])
            self._c1 = Color(*T.chungrok)
            self._fg = RoundedRectangle(radius=[dp(5)])
        self.bind(pos=self._redraw, size=self._redraw)

    def _redraw(self, *a):
        self._bg.pos, self._bg.size = self.pos, self.size
        self._fg.pos = self.pos
        self._fg.size = (max(dp(6), self.width * self.value), self.height)

    def set(self, v, label=""):
        self.value = max(0.0, min(1.0, v))
        self.label = label
        self._redraw()


class SectionTitle(BoxLayout):
    """오방색 눈금 + 제목. 화면 안에서 구획을 나누는 장치."""

    def __init__(self, text, idx=0, sub="", **kw):
        super().__init__(orientation="horizontal", spacing=dp(9),
                         size_hint_y=None, height=dp(24), **kw)
        tick = Widget(size_hint=(None, None), size=(dp(3), dp(15)),
                      pos_hint={"center_y": .5})
        with tick.canvas:
            Color(*T.OBANG[idx % len(T.OBANG)])
            r = RoundedRectangle(pos=tick.pos, size=tick.size,
                                 radius=[dp(2)])

        def sync(*_a):
            r.pos, r.size = tick.pos, tick.size
        tick.bind(pos=sync, size=sync)
        self.add_widget(tick)
        self.add_widget(lbl(text, size=14, bold=True, disp=True,
                            shorten=True, shorten_from="right"))
        if sub:
            self.add_widget(lbl(sub, size=10.5, color=T.faint,
                                halign="right", size_hint_x=None,
                                width=dp(96)))


class TapInput(TextInput):
    """
    기본 동작을 그대로 쓰되, 스크롤 제스처가 시작되면 포커스를 놓아
    자판이 올라온 채 남지 않게 한다. 팝업 등 ScrollView 밖에서도
    평소처럼 입력된다.
    """

    def __init__(self, **kw):
        # 안드로이드 기본 선택 팝업(Select All / Paste)은 ScrollView 좌표를
        # 따라오지 않아 화면 위에 그대로 떠 버리고, 길게 눌린 것으로 오인되어
        # 스크롤까지 막는다. 생성 화면처럼 입력창이 많은 곳에서 특히 심하다.
        kw.setdefault("use_bubble", False)
        kw.setdefault("use_handles", False)
        super().__init__(**kw)

    def on_touch_down(self, touch):
        r = super().on_touch_down(touch)
        if self.collide_point(*touch.pos):
            touch.ud["_ti"] = self
        return r

    def on_touch_up(self, touch):
        r = super().on_touch_up(touch)
        if touch.ud.get("_ti") is self and self.collide_point(*touch.pos):
            dx = abs(touch.sx - touch.osx) * Window.width
            dy = abs(touch.sy - touch.osy) * Window.height
            if dx < dp(16) and dy < dp(16) and not self.focus:
                # ScrollView 가 down/up 을 몰아서 다시 보내는 사이에
                # 포커스가 풀리므로 한 프레임 뒤에 확정한다.
                Clock.schedule_once(
                    lambda *a: setattr(self, "focus", True), 0.05)
        return r

    def on_touch_move(self, touch):
        if touch.ud.get("_ti") is self:
            # 화면 절대 좌표로 재야 스크롤과 탭이 구분된다.
            dx = abs(touch.sx - touch.osx) * Window.width
            dy = abs(touch.sy - touch.osy) * Window.height
            if dx > dp(16) or dy > dp(16):
                touch.ud["_ti"] = None
                try:
                    self.cancel_selection()
                except Exception:
                    pass
                self.focus = False
        return super().on_touch_move(touch)


class Field(BoxLayout):
    def __init__(self, caption, text="", hint="", numeric=False, **kw):
        super().__init__(orientation="vertical", spacing=dp(5),
                         size_hint_y=None,
                         height=dp(60 * max(1.0, UI.scale)), **kw)
        self.add_widget(lbl(caption, size=11, color=T.dim,
                            size_hint_y=None, height=dp(15)))
        self.input = TapInput(
            text=text, hint_text=hint, font_name=FONT,
            font_size=dp(13.5 * UI.scale), multiline=False,
            size_hint_y=None, height=dp(38 * max(1.0, UI.scale)),
            input_filter="int" if numeric else None,
            background_color=T.field, foreground_color=T.text,
            cursor_color=T.chija, hint_text_color=T.faint,
            padding=[dp(11), dp(10), dp(11), dp(10)],
            background_normal="", background_active="")
        self.add_widget(self.input)

    @property
    def value(self):
        return self.input.text.strip()


class Bars(Widget):
    """1~45 출현 빈도 막대."""

    def __init__(self, counts, hot=None, **kw):
        super().__init__(size_hint_y=None, height=dp(86), **kw)
        self.counts = counts
        self.hot = hot or set()
        self.bind(pos=self._draw, size=self._draw)

    def update(self, counts, hot=None):
        self.counts = counts
        self.hot = hot or set()
        self._draw()

    def _draw(self, *a):
        self.canvas.clear()
        if not self.counts or self.width <= 0:
            return
        mx = max(self.counts.values()) or 1
        gap = dp(1.5)
        bw = (self.width - gap * 44) / 45.0
        with self.canvas:
            Color(*T.stroke)
            Line(points=[self.x, self.y + dp(11),
                         self.x + self.width, self.y + dp(11)], width=dp(.8))
            for i in range(45):
                n = i + 1
                v = self.counts.get(n, 0)
                h = max(dp(2), (self.height - dp(16)) * v / mx)
                c = T.ball(n)
                Color(*(c if n in self.hot else c[:3] + (0.4,)))
                RoundedRectangle(
                    pos=(self.x + i * (bw + gap), self.y + dp(12)),
                    size=(bw, h), radius=[dp(1.5)])


def toast(msg, title="알림"):
    box = BoxLayout(orientation="vertical", padding=dp(18), spacing=dp(14))
    lines = msg.count("\n") + 1
    box.add_widget(lbl(msg, size=13.5, halign="center", size_hint_y=None,
                       height=dp(13.5 * 1.62 * UI.scale) * lines))
    p = Popup(title=title, title_font=FONT, title_size=dp(14), content=box,
              size_hint=(0.86, None),
              height=(dp(13.5 * 1.62 * UI.scale) * lines
                      + dp(18) * 2 + dp(14) + dp(42) + dp(46)),
              separator_color=T.juhong, background_color=(0, 0, 0, .72))
    b = Btn("확인", bg=T.juhong, size_hint_y=None, height=dp(42))
    b.bind(on_release=p.dismiss)
    box.add_widget(b)
    p.open()


def parse_nums(text):
    return {int(t) for t in re.split(r"[,\s]+", text or "")
            if t.isdigit() and 1 <= int(t) <= 45}


class SafeScroll(ScrollView):
    """
    ScrollView 는 진행 중인 터치를 _touch 에 담아둔다.
    자식 버튼이 중간에 터치를 가로채면 정리 절차가 건너뛰어져 _touch 에
    이미 끝난 터치가 남고, 그 뒤로는 새 터치가 와도 "이미 스크롤 중" 으로
    보고 무시해 버린다. 손을 떼면 안 되고 몇 번 시도해야 다시 되던 증상이
    이것이다. 매 터치마다 남은 찌꺼기를 직접 지운다.
    """

    def on_touch_down(self, touch):
        t = getattr(self, "_touch", None)
        if t is not None and t is not touch:
            try:
                t.ungrab(self)
            except Exception:
                pass
            self._touch = None
        return super().on_touch_down(touch)

    def on_touch_up(self, touch):
        r = super().on_touch_up(touch)
        if getattr(self, "_touch", None) is touch:
            self._touch = None
        return r


def vscroll():
    # scroll_timeout 기본값 55ms 는 너무 짧아서, 손가락이 카드 위에서
    # 출발하면 카드가 터치를 먼저 가져가 스크롤이 먹지 않는다.
    # 기본 55ms 는 너무 짧아 손가락이 버튼/카드 위에서 출발하면 그쪽이
    # 터치를 먼저 가져가 버린다. 화면 가장자리에서만 스크롤되던 이유.
    sv = SafeScroll(bar_width=dp(2.5), bar_color=T.stroke,
                    bar_inactive_color=(0, 0, 0, 0),
                    scroll_timeout=250, scroll_distance=dp(7),
                    effect_cls="ScrollEffect" if platform == "android" else
                    "DampedScrollEffect")
    body = BoxLayout(orientation="vertical", padding=[dp(15), dp(14)],
                     spacing=dp(13), size_hint_y=None)
    body.bind(minimum_height=body.setter("height"))
    sv.add_widget(body)
    return sv, body


# ===============================================================
#  공유
# ===============================================================
def share_text(rnd, combos, note=""):
    d = round_date(rnd)
    wd = "월화수목금토일"[d.weekday()]
    out = [f"[{APP_NAME}] 제{rnd}회",
           f"추첨 {d.strftime('%Y.%m.%d')}({wd}) 20:35", ""]
    for i, nums in enumerate(combos):
        tag = chr(ord("A") + i) if i < 26 else str(i + 1)
        body = " ".join(f"{n:02d}" for n in nums)
        out.append(f"{tag}   {body}   (합 {sum(nums):3d} · 분산 "
                   f"{Popularity.spread(nums):.0f})")
    out.append("")
    if note:
        out.append(note)
    out.append(f"1등 확률 {TOTAL_COMBOS:,}분의 1")
    return "\n".join(out)


def do_share(text, title="번호 공유"):
    """안드로이드는 시스템 공유 시트, 그 외에는 클립보드 복사."""
    if platform == "android":
        try:
            from jnius import autoclass, cast
            PythonActivity = autoclass("org.kivy.android.PythonActivity")
            Intent = autoclass("android.content.Intent")
            String = autoclass("java.lang.String")
            it = Intent()
            it.setAction(Intent.ACTION_SEND)
            it.setType("text/plain")
            it.putExtra(Intent.EXTRA_TEXT,
                        cast("java.lang.CharSequence", String(text)))
            ch = Intent.createChooser(
                it, cast("java.lang.CharSequence", String(title)))
            ch.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            PythonActivity.mActivity.startActivity(ch)
            return True, ""
        except Exception as e:
            return False, f"{type(e).__name__}"
    try:
        from kivy.core.clipboard import Clipboard
        Clipboard.copy(text)
        return True, "clipboard"
    except Exception as e:
        return False, f"{type(e).__name__}"


def share_now(text, title="공유"):
    """
    안드로이드에서는 미리보기를 거치지 않고 바로 시스템 공유 시트를 연다.
    카카오톡·문자·메일·블루투스·드라이브 등 설치된 앱이 전부 뜬다.
    데스크톱 테스트에서는 미리보기 창으로 대체한다.
    """
    if platform == "android":
        ok, err = do_share(text, title)
        if not ok:
            share_popup(text, title)
        return
    share_popup(text, title)


def share_popup(text, title="공유"):
    box = BoxLayout(orientation="vertical", padding=dp(14), spacing=dp(10))
    sv = SafeScroll(bar_width=dp(2.5), bar_color=T.stroke)
    pre = Label(text=text, font_name=FONT, font_size=dp(12.5),
                color=T.text, halign="left", valign="top",
                size_hint_y=None)
    pre.bind(width=lambda i, v: setattr(i, "text_size", (v, None)),
             texture_size=lambda i, v: setattr(i, "height", v[1]))
    sv.add_widget(pre)
    box.add_widget(sv)

    row = BoxLayout(orientation="horizontal", spacing=dp(9),
                    size_hint_y=None, height=dp(44))
    p = Popup(title=title, title_font=FONT, title_size=dp(14), content=box,
              size_hint=(0.92, 0.72), separator_color=T.chungrok,
              background_color=(0, 0, 0, .75))

    def send(*a):
        ok, how = do_share(text, title)
        p.dismiss()
        if not ok:
            toast(f"공유에 실패했습니다 ({how})")
        elif how == "clipboard":
            toast("클립보드에 복사했습니다.\n원하는 곳에 붙여넣으세요.")
        else:
            toast("공유 앱을 열었습니다.")

    b1 = Btn("보내기", bg=T.chungrok, fsize=13.5)
    b1.bind(on_release=send)
    b2 = Btn("닫기", bg=T.field, fsize=13.5, border=True)
    b2.bind(on_release=p.dismiss)
    row.add_widget(b1)
    row.add_widget(b2)
    box.add_widget(row)
    p.open()


def _msg_label(msg, size=13.5):
    """줄 수만큼 높이를 확보한 가운데 정렬 문구."""
    lines = msg.count("\n") + 1
    return lbl(msg, size=size, halign="center", size_hint_y=None,
               height=dp(size * 1.62 * UI.scale) * lines), lines


def _dialog_height(lines, size=13.5):
    return (dp(size * 1.62 * UI.scale) * lines
            + dp(18) * 2 + dp(16) + dp(46) + dp(46))


def confirm(msg, on_yes, yes="확인", no="취소", title="확인"):
    box = BoxLayout(orientation="vertical", padding=dp(18), spacing=dp(16))
    ml, lines = _msg_label(msg)
    box.add_widget(ml)
    p = Popup(title=title, title_font=FONT, title_size=dp(14), content=box,
              size_hint=(0.86, None), height=_dialog_height(lines),
              separator_color=T.juhong, background_color=(0, 0, 0, .75))
    row = BoxLayout(orientation="horizontal", spacing=dp(10),
                    size_hint_y=None, height=dp(46))
    b1 = Btn(no, bg=T.field, fsize=13.5, border=True)
    b1.bind(on_release=p.dismiss)
    b2 = Btn(yes, bg=T.juhong, fsize=13.5)

    def go(*a):
        p.dismiss()
        Clock.schedule_once(lambda _dt: on_yes(), 0.05)
    b2.bind(on_release=go)
    row.add_widget(b1)
    row.add_widget(b2)
    box.add_widget(row)
    p.open()
    return p


def settings_popup(app):
    box = BoxLayout(orientation="vertical", padding=dp(16), spacing=dp(12))
    p = Popup(title="설정", title_font=FONT, title_size=dp(14), content=box,
              size_hint=(0.9, None), height=dp(490 * max(1.0, UI.scale)),
              separator_color=T.chungrok, background_color=(0, 0, 0, .78))

    box.add_widget(lbl("글씨 크기", size=12, color=T.dim,
                       size_hint_y=None, height=dp(18)))
    row = BoxLayout(orientation="horizontal", spacing=dp(6),
                    size_hint_y=None, height=dp(42))
    cur = PREFS.get("font_scale", "보통")
    chips = []

    def pick(c):
        for x in chips:
            x.set_active(x is c)
        c.set_active(True)
        PREFS["font_scale"] = c.step
        save_prefs(PREFS)

    for name in UI.STEPS:
        c = Chip(name, active=(name == cur), on_toggle=pick)
        c.step = name
        chips.append(c)
        row.add_widget(c)
    box.add_widget(row)
    box.add_widget(lbl("바꾸면 화면을 다시 그립니다.", size=10.5,
                       color=T.faint, size_hint_y=None, height=dp(16)))

    box.add_widget(lbl("한 달 예산", size=12, color=T.dim,
                       size_hint_y=None, height=dp(18)))
    bf = Field("원", str(PREFS.get("budget", 20000)), numeric=True)
    box.add_widget(bf)

    box.add_widget(Widget())
    info = os.path.exists(CRASH_LOG)
    box.add_widget(lbl(
        f"카메라 {'가능' if qr_available() else '없음'}   ·   "
        f"폰트 {'OK' if FONT_OK else '없음(한글 깨짐)'}"
        f"   ·   화면 {int(Window.width)}x{int(Window.height)}\n"
        f"데이터 {DATA_DIR}\n"
        + ("오류 기록 있음 — crash.log" if info else "오류 기록 없음"),
        size=10, color=T.faint, size_hint_y=None, height=dp(42)))

    diag = Btn("연결 진단", bg=T.field, fsize=12.5, border=True,
               size_hint_y=None, height=dp(40))

    def run_diag(*a):
        diag.text = "확인 중…"

        def work():
            r = net_diagnose()
            Clock.schedule_once(
                lambda _dt: (setattr(diag, "text", "연결 진단"),
                             toast(r, "연결 진단")), 0)
        threading.Thread(target=work, daemon=True).start()
    diag.bind(on_release=run_diag)
    box.add_widget(diag)

    act = BoxLayout(orientation="horizontal", spacing=dp(9),
                    size_hint_y=None, height=dp(46))
    b1 = Btn("닫기", bg=T.field, fsize=13.5, border=True)
    b1.bind(on_release=p.dismiss)
    b2 = Btn("적용", bg=T.chungrok, fsize=13.5)

    def apply(*a):
        try:
            PREFS["budget"] = max(1000, int(bf.value))
        except (ValueError, TypeError):
            pass
        save_prefs(PREFS)
        p.dismiss()
        Clock.schedule_once(lambda _dt: app.rebuild(), 0.05)
    b2.bind(on_release=apply)
    act.add_widget(b1)
    act.add_widget(b2)
    box.add_widget(act)
    p.open()


# ===============================================================
#  화면 1 — 번호 생성
# ===============================================================
class GenScreen(Screen):
    def __init__(self, **kw):
        super().__init__(**kw)
        self.filters = Filters()
        self.mode = "조합"
        self.results, self.selected = [], set()
        self.target = DRAWS.newest() + 1
        self._build()

    def _build(self):
        sv, body = vscroll()

        # 회차 배너 -------------------------------------------
        self.banner = Card(bg=T.surface, orientation="vertical",
                           padding=[dp(16), dp(14)], spacing=dp(7),
                           size_hint_y=None, height=dp(104))
        self.b_round = lbl("", size=19, bold=True, disp=True,
                           size_hint_y=None, height=dp(26))
        self.b_date = lbl("", size=11.5, color=T.dim,
                          size_hint_y=None, height=dp(17))
        self.b_ev = lbl("", size=11.5, color=T.dim,
                        size_hint_y=None, height=dp(17))
        for w in (self.b_round, self.b_date, self.b_ev):
            self.banner.add_widget(w)
        body.add_widget(self.banner)

        # 생성 방식 -------------------------------------------
        body.add_widget(SectionTitle("생성 방식", 0))
        row = BoxLayout(orientation="horizontal", spacing=dp(7),
                        size_hint_y=None, height=dp(40))
        self.mode_chips = []
        for m in Generator.MODES:
            c = Chip(m, active=(m == self.mode), on_toggle=self._pick_mode)
            c.mode_name = m
            self.mode_chips.append(c)
            row.add_widget(c)
        body.add_widget(row)
        self.mode_desc = lbl("", size=11, color=T.faint,
                             size_hint_y=None, height=dp(34))
        body.add_widget(self.mode_desc)

        # 조건 -------------------------------------------------
        body.add_widget(SectionTitle("조건", 1))
        pre = BoxLayout(orientation="horizontal", spacing=dp(7),
                        size_hint_y=None, height=dp(40))
        self.pre_chips = []
        for name in Filters.PRESETS:
            c = Chip(name, active=(name == "표준"), on_toggle=self._pick_preset,
                     accent=T.jaju)
            c.preset_name = name
            self.pre_chips.append(c)
            pre.add_widget(c)
        body.add_widget(pre)

        cond = Card(bg=T.surface, orientation="vertical",
                    padding=[dp(14), dp(13)], spacing=dp(10),
                    size_hint_y=None)
        cond.bind(minimum_height=cond.setter("height"))

        self.f_inc = Field("고정수", hint="예: 7, 33")
        self.f_exc = Field("제외수", hint="예: 1, 2, 3")
        cond.add_widget(self.f_inc)
        cond.add_widget(self.f_exc)

        r1 = BoxLayout(orientation="horizontal", spacing=dp(10),
                       size_hint_y=None, height=dp(60))
        self.f_smin = Field("합계 최소", "100", numeric=True)
        self.f_smax = Field("합계 최대", "185", numeric=True)
        r1.add_widget(self.f_smin)
        r1.add_widget(self.f_smax)
        cond.add_widget(r1)

        r2 = BoxLayout(orientation="horizontal", spacing=dp(10),
                       size_hint_y=None, height=dp(60))
        self.f_omin = Field("홀수 최소", "1", numeric=True)
        self.f_omax = Field("홀수 최대", "5", numeric=True)
        r2.add_widget(self.f_omin)
        r2.add_widget(self.f_omax)
        cond.add_widget(r2)

        r2b = BoxLayout(orientation="horizontal", spacing=dp(10),
                        size_hint_y=None, height=dp(60))
        self.f_emin = Field("짝수 최소", "1", numeric=True)
        self.f_emax = Field("짝수 최대", "5", numeric=True)
        r2b.add_widget(self.f_emin)
        r2b.add_widget(self.f_emax)
        cond.add_widget(r2b)
        cond.add_widget(lbl(
            "번호 6개 중 홀수와 짝수의 합은 항상 6입니다. "
            "한쪽을 고치면 다른 쪽이 따라 바뀝니다.",
            size=10.5, color=T.dim, size_hint_y=None, height=dp(30)))
        self._sync = False
        self.f_omin.input.bind(text=lambda *a: self._sync_eo("odd"))
        self.f_omax.input.bind(text=lambda *a: self._sync_eo("odd"))
        self.f_emin.input.bind(text=lambda *a: self._sync_eo("even"))
        self.f_emax.input.bind(text=lambda *a: self._sync_eo("even"))

        r3 = BoxLayout(orientation="horizontal", spacing=dp(10),
                       size_hint_y=None, height=dp(60))
        self.f_run = Field("연속수 최대", "3", numeric=True)
        self.f_high = Field("32~45 최소", "1", numeric=True)
        r3.add_widget(self.f_run)
        r3.add_widget(self.f_high)
        cond.add_widget(r3)

        self.chip_pop = Chip("인기조합 회피", active=False, accent=T.chija,
                             size_hint_y=None, height=dp(38))
        cond.add_widget(self.chip_pop)
        self.chip_spread = Chip("분산도 높은 순으로 추리기", active=True,
                                accent=T.jaju, size_hint_y=None,
                                height=dp(38))
        cond.add_widget(self.chip_spread)
        cond.add_widget(lbl(
            "후보를 60개 뽑아 그중 나눠 가질 사람이 적을 형태 10개만 남깁니다.\n"
            "적중 확률은 그대로고 당첨 시 실수령액 기댓값만 올립니다.",
            size=10, color=T.faint, size_hint_y=None, height=dp(32)))

        for f in (self.f_smin, self.f_smax, self.f_omin, self.f_omax,
                  self.f_run, self.f_high):
            f.input.bind(text=lambda *a: self._update_rate())
        self.chip_pop.on_toggle = lambda c: self._update_rate()
        body.add_widget(cond)

        # 통과율 -----------------------------------------------
        self.rate_card = Card(bg=T.raised, orientation="vertical",
                              padding=[dp(14), dp(12)], spacing=dp(5),
                              size_hint_y=None, height=dp(74))
        self.rate_main = lbl("", size=13, size_hint_y=None, height=dp(20))
        self.rate_sub = lbl("", size=10.5, color=T.dim,
                            size_hint_y=None, height=dp(30))
        self.rate_card.add_widget(self.rate_main)
        self.rate_card.add_widget(self.rate_sub)
        body.add_widget(self.rate_card)

        # 생성 -------------------------------------------------
        g = Btn("번호 10조합 뽑기", bg=T.juhong, fsize=15.5,
                size_hint_y=None, height=dp(52))
        g.bind(on_release=self._generate)
        body.add_widget(g)

        self.res_box = BoxLayout(orientation="vertical", spacing=dp(8),
                                 size_hint_y=None)
        self.res_box.bind(minimum_height=self.res_box.setter("height"))
        body.add_widget(self.res_box)

        self.act_row = BoxLayout(orientation="horizontal", spacing=dp(9),
                                 size_hint_y=None, height=dp(50), opacity=0)
        self.save_btn = Btn("저장", bg=T.chungrok, fsize=14.5, disabled=True)
        self.save_btn.bind(on_release=self._save)
        self.share_btn = Btn("공유", bg=T.field, fsize=14.5, border=True,
                             disabled=True)
        self.share_btn.bind(on_release=self._share)
        self.act_row.add_widget(self.save_btn)
        self.act_row.add_widget(self.share_btn)
        body.add_widget(self.act_row)
        body.add_widget(Widget(size_hint_y=None, height=dp(6)))

        self.add_widget(sv)
        self._update_desc()
        Clock.schedule_once(lambda *a: self.refresh(), 0)

    # -- 상태 -------------------------------------------------
    def refresh(self):
        self.target = max(DRAWS.newest() + 1, latest_round_by_date() + 1)
        d = round_date(self.target)
        term, order = current_solar_term(d)
        evs = [e["name"] for e in events_for(d) if e["kind"] == "기념일"]
        self.b_round.text = f"제 {self.target} 회"
        self.b_date.text = (f"추첨  {d.strftime('%Y.%m.%d')} (토) 20:35   ·   "
                            f"[color=E8B33D]{term}[/color] 제{order}절기")
        self.b_ev.text = ("이번주  " + "  ·  ".join(evs)) if evs else \
            "이번주 기념일 없음"
        self._update_rate()

    def _pick_mode(self, chip):
        for c in self.mode_chips:
            c.set_active(c is chip)
        chip.set_active(True)
        self.mode = chip.mode_name
        self._update_desc()

    def _pick_preset(self, chip):
        for c in self.pre_chips:
            c.set_active(c is chip)
        chip.set_active(True)
        self.filters.apply_preset(chip.preset_name)
        f = self.filters
        self.f_smin.input.text = str(f.sum_min)
        self.f_smax.input.text = str(f.sum_max)
        self.f_emin.input.text = str(6 - f.odd_max)
        self.f_emax.input.text = str(6 - f.odd_min)
        self.f_omin.input.text = str(f.odd_min)
        self.f_omax.input.text = str(f.odd_max)
        self.f_run.input.text = str(f.max_consecutive)
        self.f_high.input.text = str(f.high_min)
        self.chip_pop.set_active(f.avoid_popular)
        self._update_rate()

    def _update_desc(self):
        self.mode_desc.text = {
            "임의": "완전 무작위. 조건만 통과시킵니다.",
            "조합": "이달의 이벤트 + 회차 + 랜덤.\n"
                  "같은 회차·같은 절기면 항상 같은 번호가 나옵니다.",
            "통계": "최근 100회 출현빈도를 가중치로 씁니다.\n"
                  "예측력은 없고, 분포만 달라집니다.",
        }.get(self.mode, "")

    def _collect(self):
        f = self.filters
        f.include = parse_nums(self.f_inc.value)
        f.exclude = parse_nums(self.f_exc.value)
        f.include -= f.exclude

        def num(fld, dflt, lo=None, hi=None):
            try:
                v = int(fld.value)
            except (ValueError, TypeError):
                return dflt
            if lo is not None:
                v = max(lo, v)
            if hi is not None:
                v = min(hi, v)
            return v

        f.sum_min = num(self.f_smin, 100, 21, 255)
        f.sum_max = num(self.f_smax, 185, 21, 255)
        f.odd_min = num(self.f_omin, 1, 0, 6)
        f.odd_max = num(self.f_omax, 5, 0, 6)
        f.max_consecutive = num(self.f_run, 3, 1, 6)
        f.high_min = num(self.f_high, 1, 0, 6)
        if f.sum_min > f.sum_max:
            f.sum_min, f.sum_max = f.sum_max, f.sum_min
        if f.odd_min > f.odd_max:
            f.odd_min, f.odd_max = f.odd_max, f.odd_min
        f.avoid_popular = self.chip_pop.active
        return f

    def _sync_eo(self, src):
        """홀수 ↔ 짝수 칸을 서로 맞춘다. 짝수 = 6 - 홀수."""
        if self._sync:
            return
        self._sync = True
        try:
            def g(fld, d):
                try:
                    v = int((fld.input.text or "").strip())
                except Exception:
                    return d
                return max(0, min(6, v))
            if src == "odd":
                omin, omax = g(self.f_omin, 1), g(self.f_omax, 5)
                self.f_emin.input.text = str(6 - omax)
                self.f_emax.input.text = str(6 - omin)
            else:
                emin, emax = g(self.f_emin, 1), g(self.f_emax, 5)
                self.f_omin.input.text = str(6 - emax)
                self.f_omax.input.text = str(6 - emin)
        except Exception as e:
            log_crash(e)
        finally:
            self._sync = False
        self._update_rate()

    def _update_rate(self, *a):
        f = self._collect()
        rows = DRAWS.recent(120)
        r = f.pass_rate(rows)
        if not r:
            self.rate_main.text = "데이터 없음"
            self.rate_sub.text = ""
            return
        ok, tot = r
        pct = ok / tot * 100 if tot else 0
        col = "5FBF7F" if pct >= 80 else ("E8B33D" if pct >= 55 else "D4462B")
        self.rate_main.text = (
            f"이 조건은 지난 {tot}회 당첨번호 중 "
            f"[color={col}][b]{ok}회({pct:.0f}%)[/b][/color]를 통과합니다")
        if pct >= 80:
            self.rate_sub.text = "실제 당첨 패턴을 거의 안 버립니다."
        elif pct >= 55:
            self.rate_sub.text = (
                f"실제 당첨번호의 {100 - pct:.0f}%를 미리 버리고 있습니다.\n"
                "1등 적중 가능성을 깎는 대신 조합 수가 줄어듭니다.")
        else:
            self.rate_sub.text = (
                f"[color=D4462B]조건이 과합니다.[/color] 실제 당첨번호의 "
                f"{100 - pct:.0f}%가 이 조건에 걸립니다.")

    # -- 생성/저장 ---------------------------------------------
    def _generate(self, *a):
        f = self._collect()
        if len(f.include) > 6:
            toast("고정수는 6개까지입니다.")
            return
        self.results = Generator(f).batch(
            self.mode, 10, rnd=self.target,
            spread=self.chip_spread.active)
        self.selected.clear()
        self._render()

    def _render(self):
        self.res_box.clear_widgets()
        if not self.results:
            c = Card(bg=T.surface, padding=dp(15), size_hint_y=None,
                     height=dp(72), bcol=T.juhong)
            c.add_widget(lbl("조건이 너무 좁아 만들 수 있는 조합이 없습니다.\n"
                             "합계 범위나 고정수를 완화해 보세요.",
                             size=12, color=T.dim))
            self.res_box.add_widget(c)
            self.act_row.opacity = 0
            self.save_btn.disabled = self.share_btn.disabled = True
            return

        self.res_box.add_widget(SectionTitle(
            f"{self.target}회 추천 {len(self.results)}조합", 2,
            sub="탭해서 선택"))

        for i, nums in enumerate(self.results):
            row = TapCard(bg=T.surface, orientation="horizontal",
                          padding=[dp(12), dp(10)], spacing=dp(9),
                          size_hint_y=None, height=dp(54))
            row.idx = i
            row.add_widget(lbl(chr(ord("A") + i), size=12.5, color=T.faint,
                               bold=True, halign="center",
                               size_hint_x=None, width=dp(15)))
            row.add_widget(BallRow(nums, d=31))
            sp = Popularity.spread(nums)
            col = T.chija if sp >= 70 else (T.dim if sp >= 40 else T.faint)
            box = BoxLayout(orientation="vertical", size_hint_x=None,
                            width=dp(34))
            box.add_widget(lbl(f"{sp:.0f}", size=12, color=col, bold=True,
                               halign="right", size_hint_y=None,
                               height=dp(16)))
            box.add_widget(lbl(f"{sum(nums)}", size=9.5, color=T.faint,
                               halign="right", size_hint_y=None,
                               height=dp(13)))
            row.add_widget(box)
            row.bind(on_release=self._toggle)
            self.res_box.add_widget(row)

        self.res_box.add_widget(lbl(
            "오른쪽 큰 숫자 = 분산도(높을수록 나눠 가질 사람이 적음), "
            "아래는 합계", size=10, color=T.faint,
            size_hint_y=None, height=dp(18)))

        self.act_row.opacity = 1
        self.save_btn.disabled = self.share_btn.disabled = False
        self.save_btn.text = "저장"
        self.share_btn.text = "공유"

    def _toggle(self, row):
        on = row.idx not in self.selected
        if on:
            self.selected.add(row.idx)
        else:
            self.selected.discard(row.idx)
        Animation(rgba=(T.chungrok[:3] + (0.30,)) if on else T.surface,
                  d=.13).start(row._c)
        row.set_border(T.chungrok if on else T.stroke)
        n = len(self.selected)
        self.save_btn.text = f"저장 {n}" if n else "저장"
        self.share_btn.text = f"공유 {n}" if n else "공유"

    def _save(self, *a):
        if not self.selected:
            toast("저장할 조합을 탭해서 선택하세요.")
            return
        for i in sorted(self.selected):
            VAULT.add(self.results[i], self.target, self.mode)
        n = len(self.selected)
        self.selected.clear()
        self._render()
        cnt, won = VAULT.spend_this_month()
        toast(f"{self.target}회차로 {n}개 저장했습니다.\n\n"
              f"이번 달 누적 {cnt}게임 · {won:,}원 상당")

    def _share(self, *a):
        picks = ([self.results[i] for i in sorted(self.selected)]
                 if self.selected else self.results)
        if not picks:
            return
        note = ("선택 " + str(len(picks)) + "조합"
                if self.selected else f"추천 {len(picks)}조합 전체")
        share_now(share_text(self.target, picks, note),
                  f"{self.target}회 번호 공유")


# ===============================================================
#  화면 2 — 통계
# ===============================================================
class StatScreen(Screen):
    def __init__(self, **kw):
        super().__init__(**kw)
        self.window = 100
        self._build()

    def _build(self):
        sv, body = vscroll()
        self.body = body

        body.add_widget(SectionTitle("데이터", 0))
        self.sync_card = Card(bg=T.surface, orientation="vertical",
                              padding=[dp(15), dp(13)], spacing=dp(9),
                              size_hint_y=None, height=dp(150))
        self.sync_info = lbl("", size=12, size_hint_y=None, height=dp(20))
        self.sync_sub = lbl("", size=10.5, color=T.dim,
                            size_hint_y=None, height=dp(30))
        self.sync_btn = Btn("최신 회차 받기", bg=T.chungrok, fsize=13,
                            size_hint_y=None, height=dp(40))
        self.sync_btn.bind(on_release=self._sync)
        self.sync_bar = ProgressBarKR(size_hint_y=None, height=dp(8),
                                      opacity=0)
        self.sync_pct = lbl("", size=10.5, color=T.chungrok,
                            size_hint_y=None, height=dp(18), opacity=0)
        for w in (self.sync_info, self.sync_sub, self.sync_btn,
                  self.sync_bar, self.sync_pct):
            self.sync_card.add_widget(w)
        body.add_widget(self.sync_card)

        win = BoxLayout(orientation="horizontal", spacing=dp(7),
                        size_hint_y=None, height=dp(38))
        self.win_chips = []
        for n in (30, 50, 100, 0):
            c = Chip(f"{n}회" if n else "200회", active=(n == 100),
                     on_toggle=self._pick_window)
            c.win = n
            self.win_chips.append(c)
            win.add_widget(c)
        body.add_widget(win)

        body.add_widget(SectionTitle("번호별 출현", 1))
        self.bars = Bars(Counter())
        body.add_widget(self.bars)
        self.hotcold = lbl("", size=11, color=T.dim,
                           size_hint_y=None, height=dp(36))
        body.add_widget(self.hotcold)

        body.add_widget(SectionTitle("균등성 검정", 2))
        self.chi_card = Card(bg=T.surface, orientation="vertical",
                             padding=[dp(15), dp(13)], spacing=dp(6),
                             size_hint_y=None, height=dp(110))
        self.chi_a = lbl("", size=13, size_hint_y=None, height=dp(20))
        self.chi_b = lbl("", size=11, color=T.dim,
                         size_hint_y=None, height=dp(62))
        self.chi_card.add_widget(self.chi_a)
        self.chi_card.add_widget(self.chi_b)
        body.add_widget(self.chi_card)

        body.add_widget(SectionTitle("1등 당첨자 수", 3))
        self.win_card = Card(bg=T.surface, orientation="vertical",
                             padding=[dp(15), dp(13)], spacing=dp(6),
                             size_hint_y=None, height=dp(168))
        self.win_a = lbl("", size=13, size_hint_y=None, height=dp(20))
        self.win_b = lbl("", size=11, color=T.dim,
                         size_hint_y=None, height=dp(118))
        self.win_card.add_widget(self.win_a)
        self.win_card.add_widget(self.win_b)
        body.add_widget(self.win_card)

        body.add_widget(SectionTitle("당첨금은 몇 명이 나누느냐로 갈린다", 4))
        self.spread = Card(bg=T.surface, orientation="vertical",
                           padding=[dp(15), dp(13)], spacing=dp(8),
                           size_hint_y=None, height=dp(150))
        body.add_widget(self.spread)

        body.add_widget(SectionTitle("인기도 모델 검정", 0))
        self.pop_card = Card(bg=T.surface, orientation="vertical",
                             padding=[dp(15), dp(13)], spacing=dp(7),
                             size_hint_y=None, height=dp(196))
        self.pop_a = lbl("", size=13, size_hint_y=None, height=dp(20))
        self.pop_b = lbl("", size=11, color=T.dim,
                         size_hint_y=None, height=dp(146))
        self.pop_card.add_widget(self.pop_a)
        self.pop_card.add_widget(self.pop_b)
        body.add_widget(self.pop_card)

        body.add_widget(SectionTitle("최근 당첨번호", 0))
        self.recent_box = BoxLayout(orientation="vertical", spacing=dp(7),
                                    size_hint_y=None)
        self.recent_box.bind(minimum_height=self.recent_box.setter("height"))
        body.add_widget(self.recent_box)
        body.add_widget(Widget(size_hint_y=None, height=dp(6)))

        self.add_widget(sv)

    def on_pre_enter(self, *a):
        self.refresh()

    def on_leave(self, *a):
        """탭을 벗어나면 목록 위젯을 버린다. 다시 들어올 때 새로 그린다."""
        self.recent_box.clear_widgets()
        self.spread.clear_widgets()
        gc.collect()

    def _pick_window(self, chip):
        for c in self.win_chips:
            c.set_active(c is chip)
        chip.set_active(True)
        self.window = chip.win
        self.refresh()

    def _sync(self, *a):
        if UPDATER.busy:
            return
        want = self.window or 200
        miss = DRAWS.missing(want)
        if not miss:
            toast(f"최근 {want}회는 이미 다 받았습니다.")
            return
        self.sync_btn.text = "받는 중…"
        self.sync_btn.disabled = True
        self.sync_bar.opacity = 1
        self.sync_pct.opacity = 1
        self.sync_bar.set(0.0)
        self.sync_pct.text = f"0 / {len(miss)}"

        def prog(i, tot, got):
            self.sync_bar.set(i / max(1, tot))
            self.sync_pct.text = (f"{i} / {tot}   ·   성공 {got}"
                                  f"   ·   {i * 100 // max(1, tot)}%")


        def done(got, added, fails, err):
            self.sync_btn.disabled = False
            self.sync_bar.opacity = 0
            self.sync_pct.opacity = 0
            self.refresh()
            if got:
                toast(f"{got}회 수신 · {added}회 갱신")
            else:
                toast("받지 못했습니다.\n"
                      "인터넷 연결과 방화벽을 확인해 주세요.\n\n"
                      f"마지막 오류: {err or '알 수 없음'}")

        UPDATER.run(miss, prog, done)

    def refresh(self):
        rows = DRAWS.recent(self.window)
        st = Stats(rows)

        newest = DRAWS.newest()
        should = cached_latest_round()
        nob = sum(1 for r in DRAWS.rows if not r.get("bonus"))
        want = self.window or 200
        need = len(DRAWS.missing(want))
        self.sync_btn.text = (f"최근 {want}회 받기"
                              + (f"  (부족 {need}회)" if need else "  (완료)"))
        self.sync_info.text = (
            f"보유 {len(DRAWS.rows)}회  ·  "
            f"{DRAWS.oldest()}~{newest}회")
        gap = should - newest
        self.sync_sub.text = (
            (f"[color=E8B33D]{gap}회 뒤처져 있습니다 (최신 {should}회)[/color]\n"
             if gap > 0 else "최신 회차까지 반영되어 있습니다\n")
            + (f"보너스번호 미확인 {nob}회 — 2등 판정 불가"
               if nob else "보너스번호 전부 확보"))

        # 빈도
        c = st.freq()
        rank = sorted(c.items(), key=lambda x: (-x[1], x[0]))
        hot = {x[0] for x in rank[:6]}
        self.bars.update(c, hot)
        top = sorted(x[0] for x in rank[:6])
        bot = sorted(x[0] for x in rank[-6:])
        self.hotcold.text = (
            f"많이 나온 번호   {', '.join(f'{n:>2}' for n in top)}"
            f"   ({rank[0][1]}~{rank[5][1]}회)\n"
            f"적게 나온 번호   {', '.join(f'{n:>2}' for n in bot)}"
            f"   ({rank[-1][1]}~{rank[-6][1]}회)")

        # 카이제곱
        chi = st.chi_square()
        if chi:
            sig = chi["significant"]
            col = "D4462B" if sig else "5FBF7F"
            self.chi_a.text = (
                f"카이제곱 [b]{chi['x2']:.1f}[/b]  /  임계값 60.5  →  "
                f"[color={col}][b]{'편향 있음' if sig else '균등'}[/b][/color]")
            self.chi_b.text = (
                f"{st.n}회 × 6개 = {st.n * 6}개 번호를 45칸에 나누면 "
                f"칸마다 평균 {chi['exp']:.1f}번씩 나와야 합니다.\n"
                + ("실제 분포가 그 기대치에서 통계적으로 벗어났습니다. "
                   "표본을 늘려 재확인해 보세요."
                   if sig else
                   "실제 분포는 완전 무작위와 구분되지 않습니다. "
                   "즉 특정 번호가 잘 나온다는 근거는 이 데이터엔 없습니다."))
        else:
            self.chi_a.text = "데이터 부족"
            self.chi_b.text = "10회 이상 필요합니다."

        # 당첨자 수
        w = st.winners()
        if w:
            self.win_a.text = (
                f"평균 [b]{w['mean']:.1f}명[/b]   범위 {w['min']}~{w['max']}명"
                f"   ({w['n']}회 기준)")
            years = 1 / w["p_zero"] / 52 if w["p_zero"] else 0
            self.win_b.text = (
                f"10~20명 구간에 들어온 비율   {w['in_band'] * 100:.0f}%\n"
                f"분산/평균 = {w['ratio']:.2f}  "
                f"(1에 가까울수록 순수 무작위)\n\n"
                f"1등이 0명일 확률 = {w['p_zero']:.1e}\n"
                f"→ 이월은 평균 {years:,.0f}년에 한 번. 안 나오는 게 정상입니다.")
        else:
            self.win_a.text = "당첨자 수 데이터 없음"
            self.win_b.text = "[최신 회차 받기]로 채워집니다."

        # 당첨금 스프레드
        self.spread.clear_widgets()
        sp = st.prize_spread()
        if sp:
            for tag, r, col in (("가장 적게 나눈 회차", sp["lo"], T.chija),
                                ("가장 많이 나눈 회차", sp["hi"], T.dim)):
                b = BoxLayout(orientation="vertical", spacing=dp(3),
                              size_hint_y=None, height=dp(44))
                b.add_widget(lbl(
                    f"{tag}   [b]{r['round']}회[/b]   {r['winners']}명",
                    size=11.5, color=col, size_hint_y=None, height=dp(17)))
                b.add_widget(lbl(
                    f"1인당 [b]{money(r['prize'])}원[/b]   ·   "
                    f"{', '.join(map(str, r['nums']))}",
                    size=12, size_hint_y=None, height=dp(20)))
                self.spread.add_widget(b)
            self.spread.add_widget(lbl(
                f"같은 1등인데 실수령액이 [color=E8B33D][b]"
                f"{sp['times']:.1f}배[/b][/color] 차이 납니다. "
                f"확률은 못 바꿔도 이건 조건으로 밀 수 있는 유일한 축입니다.",
                size=11, color=T.dim, size_hint_y=None, height=dp(46)))
        else:
            self.spread.add_widget(lbl("당첨금 데이터가 아직 없습니다.",
                                       size=12, color=T.dim))

        # 인기도 모델 검정
        v = Popularity.validate(DRAWS.rows)
        if not v:
            self.pop_a.text = "표본 부족"
            self.pop_b.text = ("당첨자 수가 있는 회차가 15회 이상 필요합니다.\n"
                               "[최신 회차 받기]로 채워집니다.")
        else:
            good = v["pass"]
            col = "5FBF7F" if good else "E8B33D"
            self.pop_a.text = (
                f"상관 [b]{v['rho']:+.3f}[/b]  /  잡음 한계 {v['thr']:.3f}  →  "
                f"[color={col}][b]{'근거 있음' if good else '아직 근거 없음'}"
                f"[/b][/color]")
            self.pop_b.text = (
                f"과거 {v['n']}회의 인기도 점수와 그 회차 1등 당첨자 수의 "
                f"순위상관입니다.\n"
                f"당첨자 수를 1500번 무작위로 섞어 만든 잡음 한계선과 "
                f"비교했습니다.\n\n"
                + ("한계선을 넘었습니다. 인기도 점수가 높은 조합일수록 "
                   "실제로 당첨자가 많았다는 뜻입니다. 분산 정렬이 "
                   "기댓값을 올린다는 근거가 됩니다."
                   if good else
                   f"한계선을 못 넘었습니다. 지금 표본으로는 이 모델이 "
                   f"맞는지 확인할 수 없습니다.\n"
                   f"[color=E8B33D]{v['need']}회 더 받으면[/color] 다시 "
                   f"검정합니다. 그때까지 분산 정렬은 '해로울 것 없는 추정' "
                   f"수준으로 보시는 게 맞습니다."))

        # 최근 당첨번호
        self.recent_box.clear_widgets()
        for r in reversed(DRAWS.rows[-8:]):
            card = Card(bg=T.surface, orientation="vertical",
                        padding=[dp(12), dp(10)], spacing=dp(6),
                        size_hint_y=None, height=dp(74))
            top = BoxLayout(orientation="horizontal", size_hint_y=None,
                            height=dp(18))
            top.add_widget(lbl(f"[b]{r['round']}회[/b]  {r['date']}",
                               size=11.5))
            top.add_widget(lbl(
                f"{r['winners']}명 · {money(r['prize'])}" if r["winners"]
                else "", size=10.5, color=T.faint, halign="right"))
            card.add_widget(top)
            card.add_widget(BallRow(r["nums"], d=29,
                                    bonus=r["bonus"] or None))
            self.recent_box.add_widget(card)


# ===============================================================
#  화면 3 — 지역탐방
# ===============================================================
# 이름, 주소, 전화, 위도, 경도, [(회차, 등수), ...]
# ===============================================================
#  당첨판매점 — 동행복권에서 실제로 받아온다
# ===============================================================
STORE_FILE = os.path.join(DATA_DIR, "stores.json")
GEO_FILE = os.path.join(DATA_DIR, "geo.json")

_TAG = re.compile(r"<[^>]+>")
_TR = re.compile(r"<tr[^>]*>(.*?)</tr>", re.S | re.I)
_TD = re.compile(r"<td[^>]*>(.*?)</td>", re.S | re.I)


def _cell(html):
    t = _TAG.sub(" ", html)
    t = t.replace("&nbsp;", " ").replace("&amp;", "&")
    return re.sub(r"\s+", " ", t).strip()


def fetch_top_stores(rnd, rank=1, page=1):
    """
    동행복권 당첨판매점 목록.
    1등은 상호/구분/소재지, 2등은 상호/소재지 형태로 표가 다르다.
    돌려주는 값: [(상호, 주소), ...]
    """
    url = ("https://www.dhlottery.co.kr/store.do?method=topStore"
           f"&pageGubun=L645&drwNo={rnd}&rank={rank}&nowPage={page}")
    html = _get(url, timeout=12)
    out = []
    for tr in _TR.findall(html):
        tds = [_cell(x) for x in _TD.findall(tr)]
        if len(tds) < 3:
            continue
        # 첫 칸이 번호인 표와 아닌 표가 섞여 있어 주소 모양으로 찾는다.
        addr = ""
        name = ""
        for c in tds:
            if re.match(r"^(서울|부산|대구|인천|광주|대전|울산|세종|경기|"
                        r"강원|충북|충남|전북|전남|경북|경남|제주)", c):
                addr = c
            elif c and not c.isdigit() and c not in ("자동", "수동", "반자동"):
                if not name:
                    name = c
        if name and addr:
            out.append((name, addr))
    return out


def _load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def _save_json(path, obj):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False)
    except Exception as e:
        log_crash(e)


def geocode_addr(addr, cache):
    """
    주소 → 좌표. 캐시를 먼저 보고, 없으면 두 방식을 교차로 시도한다.
      ① 전체 주소 그대로
      ② 도로명/번지를 떼고 시·군·구 + 동까지만
    Nominatim 은 초당 1회 제한이 있어 호출 사이를 띄운다.
    """
    if addr in cache:
        v = cache[addr]
        return (v[0], v[1]) if v else None

    import time as _t
    tries = [addr]
    m = re.match(r"^(\S+\s+\S+(?:\s+\S+)?)", addr)
    if m and m.group(1) != addr:
        tries.append(m.group(1))
    short = re.sub(r"\s*\d[\d\-]*(번길|길|로|가)?\s*\d*$", "", addr).strip()
    if short and short not in tries:
        tries.append(short)

    for q in tries:
        try:
            r = geocode(q)
        except Exception:
            r = None
        if r:
            cache[addr] = [r[0], r[1]]
            return r[0], r[1]
        _t.sleep(1.1)
    cache[addr] = None
    return None


def refresh_stores(rounds, on_progress=None):
    """
    최근 회차들의 1·2등 판매점을 모아 좌표까지 붙여 저장한다.
    시간이 걸리므로 반드시 백그라운드에서 부른다.
    """
    stores = _load_json(STORE_FILE, {})
    geo = _load_json(GEO_FILE, {})
    total = len(rounds) * 2
    done = 0
    for rnd in rounds:
        for rank in (1, 2):
            page = 1
            while True:
                try:
                    rows = fetch_top_stores(rnd, rank, page)
                except Exception:
                    rows = []
                if not rows:
                    break
                for name, addr in rows:
                    key = f"{name}|{addr}"
                    rec = stores.setdefault(
                        key, {"name": name, "addr": addr, "wins": []})
                    if [rnd, rank] not in rec["wins"]:
                        rec["wins"].append([rnd, rank])
                if rank == 1 or page >= 3:
                    break
                page += 1
            done += 1
            if on_progress:
                on_progress(done, total)
    _save_json(STORE_FILE, stores)
    _save_json(GEO_FILE, geo)
    return stores


def stores_near(lat, lon, radius_km, want_rank=None, region_hint=""):
    """
    저장해 둔 판매점 중 반경 안의 것을 거리순으로 돌려준다.
    좌표가 아직 없는 곳은 이 자리에서 지오코딩한다.
    지역 이름이 겹치는 것부터 먼저 처리해 헛걸음을 줄인다.
    """
    stores = _load_json(STORE_FILE, {})
    geo = _load_json(GEO_FILE, {})
    if not stores:
        return None

    items = list(stores.values())
    if region_hint:
        keys = [k for k in re.split(r"\s+", region_hint) if len(k) >= 2]

        def score(it):
            return -sum(1 for k in keys if k in it["addr"])
        items.sort(key=score)

    rows = []
    pending = []
    for it in items:
        hits = [tuple(w) for w in it["wins"]
                if want_rank is None or w[1] == want_rank]
        if not hits:
            continue
        pos = geo.get(it["addr"])
        if not pos:
            # 주소→좌표 변환은 한 건에 1초 넘게 걸린다. 화면 그리는 중에
            # 하면 앱이 통째로 멈춘다. 여기서는 캐시만 쓰고, 없는 것은
            # 백그라운드에 맡긴다.
            pending.append(it["addr"])
            continue
        d = haversine(lat, lon, pos[0], pos[1])
        if d <= radius_km:
            rows.append((d, it["name"], it["addr"], "", hits))
    rows.sort(key=lambda x: x[0])
    if pending:
        threading.Thread(target=_geocode_batch, args=(pending[:40],),
                         daemon=True).start()
    return rows


_GEO_BUSY = {"on": False}


def _geocode_batch(addrs):
    """좌표가 없는 주소를 뒤에서 천천히 채운다."""
    if _GEO_BUSY["on"]:
        return
    _GEO_BUSY["on"] = True
    try:
        geo = _load_json(GEO_FILE, {})
        n = 0
        for a in addrs:
            if a in geo:
                continue
            if geocode_addr(a, geo):
                n += 1
        _save_json(GEO_FILE, geo)
        if n:
            Clock.schedule_once(
                lambda _dt: toast(f"판매점 {n}곳의 위치를 찾았습니다."), 0)
    except Exception as e:
        log_crash(e)
    finally:
        _GEO_BUSY["on"] = False


MOCK_SHOPS = [
    ("로또명당 대박복권", "경기 광주시 경안로 12", "031-762-1234",
     37.4292, 127.2550, [(1187, 1), (1142, 2), (1098, 2)]),
    ("행운상회", "경기 광주시 쌍령동 45-2", "031-763-8800",
     37.4155, 127.2610, [(1201, 2), (1160, 2)]),
    ("복권백화점 광주점", "경기 광주시 중앙로 88", "031-764-5566",
     37.4098, 127.2555, [(1195, 1), (1173, 2), (1155, 2), (1121, 2)]),
    ("GS25 태전점", "경기 광주시 태전동 991", "031-765-2211",
     37.4210, 127.2280, [(1180, 2)]),
    ("황금열쇠복권방", "경기 성남시 분당구 야탑로 3", "031-706-9090",
     37.4113, 127.1285, [(1204, 1), (1166, 1), (1130, 2)]),
    ("CU 오포점", "경기 광주시 오포읍 문형리 22", "031-767-3030",
     37.3720, 127.2170, [(1190, 2), (1149, 2)]),
    ("일등복권", "경기 용인시 처인구 중부대로 5", "031-338-7070",
     37.2340, 127.2010, [(1199, 1)]),
    ("강남로또명가", "서울 강남구 테헤란로 152", "02-555-1234",
     37.5000, 127.0360, [(1210, 1), (1183, 2), (1140, 2)]),
    ("종로복권방", "서울 종로구 종로 100", "02-733-4567",
     37.5705, 126.9910, [(1207, 2), (1175, 1)]),
    ("부산서면복권", "부산 부산진구 중앙대로 690", "051-802-3344",
     35.1570, 129.0590, [(1198, 1), (1162, 2)]),
    ("대전둔산복권", "대전 서구 둔산로 100", "042-472-5566",
     36.3510, 127.3780, [(1193, 2), (1151, 2)]),
    ("광주충장로복권", "광주 동구 충장로 50", "062-224-7788",
     35.1490, 126.9160, [(1205, 2)]),
    ("대구동성로복권", "대구 중구 동성로 30", "053-421-9900",
     35.8690, 128.5960, [(1202, 1), (1168, 2)]),
    ("인천구월동복권", "인천 남동구 구월로 200", "032-421-1122",
     37.4490, 126.7010, [(1196, 2), (1145, 2)]),
    ("제주시청복권방", "제주 제주시 광양로 10", "064-722-3355",
     33.4990, 126.5310, [(1188, 2)]),
]


def haversine(lat1, lon1, lat2, lon2):
    """두 좌표 사이 거리(km)."""
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = (math.sin(dp / 2) ** 2
         + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2)
    return 2 * r * math.asin(min(1.0, math.sqrt(a)))


def _nominatim(path):
    """
    OpenStreetMap Nominatim. API 키가 필요 없다.
    이용 규약상 User-Agent 를 반드시 밝혀야 하므로 _get 의 UA 를 그대로 쓴다.
    """
    return json.loads(_get("https://nominatim.openstreetmap.org/" + path,
                           timeout=7))


def reverse_geocode(lat, lon):
    """좌표 → 한글 주소. 실패하면 None."""
    try:
        j = _nominatim(f"reverse?format=jsonv2&lat={lat}&lon={lon}"
                       f"&zoom=18&accept-language=ko")
        a = j.get("address", {}) or {}
        # 시·도 / 시·군·구 / 읍면동 을 각각 한 개씩만 고른다.
        sido = a.get("state") or a.get("province") or ""
        sigun = (a.get("city") or a.get("county") or a.get("town") or "")
        gu = a.get("city_district") or a.get("borough") or ""
        dong = (a.get("quarter") or a.get("neighbourhood")
                or a.get("suburb") or a.get("village") or "")
        # 옛 지명(대쌍령리 등)이 잡히면 도로명을 함께 보여 준다.
        road = a.get("road") or ""
        num = a.get("house_number") or ""
        parts = [x for x in (sido, sigun, gu, dong) if x]
        head = " ".join(dict.fromkeys(parts))
        tail = (road + (" " + num if num else "")).strip()
        if not head:
            # zoom 이 깊으면 행정구역 칸이 비는 경우가 있어 전체 주소에서 뽑는다.
            seg = [x.strip() for x in
                   (j.get("display_name") or "").split(",") if x.strip()]
            seg = [x for x in seg if not x.isdigit()]
            head = " ".join(reversed(seg[-4:-1])) if len(seg) >= 4 else ""
        if head and tail:
            return f"{head}\n{tail}"
        return head or tail or (
            (j.get("display_name") or "").split(",")[0] or None)
    except Exception:
        return None


def geocode(query):
    """한글 주소 → (위도, 경도, 표시명). 실패하면 None."""
    try:
        from urllib.parse import quote
        j = _nominatim(f"search?format=jsonv2&limit=1&accept-language=ko"
                       f"&countrycodes=kr&q={quote(query)}")
        if not j:
            return None
        r = j[0]
        lat, lon = float(r["lat"]), float(r["lon"])
        name = reverse_geocode(lat, lon) or query
        return lat, lon, name
    except Exception:
        return None


LOC_INFO = {"acc": 0.0, "src": ""}


def android_last_location():
    """
    LocationManager 가 들고 있는 마지막 위치를 즉시 꺼낸다.
    plyer 의 gps 는 콜백이 오지 않는 기기가 많아 이쪽을 먼저 쓴다.
    """
    if platform != "android":
        return None
    try:
        from jnius import autoclass
        PythonActivity = autoclass("org.kivy.android.PythonActivity")
        Context = autoclass("android.content.Context")
        lm = PythonActivity.mActivity.getSystemService(
            Context.LOCATION_SERVICE)
        import time as _t
        now = _t.time() * 1000.0
        best, best_score = None, None
        for prov in ("gps", "fused", "network", "passive"):
            try:
                loc = lm.getLastKnownLocation(prov)
            except Exception:
                loc = None
            if loc is None:
                continue
            try:
                acc = float(loc.getAccuracy()) or 9999.0
            except Exception:
                acc = 9999.0
            age = max(0.0, (now - float(loc.getTime())) / 1000.0)
            if age > 600:            # 10분보다 오래된 값은 버린다
                continue
            # 오차가 작을수록, 최근 값일수록 좋다.
            score = acc + age * 0.5
            if best_score is None or score < best_score:
                best, best_score = loc, score
        if best is not None:
            try:
                LOC_INFO["acc"] = float(best.getAccuracy())
            except Exception:
                LOC_INFO["acc"] = 0.0
            LOC_INFO["src"] = best.getProvider()
            return float(best.getLatitude()), float(best.getLongitude())
    except Exception as e:
        log_crash(e)
    return None


def android_request_location(on_fix):
    """
    한 번만 갱신을 요청한다. 실내에서도 network provider 로 잡히는 편.
    on_fix(lat, lon) 는 메인 스레드에서 부른다.
    """
    if platform != "android":
        return False
    try:
        from jnius import autoclass, PythonJavaClass, java_method
        PythonActivity = autoclass("org.kivy.android.PythonActivity")
        Context = autoclass("android.content.Context")
        Looper = autoclass("android.os.Looper")
        lm = PythonActivity.mActivity.getSystemService(
            Context.LOCATION_SERVICE)

        class _Listener(PythonJavaClass):
            __javainterfaces__ = ["android/location/LocationListener"]

            @java_method("(Landroid/location/Location;)V")
            def onLocationChanged(self, loc):
                try:
                    la, lo = float(loc.getLatitude()), float(loc.getLongitude())
                    Clock.schedule_once(lambda _dt: on_fix(la, lo), 0)
                    lm.removeUpdates(self)
                except Exception:
                    pass

            @java_method("(Ljava/lang/String;)V")
            def onProviderEnabled(self, p):
                pass

            @java_method("(Ljava/lang/String;)V")
            def onProviderDisabled(self, p):
                pass

            @java_method("(Ljava/lang/String;ILandroid/os/Bundle;)V")
            def onStatusChanged(self, p, st, ex):
                pass

        listener = _Listener()
        started = False
        for prov in ("network", "gps"):
            try:
                if lm.isProviderEnabled(prov):
                    lm.requestLocationUpdates(prov, 0, 0, listener,
                                              Looper.getMainLooper())
                    started = True
            except Exception:
                pass
        return started
    except Exception as e:
        log_crash(e)
        return False


def locate_by_ip():
    """
    GPS 를 못 쓸 때(데스크톱 테스트, 실내, 권한 거부) 통신망 IP 로 대략 위치를 잡는다.
    오차는 도시 단위. 두 곳을 차례로 시도한다.
    """
    # 안드로이드 9 부터 평문 HTTP 는 기본 차단이므로 전부 HTTPS 를 쓴다.
    for url, pick in (
        ("https://ipwho.is/",
         lambda j: (j["latitude"], j["longitude"],
                    f"{j.get('region', '')} {j.get('city', '')}".strip())),
        ("https://get.geojs.io/v1/ip/geo.json",
         lambda j: (j["latitude"], j["longitude"],
                    f"{j.get('region', '')} {j.get('city', '')}".strip())),
        ("https://ipapi.co/json/",
         lambda j: (j["latitude"], j["longitude"],
                    f"{j.get('region', '')} {j.get('city', '')}".strip())),
    ):
        try:
            j = json.loads(_get(url, timeout=5))
            lat, lon, name = pick(j)
            if lat and lon:
                lat, lon = float(lat), float(lon)
                ko = reverse_geocode(lat, lon)
                return lat, lon, (ko or name or "확인된 위치"), "인터넷 위치"
        except Exception:
            continue
    return None


class MapScreen(Screen):
    """
    현재 위치에서 반경 안의 당첨판매점을 거리순으로 보여준다.

    위치는 세 단계로 시도한다.
      1) 안드로이드 GPS (plyer)  — 가장 정확, 실내에서는 실패할 수 있다
      2) 통신망 IP               — 도시 단위, 데스크톱 테스트도 여기로 잡힌다
      3) 기본 좌표(서울시청)     — 둘 다 막혔을 때
    GPS 콜백은 다른 스레드에서 오므로 반드시 Clock 으로 메인에 넘긴다.
    """

    DEFAULT = (37.5665, 126.9780, "서울 시청 부근", "기본값")

    def __init__(self, **kw):
        super().__init__(**kw)
        self.radius, self.rank = 5, "전체"
        self.lat, self.lon, self.place, self.src = self.DEFAULT
        fx = PREFS.get("fixed_loc")
        if fx:
            self.lat, self.lon, self.place, self.src = (
                fx["lat"], fx["lon"], fx["place"], "직접 지정")
        self.busy = False
        self._gps_on = False
        self._build()

    def _build(self):
        root = BoxLayout(orientation="vertical", padding=[dp(15), dp(14)],
                         spacing=dp(12))
        root.add_widget(SectionTitle("현재 위치", 0))

        loc = Card(bg=T.surface, orientation="horizontal",
                   padding=[dp(13), dp(10)], spacing=dp(8),
                   size_hint_y=None, height=dp(68 * max(1.0, UI.scale)))
        self.loc_label = lbl("위치 확인 중…", size=12.5, color=T.dim)
        loc.add_widget(self.loc_label)
        self.refresh_btn = Btn("갱신", bg=T.chungrok, fsize=11.5,
                               size_hint=(None, None), width=dp(58),
                               height=dp(34), pos_hint={"center_y": .5})
        self.refresh_btn.bind(on_release=self._locate)
        loc.add_widget(self.refresh_btn)
        pin = Btn("지정", bg=T.field, fsize=11.5, border=True,
                  size_hint=(None, None), width=dp(52), height=dp(34),
                  pos_hint={"center_y": .5})
        pin.bind(on_release=self._pin)
        loc.add_widget(pin)
        root.add_widget(loc)

        root.add_widget(SectionTitle("반경", 1))
        rad = BoxLayout(orientation="horizontal", spacing=dp(7),
                        size_hint_y=None, height=dp(40))
        self.rad_chips = []
        for km in (3, 5, 10, 50):
            c = Chip(f"{km}km", active=(km == 5), on_toggle=self._pick_rad)
            c.km = km
            self.rad_chips.append(c)
            rad.add_widget(c)
        root.add_widget(rad)

        root.add_widget(SectionTitle("등수", 2))
        rk = BoxLayout(orientation="horizontal", spacing=dp(7),
                       size_hint_y=None, height=dp(40))
        self.rk_chips = []
        for r in ("전체", "1등", "2등"):
            c = Chip(r, active=(r == "전체"), on_toggle=self._pick_rank,
                     accent=T.juhong)
            c.rank = r
            self.rk_chips.append(c)
            rk.add_widget(c)
        root.add_widget(rk)

        row2 = BoxLayout(orientation="horizontal", spacing=dp(8),
                         size_hint_y=None, height=dp(34))
        self.count = lbl("", size=11.5, color=T.chija)
        row2.add_widget(self.count)
        self.dl_btn = Btn(text="자료 받기", bg=T.chungrok, size_hint_x=None,
                          width=dp(96))
        self.dl_btn.bind(on_release=self._download)
        row2.add_widget(self.dl_btn)
        root.add_widget(row2)
        self.dl_bar = ProgressBarKR(size_hint_y=None, height=dp(6), opacity=0)
        root.add_widget(self.dl_bar)

        sv = SafeScroll(bar_width=dp(2.5), bar_color=T.stroke)
        self.list_box = BoxLayout(orientation="vertical", spacing=dp(8),
                                  size_hint_y=None)
        self.list_box.bind(minimum_height=self.list_box.setter("height"))
        sv.add_widget(self.list_box)
        root.add_widget(sv)
        self.add_widget(root)
        Clock.schedule_once(lambda *a: self._locate(), 0.5)

    def on_leave(self, *a):
        self._stop_gps()

    # -- 위치 ---------------------------------------------------
    def _stop_gps(self):
        if self._gps_on:
            try:
                from plyer import gps
                gps.stop()
            except Exception:
                pass
            self._gps_on = False

    def _pin(self, *a):
        """
        주소를 직접 입력해 위치를 고정한다.
        IP 위치는 통신사 회선 등록지 기준이라 10km 이상 어긋나는 일이 흔하다.
        PC 에서 쓰거나 실내에서 GPS 가 안 잡힐 때 이 방법이 가장 정확하다.
        """
        box = BoxLayout(orientation="vertical", padding=dp(16), spacing=dp(12))
        p = Popup(title="위치 직접 지정", title_font=FONT, title_size=dp(14),
                  content=box, size_hint=(0.9, None),
                  height=dp(340 * max(1.0, UI.scale)),
                  separator_color=T.chungrok,
                  background_color=(0, 0, 0, .78))
        box.add_widget(lbl(
            "예) 광주시 쌍령동   ·   또는 좌표 37.4155, 127.2610\n"
            "찾은 결과를 확인하고 [적용] 을 눌러야 고정됩니다.",
            size=10.5, color=T.dim, size_hint_y=None, height=dp(32)))
        f = Field("주소", PREFS.get("fixed_loc", {}).get("place", ""),
                  hint="예: 경기도 광주시 쌍령동")
        box.add_widget(f)
        stat = lbl("", size=11.5, color=T.chija, size_hint_y=None,
                   height=dp(52))
        self._found = None
        box.add_widget(stat)
        box.add_widget(Widget())

        def apply_loc(la, lo, nm):
            PREFS["fixed_loc"] = {"lat": la, "lon": lo, "place": nm}
            save_prefs(PREFS)
            p.dismiss()
            self._done(la, lo, nm, "직접 지정")
            toast("위치를 고정했습니다.\n[갱신] 을 누르면 고정이 풀리고 "
                  "실제 위치를 다시 찾습니다.")

        def find(*_a):
            q = f.value.strip()
            if not q:
                stat.text = "주소나 좌표를 넣으세요."
                return
            # "37.4155, 127.2610" 처럼 좌표를 직접 넣으면 그대로 쓴다
            m = re.match(r"^\s*(-?\d+\.\d+)\s*,\s*(-?\d+\.\d+)\s*$", q)
            if m:
                la, lo = float(m.group(1)), float(m.group(2))
                stat.text = "좌표로 고정합니다."
                threading.Thread(target=lambda: Clock.schedule_once(
                    lambda _dt: apply_loc(la, lo, reverse_geocode(la, lo)
                                          or f"{la:.4f}, {lo:.4f}"), 0),
                    daemon=True).start()
                return
            stat.text = "찾는 중…"

            def work():
                r = geocode(q)

                def done(_dt):
                    if not r:
                        stat.text = ("찾지 못했습니다. '광주시 쌍령동' 처럼 "
                                     "짧게 쓰거나 좌표를 넣어보세요.")
                        return
                    la, lo, nm = r
                    stat.text = (f"[color=5FBF7F]{nm}[/color]\n"
                                 f"{la:.4f}, {lo:.4f}  —  [적용] 을 누르세요")
                    self._found = (la, lo, nm)
                    b3.opacity = 1
                    b3.disabled = False
                Clock.schedule_once(done, 0)
            threading.Thread(target=work, daemon=True).start()

        def clear(*_a):
            PREFS.pop("fixed_loc", None)
            save_prefs(PREFS)
            p.dismiss()
            self._locate()

        act = BoxLayout(orientation="horizontal", spacing=dp(9),
                        size_hint_y=None, height=dp(44))
        b0 = Btn("해제", bg=T.field, fsize=12.5, border=True,
                 size_hint_x=None, width=dp(72))
        b0.bind(on_release=clear)
        b1 = Btn("닫기", bg=T.field, fsize=12.5, border=True)
        b1.bind(on_release=p.dismiss)
        b2 = Btn("찾기", bg=T.field, fsize=12.5, border=True)
        b2.bind(on_release=find)
        b3 = Btn("적용", bg=T.chungrok, fsize=12.5, opacity=0, disabled=True)
        b3.bind(on_release=lambda *_a: (apply_loc(*self._found)
                                        if getattr(self, "_found", None)
                                        else None))
        for b in (b0, b1, b2, b3):
            act.add_widget(b)
        box.add_widget(act)
        p.open()

    def _locate(self, *a):
        """
        갱신 버튼.
        직접 지정한 위치가 있으면 그 상태를 먼저 풀어야 실측이 의미가 있다.
        예전에는 조용히 고정 위치를 다시 보여줘서 아무 반응이 없어 보였다.
        """
        if self.busy:
            return
        fx = PREFS.get("fixed_loc")
        if fx and not getattr(self, "_force", False):
            PREFS.pop("fixed_loc", None)
            save_prefs(PREFS)
            toast("고정 위치를 해제했습니다.\n현재 위치를 다시 찾습니다.")
        self._force = False
        self.busy = True
        # 어떤 이유로든 콜백이 오지 않을 때 버튼이 영영 잠기지 않게 한다.
        Clock.unschedule(self._unlock)
        Clock.schedule_once(self._unlock, 30.0)
        self._gen = getattr(self, "_gen", 0) + 1
        self.refresh_btn.text = "…"
        self.refresh_btn.disabled = True
        self.loc_label.text = "위치를 확인하는 중입니다…"
        self.loc_label.color = T.dim

        if platform == "android":
            if not ensure_permission("ACCESS_FINE_LOCATION",
                                     on_ready=self._locate_retry):
                self.loc_label.text = "위치 권한을 허용해 주세요."
                self.loc_label.color = T.chija
                self.busy = False
                self.refresh_btn.text = "갱신"
                self.refresh_btn.disabled = False
                return
            if self._try_gps():
                return
        self._try_network()

    def _unlock(self, *a):
        """30초가 지나도 끝나지 않으면 버튼을 되살린다."""
        if not self.busy:
            return
        self.busy = False
        Clock.unschedule(self._unlock)
        self.refresh_btn.text = "갱신"
        self.refresh_btn.disabled = False
        self.loc_label.text = "위치를 찾지 못했습니다. 다시 눌러 보세요."
        self.loc_label.color = T.chija

    def _locate_retry(self, *a):
        """권한 창에서 허용을 누른 뒤 자동으로 다시 시도한다."""
        self.busy = False
        self._locate()

    def _try_gps(self):
        # ① 마지막으로 알려진 위치 — 즉시 응답
        last = android_last_location()
        if last:
            la, lo = last
            gen = getattr(self, "_gen", 0)

            def resolve_last():
                ko = reverse_geocode(la, lo) or "현재 위치"

                def apply(_dt):
                    if getattr(self, "_gen", 0) == gen:
                        self._done(la, lo, ko, "GPS")
                Clock.schedule_once(apply, 0)
            threading.Thread(target=resolve_last, daemon=True).start()
            return True

        # ② 새로 한 번 요청
        gen2 = getattr(self, "_gen", 0)

        def on_fix(la, lo):
            if getattr(self, "_gen", 0) != gen2:
                return
            Clock.unschedule(self._gps_timeout)

            def resolve():
                ko = reverse_geocode(la, lo) or "현재 위치"
                Clock.schedule_once(
                    lambda _dt: self._done(la, lo, ko, "GPS"), 0)
            threading.Thread(target=resolve, daemon=True).start()

        if android_request_location(on_fix):
            self._gps_on = True
            Clock.schedule_once(self._gps_timeout, 15.0)
            return True

        # ③ plyer 백업
        try:
            from plyer import gps

            def on_loc(**kw):
                lat, lon = kw.get("lat"), kw.get("lon")
                if lat is None or lon is None:
                    return
                la, lo = float(lat), float(lon)

                gen = getattr(self, "_gen", 0)

                def resolve():
                    ko = reverse_geocode(la, lo) or "현재 위치"

                    def apply(_dt):
                        if getattr(self, "_gen", 0) != gen:
                            return          # 그 사이 다시 눌렀으면 버린다
                        self._done(la, lo, ko, "GPS")
                    Clock.schedule_once(apply, 0)
                threading.Thread(target=resolve, daemon=True).start()

            def on_status(stype, status):
                pass

            gps.configure(on_location=on_loc, on_status=on_status)
            gps.start(minTime=2000, minDistance=10)
            self._gps_on = True
            # GPS 가 8초 안에 안 잡히면 통신망으로 넘어간다 (실내 대비)
            Clock.schedule_once(self._gps_timeout, 15.0)
            return True
        except Exception as e:
            log_crash(e)
            return False

    def _gps_timeout(self, *a):
        if self.busy:
            self._stop_gps()
            self._try_network()

    def _try_network(self):
        """IP 조회는 네트워크라 반드시 백그라운드에서."""
        gen = getattr(self, "_gen", 0)

        def work():
            r = locate_by_ip()

            def apply(_dt):
                if getattr(self, "_gen", 0) != gen:
                    return
                self._done(*r) if r else self._failed()
            Clock.schedule_once(apply, 0)
        threading.Thread(target=work, daemon=True).start()

    def _done(self, lat, lon, place, src):
        self.busy = False
        Clock.unschedule(self._unlock)
        self._stop_gps()
        Clock.unschedule(self._gps_timeout)
        self.lat, self.lon, self.place, self.src = lat, lon, place, src
        self.refresh_btn.text = "갱신"
        self.refresh_btn.disabled = False
        self.loc_label.color = T.text
        stamp = dt.datetime.now().strftime("%H:%M")
        note = {"GPS": "위성 · 오차 수십 m",
                "인터넷 위치": "회선 기준 · 오차 수 km",
                "직접 지정": "고정됨",
                "기본값": "확인 실패"}.get(src, src)
        acc = LOC_INFO.get("acc") or 0
        acc_txt = f"  ·  오차 약 {acc:.0f}m" if (src == "GPS" and acc) else ""
        prov = LOC_INFO.get("src") or ""
        prov_txt = f"  ·  {prov}" if (src == "GPS" and prov) else ""
        self.loc_label.text = (
            f"{place}\n[size=10sp][color=BFC7D5]{note}  ·  {stamp}"
            f"{acc_txt}{prov_txt}\n{lat:.5f}, {lon:.5f}[/color][/size]")
        self._render()

    def _failed(self):
        self.busy = False
        Clock.unschedule(self._unlock)
        self.refresh_btn.text = "갱신"
        self.refresh_btn.disabled = False
        self.lat, self.lon, self.place, self.src = self.DEFAULT
        self.loc_label.color = T.chija
        self.loc_label.text = (
            "위치를 얻지 못했습니다\n"
            "[size=10sp]인터넷·위치 권한을 확인하거나 [지정] 으로 직접 넣으세요."
            "[/size]")
        self._render()

    # -- 필터 ---------------------------------------------------
    def _pick_rad(self, chip):
        for c in self.rad_chips:
            c.set_active(c is chip)
        chip.set_active(True)
        self.radius = chip.km
        self._render()

    def _download(self, *a):
        """최근 회차의 당첨판매점을 받아온다. 시간이 걸리므로 백그라운드."""
        if getattr(self, "_dl", False):
            return
        self._dl = True
        self.dl_btn.text = "…"
        self.dl_btn.disabled = True

        latest = DRAWS.latest_round_by_date()
        rounds = list(range(max(1, latest - 29), latest + 1))

        self.dl_bar.opacity = 1
        self.dl_bar.set(0.0)

        def prog(done, total):
            Clock.schedule_once(
                lambda _dt: (self.dl_bar.set(done / max(1, total)),
                             setattr(self.dl_btn, "text",
                                     f"{done * 100 // max(1, total)}%")), 0)

        def work():
            try:
                refresh_stores(rounds, prog)
                msg = "당첨판매점 자료를 받았습니다."
            except Exception as e:
                log_crash(e)
                msg = "자료를 받지 못했습니다. 잠시 뒤 다시 시도해 주세요."

            def fin(_dt):
                self._dl = False
                self.dl_bar.opacity = 0
                self.dl_btn.text = "자료 받기"
                self.dl_btn.disabled = False
                toast(msg)
                self._render()
            Clock.schedule_once(fin, 0)

        threading.Thread(target=work, daemon=True).start()

    def _pick_rank(self, chip):
        for c in self.rk_chips:
            c.set_active(c is chip)
        chip.set_active(True)
        self.rank = chip.rank
        self._render()

    # -- 목록 ---------------------------------------------------
    def _render(self):
        self.list_box.clear_widgets()
        want = {"1등": 1, "2등": 2}.get(self.rank)

        real = None
        try:
            real = stores_near(self.lat, self.lon, self.radius, want,
                               region_hint=self.place or "")
        except Exception as e:
            log_crash(e)
        if real is not None:
            rows, is_real = real, True
        else:
            rows, is_real = [], False
            for name, addr, tel, la, lo, wins in MOCK_SHOPS:
                hits = [w for w in wins if want is None or w[1] == want]
                if not hits:
                    continue
                d = haversine(self.lat, self.lon, la, lo)
                if d <= self.radius:
                    rows.append((d, name, addr, tel, hits))
            rows.sort(key=lambda x: x[0])

        self.count.text = (f"{self.radius}km 이내  ·  {self.rank}  ·  "
                           f"{len(rows)}곳")

        if not rows:
            near = min(
                (haversine(self.lat, self.lon, s[3], s[4]) for s in MOCK_SHOPS),
                default=0)
            c = Card(bg=T.surface, padding=dp(15), size_hint_y=None,
                     height=dp(76))
            c.add_widget(lbl(
                f"{self.radius}km 안에는 없습니다.\n"
                f"가장 가까운 곳이 약 {near:.0f}km 떨어져 있습니다. "
                f"반경을 넓혀 보세요.", size=12, color=T.dim))
            self.list_box.add_widget(c)
        for d, name, addr, tel, hits in rows:
            card = Card(bg=T.surface, orientation="vertical",
                        padding=[dp(13), dp(11)], spacing=dp(5),
                        size_hint_y=None,
                        height=dp(50) + dp(19) * min(len(hits), 4))
            top = BoxLayout(orientation="horizontal", size_hint_y=None,
                            height=dp(20))
            top.add_widget(lbl(f"[b]{name}[/b]", size=13.5))
            top.add_widget(lbl(f"{d:.1f}km", size=11.5, color=T.chija,
                               halign="right", size_hint_x=None,
                               width=dp(56)))
            card.add_widget(top)
            card.add_widget(lbl(f"{addr}   ·   {tel}", size=10.5,
                                color=T.dim, size_hint_y=None,
                                height=dp(16)))
            for rnd, rank in sorted(hits, reverse=True)[:4]:
                col = "D4462B" if rank == 1 else "2F8C80"
                card.add_widget(lbl(
                    f"[color={col}][b]{rank}등[/b][/color]   {rnd}회",
                    size=11.5, size_hint_y=None, height=dp(17)))
            self.list_box.add_widget(card)

        n = Card(bg=T.raised, padding=dp(13), size_hint_y=None, height=dp(88))
        n.add_widget(lbl(
            ("동행복권 당첨판매점 자료입니다. [자료 받기] 로 회차를 더 "
             "모으면 목록이 촘촘해집니다.\n\n"
             if is_real else
             "아직 예시 데이터입니다. 아래 [자료 받기] 를 눌러 실제 "
             "당첨판매점을 받아오세요.\n\n") +
            "참고 — 1등이 많이 나온 집은 그만큼 많이 파는 집입니다. "
            "확률이 높은 게 아니라 판매량이 많은 겁니다.",
            size=10.5, color=T.dim))
        self.list_box.add_widget(n)


# ===============================================================
#  화면 4 — QR 확인
# ===============================================================
class ScanFrame(ButtonBehavior, Card):
    """
    누르면 카메라가 켜지는 스캔 영역. 네 모서리 괄호는 직접 그린다.
    카메라 모듈이 없는 환경(PC 테스트)에서는 눌러도 안내만 띄운다.
    """

    def __init__(self, **kw):
        super().__init__(**kw)
        with self.canvas.after:
            Color(*T.chija)
            self._l = [Line(width=dp(1.8)) for _ in range(4)]
        self.bind(pos=self._draw, size=self._draw)

    def _draw(self, *a):
        m, L = dp(28), dp(26)
        x, y = self.x + m, self.y + m
        w, h = self.width - 2 * m, self.height - 2 * m
        self._l[0].points = [x, y + L, x, y, x + L, y]
        self._l[1].points = [x + w - L, y, x + w, y, x + w, y + L]
        self._l[2].points = [x + w, y + h - L, x + w, y + h, x + w - L, y + h]
        self._l[3].points = [x + L, y + h, x, y + h, x, y + h - L]


def ensure_permission(name, on_ready=None):
    """
    안드로이드 런타임 권한을 확인하고, 없으면 요청한다.
    이미 허용돼 있으면 True 를 돌려준다.
    앱 시작 시 사용자가 [거부] 를 눌렀어도 기능을 쓸 때 다시 물어보게 한다.
    """
    if platform != "android":
        return True
    try:
        from android.permissions import (request_permissions, Permission,
                                         check_permission)
        p = getattr(Permission, name, None)
        if p is None:
            return False
        if check_permission(p):
            return True
        request_permissions(
            [p], (lambda *a: Clock.schedule_once(lambda _dt: on_ready(), 0))
            if on_ready else None)
        return False
    except Exception as e:
        log_crash(e)
        return False


CAM_ERR = ""
_CAM_OK = None          # None = 아직 확인 안 함


def qr_available():
    """
    카메라 스캔 가능 여부.
    camera4kivy import 는 안드로이드에서 수 초가 걸리기도 해서, 설정 화면을
    열 때마다 부르면 앱이 멈춘 것처럼 보인다. 결과를 한 번만 계산해 둔다.
    """
    global CAM_ERR, _CAM_OK
    if _CAM_OK is not None:
        return _CAM_OK
    try:
        import camera4kivy  # noqa: F401
        CAM_ERR = ""
        _CAM_OK = True
    except Exception as e:
        CAM_ERR = f"{type(e).__name__}: {e}"
        _CAM_OK = False
    return _CAM_OK


def decode_qr_bytes(pixels, size, fmt="rgba"):
    """
    프레임에서 QR 문자열을 뽑는다. pyzbar 를 먼저 쓰고 없으면 OpenCV.
    둘 다 없으면 None.
    """
    try:
        from PIL import Image as PILImage
        img = PILImage.frombytes("RGBA" if fmt == "rgba" else "RGB",
                                 size, bytes(pixels))
        try:
            from pyzbar.pyzbar import decode as zdecode
            from PIL import ImageOps
            g = img.convert("L")
            # 초점이 덜 맞거나 어두운 프레임을 위해 여러 형태로 시도한다.
            cands = [g, ImageOps.autocontrast(g)]
            w, h = g.size
            if w > 640:
                cands.append(g.resize((w // 2, h // 2)))
            for im in cands:
                for r in zdecode(im):
                    t = r.data.decode("utf-8", "ignore")
                    if t:
                        return t
            return None
        except Exception:
            pass
        try:
            import numpy as np
            import cv2
            arr = np.array(img.convert("RGB"))[:, :, ::-1]
            t, _pts, _st = cv2.QRCodeDetector().detectAndDecode(arr)
            return t or None
        except Exception:
            return None
    except Exception:
        return None


class ScanPopup(Popup):
    """
    카메라 미리보기 + 자동 인식.
    프레임마다 디코딩을 돌리면 느려지므로 0.4 초 간격으로만 검사한다.
    """

    def __init__(self, on_found, **kw):
        self.on_found = on_found
        self.preview = None
        self._last = 0.0
        self._done = False
        box = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(9))
        super().__init__(title="QR 스캔", title_font=FONT, title_size=dp(14),
                         content=box, size_hint=(0.96, 0.82),
                         separator_color=T.chija,
                         background_color=(0, 0, 0, .9), **kw)
        self.status = lbl("카메라를 여는 중…", size=12, color=T.dim,
                          halign="center", size_hint_y=None, height=dp(22))
        try:
            from camera4kivy import Preview
            self.preview = Preview(aspect_ratio="4:3")
            box.add_widget(self.preview)
            self.diag = lbl("카메라 준비 중…", size=10.5, color=T.dim,
                            halign="center", size_hint_y=None, height=dp(34))
            box.add_widget(self.diag)
        except Exception as e:
            log_crash(e)
            qr_available()          # CAM_ERR 갱신
            box.add_widget(lbl(
                "카메라를 열지 못했습니다.\n\n"
                f"[color=E8B33D]{CAM_ERR or type(e).__name__}: {e}[/color]\n\n"
                "requirements 에 camera4kivy, gestures4kivy,\n"
                "libzbar, pyzbar, pillow 가 들어갔는지 확인하세요.",
                size=11.5, color=T.dim, halign="center"))
            self.status.text = ""
        box.add_widget(self.status)
        row = BoxLayout(orientation="horizontal", spacing=dp(9),
                        size_hint_y=None, height=dp(46))
        b = Btn("닫기", bg=T.field, fsize=13, border=True)
        b.bind(on_release=self.dismiss)
        row.add_widget(b)
        box.add_widget(row)
        self.bind(on_dismiss=self._stop)

    def open(self, *a, **k):
        super().open(*a, **k)
        if self.preview:
            Clock.schedule_once(self._start, 0.35)

    def _start(self, *a):
        try:
            # camera4kivy 가 실제로 부르는 이름은 analyze_pixels_callback 이다.
            # on_analyze_pixels 로 걸어두면 콜백이 영영 오지 않는다.
            self.preview.analyze_pixels_callback = self._frame
            # 탭 초점·핀치 줌 제스처를 끄면 CameraX 의 연속 자동초점이
            # 계속 동작한다. 손대면 확 당겨지던 문제도 같이 사라진다.
            # 제스처를 끄면 초점을 맞출 방법이 사라진다. 켠 채로 두고
            # 자동 인식만 콜백으로 처리한다.
            kw = dict(enable_analyze_pixels=True,
                      enable_zoom_gesture=True,
                      enable_focus_gesture=True,
                      analyze_pixels_resolution=1024,
                      default_zoom=0.0)
            while True:
                try:
                    self.preview.connect_camera(**kw)
                    break
                except TypeError as te:
                    bad = [k for k in list(kw) if k in str(te)]
                    if not bad:
                        raise
                    for k in bad:
                        kw.pop(k, None)
            self.status.text = "용지의 QR 을 화면 안에 맞춰 주세요"
        except Exception as e:
            log_crash(e)
            self.status.text = f"카메라를 열지 못했습니다 ({type(e).__name__})"

    def _frame(self, pixels, size, image_pos, image_scale, mirror):
        if self._done:
            return
        import time
        now = time.time()
        if now - self._last < 0.25:
            return
        self._last = now
        self._nframe = getattr(self, "_nframe", 0) + 1
        try:
            txt = decode_qr_bytes(pixels, size)
            self._lasterr = ""
        except Exception as e:
            txt = None
            self._lasterr = f"{type(e).__name__}: {e}"
        if self._nframe % 4 == 0 and getattr(self, "diag", None):
            msg = (f"프레임 {self._nframe}  ·  {size[0]}x{size[1]}"
                   + (f"\n{self._lasterr}" if self._lasterr else ""))
            Clock.schedule_once(
                lambda _dt: setattr(self.diag, "text", msg), 0)
        if txt:
            self._done = True
            Clock.schedule_once(lambda _dt: self._hit(txt), 0)

    def _hit(self, txt):
        self._stop()
        self.dismiss()
        self.on_found(txt)

    def _stop(self, *a):
        try:
            if self.preview:
                self.preview.disconnect_camera()
        except Exception:
            pass


class QRScreen(Screen):
    def __init__(self, **kw):
        super().__init__(**kw)
        self._build()

    def _build(self):
        sv, body = vscroll()
        body.add_widget(SectionTitle("QR 당첨확인", 0))

        f = ScanFrame(bg=T.surface, orientation="vertical", padding=dp(14),
                      size_hint_y=None, height=dp(150))
        f.add_widget(Widget())
        f.add_widget(lbl("여기를 눌러 QR 스캔", size=13.5, color=T.chija,
                         bold=True, halign="center", size_hint_y=None,
                         height=dp(20)))
        f.add_widget(lbl("용지의 QR 을 비추면 자동으로 읽습니다",
                         size=10.5, color=T.faint, halign="center",
                         size_hint_y=None, height=dp(16)))
        f.add_widget(Widget())
        f.bind(on_release=self._scan)
        body.add_widget(f)
        body.add_widget(lbl(
            "카메라가 없거나 안 될 때는 아래에 주소를 직접 붙여넣어도 됩니다.",
            size=10.5, color=T.faint, size_hint_y=None, height=dp(18)))

        self.qr = TapInput(
            hint_text="QR 을 찍거나 주소를 붙여넣으세요",
            font_name=FONT, font_size=dp(12 * UI.scale), size_hint_y=None,
            height=dp(74),
            background_color=T.field, foreground_color=T.text,
            cursor_color=T.chija, hint_text_color=T.faint,
            padding=[dp(11), dp(11)], background_normal="",
            background_active="")
        body.add_widget(self.qr)

        b = Btn("당첨 확인", bg=T.juhong, fsize=15, size_hint_y=None,
                height=dp(50))
        b.bind(on_release=self._check)
        body.add_widget(b)

        self.out = BoxLayout(orientation="vertical", spacing=dp(8),
                             size_hint_y=None)
        self.out.bind(minimum_height=self.out.setter("height"))
        body.add_widget(self.out)
        body.add_widget(Widget(size_hint_y=None, height=dp(6)))
        self.add_widget(sv)

    def _scan(self, *a):
        if platform == "android" and not ensure_permission(
                "CAMERA", on_ready=self._scan):
            toast("카메라 권한을 허용해 주세요.")
            return
        """스캔 영역 탭 → 카메라. 읽으면 입력창에 넣고 바로 판정한다."""
        def found(txt):
            self.qr.text = txt
            self._check()
            toast("QR 을 읽었습니다.")
        try:
            ScanPopup(found).open()
        except Exception as e:
            log_crash(e)
            toast(f"카메라를 열 수 없습니다 ({type(e).__name__})")

    def _check(self, *a):
        self.out.clear_widgets()
        data, err = parse_lotto_qr(self.qr.text)
        if err:
            c = Card(bg=T.surface, padding=dp(14), size_hint_y=None,
                     height=dp(58), bcol=T.juhong)
            c.add_widget(lbl(err, size=12.5, color=T.text))
            self.out.add_widget(c)
            return

        rnd = data["round"]
        row = DRAWS.get(rnd)
        self.out.add_widget(SectionTitle(
            f"{rnd}회 · {len(data['games'])}게임", 1,
            sub=(row["date"] if row else "추첨 전")))
        if data.get("tr"):
            self.out.add_widget(lbl(
                f"TR {data['tr']}   ·   판매점 {data['store']}",
                size=10, color=T.faint, size_hint_y=None, height=dp(16)))

        if row:
            w = Card(bg=T.raised, orientation="vertical", padding=dp(12),
                     spacing=dp(6), size_hint_y=None, height=dp(70))
            w.add_widget(lbl("당첨번호", size=11, color=T.dim,
                             size_hint_y=None, height=dp(15)))
            w.add_widget(BallRow(row["nums"], d=29,
                                 bonus=row["bonus"] or None))
            self.out.add_widget(w)

        for i, nums in enumerate(data["games"]):
            res = DRAWS.check(nums, rnd)
            hitset = set(row["nums"]) if row else set()
            card = Card(bg=T.surface, orientation="vertical", padding=dp(12),
                        spacing=dp(7), size_hint_y=None, height=dp(84))
            top = BoxLayout(orientation="horizontal", size_hint_y=None,
                            height=dp(20))
            md = data["modes"][i] if i < len(data.get("modes", [])) else ""
            top.add_widget(lbl(
                f"[b]{chr(ord('A') + i)}[/b]"
                + (f"  [color=6B7280]{md}[/color]" if md and md != "?" else ""),
                size=13))
            if res is None:
                top.add_widget(lbl("추첨 전", size=11.5, color=T.dim,
                                   halign="right"))
            elif res["rank"]:
                card.set_border(T.chija)
                card.set_bg((T.chija[:3] + (0.14,)))
                extra = " (보너스 미확인)" if res["unsure"] else ""
                top.add_widget(lbl(
                    f"[color=E8B33D][b]{res['rank']}등[/b][/color]  "
                    f"{res['hit']}개 일치{extra}", size=12, halign="right"))
            else:
                top.add_widget(lbl(f"낙첨 · {res['hit']}개 일치", size=11.5,
                                   color=T.dim, halign="right"))
            card.add_widget(top)
            row_w = BoxLayout(orientation="horizontal", spacing=dp(5),
                              size_hint_y=None, height=dp(30))
            for n in nums:
                row_w.add_widget(Ball(n, 30, faded=bool(hitset)
                                      and n not in hitset))
            row_w.add_widget(Widget())
            card.add_widget(row_w)
            self.out.add_widget(card)

        sb = Btn("이 용지 공유", bg=T.field, fsize=13, border=True,
                 size_hint_y=None, height=dp(44))
        sb.bind(on_release=lambda *a: share_now(
            share_text(rnd, data["games"], "QR 스캔 결과"),
            f"{rnd}회 용지 공유"))
        self.out.add_widget(sb)


# ===============================================================
#  화면 5 — 내 번호 (회차·날짜별 정리)
# ===============================================================
RANK_COLOR = {1: "E8B33D", 2: "E8B33D", 3: "5FBF7F",
              4: "5FBF7F", 5: "2F8C80"}


class MyScreen(Screen):
    def __init__(self, **kw):
        super().__init__(**kw)
        self._build()

    def _build(self):
        root = BoxLayout(orientation="vertical")
        head = BoxLayout(orientation="horizontal", padding=[dp(15), dp(12), dp(15), dp(4)],
                         spacing=dp(9), size_hint_y=None, height=dp(46))
        head.add_widget(lbl("내 번호", size=18, bold=True, disp=True))
        allshare = Btn("전체 공유", bg=T.field, fsize=11, border=True,
                       size_hint=(None, None), width=dp(70), height=dp(30),
                       pos_hint={"center_y": .5})
        allshare.bind(on_release=self._share_all)
        head.add_widget(allshare)
        clr = Btn("비우기", bg=T.field, fsize=11, border=True,
                  size_hint=(None, None), width=dp(58), height=dp(30),
                  pos_hint={"center_y": .5})
        clr.bind(on_release=self._clear)
        head.add_widget(clr)
        root.add_widget(head)

        sv, body = vscroll()
        self.body = body
        root.add_widget(sv)
        self.add_widget(root)

    def on_pre_enter(self, *a):
        self.refresh()

    def on_leave(self, *a):
        self.body.clear_widgets()
        gc.collect()

    def _clear(self, *a):
        VAULT.items = []
        VAULT.save()
        self.refresh()

    def _share_all(self, *a):
        groups = VAULT.by_round()
        limit = getattr(self, "_limit", 6)
        more = max(0, len(groups) - limit)
        groups = groups[:limit]
        if not groups:
            toast("저장된 번호가 없습니다.")
            return
        out = [f"[{APP_NAME}] 저장 번호 전체", ""]
        for rnd, items in groups:
            d = round_date(rnd)
            wd = "월화수목금토일"[d.weekday()]
            row = DRAWS.get(rnd)
            out.append(f"── 제{rnd}회  {d.strftime('%Y.%m.%d')}({wd})")
            if row:
                out.append("   당첨  " + " ".join(f"{n:02d}"
                                                for n in row["nums"])
                           + (f" + {row['bonus']:02d}" if row["bonus"] else ""))
            for i, it in enumerate(sorted(items, key=lambda z: z["saved"])):
                res = DRAWS.check(it["nums"], rnd)
                mark = ""
                if res and res["rank"]:
                    mark = f"  ← {res['rank']}등"
                elif res:
                    mark = f"  ({res['hit']}개)"
                out.append(f"   {chr(65 + i)}   "
                           + " ".join(f"{n:02d}" for n in it["nums"]) + mark)
            out.append("")
        cnt, won = VAULT.spend_this_month()
        out.append(f"이번 달 {cnt}게임 · {won:,}원 상당")
        share_now("\n".join(out), "전체 공유")

    def _drop(self, items):
        for it in items:
            VAULT.remove(it["id"])
        self.refresh()

    def refresh(self):
        b = self.body
        b.clear_widgets()

        # 요약
        cnt, won = VAULT.spend_this_month()
        budget = PREFS.get("budget", 20000)
        ratio = min(1.0, won / budget) if budget else 0
        s = Card(bg=T.surface, orientation="vertical",
                 padding=[dp(15), dp(13)], spacing=dp(8),
                 size_hint_y=None, height=dp(96))
        top = BoxLayout(orientation="horizontal", size_hint_y=None,
                        height=dp(22))
        top.add_widget(lbl(f"이번 달 {cnt}게임", size=14, bold=True))
        top.add_widget(lbl(f"{won:,}원 / {budget:,}원", size=11.5,
                           color=T.chija if ratio >= 1 else T.dim,
                           halign="right"))
        s.add_widget(top)

        bar = Widget(size_hint_y=None, height=dp(6))
        with bar.canvas:
            Color(*T.field)
            bg = RoundedRectangle(radius=[dp(3)])
            Color(*(T.juhong if ratio >= 1 else T.chungrok))
            fg = RoundedRectangle(radius=[dp(3)])

        def sync(*a):
            bg.pos, bg.size = bar.pos, bar.size
            fg.pos = bar.pos
            fg.size = (bar.width * ratio, bar.height)
        bar.bind(pos=sync, size=sync)
        sync()
        s.add_widget(bar)
        s.add_widget(lbl(
            f"총 {len(VAULT.items)}건 저장  ·  한 게임 {TICKET_PRICE:,}원 기준",
            size=10.5, color=T.faint, size_hint_y=None, height=dp(16)))
        b.add_widget(s)

        groups = VAULT.by_round()
        limit = getattr(self, "_limit", 6)
        more = max(0, len(groups) - limit)
        groups = groups[:limit]
        if not groups:
            c = Card(bg=T.surface, padding=dp(18), size_hint_y=None,
                     height=dp(92))
            c.add_widget(lbl("저장된 번호가 없습니다.\n\n"
                             "번호생성에서 조합을 뽑고, 마음에 드는 걸 탭한 뒤 "
                             "저장하세요.", size=12.5, color=T.dim,
                             halign="center"))
            b.add_widget(c)
            return

        cur = latest_round_by_date()
        for gi, (rnd, items) in enumerate(groups):
            d = round_date(rnd)
            row = DRAWS.get(rnd)
            if rnd > cur:
                left = (d - dt.date.today()).days
                status = f"추첨까지 {left}일" if left > 0 else "오늘 추첨"
                scol = T.chija
            elif row:
                best = min((DRAWS.check(it["nums"], rnd)["rank"] or 9)
                           for it in items)
                status = f"최고 {best}등" if best < 9 else "낙첨"
                scol = T.chija if best < 9 else T.faint
            else:
                status = "결과 미수신"
                scol = T.faint

            gh = Card(bg=T.raised, orientation="horizontal",
                      padding=[dp(13), dp(9)], spacing=dp(8),
                      size_hint_y=None, height=dp(52), bcol=scol)
            left = BoxLayout(orientation="vertical", spacing=dp(2))
            left.add_widget(lbl(f"{rnd}회", size=15, bold=True, disp=True,
                                size_hint_y=None, height=dp(20)))
            left.add_widget(lbl(
                f"{d.strftime('%Y.%m.%d')} "
                f"({'월화수목금토일'[d.weekday()]}) 추첨   ·   {len(items)}게임",
                size=10.5, color=T.dim, size_hint_y=None, height=dp(15)))
            gh.add_widget(left)
            pill = Card(bg=scol[:3] + (0.20,), radius=9, bcol=scol,
                        padding=[dp(9), dp(5)], size_hint=(None, None),
                        width=dp(84), height=dp(28), pos_hint={"center_y": .5})
            pill.add_widget(lbl(status, size=10.5, color=scol,
                                halign="center", bold=True))
            gh.add_widget(pill)
            b.add_widget(gh)

            act = BoxLayout(orientation="horizontal", spacing=dp(8),
                            size_hint_y=None, height=dp(36))
            sb = Btn("이 회차 공유", bg=T.field, fsize=11.5, border=True)
            sb.bind(on_release=lambda _w, rr=rnd, its=items: share_now(
                share_text(rr, [x["nums"] for x in
                                sorted(its, key=lambda z: z["saved"])],
                           f"저장한 {len(its)}조합"),
                f"{rr}회 공유"))
            act.add_widget(sb)
            cb = Btn("삭제", bg=T.field, fsize=11.5, border=True,
                     size_hint_x=None, width=dp(70))
            cb.bind(on_release=lambda _w, its=items: self._drop(its))
            act.add_widget(cb)
            b.add_widget(act)

            if row:
                w = Card(bg=T.raised, orientation="horizontal",
                         padding=[dp(12), dp(9)], spacing=dp(8),
                         size_hint_y=None, height=dp(48))
                w.add_widget(lbl("당첨", size=10.5, color=T.dim,
                                 size_hint_x=None, width=dp(28)))
                w.add_widget(BallRow(row["nums"], d=26,
                                     bonus=row["bonus"] or None))
                b.add_widget(w)

            for it in sorted(items, key=lambda x: x["saved"]):
                res = DRAWS.check(it["nums"], rnd)
                card = Card(bg=T.surface, orientation="vertical",
                            padding=[dp(12), dp(10)], spacing=dp(6),
                            size_hint_y=None, height=dp(80))
                top = BoxLayout(orientation="horizontal", size_hint_y=None,
                                height=dp(18))
                saved = it["saved"].replace("T", " ")[5:16]
                top.add_widget(lbl(f"{saved}  ·  {it['mode']}", size=10.5,
                                   color=T.faint))
                if res and res["rank"]:
                    col = RANK_COLOR.get(res["rank"], "E8B33D")
                    card.set_border(T.chija)
                    card.set_bg(T.chija[:3] + (0.12,))
                    top.add_widget(lbl(
                        f"[color={col}][b]{res['rank']}등[/b][/color]"
                        + ("?" if res["unsure"] else ""),
                        size=12, halign="right"))
                elif res:
                    top.add_widget(lbl(f"{res['hit']}개 일치", size=10.5,
                                       color=T.dim, halign="right"))
                else:
                    top.add_widget(lbl("대기", size=10.5, color=T.dim,
                                       halign="right"))
                card.add_widget(top)

                hs = set(row["nums"]) if row else set()
                rw = BoxLayout(orientation="horizontal", spacing=dp(5),
                               size_hint_y=None, height=dp(29))
                for n in it["nums"]:
                    rw.add_widget(Ball(n, 29, faded=bool(hs) and n not in hs))
                rw.add_widget(Widget())
                card.add_widget(rw)
                b.add_widget(card)

        if more:
            mb = Btn(f"이전 {more}개 회차 더 보기", bg=T.field, fsize=12.5,
                     border=True, size_hint_y=None, height=dp(44))

            def expand(*a):
                self._limit = limit + 10
                self.refresh()
            mb.bind(on_release=expand)
            b.add_widget(mb)
        b.add_widget(Widget(size_hint_y=None, height=dp(8)))


# ===============================================================
#  루트
# ===============================================================
TABS = [("gen", "생성"), ("stat", "통계"), ("map", "탐방"),
        ("qr", "QR"), ("my", "내번호")]


def gradient_texture(top, bot, h=256):
    tex = Texture.create(size=(1, h), colorfmt="rgb")
    buf = bytearray()
    for i in range(h):
        t = i / (h - 1)
        for k in range(3):
            buf.append(int(255 * (bot[k] * (1 - t) + top[k] * t)))
    tex.blit_buffer(bytes(buf), colorfmt="rgb", bufferfmt="ubyte")
    tex.wrap = "clamp_to_edge"
    return tex


class SwipeManager(ScreenManager):
    """
    좌우로 쓸어 탭을 넘긴다.
    가로 이동이 세로보다 뚜렷할 때만 넘겨서, 목록 스크롤과 부딪히지 않게 한다.
    """
    THRESH = dp(48)

    def on_touch_down(self, touch):
        touch.ud["_sw"] = touch.pos
        return super().on_touch_down(touch)

    def on_touch_up(self, touch):
        # 자식이 잡고 있던 터치를 도중에 놓으면 on_touch_up 이 두 번 들어와
        # 화면이 두 칸씩 넘어간다. 한 터치에 한 번만 처리한다.
        import time as _t
        now = _t.time()
        if touch.ud.get("_sw_used") or now - getattr(self, "_last_sw", 0) < 0.6:
            return super().on_touch_up(touch)
        st = touch.ud.get("_sw")
        r = getattr(self, "root_ref", None)
        if st and r:
            # 손가락 궤적은 마우스 드래그보다 훨씬 휘므로 세로 비율을 완화한다.
            dx = (touch.sx - touch.osx) * Window.width
            dy = (touch.sy - touch.osy) * Window.height
            if abs(dx) > self.THRESH and abs(dx) > abs(dy) * 1.1:
                keys = [k for k, _ in TABS]
                try:
                    i = keys.index(self.current)
                except ValueError:
                    i = 0
                j = i - 1 if dx > 0 else i + 1
                if 0 <= j < len(keys):
                    touch.ud["_sw_used"] = True
                    self._last_sw = now
                    self.transition.direction = "right" if dx > 0 else "left"
                    r.go(keys[j], slide=True)
                    return True
        return super().on_touch_up(touch)


class Root(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", **kw)
        with self.canvas.before:
            Color(1, 1, 1, 1)
            self._bg = Rectangle(texture=gradient_texture(T.bg_top, T.bg_bot))
        self.bind(pos=self._sync, size=self._sync)

        self.add_widget(self._header())

        self.sm = SwipeManager(transition=SlideTransition(duration=.18))
        self.sm.root_ref = self
        self.screens = {
            "gen": GenScreen(name="gen"), "stat": StatScreen(name="stat"),
            "map": MapScreen(name="map"), "qr": QRScreen(name="qr"),
            "my": MyScreen(name="my"),
        }
        for s in self.screens.values():
            self.sm.add_widget(s)
        self.add_widget(self.sm)
        self.add_widget(self._nav())
        self._paint("gen")

    def _header(self):
        h = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(70))
        inner = BoxLayout(orientation="vertical", padding=[dp(15), dp(12), dp(15), dp(8)],
                          spacing=dp(2))
        with h.canvas.before:
            Color(*T.surface)
            self._hb = Rectangle()
        h.bind(pos=lambda i, v: setattr(self._hb, "pos", i.pos),
               size=lambda i, v: setattr(self._hb, "size", i.size))
        titlerow = BoxLayout(orientation="horizontal", spacing=dp(8),
                             size_hint_y=None, height=dp(28))
        titlerow.add_widget(lbl(APP_NAME, size=20, bold=True, disp=True))
        gear = Btn("설정", bg=T.field, fsize=10.5, border=True,
                   size_hint=(None, None), width=dp(52), height=dp(26),
                   pos_hint={"center_y": .5})
        gear.bind(on_release=lambda *a: settings_popup(App.get_running_app()))
        titlerow.add_widget(gear)
        inner.add_widget(titlerow)
        inner.add_widget(lbl(
            f"로또 6/45   ·   1등 확률 {TOTAL_COMBOS:,}분의 1",
            size=10.5, color=T.faint, size_hint_y=None, height=dp(15)))
        h.add_widget(inner)

        # 오방색 띠 — 이 앱의 표식
        stripe = Widget(size_hint_y=None, height=dp(3))
        with stripe.canvas:
            self._sr = []
            for c in T.OBANG:
                Color(*c)
                self._sr.append(Rectangle())

        def sync_stripe(*a):
            w = stripe.width / len(T.OBANG)
            for i, r in enumerate(self._sr):
                r.pos = (stripe.x + i * w, stripe.y)
                r.size = (w + 1, stripe.height)
        stripe.bind(pos=sync_stripe, size=sync_stripe)
        h.add_widget(stripe)
        if not FONT_OK:
            h.height = dp(96)
            warn = Card(bg=(0.55, 0.12, 0.08, 1), padding=[dp(10), dp(5)],
                        radius=0, border=False, size_hint_y=None,
                        height=dp(26))
            warn.add_widget(Label(
                text="Korean font missing - put NanumGothic.ttf in assets/",
                font_size=dp(10.5), color=(1, 1, 1, 1)))
            h.add_widget(warn)
        return h

    def _nav(self):
        nav = BoxLayout(orientation="horizontal", size_hint_y=None,
                        height=dp(60), padding=[dp(7), dp(7)], spacing=dp(4))
        with nav.canvas.before:
            Color(*T.surface)
            self._nb = Rectangle()
            Color(*T.stroke)
            self._nl = Rectangle()

        def sync(*a):
            self._nb.pos, self._nb.size = nav.pos, nav.size
            self._nl.pos = (nav.x, nav.top - dp(1))
            self._nl.size = (nav.width, dp(1))
        nav.bind(pos=sync, size=sync)

        self.tabs = {}
        for key, label in TABS:
            b = TapCard(bg=T.surface, radius=11, border=False)
            b.add_widget(lbl(label, size=12, halign="center", bold=True))
            b.key = key
            b.bind(on_release=lambda w: self.go(w.key))
            self.tabs[key] = b
            nav.add_widget(b)
        return nav

    def go(self, key, slide=False):
        if not slide:
            keys = [k for k, _ in TABS]
            try:
                a, b = keys.index(self.sm.current), keys.index(key)
                self.sm.transition.direction = "left" if b > a else "right"
            except ValueError:
                pass
        self.sm.current = key
        self._paint(key)

    def _paint(self, active):
        for k, b in self.tabs.items():
            on = (k == active)
            Animation(rgba=T.juhong if on else T.surface, d=.15).start(b._c)
            b.children[0].color = (1, 1, 1, 1) if on else T.dim

    def _sync(self, *a):
        self._bg.pos, self._bg.size = self.pos, self.size


class Splash(FloatLayout):
    """
    실행 화면. 아이콘이 떠오르고 오방색 띠가 좌에서 우로 채워진 뒤
    본 화면으로 넘어간다. 이 동안 뒤에서 실제 화면을 만든다.
    """

    def __init__(self, on_done=None, **kw):
        super().__init__(**kw)
        self.on_done = on_done
        with self.canvas.before:
            Color(1, 1, 1, 1)
            self._bg = Rectangle(
                texture=gradient_texture(T.bg_top, T.bg_bot))
        self.bind(pos=self._sync, size=self._sync)

        icon = asset("icon.png") or asset("out_icon.png")
        self.art = None
        if icon:
            self.art = KvImage(source=icon, size_hint=(None, None),
                               size=(dp(148), dp(148)),
                               pos_hint={"center_x": .5, "center_y": .58},
                               opacity=0)
            self.add_widget(self.art)

        self.title = lbl(APP_NAME, size=24, bold=True, disp=True,
                         halign="center", size_hint=(1, None), height=dp(34),
                         pos_hint={"center_x": .5, "center_y": .40},
                         opacity=0)
        self.sub = lbl("로또 6/45", size=12, color=T.faint, halign="center",
                       size_hint=(1, None), height=dp(20),
                       pos_hint={"center_x": .5, "center_y": .355},
                       opacity=0)
        self.add_widget(self.title)
        self.add_widget(self.sub)

        self.bar = Widget(size_hint=(None, None),
                          size=(dp(160), dp(4)),
                          pos_hint={"center_x": .5, "center_y": .30})
        with self.bar.canvas:
            Color(*T.stroke)
            self._track = RoundedRectangle(radius=[dp(2)])
            self._segs = []
            for c in T.OBANG:
                Color(*c)
                self._segs.append(RoundedRectangle(radius=[dp(2)]))
        self.bar.bind(pos=self._bar_sync, size=self._bar_sync)
        self.add_widget(self.bar)
        self.progress = 0.0

    def _sync(self, *a):
        self._bg.pos, self._bg.size = self.pos, self.size

    def _bar_sync(self, *a):
        b = self.bar
        self._track.pos, self._track.size = b.pos, b.size
        n = len(self._segs)
        seg = b.width / n
        for i, r in enumerate(self._segs):
            fill = max(0.0, min(1.0, self.progress * n - i))
            r.pos = (b.x + seg * i, b.y)
            r.size = (max(0.0, seg * fill - dp(2)), b.height)

    def set_progress(self, v):
        self.progress = v
        self._bar_sync()

    def play(self):
        if self.art:
            self.art.opacity = 0
            self.art.pos_hint = {"center_x": .5, "center_y": .545}
            Animation(opacity=1, d=.34, t="out_quad").start(self.art)
            Animation(pos_hint={"center_x": .5, "center_y": .58},
                      d=.55, t="out_back").start(self.art)
        Animation(opacity=1, d=.30, t="out_quad").start(self.title)
        Animation(opacity=1, d=.30, t="out_quad").start(self.sub)
        a = Animation(progress=1.0, d=.75, t="in_out_quad")
        a.bind(on_progress=lambda *_: self._bar_sync())
        a.start(self)

    def finish(self):
        anim = Animation(opacity=0, d=.32, t="in_quad")
        anim.bind(on_complete=lambda *a: self.on_done and self.on_done())
        anim.start(self)


class HeungboApp(App):
    title = APP_NAME
    icon = asset("icon.png") or ""

    def build(self):
        Window.clearcolor = T.bg_bot
        try:
            Window.softinput_mode = "below_target"
        except Exception:
            pass
        install_crash_guard()
        if "font_scale" not in PREFS:
            PREFS["font_scale"] = UI.detect_system()
            save_prefs(PREFS)
        UI.apply(PREFS["font_scale"])
        # build() 안에서 바로 요청하면 액티비티가 준비 전이라 조용히 무시된다.
        if platform == "android":
            Clock.schedule_once(lambda *a: self._ask_permissions(), 1.2)
        # 카메라 모듈 확인은 느리므로 미리 백그라운드에서 끝내 둔다.
        threading.Thread(target=qr_available, daemon=True).start()
        # 저장된 총액형 당첨금을 1인당으로 되돌린다.
        try:
            DRAWS.drop_future()
            DRAWS.fix_prizes()
        except Exception as e:
            log_crash(e)
        self.holder = FloatLayout()
        self.root_w = None
        self.splash = Splash(on_done=self._drop_splash)
        self.holder.add_widget(self.splash)
        Window.bind(on_keyboard=self._on_key)
        Clock.schedule_once(lambda *a: self.splash.play(), 0.02)
        Clock.schedule_once(self._build_main, 0.06)
        return self.holder


    def _auto_sync(self, *a):
        """
        앱을 켤 때 빠진 최신 회차를 조용히 받아온다.
        내 번호 대조가 손을 대지 않아도 맞아 떨어지게 하려는 것이다.
        하루 한 번만 돈다.
        """
        import time as _t
        if _t.time() - float(PREFS.get("auto_sync_at") or 0) < 21600:
            return

        def work():
            try:
                resolve_latest_round()      # 서버에 실제 최신 회차를 확인
                miss = DRAWS.missing(8)
                if not miss:
                    return
                got = []
                for r in sorted(miss, reverse=True)[:8]:
                    row, _e = fetch_round(r, 2)
                    if row:
                        got.append(row)
                if got:
                    DRAWS.merge(got)
                PREFS["auto_sync_at"] = _t.time()
                save_prefs(PREFS)

                def fin(_dt):
                    rw = getattr(self, "root_w", None)
                    scr = getattr(rw, "screens", {}) or {}
                    for key in ("stat", "my"):
                        sc = scr.get(key)
                        if sc is not None and hasattr(sc, "on_pre_enter"):
                            try:
                                sc.on_pre_enter()
                            except Exception:
                                pass
                    toast("최신 회차를 받아 내 번호와 대조했습니다.")
                Clock.schedule_once(fin, 0)
            except Exception as e:
                log_crash(e)

        threading.Thread(target=work, daemon=True).start()

    # -- 시작 --------------------------------------------------
    def _build_main(self, *a):
        """무거운 위젯 생성은 스플래시가 떠 있는 동안 처리한다."""
        try:
            self.root_w = Root()
        except Exception as e:
            log_crash(e)
            self.root_w = BoxLayout()
            self.root_w.add_widget(lbl(
                "화면을 만드는 중 오류가 났습니다.\n"
                f"{DATA_DIR}/crash.log 를 확인해 주세요.",
                size=13, halign="center"))
        self.holder.add_widget(self.root_w, index=1)
        Clock.schedule_once(lambda *a: self._auto_sync(), 2.5)
        if platform == "android":
            self._bind_new_intent()
            Clock.schedule_once(lambda *b: self._open_from_intent(), 0.1)
        Clock.schedule_once(lambda *b: self.splash.finish(), 0.55)

    def _open_from_intent(self, *a):
        """위젯 버튼으로 열렸을 때 해당 탭으로 바로 이동."""
        if platform != "android" or not self.root_w:
            return
        try:
            from jnius import autoclass
            PythonActivity = autoclass("org.kivy.android.PythonActivity")
            it = PythonActivity.mActivity.getIntent()
            tab = it.getStringExtra("heungbo_tab") if it else None
            if tab and tab in self.root_w.screens:
                self.root_w.go(tab)
                it.removeExtra("heungbo_tab")
        except Exception as e:
            log_crash(e)

    def _bind_new_intent(self):
        try:
            from android import activity
            activity.bind(on_new_intent=lambda i: Clock.schedule_once(
                lambda *a: self._open_from_intent(), 0))
        except Exception:
            pass

    def _drop_splash(self, *a):
        if self.splash and self.splash.parent:
            self.holder.remove_widget(self.splash)
        self.splash = None
        gc.collect()

    def rebuild(self):
        """설정 변경 후 화면 전체를 다시 만든다."""
        UI.apply(PREFS.get("font_scale", "보통"))
        cur = self.root_w.sm.current if self.root_w else "gen"
        if self.root_w:
            self.holder.remove_widget(self.root_w)
        self.root_w = None
        gc.collect()
        self.root_w = Root()
        self.holder.add_widget(self.root_w)
        try:
            self.root_w.go(cur)
        except Exception:
            pass

    # -- 권한 --------------------------------------------------
    def _ask_permissions(self, *a):
        try:
            from android.permissions import request_permissions, Permission
            perms = []
            # INTERNET / ACCESS_NETWORK_STATE 는 설치 시 자동 허용되는 일반
            # 권한이라 목록에 넣으면 요청 전체가 통째로 무시된다.
            for name in ("ACCESS_COARSE_LOCATION", "ACCESS_FINE_LOCATION",
                         "CAMERA", "POST_NOTIFICATIONS"):
                if hasattr(Permission, name):
                    perms.append(getattr(Permission, name))
            if perms:
                request_permissions(perms)
        except Exception as e:
            log_crash(e)

    # -- 종료 --------------------------------------------------
    def _on_key(self, window, key, *a):
        if key != 27:
            return False
        if self.root_w is None:
            return True
        if self.root_w.sm.current != "gen":
            self.root_w.go("gen")
            return True
        self.ask_exit()
        return True

    def ask_exit(self):
        if getattr(self, "_exiting", None):
            return
        cnt, won = VAULT.spend_this_month()
        msg = (f"흥보가 기가막혀를 종료할까요?\n\n"
               f"이번 달 {cnt}게임 · {won:,}원\n"
               f"저장한 번호는 그대로 남습니다.")
        self._exiting = confirm(msg, self._quit, yes="종료", no="계속",
                                title="종료")
        self._exiting.bind(on_dismiss=lambda *a:
                           setattr(self, "_exiting", None))

    def _quit(self):
        self.save_all()
        toast("다음 회차에 또 뵙겠습니다.", title="흥보가 기가막혀")
        Clock.schedule_once(lambda *a: self.stop(), 0.9)

    # -- 수명주기 ----------------------------------------------
    def save_all(self):
        try:
            VAULT.save()
            save_prefs(PREFS)
            DRAWS.save()
        except Exception as e:
            log_crash(e)

    def on_pause(self):
        self.save_all()
        return True

    def on_resume(self):
        try:
            if self.root_w and self.root_w.sm.current == "gen":
                self.root_w.screens["gen"].refresh()
        except Exception as e:
            log_crash(e)
        return True

    def on_stop(self):
        self.save_all()


# ===============================================================
#  빌드 산출물 생성  (python lotto-4.py --spec / --widget)
# ===============================================================
SPEC = """[app]
title = 흥보가 기가막혀
package.name = heungbo
package.domain = org.heungbo
source.dir = .
source.include_exts = py,png,jpg,ttf,otf,json,xml
source.include_patterns = assets/*,assets/*.ttf,*.ttf
version = 1.0

requirements = python3,kivy==2.3.1,plyer,android,certifi,urllib3,pillow,camera4kivy,gestures4kivy,zbar,pyzbar

orientation = portrait
fullscreen = 0
icon.filename = assets/icon.png
presplash.filename = assets/presplash.png
android.presplash_color = #131519

# 갤럭시 = arm64. 구형 대비로 32비트도 같이 넣는다.
android.archs = arm64-v8a,armeabi-v7a

# 안드로이드 7.0(24) ~ 16(36)
android.api = 36
android.minapi = 24
android.ndk_api = 24

android.permissions = INTERNET,ACCESS_NETWORK_STATE,ACCESS_COARSE_LOCATION,ACCESS_FINE_LOCATION,CAMERA,POST_NOTIFICATIONS
android.allow_backup = True
android.enable_androidx = True

# camera4kivy 는 AndroidX CameraX 를 쓴다. 이 줄이 없으면 카메라가 안 잡힌다.
android.gradle_dependencies = androidx.camera:camera-core:1.2.3, androidx.camera:camera-camera2:1.2.3, androidx.camera:camera-lifecycle:1.2.3, androidx.camera:camera-video:1.2.3, androidx.camera:camera-view:1.2.3, androidx.camera:camera-extensions:1.2.3
android.wakelock = False

# HTTPS 만 쓰므로 평문 허용 안 함
android.manifest.intent_filters =

[buildozer]
log_level = 2
warn_on_root = 0
"""

WIDGET_JAVA = """package org.heungbo.heungbo;

import android.app.PendingIntent;
import android.appwidget.AppWidgetManager;
import android.appwidget.AppWidgetProvider;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.widget.RemoteViews;

/**
 * 홈 화면 위젯. 메뉴 버튼을 누르면 앱이 해당 탭으로 열린다.
 * 어떤 메뉴를 보일지는 설정 액티비티에서 고른다.
 */
public class HeungboWidget extends AppWidgetProvider {

    static final String[] KEYS = {"gen", "stat", "map", "qr", "my"};
    static final int[] BTN = {R.id.w_gen, R.id.w_stat, R.id.w_map,
                              R.id.w_qr, R.id.w_my};

    @Override
    public void onUpdate(Context ctx, AppWidgetManager mgr, int[] ids) {
        SharedPreferences sp =
            ctx.getSharedPreferences("heungbo_widget", Context.MODE_PRIVATE);
        for (int id : ids) {
            RemoteViews v = new RemoteViews(ctx.getPackageName(),
                                            R.layout.heungbo_widget);
            for (int i = 0; i < KEYS.length; i++) {
                boolean on = sp.getBoolean("menu_" + KEYS[i], true);
                v.setViewVisibility(BTN[i], on ? android.view.View.VISIBLE
                                               : android.view.View.GONE);
                Intent it = new Intent(ctx, org.kivy.android.PythonActivity.class);
                it.setAction(Intent.ACTION_MAIN);
                it.addCategory(Intent.CATEGORY_LAUNCHER);
                it.putExtra("heungbo_tab", KEYS[i]);
                it.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK
                            | Intent.FLAG_ACTIVITY_SINGLE_TOP);
                int flags = PendingIntent.FLAG_UPDATE_CURRENT;
                if (android.os.Build.VERSION.SDK_INT >= 23) {
                    flags |= PendingIntent.FLAG_IMMUTABLE;
                }
                PendingIntent pi = PendingIntent.getActivity(
                    ctx, id * 10 + i, it, flags);
                v.setOnClickPendingIntent(BTN[i], pi);
            }
            mgr.updateAppWidget(id, v);
        }
    }
}
"""

WIDGET_CONFIG_JAVA = """package org.heungbo.heungbo;

import android.app.Activity;
import android.appwidget.AppWidgetManager;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.LinearLayout;

/** 위젯을 놓을 때 뜨는 설정 화면. 보일 메뉴를 고른다. */
public class HeungboWidgetConfig extends Activity {

    int widgetId = AppWidgetManager.INVALID_APPWIDGET_ID;
    static final String[] KEYS = {"gen", "stat", "map", "qr", "my"};
    static final String[] LABELS = {"번호생성", "통계", "지역탐방", "QR확인", "내번호"};
    CheckBox[] boxes = new CheckBox[KEYS.length];

    @Override
    protected void onCreate(Bundle b) {
        super.onCreate(b);
        setResult(RESULT_CANCELED);
        Bundle ex = getIntent().getExtras();
        if (ex != null) {
            widgetId = ex.getInt(AppWidgetManager.EXTRA_APPWIDGET_ID,
                                 AppWidgetManager.INVALID_APPWIDGET_ID);
        }
        if (widgetId == AppWidgetManager.INVALID_APPWIDGET_ID) {
            finish();
            return;
        }
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setPadding(48, 48, 48, 48);
        SharedPreferences sp =
            getSharedPreferences("heungbo_widget", Context.MODE_PRIVATE);
        for (int i = 0; i < KEYS.length; i++) {
            boxes[i] = new CheckBox(this);
            boxes[i].setText(LABELS[i]);
            boxes[i].setChecked(sp.getBoolean("menu_" + KEYS[i], true));
            root.addView(boxes[i]);
        }
        Button ok = new Button(this);
        ok.setText("확인");
        ok.setOnClickListener(new View.OnClickListener() {
            public void onClick(View v) { save(); }
        });
        root.addView(ok);
        setContentView(root);
    }

    void save() {
        SharedPreferences.Editor e =
            getSharedPreferences("heungbo_widget", Context.MODE_PRIVATE).edit();
        for (int i = 0; i < KEYS.length; i++) {
            e.putBoolean("menu_" + KEYS[i], boxes[i].isChecked());
        }
        e.apply();
        AppWidgetManager mgr = AppWidgetManager.getInstance(this);
        new HeungboWidget().onUpdate(this, mgr, new int[]{widgetId});
        Intent r = new Intent();
        r.putExtra(AppWidgetManager.EXTRA_APPWIDGET_ID, widgetId);
        setResult(RESULT_OK, r);
        finish();
    }
}
"""

WIDGET_LAYOUT = """<?xml version="1.0" encoding="utf-8"?>
<LinearLayout xmlns:android="http://schemas.android.com/apk/res/android"
    android:layout_width="match_parent"
    android:layout_height="match_parent"
    android:orientation="vertical"
    android:background="#1B1F27"
    android:padding="12dp">

    <TextView
        android:layout_width="match_parent"
        android:layout_height="wrap_content"
        android:text="흥보가 기가막혀"
        android:textColor="#ECE6D8"
        android:textSize="16sp"
        android:textStyle="bold" />

    <LinearLayout
        android:layout_width="match_parent"
        android:layout_height="0dp"
        android:layout_weight="1"
        android:layout_marginTop="10dp"
        android:orientation="horizontal">

        <Button android:id="@+id/w_gen"  android:layout_width="0dp"
            android:layout_weight="1" android:layout_height="match_parent"
            android:text="생성"   android:textSize="12sp"
            android:textColor="#FFFFFF" android:background="#D4462B" />
        <Button android:id="@+id/w_stat" android:layout_width="0dp"
            android:layout_weight="1" android:layout_height="match_parent"
            android:text="통계"   android:textSize="12sp"
            android:textColor="#FFFFFF" android:background="#2F8C80" />
        <Button android:id="@+id/w_map"  android:layout_width="0dp"
            android:layout_weight="1" android:layout_height="match_parent"
            android:text="탐방"   android:textSize="12sp"
            android:textColor="#1B1F27" android:background="#E8B33D" />
        <Button android:id="@+id/w_qr"   android:layout_width="0dp"
            android:layout_weight="1" android:layout_height="match_parent"
            android:text="QR"     android:textSize="12sp"
            android:textColor="#FFFFFF" android:background="#8E3B6B" />
        <Button android:id="@+id/w_my"   android:layout_width="0dp"
            android:layout_weight="1" android:layout_height="match_parent"
            android:text="내번호" android:textSize="12sp"
            android:textColor="#FFFFFF" android:background="#3E6FB4" />
    </LinearLayout>
</LinearLayout>
"""

WIDGET_INFO = """<?xml version="1.0" encoding="utf-8"?>
<appwidget-provider xmlns:android="http://schemas.android.com/apk/res/android"
    android:minWidth="250dp"
    android:minHeight="110dp"
    android:targetCellWidth="4"
    android:targetCellHeight="2"
    android:updatePeriodMillis="1800000"
    android:initialLayout="@layout/heungbo_widget"
    android:configure="org.heungbo.heungbo.HeungboWidgetConfig"
    android:resizeMode="horizontal|vertical"
    android:widgetCategory="home_screen" />
"""

MANIFEST_APP = """<receiver
    android:name="org.heungbo.heungbo.HeungboWidget"
    android:exported="false">
    <intent-filter>
        <action android:name="android.appwidget.action.APPWIDGET_UPDATE" />
    </intent-filter>
    <meta-data
        android:name="android.appwidget.provider"
        android:resource="@xml/heungbo_widget_info" />
</receiver>
<activity
    android:name="org.heungbo.heungbo.HeungboWidgetConfig"
    android:exported="false">
    <intent-filter>
        <action android:name="android.appwidget.action.APPWIDGET_CONFIGURE" />
    </intent-filter>
</activity>
"""

WIDGET_SPEC_LINES = """
# ---- 홈 위젯 (선택) ----
# 반드시 기본 APK 가 정상 설치·실행된 뒤에 아래 3줄의 주석을 푸세요.
# buildozer 1.5 이상이 필요합니다.
#android.add_src = android/java
#android.add_resources = android/res
#android.extra_manifest_application_arguments = android/manifest_application.xml
"""


def _w(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print("  생성", os.path.relpath(path, HERE))


def write_spec(with_widget=False):
    spec = SPEC + (WIDGET_SPEC_LINES if with_widget else "")
    _w(os.path.join(HERE, "buildozer.spec"), spec)
    if with_widget:
        j = os.path.join(HERE, "android", "java", "org", "heungbo", "heungbo")
        _w(os.path.join(j, "HeungboWidget.java"), WIDGET_JAVA)
        _w(os.path.join(j, "HeungboWidgetConfig.java"), WIDGET_CONFIG_JAVA)
        r = os.path.join(HERE, "android", "res")
        _w(os.path.join(r, "layout", "heungbo_widget.xml"), WIDGET_LAYOUT)
        _w(os.path.join(r, "xml", "heungbo_widget_info.xml"), WIDGET_INFO)
        _w(os.path.join(HERE, "android", "manifest_application.xml"),
           MANIFEST_APP)
    print()
    print("다음 순서로 진행하세요.")
    print("  1) assets/icon.png, assets/presplash.png 확인")
    print("  2) assets/NanumGothic.ttf 가 있는지 반드시 확인 (없으면 한글이 전부 깨집니다)")
    print("  3) buildozer -v android debug")
    if with_widget:
        print("  4) 기본 APK 가 잘 돌아간 뒤에 buildozer.spec 아래쪽")
        print("     위젯 3줄 주석을 풀고 다시 빌드")


if __name__ == "__main__":
    if "--spec" in sys.argv or "--widget" in sys.argv:
        write_spec(with_widget="--widget" in sys.argv)
        sys.exit(0)
    print(f"── {APP_NAME} ──")
    print(f"보유 회차 {len(DRAWS.rows)}  ({DRAWS.oldest()}~{DRAWS.newest()})")
    print(f"오늘 기준 최신 회차 {latest_round_by_date()}")
    print(f"데이터 폴더 {DATA_DIR}")
    print(f"폰트 {FONT} / {FONT_D}  · 배율 {PREFS.get('font_scale', '보통')}")
    print(f"아이콘 {asset('icon.png') or '없음'}")
    HeungboApp().run()
