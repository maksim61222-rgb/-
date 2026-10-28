"""
Карта Европы с осадками (радар) на весь экран:
масштабирование, перетаскивание, пиксельный радар и шкала времени за 2 часа.

Для Thonny:
  1) Tools -> Manage packages... -> установить:  Pillow
  2) Открыть файл и нажать F5 (Run).
Нужен интернет.

Управление:
  Колесо мыши / двойной клик / + и -  - приблизить / отдалить
  Левая кнопка мыши (тянуть)          - двигать карту
  Пробел - пауза/старт,  <- / -> - кадр назад/вперёд
  H - вернуться к Европе
  A - сглаживание радара (анти-алиасинг) вкл/выкл
  S - инструмент выделения области: нарисуйте рамку мышью, и откроется
      окно с 3D-моделью облака (вращать - тянуть мышью, колесо - масштаб)
  F11 - полный экран вкл/выкл,  Esc - выйти из полного экрана,  Q - закрыть

Данные осадков: RainViewer (последние 2 часа, шаг 10 минут).
Подложка карты: OpenStreetMap.
"""

import io
import json
import math
import threading
import time
import tkinter as tk
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from tkinter import ttk
from urllib.request import Request, urlopen

from PIL import Image, ImageDraw, ImageTk
import random

# ---------------- Настройки ----------------
FRAME_DELAY_MS = 600       # скорость анимации
PIXEL_BLOCK = 4            # размер "пикселя" осадков на экране (1 = без укрупнения)
RADAR_COLOR = 2            # цветовая схема RainViewer
RADAR_OPTIONS = "0_1"      # сглаживание выключено (0), снег показывать (1)
ZMIN, ZMAX = 3, 9          # минимальный / максимальный масштаб
RADAR_MAXZ = 7             # максимальный масштаб данных радара (дальше - увеличение)
HOME_LONLAT = (14, 57)     # центр Европы
BAR_H = 56                 # высота нижней панели
# -------------------------------------------

API_URL = "https://api.rainviewer.com/public/weather-maps.json"
HEADERS = {"User-Agent": "EuropeRainMap/1.0 (Thonny learning project)"}
TILE = 256
RADAR_TILE = 512


def http_get(url):
    req = Request(url, headers=HEADERS)
    with urlopen(req, timeout=20) as resp:
        return resp.read()


def lonlat_to_px(lon, lat, z):
    """Координаты (lon, lat) -> пиксели мира на масштабе z."""
    world = TILE * 2 ** z
    x = (lon + 180) / 360 * world
    s = math.sin(math.radians(lat))
    y = (0.5 - math.log((1 + s) / (1 - s)) / (4 * math.pi)) * world
    return x, y


# =====================================================================
#            3D-модель облака по данным радара (выделенная область)
# =====================================================================
# Радар показывает только интенсивность осадков (dBZ) на плоскости, поэтому
# форма облака ОЦЕНИВАЕТСЯ: чем сильнее отражение, тем выше вертикальная
# колонна облака (слабый дождь - низкие слоистые облака, ливень/гроза -
# высокие кучево-дождевые башни).

GRID_MAX = 44              # сетка модели: до 44 ячеек по длинной стороне
MAX_PUFFS = 4500           # максимум "клубков" облака (скорость отрисовки)
CLOUD_BASE_KM = 1.0        # высота нижней границы облака, км
MIN_DBZ = 5                # слабее этого - считаем, что осадков нет
FETCH_MAX = 20             # сетка запроса облачности: до 20 точек по длинной стороне
CLOUD_API = "https://api.open-meteo.com/v1/forecast"

# Палитра RainViewer "Universal Blue" (с 2026 года единственная схема API).
# По цвету пикселя тайла восстанавливаем интенсивность в dBZ.
# Значения идут подряд, начиная с -10 dBZ, шаг 1 dBZ.
_RAIN_UB = (
    "63615914 66635a19 69665c1e 6c685d24 6f6b5f29 726e612e 75706234 78736439 "
    "7c75653e 7f786744 827b6949 857d6a4e 88806c54 8b826d59 8e856f5e "
    "92887164 9e93756e aa9e7978 b6a97e82 c2b4828c cec08796 d2c48ba0 d6c88faa "
    "dacc93b4 ded097be 88ddeeff 6cd1ebff 51c5e8ff 36bae5ff 1baee2ff "
    "00a3e0ff 009ad5ff 0091caff 0088bfff 007fb4ff 0077aaff 0070a3ff 00699cff "
    "006295ff 005b8eff 005588ff 005180ff 004e78ff 004a70ff 004768ff "
    "ffee00ff ffe000ff ffd200ff ffc500ff ffb700ff ffaa00ff ff9f00ff ff9500ff "
    "ff8b00ff ff8100ff ff4400ff f23600ff e62800ff d91b00ff cd0d00ff c10000ff "
    "a80000ff 8f0000ff 760000ff 5d0000ff ffaaffff ff9fffff ff95ffff ff8bffff "
    "ff81ffff ff77ffff ff6cffff ff62ffff ff58ffff ff4effff ffffffff")
_SNOW_UB = (
    "cfffff00 ceffff0c cdffff19 ccffff26 cbffff33 cbffff3f caffff4c c9ffff59 "
    "c8ffff66 c7ffff72 c7ffff7f c6ffff8c c5ffff99 c4ffffa5 c3ffffb2 "
    "c3ffffbf c2ffffcc c1ffffd8 c0ffffe5 bffffff2 bfffffff b8f8ffff b2f2ffff "
    "abebffff a5e5ffff 9fdfffff 98d8ffff 92d2ffff 8bcbffff 85c5ffff 7fbfffff "
    "78b8ffff 72b2ffff 6babffff 65a5ffff 5f9fffff 5b9bffff 5898ffff 5595ffff "
    "5292ffff 4f8fffff 4b8bffff 4888ffff 4585ffff 4282ffff 3f7fffff 3b7bffff "
    "3878ffff 3575ffff 3272ffff 2f6fffff 2b6bffff 2868ffff 2565ffff 2262ffff "
    "1f5fffff 1b5bffff 1858ffff 1555ffff 1252ffff 0f4fffff 0c4bffff 0948ffff "
    "0645ffff 0242ffff 003fffff 003bffff 0038ffff 0035ffff 0032ffff 002fffff "
    "002bffff 0028ffff 0025ffff 0022ffff 001fffff 001bffff 0018ffff 0015ffff "
    "0012ffff 000fffff 000cffff 0009ffff 0006ffff 0002ffff 0000ffff")

_PALETTE = []
_COLOR_CACHE = {}


def _init_palette():
    for lst in (_RAIN_UB, _SNOW_UB):
        for i, h in enumerate(lst.split()):
            c = (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16), int(h[6:8], 16))
            _PALETTE.append((c, -10 + i))
            _COLOR_CACHE.setdefault(c, -10 + i)


_init_palette()


def color_to_dbz(px):
    """Цвет пикселя радара (R, G, B, A) -> dBZ, либо None, если данных нет."""
    if px in _COLOR_CACHE:
        return _COLOR_CACHE[px]
    res = None
    if px[3] >= 8:
        bd = 1e12
        for c, d in _PALETTE:
            dist = ((c[0] - px[0]) ** 2 + (c[1] - px[1]) ** 2 +
                    (c[2] - px[2]) ** 2 + (c[3] - px[3]) ** 2)
            if dist < bd:
                bd, res = dist, d
    _COLOR_CACHE[px] = res
    return res


def extract_grid(radar, gw, gh):
    """Радарная картинка области -> сетка (покрытие 0..1, средний dBZ)."""
    rw, rh = radar.size
    ss = 3 if (rw >= gw * 3 and rh >= gh * 3) else 1
    small = radar.resize((gw * ss, gh * ss), Image.NEAREST)   # цвета не смешиваем
    data = list(small.getdata())
    stride = gw * ss
    n = ss * ss
    cover = [[0.0] * gw for _ in range(gh)]
    val = [[0.0] * gw for _ in range(gh)]
    for gy in range(gh):
        for gx in range(gw):
            tot = cnt = 0
            for dy in range(ss):
                base = (gy * ss + dy) * stride + gx * ss
                for dx in range(ss):
                    d = color_to_dbz(data[base + dx])
                    if d is not None and d >= MIN_DBZ:
                        tot += d
                        cnt += 1
            if cnt:
                cover[gy][gx] = cnt / n
                val[gy][gx] = tot / cnt
    return cover, val


def blur3(g, gw, gh):
    k = ((1, 2, 1), (2, 4, 2), (1, 2, 1))
    out = [[0.0] * gw for _ in range(gh)]
    for y in range(gh):
        for x in range(gw):
            s = w = 0.0
            for dy in (-1, 0, 1):
                yy = y + dy
                if 0 <= yy < gh:
                    for dx in (-1, 0, 1):
                        xx = x + dx
                        if 0 <= xx < gw:
                            ww = k[dy + 1][dx + 1]
                            s += g[yy][xx] * ww
                            w += ww
            out[y][x] = s / w
    return out


def smoothstep(t):
    t = min(max(t, 0.0), 1.0)
    return t * t * (3 - 2 * t)


def persp_coeffs(dst, src):
    """Коэффициенты для Image.transform(PERSPECTIVE): точки dst -> точки src."""
    a, b = [], []
    for (X, Y), (u, v) in zip(dst, src):
        a.append([X, Y, 1, 0, 0, 0, -X * u, -Y * u]); b.append(u)
        a.append([0, 0, 0, X, Y, 1, -X * v, -Y * v]); b.append(v)
    n = 8
    for i in range(n):                               # метод Гаусса
        p = max(range(i, n), key=lambda r: abs(a[r][i]))
        if abs(a[p][i]) < 1e-12:
            raise ZeroDivisionError("вырожденная проекция")
        a[i], a[p] = a[p], a[i]
        b[i], b[p] = b[p], b[i]
        for r in range(i + 1, n):
            f = a[r][i] / a[i][i]
            for c in range(i, n):
                a[r][c] -= f * a[i][c]
            b[r] -= f * b[i]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = (b[i] - sum(a[i][j] * x[j] for j in range(i + 1, n))) / a[i][i]
    return x


class CloudModel:
    """Строит облако из радарной картинки и рисует его (только Pillow)."""

    def __init__(self, radar, ground, km_w, km_h, layers=None):
        self.L = max(km_w, km_h, 1e-6)
        self.Wn, self.Hn = km_w / self.L, km_h / self.L
        rw, rh = radar.size
        self.layers = layers          # (gw, gh, низкие, средние, высокие) в %
        if layers:
            self.gw, self.gh = layers[0], layers[1]
        else:
            cell = max(rw, rh) / GRID_MAX
            self.gw = max(2, min(rw, round(rw / cell)))
            self.gh = max(2, min(rh, round(rh / cell)))
        gw, gh = self.gw, self.gh

        cover, val = extract_grid(radar, gw, gh)
        self.max_dbz = max((max(r) for r in val), default=0.0)
        dens = blur3(cover, gw, gh)
        wv = blur3([[cover[y][x] * val[y][x] for x in range(gw)]
                    for y in range(gh)], gw, gh)

        rng = random.Random(7)
        self.cells = []
        for y in range(gh):
            for x in range(gw):
                d = dens[y][x]
                if d < 0.22:
                    continue
                v = wv[y][x] / d
                e = smoothstep((d - 0.22) / 0.55)          # скругляем края
                thick = ((1.5 + 0.2 * min(v, 60.0)) * (0.35 + 0.65 * e)
                         * (0.88 + 0.24 * rng.random()))
                self.cells.append((x, y, v, thick))
        self.has_cloud = bool(self.cells)
        self.max_top_km = (CLOUD_BASE_KM + max(c[3] for c in self.cells)
                           if self.has_cloud else 0.0)
        if layers:
            # радар: грозовые колонны (>=20 dBZ) и затемнение облаков с дождём
            self.storm = {(c[0], c[1]): (c[2], c[3])
                          for c in self.cells if c[2] >= 20}
            self.rain = [[val[y][x] if cover[y][x] >= 0.3 else 0.0
                          for x in range(gw)] for y in range(gh)]

            def anyc(g):
                return any(v >= 10 for r in g for v in r)
            self.has_cloud = (anyc(layers[2]) or anyc(layers[3])
                              or anyc(layers[4]) or bool(self.storm))
            top = 0.0
            for g, z in ((layers[2], 3.0), (layers[3], 7.5), (layers[4], 10.5)):
                if anyc(g):
                    top = z
            if self.storm:
                top = max(top, CLOUD_BASE_KM + max(t for _, t in self.storm.values()))
            self.max_top_km = top

        # --- земля: карта + тень от облака ---
        tw, th = ground.size
        k = 640.0 / max(tw, th)
        size = (max(2, int(tw * k)), max(2, int(th * k)))
        tex = ground.resize(size, Image.LANCZOS if k < 1 else Image.BICUBIC)
        if layers:
            def total(x, y):
                c = 1.0
                for g in layers[2:5]:
                    c *= 1 - g[y][x] / 100.0
                return 1 - c
            shade = [[total(x, y) for x in range(gw)] for y in range(gh)]
        else:
            shade = [[dens[y][x] * 1.3 for x in range(gw)] for y in range(gh)]
        sh = Image.new("L", (gw, gh))
        sh.putdata([int(min(1.0, shade[y][x]) * 255)
                    for y in range(gh) for x in range(gw)])
        sh = sh.resize(size, Image.BICUBIC).point(lambda v: int(v * 0.6))
        dark = tex.point(lambda v: int(v * 0.45))
        self.tex = Image.composite(dark, tex, sh)
        self.gmask = Image.new("L", size, 255)

        # --- спрайт мягкого "клубка" ---
        S = 128
        m = Image.new("L", (S, S))
        px = []
        for j in range(S):
            for i in range(S):
                r2 = ((i + 0.5 - S / 2) ** 2 + (j + 0.5 - S / 2) ** 2) / (S / 2) ** 2
                px.append(int(255 * 0.8 * (1 - r2) ** 1.4) if r2 < 1 else 0)
        m.putdata(px)
        self._base_mask = m
        self._thin_mask = m.point(lambda v: int(v * 0.5))   # тонкие перистые
        self._masks = {}
        self._sky_cache = None
        self.puffs, self.puffs_fast = [], []
        self.exag = 1

    # ---------- вертикальный масштаб ----------
    def auto_exag(self):
        """Во сколько раз растянуть высоту, чтобы облако было хорошо видно."""
        return 1          # реальные пропорции, без растяжения по высоте

    def build_puffs(self, exag):
        if self.layers:
            return self._build_layered(exag)
        self.exag = exag
        L, gw = self.L, self.gw
        cell_n = self.Wn / gw
        rk = 1.0
        while True:                       # подбираем размер клубков под лимит
            r = cell_n * 0.85 * rk
            plan = [max(1, min(12, int(round(c[3] / L * exag / (r * 0.9)))))
                    for c in self.cells]
            if sum(plan) <= MAX_PUFFS or rk > 8:
                break
            rk *= 1.2
        rng = random.Random(11)
        base_n = CLOUD_BASE_KM / L * exag
        self.puffs, self.puffs_fast = [], []
        for (gx, gy, v, thick), n in zip(self.cells, plan):
            cx = ((gx + 0.5) / self.gw - 0.5) * self.Wn
            cy = (0.5 - (gy + 0.5) / self.gh) * self.Hn
            tn = thick / L * exag
            dark = min(1.0, max(0.0, (v - 15) / 45.0))     # сильный дождь - темнее
            for k in range(n):
                t = (k + 0.5) / n
                x = cx + (rng.random() - 0.5) * cell_n * 0.9
                y = cy + (rng.random() - 0.5) * cell_n * 0.9
                z = base_n + t * tn + (rng.random() - 0.5) * tn / n * 0.5
                pr = r * (0.85 + 0.4 * rng.random()) * (1 + 0.3 * t)
                light = (0.58 + 0.42 * t) * (1 - 0.4 * dark) * (0.95 + 0.1 * rng.random())
                col = (min(255, int(246 * light)), min(255, int(248 * light)),
                       min(255, int(255 * light)))
                q = min(1.0, tn / n * 0.65 / pr)     # сплюснутость по высоте
                self.puffs.append((x, y, z, pr, col, False, q))
                if k % 2 == 0:
                    self.puffs_fast.append((x, y, z, pr * 1.3, col, False, q / 1.3))
        self.top_n = self.max_top_km / L * exag

    # ---------- облака по реальной облачности (3 слоя высоты) ----------
    @staticmethod
    def _bilin(g, gw, gh, fx, fy):
        x = min(max(fx, 0.0), gw - 1.0)
        y = min(max(fy, 0.0), gh - 1.0)
        x0, y0 = int(x), int(y)
        x1, y1 = min(x0 + 1, gw - 1), min(y0 + 1, gh - 1)
        tx, ty = x - x0, y - y0
        a = g[y0][x0] * (1 - tx) + g[y0][x1] * tx
        b = g[y1][x0] * (1 - tx) + g[y1][x1] * tx
        return a * (1 - ty) + b * ty

    def _build_layered(self, exag):
        self.exag = exag
        L, gw, gh = self.L, self.gw, self.gh
        cell_n = self.Wn / gw
        rng = random.Random(11)
        lo, mi, hi = self.layers[2:5]
        # имя, сетка %, низ км, верх км, уровней, коэф. размера, тонкие, яркость
        spec = (("low", lo, 0.8, 3.0, 2, 1.0, False, (0.60, 0.40)),
                ("mid", mi, 3.5, 7.5, 2, 0.9, False, (0.78, 0.22)),
                ("high", hi, 8.5, 10.5, 1, 1.25, True, (0.97, 0.03)))
        raw = []
        subs = {"low": 2, "mid": 2, "high": 2}     # клубков на ячейку: 2x2
        for gy in range(gh):
            for gx in range(gw):
                v = self.rain[gy][gx]
                dark = min(1.0, max(0.0, (v - 15) / 45.0))
                storm = self.storm.get((gx, gy))
                for name, g, z0, z1, nl, rf, thin, (l0, l1) in spec:
                    m = subs[name]
                    for sy in range(m):
                        for sx in range(m):
                            ox, oy = (sx + 0.5) / m - 0.5, (sy + 0.5) / m - 0.5
                            c = self._bilin(g, gw, gh, gx + ox, gy + oy) / 100.0
                            z1e = z1
                            if name == "low" and storm:     # гроза: башня до радарной высоты
                                c, z1e = 1.0, CLOUD_BASE_KM + storm[1]
                            if rng.random() >= smoothstep((c - 0.08) / 0.7):
                                continue
                            cx = ((gx + 0.5 + ox) / gw - 0.5) * self.Wn
                            cy = (0.5 - (gy + 0.5 + oy) / gh) * self.Hn
                            span = (z1e - z0) * (0.55 + 0.45 * c)
                            r = cell_n / m * 0.6 * rf * (0.65 + 0.55 * c)
                            n = max(nl, min(10, int(round(span / L * exag / (r * 1.1)))))
                            for k in range(n):
                                t = (k + 0.5) / n
                                z = (z0 + t * span) / L * exag
                                z += (rng.random() - 0.5) * span / L * exag / n * 0.5
                                x = cx + (rng.random() - 0.5) * cell_n / m * 0.8
                                y = cy + (rng.random() - 0.5) * cell_n / m * 0.8
                                pr = r * (0.85 + 0.4 * rng.random()) * (1 + 0.25 * t)
                                light = l0 + l1 * t
                                if not thin:
                                    light *= 1 - 0.4 * dark
                                light *= 0.95 + 0.1 * rng.random()
                                col = (min(255, int(246 * light)), min(255, int(248 * light)),
                                       min(255, int(255 * light)))
                                q = min(1.0, span / L * exag / n * 0.65 / pr)
                                raw.append((x, y, z, pr, col, thin, q))
        if len(raw) > MAX_PUFFS:
            f = min(2.2, (len(raw) / MAX_PUFFS) ** 0.5)
            raw = [(x, y, z, pr * f, col, th, q / f)
                   for (x, y, z, pr, col, th, q) in rng.sample(raw, MAX_PUFFS)]
        self.puffs = raw
        self.puffs_fast = [(x, y, z, pr * 1.3, col, th, q / 1.3)
                           for (x, y, z, pr, col, th, q) in raw[::2]]
        self.top_n = self.max_top_km / L * exag

    # ---------- рисование ----------
    def _sky(self, W, H):
        if self._sky_cache and self._sky_cache[0] == (W, H):
            return self._sky_cache[1]
        img = Image.new("RGB", (W, H))
        d = ImageDraw.Draw(img)
        top, bot = (20, 44, 92), (150, 190, 228)
        for y in range(H):
            t = y / max(1, H - 1)
            d.line([(0, y), (W, y)], fill=tuple(int(top[i] + (bot[i] - top[i]) * t)
                                                 for i in range(3)))
        self._sky_cache = ((W, H), img)
        return img

    def _mask(self, dw, dh, thin=False):
        m = self._masks.get((dw, dh, thin))
        if m is None:
            if len(self._masks) > 1500:
                self._masks.clear()
            src = self._thin_mask if thin else self._base_mask
            m = src.resize((dw, dh), Image.BILINEAR)
            self._masks[(dw, dh, thin)] = m
        return m

    def render(self, W, H, yaw, pitch, zoom=1.0, fast=False):
        img = self._sky(W, H).copy()
        a, p = math.radians(yaw), math.radians(pitch)
        ca, sa, cp, sp = math.cos(a), math.sin(a), math.cos(p), math.sin(p)
        D = 2.3
        F = 1.7 * zoom * min(W, H * 1.25)
        zt = 0.38 * getattr(self, "top_n", 0.0)
        mx, my = W / 2, H * 0.55

        def proj(x, y, z):
            x1 = x * ca - y * sa
            y1 = x * sa + y * ca
            zz = z - zt
            dd = y1 * cp - zz * sp
            up = y1 * sp + zz * cp
            k = F / (D + dd)
            return mx + x1 * k, my - up * k, dd, k

        # --- земля (карта в перспективе) ---
        hw, hh = self.Wn / 2, self.Hn / 2
        corners = [(-hw, hh), (hw, hh), (hw, -hh), (-hw, -hh)]
        sp_pts = [proj(x, y, 0)[:2] for x, y in corners]
        try:
            xs = [q[0] for q in sp_pts]
            ys = [q[1] for q in sp_pts]
            bx0, by0 = max(0, int(min(xs))), max(0, int(min(ys)))
            bx1, by1 = min(W, int(max(xs)) + 1), min(H, int(max(ys)) + 1)
            if bx1 > bx0 and by1 > by0:
                tw, th = self.tex.size
                co = persp_coeffs([(qx - bx0, qy - by0) for qx, qy in sp_pts],
                                  [(0, 0), (tw, 0), (tw, th), (0, th)])
                size = (bx1 - bx0, by1 - by0)
                warped = self.tex.transform(size, Image.PERSPECTIVE, co, Image.BILINEAR)
                mk = self.gmask.transform(size, Image.PERSPECTIVE, co, Image.BILINEAR)
                img.paste(warped, (bx0, by0), mk)
        except ZeroDivisionError:
            pass
        dr = ImageDraw.Draw(img)
        dr.line(sp_pts + [sp_pts[0]], fill=(255, 255, 255), width=2)
        nx, ny = proj(0, hh + 0.05, 0)[:2]
        dr.text((nx - 3, ny - 6), "N", fill=(255, 255, 255))

        # --- облако: клубки от дальних к ближним ---
        items = []
        for (x, y, z, r, col, thin, q) in (self.puffs_fast if fast else self.puffs):
            x1 = x * ca - y * sa
            y1 = x * sa + y * ca
            zz = z - zt
            dd = y1 * cp - zz * sp
            up = y1 * sp + zz * cp
            k = F / (D + dd)
            items.append((dd, mx + x1 * k, my - up * k, r * k, col, thin, q))
        items.sort(key=lambda it: it[0], reverse=True)
        for _, sx, sy, rr, col, thin, q in items:
            dw = int(2 * rr)                     # клубок - сплюснутый эллипсоид
            dh = int(2 * math.hypot(rr * sp, rr * q * cp))
            if dw < 3 or dh < 2:
                continue
            dw, dh = min(dw, 500), min(dh, 500)
            dw += dw & 1
            dh += dh & 1
            x0, y0 = int(sx - dw / 2), int(sy - dh / 2)
            if x0 >= W or y0 >= H or x0 + dw <= 0 or y0 + dh <= 0:
                continue
            m = self._mask(dw, dh, thin)
            if x0 < 0 or y0 < 0 or x0 + dw > W or y0 + dh > H:
                cx0, cy0 = max(0, -x0), max(0, -y0)
                cx1, cy1 = dw - max(0, x0 + dw - W), dh - max(0, y0 + dh - H)
                m = m.crop((cx0, cy0, cx1, cy1))
                box = (x0 + cx0, y0 + cy0, x0 + cx1, y0 + cy1)
            else:
                box = (x0, y0, x0 + dw, y0 + dh)
            img.paste(col, box, m)
        return img


class CloudWindow:
    """Окно с вращаемой 3D-моделью облака для выделенной области."""

    def __init__(self, app, spec, ground):
        self.app, self.spec, self.ground = app, spec, ground
        self.alive = True
        self.model = None
        self.yaw, self.pitch, self.zoom = -28.0, 30.0, 1.0
        self.drag = None
        self.job = None
        self.want_fast = False
        self.photo = None
        self.t0 = time.time()

        # какие тайлы радара нужны для выбранной области
        rz, s = spec["rz"], spec["s"]
        n = 2 ** rz
        x0, y0, x1, y1 = spec["box"]
        wx0, wy0 = spec["left"] + x0, spec["top"] + y0
        wx1, wy1 = spec["left"] + x1, spec["top"] + y1
        tx0, tx1 = max(0, wx0 // s), min(n - 1, (wx1 - 1) // s)
        ty0, ty1 = max(0, wy0 // s), min(n - 1, (wy1 - 1) // s)
        self.keys = [("r", spec["index"], rz, x, y)
                     for y in range(ty0, ty1 + 1) for x in range(tx0, tx1 + 1)]
        self.fetch_done, self.fetch_err, self.fetch_result = False, None, None
        self.start_fetch()

        top = self.top = tk.Toplevel(app.root)
        top.title("3D-модель облака - выбранная область")
        top.configure(bg="#0b1220")
        sw, sh = top.winfo_screenwidth(), top.winfo_screenheight()
        self.W = max(500, min(1000, sw - 120))
        self.H = max(400, min(680, sh - 220))
        top.geometry(f"{self.W}x{self.H + 50}+{(sw - self.W) // 2}"
                     f"+{max(0, (sh - self.H - 50) // 4)}")

        bar = ttk.Frame(top, height=50)
        bar.pack(side="bottom", fill="x")
        bar.pack_propagate(False)
        self.auto = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="Вращение", variable=self.auto
                        ).pack(side="left", padx=(12, 12))
        ttk.Button(bar, text="Сбросить вид", command=self.reset_view
                   ).pack(side="left", padx=4)
        ttk.Button(bar, text="Закрыть", command=self.close
                   ).pack(side="right", padx=10)

        self.canvas = tk.Canvas(top, width=self.W, height=self.H, bg="#0b1220",
                                highlightthickness=0, cursor="fleur")
        self.canvas.pack(fill="both", expand=True)
        c = self.canvas
        self.img_id = c.create_image(0, 0, anchor="nw")
        self.status_id = c.create_text(self.W // 2, self.H // 2, fill="white",
                                       font=("Arial", 16),
                                       text="Загрузка радарных данных...")
        self.info1 = self._label(14, 12, ("Arial", 13, "bold"), "nw")
        self.info2 = self._label(14, 34, ("Arial", 11), "nw")
        self.hint = self._label(12, self.H - 8, ("Arial", 10), "sw")
        self._set(self.hint, "Тянуть мышью - вращать | колесо - приблизить | R - сбросить вид | "
                             "Esc - закрыть.  Высоты облака оценочные: радар показывает "
                             "осадки, а не форму облака.")

        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_motion)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<MouseWheel>", lambda e: self.zoom_by(1.12 if e.delta > 0 else 1 / 1.12))
        c.bind("<Button-4>", lambda e: self.zoom_by(1.12))
        c.bind("<Button-5>", lambda e: self.zoom_by(1 / 1.12))
        c.bind("<Configure>", self.on_configure)
        top.bind("<Escape>", lambda e: self.close())
        top.bind("<r>", lambda e: self.reset_view())
        top.bind("<Destroy>", self.on_destroy)
        top.protocol("WM_DELETE_WINDOW", self.close)

        # окно должно появиться поверх полноэкранной карты
        top.lift()
        top.attributes("-topmost", True)
        top.after(400, lambda: self.alive and top.attributes("-topmost", False))
        top.focus_force()

        self.wait_data()
        top.after(60, self.spin)

    # ---------- реальная облачность (Open-Meteo) ----------
    def start_fetch(self):
        spec = self.spec
        x0, y0, x1, y1 = spec["box"]
        rw, rh = x1 - x0, y1 - y0
        cell = max(rw, rh) / FETCH_MAX
        self.fgw = max(2, min(rw, round(rw / cell)))
        self.fgh = max(2, min(rh, round(rh / cell)))
        world = TILE * 2 ** spec["z"]
        wx0, wy0 = spec["left"] + x0, spec["top"] + y0
        lats, lons = [], []
        for gy in range(self.fgh):
            for gx in range(self.fgw):
                wx = wx0 + (gx + 0.5) / self.fgw * rw
                wy = wy0 + (gy + 0.5) / self.fgh * rh
                lons.append(round(wx / world * 360 - 180, 3))
                lats.append(round(math.degrees(
                    math.atan(math.sinh(math.pi * (1 - 2 * wy / world)))), 3))
        self.app.pool.submit(self._fetch, lats, lons)

    def _fetch(self, lats, lons):      # работает в фоновом потоке
        try:
            lo, mi, hi, t = [], [], [], None
            for i in range(0, len(lats), 100):
                url = (f"{CLOUD_API}?latitude={','.join(map(str, lats[i:i + 100]))}"
                       f"&longitude={','.join(map(str, lons[i:i + 100]))}"
                       "&current=cloud_cover_low,cloud_cover_mid,cloud_cover_high"
                       "&timeformat=unixtime")
                data = json.loads(http_get(url))
                if isinstance(data, dict):
                    data = [data]
                for d in data:
                    cur = d["current"]
                    lo.append(float(cur["cloud_cover_low"] or 0))
                    mi.append(float(cur["cloud_cover_mid"] or 0))
                    hi.append(float(cur["cloud_cover_high"] or 0))
                    t = t or cur.get("time")
            if len(lo) != len(lats):
                raise ValueError("неполный ответ сервера")
            self.fetch_result = (lo, mi, hi, t)
        except Exception as ex:
            self.fetch_err = str(ex)
        self.fetch_done = True

    # ---------- подписи с тенью ----------
    def _label(self, x, y, font, anchor):
        c = self.canvas
        sh = c.create_text(x + 1, y + 1, anchor=anchor, fill="black", font=font)
        tx = c.create_text(x, y, anchor=anchor, fill="white", font=font)
        return (sh, tx)

    def _set(self, label, text):
        for i in label:
            self.canvas.itemconfig(i, text=text)

    # ---------- данные ----------
    def wait_data(self):
        if not self.alive:
            return
        app = self.app
        missing = [k for k in self.keys if k not in app.raw]
        el = time.time() - self.t0
        if (missing and el < 25) or (not self.fetch_done and el < 30):
            for k in missing:
                app.ensure(k)
            self.canvas.itemconfig(
                self.status_id,
                text="Загрузка данных об облачности и радара... "
                     f"радар {len(self.keys) - len(missing)}/{len(self.keys)}")
            self.top.after(250, self.wait_data)
            return
        self.build()

    def build(self):
        app, spec = self.app, self.spec
        x0, y0, x1, y1 = spec["box"]
        rw, rh = x1 - x0, y1 - y0
        s = spec["s"]
        wx0, wy0 = spec["left"] + x0, spec["top"] + y0
        try:
            radar = Image.new("RGBA", (rw, rh), (0, 0, 0, 0))
            for key in self.keys:
                tile = app.decode(key)
                if tile is None:
                    continue
                if tile.size != (s, s):
                    tile = tile.resize((s, s), Image.NEAREST)   # точные цвета
                _, _, _, tx, ty = key
                radar.paste(tile, (tx * s - wx0, ty * s - wy0))
            # реальные размеры области в километрах
            world = TILE * 2 ** spec["z"]
            yc = wy0 + rh / 2
            lat = math.degrees(math.atan(math.sinh(math.pi * (1 - 2 * yc / world))))
            km_px = 40075.017 * math.cos(math.radians(lat)) / world
            layers = None
            if self.fetch_done and self.fetch_result:
                lo, mi, hi, self.cloud_time = self.fetch_result
                n = self.fgw
                grid = lambda a: [a[r * n:(r + 1) * n] for r in range(self.fgh)]
                layers = (self.fgw, self.fgh, grid(lo), grid(mi), grid(hi))
            self.layered = layers is not None
            self.model = CloudModel(radar, self.ground, rw * km_px, rh * km_px, layers)
            exag = self.model.auto_exag()
            self.model.build_puffs(exag)
        except Exception as ex:
            self.canvas.itemconfig(self.status_id, text=f"Ошибка построения модели: {ex}")
            return
        m = self.model
        self.canvas.itemconfig(self.status_id, text="")
        t = datetime.fromtimestamp(self.spec["time"]).strftime("%H:%M")
        self.size_txt = f"Область {rw * km_px:.0f} x {rh * km_px:.0f} км"
        if self.layered:
            tc = (datetime.fromtimestamp(self.cloud_time).strftime("%H:%M")
                  if self.cloud_time else "сейчас")
            if m.has_cloud:
                self._set(self.info1, f"{self.size_txt}  |  облачность на {tc}  |  "
                                      f"радар {t}  |  верх до ~{m.max_top_km:.0f} км")
            else:
                self._set(self.info1, f"{self.size_txt}  |  на {tc} в этой области ясно - облаков нет")
            self._set(self.hint,
                      "Тянуть мышью - вращать | колесо - приблизить | R - сброс | Esc - закрыть.  "
                      "Облака: Open-Meteo (погодная модель, не снимок спутника); "
                      "тёмные - зоны осадков по радару.")
            self._set(self.info2, self.line2(exag))
            self.redraw()
            return
        err = f" (облачность недоступна: {self.fetch_err})" if self.fetch_err else ""
        self._set(self.hint, "Тянуть мышью - вращать | колесо - приблизить | R - сброс | "
                             "Esc - закрыть.  Нет данных об облачности - форма облака "
                             "оценена по радару осадков." + err)
        if m.has_cloud:
            self._set(self.info1,
                      f"Область {rw * km_px:.0f} x {rh * km_px:.0f} км  |  радар {t}  |  "
                      f"макс. {m.max_dbz:.0f} dBZ  |  верх облака до ~{m.max_top_km:.0f} км")
        else:
            self._set(self.info1, f"Область {rw * km_px:.0f} x {rh * km_px:.0f} км  |  радар {t}  |  "
                                  "в этой области радар не видит осадков - облака нет")
        self._set(self.info2, self.line2(exag))
        self.redraw()

    def line2(self, exag):
        if getattr(self, "layered", False):
            return "Слои: низкие до 3 км, средние 3-8 км, высокие выше 8 км  |  высота в реальном масштабе"
        return "Высота в реальном масштабе"

    # ---------- отрисовка ----------
    def redraw(self, fast=False):
        if not (self.alive and self.model):
            return
        img = self.model.render(self.W, self.H, self.yaw, self.pitch, self.zoom, fast)
        self.photo = ImageTk.PhotoImage(img)
        self.canvas.itemconfig(self.img_id, image=self.photo)

    def request(self, fast=False):
        self.want_fast = fast
        if self.job is None and self.alive:
            self.job = self.top.after(15, self._run)

    def _run(self):
        self.job = None
        self.redraw(self.want_fast)

    def spin(self):
        if not self.alive:
            return
        if self.auto.get() and not self.drag and self.model:
            self.yaw += 2.0
            self.redraw()
        self.top.after(50, self.spin)

    # ---------- управление ----------
    def on_press(self, e):
        self.drag = (e.x, e.y, self.yaw, self.pitch)

    def on_motion(self, e):
        if not self.drag:
            return
        sx, sy, y0, p0 = self.drag
        self.yaw = y0 + (e.x - sx) * 0.45
        self.pitch = min(max(p0 + (e.y - sy) * 0.35, 8.0), 88.0)
        self.request(fast=True)

    def on_release(self, e):
        self.drag = None
        self.request(fast=False)

    def zoom_by(self, f):
        self.zoom = min(max(self.zoom * f, 0.4), 12.0)
        self.request(fast=False)

    def reset_view(self):
        self.yaw, self.pitch, self.zoom = -28.0, 30.0, 1.0
        self.request(fast=False)

    def on_configure(self, e):
        if e.width < 100 or e.height < 100:
            return
        if (e.width, e.height) != (self.W, self.H):
            self.W, self.H = e.width, e.height
            self.canvas.coords(self.status_id, self.W // 2, self.H // 2)
            self.canvas.coords(self.hint[0], 13, self.H - 7)
            self.canvas.coords(self.hint[1], 12, self.H - 8)
            self.request(fast=False)

    def on_destroy(self, e):
        if e.widget is self.top:
            self.alive = False

    def close(self):
        self.alive = False
        try:
            self.top.destroy()
        except tk.TclError:
            pass


class RainApp:
    def __init__(self, root):
        self.root = root
        root.title("Осадки в Европе - последние 2 часа")
        root.configure(bg="black")
        self.fullscreen = True
        root.attributes("-fullscreen", True)

        self.aw = root.winfo_screenwidth()
        self.ah = root.winfo_screenheight() - BAR_H

        self.canvas = tk.Canvas(root, width=self.aw, height=self.ah,
                                bg="black", highlightthickness=0, cursor="fleur")
        self.canvas.pack()
        self.status_id = self.canvas.create_text(
            self.aw // 2, self.ah // 2, text="Загрузка данных...",
            fill="white", font=("Arial", 20))

        bar = ttk.Frame(root, height=BAR_H)
        bar.pack(fill="x")
        bar.pack_propagate(False)
        self.play_btn = ttk.Button(bar, text="Пауза", command=self.toggle_play)
        self.play_btn.pack(side="left", padx=(10, 4), pady=10)
        ttk.Button(bar, text="−", width=3,
                   command=lambda: self.zoom_at(self.aw / 2, self.ah / 2, -1)
                   ).pack(side="left", padx=2)
        ttk.Button(bar, text="+", width=3,
                   command=lambda: self.zoom_at(self.aw / 2, self.ah / 2, 1)
                   ).pack(side="left", padx=2)
        ttk.Button(bar, text="Европа", command=self.go_home
                   ).pack(side="left", padx=(2, 8))
        self.smooth_btn = ttk.Button(bar, text="Сглаживание: выкл",
                                     command=self.toggle_smooth)
        self.smooth_btn.pack(side="left", padx=2)
        self.select_btn = ttk.Button(bar, text="Выделить область",
                                     command=self.toggle_select)
        self.select_btn.pack(side="left", padx=(2, 8))
        self.time_label = ttk.Label(bar, text="--:--", width=22,
                                    font=("Arial", 14, "bold"))
        self.time_label.pack(side="right", padx=10)
        self.slider = tk.Scale(bar, from_=0, to=0, orient="horizontal",
                               showvalue=False, sliderlength=30,
                               command=self.on_slide)
        self.slider.pack(side="left", fill="x", expand=True, padx=8)

        # --- события ---
        c = self.canvas
        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_motion)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Double-Button-1>", self.on_double)
        c.bind("<MouseWheel>", self.on_wheel)                       # Windows / macOS
        c.bind("<Button-4>", lambda e: self.zoom_at(e.x, e.y, 1))   # Linux
        c.bind("<Button-5>", lambda e: self.zoom_at(e.x, e.y, -1))
        root.bind("<Escape>", self.on_escape)
        root.bind("<F11>", lambda e: self.set_fullscreen(not self.fullscreen))
        root.bind("<space>", lambda e: self.toggle_play())
        root.bind("<Left>", lambda e: self.step(-1))
        root.bind("<Right>", lambda e: self.step(1))
        for k in ("plus", "equal", "KP_Add"):
            root.bind(f"<{k}>", lambda e: self.zoom_at(self.aw / 2, self.ah / 2, 1))
        for k in ("minus", "KP_Subtract"):
            root.bind(f"<{k}>", lambda e: self.zoom_at(self.aw / 2, self.ah / 2, -1))
        root.bind("<h>", lambda e: self.go_home())
        root.bind("<a>", lambda e: self.toggle_smooth())
        root.bind("<s>", lambda e: self.toggle_select())
        for ks, fn in (("Cyrillic_ef", self.toggle_smooth),      # А на русской раскладке
                       ("Cyrillic_yeru", self.toggle_select)):   # Ы на русской раскладке
            try:
                root.bind(f"<{ks}>", lambda e, f=fn: f())
            except tk.TclError:
                pass
        root.bind("<q>", lambda e: root.destroy())

        # --- данные / кэши ---
        self.pool = ThreadPoolExecutor(max_workers=8)
        self.raw = {}            # ключ плитки -> байты PNG (b"" = нет данных)
        self.pending = set()
        self.wanted = set()
        self.wanted_radar = []
        self.version = 0
        self.drawn_version = -1
        self.dec = OrderedDict()  # кэш декодированных плиток
        self.frame_cache = {}
        self.base_cache = None
        self.view_key = None
        self.ready = False
        self.playing = True
        self.index = 0
        self.times, self.paths = [], []
        self.drag = None
        self.redraw_scheduled = False
        self.prefetch_job = None
        self.last_wheel = 0
        self.cur_photo = None
        self.lock = threading.Lock()
        self.smooth = False       # сглаживание радара (анти-алиасинг)
        self.select_mode = False  # инструмент выделения области
        self.sel_start = None
        self.sel_rect = None

        self.z = 4
        self.cx = self.cy = 0
        root.update()
        self.load_data()

    # ================= загрузка списка кадров =================
    def load_data(self):
        try:
            info = json.loads(http_get(API_URL))
            self.host = info["host"]
            past = info["radar"]["past"]
        except Exception as e:
            self.canvas.itemconfig(self.status_id, text=f"Ошибка загрузки: {e}")
            return
        self.paths = [f["path"] for f in past]
        self.times = [f["time"] for f in past]

        self.canvas.delete(self.status_id)
        self.canvas_img = self.canvas.create_image(0, 0, anchor="nw")
        self.shadow_id = self.canvas.create_text(
            22, 22, anchor="nw", fill="black", font=("Arial", 30, "bold"))
        self.text_id = self.canvas.create_text(
            20, 20, anchor="nw", fill="white", font=("Arial", 30, "bold"))
        self.zoom_id = self.canvas.create_text(
            22, 70, anchor="nw", fill="white", font=("Arial", 12, "bold"))
        self.progress_id = self.canvas.create_text(
            12, self.ah - 28, anchor="sw", fill="white", font=("Arial", 12, "bold"))
        self.mode_id = self.canvas.create_text(
            22, 94, anchor="nw", fill="#ffe000", font=("Arial", 13, "bold"))
        hint = ("Колесо мыши - масштаб | тянуть - двигать | пробел - пауза | "
                "A - сглаживание | S - выделить область (3D) | "
                "H - к Европе | Esc - выход из полного экрана")
        self.canvas.create_text(11, self.ah - 7, anchor="sw", fill="white",
                                text=hint, font=("Arial", 10))
        self.canvas.create_text(10, self.ah - 8, anchor="sw", fill="#111",
                                text=hint, font=("Arial", 10))
        self.canvas.create_text(self.aw - 9, self.ah - 7, anchor="se", fill="white",
                                text="Данные: RainViewer | Карта: © OpenStreetMap",
                                font=("Arial", 9))
        self.canvas.create_text(self.aw - 10, self.ah - 8, anchor="se", fill="#111",
                                text="Данные: RainViewer | Карта: © OpenStreetMap",
                                font=("Arial", 9))

        self.slider.config(to=len(self.times) - 1)
        self.ready = True
        self.go_home(first=True)
        self.show(len(self.times) - 1)       # начинаем с самого свежего кадра
        self.root.after(150, self.poll)
        self.root.after(FRAME_DELAY_MS, self.tick)

    # ================= вид карты =================
    def go_home(self, first=False):
        self.z = 4 if self.ah >= 640 else 3
        self.cx, self.cy = lonlat_to_px(*HOME_LONLAT, self.z)
        self.clamp_center()
        if not first:
            self.redraw()
            self.prefetch()

    def clamp_center(self):
        world = TILE * 2 ** self.z
        lo_x, hi_x = self.aw / 2, world - self.aw / 2
        lo_y, hi_y = self.ah / 2, world - self.ah / 2
        self.cx = world / 2 if lo_x > hi_x else min(max(self.cx, lo_x), hi_x)
        self.cy = world / 2 if lo_y > hi_y else min(max(self.cy, lo_y), hi_y)

    def zoom_at(self, mx, my, dz):
        if not self.ready:
            return
        newz = min(max(self.z + dz, ZMIN), ZMAX)
        if newz == self.z:
            return
        f = 2.0 ** (newz - self.z)
        left, top = self.cx - self.aw / 2, self.cy - self.ah / 2
        self.cx = (left + mx) * f - mx + self.aw / 2
        self.cy = (top + my) * f - my + self.ah / 2
        self.z = newz
        self.clamp_center()
        self.redraw()
        self.prefetch()

    def on_wheel(self, e):
        now = time.time()
        if now - self.last_wheel < 0.12:      # защита от слишком быстрого зума
            return
        self.last_wheel = now
        self.zoom_at(e.x, e.y, 1 if e.delta > 0 else -1)

    def on_press(self, e):
        if self.select_mode:
            if not self.ready:
                return
            x = min(max(e.x, 0), self.aw)
            y = min(max(e.y, 0), self.ah)
            self.sel_start = (x, y)
            if self.sel_rect:
                self.canvas.delete(self.sel_rect)
            self.sel_rect = self.canvas.create_rectangle(
                x, y, x, y, outline="#ffe000", width=2, dash=(6, 3))
            return
        self.drag = (e.x, e.y, self.cx, self.cy)

    def on_double(self, e):
        if not self.select_mode:
            self.zoom_at(e.x, e.y, 1)

    def on_release(self, e):
        if self.select_mode:
            self.finish_selection(e)
            return
        self.schedule_prefetch()

    def on_escape(self, e):
        if self.select_mode:
            self.set_select_mode(False)
        else:
            self.set_fullscreen(False)

    def on_motion(self, e):
        if self.select_mode:
            if self.sel_start and self.sel_rect:
                x = min(max(e.x, 0), self.aw)
                y = min(max(e.y, 0), self.ah)
                self.canvas.coords(self.sel_rect, self.sel_start[0],
                                   self.sel_start[1], x, y)
            return
        if not self.drag or not self.ready:
            return
        sx, sy, ox, oy = self.drag
        self.cx, self.cy = ox - (e.x - sx), oy - (e.y - sy)
        self.clamp_center()
        if not self.redraw_scheduled:
            self.redraw_scheduled = True
            self.root.after(20, self.redraw)

    # ================= плитки =================
    def url_for(self, key):
        if key[0] == "b":
            _, z, x, y = key
            return f"https://tile.openstreetmap.org/{z}/{x}/{y}.png"
        _, i, rz, x, y = key
        return (f"{self.host}{self.paths[i]}/{RADAR_TILE}/{rz}/{x}/{y}/"
                f"{RADAR_COLOR}/{RADAR_OPTIONS}.png")

    def ensure(self, key):
        """Поставить плитку в очередь на скачивание."""
        self.wanted.add(key)
        if key in self.raw or key in self.pending:
            return
        self.pending.add(key)
        self.pool.submit(self.worker, key)

    def worker(self, key):
        try:
            if key not in self.wanted:        # вид уже сменился - не качаем
                return
            data = None
            for _ in range(2):
                try:
                    data = http_get(self.url_for(key))
                    break
                except Exception:
                    pass
            self.raw[key] = data or b""
            with self.lock:
                self.version += 1
        finally:
            self.pending.discard(key)

    def decode(self, key):
        if key in self.dec:
            self.dec.move_to_end(key)
            return self.dec[key]
        data = self.raw.get(key)
        if not data:
            return None
        try:
            img = Image.open(io.BytesIO(data)).convert("RGBA")
        except Exception:
            return None
        self.dec[key] = img
        if len(self.dec) > 150:
            self.dec.popitem(last=False)
        return img

    def geom(self):
        self.left = int(round(self.cx - self.aw / 2))
        self.top = int(round(self.cy - self.ah / 2))

    def base_keys(self):
        n = 2 ** self.z
        x0 = max(0, self.left // TILE)
        x1 = min(n - 1, (self.left + self.aw - 1) // TILE)
        y0 = max(0, self.top // TILE)
        y1 = min(n - 1, (self.top + self.ah - 1) // TILE)
        return [("b", self.z, x, y)
                for y in range(y0, y1 + 1) for x in range(x0, x1 + 1)]

    def radar_geom(self):
        rz = max(0, min(self.z - 1, RADAR_MAXZ))
        size = TILE * 2 ** (self.z - rz)       # размер плитки радара на экране
        return rz, size

    def radar_keys(self, i):
        rz, s = self.radar_geom()
        n = 2 ** rz
        x0 = max(0, self.left // s)
        x1 = min(n - 1, (self.left + self.aw - 1) // s)
        y0 = max(0, self.top // s)
        y1 = min(n - 1, (self.top + self.ah - 1) // s)
        return [("r", i, rz, x, y)
                for y in range(y0, y1 + 1) for x in range(x0, x1 + 1)]

    # ================= отрисовка =================
    def get_base(self):
        bc = self.base_cache
        if bc and (bc[1] or bc[0] == self.version):
            return bc[2], bc[1]
        v = self.version
        img = Image.new("RGBA", (self.aw, self.ah), (221, 221, 221, 255))
        complete = True
        for key in self.base_keys():
            if key not in self.raw:
                self.ensure(key)
                complete = False
                continue
            tile = self.decode(key)
            if tile is not None:
                _, _, x, y = key
                img.paste(tile, (x * TILE - self.left, y * TILE - self.top))
        self.base_cache = (v, complete, img)
        return img, complete

    def get_frame(self, i):
        ent = self.frame_cache.get(i)
        if ent and (ent[1] or ent[0] == self.version):
            return ent[2]
        v = self.version
        base, complete = self.get_base()
        rz, s = self.radar_geom()
        layer = Image.new("RGBA", (self.aw, self.ah), (0, 0, 0, 0))
        for key in self.radar_keys(i):
            if key not in self.raw:
                self.ensure(key)
                complete = False
                continue
            tile = self.decode(key)
            if tile is None:
                continue
            if tile.size != (s, s):
                tile = tile.resize(
                    (s, s), Image.BICUBIC if self.smooth else Image.NEAREST)
            _, _, _, x, y = key
            layer.paste(tile, (x * s - self.left, y * s - self.top))
        b = PIXEL_BLOCK
        if self.smooth:                      # сглаженный вид: без «квадратиков»
            if b > 1:
                layer = layer.resize((max(1, self.aw // b), max(1, self.ah // b)),
                                     Image.BOX).resize((self.aw, self.ah),
                                                       Image.BICUBIC)
        elif b > 1:                          # пиксельный вид осадков
            layer = layer.resize((max(1, self.aw // b), max(1, self.ah // b)),
                                 Image.NEAREST).resize((self.aw, self.ah),
                                                       Image.NEAREST)
        photo = ImageTk.PhotoImage(Image.alpha_composite(base, layer))
        self.frame_cache[i] = (v, complete, photo)
        return photo

    def redraw(self):
        self.redraw_scheduled = False
        if not self.ready:
            return
        self.drawn_version = self.version
        self.geom()
        key = (self.z, self.left, self.top)
        if key != self.view_key:
            self.view_key = key
            self.frame_cache.clear()
            self.base_cache = None
        self.cur_photo = self.get_frame(self.index)
        self.canvas.itemconfig(self.canvas_img, image=self.cur_photo)
        self.canvas.itemconfig(self.zoom_id, text=f"Масштаб: {self.z}", fill="white")

    # ================= предзагрузка всех кадров =================
    def schedule_prefetch(self):
        if self.prefetch_job:
            self.root.after_cancel(self.prefetch_job)
        self.prefetch_job = self.root.after(300, self.prefetch)

    def prefetch(self):
        self.prefetch_job = None
        if not self.ready:
            return
        self.geom()
        order = [self.index] + [i for i in range(len(self.times) - 1, -1, -1)
                                if i != self.index]
        base = self.base_keys()
        radar = []
        for i in order:
            radar += self.radar_keys(i)
        self.wanted = set()
        self.wanted_radar = radar
        for k in base + radar:
            self.ensure(k)

    def progress(self):
        total = len(self.wanted_radar)
        done = sum(1 for k in self.wanted_radar if k in self.raw)
        return done, total

    def poll(self):
        if self.version != self.drawn_version:
            self.redraw()
        done, total = self.progress()
        self.canvas.itemconfig(
            self.progress_id,
            text="" if done >= total else f"Загрузка радара: {done}/{total}")
        self.root.after(150, self.poll)

    # ================= время / управление =================
    def show(self, i):
        self.index = i
        t = datetime.fromtimestamp(self.times[i])
        mins_ago = round((self.times[-1] - self.times[i]) / 60)
        ago = "сейчас" if mins_ago == 0 else f"-{mins_ago} мин"
        label = t.strftime("%H:%M")
        self.canvas.itemconfig(self.text_id, text=label)
        self.canvas.itemconfig(self.shadow_id, text=label)
        self.time_label.config(text=f"{label}  ({ago})")
        self.slider.set(i)
        self.redraw()
        if not self.wanted_radar:
            self.prefetch()

    def on_slide(self, value):
        if self.ready and int(value) != self.index:
            self.show(int(value))

    def step(self, d):
        if self.ready:
            self.playing = False
            self.play_btn.config(text="Старт")
            self.show((self.index + d) % len(self.times))

    def toggle_play(self):
        self.playing = not self.playing
        self.play_btn.config(text="Пауза" if self.playing else "Старт")

    # ================= сглаживание =================
    def toggle_smooth(self):
        self.smooth = not self.smooth
        self.smooth_btn.config(
            text="Сглаживание: вкл" if self.smooth else "Сглаживание: выкл")
        if self.ready:
            self.frame_cache.clear()
            self.redraw()

    # ================= выделение области + 3D-облако =================
    def toggle_select(self):
        if self.ready:
            self.set_select_mode(not self.select_mode)

    def set_select_mode(self, value):
        self.select_mode = value
        self.sel_start = None
        if self.sel_rect:
            self.canvas.delete(self.sel_rect)
            self.sel_rect = None
        self.canvas.config(cursor="crosshair" if value else "fleur")
        self.select_btn.config(text="Отмена выделения" if value
                               else "Выделить область")
        if self.ready:
            self.canvas.itemconfig(
                self.mode_id,
                text="Выделение: нарисуйте рамку мышью (Esc - отмена)"
                if value else "")

    def finish_selection(self, e):
        if not self.sel_start:
            return
        x0, y0 = self.sel_start
        x1 = min(max(e.x, 0), self.aw)
        y1 = min(max(e.y, 0), self.ah)
        self.sel_start = None
        if self.sel_rect:
            self.canvas.delete(self.sel_rect)
            self.sel_rect = None
        x0, x1 = sorted((int(x0), int(x1)))
        y0, y1 = sorted((int(y0), int(y1)))
        if x1 - x0 < 12 or y1 - y0 < 12:      # слишком маленькая рамка
            return
        self.set_select_mode(False)
        self.open_cloud(x0, y0, x1, y1)

    def open_cloud(self, x0, y0, x1, y1):
        self.geom()
        rz, s = self.radar_geom()
        base, _ = self.get_base()
        spec = dict(z=self.z, left=self.left, top=self.top, rz=rz, s=s,
                    box=(x0, y0, x1, y1), index=self.index,
                    time=self.times[self.index])
        ground = base.crop((x0, y0, x1, y1)).convert("RGB")
        CloudWindow(self, spec, ground)

    def set_fullscreen(self, value):
        self.fullscreen = value
        self.root.attributes("-fullscreen", value)

    def tick(self):
        done, total = self.progress()
        if self.playing and self.ready and done >= total:
            self.show((self.index + 1) % len(self.times))
        self.root.after(FRAME_DELAY_MS, self.tick)


if __name__ == "__main__":
    root = tk.Tk()
    RainApp(root)
    root.mainloop()
