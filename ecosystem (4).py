#!/usr/bin/env python3
"""
Jurassic Park - Mini Ecosystem Lab
==================================
Grass grows, cows graze, lions and tigers hunt. Tweak the sliders and see
whether the little world survives or collapses.

Requirements:  Python 3.8+, tkinter (bundled with Python)
Optional DB:   pip install mysql-connector-python
               (the simulation works without MySQL; it just won't save history)

MySQL settings: use the "Database" button, or set the environment variables
ECO_DB_HOST, ECO_DB_PORT, ECO_DB_USER, ECO_DB_PASSWORD, ECO_DB_NAME.
The database and tables are created automatically.
"""
import array
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import wave
import tkinter as tk
from tkinter import ttk, messagebox

try:
    import mysql.connector as mysql_connector
except ImportError:  # the sim still runs, just without history
    mysql_connector = None

# --------------------------------------------------------------------------- #
#  Constants & palette
# --------------------------------------------------------------------------- #
CELL = 26
COLS = ROWS = W = H = 0
FPS = 30


def set_grid(width, height):
    """Size the meadow to the canvas so it always fills the whole window."""
    global COLS, ROWS, W, H
    W, H = max(320, int(width)), max(240, int(height))
    COLS, ROWS = math.ceil(W / CELL), math.ceil(H / CELL)


set_grid(1000, 600)

BG, PANEL, CARD = "#0e1d17", "#142a20", "#1b3629"
TEXT, MUTED = "#e9f4e1", "#8fb39a"
C_GRASS, C_COW, C_PRED = "#7bd88f", "#9ad0ff", "#ffb347"
OK, WARN, BAD = "#7bd88f", "#f2b45a", "#ee6b6e"


def lerp_color(a, b, t):
    a = [int(a[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(b[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


# bucket 0 = bare soil ... bucket 5 = lush grass
GROUND = [lerp_color("#6b5a3a", "#2f6b34", i / 5) for i in range(6)]
BLADES = [[lerp_color("#8a7a4a", c, i / 5) for c in ("#5fb04a", "#79cf5a", "#4a9a40")]
          for i in range(6)]


# --------------------------------------------------------------------------- #
#  Simulation model
# --------------------------------------------------------------------------- #
class Animal:
    _next_id = 0

    def __init__(self, x, y, energy, kind):
        self.id = Animal._next_id
        Animal._next_id += 1
        self.tag = "a%d" % self.id
        self.kind = kind                       # "cow", "lion" or "tiger"
        self.x, self.y, self.energy = x, y, energy
        self.angle = random.uniform(0, 2 * math.pi)
        self.face = 1 if math.cos(self.angle) >= 0 else -1
        self.cool = random.randint(0, 250)     # reproduction cooldown
        self.timer = random.randint(0, 6)      # next sense / decision
        self.gtimer = random.randint(0, 10)
        self.target = None
        self.threat = None
        self.rest = 0
        self.age = 0
        self.alive = True
        self.moving = False
        # render cache
        self.rx = self.ry = self.rface = self.rpose = None


class World:
    def __init__(self, init_h, init_p):
        self.tick = 0
        self.grass = [[random.uniform(0.5, 1.0) for _ in range(COLS)] for _ in range(ROWS)]
        self.herbs, self.preds = [], []
        self.graveyard = []
        self._newh, self._newp = [], []
        self.events = []
        self.kills = 0
        self.max_h, self.max_p = self.caps()
        for _ in range(int(init_h)):
            self.add("cow", random.uniform(20, W - 20), random.uniform(20, H - 20), random.uniform(50, 90))
        for _ in range(int(init_p)):
            self.add(random.choice(("lion", "tiger")), random.uniform(20, W - 20),
                     random.uniform(20, H - 20), random.uniform(80, 120))

    # -- helpers ----------------------------------------------------------- #
    @staticmethod
    def caps():
        f = COLS * ROWS / 640.0          # bigger meadow -> room for more animals
        return min(450, int(220 * f)), min(90, int(50 * f))

    def resize(self):
        old = self.grass
        self.grass = [[old[r][c] if r < len(old) and c < len(old[0]) else random.uniform(0.5, 1.0)
                       for c in range(COLS)] for r in range(ROWS)]
        for a in self.herbs + self.preds:
            a.x, a.y = min(a.x, W - 12), min(a.y, H - 10)
        self.max_h, self.max_p = self.caps()

    def add(self, kind, x, y, energy=None):
        if kind == "cow":
            if len(self.herbs) >= self.max_h:
                return
            self.herbs.append(Animal(x, y, energy or 60, "cow"))
        else:
            if len(self.preds) >= self.max_p:
                return
            self.preds.append(Animal(x, y, energy or 100, kind))

    def grass_pct(self):
        return sum(sum(r) for r in self.grass) / (ROWS * COLS) * 100

    def drought(self):
        for r in self.grass:
            for c in range(COLS):
                r[c] *= 0.25

    def rain(self):
        for r in self.grass:
            for c in range(COLS):
                r[c] = min(1.0, r[c] + 0.5)

    def plague(self, frac):
        n = int(len(self.herbs) * frac)
        for _ in range(n):
            self._kill(self.herbs.pop(random.randrange(len(self.herbs))))
        return n

    @staticmethod
    def _move(a, speed):
        a.x += math.cos(a.angle) * speed
        a.y += math.sin(a.angle) * speed
        if a.x < 10:
            a.x, a.angle = 10, math.pi - a.angle
        elif a.x > W - 10:
            a.x, a.angle = W - 10, math.pi - a.angle
        if a.y < 14:
            a.y, a.angle = 14, -a.angle
        elif a.y > H - 8:
            a.y, a.angle = H - 8, -a.angle
        cs = math.cos(a.angle)
        if cs > 0.25:
            a.face = 1
        elif cs < -0.25:
            a.face = -1

    def _kill(self, a):
        a.alive = False
        self.graveyard.append(a)

    # -- one simulation tick ------------------------------------------------ #
    def step(self, p):
        self.tick += 1
        self._grow_grass(p["grass_rate"])
        for h in self.herbs:
            if h.alive:
                self._cow(h, p)
        for q in self.preds:
            if q.alive:
                self._predator(q, p)
        self.herbs = [h for h in self.herbs if h.alive] + self._newh
        self.preds = [q for q in self.preds if q.alive] + self._newp
        self._newh, self._newp = [], []

    def _grow_grass(self, rate):
        g = self.grass
        base = 0.0009 * rate
        seed_p, wind_p = 0.01 * rate, 0.0004 * rate
        rnd = random.random
        for r in range(ROWS):
            row = g[r]
            for c in range(COLS):
                v = row[c]
                if v >= 1.0:
                    continue
                if v < 0.04:   # bare soil needs seeds from a neighbour (or wind)
                    if (rnd() < seed_p and self._neighbour_max(r, c) > 0.3) or rnd() < wind_p:
                        row[c] = 0.05
                else:
                    v += base * (0.6 + rnd() * 0.8) * (1 + v)
                    row[c] = v if v < 1.0 else 1.0

    def _neighbour_max(self, r, c):
        g, m = self.grass, 0.0
        if r > 0:
            m = max(m, g[r - 1][c])
        if r < ROWS - 1:
            m = max(m, g[r + 1][c])
        if c > 0:
            m = max(m, g[r][c - 1])
        if c < COLS - 1:
            m = max(m, g[r][c + 1])
        return m

    # -- cows ---------------------------------------------------------------- #
    def _cow(self, h, p):
        h.age += 1
        h.energy -= 0.19
        if h.energy <= 0 or h.age > 5000:
            self._kill(h)
            return

        h.timer -= 1
        if h.timer <= 0:                        # look out for predators
            h.timer = 4
            h.threat, best = None, 85 * 85
            for q in self.preds:
                d = (q.x - h.x) ** 2 + (q.y - h.y) ** 2
                if d < best:
                    best, h.threat = d, q

        speed = 0.0
        if h.threat is not None and h.threat.alive:      # run!
            h.angle = math.atan2(h.y - h.threat.y, h.x - h.threat.x) + random.uniform(-0.3, 0.3)
            speed = 1.9
            h.energy -= 0.1
        else:
            h.threat = None
            r = min(ROWS - 1, max(0, int(h.y // CELL)))
            c = min(COLS - 1, max(0, int(h.x // CELL)))
            v = self.grass[r][c]
            if v > 0.12 and h.energy < 95:               # graze
                bite = min(v, 0.05)
                self.grass[r][c] = v - bite
                h.energy += bite * 55
            else:
                h.gtimer -= 1
                if h.gtimer <= 0:
                    h.gtimer = 10
                    h.target = self._find_grass(h) if h.energy < 85 else None
                if h.target:
                    tx, ty = h.target
                    h.angle = math.atan2(ty - h.y, tx - h.x)
                    speed = 1.3
                    if (tx - h.x) ** 2 + (ty - h.y) ** 2 < 36:
                        h.target = None
                else:
                    h.angle += random.uniform(-0.35, 0.35)
                    speed = 0.7
        h.moving = speed > 0
        if speed:
            self._move(h, speed)

        h.cool -= 1                                      # reproduction
        if h.cool <= 0 and h.energy >= 75 and len(self.herbs) + len(self._newh) < self.max_h:
            h.energy -= 38
            h.cool = int(260 / p["repro"] * random.uniform(0.8, 1.2))
            self._newh.append(Animal(h.x + random.uniform(-8, 8), h.y + random.uniform(-8, 8), 32, "cow"))
            self.events.append(("birth_h", h.x, h.y))

    def _find_grass(self, h):
        r0, c0 = int(h.y // CELL), int(h.x // CELL)
        best, best_s = None, 0.0
        for r in range(max(0, r0 - 4), min(ROWS, r0 + 5)):
            for c in range(max(0, c0 - 4), min(COLS, c0 + 5)):
                v = self.grass[r][c]
                if v > 0.3:
                    s = v - 0.12 * math.hypot(r - r0, c - c0)
                    if s > best_s:
                        best_s, best = s, (c * CELL + CELL / 2, r * CELL + CELL / 2)
        return best

    # -- predators ----------------------------------------------------------- #
    def _predator(self, q, p):
        q.age += 1
        q.energy -= 0.2 * p["pred_hunger"]
        if q.energy <= 0 or q.age > 7000:
            self._kill(q)
            return
        if q.rest > 0:
            q.rest -= 1

        q.timer -= 1
        if q.timer <= 0:
            q.timer = 5
            q.target = None
            if q.rest <= 0 and q.energy < 115:
                best = 150 * 150
                for h in self.herbs:
                    if h.alive:
                        d = (h.x - q.x) ** 2 + (h.y - q.y) ** 2
                        if d < best:
                            best, q.target = d, h

        speed = 0.5 if q.rest > 0 else 0.9
        t = q.target
        if t is not None and t.alive and q.rest <= 0:
            dx, dy = t.x - q.x, t.y - q.y
            if dx * dx + dy * dy < 14 * 14:             # caught it
                self._kill(t)
                self.kills += 1
                self.events.append(("kill", t.x, t.y))
                q.energy = min(q.energy + 65, 170)
                q.rest = 70
                q.target = None
            else:
                q.angle = math.atan2(dy, dx)
                speed = 2.25
                q.energy -= 0.12
        else:
            q.target = None
            q.angle += random.uniform(-0.3, 0.3)
        q.moving = True
        self._move(q, speed)

        q.cool -= 1
        if q.cool <= 0 and q.energy >= 130 and len(self.preds) + len(self._newp) < self.max_p:
            q.energy -= 60
            q.cool = int(1700 / p["repro"] * random.uniform(0.8, 1.2))
            kind = random.choice(("lion", "tiger"))
            self._newp.append(Animal(q.x + random.uniform(-8, 8), q.y + random.uniform(-8, 8), 45, kind))
            self.events.append(("birth_p", q.x, q.y, kind))


# --------------------------------------------------------------------------- #
#  MySQL layer (optional)
# --------------------------------------------------------------------------- #
class Database:
    def __init__(self):
        self.cfg = {
            "host": os.getenv("ECO_DB_HOST", "localhost"),
            "port": int(os.getenv("ECO_DB_PORT", "3306")),
            "user": os.getenv("ECO_DB_USER", "root"),
            "password": os.getenv("ECO_DB_PASSWORD", ""),
            "database": os.getenv("ECO_DB_NAME", "ecosystem_sim"),
        }
        self.conn = None
        self.error = ""

    @property
    def ok(self):
        return self.conn is not None

    def close(self):
        try:
            if self.conn:
                self.conn.close()
        except Exception:
            pass
        self.conn = None

    def _fail(self, exc):
        self.error = str(exc)
        self.close()

    def connect(self, cfg=None):
        if cfg:
            self.cfg.update(cfg)
        if mysql_connector is None:
            self.error = "Driver missing: pip install mysql-connector-python"
            return False
        self.close()
        db = re.sub(r"[^A-Za-z0-9_]", "", str(self.cfg["database"])) or "ecosystem_sim"
        try:
            c = mysql_connector.connect(host=self.cfg["host"], port=int(self.cfg["port"]),
                                        user=self.cfg["user"], password=self.cfg["password"],
                                        connection_timeout=4)
            cur = c.cursor()
            cur.execute("CREATE DATABASE IF NOT EXISTS `%s`" % db)
            c.database = db
            cur.execute("""CREATE TABLE IF NOT EXISTS runs (
                id INT AUTO_INCREMENT PRIMARY KEY,
                started_at DATETIME NOT NULL,
                ended_at DATETIME NULL,
                init_herbivores INT, init_predators INT,
                grass_rate FLOAT, repro_speed FLOAT, pred_hunger FLOAT,
                total_ticks INT DEFAULT 0,
                outcome VARCHAR(80) DEFAULT 'running')""")
            cur.execute("""CREATE TABLE IF NOT EXISTS population_log (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                run_id INT NOT NULL,
                tick INT NOT NULL,
                grass_pct FLOAT, herbivores INT, predators INT,
                INDEX idx_run_tick (run_id, tick),
                FOREIGN KEY (run_id) REFERENCES runs(id) ON DELETE CASCADE)""")
            c.commit()
            self.conn, self.cfg["database"], self.error = c, db, ""
            return True
        except Exception as exc:
            self._fail(exc)
            return False

    def start_run(self, p):
        if not self.ok:
            return None
        try:
            cur = self.conn.cursor()
            cur.execute("INSERT INTO runs (started_at, init_herbivores, init_predators, grass_rate,"
                        " repro_speed, pred_hunger) VALUES (NOW(),%s,%s,%s,%s,%s)",
                        (p["init_h"], p["init_p"], p["grass_rate"], p["repro"], p["pred_hunger"]))
            self.conn.commit()
            return cur.lastrowid
        except Exception as exc:
            self._fail(exc)
            return None

    def flush(self, rows):
        if not (self.ok and rows):
            return
        try:
            cur = self.conn.cursor()
            cur.executemany("INSERT INTO population_log (run_id,tick,grass_pct,herbivores,predators)"
                            " VALUES (%s,%s,%s,%s,%s)", rows)
            self.conn.commit()
        except Exception as exc:
            self._fail(exc)

    def end_run(self, run_id, ticks, outcome):
        if not (self.ok and run_id):
            return
        try:
            cur = self.conn.cursor()
            cur.execute("UPDATE runs SET ended_at=NOW(), total_ticks=%s, outcome=%s WHERE id=%s",
                        (ticks, outcome, run_id))
            self.conn.commit()
        except Exception as exc:
            self._fail(exc)

    def list_runs(self):
        if not self.ok:
            return []
        try:
            cur = self.conn.cursor()
            cur.execute("SELECT id, started_at, init_herbivores, init_predators, grass_rate, repro_speed,"
                        " total_ticks, outcome FROM runs ORDER BY id DESC LIMIT 200")
            return cur.fetchall()
        except Exception as exc:
            self._fail(exc)
            return []

    def run_log(self, run_id):
        if not self.ok:
            return []
        try:
            cur = self.conn.cursor()
            cur.execute("SELECT tick, grass_pct, herbivores, predators FROM population_log"
                        " WHERE run_id=%s ORDER BY tick", (run_id,))
            return [(t, float(g), h, p) for t, g, h, p in cur.fetchall()]
        except Exception as exc:
            self._fail(exc)
            return []

    def delete_run(self, run_id):
        if not self.ok:
            return
        try:
            cur = self.conn.cursor()
            cur.execute("DELETE FROM runs WHERE id=%s", (run_id,))
            self.conn.commit()
        except Exception as exc:
            self._fail(exc)


# --------------------------------------------------------------------------- #
#  Drawing helpers
# --------------------------------------------------------------------------- #
def draw_graph(cv, samples, w, h):
    """Population graph: grass % (green), cows (blue), predators (orange)."""
    cv.delete("all")
    cv.create_rectangle(0, 0, w, h, fill=CARD, outline="")
    pad = 10
    for i in range(1, 4):
        y = pad + (h - 2 * pad) * i / 4
        cv.create_line(pad, y, w - pad, y, fill="#25463a")
    cv.create_text(pad + 2, 9, anchor="w", text="grass %", fill=C_GRASS, font=("Helvetica", 8, "bold"))
    cv.create_text(pad + 50, 9, anchor="w", text="herbivores", fill=C_COW, font=("Helvetica", 8, "bold"))
    cv.create_text(pad + 112, 9, anchor="w", text="predators", fill=C_PRED, font=("Helvetica", 8, "bold"))
    if len(samples) < 2:
        cv.create_text(w / 2, h / 2 + 6, text="population history appears here", fill=MUTED,
                       font=("Helvetica", 9, "italic"))
        return
    if len(samples) > 260:
        step = len(samples) / 260
        samples = [samples[int(i * step)] for i in range(260)] + [samples[-1]]
    ymax = max(10, max(max(s[2], s[3]) for s in samples))
    n = len(samples)
    top, bot = pad + 10, h - pad

    def line(idx, scale, color):
        pts = []
        for i, s in enumerate(samples):
            pts += [pad + (w - 2 * pad) * i / (n - 1), bot - (bot - top) * min(1.0, s[idx] / scale)]
        cv.create_line(*pts, fill=color, width=2)

    line(1, 100.0, C_GRASS)
    line(2, ymax, C_COW)
    line(3, ymax, C_PRED)
    cv.create_text(w - pad, 9, anchor="e", text="max %d" % ymax, fill=MUTED, font=("Helvetica", 8))


def draw_animal(c, a, pose):
    """Draw an animal from simple canvas shapes, facing a.face (+1 right, -1 left)."""
    x, y, f, tag = a.x, a.y, a.face, (a.tag,)

    def ov(cx, cy, rx, ry, **kw):
        c.create_oval(x + f * cx - rx, y + cy - ry, x + f * cx + rx, y + cy + ry, tags=tag, **kw)

    def ln(x1, y1, x2, y2, **kw):
        c.create_line(x + f * x1, y + y1, x + f * x2, y + y2, tags=tag, capstyle=tk.ROUND, **kw)

    sw = 2 if pose else -2
    ov(0, 11, 16, 4, fill="#264a2c", outline="")                       # shadow

    if a.kind == "cow":
        for lx, s in ((-9, sw), (-5, -sw), (6, -sw), (10, sw)):
            ln(lx, 3, lx + s, 12, fill="#d8d8d8", width=3)
        ln(-14, -5, -18, 4, fill="#444", width=2)                        # tail
        ov(0, -2, 15, 8, fill="#fafafa", outline="#555")                  # body
        ov(-6, -4, 4, 3, fill="#222", outline="")
        ov(5, 1, 4, 3, fill="#222", outline="")
        ov(16, -6, 6, 5.5, fill="#fafafa", outline="#555")                # head
        ov(21, -4, 3.5, 3, fill="#f4a6b0", outline="")                    # snout
        ov(17, -8, 1.2, 1.2, fill="#111", outline="")                     # eye
        ln(14, -10, 13, -15, fill="#e8d9a8", width=2)                     # horn
        ov(12, -9, 2.5, 1.8, fill="#8a5a3a", outline="")                  # ear

    elif a.kind == "lion":
        for lx, s in ((-10, sw), (-6, -sw), (7, -sw), (11, sw)):
            ln(lx, 3, lx + s, 12, fill="#c9953a", width=3)
        ln(-15, -4, -23, -8, fill="#c9953a", width=2)                     # tail
        ov(-24, -9, 3, 3, fill="#7a3f10", outline="")                     # tail tuft
        ov(0, -2, 17, 8.5, fill="#e0aa4b", outline="#8a5a1a")             # body
        ov(16, -6, 10.5, 10.5, fill="#7a3f10", outline="#4a2508")         # mane
        ov(18, -5, 6.5, 6, fill="#efc27a", outline="")                    # face
        ov(22.5, -3, 3, 2.5, fill="#f6dba8", outline="")                  # muzzle
        ov(24.5, -4.5, 1.1, 1.1, fill="#3a2010", outline="")              # nose
        ov(19, -7.5, 1.2, 1.2, fill="#111", outline="")                   # eye
        ov(14, -14, 2.6, 2.6, fill="#7a3f10", outline="#4a2508")          # ear

    else:  # tiger
        for lx, s in ((-10, sw), (-6, -sw), (7, -sw), (11, sw)):
            ln(lx, 3, lx + s, 12, fill="#ee8b2b", width=3)
        ln(-15, -4, -23, -9, fill="#ee8b2b", width=3)                     # tail
        ln(-21, -8, -24, -10, fill="#111", width=3)
        ov(0, -2, 17, 8, fill="#ee8b2b", outline="#6a3300")               # body
        for sx in (-9, -3, 4, 10):
            ln(sx, -9, sx + 1.5, 3, fill="#111", width=2)                 # stripes
        ov(17, -5, 7, 6.2, fill="#f09a3c", outline="#6a3300")             # head
        ov(20, -2, 3.6, 2.6, fill="#fff3df", outline="")                  # cheek
        ov(24, -3.5, 1.2, 1, fill="#c0392b", outline="")                  # nose
        ov(19, -7.5, 1.4, 1.4, fill="#ffe14a", outline="")                # eye
        ov(19, -7.5, 0.6, 0.6, fill="#111", outline="")
        ln(15, -10.5, 15.5, -8, fill="#111", width=2)                     # forehead stripes
        ln(17.5, -11, 17.8, -8.5, fill="#111", width=2)
        ov(13, -11.5, 2.5, 2.5, fill="#ee8b2b", outline="#6a3300")        # ear


# --------------------------------------------------------------------------- #
#  Soft jungle ambience (synthesised, no downloads or extra packages needed)
# --------------------------------------------------------------------------- #
def synth_jungle(path, secs=24, sr=22050):
    """Write a seamless, quiet loop: leafy wind, crickets, distant birds, a low hoot."""
    rnd = random.Random(11)
    fade = sr                                  # 1 s cross-fade makes the loop seamless
    n = secs * sr
    total = n + fade
    buf = [0.0] * total
    two_pi = 2 * math.pi

    # leafy rustle: low-passed noise that slowly swells and fades
    lp = 0.0
    for i in range(total):
        lp += 0.10 * (rnd.uniform(-1, 1) - lp)
        swell = 0.55 + 0.45 * math.sin(two_pi * 3 * i / n)
        buf[i] = lp * swell * 0.55

    # crickets: soft pulsed high tone
    for freq, rate, amp in ((4300, 7.0, 0.020), (5100, 5.3, 0.014)):
        for i in range(total):
            t = i / sr
            gate = max(0.0, math.sin(two_pi * rate * t))
            group = 0.5 + 0.5 * math.sin(two_pi * 0.4 * t + freq)
            buf[i] += amp * gate * gate * group * math.sin(two_pi * freq * t)

    def note(start, dur, f0, f1, amp, vib=0.0):
        s0, cnt, phase = int(start * sr), int(dur * sr), 0.0
        for j in range(cnt):
            if s0 + j >= total:
                break
            u = j / cnt
            f = f0 + (f1 - f0) * u + vib * math.sin(two_pi * 28 * j / sr)
            phase += two_pi * f / sr
            env = math.sin(math.pi * u) ** 2
            buf[s0 + j] += amp * env * math.sin(phase)

    # bird calls: little 2-5 note phrases at random moments
    for _ in range(14):
        t = rnd.uniform(0.5, secs - 1.5)
        base = rnd.uniform(1800, 3300)
        amp = rnd.uniform(0.05, 0.10)
        for k in range(rnd.randint(2, 5)):
            d = rnd.uniform(0.07, 0.16)
            up = rnd.choice((-1, 1))
            note(t, d, base, base + up * rnd.uniform(300, 900), amp, vib=rnd.uniform(0, 120))
            t += d + rnd.uniform(0.04, 0.10)

    # far-off hoot
    for _ in range(3):
        t = rnd.uniform(1, secs - 2)
        note(t, 0.55, 520, 440, 0.07)
        note(t + 0.8, 0.7, 500, 400, 0.06)

    _write_wav(path, _loopify(buf, n, fade))


def _loopify(buf, n, fade):
    """Blend the extra tail into the start so the loop has no audible seam."""
    out = buf[:n]
    for j in range(fade):
        w = j / fade
        out[j] = buf[j] * w + buf[n + j] * (1 - w)
    return out


def _write_wav(path, samples, sr=22050, gain=0.35):
    peak = max(1e-6, max(abs(v) for v in samples))
    data = array.array("h", (int(v / peak * 32767 * gain) for v in samples))   # keep it soft
    tmp = path + ".tmp"
    with wave.open(tmp, "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(data.tobytes())
    os.replace(tmp, path)


def synth_gameover(path, sr=22050):
    """Original retro 8-bit 'game over' jingle: square-wave notes, a falling wobble slide, triangle bass."""
    total = int(4.6 * sr)
    buf = [0.0] * total
    two_pi = 2 * math.pi
    rnd = random.Random(8)

    def hz(m):
        return 440.0 * 2 ** ((m - 69) / 12.0)

    def square(start, dur, f0, f1, amp, duty=0.5, wobble=0.0, hold=0.85):
        s0, cnt, ph = int(start * sr), int(dur * sr), 0.0
        for j in range(cnt):
            if s0 + j >= total:
                break
            u = j / cnt
            f = f0 + (f1 - f0) * u + wobble * math.sin(two_pi * 9 * j / sr)
            ph = (ph + f / sr) % 1.0
            env = min(1.0, j / (0.004 * sr)) * (1.0 if u < hold else (1 - u) / (1 - hold))
            buf[s0 + j] += amp * env * (1.0 if ph < duty else -1.0)

    def triangle(start, dur, f, amp):
        s0, cnt, ph = int(start * sr), int(dur * sr), 0.0
        for j in range(cnt):
            if s0 + j >= total:
                break
            ph = (ph + f / sr) % 1.0
            tri = 4 * abs(ph - 0.5) - 1
            buf[s0 + j] += amp * tri * math.exp(-j / sr * 1.6) * min(1.0, j / (0.004 * sr))

    def thud(start, dur, amp):
        s0, cnt = int(start * sr), int(dur * sr)
        for j in range(cnt):
            if s0 + j < total:
                buf[s0 + j] += amp * math.exp(-j / sr * 14) * rnd.uniform(-1, 1)

    thud(0.0, 0.15, 0.9)                                       # impact
    for k, midi in enumerate((76, 72, 69, 64)):                # quick falling steps
        square(0.18 + k * 0.14, 0.12, hz(midi), hz(midi), 0.30)
    square(0.78, 1.3, 330, 62, 0.26, duty=0.25, wobble=14)     # long wobbling fall
    triangle(0.78, 1.8, 110, 0.55)
    for k, midi in enumerate((57, 55, 52)):                    # sad little tail
        square(2.25 + k * 0.38, 0.34, hz(midi), hz(midi) * 0.985, 0.22, duty=0.125)
    triangle(2.25, 2.2, 55, 0.5)
    thud(3.55, 0.5, 0.6)                                       # final thump

    _write_wav(path, buf, sr=sr, gain=0.45)


class Ambience:
    """Loops generated soundtracks with whatever audio player the OS offers.
    Modes: "jungle" (alive) and "death" (the herbivores are gone: a one-shot 8-bit game-over jingle)."""

    TRACKS = (("jungle", "eco_jungle_ambience_v2.wav"), ("death", "eco_gameover_8bit_v1.wav"))

    def __init__(self):
        self.enabled = True
        self.mode = "jungle"
        self.paths = {}
        self.proc = None
        self._ev = threading.Event()
        self._lock = threading.Lock()

    def prepare(self):
        threading.Thread(target=self._build, daemon=True).start()

    def _build(self):
        for name, fname in self.TRACKS:
            path = os.path.join(tempfile.gettempdir(), fname)
            try:
                if not os.path.exists(path):
                    (synth_jungle if name == "jungle" else synth_gameover)(path)
                self.paths[name] = path
                if name == self.mode:
                    self._apply()
            except Exception:
                pass

    def set_mode(self, mode):
        if mode != self.mode:
            self.mode = mode
            self._apply()

    def toggle(self):
        self.enabled = not self.enabled
        self._apply()
        return self.enabled

    def _apply(self):
        with self._lock:
            self._halt()
            path = self.paths.get(self.mode)
            if not (self.enabled and path):
                return
            if sys.platform.startswith("win"):
                import winsound
                flags = winsound.SND_FILENAME | winsound.SND_ASYNC
                if self.mode != "death":                 # the game-over jingle plays once
                    flags |= winsound.SND_LOOP
                winsound.PlaySound(path, flags)
                return
            if sys.platform == "darwin":
                cmd = ["afplay", path]
            else:
                cmd = next(([c, *a, path] for c, a in (("paplay", []), ("aplay", ["-q"]), ("play", ["-q"]))
                            if shutil.which(c)), None)
            if cmd and shutil.which(cmd[0]):
                self._ev = threading.Event()
                threading.Thread(target=self._loop, args=(cmd, self._ev, self.mode != "death"), daemon=True).start()

    def _loop(self, cmd, ev, repeat=True):
        while not ev.is_set():
            try:
                self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                self.proc.wait()
            except Exception:
                break
            if not repeat:
                break

    def _halt(self):
        self._ev.set()
        if sys.platform.startswith("win"):
            try:
                import winsound
                winsound.PlaySound(None, winsound.SND_PURGE)
            except Exception:
                pass
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.terminate()
            except Exception:
                pass
        self.proc = None

    def stop(self):
        with self._lock:
            self._halt()


# --------------------------------------------------------------------------- #
#  Game layer: palettes, goals, powers, achievements
# --------------------------------------------------------------------------- #
HUD_BG, GOLD = "#0c1a14", "#ffd166"
BASE_H, BASE_P = 45, 6           # default starting populations for a 640-cell meadow
PRESETS = {                      # name: (herbivores, predators, grass growth, breeding speed)
    "Balanced garden": (45, 6, 1.0, 1.0),
    "Predator invasion": (30, 30, 1.0, 1.0),
    "Herbivore boom": (120, 2, 1.0, 1.0),
    "Drought land": (60, 6, 0.25, 1.0),
    "Lush paradise": (60, 10, 2.0, 1.0),
}
PANEL_W = 340
LEVEL_GOALS = [1500, 4000, 8000, 14000, 22000, 32000, 45000]      # ticks both species must stay alive
POWERS = {"rain": ("Rain", 20), "drought": ("Drought", 25), "plague": ("Plague", 30)}   # label, cooldown (s)
ACH = {
    "first_hunt": ("First Hunt", "A predator made its first kill"),
    "cub": ("A Cub Is Born", "The predators have bred"),
    "herd": ("Thundering Herd", "100 herbivores roam the land"),
    "pride": ("Apex Pride", "12 predators on the prowl"),
    "lush": ("Lush Paradise", "Green meadow, thriving herd"),
    "survivor": ("Survivor", "100 seconds of balance"),
    "comeback": ("Comeback Kid", "Herd rebuilt after near-extinction"),
}
_TINTS = {}


def level_goal(k):
    return LEVEL_GOALS[k - 1] if k <= len(LEVEL_GOALS) else LEVEL_GOALS[-1] + 15000 * (k - len(LEVEL_GOALS))


def tint_tables(key):
    """Palette for (night level 0-6, doom?) - dusk bluish, doom ashen red."""
    if key in _TINTS:
        return _TINTS[key]
    night, doom = key

    def t(col):
        if night:
            col = lerp_color(col, "#0b1433", night * 0.09)
        if doom:
            col = lerp_color(col, "#5a3b33", 0.6)
        return col

    _TINTS[key] = ([t(c) for c in GROUND], [[t(c) for c in row] for row in BLADES], t(GROUND[3]))
    return _TINTS[key]


def fmt_time(ticks):
    s = int(ticks / FPS)
    return "%d:%02d" % (s // 60, s % 60)


class App:
    def __init__(self, root):
        self.root = root
        root.title("Jurassic Park - Mini Ecosystem Lab")
        root.configure(bg=BG)
        root.minsize(1000, 680)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        root.bind("<F11>", lambda e: self.toggle_fullscreen())
        root.bind("<Escape>", lambda e: root.attributes("-fullscreen", False))

        self.db = Database()
        self.sound = Ambience()
        self.vars = {"grass_rate": tk.DoubleVar(value=1.0), "repro": tk.DoubleVar(value=1.0),
                     "speed": tk.DoubleVar(value=1)}
        self.running = False
        self.frame = 0
        self.run_id = None
        self.buffer, self.samples = [], []
        self.last_status = ("", MUTED)
        self._resize_job = None
        self.blades_per_cell, self.sway_every = 3, 3
        self.mode = "jungle"
        self.night = 0
        self.tint_key = (0, False)
        self.ground, self.blades, _bg = tint_tables(self.tint_key)
        self.fx, self.flies, self.rain_items = [], [], []
        self.rain_frames = 0
        self.power_ready = {k: 0.0 for k in POWERS}
        self.achieved = set()
        self.new_game()

        self._style()
        self._build_ui()
        self.maximize()
        root.update()                                   # let Tk lay out the full-size window
        set_grid(self.canvas.winfo_width(), self.canvas.winfo_height())
        self.area_f = COLS * ROWS / 640.0
        self.start_h = min(150, max(8, int(BASE_H * self.area_f)))
        self.start_p = min(40, max(2, int(BASE_P * self.area_f)))
        self.world = World(self.start_h, self.start_p)
        self._build_grass()
        self._make_flies()
        self.canvas.bind("<Configure>", self.on_canvas_configure)
        self.samples.append(self._sample())
        self.update_stats()
        self.sound.prepare()
        self.root.after(300, self.init_db)
        self.loop()

    # -- game state ----------------------------------------------------------- #
    def new_game(self):
        self.score, self.level, self.streak = 0, 1, 0
        self.pred_births = 0
        self.low_herb = False
        self.toast_q, self.toast_cur, self.log = [], None, []

    def toast(self, title, sub="", color=GOLD):
        self.toast_q.append((title, sub, color))

    def log_add(self, text, color=TEXT):
        self.log.append([text, color, 360])
        self.log = self.log[-4:]

    def params(self):
        return {"grass_rate": round(self.vars["grass_rate"].get(), 2),
                "repro": round(self.vars["repro"].get(), 2),
                "speed": int(round(self.vars["speed"].get())),
                "pred_hunger": 1.0}

    def maximize(self):
        try:
            self.root.state("zoomed")                   # Windows
            return
        except tk.TclError:
            pass
        try:
            self.root.attributes("-zoomed", True)       # Linux
            return
        except tk.TclError:
            pass
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry("%dx%d+0+0" % (sw, sh - 80))  # macOS fallback

    def toggle_fullscreen(self):
        self.root.attributes("-fullscreen", not self.root.attributes("-fullscreen"))

    def _style(self):
        s = ttk.Style()
        s.theme_use("clam")
        s.configure("TFrame", background=PANEL)
        s.configure("TLabel", background=PANEL, foreground=TEXT, font=("Helvetica", 10))
        s.configure("Horizontal.TScale", background=PANEL, troughcolor="#0b1812")
        s.configure("TButton", background=CARD, foreground=TEXT, borderwidth=0, padding=(8, 5),
                    font=("Helvetica", 10, "bold"))
        s.map("TButton", background=[("active", "#2a4d3a")], foreground=[("disabled", "#5d7a69")])
        for name, bg, hover in (("Go", "#2e8b57", "#37a566"), ("Danger", "#8b3a3a", "#a84646"),
                                ("Herb", "#25506b", "#2f6a8e"), ("Pred", "#7a4a1a", "#9a5f24"),
                                ("Rain", "#2d5f8f", "#3a77b0"), ("Plague", "#5b3a78", "#74499a")):
            s.configure(name + ".TButton", background=bg, foreground="white")
            s.map(name + ".TButton", background=[("active", hover), ("disabled", "#2a3a33")],
                  foreground=[("disabled", "#6b8576")])
        s.configure("Sel.TButton", background="#2e8b57", foreground="white")
        s.configure("TCombobox", fieldbackground=CARD, background=CARD, foreground=TEXT,
                    arrowcolor=TEXT, selectbackground=CARD, selectforeground=TEXT)
        s.configure("Treeview", background=CARD, fieldbackground=CARD, foreground=TEXT, rowheight=24)
        s.configure("Treeview.Heading", background=PANEL, foreground=TEXT)
        s.map("Treeview", background=[("selected", "#2e8b57")])
        self.root.option_add("*TCombobox*Listbox.background", CARD)
        self.root.option_add("*TCombobox*Listbox.foreground", TEXT)

    def _build_ui(self):
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        left = tk.Frame(self.root, bg=BG)
        left.grid(row=0, column=0, sticky="nsew", padx=(14, 6), pady=10)
        right = tk.Frame(self.root, bg=PANEL, width=PANEL_W)
        right.grid(row=0, column=1, sticky="ns", padx=(6, 14), pady=10)
        right.pack_propagate(False)

        head = tk.Frame(left, bg=BG)
        head.pack(fill="x", pady=(0, 6))
        tk.Label(head, text="JURASSIC PARK", bg=BG, fg=C_GRASS, font=("Helvetica", 20, "bold")).pack(side="left")
        tk.Label(head, text="  keep the circle of life turning", bg=BG, fg=MUTED,
                 font=("Helvetica", 12, "italic")).pack(side="left", pady=(7, 0))
        self.db_label = tk.Label(head, text="DB: connecting...", bg=BG, fg=MUTED, font=("Helvetica", 10))
        self.db_label.pack(side="right")

        self.status = tk.Label(left, text="", bg=BG, fg=MUTED, font=("Helvetica", 12, "bold"), anchor="w")
        self.status.pack(side="bottom", fill="x", pady=(6, 0))
        tk.Label(left, text="Left-click the meadow: drop a herbivore   |   Right-click: release a lion or tiger"
                            "   |   F11: full screen", bg=BG, fg=MUTED, font=("Helvetica", 9)
                 ).pack(side="bottom", anchor="w")

        frame = tk.Frame(left, bg="#2a5a3a", padx=3, pady=3)
        frame.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(frame, width=700, height=420, bg=GROUND[3], highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Button-1>", lambda e: self.drop("cow", e))
        for b in ("<Button-2>", "<Button-3>"):
            self.canvas.bind(b, lambda e: self.drop(random.choice(("lion", "tiger")), e))

        # ---- right panel ----
        def section(title):
            tk.Label(right, text=title, bg=PANEL, fg=MUTED, font=("Helvetica", 9, "bold")).pack(
                anchor="w", padx=14, pady=(8, 2))

        cards = tk.Frame(right, bg=PANEL)
        cards.pack(fill="x", padx=10, pady=(8, 2))
        self.stat = {}
        for i, (key, title, color) in enumerate((("grass", "GRASS", C_GRASS), ("herb", "HERBIVORES", C_COW),
                                                  ("pred", "PREDATORS", C_PRED))):
            card = tk.Frame(cards, bg=CARD, padx=6, pady=4)
            card.grid(row=0, column=i, padx=3, sticky="ew")
            cards.columnconfigure(i, weight=1)
            tk.Label(card, text=title, bg=CARD, fg=MUTED, font=("Helvetica", 8, "bold")).pack()
            self.stat[key] = tk.Label(card, text="0", bg=CARD, fg=color, font=("Helvetica", 20, "bold"))
            self.stat[key].pack()
        self.sub = tk.Label(right, text="", bg=PANEL, fg=MUTED, font=("Helvetica", 9))
        self.sub.pack()

        self.graph = tk.Canvas(right, width=PANEL_W - 24, height=90, bg=CARD, highlightthickness=0)
        self.graph.pack(padx=12, pady=(4, 0))

        section("POPULATION  (instant)")
        for group, label, style in (("herb", "Herbivores", "Herb.TButton"), ("pred", "Predators", "Pred.TButton")):
            row = tk.Frame(right, bg=PANEL)
            row.pack(fill="x", padx=14, pady=2)
            tk.Label(row, text=label, bg=PANEL, fg=TEXT, font=("Helvetica", 11, "bold"), width=10,
                     anchor="w").pack(side="left")
            for n in (-10, -1, 1, 10):
                ttk.Button(row, text=("%+d" % n), style=style, width=4,
                           command=lambda g=group, k=n: self.adjust(g, k)).pack(side="left", padx=2)

        section("ENVIRONMENT  (instant)")
        self.readouts = {}
        for key, label in (("grass_rate", "Grass growth"), ("repro", "Breeding speed")):
            row = tk.Frame(right, bg=PANEL)
            row.pack(fill="x", padx=14)
            tk.Label(row, text=label, bg=PANEL, fg=TEXT, font=("Helvetica", 10)).pack(side="left")
            self.readouts[key] = tk.Label(row, text="", bg=PANEL, fg=C_GRASS, font=("Helvetica", 10, "bold"))
            self.readouts[key].pack(side="right")
            ttk.Scale(right, from_=0.1, to=3.0, variable=self.vars[key], orient="horizontal",
                      command=lambda _v, k=key: self._refresh_readout(k)).pack(fill="x", padx=14, pady=(0, 2))
            self._refresh_readout(key)

        row = tk.Frame(right, bg=PANEL)
        row.pack(fill="x", padx=14, pady=(4, 0))
        tk.Label(row, text="Speed", bg=PANEL, fg=TEXT, font=("Helvetica", 10)).pack(side="left")
        self.speed_btns = {}
        for sp in (4, 2, 1):
            b = ttk.Button(row, text="%dx" % sp, width=4, command=lambda v=sp: self.set_speed(v))
            b.pack(side="right", padx=2)
            self.speed_btns[sp] = b
        self.set_speed(1)

        section("SCENARIO  (restarts the world)")
        self.preset = ttk.Combobox(right, values=list(PRESETS), state="readonly", font=("Helvetica", 10))
        self.preset.set("Pick a scenario...")
        self.preset.pack(fill="x", padx=14)
        self.preset.bind("<<ComboboxSelected>>", self.apply_preset)

        section("NATURE'S POWERS")
        pw = tk.Frame(right, bg=PANEL)
        pw.pack(fill="x", padx=12)
        self.power_btns = {}
        for i, (key, (label, _cd)) in enumerate(POWERS.items()):
            style = {"rain": "Rain.TButton", "drought": "Danger.TButton", "plague": "Plague.TButton"}[key]
            b = ttk.Button(pw, text=label, style=style, command=lambda k=key: self.use_power(k))
            b.grid(row=0, column=i, sticky="ew", padx=2)
            pw.columnconfigure(i, weight=1)
            self.power_btns[key] = b

        btns = tk.Frame(right, bg=PANEL)
        btns.pack(fill="x", padx=12, pady=(12, 4))
        self.btn_run = ttk.Button(btns, text="Start", style="Go.TButton", command=self.toggle)
        self.btn_run.grid(row=0, column=0, sticky="ew", padx=2, pady=2)
        ttk.Button(btns, text="Reset", command=self.reset).grid(row=0, column=1, sticky="ew", padx=2, pady=2)
        self.btn_sound = ttk.Button(btns, text="Sound: On", command=self.toggle_sound)
        self.btn_sound.grid(row=0, column=2, sticky="ew", padx=2, pady=2)
        ttk.Button(btns, text="Database", command=self.db_dialog).grid(row=1, column=0, sticky="ew", padx=2, pady=2)
        ttk.Button(btns, text="History", command=self.history_window).grid(row=1, column=1, sticky="ew", padx=2, pady=2)
        ttk.Button(btns, text="Full screen", command=self.toggle_fullscreen).grid(
            row=1, column=2, sticky="ew", padx=2, pady=2)
        for i in range(3):
            btns.columnconfigure(i, weight=1)

    def _refresh_readout(self, key):
        self.readouts[key].config(text="%.2fx" % self.vars[key].get())

    def set_speed(self, v):
        self.vars["speed"].set(v)
        for sp, b in self.speed_btns.items():
            b.config(style="Sel.TButton" if sp == v else "TButton")

    def toggle_sound(self):
        on = self.sound.toggle()
        self.btn_sound.config(text="Sound: On" if on else "Sound: Off")

    # -- meadow items ----------------------------------------------------------- #
    def _build_grass(self):
        c = self.canvas
        cells = COLS * ROWS
        self.blades_per_cell = 3 if cells <= 900 else 2
        self.sway_every = 3 if cells <= 900 else 5
        self.bucket = [[-1] * COLS for _ in range(ROWS)]
        self.row_key = [self.tint_key] * ROWS
        self.bg_items, self.blade_items, self.blade_base = [], [], []
        nb = self.blades_per_cell
        for r in range(ROWS):
            bgs, blades, bases = [], [], []
            for col in range(COLS):
                x0, y0 = col * CELL, r * CELL
                bgs.append(c.create_rectangle(x0, y0, x0 + CELL, y0 + CELL, fill=self.ground[0], outline=""))
                items, base = [], []
                for k in range(nb):
                    bx = x0 + CELL * (0.25 + 0.54 * k / max(1, nb - 1)) + random.uniform(-2, 2)
                    by = y0 + CELL * random.uniform(0.78, 0.95)
                    base.append((bx, by, random.uniform(0, 6.28), (0.8, 1.0, 0.7)[k]))
                    items.append(c.create_line(bx, by, bx, by - 5, width=2, fill=self.blades[0][k],
                                               capstyle=tk.ROUND, state="hidden"))
                blades.append(items)
                bases.append(base)
            self.bg_items.append(bgs)
            self.blade_items.append(blades)
            self.blade_base.append(bases)

    def _make_flies(self):
        self.flies = []
        for _ in range(16):
            x, y = random.uniform(0, W), random.uniform(0, H)
            item = self.canvas.create_oval(x - 2, y - 2, x + 2, y + 2, fill="#f4f08a", outline="",
                                           state="hidden", tags=("fly",))
            self.flies.append([item, x, y, random.uniform(-.5, .5), random.uniform(-.5, .5)])

    def on_canvas_configure(self, _e):
        if self._resize_job:
            self.root.after_cancel(self._resize_job)
        self._resize_job = self.root.after(350, self.apply_size)

    def apply_size(self):
        self._resize_job = None
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if abs(w - W) < 4 and abs(h - H) < 4:
            return
        set_grid(w, h)
        self.world.resize()
        self.canvas.delete("all")
        for a in self.world.herbs + self.world.preds:
            a.rx = None
        self.world.graveyard.clear()
        self.fx, self.rain_items = [], []
        self._build_grass()
        self._make_flies()
        self._tint_flies()

    # -- DB -------------------------------------------------------------------- #
    def init_db(self):
        self.db.connect()
        self.refresh_db_label()

    def refresh_db_label(self):
        if self.db.ok:
            self.db_label.config(text="DB: connected (%s)" % self.db.cfg["database"], fg=OK)
        else:
            tip = self.db.error.split("\n")[0][:60] if self.db.error else "not connected"
            self.db_label.config(text="DB: offline - %s" % tip, fg=WARN)

    def db_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("MySQL connection")
        win.configure(bg=PANEL)
        win.resizable(False, False)
        entries = {}
        for i, (k, label) in enumerate((("host", "Host"), ("port", "Port"), ("user", "User"),
                                         ("password", "Password"), ("database", "Database"))):
            tk.Label(win, text=label, bg=PANEL, fg=TEXT).grid(row=i, column=0, sticky="w", padx=12, pady=5)
            e = tk.Entry(win, width=26, show="*" if k == "password" else "", bg=CARD, fg=TEXT,
                         insertbackground=TEXT, relief="flat")
            e.insert(0, str(self.db.cfg[k]))
            e.grid(row=i, column=1, padx=12, pady=5)
            entries[k] = e
        msg = tk.Label(win, text="", bg=PANEL, fg=MUTED, wraplength=260, justify="left")
        msg.grid(row=6, column=0, columnspan=2, padx=12)

        def go():
            cfg = {k: e.get().strip() for k, e in entries.items()}
            cfg["password"] = entries["password"].get()
            try:
                cfg["port"] = int(cfg["port"])
            except ValueError:
                cfg["port"] = 3306
            ok = self.db.connect(cfg)
            self.refresh_db_label()
            if ok:
                win.destroy()
            else:
                msg.config(text=self.db.error, fg=BAD)

        ttk.Button(win, text="Connect", style="Go.TButton", command=go).grid(
            row=7, column=0, columnspan=2, pady=12)

    def history_window(self):
        if not self.db.ok:
            messagebox.showinfo("Run history", "Connect to MySQL first (Database button).")
            return
        win = tk.Toplevel(self.root)
        win.title("Run history")
        win.configure(bg=PANEL)
        cols = ("id", "started", "herb", "pred", "grass", "breed", "ticks", "outcome")
        tree = ttk.Treeview(win, columns=cols, show="headings", height=8)
        for c, w in zip(cols, (40, 140, 50, 50, 55, 55, 65, 200)):
            tree.heading(c, text=c.capitalize())
            tree.column(c, width=w, anchor="center")
        tree.pack(padx=12, pady=(12, 6))
        cv = tk.Canvas(win, width=640, height=200, bg=CARD, highlightthickness=0)
        cv.pack(padx=12, pady=6)
        draw_graph(cv, [], 640, 200)

        def load():
            tree.delete(*tree.get_children())
            for r in self.db.list_runs():
                tree.insert("", "end", values=(r[0], str(r[1])[:19], r[2], r[3], r[4], r[5], r[6], r[7]))

        def show(_e=None):
            sel = tree.selection()
            if sel:
                draw_graph(cv, self.db.run_log(tree.item(sel[0])["values"][0]), 640, 200)

        def delete():
            sel = tree.selection()
            if sel and messagebox.askyesno("Delete", "Delete this run and its log?", parent=win):
                self.db.delete_run(tree.item(sel[0])["values"][0])
                load()

        tree.bind("<<TreeviewSelect>>", show)
        bar = tk.Frame(win, bg=PANEL)
        bar.pack(pady=(0, 12))
        ttk.Button(bar, text="Refresh", command=load).pack(side="left", padx=4)
        ttk.Button(bar, text="Delete run", style="Danger.TButton", command=delete).pack(side="left", padx=4)
        load()


    # -- user actions ------------------------------------------------------------ #
    def adjust(self, group, n):
        """Add or remove |n| herbivores / predators on the spot."""
        w = self.world
        if n > 0:
            for _ in range(n):
                kind = "cow" if group == "herb" else random.choice(("lion", "tiger"))
                w.add(kind, random.uniform(20, W - 20), random.uniform(20, H - 20))
        else:
            pool = w.herbs if group == "herb" else w.preds
            for _ in range(min(-n, len(pool))):
                w._kill(pool.pop(random.randrange(len(pool))))
        self.update_stats()

    def use_power(self, name):
        label, cooldown = POWERS[name]
        now = time.time()
        if now < self.power_ready[name]:
            return
        self.power_ready[name] = now + cooldown
        w = self.world
        if name == "rain":
            w.rain()
            self.rain_frames = FPS * 5
            self._make_rain()
            self.toast("Rain falls!", "The meadow drinks it up", "#7ec8ff")
            self.log_add("Rain! The grass surges back", "#7ec8ff")
        elif name == "drought":
            w.drought()
            self.toast("Drought!", "The grass withers away", WARN)
            self.log_add("Drought - the grass is dying", WARN)
        else:
            n = w.plague(0.4)
            self.toast("Plague!", "%d herbivores perish" % n, "#c58cff")
            self.log_add("Plague strikes the herd (-%d)" % n, "#c58cff")
        self.update_stats()

    def apply_preset(self, _e=None):
        h, p, grass, breed = PRESETS[self.preset.get()]
        f = self.area_f
        self.start_h = max(1, int(h * f))
        self.start_p = max(1, int(p * f)) if p else 0
        self.vars["grass_rate"].set(grass)
        self.vars["repro"].set(breed)
        for k in ("grass_rate", "repro"):
            self._refresh_readout(k)
        self.reset()

    def toggle(self):
        if not self.running and self.is_game_over():
            self.reset()
        self.running = not self.running
        if self.running and self.world.tick == 0:       # remember the starting line-up
            self.start_h, self.start_p = len(self.world.herbs), len(self.world.preds)
        if self.running and self.run_id is None and self.db.ok:
            p = self.params()
            p["init_h"], p["init_p"] = self.start_h, self.start_p
            self.run_id = self.db.start_run(p)
        self.btn_run.config(text="Pause" if self.running else "Resume")

    def is_game_over(self):
        return self.world.tick > 0 and not self.world.herbs and not self.world.preds

    def outcome(self):
        nh, npd = len(self.world.herbs), len(self.world.preds)
        if nh == 0 and npd == 0:
            return "Total collapse - all animals died"
        if nh == 0:
            return "Herbivores extinct - predators doomed"
        if npd == 0:
            return "Predators extinct - herbivores only"
        return "Both species alive (%d ticks)" % self.world.tick

    def finish_run(self, outcome=None):
        if self.run_id is not None:
            self.db.flush(self.buffer)
            self.db.end_run(self.run_id, self.world.tick, outcome or self.outcome())
        self.buffer, self.run_id = [], None

    def reset(self):
        self.finish_run()
        for a in self.world.herbs + self.world.preds + self.world.graveyard:
            self.canvas.delete(a.tag)
        self.clear_fx()
        self.world = World(self.start_h, self.start_p)
        self.new_game()
        self.samples = [self._sample()]
        self.running = False
        self.btn_run.config(text="Start")
        self.bucket = [[-1] * COLS for _ in range(ROWS)]
        self.update_stats()

    def drop(self, kind, e):
        self.world.add(kind, e.x, e.y)

    def _sample(self):
        w = self.world
        return (w.tick, round(w.grass_pct(), 1), len(w.herbs), len(w.preds))

    # -- game logic -------------------------------------------------------------------- #
    def game_tick(self):
        w = self.world
        if w.herbs and w.preds:
            self.streak += 1
            if w.tick % 5 == 0:
                self.score += self.level
        else:
            self.streak = 0
        if self.streak >= level_goal(self.level):
            self.score += 500 * self.level
            self.toast("LEVEL %d COMPLETE" % self.level, "+%d bonus points" % (500 * self.level))
            self.log_add("Level %d complete!" % self.level, GOLD)
            self.level += 1
        if w.tick % 30 == 0:
            self.check_achievements()

    def check_achievements(self):
        w = self.world
        nh, npd, gp = len(w.herbs), len(w.preds), w.grass_pct()
        if nh < 8 and w.tick > 300:
            self.low_herb = True
        conds = {"first_hunt": w.kills >= 1, "cub": self.pred_births >= 1, "herd": nh >= 100,
                 "pride": npd >= 12, "lush": gp >= 85 and nh >= 40, "survivor": self.streak >= 3000,
                 "comeback": self.low_herb and nh >= 30}
        for key, ok in conds.items():
            if ok and key not in self.achieved:
                self.achieved.add(key)
                title, sub = ACH[key]
                self.score += 150
                self.toast("ACHIEVEMENT: " + title, sub + "  (+150)")
                self.log_add("Achievement - " + title, GOLD)

    def consume_events(self):
        w = self.world
        for ev in w.events:
            kind, x, y = ev[0], ev[1], ev[2]
            if kind == "birth_h":
                self.score += 1
                self.spawn_text("\u2665", x, y - 12, "#ff8fb3", 26, 12)
            elif kind == "birth_p":
                self.score += 10
                self.pred_births += 1
                self.spawn_text("\u2605", x, y - 12, GOLD, 30, 14)
                self.log_add("A %s cub is born" % ev[3], C_PRED)
            elif kind == "kill":
                self.spawn_burst(x, y)
                if random.random() < 0.35:
                    self.spawn_text("chomp!", x, y - 14, "#ff9a8b", 24, 9)
        w.events.clear()

    # -- particles ------------------------------------------------------------------------ #
    def spawn_text(self, text, x, y, color, life, size):
        if len(self.fx) > 140:
            return
        item = self.canvas.create_text(x, y, text=text, fill=color, font=("Helvetica", size, "bold"), tags=("fx",))
        self.fx.append([item, 0.0, -0.7, life])

    def spawn_burst(self, x, y):
        if len(self.fx) > 140:
            return
        for _ in range(5):
            r = random.uniform(1.5, 3)
            item = self.canvas.create_oval(x - r, y - r, x + r, y + r, tags=("fx",),
                                           fill=random.choice(("#e8453c", "#ff8a4c", "#ffd166")), outline="")
            self.fx.append([item, random.uniform(-2, 2), random.uniform(-2.2, 1.2), 14])

    def update_fx(self):
        c = self.canvas
        alive = []
        for p in self.fx:
            p[3] -= 1
            if p[3] <= 0:
                c.delete(p[0])
            else:
                c.move(p[0], p[1], p[2])
                alive.append(p)
        self.fx = alive

    def clear_fx(self):
        for p in self.fx:
            self.canvas.delete(p[0])
        self.fx = []
        for r in self.rain_items:
            self.canvas.delete(r[0])
        self.rain_items, self.rain_frames = [], 0

    def _make_rain(self):
        for r in self.rain_items:
            self.canvas.delete(r[0])
        self.rain_items = []
        for _ in range(70):
            x, y = random.uniform(0, W), random.uniform(0, H)
            item = self.canvas.create_line(x, y, x - 3, y + 11, fill="#9ed2ff", width=1, tags=("fx",))
            self.rain_items.append([item, x, y])

    def update_rain(self):
        if not self.rain_items:
            return
        c = self.canvas
        self.rain_frames -= 1
        if self.rain_frames <= 0:
            for r in self.rain_items:
                c.delete(r[0])
            self.rain_items = []
            return
        for r in self.rain_items:
            r[2] += 16
            r[1] -= 3
            if r[2] > H:
                r[1], r[2] = random.uniform(0, W + 40), random.uniform(-30, 0)
            c.coords(r[0], r[1], r[2], r[1] - 3, r[2] + 11)

    def update_flies(self):
        if not (self.night >= 3 or self.mode == "death"):
            return
        c = self.canvas
        for f in self.flies:
            f[3] = max(-1.0, min(1.0, f[3] + random.uniform(-.08, .08)))
            f[4] = max(-1.0, min(1.0, f[4] + random.uniform(-.08, .08)))
            f[1] = (f[1] + f[3]) % W
            f[2] = (f[2] + f[4]) % H
            c.coords(f[0], f[1] - 2, f[2] - 2, f[1] + 2, f[2] + 2)

    def _tint_flies(self):
        show = self.night >= 3 or self.mode == "death"
        color = "#ff6a3c" if self.mode == "death" else "#f4f08a"
        for f in self.flies:
            self.canvas.itemconfigure(f[0], state="normal" if show else "hidden", fill=color)

    def update_tint(self):
        d = 0.5 + 0.5 * math.cos(2 * math.pi * self.frame / (FPS * 75))      # 75 s day/night cycle
        self.night = int(round((1 - d) * 6))
        key = (self.night, self.mode == "death")
        if key != self.tint_key:
            self.tint_key = key
            self.ground, self.blades, bg = tint_tables(key)
            self.canvas.configure(bg=bg)
            self._tint_flies()

    # -- HUD ---------------------------------------------------------------------------------- #
    def draw_hud(self):
        c = self.canvas
        c.delete("hud")
        tag = ("hud",)
        f = ("Helvetica", 9, "bold")

        # score / level / progress
        c.create_rectangle(12, 12, 340, 104, fill=HUD_BG, outline="#2f7a52", width=2, tags=tag)
        c.create_text(26, 24, anchor="w", text="SCORE", fill=MUTED, font=f, tags=tag)
        c.create_text(26, 46, anchor="w", text=str(self.score), fill=C_GRASS, font=("Helvetica", 20, "bold"), tags=tag)
        c.create_text(190, 24, anchor="w", text="LEVEL %d" % self.level, fill=GOLD, font=("Helvetica", 11, "bold"), tags=tag)
        c.create_text(190, 44, anchor="w", text="keep both species alive", fill=TEXT, font=("Helvetica", 9), tags=tag)
        goal = level_goal(self.level)
        prev = level_goal(self.level - 1) if self.level > 1 else 0
        frac = max(0.0, min(1.0, (self.streak - prev) / float(goal - prev)))
        c.create_rectangle(26, 68, 326, 80, fill=CARD, outline="#2f7a52", tags=tag)
        if frac > 0:
            c.create_rectangle(26, 68, 26 + 300 * frac, 80, fill=lerp_color("#f2b45a", "#7bd88f", frac), outline="", tags=tag)
        c.create_text(26, 92, anchor="w", fill=MUTED, font=("Helvetica", 8), tags=tag,
                      text="balanced for %s   -   next level at %s" % (fmt_time(self.streak), fmt_time(goal)))

        # day / night clock
        x0 = W - 150
        c.create_rectangle(x0, 12, W - 12, 56, fill=HUD_BG, outline="#2f7a52", width=2, tags=tag)
        night = self.night
        if night >= 4:
            c.create_oval(x0 + 12, 22, x0 + 36, 46, fill="#dfe6f5", outline="", tags=tag)
            c.create_oval(x0 + 20, 20, x0 + 44, 44, fill=HUD_BG, outline="", tags=tag)
            label = "Night"
        else:
            col = "#ffd166" if night <= 1 else "#ff9f5a"
            c.create_oval(x0 + 14, 24, x0 + 34, 44, fill=col, outline="", tags=tag)
            label = "Day" if night <= 1 else "Dusk"
        c.create_text(x0 + 56, 34, anchor="w", text=label, fill=TEXT, font=("Helvetica", 11, "bold"), tags=tag)

        # toast
        if self.toast_cur:
            title, sub, color, _ttl = self.toast_cur
            cx = W / 2
            c.create_rectangle(cx - 230, 14, cx + 230, 70, fill=HUD_BG, outline=color, width=2, tags=tag)
            c.create_text(cx, 34, text=title, fill=color, font=("Helvetica", 14, "bold"), tags=tag)
            c.create_text(cx, 54, text=sub, fill=TEXT, font=("Helvetica", 10), tags=tag)

        # event log
        for i, (text, color, _ttl) in enumerate(reversed(self.log)):
            t = c.create_text(20, H - 14 - i * 20, anchor="sw", text=text, fill=color,
                              font=("Helvetica", 10, "bold"), tags=tag)
            bb = c.bbox(t)
            if bb:
                bg = c.create_rectangle(bb[0] - 6, bb[1] - 2, bb[2] + 6, bb[3] + 2, fill=HUD_BG, outline="", tags=tag)
                c.tag_lower(bg, t)

        # centre cards
        w = self.world
        card = None
        if w.tick == 0 and not self.running:
            card = ("Welcome to the wild", "Press START - then rain, plague and population buttons are yours to wield.\n"
                    "Keep herbivores AND predators alive to climb the levels.", C_GRASS)
        elif self.is_game_over():
            card = ("THE WORLD HAS FALLEN SILENT", "Final score %d  -  reached level %d  -  %s survived.\n"
                    "Press Start or pick a scenario to try again." % (self.score, self.level, fmt_time(w.tick)), BAD)
        elif not self.running:
            card = ("PAUSED", "Press Resume to continue.", WARN)
        if card:
            cx, cy = W / 2, H / 2
            c.create_rectangle(cx - 280, cy - 60, cx + 280, cy + 60, fill=HUD_BG, outline=card[2], width=3, tags=tag)
            c.create_text(cx, cy - 28, text=card[0], fill=card[2], font=("Helvetica", 20, "bold"), tags=tag)
            c.create_text(cx, cy + 14, text=card[1], fill=TEXT, font=("Helvetica", 10), justify="center", tags=tag)

    def tick_hud_state(self):
        for entry in self.log:
            entry[2] -= 1
        self.log = [e for e in self.log if e[2] > 0]
        if self.toast_cur:
            self.toast_cur[3] -= 1
            if self.toast_cur[3] <= 0:
                self.toast_cur = None
        if self.toast_cur is None and self.toast_q:
            title, sub, color = self.toast_q.pop(0)
            self.toast_cur = [title, sub, color, FPS * 4]

    # -- main loop ---------------------------------------------------------------- #
    def loop(self):
        t0 = time.time()
        if self.running:
            p = self.params()
            for _ in range(p["speed"]):
                self.world.step(p)
                self.game_tick()
                if self.world.tick % 10 == 0:
                    s = self._sample()
                    self.samples.append(s)
                    if self.run_id is not None:
                        self.buffer.append((self.run_id,) + s)
                        if len(self.buffer) >= 60:
                            self.db.flush(self.buffer)
                            self.buffer = []
                if not self.world.herbs and not self.world.preds:
                    self.running = False
                    self.btn_run.config(text="Start")
                    self.samples.append(self._sample())
                    self.finish_run()
                    break
        self.render()
        wait = max(1, int(1000 / FPS - (time.time() - t0) * 1000))
        self.root.after(wait, self.loop)

    # -- rendering ------------------------------------------------------------------ #
    def render(self):
        self.frame += 1
        c, f = self.canvas, self.frame
        if f % 15 == 0:
            self.update_tint()
        if f % self.sway_every == 0:
            self._draw_grass(f / FPS)

        for a in self.world.graveyard:
            c.delete(a.tag)
        self.world.graveyard.clear()

        for a in self.world.herbs + self.world.preds:
            pose = ((f // 7) + a.id) % 2 if a.moving else 0
            if a.rx is None or a.rface != a.face or a.rpose != pose:
                c.delete(a.tag)
                draw_animal(c, a, pose)
                a.rface, a.rpose = a.face, pose
            else:
                dx, dy = a.x - a.rx, a.y - a.ry
                if dx or dy:
                    c.move(a.tag, dx, dy)
            a.rx, a.ry = a.x, a.y

        self.consume_events()
        self.update_fx()
        self.update_rain()
        self.update_flies()
        self.tick_hud_state()
        if f % 4 == 0 or self.toast_cur is not None and f % 2 == 0:
            self.draw_hud()
        try:
            c.tag_raise("fly")
            c.tag_raise("fx")
            c.tag_raise("hud")
        except tk.TclError:
            pass

        if f % 6 == 0:
            self.update_stats()
        if f % 15 == 0:
            draw_graph(self.graph, self.samples, PANEL_W - 24, 90)

    def _draw_grass(self, t):
        c, g = self.canvas, self.world.grass
        sin = math.sin
        refreshed = 0
        for r in range(min(ROWS, len(self.bucket))):
            grow, bucket = g[r], self.bucket[r]
            if self.row_key[r] != self.tint_key and refreshed < 4:   # repaint a few rows per pass
                refreshed += 1
                self.row_key[r] = self.tint_key
                for col in range(len(bucket)):
                    bucket[col] = -1
            for col in range(min(COLS, len(bucket))):
                v = grow[col]
                b = 0 if v < 0.05 else 1 + int(min(v, 0.999) * 5)
                if b != bucket[col]:
                    bucket[col] = b
                    c.itemconfigure(self.bg_items[r][col], fill=self.ground[b])
                    for k, item in enumerate(self.blade_items[r][col]):
                        if b == 0:
                            c.itemconfigure(item, state="hidden")
                        else:
                            c.itemconfigure(item, state="normal", fill=self.blades[b][k])
                if b:
                    amp = 1.5 + 3.0 * v
                    height = 5 + 17 * v
                    for item, (bx, by, ph, hv) in zip(self.blade_items[r][col], self.blade_base[r][col]):
                        sway = sin(t * 2.2 + col * 0.55 + r * 0.35 + ph) * amp
                        c.coords(item, bx, by, bx + sway, by - height * hv)

    def update_stats(self):
        w = self.world
        nh, npd, gp = len(w.herbs), len(w.preds), w.grass_pct()
        lions = sum(1 for q in w.preds if q.kind == "lion")
        self.stat["grass"].config(text="%d%%" % gp)
        self.stat["herb"].config(text=str(nh))
        self.stat["pred"].config(text=str(npd))
        self.sub.config(text="lions %d  -  tigers %d  -  time %s" % (lions, npd - lions, fmt_time(w.tick)))

        # soundtrack + mood: the herbivores are gone -> the ecosystem has failed -> funeral music
        mode = "death" if (w.tick > 0 and nh == 0) else "jungle"
        if mode != self.mode:
            old, self.mode = self.mode, mode
            self.sound.set_mode(mode)
            self.update_tint()
            self._tint_flies()
            if mode == "death":
                self.toast("THE ECOSYSTEM HAS FAILED", "The herbivores are gone. The end is near...", BAD)
                self.log_add("The last herbivore is gone", BAD)
            elif mode == "jungle" and old == "death":
                self.toast("Life returns", "The jungle stirs again", OK)

        now = time.time()
        for key, b in self.power_btns.items():
            rem = self.power_ready[key] - now
            if rem > 0:
                b.config(text="%s %ds" % (POWERS[key][0], int(rem) + 1))
                b.state(["disabled"])
            else:
                b.config(text=POWERS[key][0])
                b.state(["!disabled"])

        if w.tick == 0 and not self.running:
            msg, col = "Press Start. Can this little world keep itself alive?", MUTED
        elif nh == 0 and npd == 0:
            msg, col = "Total collapse - every animal has died. Try a different scenario.", BAD
        elif nh == 0:
            msg, col = "The herbivores are extinct - the predators will starve.", BAD
        elif npd == 0:
            msg, col = "The predators are extinct - the herbivores are free to overgraze.", WARN
        elif gp < 15:
            msg, col = "Overgrazing! The grass is almost gone - herbivores will starve.", WARN
        elif nh < 6:
            msg, col = "Herbivores are nearly wiped out - predators are in danger.", WARN
        else:
            msg, col = "Ecosystem alive - %s survived." % fmt_time(w.tick), OK
        if (msg, col) != self.last_status:
            self.status.config(text=msg, fg=col)
            self.last_status = (msg, col)

    def on_close(self):
        self.sound.stop()
        if self.run_id is not None:
            self.finish_run()
        self.db.close()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
