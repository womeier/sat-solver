#!/usr/bin/env python3
"""Emits docs/scaling{,-dark}.svg from docs/scaling.csv.

The dataset is a file rather than a table in this script: twenty-odd rows
transcribed by hand is twenty-odd chances to mistype a number that nothing would
catch. `just satlib-scaling` re-measures it and redraws both files.

Colors are literal presentation attributes, not CSS custom properties: librsvg
(and GitHub's SVG sanitizer) do not resolve `var()`, which renders the whole
figure black. Dark mode is therefore a second file, swapped by `<picture>` in the
README, with its own steps from the same ramps.

  python3 docs/make_scaling_svg.py           # write both SVGs
  python3 docs/make_scaling_svg.py --check   # ASCII preview + layout assertions
  python3 docs/make_scaling_svg.py --alt     # the README's alt text, same source

`--check` exists because there is no SVG renderer in this repo's dev shell. It
verifies the data -> coordinate mapping and that nothing lands outside the canvas,
which is what silently breaks when the dataset grows a row.

**What is plotted is the median over the instances solved inside the cap**, not
the mean. A per-instance cap censors the slow tail, so a mean is wrong by exactly
the instances it could not see; the median is exact as long as more than half the
set came in under the cap, and that is also the rule for where a curve stops.
"""
import csv
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CSV = os.path.join(HERE, "scaling.csv")

# Color by solver, marker by solver, dash by verdict: identity never rests on
# color alone. Fastest first.
SOLVERS = [("cdcl", "circle", 0), ("dpll", "square", 1), ("naive", "triangle", 2)]
VERDICTS = [("SAT", None), ("UNSAT", "5 3")]

THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781",
                  grid="#e1e0d9", axis="#c3c2b7",
                  series=("#2a78d6", "#eb6834", "#1baf7a")),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781",
                 grid="#2c2c2a", axis="#383835",
                 series=("#3987e5", "#d95926", "#199e70")),
}

W, H = 780, 476
PLOT_L, PLOT_R = 74.0, 596.0
PLOT_T, PLOT_B = 132.0, 404.0

X_LO, X_HI = 10, 262
# The axis tops out at the per-instance budget on purpose: the top gridline *is*
# the cap, so "how close is this curve to falling off" is readable directly.
Y_LO, Y_HI = -5.0, 1.0  # log10 seconds: 10 µs .. 10 s
Y_TICKS = [(1e-5, "10 µs"), (1e-4, "100 µs"), (1e-3, "1 ms"), (1e-2, "10 ms"),
           (1e-1, "100 ms"), (1e0, "1 s"), (1e1, "10 s")]
FONT = "system-ui, -apple-system, 'Segoe UI', sans-serif"


class Row:
    """One (solver, set) cell of the dataset, times in seconds."""

    def __init__(self, d):
        self.solver = d["solver"].strip()
        self.set = d["set"].strip()
        self.vars = int(d["vars"])
        self.verdict = d["verdict"].strip()
        self.solved = int(d["solved"])
        self.attempted = int(d["attempted"])
        self.median = self._s(d["median_ms"])
        self.mean = self._s(d["mean_ms"])
        self.worst = self._s(d["worst_ms"])

    @staticmethod
    def _s(cell):
        cell = (cell or "").strip()
        return float(cell) / 1e3 if cell else None

    @property
    def usable(self):
        """True when the median is exact: more than half the set came in."""
        return self.solved * 2 > self.attempted

    @property
    def fraction(self):
        return f"{self.solved}/{self.attempted}"


def load(path=CSV):
    with open(path, newline="") as f:
        return [Row(d) for d in csv.DictReader(f)]


def series(rows, solver, verdict):
    got = [r for r in rows if r.solver == solver and r.verdict == verdict]
    return sorted(got, key=lambda r: r.vars)


def x_of(v):
    return PLOT_L + (v - X_LO) / (X_HI - X_LO) * (PLOT_R - PLOT_L)


def y_of(sec):
    t = (math.log10(sec) - Y_LO) / (Y_HI - Y_LO)
    return PLOT_B - t * (PLOT_B - PLOT_T)


def fmt(sec):
    if sec is None:
        return "—"
    if sec < 1e-3:
        return f"{sec * 1e6:.0f} µs"
    if sec < 1e-2:
        return f"{sec * 1e3:.2f} ms"
    if sec < 1:
        return f"{sec * 1e3:.1f} ms"
    return f"{sec:.2f} s" if sec < 10 else f"{sec:.1f} s"


def growth(rows):
    """Cost multiplier per +25 variables, from the endpoints of a series.

    Endpoints rather than a least-squares fit on log10(time): the claim being made
    is "about N times per 25 variables across this range", and a reader can check
    that against two numbers in the table instead of trusting a regression.
    """
    pts = [r for r in rows if r.usable]
    if len(pts) < 2 or pts[0].vars == pts[-1].vars:
        return None
    lo, hi = pts[0], pts[-1]
    return 10 ** (math.log10(hi.median / lo.median) / (hi.vars - lo.vars) * 25)


def describe(rows):
    """The `<desc>`, generated from the same numbers the lines are drawn from."""
    out = ["Median solve time per instance against the number of variables, on a logarithmic "
           "time axis, over SATLIB uniform random 3-SAT at the phase transition (clause to "
           "variable ratio 4.26). Satisfiable sets are drawn solid, unsatisfiable dashed. Each "
           "instance had a ten-second budget; a curve stops where fewer than half the set fits "
           "in it."]
    for name, _, _ in SOLVERS:
        for verdict, _ in VERDICTS:
            s = series(rows, name, verdict)
            ok = [r for r in s if r.usable]
            if not ok:
                if s:
                    out.append(f"{name} solves none of the {verdict.lower()} sets within the "
                               f"budget, from {s[0].vars} variables up.")
                continue
            if len(ok) == 1:
                bit = (f"{name} manages only the {ok[0].vars}-variable {verdict.lower()} set, "
                       f"at {fmt(ok[0].median)}")
            else:
                bit = (f"{name} on {verdict.lower()} sets runs from {fmt(ok[0].median)} at "
                       f"{ok[0].vars} variables to {fmt(ok[-1].median)} at {ok[-1].vars}")
                g = growth(s)
                if g:
                    bit += f", about {g:.1f} times per 25 variables"
            beyond = [r for r in s if r.vars > ok[-1].vars]
            if beyond:
                bit += (f", and at {beyond[0].vars} variables solves only "
                        f"{beyond[0].fraction} in the budget")
            out.append(bit + ".")
    return " ".join(out)


def text(x, y, s, fill, size, weight=None, anchor=None, style=None, spacing=None):
    bits = [f'x="{x:.1f}"', f'y="{y:.1f}"', f'fill="{fill}"', f'font-size="{size}"']
    if weight:
        bits.append(f'font-weight="{weight}"')
    if anchor:
        bits.append(f'text-anchor="{anchor}"')
    if style:
        bits.append(f'font-style="{style}"')
    if spacing:
        bits.append(f'letter-spacing="{spacing}"')
    return f'<text {" ".join(bits)}>{s}</text>'


def marker(shape, cx, cy, color, surface):
    """Series color with a 2px surface ring, so crossing lines stay readable."""
    r = 3.6
    if shape == "circle":
        geo = f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}"'
    elif shape == "square":
        s = r * 1.78
        geo = (f'<rect x="{cx - s / 2:.1f}" y="{cy - s / 2:.1f}" '
               f'width="{s:.1f}" height="{s:.1f}" rx="1"')
    else:
        h = r * 1.95
        pts = (f"{cx:.1f},{cy - h * 0.62:.1f} {cx + h * 0.6:.1f},{cy + h * 0.45:.1f} "
               f"{cx - h * 0.6:.1f},{cy + h * 0.45:.1f}")
        geo = f'<polygon points="{pts}"'
    return (f'{geo} fill="none" stroke="{surface}" stroke-width="2"/>'
            f'{geo} fill="{color}"/>')


def build(theme_name, rows):
    t = THEMES[theme_name]
    surface, ink, ink2, muted = t["surface"], t["ink"], t["ink2"], t["muted"]
    colors = t["series"]
    xs = sorted({r.vars for r in rows})
    out = []
    a = out.append

    a(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
      f'role="img" aria-labelledby="figTitle figDesc" font-family="{FONT}">')
    a('<title id="figTitle">How the three solvers scale with problem size</title>')
    a(f'<desc id="figDesc">{describe(rows)}</desc>')
    a(f'<rect x="0" y="0" width="{W}" height="{H}" fill="{surface}"/>')

    a(text(24, 34, "How the three solvers scale", ink, 15, weight=600))
    a(text(24, 53, "Median solve time per instance · SATLIB uniform random 3-SAT at the phase "
                   "transition (ratio 4.26)", ink2, 11.5))
    a(text(24, 71, "Solid: satisfiable.  Dashed: unsatisfiable.  10 s per instance; a curve ends "
                   "where under half the set fits in that,", muted, 10.5))
    a(text(24, 86, "and its last point says how much of that set it did solve.", muted, 10.5))

    lx = 24.0
    for name, shape, ci in SOLVERS:
        a(f'<line x1="{lx:.1f}" y1="106" x2="{lx + 22:.1f}" y2="106" '
          f'stroke="{colors[ci]}" stroke-width="1.8"/>')
        a(marker(shape, lx + 11, 106, colors[ci], surface))
        a(text(lx + 29, 110, name, ink2, 11.5))
        lx += 29 + 6.9 * len(name) + 20

    for v, label in Y_TICKS:
        gy = y_of(v)
        a(f'<line x1="{PLOT_L:.1f}" y1="{gy:.1f}" x2="{PLOT_R:.1f}" y2="{gy:.1f}" '
          f'stroke="{t["grid"]}" stroke-width="1"/>')
        a(text(PLOT_L - 8, gy + 3.5, label, muted, 10.5, anchor="end"))
    for v in xs:
        gx = x_of(v)
        a(f'<line x1="{gx:.1f}" y1="{PLOT_B:.1f}" x2="{gx:.1f}" y2="{PLOT_B + 4:.1f}" '
          f'stroke="{t["axis"]}" stroke-width="1"/>')
        a(text(gx, PLOT_B + 18, str(v), muted, 10.5, anchor="middle"))
    a(f'<line x1="{PLOT_L:.1f}" y1="{PLOT_B:.1f}" x2="{PLOT_R:.1f}" y2="{PLOT_B:.1f}" '
      f'stroke="{t["axis"]}" stroke-width="1"/>')
    a(text((PLOT_L + PLOT_R) / 2, PLOT_B + 38, "variables", ink2, 11, anchor="middle"))

    labels = []
    for name, shape, ci in SOLVERS:
        for verdict, dash in VERDICTS:
            s = series(rows, name, verdict)
            ok = [r for r in s if r.usable]
            if not ok:
                continue
            pts = [(x_of(r.vars), y_of(r.median)) for r in ok]
            d = " ".join(("M" if i == 0 else "L") + f"{x:.1f} {y:.1f}"
                         for i, (x, y) in enumerate(pts))
            extra = f' stroke-dasharray="{dash}"' if dash else ""
            a(f'<path d="{d}" fill="none" stroke="{colors[ci]}" stroke-width="1.8" '
              f'stroke-linecap="round" stroke-linejoin="round"{extra}/>')
            for x, y in pts:
                a(marker(shape, x, y, colors[ci], surface))

            # Whisker to the slowest instance that did finish: the tail grows
            # faster than the median does, and the median alone hides that.
            last = ok[-1]
            if last.worst is not None and last.worst > last.median:
                xw = pts[-1][0]
                yw = max(y_of(last.worst), PLOT_T)
                a(f'<line x1="{xw:.1f}" y1="{pts[-1][1]:.1f}" x2="{xw:.1f}" y2="{yw:.1f}" '
                  f'stroke="{colors[ci]}" stroke-width="1.5" opacity="0.45"/>')
                a(f'<line x1="{xw - 3:.1f}" y1="{yw:.1f}" x2="{xw + 3:.1f}" y2="{yw:.1f}" '
                  f'stroke="{colors[ci]}" stroke-width="1.5" opacity="0.45"/>')

            tag = f"{name} {verdict.lower()}"
            if last.solved < last.attempted:
                tag += f" ({last.fraction})"
            labels.append((pts[-1][0], pts[-1][1], tag, colors[ci]))


    # End-of-line labels. A label is only pushed down when it would actually
    # touch an earlier one -- which means overlapping in *both* axes, since these
    # lines end at different variable counts. Nudging on y alone moved labels 20px
    # off the endpoint they name, for collisions that were never going to happen.
    def box(lbl):
        x, y, s, _ = lbl
        return (x + 9, x + 9 + 6.3 * len(s), y)

    labels.sort(key=lambda p: p[1])
    for i in range(1, len(labels)):
        x, y, s, c = labels[i]
        x0, x1, _ = box(labels[i])
        for j in range(i):
            px0, px1, py = box(labels[j])
            if y - py < 13 and x0 < px1 and px0 < x1:
                y = py + 13
                x0, x1 = x + 9, x + 9 + 6.3 * len(s)
        labels[i] = (x, y, s, c)
    for x, y, s, c in labels:
        a(text(x + 9, y + 4, s, c, 11.5))

    a(text(24, H - 20, "Logarithmic time axis, so a straight line is exponential growth. Release "
                       "build, one instance at a time, in a fresh process each. Dataset: "
                       "docs/scaling.csv.", muted, 10.5))
    a('</svg>')
    return "\n".join(out)


def check(rows):
    """ASCII preview and layout assertions, in place of a renderer."""
    print(f"{'solver':6} {'verdict':7} {'vars':>4} {'solved':>7} {'median':>10} "
          f"{'mean':>10} {'worst':>10}")
    for r in sorted(rows, key=lambda r: (r.solver, r.verdict, r.vars)):
        flag = "" if r.usable else "  (censored)"
        print(f"{r.solver:6} {r.verdict:7} {r.vars:>4} {r.fraction:>7} {fmt(r.median):>10} "
              f"{fmt(r.mean):>10} {fmt(r.worst):>10}{flag}")

    print()
    for name, _, _ in SOLVERS:
        for verdict, _ in VERDICTS:
            g = growth(series(rows, name, verdict))
            if g:
                print(f"{name:6} {verdict:7} x{g:.2f} per +25 vars")

    drawn = [r for r in rows if r.usable]
    assert drawn, "nothing is usable: every set is censored"
    lo = min(r.median for r in drawn)
    hi = max(r.worst or r.median for r in drawn)
    assert 10 ** Y_LO <= lo, f"y axis starts above the fastest point ({fmt(lo)})"
    if hi > 10 ** Y_HI:
        print(f"note: worst instance {fmt(hi)} is above the axis; its whisker is clipped")
    for r in rows:
        assert X_LO <= r.vars <= X_HI, f"{r.vars} variables is off the x axis"
    ys = sorted(y_of(v) for v, _ in Y_TICKS)
    assert min(b - a for a, b in zip(ys, ys[1:])) > 12, "y tick labels would collide"
    xs = sorted({r.vars for r in rows})
    assert min(x_of(b) - x_of(a) for a, b in zip(xs, xs[1:])) > 20, \
        "x tick labels would collide"
    print(f"\nplot box x {PLOT_L}..{PLOT_R}, y {PLOT_T}..{PLOT_B} in {W}x{H}: ok")


if __name__ == "__main__":
    data = load()
    if "--alt" in sys.argv:
        # GitHub renders the `<img alt>`, not the SVG's `<desc>`, so the README
        # needs its own copy of the same sentence -- generated, not retyped.
        print(describe(data))
    elif "--check" in sys.argv:
        check(data)
    else:
        for theme, name in (("light", "scaling.svg"), ("dark", "scaling-dark.svg")):
            with open(os.path.join(HERE, name), "w") as f:
                f.write(build(theme, data) + "\n")
            print(f"wrote docs/{name}", file=sys.stderr)
