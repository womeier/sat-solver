#!/usr/bin/env python3
"""Emits docs/benchmarks{,-dark}.svg from the `figure_data` dataset.

Colors are written as literal presentation attributes, not CSS custom
properties: librsvg (and GitHub's SVG sanitizer) do not resolve `var()`, which
renders the whole figure black. Dark mode is therefore a second file, swapped by
`<picture>` in the README, with its own steps from the same ramps.
"""
import math
import sys

SERIES = [  # label, shape; colors come from the theme
    ("dpll", "circle"),
    ("naive", "square"),
]

GROUPS = [
    ("uf20-91", "20 variables · 91 clauses · satisfiable", {
        "dpll": (0.15778, 0.50968),
        "naive": (192.456, 559.615),
    }),
    ("uf50-218", "50 variables · 218 clauses · satisfiable", {
        "dpll": (5.69549, 20.35636),
        "naive": None,
    }),
    ("uuf50-218", "50 variables · 218 clauses · unsatisfiable", {
        "dpll": (15.75463, 58.92630),
        "naive": None,
    }),
]

THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781",
                  grid="#e1e0d9", axis="#c3c2b7",
                  series=("#2a78d6", "#eb6834", "#1baf7a")),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781",
                 grid="#2c2c2a", axis="#383835",
                 series=("#3987e5", "#d95926", "#199e70")),
}

W = 780
PLOT_L, PLOT_R = 168.0, 636.0
MEAN_COL, WORST_COL = 700.0, 764.0
DOM_LO, DOM_HI = -1.0, 3.0
TICKS = [(0.1, "0.1 ms"), (1, "1 ms"), (10, "10 ms"), (100, "100 ms"), (1000, "1 s")]
TOP = 116.0
HEADER_H, ROW_H, GROUP_GAP = 20.0, 23.0, 16.0
BLOCK = HEADER_H + len(SERIES) * ROW_H + GROUP_GAP
PLOT_BOTTOM = TOP + len(GROUPS) * BLOCK - GROUP_GAP + 6
H = PLOT_BOTTOM + 52
FONT = "system-ui, -apple-system, 'Segoe UI', sans-serif"


def x_of(ms):
    return PLOT_L + (math.log10(ms) - DOM_LO) / (DOM_HI - DOM_LO) * (PLOT_R - PLOT_L)


def fmt(ms):
    return f"{ms:.2f} ms" if ms < 10 else (f"{ms:.1f} ms" if ms < 100 else f"{ms:.0f} ms")


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
    """Series color fill with a 2px surface ring; shape is the secondary encoding."""
    r = 4.6
    if shape == "circle":
        geo = f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}"'
    elif shape == "square":
        s = r * 1.78
        geo = f'<rect x="{cx - s / 2:.1f}" y="{cy - s / 2:.1f}" width="{s:.1f}" height="{s:.1f}" rx="1"'
    else:
        h = r * 1.95
        pts = (f"{cx:.1f},{cy - h * 0.62:.1f} {cx + h * 0.6:.1f},{cy + h * 0.45:.1f} "
               f"{cx - h * 0.6:.1f},{cy + h * 0.45:.1f}")
        geo = f'<polygon points="{pts}"'
    return (f'{geo} fill="none" stroke="{surface}" stroke-width="2"/>'
            f'{geo} fill="{color}"/>')


def build(theme_name):
    t = THEMES[theme_name]
    surface, ink, ink2, muted = t["surface"], t["ink"], t["ink2"], t["muted"]
    colors = t["series"]
    out = []
    a = out.append

    a(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
      f'role="img" aria-labelledby="figTitle figDesc" font-family="{FONT}">')
    a('<title id="figTitle">SATLIB solve time by solver</title>')
    a('<desc id="figDesc">Mean solve time per instance on a logarithmic scale, for two solvers across three '
      'SATLIB random 3-SAT sets, 100 instances each. On uf20-91 (20 variables, satisfiable): dpll 0.16 ms mean '
      'and 0.51 ms worst; naive 192 ms mean and 560 ms worst. On uf50-218 (50 variables, satisfiable): dpll '
      '5.70 ms mean, 20.4 ms worst. On uuf50-218 (50 variables, unsatisfiable): dpll 15.8 ms mean, 58.9 ms '
      'worst. The naive solver is out of reach on the 50-variable sets, since it enumerates all 2^50 '
      'valuations.</desc>')
    a(f'<rect x="0" y="0" width="{W}" height="{H}" fill="{surface}"/>')

    block, plot_bottom = BLOCK, PLOT_BOTTOM

    # Grid first, so marks sit on top of it -- and segmented per group block, so
    # the group headings sit on clean surface instead of across a gridline.
    for gi in range(len(GROUPS)):
        y0 = TOP + gi * block + HEADER_H - 4
        y1 = y0 + len(SERIES) * ROW_H + 4
        for v, _ in TICKS:
            gx = x_of(v)
            a(f'<line x1="{gx:.1f}" y1="{y0:.1f}" x2="{gx:.1f}" y2="{y1:.1f}" '
              f'stroke="{t["grid"]}" stroke-width="1"/>')
    a(f'<line x1="{PLOT_L:.1f}" y1="{plot_bottom:.1f}" x2="{PLOT_R:.1f}" y2="{plot_bottom:.1f}" '
      f'stroke="{t["axis"]}" stroke-width="1"/>')

    a(text(24, 34, "SATLIB solve time by solver", ink, 15, weight=600))
    a(text(24, 53, "Mean per instance, 100 instances per set · mark is the mean, line runs to the "
                   "worst instance", ink2, 11.5))

    # Legend: identity via swatch shape + label, never color alone.
    lx = 24.0
    for i, (name, shape) in enumerate(SERIES):
        a(marker(shape, lx + 6, 74, colors[i], surface))
        a(text(lx + 18, 78, name, ink2, 11.5))
        lx += 24 + 6.9 * len(name) + 16

    a(text(MEAN_COL, TOP - 12, "MEAN", muted, 9.5, anchor="end", spacing="0.04em"))
    a(text(WORST_COL, TOP - 12, "WORST", muted, 9.5, anchor="end", spacing="0.04em"))

    y = TOP
    for gname, ann, rows in GROUPS:
        a(text(24, y + 4, gname, ink, 12, weight=600))
        a(text(24, y + 17, ann, muted, 10.5))
        y += HEADER_H
        for i, (name, shape) in enumerate(SERIES):
            cy = y + ROW_H / 2
            a(text(156, cy + 4, name, ink2, 11.5, anchor="end"))
            cell = rows[name]
            if cell is None:
                a(text(PLOT_L + 6, cy + 4, "out of reach — enumerates 2⁵⁰ valuations",
                       muted, 11, style="italic"))
            else:
                mean_ms, worst_ms = cell
                xm, xw = x_of(mean_ms), x_of(worst_ms)
                a(f'<line x1="{xm:.1f}" y1="{cy:.1f}" x2="{xw:.1f}" y2="{cy:.1f}" '
                  f'stroke="{colors[i]}" stroke-width="1.5" stroke-linecap="round" opacity="0.5"/>')
                a(f'<line x1="{xw:.1f}" y1="{cy - 3.5:.1f}" x2="{xw:.1f}" y2="{cy + 3.5:.1f}" '
                  f'stroke="{colors[i]}" stroke-width="1.5" opacity="0.5"/>')
                a(marker(shape, xm, cy, colors[i], surface))
                a(text(MEAN_COL, cy + 4, fmt(mean_ms), ink, 11.5, anchor="end"))
                a(text(WORST_COL, cy + 4, fmt(worst_ms), muted, 11, anchor="end"))
            y += ROW_H
        y += GROUP_GAP

    for v, label in TICKS:
        a(text(x_of(v), plot_bottom + 16, label, muted, 10.5, anchor="middle"))

    a(text(24, plot_bottom + 40,
           "Logarithmic time axis. Release build; SATLIB uniform random 3-SAT at the phase transition "
           "(ratio ≈ 4.26).", muted, 10.5))
    a('</svg>')
    return "\n".join(out)


for name, path in (("light", "docs/benchmarks.svg"), ("dark", "docs/benchmarks-dark.svg")):
    with open(path, "w") as f:
        f.write(build(name) + "\n")
    print(f"wrote {path}", file=sys.stderr)
