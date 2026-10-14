import sys
from common import *
rows = [  # label, lines, Xeon 8358 ms, M4 Pro ms, certified; from heapsort/bench/README.md and sizes.csv at 0f57ee2
  ('C, clang -O2', 17, 128.2, 50.0, False),
  ('C, gcc -O2', 17, 139.5, None, False),
  ('OCaml, handwritten, -unsafe (no bounds checks)', 23, 163.6, 91.9, False),
  ('OCaml, handwritten, bounds checks', 23, 178.4, 101.3, False),
  ('Lean 4, verified', 263, 228.2, 117.6, True),
  ('ATS2, certified, clang -O2', 281, 105.4, 49.9, True),
  ('ATS2, certified, gcc -O2', 281, 139.8, None, True),
  ('Idris 2, certified (Chez backend)', 338, 424.9, 210.0, True),
  ('Sleight, Claude outside the runner, flambda', 611, 145.1, 90.6, True),
  ('Sleight, claude-opus-5-5, flambda', 834, 136.1, 87.6, True),
  ('Sleight, mimo-v2.6-pro, flambda', 2047, 135.9, 88.0, True),
  ('Sleight, glm-5.3-flash, flambda', 2099, 157.2, 90.7, True),
]
panels = [('Lines of code, comments removed', 0, 2500, [0, 500, 1000, 1500, 2000, 2500], lambda v: f'{int(v):,}'),
          ('Sort time, Xeon Platinum 8358 (ms)', 0, 450, [0, 100, 200, 300, 400], lambda v: f'{v:.0f}'),
          ('Sort time, Apple M4 Pro (ms)', 0, 250, [0, 50, 100, 150, 200, 250], lambda v: f'{v:.0f}')]
W, H = 1800, 800
out = frame(W, H, 'Heap sorts of the same 2^20 integers, certified and not',
            'Median of 11 rounds, sort only; OCaml-based sorts with flambda -O3 except where noted. Sleight counts exclude the 53-line spec the task supplies; Lean, ATS and Idris counts include theirs.')
out += [f"<circle cx='{W-330}' cy='48' r='7' fill='{hue}'/>", text(W - 316, 53, 'certified', 15, ink2),
        f"<circle cx='{W-210}' cy='48' r='7' fill='{gray}'/>", text(W - 196, 53, 'uncertified', 15, ink2)]
def value(out, p, i, x0, y, sx, fmt):
    r = rows[i]; v = r[1 + p]
    if v is None:
        out.append(text(x0, y + 6, 'no gcc on macOS', 15, gray, extra="font-style='italic'")); return
    out.append(dot(sx(v), y, hue if r[4] else gray))
    out.append(text(f"{sx(v)+14:.1f}", y + 5, fmt(v), 14, ink2))
dotplot(out, [r[0] for r in rows], panels, 470, 120, 48, 370, 50, value)
out.append(text(40, H - 24, 'Sources: heapsort/bench/README.md and sizes.csv.', 14, ink2))
out.append('</svg>'); open(sys.argv[1], 'w').write('\n'.join(out))
