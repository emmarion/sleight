import csv, statistics, sys
from common import *
rows = list(csv.DictReader(open(sys.argv[1])))
models = {}
for r in rows: models.setdefault(r['model'], []).append(r)
f = lambda x: float(x) if x else None
order = sorted(models, key=lambda m: (not any(r['first_passing_session'] for r in models[m]),
    statistics.median([int(r['first_passing_session']) for r in models[m] if r['first_passing_session']] or [99])))
cols = ['first_passing_session', 'usd_run_total_at_pass', 'code_lines', 'x86_flambda_sort_ms_median_first_pass']
panels = [('Sessions to first pass', 0, 15, [1, 5, 10, 15], lambda v: f'{int(v)}'),
          ('Dollars spent at first pass', 0, 16, [0, 5, 10, 15], lambda v: f'${int(v)}'),
          ('Lines of code (comments removed)', 0, 3200, [0, 1000, 2000, 3000], lambda v: f'{int(v):,}'),
          ('Sort time, Xeon 8358, flambda (ms)', 100, 350, [100, 150, 200, 250, 300, 350], lambda v: f'{int(v)}')]
W, H = 1800, 680
out = frame(W, H, 'Heapsort task: 28 runs, 10 models',
            'One dot per run. Pass = certified against the spec, no warnings, correct checksum, zero words allocated. Rows ordered by median sessions to pass.')
labels = [m.replace('-flex', '') + (' (1 run)' if len(models[m]) == 1 else '') for m in order]
def value(out, p, i, x0, y, sx, fmt):
    vals = [f(r[cols[p]]) for r in models[order[i]]]
    if all(v is None for v in vals):
        if p == 0: out.append(text(x0, y + 6, 'never passed: nothing compiled in 3 runs of 30 sessions', 15, gray, extra="font-style='italic'"))
        return
    for v in vals:
        if v is not None: out.append(dot(sx(v), y, hue))
    if p == 3 and max(v for v in vals if v) > 280:
        out.append(text(f"{sx(350)-12:.1f}", y - 12, f"{int(round(max(v for v in vals if v)))} ms, preorder layout", 13, ink2, 'end'))
dotplot(out, labels, panels, 300, 110, 46, 330, 46, value)
out.append(text(40, H - 24, 'Source: heapsort/agent-runs-8860c75.csv. 25 of 28 runs passed. For scale: the same sort is 17 lines of C, 23 of OCaml, 263 of verified Lean, 281 of certified ATS.', 14, ink2))
out.append('</svg>'); open(sys.argv[2], 'w').write('\n'.join(out))
