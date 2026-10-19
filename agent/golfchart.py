"""Chart the size of every session of the fetched heapsort-fast+golf runs that ends with a valid sort.

usage: python3 agent/golfchart.py [--slc SLC] [--out DIR] RESULTS-DIR...

Each RESULTS-DIR is a box-* directory or a run directory; runs of other tasks are skipped. Only finished
sessions are checked: those with an answer.txt or a later session. A session with checks/ is valid when one of its
checks has no `;! suppress`, proves the goal with SLC with no warnings, and runs perf.sl as below; its size is the
smallest such check's. A check with no `qed` is given one of `heapsort-fast`, which perf.sl calls by that name. An older session is valid when the sl files that its work/files.txt lists compile with SLC,
with accept.sl and perf.sl, with no warnings and no `;! suppress`. A run is valid when the OCaml that SLC emits,
built with ocamlfind, prints perf.sl's checksum and `minor-words 0` within a second. Results are cached in
DIR/sizes.json by session and SLC. Writes DIR/size{,-log,-loglog}.{svg,png}.
"""
import argparse, hashlib, json, math, os, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "talk/chart"))
from common import *

CHECKSUM = "393660565753209066784"
CHROME = os.environ.get("CHROME", "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
LIBS = ["std/nat.sl", "std/list.sl", "std/macro.sl", "std/tactics.sl", "heapsort-fast/spec.sl"]
TESTS = ["heapsort-fast/accept.sl", "heapsort-fast/perf.sl"]
PERF = "heapsort-fast/perf.sl"


def runs(dirs):
    for d in map(Path, dirs):
        for r in [d] if (d / "run.json").exists() else sorted(p.parent for p in d.glob("*/run.json")):
            j = json.loads((r / "run.json").read_text())
            if sorted(Path(p).name for p in j["prompts"]) == ["golf.txt", "heapsort-fast.txt"]:
                yield r, j["env"].get("PI_MODEL", r.name)


def labels(rs):
    models = [m for _, m in rs]
    copy = lambda r: (re.search(r"-(\d+)$", r.name) or [0, 1])[1]
    return [m if models.count(m) == 1 else f"{m} #{copy(r)}" for r, m in rs]


def check(session, slc, build):
    if (session / "checks").is_dir() or not (session / "sandbox/work/files.txt").exists():
        return best_check(session, slc, build)
    d = session / "sandbox"
    fs = [f if f.startswith("work/") else "work/" + f for f in (d / "work/files.txt").read_text().split() if not f.startswith("#")]
    size = sum((d / f).stat().st_size for f in fs if (d / f).exists())
    if not all((d / f).exists() for f in fs) or any(b";! suppress" in (d / f).read_bytes() for f in fs):
        return size, "missing or suppressed"
    return size, run_perf([slc, "--no-shape-note", *LIBS, *fs, *TESTS], d, build)


def best_check(session, slc, build):
    d, sizes, qed = session / "sandbox", [], build.resolve() / "qed.sl"
    build.mkdir(parents=True, exist_ok=True)
    qed.write_text("(qed (MkHeapsort (level-of heapsort-fast) heapsort-fast))\n")
    for j in sorted((session / "checks").glob("*.json"), key=lambda j: json.loads(j.read_text())["size"]):
        r, b = json.loads(j.read_text()), j.with_suffix(".sl").resolve()
        sizes.append(r["size"])
        if r["exit"] or b";! suppress" in b.read_bytes():
            continue
        own = re.search(rb"\(qed\b", b.read_bytes())
        p = subprocess.run([slc, "--no-shape-note", "--goal", "proved", *LIBS, b, *([] if own else [qed])], cwd=d, capture_output=True)
        if not p.returncode and not re.search(rb"(?m)(^|: )warning: ", p.stderr) and run_perf([slc, "--no-shape-note", *LIBS, b, PERF], d, build) == "valid":
            return r["size"], "valid"
    return min(sizes, default=0), "no valid check"


def run_perf(cmd, cwd, build):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True)
    if p.returncode or p.stderr.strip():
        return "compile"
    build.mkdir(parents=True, exist_ok=True)
    (build / "p.ml").write_bytes(p.stdout)
    if subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg", "p.ml", "-o", "p"], cwd=build, capture_output=True).returncode:
        return "ocaml"
    try:
        out = subprocess.run(["./p"], cwd=build, capture_output=True, text=True, timeout=1).stdout
    except subprocess.TimeoutExpired:
        return "timeout"
    return "valid" if f"checksum {CHECKSUM}" in out and re.search(r"^minor-words 0$", out, re.M) else "wrong output"


def chart(data, out):
    rows = -(-len(data) // 2)
    W, L, T, R, PB = 1500, 110, 150, 50, 660
    B = 110 + rows * 32
    H = PB + B
    lin = lambda a, b: lambda v: (v - a) / (b - a)
    lg = lambda a, b: lambda v: (math.log(v) - math.log(a)) / (math.log(b) - math.log(a))
    pts = [p for P in data.values() for p in P]
    n = max([int(p["session"]) for p in pts] + [5])
    top = max([p["size"] for p in pts] + [10000])
    step = 10 ** int(math.log10(top)) // 2
    ymax = -(-top * 11 // 10 // step) * step
    decades = [m * 10 ** e for e in range(3, 8) for m in (1, 2, 5)]
    lo, hi = min([p["size"] for p in pts] + [top]) * 0.7, top * 1.3
    ylog = (lg(lo, hi), [v for v in decades if lo <= v <= hi])
    modes = {"size": ((lin(0.5, n + 0.5), range(1, n + 1)), (lin(0, ymax), range(0, ymax + 1, step)), ""),
             "size-log": ((lin(0.5, n + 0.5), range(1, n + 1)), ylog, " (log scale)"),
             "size-loglog": ((lg(0.9, n * 1.07), [k for k in (1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 25, 30, 40, 50) if k <= n]), ylog, " (both axes log scale)")}
    colors = hues + ["#c2417e", "#3a8fa0", "#b08d1a", "#8a8a8a"]
    for name, ((fx, xt), (fy, yt), scale) in modes.items():
        sx = lambda h: L + fx(h) * (W - L - R)
        sy = lambda v: H - B - fy(v) * (H - T - B)
        o = frame(W, H, "Certified heapsort: solution size by session",
                  f"Bytes in the solution{scale}: work/files.txt at the end of each session, or the session's smallest valid check.")
        for v in yt:
            o += [f"<line x1='{L}' y1='{sy(v):.1f}' x2='{W - R}' y2='{sy(v):.1f}' stroke='{grid}'/>",
                  text(L - 12, f"{sy(v) + 5:.1f}", f"{v // 1000}k" if v else "0", 14, ink2, "end")]
        for h in xt:
            o += [f"<line x1='{sx(h):.1f}' y1='{T - 10}' x2='{sx(h):.1f}' y2='{H - B}' stroke='{grid}'/>",
                  text(f"{sx(h):.1f}", H - B + 26, str(h), 14, ink2, "middle")]
        o.append(text(f"{(W - R + L) / 2}", H - B + 56, "Session" + (" (log scale)" if "loglog" in name else ""), 14, ink2, "middle"))
        for i, (run, P) in enumerate(sorted(data.items(), key=lambda kv: (not kv[1], kv[0]))):
            c = colors[i % len(colors)]
            xy = [(sx(int(p["session"])), sy(p["size"])) for p in P]
            o.append(f"<polyline points='{' '.join(f'{x:.1f},{y:.1f}' for x, y in xy)}' fill='none' stroke='{c}' stroke-width='2' stroke-linejoin='round' opacity='0.8'/>")
            o += [dot(x, f"{y:.1f}", c) for x, y in xy]
            y, x0 = PB + 100 + i // 2 * 32, L + i % 2 * (W - L - R) // 2
            o += [dot(x0, y - 5, c), text(x0 + 18, y, f"<tspan font-weight='600' fill='{c}'>{run}</tspan>  " + (f"valid in session {int(P[0]['session'])}" if P else "never valid"), 16)]
            if P:
                o.append(text(x0 + 620, y, f"{P[-1]['size']:,} bytes after session {int(P[-1]['session'])}", 16, ink, "end"))
        (out / f"{name}.svg").write_text("\n".join(o + ["</svg>"]))
        subprocess.run([CHROME, "--headless", "--disable-gpu", "--hide-scrollbars", "--force-device-scale-factor=2", f"--window-size={W},{H}",
                        f"--screenshot={out / name}.png", f"file://{out / name}.svg"], capture_output=True, timeout=90)


def main():
    a = argparse.ArgumentParser()
    a.add_argument("--slc", default=str(ROOT / "_build/release/slc"))
    a.add_argument("--out", default=str(ROOT / "agent/results/charts"))
    a.add_argument("dirs", nargs="+")
    args = a.parse_args()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    cache_file = out / "sizes.json"
    cache = json.loads(cache_file.read_text()) if cache_file.exists() else {}
    slc = hashlib.sha256(Path(args.slc).read_bytes()).hexdigest()[:16]
    rs = list(runs(args.dirs))
    data = {}
    for (run, _), name in zip(rs, labels(rs)):
        data[name] = []
        ss = sorted(p for p in run.iterdir() if p.name.isdigit())
        for s in [s for s, later in zip(ss, ss[1:] + [None]) if later or (s / "answer.txt").exists()]:
            key = f"{slc} {s.resolve()}"
            if key not in cache:
                cache[key] = dict(zip(("size", "status"), check(s, args.slc, out / "build")))
                cache_file.write_text(json.dumps(cache, indent=1))
            r = cache[key]
            print(f"{name} {s.name} {r['size']} {r['status']}", flush=True)
            if r["status"] == "valid":
                data[name].append({"session": s.name, "size": r["size"]})
    chart(data, out)
    print(f"wrote {out}/size{{,-log,-loglog}}.png")


main()
