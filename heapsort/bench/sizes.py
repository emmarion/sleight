import csv, re, sys
from pathlib import Path

H = Path(__file__).resolve().parent.parent
R = H.parent
COMMENTS = {
    ".c": [r"/\*.*?\*/", r"//[^\n]*"],
    ".dats": [r"/\*.*?\*/", r"\(\*.*?\*\)", r"//[^\n]*"],
    ".ml": [r"\(\*.*?\*\)"],
    ".lean": [r"/-.*?-/", r"--[^\n]*"],
    ".idr": [r"\{-.*?-\}", r"--[^\n]*"],
    ".sl": [r'"(?:\\.|[^"\\])*"|;[^\n]*'],
}


def strip(path, text):
    for c in COMMENTS[path.suffix]:
        text = re.sub(c, lambda m: m[0] if m[0].startswith('"') else "", text, flags=re.S)
    return text


def part(path, start=None, end=None):
    t = path.read_text()
    a = re.search(start, t, re.M).start() if start else 0
    b = re.search(end, t, re.M).start() if end else len(t)
    return path, t[a:b]


def sl(sandbox, listing):
    fs = [f for f in listing.read_text().split() if not f.startswith("#")]
    return [part(sandbox / f if (sandbox / f).exists() else sandbox / "work" / f) for f in fs]


ROWS = [
    ("ATS certified", "yes", [part(H / "ats/heapsort_cert.dats")]),
    ("ATS plain", "no", [part(H / "ats/heapsort_plain.dats", r"^fun sift", r"^%\{\^")]),
    ("C", "no", [part(H / "ats/heapsort_c.c", r"^static void sift", r"^long c_sort")]),
    ("OCaml handwritten", "no", [part(H / "heapsort.ml", r"^let sift", r"(?<=^  done\n)")]),
    ("Lean verified", "yes", [part(H / "HeapSort.lean"), part(H / "Int63.lean")]),
    ("Idris 2 (plain port)", "no", [part(H / "bench/Hs.idr", r"^Arr : Type", r"^fill :")]),
    *((f"Sleight {d}/", "yes", sl(R, H / d / "files.txt")) for d in ("opus", "mimo", "flat")),
    *((name, "yes", sl(Path(p), Path(p) / "work/files.txt")) for name, p in (a.split("=", 1) for a in sys.argv[1:])),
    ("Sleight spec.sl (given, not counted above)", "", [part(R / "agent/tasks/heapsort-fast/spec.sl")]),
]

w = csv.writer(open(Path(__file__).parent / "sizes.csv", "w", newline=""), lineterminator="\n")
w.writerow(["sort", "verified", "files", "code_lines", "code_nonws_chars", "code_bytes"])
for name, ver, parts in ROWS:
    code = "\n".join(strip(p, t) for p, t in parts)
    w.writerow([name, ver, len({p for p, _ in parts}), sum(1 for l in code.splitlines() if l.strip()),
                len(re.sub(r"\s", "", code)), sum(len(t.encode()) for _, t in parts)])
