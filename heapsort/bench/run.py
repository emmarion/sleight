import re, statistics, subprocess, sys
from pathlib import Path

H = Path(__file__).resolve().parent
B = H / "_build"
CK = "393660565753209066784"
E = {
    "C (clang -O2)": [H.parent / "ats/driver", "bench", "c"],
    "ATS plain": [H.parent / "ats/driver", "bench", "plain"],
    "ATS certified": [H.parent / "ats/driver", "bench", "cert"],
    "OCaml handwritten": [B / "ml_safe"],
    "OCaml handwritten -unsafe": [B / "ml_unsafe"],
    "Lean verified": [H / "lean/.lake/build/bin/bench"],
    "Idris 2 (plain port)": [B / "idris/exec/hs"],
    **{f"SL {d}/": [B / f"sl_{d}"] for d in ("opus", "mimo", "flat")},
    **{f"SL {p}": [p] for p in sys.argv[2:]},
}


def ms(out):
    m = re.search(r"^wall-ns (\d+)$", out, re.M)
    return int(m[1]) / 1e6 if m else float(re.search(r"(?:^ms |\s)([\d.]+)(?: ms)? checksum", out, re.M)[1])


T = {k: [] for k in E}
for _ in range(int(sys.argv[1]) if len(sys.argv) > 1 else 11):
    for k, cmd in E.items():
        out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        assert CK in out, (k, out)
        T[k].append(ms(out))
for k, t in sorted(T.items(), key=lambda kv: statistics.median(kv[1])):
    print(f"{k:28} median {statistics.median(t):7.1f} ms   min {min(t):7.1f} ms")
