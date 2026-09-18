#!/usr/bin/env python3
"""Compare a compiled manacher_main.sl driver with an independent cubic oracle."""
import argparse
import itertools
from pathlib import Path
import random
import subprocess
import time


def oracle(s):
    return max(
        j - i
        for i in range(len(s) + 1)
        for j in range(i, len(s) + 1)
        if s[i:j] == s[i:j][::-1]
    )


def check(executable, s, expected):
    result = subprocess.run(
        [executable], input=s, text=True, capture_output=True, timeout=15, check=True
    )
    actual = int(result.stdout.strip())
    if actual != expected:
        raise AssertionError(f"{s!r}: expected {expected}, got {actual}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", help="compiled pal/manacher_main.sl driver")
    parser.add_argument("--large", action="store_true", help="also time known large answers")
    args = parser.parse_args()
    executable = str(Path(args.executable).resolve())
    rng = random.Random(3917)
    cases = ["".join(p) for n in range(8) for p in itertools.product("abc", repeat=n)]
    cases += ["".join(rng.choices("abcd", k=rng.randrange(100))) for _ in range(300)]
    for s in cases:
        check(executable, s, oracle(s))
    print(f"{len(cases)} oracle cases passed")
    if args.large:
        for n in (1000, 10000, 100000):
            for name, s, expected in (
                ("repeated", "a" * n, n),
                ("alternating", ("ab" * n)[:n], n - 1 + n % 2),
            ):
                start = time.monotonic()
                check(executable, s, expected)
                print(f"{name}: n={n}, {time.monotonic() - start:.3f}s")


if __name__ == "__main__":
    main()
