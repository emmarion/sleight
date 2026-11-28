# Notes on `bb/l3c10-uniform.sl`

These notes are a session's account of the file; they may be wrong in
places.

## What is proven

The descent of an odd register, level by level from `phi_O(q, s)` (or
`phi_VO(q, s)`) down through the end round and the SHED round of each
level, is proven once, by erased induction, and a macro only computes
the result:

- `shed-mk` and `shed-v`: the end word of `phi_O(p+1, 0)` (resp.
  `phi_VO`) is `1 0 1 W`, and `Tp 1 W` is the phi word of the next
  family at `2 Top(p) + 1` (Rocq's `shed_out_split`, `vshed_out_split`);
  `phi_O(0, ...)` is a concrete case.
- `lvl-mk`: one level as token rounds (`phi-chain`, `eol`, `conj`) with
  its blank count, stated through cell counts: cells(X) + used =
  cells(X') + 3s + 12.
- `Fst` names the family step (`FO (p+1) T` to `FO p T`, `FVO (p+2)` to
  `FVO (p+1)`); `Dsc` is the closed-form descent (tops, left runs pushed,
  the sum of 3s + 12); `dch-mk` turns a `Dsc` into the token chain
  `Dch`, by induction on it; `dch-run` turns a `Dch` into one `Run`
  (`rdk-run`, `round-run`, `shed-go`).
- `c-dlev K`: parses once, checks the register against `phi-run`,
  builds the `Dsc` at run time (`dsc-run`, a few big-number operations
  per level), computes the blank use as cells(final) + g - cells(X),
  takes it from the gap once, and builds the output. Its type is
  `Rch l3 c0 e -> Rs l3 c0`; no axiom is used.

Macros: `c-death-u` (DEATH, 10), `c-fdesc-u` (FDESC, 17), `c-vdesc-u`
(VDESC 3 and VDESC2 25), `c-casc` (a whole cascade from
`phi_O(q, 2 Top q)`, either plain tail). FDESC's level count comes from
`rl-top`, a closed form of the cell count of `phi_O(p, 2 Top p)` that
is not proven, since the count is only a choice; VDESC2's from a binary
search over `c-dlev`. DEATH's walk depth is taken as 2P + 4, which held
on every instance checked; when it does not, the macro falls back to
the normalized comparison.

## Agreement and timings

Shared 4-core container, noisy. Rocq's times from `hints mine`.

| macro | in situ | Sleight | Rocq |
|---|---|---|---|
| DEATH (cmain 10, moves 1 to 39,806) | 179/179 | about 0.35 s | 0.08 s |
| FDESC (umain 17) | 1,012/1,012 | about 0.3 to 0.4 s | 36 s |
| VDESC (umain 3) | 2/2 | about 0.03 s | 0.042 s |
| VDESC2 (umain 25) | 14/14 | about 0.09 s | under 0.001 s |

Sleight times are differences between repetition counts.

## Open

`c-casc` inside CHILD's replay (before each M9 move) made the CHILD
instance at move 22,321 fail, which suggests its target lies inside a
cascade there. After the merge of the base at 68293793,
`bb/l3c10-child.sl` does not elaborate (`tdigits`, `rdig`, `odd-s`),
so the measurements above are from the tree before that merge.
