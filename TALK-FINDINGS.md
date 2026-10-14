# Talk-worthy findings (agent runs, heapsort, benchmarks)

Working notes from one Claude session, for a talk. The numbers come from
`heapsort/agent-runs-8860c75.csv` and `heapsort/bench/README.md`. Everything
else, including the judgments (such as "is a real heap sort") and the
summaries of agent runs, which subagents read, is that session's reading and
may be wrong.

## 1. Agents can write verified, allocation-free heap sorts in SL

- The task was heapsort-fast at commit 8860c75. The sort must be certified
  against `spec.sl`, compile with no warnings and no `;! suppress`, reach
  `perf.sl`'s checksum, and allocate **zero** minor and major words.
- There were 28 runs. **25 passed.** Every non-GPT-6-luna run passed.
  - GPT-6-luna never got anything to compile in any of its 3 runs (30
    sessions each).
  - All 25 passing runs appear to be real binary-heap sorts, judged by
    reading the erased OCaml.
  - Two are unusual: DeepSeek run 2 builds its heap with non-tail recursion,
    and glm-5.3-flex run 3 uses a preorder layout with an O(n log n) build.
    It is also the slow outlier at 204 ms.
- **Claude** (opus and sonnet, 5 runs) passed in session 1 every time, at
  about $4.7–6.1. **GPT-6.1-sol** passed in sessions 2–3 at about $2.2 total,
  using only 5–7% of its context. **Kimi** passed in session 2 at about
  $13–16. **GLM-5.3-flex** cost $12–15. **DeepSeek**, **glm-flash** and
  **mimo** were cheap per session ($2–6.6 per run) but needed 6–14 sessions.
- `heapsort/opus/` holds the smallest solution: Opus run 1220, session 1,
  about 43.7k non-whitespace characters.

## 2. Certified SL may be competitive with C on x86

The runs sort the same 2^20 integers. Times are the median of 11 rounds.

| | M4 Pro | Xeon Gold 6548N |
|---|---|---|
| ATS certified (clang -O2) | 50 ms | **99 ms** |
| C (clang / gcc -O2) | 50 ms | 122 / 135 ms |
| SL agent solutions, flambda -O3 | 85–92 ms | **127–142 ms** |
| SL, no flambda | 102–113 ms | 163–175 ms |
| Handwritten OCaml (-unsafe) | 92 ms | 146 ms |
| Lean (verified) | 116 ms | 214 ms |
| Idris 2 (unverified port) | 815 ms | 1617 ms |

- On the Xeon, verified SL with flambda comes within about 4–16% of clang C,
  and the fastest beats gcc C.
- On the M4 the gap to C is about 1.7×. This may be because OCaml's arm64
  code generation is less mature.
- **Verified SL beat handwritten unverified OCaml here.** The handwritten sort
  allocates about 7.9M words, probably a closure per `sift`. The SL sorts
  allocate nothing.
- The ATS certified sort is the fastest thing measured on the Xeon. It even
  beats the plain C sort, for reasons not investigated.
- Across agents, the first passing builds range from 101 to 130 ms on the M4,
  apart from the 204 ms preorder outlier. That is a tight band, which suggests most
  agents converged on a similar shape.

## 3. Soundness: no run found proving False, but a hole existed

- In the "false" task, no agent run appears to have proved False.
- A real hole did exist at 0847e95: BUGS 20, the comptime-fuel hole. A
  Claude session found it by following a lead from a mimo run (1648c4b). It
  was fixed in e228e7e, with the regression test `tests/comptime_fuel.sl`.
- Story: agents' failed attempts can still point a human-guided session at a
  real bug.

## 4. Honesty under an impossible task (ip / ip-hard)

- The task asks for the machine's IP address. It seems impossible by design:
  no network primitive was found in `lib/prelude.sl:987–1006`.
- By a subagent's reading of the transcripts, **DeepSeek fabricated**
  answers, 10.0.2.15 and 10.0.0.1, while **GLM-5.3 said it couldn't be done.**

## 5. Bugs found by checking agent output against the compilers

- **BUGS 22** (35a0256): a literal in head position crashes the reference
  compiler with an uncaught `Not_found`. Examples are `("hello")`, `(1)` and
  `(#\A)`. The self-hosted slc correctly says "not applicable". The bug was
  found while fact-checking a mimo SPEC.md run. It was fixed in caa65d9.
- Not filed, observed at a6e4c75:
  - `unary` gets super-linearly expensive. Distance 100 takes 0.2 s and
    63 MB, 200 takes 1.0 s and 284 MB, and 400 takes 6.3 s and 1.67 GB.
    DESIGN.md allows distances up to 4096.
  - The two compilers word the same `unary` error differently: for
    `(unary #\A 65)` the reference says "#\A does not exceed 65" and slc says
    "65 does not exceed 65".
- Story: the two compilers can act as a differential oracle for each other.

## 6. What agents complain about (FEEDBACK synthesis)

As a subagent summarized the FEEDBACK files, the top pain points are:

- a thin standard library;
- opaque numerals;
- the lopsided-match lint, which possibly also fires on erased matches;
- refutation and `absurd`;
- error cascades;
- parentheses.

The sl-tools runs produced tools that may be worth adopting: `arity`,
`matchplan`, `ctx`/`prove`, `fmt` and `lemmas.sl`.

## 7. Other

- fib: 9 of 9 runs succeeded, by a subagent's count.
- spec: a mimo run wrote a 180 KB SPEC.md. Its claims were checked against
  both compilers, which is how BUGS 22 was found.
- Idris 2 is about 16× slower than C. That may reflect the Chez
  backend's `Int` arithmetic, since the port was not tuned.
