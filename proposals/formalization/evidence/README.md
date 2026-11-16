# Evidence: the sub-agents' reports

Each file here is the report of one sub-agent of the Claude session
that wrote these proposals, kept as the agent wrote it. A report is an
agent's word. It is not the owner's, and what it says of an
implementation is not what the language is.

Every claim in a report carries a tag: `[QUOTE file:line]` for copied
text, `[RAN]` for a command the agent ran with its output, `[READ
file:lines]` for code the agent read, `[INFERENCE]` for reasoning it
did not verify, and `[UNKNOWN]`. The survey of prior art uses
`[SOURCE]` and `[RECALL]` as well.

| Report | Subject |
|---|---|
| `A1-slc-anatomy.md` | What slc proves today, its counters, and how it reaches the interpreter |
| `A2-reference-run.md` | How the reference implementation runs code; probes of evaluation order |
| `A3-mini-and-precedents.md` | `mini/` measured; the repository's other certified programs |
| `A4-lean-lessons.md` | What the Lean model's documents say went well and badly |
| `A5-design-audit.md` | DESIGN.md read for what a formal specification would need |
| `A6-prior-art.md` | Comparable projects, from their papers and sources |
| `A7-emission.md` | slc's output path to OCaml |
| `A8-assumptions-backlog.md` | ASSUMPTIONS.md's items classified |
| `S1-step-machine.md` | The spike under `spikes/step-machine/` |
| `S1b-derivation-and-doubling.md` | The spike under `spikes/derivation-and-doubling/` |
| `S2-heap-machine.md` | The spike under `spikes/heap-machine/` |
| `S3-suspendable-elaborator.md` | The spike under `spikes/suspendable-elaborator/` |
| `S4-reader-spec.md` | The spike under `spikes/reader/` |

The reports name files in a scratch directory that is not kept. For
the five spikes, the code is the directory in the table. The probes of
`A2-reference-run.md` that the proposals cite are under
`spikes/order/`. Other scratch files (measuring scripts, logs, and
built binaries) were not kept, so a `[RAN]` line that depends on one
can be re-run only after rebuilding it as the report describes.
