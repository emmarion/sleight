# Reference extraction appears to split one mutable cell into two

Observed on the fresh reference and self-hosted binaries built for the
2026-10-07 review. This appears to be a new high-severity wrong-code issue,
not one of the remaining items in BUGS.md or audit/README.md.

The accepted program `extract_cell_alias.sl` records a cell's slot, writes
that cell at compile time, and captures both the old slot word and the
current unique cell in an IO continuation. At runtime it updates the cell
from 0 to 1, then reads it through a parameter promised `at` the saved
slot. DESIGN §§35–37 require those words to identify the same cell.

Observed output (all exits 0; the program deliberately prints no newline):

| Execution | Output |
| --- | --- |
| Reference interpreter | `1` |
| Reference extracted OCaml | `0` |
| Reference interpreter, `--no-extern` | `1` |
| Reference extracted OCaml, `--no-extern` | `0` |
| Reference extracted OCaml, `--no-templates` | `0` |
| Fresh slc `--interpret` | `1` |
| Fresh slc compiled OCaml | `1` |

The likely cause is the mismatch between runtime cell identity and the
extractor's memo key. `lib/eval.ml:42–46` returns a fresh `VCtor (k, fs)`
after a unique cell write while retaining the original mutable `fs`
array. The original and returned wrappers thus appear distinct to the
`v' == v` memo test in `lib/extract.ml:191–203`, although both refer to
one cell. Extraction allocates a separate OCaml block for each wrapper.
The emitted continuation writes one block and reads the other. Extern
arrays and bytes already use their underlying buffer as identity in
`lib/extract.ml:184–190` and `216–223`.

The printed discrepancy establishes wrong code independently of FFI
or template behavior. Its significance appears broader than printing:
it invalidates an accepted `at` promise and can separate an erased
content/index fact from the runtime contents on which it relies. No
additional arbitrary-code or contradiction exploit was needed or tested.

Reproduction from the repository root (the audit's fresh slc binary is
`_build/audit-current/slc`):

```sh
export PATH=/Users/ericmarion/.opam/default/bin:$PATH
_build/default/bin/main.exe audit/2026-10-07-review/extract_cell_alias.sl
_build/default/bin/main.exe audit/2026-10-07-review/extract_cell_alias.sl --extract /tmp/cell-alias-reference.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg /tmp/cell-alias-reference.ml -o /tmp/cell-alias-reference
/tmp/cell-alias-reference
_build/audit-current/slc --interpret audit/2026-10-07-review/extract_cell_alias.sl
_build/audit-current/slc audit/2026-10-07-review/extract_cell_alias.sl > /tmp/cell-alias-self.ml
ocamlfind ocamlopt -package zarith,unix -linkpkg /tmp/cell-alias-self.ml -o /tmp/cell-alias-self
/tmp/cell-alias-self
```

No implementation changes were made. A prospective repair should preserve
the identity of the underlying mutable cell throughout the evaluator /
extractor boundary, including captured slots and cyclic cell graphs.
