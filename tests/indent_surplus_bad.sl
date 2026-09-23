; error: unexpected `)`
; warns: tests/indent_surplus_bad.sl:7:24: warning: a `)` here closes more than is open (surplus `)`)
; A ) closing more than is open is reported where it sits, and leaves the depth at zero, so the lines after
; it are still checked against the count of forms actually open.

(def-lvl A)
(let ((many x)) (Zero)))
x
; warns: tests/indent_surplus_bad.sl: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes
