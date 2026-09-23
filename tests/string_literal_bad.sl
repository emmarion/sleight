; error: unterminated string literal
; warns: tests/string_literal_bad.sl:3:1: warning: this form is never closed
(let ((many s)) "abc)
(Zero)
; warns: tests/string_literal_bad.sl: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes
