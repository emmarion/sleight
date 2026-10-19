(def-fns _ $ (many one : -> (many (Nat) r))
;! file "claimed/rest.sl"
  1)
; warns: tests/file_pragma_in_form.sl:1:1: warning: this form is never closed
; warns: tests/file_pragma_in_form.sl: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes
; error: tests/file_pragma_in_form.sl:1:12: syntax error: missing `)` after `$`
