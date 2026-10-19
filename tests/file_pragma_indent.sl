;! file "claimed/indent.sl"
(def-fns _ $ (many one : -> (many (Nat) r))
(Succ (Zero)))
(one)
; expect: 1
; warns: claimed/indent.sl:2:1: warning: same indentation (0) as the previous checked line but nesting is 1, expected 0 (matching that line)
; warns: claimed/indent.sl:1:1: note: the previous line at this indentation
; warns: claimed/indent.sl:3:1: warning: same indentation (0) as the previous checked line but nesting is 0, expected 1 (matching that line)
; warns: claimed/indent.sl:2:1: note: the previous line at this indentation
; warns: tests/file_pragma_indent.sl: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes
