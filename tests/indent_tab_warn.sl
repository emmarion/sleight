; expect: 3
; warns: tests/indent_tab_warn.sl:8:2: warning: indentation uses a tab, not spaces only
; A tab in the indentation is reported whatever nesting it claims: the check reads a column, which a tab
; makes depend on a setting the file does not carry.

(def-lvl A)
(def-fns A $ (many inc : (many (Nat) n) -> (many (Nat) m))
	(Succ n))

(inc 2)
; warns: tests/indent_tab_warn.sl: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes
