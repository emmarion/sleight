; expect: 3
; warns: tests/indent_warn.sl:11:3: warning: indentation increased (0 -> 2) but nesting did not increase (0 -> 0)
; warns: tests/indent_warn.sl:10:1: note: the line before it
; Indentation is read as a claim about paren nesting (lib/indent.ml), checked before the file is parsed and
; reported as a warning, so a program that goes on to elaborate and run is reported on like any other.

(def-lvl A)
(def-fns A $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(let ((many x)) (inc 2))
  x
