; needs: ../std/macro macro_lib
; expect: 9
(warn-nowhere)
(warn-zero)
(warn-elsewhere)
(def-fns _ $ (many f : -> (many (Nat) n))
  (warn-here)
  (line))
(let ((many x)) (line))
x
; warns: warning: nowhere
; warns: tests/macro_pos.sl:3:1: note: in the expansion of `warn-nowhere` here
; warns: :0:0: warning: zero
; warns: tests/macro_pos.sl:4:1: note: in the expansion of `warn-zero` here
; warns: elsewhere.sl:7:9: warning: elsewhere
; warns: tests/macro_pos.sl:5:1: note: in the expansion of `warn-elsewhere` here
; warns: tests/macro_pos.sl:7:3: warning: here
; warns: tests/macro_pos.sl:7:3: note: in the expansion of `warn-here` here
