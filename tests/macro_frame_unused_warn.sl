; needs: ../std/macro
(def-macro (bind-to args)
  (let-match many args (Cons _ v r1) ((Nil _) (Nil _)))
  (let-match many r1 (Cons _ x _) ((Nil _) (Nil _)))
  (qq (let ((many (~ v))) (~ x))))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))
  (bind-to y n)
  n)
(f 3)
; expect: 3
; warns: tests/macro_frame_unused_warn.sl:5:13: warning: unused `y`; delete its `let`
; warns: tests/macro_frame_unused_warn.sl:7:3: note: in the expansion of `bind-to` here
