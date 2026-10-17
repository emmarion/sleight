(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many run : -> (many (Nat) r))
  (let ((many a)) (Zero))
  (let ((many b)) (Succ (Succ (Zero))))
  (let ((unique u)) (cell-alloc (P (slot-of a) (slot-of b))))
  (let ((unique v))
    (cell-match unique u (((Cell P (slot-of a) (slot-of b)) v at u))
      (P values notail tail) tail))
  (let ((unique p)) (at (v a b)))
  (match unique p (((Nat) r))
    ((P _ y delegate) y)))
run
; expect: 2
; warns: tests/shadow_cell_binders_warn.sl:8:10: warning: declaration of `values` shadows a built-in
; warns: tests/shadow_cell_binders_warn.sl:8:17: warning: declaration of `notail` shadows a built-in
; warns: tests/shadow_cell_binders_warn.sl:8:24: warning: declaration of `tail` shadows a built-in
; warns: tests/shadow_cell_binders_warn.sl:11:13: warning: declaration of `delegate` shadows a built-in
; warns: tests/shadow_cell_binders_warn.sl:8:10: warning: unused `values`; write `_` in its place
; warns: tests/shadow_cell_binders_warn.sl:8:17: warning: unused `notail`; write `_` in its place
; warns: tests/shadow_cell_binders_warn.sl:11:13: warning: unused `delegate`; delete it
