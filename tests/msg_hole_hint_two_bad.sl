(def-adts $ (W : -> Type)
  enum
  (many MkW : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) (erased (Lt b a) q) -> (W)))
(def-fns _ $ (many h : (many (Nat) x) (many (Nat) y) (erased (Lt x y) xy) (erased (Lt y x) yx) -> (many (Nat) r))
  (let ((erased t)) (MkW x y _ _))
  x)
(Zero)
; error: cannot infer `__?1` and `__?2` in `(MkW x y __?1 __?2)`
; error: tests/msg_hole_hint_two_bad.sl:5:30: hint: `__?1` has type `(Lt x y)`, as does:
; error: tests/msg_hole_hint_two_bad.sl:4:54: hint: `xy`, bound here
; error: tests/msg_hole_hint_two_bad.sl:5:32: hint: `__?2` has type `(Lt y x)`, as does:
; error: tests/msg_hole_hint_two_bad.sl:4:75: hint: `yx`, bound here
