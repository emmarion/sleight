; error: `b`, declared `erased`, used in a non-erased position
; An erased binder is named as written even where a match makes it equal to a newer non-erased one.

(def-lvl L)
(def-fns L $ (many f : (erased (Nat) b) (many (Nat) a) (erased (Eq (Nat) a b) p) -> (many (Nat) r))
  (let-match erased p (Refl _ _))
  b)
