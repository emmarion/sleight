; needs: list
; expect: (Succ (Zero))
; A Matchable parameter whose type names a concrete type says nothing the declaration did not: the shape is
; stamped from the type's own Matchable, which is in ambient scope (section 19), so the match reads neither
; the parameter nor anything else at runtime and the parameter may be erased.
(def-lvl X)
(def-fns X $ many len : (erased (Matchable enum List (many Nil) (many Cons)) m)
    (subterm many (List (Nat)) xs) -> (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (len m (subterm (prove-subterm tl xs)) tl)))))
(len (matchable-of List) (Cons (Nat) 0 (Nil (Nat))))
