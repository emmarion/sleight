; needs: list
; expect: 1
; A Matchable parameter whose type names a concrete type says nothing the declaration did not: opened, it merges
; with the type's own Matchable, which def-adts opened (DESIGN.md section 19), and the record keeps
; that one, so the match reads neither the parameter nor anything else at runtime and the parameter may be erased.
(def-lvl X)
(def-fns X $ (many len : (erased (Matchable enum List (many Nil) (many Cons)) m)
    (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (open-adt erased m)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (len m (subterm (prove-subterm tl xs)) tl)))))
(len (matchable-of List) (Cons (Nat) 0 (Nil (Nat))))
