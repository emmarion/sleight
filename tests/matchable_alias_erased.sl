; needs: list
; expect: 1
; An erased alias of a type's own Matchable does not stand in for it: the lookup reads the alias through to the
; def-adts one, whose ADT the elaborator sees, so a non-erased match on the type still needs nothing at runtime.
(let (erased m) (matchable-of List))
(def-lvl X)
(def-fns X $ many len : (subterm many (List (Nat)) xs) -> (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (len (subterm (prove-subterm tl xs)) tl)))))
(len (Cons (Nat) 0 (Nil (Nat))))
