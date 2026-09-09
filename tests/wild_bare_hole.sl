; needs: list
; expect: (Some (Zero))
; A bare `_` as a whole annotation entry is a hole of type Type, solved by the expected telescope.
(def-lvl L)
(def-fns L $ many first : (many (List (Nat)) xs) -> (many (Maybe (Nat)) m)
  (match many xs ((_ r))
    ((Nil a) (None _))
    ((Cons a hd tl) (Some _ hd))))
(first (Cons (Nat) (Zero) (Nil (Nat))))
