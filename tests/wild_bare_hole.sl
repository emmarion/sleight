; needs: list
; expect: (Some _ 0)
; A bare `_` as a whole annotation entry is a hole of type Type, solved by the expected telescope.
(def-lvl L)
(def-fns L $ (many first : (many (List (Nat)) xs) -> (many (Maybe (Nat)) m))
  (match many xs ((_ r))
    ((Nil _) (None _))
    ((Cons _ hd _) (Some _ hd))))
(first (Cons (Nat) (Zero) (Nil (Nat))))
