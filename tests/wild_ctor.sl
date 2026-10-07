; needs: list
; expect: (Cons _ 1 $ Cons _ 0 $ Nil _)
; A `_` argument (DESIGN.md section 50) is solved from the arguments after it, from the telescope a body returns into,
; through values, and from a match's annotation.

(def-lvl L)
(def-fns L $ (many two : (many (Nat) a) -> (many (List (Nat)) xs) (many (Maybe (Nat)) m))
  (values (Cons _ a (Cons _ (Zero) (Nil _))) (Some _ a)))

(def-fns L $ (many head-or : (many (List (Nat)) xs) -> (many (Maybe (Nat)) m))
  (match many xs _
    ((Nil a) (None _))
    ((Cons a hd tl) (Some _ hd))))

(let ((many xs) (many m)) (two (Succ (Zero))))
(match many (head-or xs) (((List (Nat)) r))
  ((None a) (Nil _))
  ((Some a n) xs))
