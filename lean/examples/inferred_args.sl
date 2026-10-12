; `_` for an inferred argument (DESIGN.md section 50), solved by unification against the parameters' types
(def-fns _ $ (many len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a h t) (Succ (len _ t)))))
(let ((many xs)) (Cons _ (Zero) (Cons _ (Succ (Zero)) (Nil (Nat)))))
(let ((erased e)) (Refl _ (len _ xs)))
(len _ xs)
