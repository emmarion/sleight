; needs: list
; expect: (Cons _ 1 $ Nil _)
; A let whose binders all carry a type is the telescope its right-hand side is expected to produce
; (DESIGN.md section 50): a `_` argument is solved by it, and a match there may write `_` for its annotation.

(def-lvl L)
(def-fns L $ (many wrap : (many (Nat) n) -> (many (List (Nat)) xs))
  (let ((many (List (Nat)) empty)) (Nil _))
  (let ((many (Maybe (Nat)) m) (many (List (Nat)) ys))
    (match many n _
      ((Zero) (values (None _) empty))
      ((Succ k) (values (Some _ n) (Cons _ n empty)))))
  ys)

(wrap (Succ (Zero)))
