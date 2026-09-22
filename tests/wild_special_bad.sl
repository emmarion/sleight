; needs: list
; error: cannot infer the _ in (Nil _)
; A special form's argument is a boundary: prove-subterm reads its terms, so an open `_` is refused there.
(let ((many xs)) (Cons (Nat) (Zero) (Nil (Nat))))
(let ((erased p)) (prove-subterm (Nil _) xs))
xs
