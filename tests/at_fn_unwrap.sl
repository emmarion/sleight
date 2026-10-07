; expect: (Cons _ 1 $ Cons _ 2 $ Nil _)
; The review's P4 as an at-function (section 39): unwrapping a list of a newtype at `many` is a traversal
; whose every branch erases to nothing, so the call is skipped and the result is read off the argument.
(def-adts $ (Meters : -> Type) enum newtype (many MkMeters : (many (Nat) n) -> (Meters)))
(def-fns _ $ (many at unwrap : (subterm many (List (Meters)) ms) -> (many (List (Nat)) ns at ms))
  (match many ms _
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
(unwrap (Cons _ (MkMeters 1) (Cons _ (MkMeters 2) (Nil _))))
; warns: tests/at_fn_unwrap.sl:6:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
