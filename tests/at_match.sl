; expect: (Cons _ 1 $ Cons _ 2 $ Nil _)
; An at-match (AT_REDESIGN A9): its annotation is written in an `at` form, every entry erased or `at`, its
; branches erase to nothing, and it skips its runtime; coverage is still checked.
(def-adts $ (Meters : -> Type) enum newtype (many MkMeters : (many (Nat) n) -> (Meters)))
(def-fns _ $ (many at unwrap : (subterm many (List (Meters)) ms) -> (many (List (Nat)) ns at ms))
  (match many ms (at (((List (Nat)) ns at ms)))
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
(def-fns _ $ (many go : (many (List (Meters)) ms) -> (many (List (Nat)) ns at ms))
  (match many ms (at (((List (Nat)) ns at ms)))
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
(go (Cons _ (MkMeters 1) (Cons _ (MkMeters 2) (Nil _))))
; warns: tests/at_match.sl:6:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
; warns: tests/at_match.sl:13:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
