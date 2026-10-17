; expect: (MkBox 3)
; As at_closed_temporary.sl, with the temporary closing inside the match's scrutinee.
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) -> (Box)))
(def-fns _ $ (many id-box : (many (Box) x) -> (many (Box) r at x)) x)
(def-fns _ $ (many copy-box : (many (Box) x) -> (many (Box) r)) (let-match many x (MkBox n)) (MkBox n))
(def-fns _ $ (many twice : (many (Box) x) -> (many (Box) r1 at x) (many (Box) r2 at r1)) (values x x))
(def-fns _ $ (many go : (many (Box) z) -> (many (Box) b))
  (match many (copy-box (id-box z)) (((Box) b))
    ((MkBox _)
      (let ((many _) (many b)) (twice z))
      b)))
(go (MkBox 3))
; warns: tests/at_closed_temporary_scrutinee.sl:8:4: warning: lopsided `match`; flatten it with a `let-match` on `MkBox`
