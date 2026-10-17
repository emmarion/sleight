(def-adts $ (Meters : -> Type) enum newtype (many MkMeters : (many (Nat) n) -> (Meters)))
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Meters) b) -> (Pair2)))
;! warn Meters reading meters
(def-fns _ $ (many at unwrap : (subterm many (List (Meters)) ms) -> (many (List (Nat)) ns at ms))
  (match many ms _
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
;! warn unwrap costs nothing
(def-fns _ $ (many go : (many (List (Meters)) ms) -> (many (List (Nat)) ns at ms))
  (match many ms (at (((List (Nat)) ns at ms)))
    ((Nil _ u) (at (u _)))
    ((Cons _ m tl u)
      (let-match many m (MkMeters n))
      (let ((many r)) (unwrap tl))
      (at (u _ n r)))))
(def-fns _ $ (many view : (many (Meters) m) -> (many (Nat) n at m))
  (match many m (at (((Nat) n at m))) ((MkMeters n) n)))
(let ((many w)) (MkMeters 2))
(let ((many a)) (Zero))
(def-fns _ $ (many rebuild :
    (unique (Cell P (slot-of a) (slot-of w)) u) -> (unique (Pair2) r at u))
  (at ((cell-match unique u (at (((Cell P (slot-of a) (slot-of w)) v at u)))
    (P _ _ back)
    (let-match many w (MkMeters _))
    back) a w)))
(def-fns _ $ (many plain : (many (Meters) m) -> (many (Nat) n))
  (let-match many m (MkMeters n))
  n)
(let ((many xs)) (Cons _ (MkMeters 1) (Cons _ (MkMeters 2) (Nil _))))
(let ((many ys)) (unwrap xs))
(let ((many v)) (view w))
(go xs)
; expect: (Cons _ 1 $ Cons _ 2 $ Nil _)
; warns: tests/warn_pragma_at.sl:5:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
; warns: tests/warn_pragma_at.sl:13:4: warning: lopsided `match`; flatten it with a `let-match` on `Cons`
; warns: tests/warn_pragma_at.sl:30:3: warning: match on `Meters`: reading meters
; warns: tests/warn_pragma_at.sl:3:1: note: `;! warn` for `Meters` is here
