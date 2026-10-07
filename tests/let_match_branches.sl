; expect: (Cons _ 2 $ Cons _ 0 $ Cons _ 1 $ Cons _ 5 $ Cons _ 3 $ Cons _ 7 $ Cons _ 4 $ Nil _)

(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))

(def-adts $ (Surely : -> Type) enum
  (many Got : (many (Nat) v) -> (Surely))
  (many Nope : (erased (False) f) -> (Surely)))

(def-lvl X)

(def-fns X $ (many or-zero : (many (Opt) o) -> (many (Nat) n))
  (let-match many o (Full v) (else (Zero)))
  (Succ v))

(def-fns X $ (many pred-or : (many (Nat) d) (many (Nat) m) -> (many (Nat) n))
  (let ((many e)) d)
  (let-match many m (Succ k)
    ((Zero) e))
  (let-match many k (Succ j) ((Zero) (Succ (Succ (Succ e)))))
  j)

(def-fns X $ (many in-branch : (many (Opt) o) (many (Opt) p) -> (many (Nat) n))
  (match many o _
    ((Empty) (Zero))
    ((Full v)
      (let-match many p (Full w) ((Empty) v))
      w)))

(def-fns X $ (many cell-root : (many (Nat) n) -> (many (Nat) r))
  (let ((many a)) (Zero))
  (let ((unique u)) (cell-alloc (Full (slot-of a))))
  (let ((unique v))
    (cell-match unique u (((Cell Full (slot-of a)) v at u))
      (Full s back)
      (let-match many n (Succ k) ((Zero) back))
      back))
  (let ((many p)) (at (v a)))
  (let-match many p (Full x))
  (Succ (Succ (Succ (Succ x)))))

(def-fns X $ (many sure : (many (Surely) s) -> (many (Nat) n))
  (let ((many w)) (let-match many s (Got v) (absurd (Nope f) f)) v)
  w)

(def-fns X $ (many mk : (many (Nat) n) -> (many (Surely) s)) (Got n))

(let ((many y)) (mk 7))
(let-match many y (Got seven) (absurd (Nope f) f))

(Cons (Nat) (or-zero (Full 1)) $ Cons (Nat) (or-zero (Empty)) $ Cons (Nat) (pred-or 1 0) $
  Cons (Nat) (pred-or 2 1) $ Cons (Nat) (in-branch (Full 3) (Empty)) $ Cons (Nat) (sure (Got seven)) $
  Cons (Nat) (cell-root 1) $ Nil (Nat))
; warns: tests/let_match_branches.sl:25:4: warning: lopsided `match`; flatten it with a `let-match` on `Full`
