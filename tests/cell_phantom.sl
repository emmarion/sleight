; expect: 2
(def-adts $ (T : -> Type) enum (many Live : (many (Nat) n) -> (T)) (erased Ghost : (erased (Nat) n) -> (T)))
(def-adts $ (G : -> Type) enum (many MkG : -> (G)) (erased Ghost2 : (many (Nat) n) -> (G)))
(def-fns _ $ (erased ghost : (many (Nat) n) -> (many (G) t))
  (let ((erased c)) (cell-alloc Ghost2))
  (let ((erased c2)) (cell-write erased c (Ghost2 (slot-of n))))
  (c2 n))
(def-fns _ $ (erased abstract :
    (erased (TyCtor -> Type) U)
    (erased (ValCtor -> (U)) C)
    (erased (Matchable enum U (erased C)) m) -> (erased Type r))
  (open-adt erased m)
  (Cell C))
(def-fns _ $ (erased write-live : (unique (Cell Live vacant-slot) u) (many (Nat) n) ->
    (unique (Cell Live (slot-of n)) r at u))
  (cell-write erased u (Live (slot-of n))))
(def-fns _ $ (many at swap : (erased Type P) (erased Type Q) (erased Q q) (many (ErasedOr P) x) ->
    (many (ErasedOr Q) y at x))
  (match many x _
    ((EONonErased _ p u) (at (u Q q)))
    ((EOErased _ u) (u Q))))
(def-fns _ $ (many at relabel : (unique (T) x) -> (unique (T) y at x))
  (match unique x _
    ((Live n u) (at (u n)))
    ((Ghost n u) (u n))))
(def-fns _ $ (erased rebuild : (erased (T) x) -> (erased (T) y at x))
  (let-match erased x (Ghost n u) ((Live n2) x))
  (u n))
(let ((many s)) (swap (Nat) (Nat) 3 (EONonErased (Nat) 2)))
(let ((many v)) (share (relabel (Live 2))))
(comptime-match many s (EONonErased _ _))
(match many v (((Nat) r)) ((Live n) n) ((Ghost n) n))
; warns: tests/cell_phantom.sl:3:52: warning: phantom constructor `Ghost2` has a non-erased field
