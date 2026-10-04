; expect: 2
; A def-adts inside a body whose field is pinned by is to the enclosing function's parameter n, closed over.

(def-lvl X)
(def-fns X $ (many pin : (many (Nat) n) -> (many (Nat) m))
  (def-adts $ (Pinned : -> Type)
    enum
    (many MkPinned : (many n is v) -> (Pinned)))
  (let ((many p)) (MkPinned n))
  (match many p (((Nat) r))
    ((MkPinned v) (Succ v))))
(pin (Succ (Zero)))
