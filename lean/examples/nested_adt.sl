; def-adts inside a body may mention the body's entries, which it lifts (DESIGN.md section 27)

(def-lvl X)
(def-fns X $ (many pin : (many (Nat) n) -> (many (Nat) m))
  (def-adts $ (Pinned : -> Type)
    enum
    (many MkPinned : (many n is v) -> (Pinned)))
  (let ((many p)) (MkPinned n))
  (match many p (((Nat) r))
    ((MkPinned v) (Succ v))))
(pin (Succ (Zero)))
