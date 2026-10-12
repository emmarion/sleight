; a let-match with a second real branch is confined to a body
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many r))
    (let-match many n (Succ k) ((Zero) (Zero)))
    k)
  r)
(f (Zero))
