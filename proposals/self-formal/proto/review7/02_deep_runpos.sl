(def-fns _ $ (many deep : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ m) ((Zero) 0))
  (Succ (notail (deep m))))
(let ((many r)) (deep 100000000))
r
