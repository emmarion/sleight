; error: `m`, declared `erased`, used in a non-erased position

(def-fns _ $ (many pred : (many (Nat) n) -> (many (Nat) r))
  (let-match many (nat-zero-dec n) (IsSucc m) ((IsZero) (Zero)))
  m)
