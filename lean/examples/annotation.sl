; `_` as a match annotation (DESIGN.md section 47) where the position fixes the telescope
(def-fns _ $ (many half : (subterm many (Nat) n) -> (many (Nat) h))
  (match many n _
    ((Zero) (Zero))
    ((Succ m)
      (match many m _
        ((Zero) (Zero))
        ((Succ k) (Succ (half k)))))))
(def-fns _ $ (many g : (many (Nat) x) -> (many (Nat) r))
  (let ((many (Nat) a))
    (match many x _
      ((Zero) (Zero))
      ((Succ k) (half (Succ (Succ (Succ (Succ k))))))))
  a)
(g (Succ (Zero)))
