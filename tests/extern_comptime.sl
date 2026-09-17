; externs: only
; expect: (Zero)
(let (many r) (nat-cmp 50000 50001))
(match many r (((Nat) n))
  ((CLt t rr x y p) (Zero))
  ((CEq t rr x) (Succ (Zero)))
  ((CGt t rr x y q) (Succ (Succ (Zero)))))
