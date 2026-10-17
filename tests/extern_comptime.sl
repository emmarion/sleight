; externs: only
; expect: 0
(let ((many r)) (nat-cmp 50000 50001))
(match many r (((Nat) n))
  ((CLt _ _ _ _ _) (Zero))
  ((CEq _ _ _) (Succ (Zero)))
  ((CGt _ _ _ _ _) (Succ (Succ (Zero)))))
