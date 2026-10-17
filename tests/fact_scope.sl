; needs: list
; expect: 1
; Facts forced inside a match's branches end with the match: the second match needs both branches.

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many k))
    (match many n (((Nat) r))
      ((Zero) (Zero))
      ((Succ j) j)))
  (match many n (((Nat) r))
    ((Zero) k)
    ((Succ _) (Succ k))))
(f (Succ (Zero)))
