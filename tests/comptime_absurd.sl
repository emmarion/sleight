; needs: list
; expect: (Zero)
; comptime-match inside a branch contradicting the branch's facts proves the branch absurd (section 18).

(def-lvl W)
(def-fns W $ many id : (many (Nat) n) -> (many (Nat) m) n)
(let (many z) (id (Zero)))

(def-lvl X)
(def-fns X $ many f : (erased (Nat) n) -> (many (Nat) m)
  (match many z (((Nat) r))
    ((Zero) (Zero))
    ((Succ k)
      (comptime-match z (Zero))
      (Succ (Zero)))))

(f (Zero))
