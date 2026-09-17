; needs: list
; expect: 0
; A run-position comptime-match records an unconditional fact, which refutes a branch inside a later function.

(def-lvl W)
(def-fns W $ many id : (many (Nat) n) -> (many (Nat) m) n)
(let (many z) (id (Zero)))
(comptime-match z (Zero))

(def-lvl X)
(def-fns X $ many f : (erased (Nat) n) -> (many (Nat) m)
  (match many z (((Nat) r))
    ((Zero) (Zero))
    (absurd Succ)))

(f (Zero))
