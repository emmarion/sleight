; needs: list
; expect: 1
; Nested matches on the same variable: the inner match sees the outer branch's facts.

(def-lvl X)
(def-fns X $ (many f : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) r))
    ((Zero) (Zero))
    ((Succ k)
      (match many n (((Nat) r))
        (absurd Zero)
        ((Succ j) (Succ (Zero)))))))
(f (Succ (Succ (Zero))))
; warns: tests/nested_match.sl:7:4: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
