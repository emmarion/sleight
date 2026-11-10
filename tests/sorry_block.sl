; Within a `def-fns` block every function starts untainted and taint spreads until nothing more changes: `even`
; calls `odd`, whose `Zero` branch is a `sorry`. A function of the block that reaches no tainted one stays untainted.
(def-fns _
  ((many even : (subterm many (Nat) n) -> (many (Bool) b))
    (let-match many n (Succ p) ((Zero) (BTrue)))
    (tail (odd p)))
  ((many odd : (subterm many (Nat) n) -> (many (Bool) b))
    (let-match many n (Succ p) ((Zero) (sorry _)))
    (tail (even p)))
  ((many same : (many (Nat) n) -> (many (Nat) m))
    n))
(same 6)
;! file "sorry/even.sl"
(even 4)
; expect: 6
; expect: sorry
; warns: tests/sorry_block.sl:8:40: warning: this unit uses `sorry` once, here; nothing that depends on it runs
