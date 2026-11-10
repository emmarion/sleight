; Where an argument of `prove-literal-lt` is tainted, the macro expands to a `sorry` of the `Lt` it would have
; minted, and checking goes on with it; `unary` expands to a `let-match` on a `sorry`, which creates no rule
; and taints the rest of the scope. Each such `sorry` is counted.
(def-fns _ $ (many small : (many (Nat) n) (erased (Lt n 5) _p) -> (many (Nat) m))
  (Succ n))
(let ((many t)) (sorry (((Nat) q))))
(let ((erased p)) (prove-literal-lt t 5))
(let ((erased p3)) (prove-literal-lt 3 5))
(small 3 p3)
;! file "sorry/macros-lt.sl"
(small t p)
;! file "sorry/macros-unary.sl"
(unary t 3)
(small 3 p3)
; expect: 4
; expect: sorry
; expect: sorry
; warns: tests/sorry_macros.sl:6:17: warning: this unit uses `sorry` 3 times, first here; nothing that depends on it runs
