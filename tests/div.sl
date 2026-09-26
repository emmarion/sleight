; expect: 3
; Division by repeated subtraction, recursing on the subtraction's result: sub-pos returns n - (Succ d)
; with an erased proof that the result is a strict subterm of n, built along its recursion with
; subterm-trans, and slow-div recurses under that proof. (slow-div n d1) divides n by (Succ d1).

(def-lvl S)
(let ((erased ns)) (prove-predates nat-lvl S))
(def-fns S $ (many sub-pos : (subterm many (Nat) n) (many (Nat) d) (erased (Lt d n) lt) ->
    (many (Nat) r) (erased (Subterm (Nat) r (Nat) n) p))
  (match many n _
    (absurd (Zero) lt)
    ((Succ n1)
      (match many d _
        ((Zero) (values n1 (prove-subterm n1 n)))
        ((Succ d1)
          (let ((erased lt1)) (match erased lt (((Lt d1 n1) q)) (absurd LtZ) ((LtS a b p1) p1)))
          (let ((many r) (erased p)) (tail $ sub-pos (subterm _) n1 d1 lt1))
          (values r (subterm-trans p (prove-subterm n1 n))))))))

(def-lvl Q)
(let ((erased nq)) (prove-predates nat-lvl Q))
(let ((erased sq)) (prove-predates S Q))
(def-fns Q $ (many slow-div : (subterm many (Nat) n) (many (Nat) d1) -> (many (Nat) q))
  (match many (lt-dec (predates nq) d1 n) _
    ((Yes a b lt)
      (let ((many r) (erased p)) (sub-pos (predates sq) n d1 lt))
      (Succ (notail $ slow-div (subterm p) r d1)))
    ((No a b q) (Zero))))

(slow-div 7 1)
