; needs: list
; expect: 1
; A multi-return tail call bound by a let and repackaged in a values (section 9): the returns must
; keep their order, and the call must really be in tail position, so 2000 frames do not accumulate.

(def-lvl X)

(def-fns X $ (many count : (subterm many (Nat) n) (many (Nat) acc) (many (Nat) tag) ->
    (many (Nat) total) (many (Nat) same))
  (match many n (((Nat) r) ((Nat) s))
    ((Zero) (values acc tag))
    ((Succ k)
      (let ((erased p)) (prove-subterm k n))
      (let ((many total) (many same)) (tail (count (subterm p) k (Succ acc) tag)))
      (values total same))))

(def-lvl Y)
(let ((erased pxy)) (prove-predates X Y))

(def-fns Y $ (many run : -> (many (Nat) same))
  (let ((many total) (many same)) (count (predates pxy) 2000 (Zero) (Succ (Zero))))
  same)

run
