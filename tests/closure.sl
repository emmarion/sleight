; needs: list
; expect: 2
; A nested def-fns closes over its enclosing function's parameter.

(def-lvl F)

(def-fns F $ (many adder : (many (Nat) n) -> (erased (Level) L) (many (Fn L (many (Nat) m) -> (many (Nat) r)) add-n))
  (def-lvl L)
  (def-fns L $ (many add-n : (many (Nat) m) -> (many (Nat) r))
    (match many n (((Nat) r))
      ((Zero) m)
      ((Succ _) (Succ m))))
  (values L add-n))

(let ((erased L) (many add-one)) (adder (Succ (Zero))))
(add-one (Succ (Zero)))
