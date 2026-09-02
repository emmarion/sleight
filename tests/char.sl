; expect: (Succ (Succ (Succ (Zero))))
; A character literal is (MkChar (MkU8 n p)) over its code's numeral, transparent down to the opaque n:
; comptime-match reaches n, and numeral-of finds the code's proof through it.

(def-fns _ $ erased three : (erased (Nat) n) (erased (Numeral (B1 (B1 (BZ))) n) v) -> (erased (Nat) m)
  n)

(let (many c) #\x03)
(comptime-match c (MkChar u))
(comptime-match u (MkU8 n p))
(let (erased r) (three n (numeral-of n)))
n
