; expect: 3
; A character literal is (MkChar (MkU8 n p)) over its code's numeral, transparent down to the opaque n:
; comptime-match reaches n, and the character's own Numeral proof serves it.

(def-fns _ $ (erased three : (erased (Nat) n) (erased (Numeral (B1 (B1 (BZ))) n) v) -> (erased (Nat) m))
  n)

(let ((many c)) #\x03)
(comptime-match many c (MkChar u))
(comptime-match many u (MkU8 n p))
(let ((erased r)) (three n (numeral-of #\x03)))
n
