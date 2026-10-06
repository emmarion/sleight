; needs: list map
; expect: 2
; A delegate whose result is bound by a let and returned still counts (section 9).

(def-lvl V)
(let ((erased piv)) (prove-predates I V))
(def-fns V $ (many inc-noted : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))
  (let ((many r)) (delegate (inc (predates piv) n)))
  (let ((erased twice)) (Succ r))
  r)
(let ((erased ig)) (coercible-of (delegate-of inc-noted)))
(let ((many (Fn I (many (Nat) a) -> (many (Nat) b)) g)) (coerce inc-noted ig))
(g (inc-noted (Zero) (Zero)))
; warns: tests/delegate_let.sl:8:34: warning: unnecessary `(predates _)`; drop it
