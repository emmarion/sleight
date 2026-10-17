; needs: list map
; expect: 2
; A delegate whose result is bound by a let and returned still counts (section 19).

(def-lvl V)
(let ((erased piv)) (prove-predates I V))
(def-fns V $ (many inc-noted at inc : (many (Nat) n) (erased (Nat) _note) -> (many (Nat) m))
  (let ((many r)) (delegate (inc (predates piv) n)))
  (let ((erased _)) (Succ r))
  r)
(let ((erased ig)) (coercible-of (delegate-of inc-noted)))
(let ((many (Fn I (many (Nat) a) -> (many (Nat) b)) g)) (coerce inc-noted ig))
(g (inc-noted (Zero) (Zero)))
; warns: tests/delegate_let.sl:8:34: warning: unnecessary `(predates _)`; drop it
