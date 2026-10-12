; expect: 3
; A slot is introduced with its entry, so `prove-predates` takes `(slot-of x)` for an `x` older than the level:
; written directly, through a `let` that forwards from it, and in a body.
(let ((many x)) 3)
(def-lvl L)
(let ((erased p)) (prove-predates (slot-of x) L))
(let ((many s)) (slot-of x))
(let ((erased q)) (prove-predates s L))
(def-fns _ $ (many f : (many (Nat) y) -> (many (Nat) r))
  (def-lvl M)
  (let ((many t)) (slot-of y))
  (let ((erased u)) (prove-predates t M))
  y)
(f x)
