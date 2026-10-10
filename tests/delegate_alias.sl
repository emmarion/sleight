; expect: 3
; The body's `delegate` call need only name a callee that canonicalizes to the one its header names (section 19).
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many g at inc : (many (Nat) n) -> (many (Nat) m))
  (let ((many h)) inc)
  (delegate (h n)))
(let ((erased p)) (coercible-of (delegate-of g)))
(g 2)
