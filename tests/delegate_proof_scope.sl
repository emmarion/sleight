; expect: 7
; A `Delegate` proof is minted with its function's header (section 41), so it is in scope in every body of the
; block, the function's own included, and a signature sees the functions before it in its block (section 53).
(def-fns _ $ (many ident : (many (Nat) x) -> (many (Nat) r)) x)
(def-fns _
  ((many a at ident : (many (Nat) x) -> (many (Nat) r))
    (let ((erased _)) (delegate-of a))
    (let ((erased _)) (delegate-of c))
    (delegate (ident x)))
  ((many b : -> (many (Fn (level-of a) (many (Nat) y) -> (many (Nat) s)) f))
    (let ((erased _)) (delegate-of a))
    a)
  ((many c at ident : (many (Nat) x) -> (many (Nat) r))
    (delegate (ident x))))
(let ((erased p)) (coercible-of (delegate-of c)))
(let ((many f)) (b))
(f ((coerce c p) 7))
