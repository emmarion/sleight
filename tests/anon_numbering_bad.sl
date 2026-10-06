(let ((many fs))
  (def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
    (Succ n))
  (Cons _ inc (Nil _)))
(let ((many gs))
  (def-fns _ $ (many dec : (many (Nat) n) -> (many (Nat) m))
    n)
  (Cons _ dec fs))
(Zero)
; error: error: argument 3, `rest`, of `Cons`: type mismatch: expected `(List (Fn (level-of dec) (many (Nat) n) -> (many (Nat) m)))`, got `(List (Fn _1 (many (Nat) n) -> (many (Nat) m)))`
; error: tests/anon_numbering_bad.sl:2:12: note: `_1` is anonymous, minted here
