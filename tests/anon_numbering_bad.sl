(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many dec : (many (Nat) n) -> (many (Nat) m))
  n)
(def-fns _ $ (many app : (many (Fn (level-of inc) (many (Nat) n) -> (many (Nat) m)) f) (many (Nat) x) -> (many (Nat) m))
  (f x))
(app dec 3)
; error: error: type mismatch: expected `(Fn _1 (many (Nat) n) -> (many (Nat) m))`, got `(Fn _2 (many (Nat) n) -> (many (Nat) m))`
; error: tests/anon_numbering_bad.sl:1:10: note: `_1` is anonymous, minted here
; error: tests/anon_numbering_bad.sl:3:10: note: `_2` is anonymous, minted here
