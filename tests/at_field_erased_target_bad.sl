; error: `at` needs a variable declared `many` or `unique`
(def-adts $ (B : -> Type) enum (many MkB : (erased (Nat) n) (many (Nat) m at n) -> (B)))
