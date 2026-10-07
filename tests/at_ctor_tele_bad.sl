; error: `at` is allowed only on function telescope and match annotation entries
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Nat) n) (many (Nat) m at n) -> (Box)))
