; error: `at` is allowed only on function telescope and match annotation entries
(def-adts $ (Box : ((Nat) n) ((Nat) m at n) -> Type) enum (many MkBox : -> (Box 0 0)))
