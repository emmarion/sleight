; error: argument 2, `b`, of `MkC`: type mismatch: expected `(False)`, got `(Unit)`
(def-adts $ (C : -> Type) enum (many MkC : (erased (False) a) (many a is b) -> (C)))
(def-fns _ $ (many absurd boom : (many (False) f) -> (many (Nat) n)) f)
(def-fns _ $ (many un : (many (C) c) -> (many (Nat) n)) (let-match many c (MkC a b)) (boom b))
(un (MkC _ (MkUnit)))
