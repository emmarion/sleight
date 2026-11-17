(def-adts $ (Four : -> Type) enum (many A0 : -> (Four)) (many A1 : -> (Four)) (many A2 : -> (Four)) (many A3 : -> (Four)))
(def-fns _ $ (many id-at : (many (Four) c) (many (Nat) n at c) -> (many (Nat) r)) n)
(let ((many c)) (A3))
(id-at c 3)
