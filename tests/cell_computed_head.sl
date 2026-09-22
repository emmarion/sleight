; expect: 1
(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(let ((many x)) ((cell-alloc B) (Succ (Zero))))
(let-match many x (B n))
n
