; expect: (Cons _ 7 $ Cons _ 9 $ Cons _ 11 $ Nil _)
; Index refinement selects a middle runtime tag, both in a body and in run position.
; The same rule applies to unions, without changing their runtime representation.
(def-adts $ (Choice : ((Nat) i) -> Type) enum
  (many First : (many (Nat) x) -> (Choice (Zero)))
  (many Middle : (many (Nat) x) -> (Choice (Succ (Zero))))
  (many Last : (many (Nat) x) -> (Choice (Succ (Succ (Zero))))))
(def-fns _ $ (many middle-value : (many (Choice (Succ (Zero))) x) -> (many (Nat) n))
  (let-match many x (Middle n))
  n)
(def-fns _ $ (many indexed-main : -> (many (Nat) n))
  (middle-value (Middle 7)))
(let ((many chosen)) (Middle 9))
(let-match many chosen (Middle chosen-n))
(def-adts $ (UChoice : ((Nat) i) -> Type) union
  (many UFirst : (many (Nat) x) -> (UChoice (Zero)))
  (many ULast : (many (Nat) x) -> (UChoice (Succ (Zero)))))
(def-fns _ $ (many union-value : (many (UChoice (Succ (Zero))) x) -> (many (Nat) n))
  (let-match many x (ULast n))
  n)
(def-fns _ $ (many union-main : -> (many (Nat) n))
  (union-value (ULast 11)))

(def-fns _ $ (many indexed-tests : -> (many (List (Nat)) results))
  (Cons _ (indexed-main) (Cons _ chosen-n (Cons _ (union-main) (Nil _)))))
indexed-tests
