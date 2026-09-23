; expect: 0
; A same-level call in an erased position does not warn, even inside a function that runs: the call
; compiles to nothing, so there is no stack to grow. Each erased position is taken once -- an erased let
; binder's right-hand side, an argument at an erased parameter inside a non-erased call, an erased match,
; and a binder's type -- and the file earns no warning at all.

(def-fns _
  ((many walk : (subterm many (List (Nat)) xs) (erased (List (Nat)) ghost) -> (many (Nat) n))
    (match many xs _
      ((Nil _) (Zero))
      ((Cons _ h rest)
        (let ((erased e1)) (walk rest rest))
        (let ((many r)) (tail $ walk rest (Cons (Nat) (walk rest rest) (Nil (Nat)))))
        (let ((erased e3)) (match erased rest (((Nat) k)) ((Nil _) (Zero)) ((Cons _ _ t2) (walk t2 t2))))
        (let ((erased (Nat) e4)) (Zero))
        r))))
(walk (Cons (Nat) 1 $ Nil (Nat)) (Nil (Nat)))
