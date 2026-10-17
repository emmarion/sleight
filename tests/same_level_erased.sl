; expect: 0
; A same-level call in an erased position does not warn, even inside a function that runs: the call
; compiles to nothing, so there is no stack to grow. Each erased position is taken once -- an erased let
; binder's right-hand side, an argument at an erased parameter inside a non-erased call, an erased match,
; and a binder's type -- and the file earns no warning at all.

(def-fns _
  ((many walk : (subterm many (List (Nat)) xs) (erased (List (Nat)) _ghost) -> (many (Nat) n))
    (let-match many xs (Cons _ _ rest) ((Nil _) (Zero)))
    (let ((erased _)) (walk rest rest))
    (let ((many r)) (tail $ walk rest (Cons (Nat) (walk rest rest) (Nil (Nat)))))
    (let ((erased _)) (match erased rest (((Nat) k)) ((Nil _) (Zero)) ((Cons _ _ t2) (walk t2 t2))))
    (let ((erased (Nat) _)) (Zero))
    r))
(walk (Cons (Nat) 1 $ Nil (Nat)) (Nil (Nat)))
