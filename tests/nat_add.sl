; needs: list
; expect: 5
; A second return entry mentioning the parameters, reused by _ (SUGAR.md section 2).
(def-adts
  ((Plus : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many PlusZero : (erased (Nat) b) -> (Plus (Zero) b b))
    (many PlusSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) q) -> (Plus (Succ a) b (Succ c)))))

(def-fns _ $ (many plus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Plus a b c) pa))
  (match many a _
    ((Zero) (values b (PlusZero b)))
    ((Succ k)
      (let ((many c) (erased q)) (plus (subterm _) k b))
      (values (Succ c) (PlusSucc k b c q)))))

(let ((many two)) (Succ (Succ (Zero))))
(let ((many s) (erased pa)) (plus two (Succ two)))
s
