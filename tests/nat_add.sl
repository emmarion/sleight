; needs: list
; expect: (Succ (Succ (Succ (Succ (Succ (Zero))))))
; A second return entry mentioning the parameters, inherited by _ (SUGAR.md section 2).
(def-adts
  (Add : ((Nat) a) ((Nat) b) ((Nat) c) -> Type
    enum
    (many AddZero : (erased (Nat) b) -> (Add (Zero) b b))
    (many AddSucc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Add a b c) q) -> (Add (Succ a) b (Succ c)))))

(def-fns _ $ many add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c) (erased (Add a b c) p)
  (match many a _
    ((Zero) (values b (AddZero b)))
    ((Succ k)
      (let (many c) (erased q) (add (subterm _) k b))
      (values (Succ c) (AddSucc k b c q)))))

(let (many two) (Succ (Succ (Zero))))
(let (many s) (erased p) (add two (Succ two)))
s
