(def-fns _ $ (many numeral : (subterm many (Nat) n) (many (Core) acc) -> (many (Core) c))
  (let-match many n (Succ m) ((Zero) acc))
  (tail $ numeral m (CApp (CVar 12) (Cons _ acc (Nil _)))))

(let ((many zero)) (CApp (CVar 11) (Nil _)))
(let ((many one)) (CApp (CVar 12) (Cons _ zero (Nil _))))

(def-fns _ $ (many parity-fn : (many (Nat) id) (many (Nat) x) (many (Nat) y) (many (Core) base) (many (Nat) other) -> (many (FnDef) d))
  (MkFnDef id (Cons _ x (Nil _))
    (CMatch (CVar x)
      (Cons _ (MkBranch 11 (Nil _) base)
        (Cons _ (MkBranch 12 (Cons _ y (Nil _)) (CCall (CVar other) (Cons _ (CVar y) (Nil _)))) (Nil _))))))

(let ((many tree-fn))
  (MkFnDef 19 (Cons _ 20 (Nil _))
    (CMatch (CVar 20)
      (Cons _ (MkBranch 11 (Nil _) zero)
        (Cons _ (MkBranch 12 (Cons _ 21 (Nil _))
                  (CMatch (CCall (CVar 19) (Cons _ (CVar 21) (Nil _)))
                    (Cons _ (MkBranch 11 (Nil _) (CCall (CVar 19) (Cons _ (CVar 21) (Nil _))))
                      (Cons _ (MkBranch 12 (Cons _ 22 (Nil _)) zero) (Nil _)))))
          (Nil _))))))

(def-fns _ $ (many with-decls : (many (Core) rest) -> (many (Core) c))
  (CStmt (SDefAdts (Cons _ 10 (Cons _ 11 (Cons _ 12 (Nil _)))))
    (CStmt (SDefFns (Cons _ (parity-fn 13 14 15 zero 16) (Cons _ (parity-fn 16 17 18 one 13) (Nil _))))
      (CStmt (SDefFns (Cons _ tree-fn (Nil _))) rest))))

(def-fns _ $ (many parity-of : (many (Nat) n) -> (many (Core) c))
  (CCall (CVar 13) (Cons _ (numeral n zero) (Nil _))))

(def-fns _ $ (many deep-program : (many (Nat) n) -> (many (Core) c))
  (with-decls (parity-of n)))

(def-fns _ $ (many wide-program : (many (Nat) k) (many (Nat) n) -> (many (Core) c))
  (with-decls (CStmt (SLet (Cons _ 23 (Nil _)) (CCall (CVar 19) (Cons _ (numeral k zero) (Nil _)))) (parity-of n))))

(MkUnit)
