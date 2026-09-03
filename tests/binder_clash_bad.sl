; error: branch MkTag is refuted

(def-lvl L)
(def-adts
  (Tag : (Type A) -> Type
    enum
    (many MkTag : -> (Tag (Fn L (many (Nat) x) -> (many x is y))))))
(def-lvl M)
(def-fns M $ many probe : (erased (Nat) k)
    (many (Tag (Fn L (many (Nat) x) -> (many k is y))) t) -> (many (Nat) r)
  (match many t (((Nat) r))
    ((MkTag) (Zero))))
