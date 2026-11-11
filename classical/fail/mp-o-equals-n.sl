(def-lvl N0)
(def-adts $ (MB : ((Nat) i) -> Type)
  enum
  (many MkMB : (erased (Nat) i) (many (Fn N0 (erased (Ex MB) x) -> (erased (False) f)) g) -> (MB i)))
(def-fns N0 $ (erased nn : (erased (Fn N0 (erased (Ex MB) x) -> (erased (False) f)) ne) -> (erased (False) f))
  (ne (MkEx MB (Zero) (MkMB (Zero) ne))))
