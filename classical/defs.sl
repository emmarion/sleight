(def-adts $ (Or : (Type A) (Type B) -> Type)
  enum
  (many Inl : (erased Type A) (erased Type B) (many A a) -> (Or A B))
  (many Inr : (erased Type A) (erased Type B) (many B b) -> (Or A B)))

(def-adts $ (IsProp : ((Level) L) (Type P) -> Type)
  enum
  (many MkIsProp : (erased (Level) L) (erased Type P)
     (erased (Fn L (erased P x) (erased P y) -> (erased (Eq P x y) e)) all-eq) ->
     (IsProp L P)))
(def-adts $ (Ex : ((TyCtor ((Nat) n) -> Type) Q) -> Type)
  enum
  (many MkEx : (erased (TyCtor ((Nat) n) -> Type) Q) (many (Nat) n) (erased (Q n) q) -> (Ex Q)))

(def-adts
  ((Even : ((Nat) n) -> Type)
    enum
    (many EvZ : -> (Even (Zero)))
    (many EvSS : (erased (Nat) n) (erased (Even n) e) -> (Even (Succ (Succ n)))))
  ((Odd : ((Nat) n) -> Type)
    enum
    (many OdO : -> (Odd (Succ (Zero))))
    (many OdSS : (erased (Nat) n) (erased (Odd n) o) -> (Odd (Succ (Succ n))))))
