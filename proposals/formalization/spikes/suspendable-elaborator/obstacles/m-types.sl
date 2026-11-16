(def-lvl W)
(def-lvl K)

(def-adts $ (CM : -> Type)
  enum
  (many CRet : (many (Nat) v) -> (CM))
  (many CBind : (many (CM) m) (many (Fn K (many (Nat) v) -> (many (CM) next)) f) -> (CM)))
