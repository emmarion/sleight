(def-lvl W)
(def-lvl K)

(def-adts $ (ElabM : (Type A) -> Type)
  enum
  (many Ret : (erased Type A) (many A a) -> (ElabM A))
  (many Ask : (erased Type A) (many (Nat) s) (many (Fn K (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next)) k) -> (ElabM A)))
