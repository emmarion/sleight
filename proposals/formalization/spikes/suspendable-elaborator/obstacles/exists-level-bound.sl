(def-lvl TOP)
(def-lvl BL)

(def-adts $ (BoundedM : (Type A) -> Type)
  enum
  (many BRet : (erased Type A) (many A a) -> (BoundedM A))
  (many BAsk : (erased Type A) (erased (Level) L) (erased (Predates (Level) L TOP) below) (many (Nat) s)
     (many (Fn L (many (Nat) a) (erased (Runs s a) p) -> (many (BoundedM A) next)) k) -> (BoundedM A)))

(def-fns BL $ (many rebind : (erased Type A) (erased (Level) L) (many (Nat) s)
    (many (Fn L (many (Nat) a) (erased (Runs s a) p) -> (many (BoundedM A) next)) k) -> (many (BoundedM A) r))
  (def-lvl L2)
  (def-fns L2 $ (many k2 : (many (Nat) a) (erased (Runs s a) p) -> (many (BoundedM A) next))
    (k a p))
  (BAsk _ L2 (prove-predates L2 TOP) s k2))

(MkUnit)
