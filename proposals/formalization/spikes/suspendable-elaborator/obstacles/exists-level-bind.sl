(def-adts $ (SomeM : (Type A) -> Type)
  enum
  (many PackRet : (erased Type A) (many A a) -> (SomeM A))
  (many PackAsk : (erased Type A) (erased (Level) L) (many (Nat) s)
     (many (Fn L (many (Nat) a) (erased (Runs s a) p) -> (many (SomeM A) next)) k) -> (SomeM A)))

(def-lvl B)

(def-fns B $ (many bind-ask : (erased Type A) (erased (Level) L) (many (Nat) s)
    (many (Fn L (many (Nat) a) (erased (Runs s a) p) -> (many (SomeM A) next)) k) -> (many (SomeM A) r))
  (def-lvl L2)
  (def-fns L2 $ (many k2 : (many (Nat) a) (erased (Runs s a) p) -> (many (SomeM A) next))
    (match many (k a p) _
      ((PackRet _ x) (PackRet _ x))
      ((PackAsk _ L3 s3 k3) (bind-ask _ L3 s3 k3))))
  (PackAsk _ L2 s k2))
(MkUnit)
