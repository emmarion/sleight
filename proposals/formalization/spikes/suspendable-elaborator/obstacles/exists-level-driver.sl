(def-lvl D)

(def-fns D $ (many resume : (erased Type A) (many (SomeM A) m) (many (Nat) s0 a0) (erased (Runs s0 a0) p0) -> (many (SomeM A) r))
  (match many m _
    ((PackRet _ x) (PackRet _ x))
    ((PackAsk _ L s k)
      (let-match many (nat-eq s s0) (Equal _ _ _) ((Unequal _ _ _ _ _) m))
      (k a0 p0))))

(MkUnit)
