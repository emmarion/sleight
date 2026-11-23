(def-fns _ $ (many smoke : -> (many (Res (Span l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) 1000)) r))
  (let ((many e) (erased ch)) (rrun l3 _ 10000000 (MkRq (Zero) (Nil (Rn)) (BFalse) (Nil (Rn))) (rch0 l3)))
  (let-match many (span-check l3 1000 e ch) (SpOk _ _ _ sp) ((SpLow _ _ _ got) (RFail _)))
  (ROk _ sp))
(let ((many sres)) (native-compute smoke))
(comptime-match many sres (ROk _ sp))

(def-fns _ $ (erased bound : (erased (Nat) k) (erased (HaltsAt l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) k) h) -> (erased (Lt 1000 k) p))
  (span-bound l3 _ 1000 k sp h))

(goal erased (NoHaltBelow l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) 1000))
(qed (MkNHB l3 _ 1000 (level-of bound) bound))
