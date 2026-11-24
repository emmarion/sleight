(def-fns _ $ (many smoke10 : -> (many (Res (Span l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) 10000)) r))
  (let ((many left) (many e) (erased ch)) (c10run _ 3000000 (MkRq (Zero) (Nil (Rn)) (BFalse) (Nil (Rn))) (rch0 l3)))
  (let-match many (span-check l3 10000 e ch) (SpOk _ _ _ sp) ((SpLow _ _ _ got) (RFail _)))
  (ROk _ sp))
(let ((many sres)) (native-compute smoke10))
(comptime-match many sres (ROk _ sp))

(def-fns _ $ (erased bound : (erased (Nat) k) (erased (HaltsAt l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) k) h) -> (erased (Lt 10000 k) p))
  (span-bound l3 _ 10000 k sp h))

(goal erased (NoHaltBelow l3 (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) 10000))
(qed (MkNHB l3 _ 10000 (level-of bound) bound))
