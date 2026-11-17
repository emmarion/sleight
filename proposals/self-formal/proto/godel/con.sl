(def-adts $ (Con : -> Type)
  enum
  (many MkCon : (erased (Level) L) (erased (Fn L (erased (Deriv (Bot)) d) -> (erased (False) no)) c) -> (Con)))
(goal erased (Con))

(def-fns _ $ (erased ev-total : (subterm erased (Fm) f) -> (erased (Bool) v) (erased (Ev f v) e))
  (let-match erased f (Imp a b) ((Bot) (values (BFalse) (EvBot))) ((At n) (values (BTrue) (EvAt n))))
  (let ((erased va) (erased ea)) (ev-total a))
  (let ((erased vb) (erased eb)) (ev-total b))
  (let-match erased va (BTrue) ((BFalse) (values (BTrue) (EvImpT1 a b ea))))
  (match erased vb _
    ((BTrue) (values (BTrue) (EvImpT2 a b eb)))
    ((BFalse) (values (BFalse) (EvImpF a b ea eb)))))

(def-fns _ $ (erased ev-apart : (subterm erased (Fm) f) (erased (Ev f (BTrue)) t) (erased (Ev f (BFalse)) u) -> (erased (False) no))
  (match erased f _
    ((Bot) (match erased t _))
    ((At n) (match erased u _))
    ((Imp a b)
      (let-match erased u (EvImpF _ _ ua ub))
      (match erased t _
        ((EvImpT1 _ _ ta) (ev-apart a ua ta))
        ((EvImpT2 _ _ tb) (ev-apart b tb ub))))))

(def-fns _ $ (erased sound : (erased (Fm) f) (subterm erased (Deriv f) d) -> (erased (Ev f (BTrue)) e))
  (match erased d _
    ((AxK a b)
      (let ((erased va) (erased ea)) (ev-total a))
      (match erased va _
        ((BFalse) (EvImpT1 _ _ ea))
        ((BTrue) (EvImpT2 _ _ (EvImpT2 _ _ ea)))))
    ((MP a b dab da)
      (let ((erased eab)) (sound _ dab))
      (let ((erased ea)) (sound _ da))
      (match erased eab _
        ((EvImpT2 _ _ eb) eb)
        (absurd (EvImpT1 _ _ fa) (ev-apart a ea fa))))))

(def-fns _ $ (erased con : (erased (Deriv (Bot)) d) -> (erased (False) no))
  (match erased (sound _ d) _))

(qed (MkCon _ con))
