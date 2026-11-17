(def-adts $ (Fm : -> Type)
  enum
  (many Bot : -> (Fm))
  (many At : (many (Nat) n) -> (Fm))
  (many Imp : (many (Fm) a) (many (Fm) b) -> (Fm)))

(def-adts $ (Deriv : ((Fm) f) -> Type)
  enum
  (many AxK : (erased (Fm) a) (erased (Fm) b) -> (Deriv (Imp a (Imp b a))))
  (many MP : (erased (Fm) a) (erased (Fm) b) (erased (Deriv (Imp a b)) dab) (erased (Deriv a) da) -> (Deriv b)))

(def-adts $ (Ev : ((Fm) f) ((Bool) v) -> Type)
  enum
  (many EvBot : -> (Ev (Bot) (BFalse)))
  (many EvAt : (erased (Nat) n) -> (Ev (At n) (BTrue)))
  (many EvImpF : (erased (Fm) a) (erased (Fm) b) (erased (Ev a (BTrue)) ea) (erased (Ev b (BFalse)) eb) -> (Ev (Imp a b) (BFalse)))
  (many EvImpT1 : (erased (Fm) a) (erased (Fm) b) (erased (Ev a (BFalse)) ea) -> (Ev (Imp a b) (BTrue)))
  (many EvImpT2 : (erased (Fm) a) (erased (Fm) b) (erased (Ev b (BTrue)) eb) -> (Ev (Imp a b) (BTrue))))
