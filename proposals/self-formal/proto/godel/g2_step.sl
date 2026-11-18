(def-adts $ (G2Step : -> Type)
  enum
  (many MkG2Step : (erased (Level) L)
     (erased (Fn L (erased (TyCtor ((Fm) c) -> Type) P) (erased (Fm) g)
                   (erased (Hbl P g) h) (erased (NotP P (Bot)) con) -> (erased (NotP P g) r)) f)
     -> (G2Step)))

(goal erased (G2Step))
(qed (MkG2Step _ con-to-g))
