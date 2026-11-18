(def-adts $ (Triv : ((Fm) c) -> Type)
  enum
  (many MkTriv : (erased (Fm) c) -> (Triv c)))
(def-fns _
  ((erased d2 : (erased (Fm) a) (erased (Fm) b) (erased (Triv (Imp a b)) pab) (erased (Triv a) pa) -> (erased (Triv b) pb))
    (MkTriv b))
  ((erased d3 : (erased (Fm) a) (erased (Triv a) pa) -> (erased (Triv (Pv a)) ppa))
    (MkTriv (Pv a))))
(let ((erased g)) (Txt (SNil)))
(let ((erased h)) (MkHbl Triv g (level-of d2) d2 d3 (MkTriv (Imp g (Imp (Pv g) (Bot))))))
(let ((erased con)) (gensym-unique (NotP Triv (Bot))))
(let ((erased ng)) (con-to-g Triv g h con))
(let-match erased ng (MkNotP _ _ N n))
(let ((erased (False) bot)) (n (MkTriv g)))
