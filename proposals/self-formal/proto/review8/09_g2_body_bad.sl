(def-fns _ $ (erased fin : (erased (NotP Triv g) x) -> (erased (False) f))
  (let-match erased x (MkNotP _ _ N2 n2))
  (n2 (MkTriv g)))
