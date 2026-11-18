(def-adts $ (Fm : -> Type)
  enum
  (many Bot : -> (Fm))
  (many Imp : (many (Fm) a) (many (Fm) b) -> (Fm))
  (many Pv : (many (Fm) a) -> (Fm))
  (many Txt : (many (String) s) -> (Fm)))

(def-adts $ (Hbl : ((TyCtor ((Fm) c) -> Type) P) ((Fm) g) -> Type)
  enum
  (many MkHbl : (erased (TyCtor ((Fm) c) -> Type) P) (erased (Fm) g) (erased (Level) K)
     (erased (Fn K (erased (Fm) a) (erased (Fm) b) (erased (P (Imp a b)) pab) (erased (P a) pa) -> (erased (P b) pb)) d2)
     (erased (Fn K (erased (Fm) a) (erased (P a) pa) -> (erased (P (Pv a)) ppa)) d3)
     (erased (P (Imp g (Imp (Pv g) (Bot)))) dg)
     -> (Hbl P g)))

(def-adts $ (NotP : ((TyCtor ((Fm) c) -> Type) P) ((Fm) f) -> Type)
  enum
  (many MkNotP : (erased (TyCtor ((Fm) c) -> Type) P) (erased (Fm) f) (erased (Level) K)
     (erased (Fn K (erased (P f) p) -> (erased (False) no)) n) -> (NotP P f)))

(def-fns _ $ (erased con-to-g : (erased (TyCtor ((Fm) c) -> Type) P) (erased (Fm) g)
    (erased (Hbl P g) h) (erased (NotP P (Bot)) con) -> (erased (NotP P g) r))
  (let-match erased h (MkHbl _ _ K d2 d3 dg))
  (let-match erased con (MkNotP _ _ KC c))
  (def-lvl N)
  (def-fns N $ (erased ng : (erased (P g) p) -> (erased (False) no))
    (c $ d2 _ _ (d2 _ _ dg p) (d3 _ p)))
  (MkNotP P g N ng))
