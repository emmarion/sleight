(def-adts $ (Model : ((TyCtor ((Nat) a) ((Nat) b) -> Type) R) -> Type)
  enum
  (many MkModel : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Level) M)
     (many (Fn M (many (Nat) n) -> (many (Nat) m) (erased (R (Succ n) m) p)) step)
     (erased (Fn M (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (R n a) p) (erased (R n b) q) -> (erased (Eq (Nat) a b) e)) det)
     -> (Model R)))
(def-fns _ $ (many run-from-model : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (many (Model R) md) ->
    (erased (Level) L)
    (many (Fn L (many (Nat) s) (subterm erased (Halts R s) h) -> (many (Nat) k) (erased (RunsTo R s k) r)) run))
  (let-match many md (MkModel _ M step det))
  (run-factory M R step det))
