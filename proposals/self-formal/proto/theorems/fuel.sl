(def-adts $ (Prefix : ((TyCtor ((Nat) a) ((Nat) b) -> Type) R) ((Nat) s) ((Nat) k) ((Nat) t) -> Type)
  enum
  (many PZ : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) s) -> (Prefix R s (Zero) s))
  (many PS : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) n) (erased (Nat) m) (erased (Nat) k) (erased (Nat) t)
     (erased (R (Succ n) m) st) (erased (Prefix R m k t) p) -> (Prefix R (Succ n) (Succ k) t)))

(def-adts $ (FuelRes : ((TyCtor ((Nat) a) ((Nat) b) -> Type) R) ((Nat) s) ((Nat) f) -> Type)
  enum
  (many FDone : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) s) (erased (Nat) f)
     (many (Nat) k) (erased (RunsTo R s k) r) -> (FuelRes R s f))
  (many FOut : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) s) (erased (Nat) f)
     (erased (Nat) t) (erased (Prefix R s f (Succ t)) p) -> (FuelRes R s f)))

(def-fns _ $ (erased bound-factory : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Level) M)
    (erased (Fn M (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (R n a) p) (erased (R n b) q) -> (erased (Eq (Nat) a b) e)) det) ->
    (erased (Level) L) (erased (Fn L (erased (Nat) s) (erased (Nat) k) (erased (Nat) n) (erased (Nat) t)
        (erased (RunsTo R s k) r) (subterm erased (Prefix R s n (Succ t)) p) -> (erased (Lt n k) lt)) bnd))
  (def-fns _ $ (erased bound : (erased (Nat) s) (erased (Nat) k) (erased (Nat) n) (erased (Nat) t)
      (erased (RunsTo R s k) r) (subterm erased (Prefix R s n (Succ t)) p) -> (erased (Lt n k) lt))
    (match erased p _
      ((PZ _ _)
        (match erased r _
          ((RStep _ n0 m k0 st r1) (LtZ k0))))
      ((PS _ n0 m k1 _ st p1)
        (let-match erased r (RStep _ _ m2 k2 st2 r2))
        (let ((erased e)) (det (Succ n0) m m2 st st2))
        (let-match erased e (Refl _ _))
        (let ((erased sp)) (prove-subterm p1 p))
        (let ((erased l)) (bound m k2 k1 t r2 (subterm sp) p1))
        (LtS k1 k2 l))))
  (values (level-of bound) bound))
