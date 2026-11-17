(def-fns _ $ (many fuel-factory : (erased (Level) M) (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R)
    (many (Fn M (many (Nat) n) -> (many (Nat) m) (erased (R (Succ n) m) p)) step) ->
    (erased (Level) L)
    (many (Fn L (subterm many (Nat) f) (many (Nat) s) -> (many (FuelRes R s f) r)) run))
  (def-fns _ $ (many run : (subterm many (Nat) f) (many (Nat) s) -> (many (FuelRes R s f) r))
    (match many s _
      ((Zero) (FDone R (Zero) f (Zero) (RDone R)))
      ((Succ n)
        (match many f _
          ((Zero) (FOut R (Succ n) (Zero) n (PZ R (Succ n))))
          ((Succ f1)
            (let ((many m) (erased st)) (step n))
            (let ((many res)) (run f1 m))
            (match many res _
              ((FDone _ _ _ k r) (FDone R (Succ n) (Succ f1) (Succ k) (RStep R n m k st r)))
              ((FOut _ _ _ t p) (FOut R (Succ n) (Succ f1) t (PS R n m f1 (Succ t) st p)))))))))
  (values (level-of run) run))
