(def-adts $ (Halts : ((TyCtor ((Nat) a) ((Nat) b) -> Type) R) ((Nat) s) -> Type)
  enum
  (many HDone : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) -> (Halts R (Zero)))
  (many HStep : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) n) (erased (Nat) m)
     (erased (R (Succ n) m) st) (erased (Halts R m) h) -> (Halts R (Succ n))))

(def-adts $ (RunsTo : ((TyCtor ((Nat) a) ((Nat) b) -> Type) R) ((Nat) s) ((Nat) k) -> Type)
  enum
  (many RDone : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) -> (RunsTo R (Zero) (Zero)))
  (many RStep : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R) (erased (Nat) n) (erased (Nat) m) (erased (Nat) k)
     (erased (R (Succ n) m) st) (erased (RunsTo R m k) h) -> (RunsTo R (Succ n) (Succ k))))

(def-fns _ $ (many run-factory : (erased (Level) M) (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) R)
    (many (Fn M (many (Nat) n) -> (many (Nat) m) (erased (R (Succ n) m) p)) step)
    (erased (Fn M (erased (Nat) n) (erased (Nat) a) (erased (Nat) b) (erased (R n a) p) (erased (R n b) q) -> (erased (Eq (Nat) a b) e)) det) ->
    (erased (Level) L)
    (many (Fn L (many (Nat) s) (subterm erased (Halts R s) h) -> (many (Nat) k) (erased (RunsTo R s k) r)) run))
  (def-fns _ $ (many run : (many (Nat) s) (subterm erased (Halts R s) h) -> (many (Nat) k) (erased (RunsTo R s k) r))
    (match many s _
      ((Zero) (values (Zero) (RDone R)))
      ((Succ n)
        (let ((many m2) (erased st2)) (step n))
        (let-match erased h (HStep _ _ m st h1))
        (let ((erased e)) (det (Succ n) m m2 st st2))
        (let-match erased e (Refl _ _))
        (let ((erased sp)) (prove-subterm h1 h))
        (let ((many k) (erased r)) (run m2 (subterm sp) h1))
        (values (Succ k) (RStep R n m2 k st2 r)))))
  (values (level-of run) run))
