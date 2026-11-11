(def-fns _ $ (many no-llpo : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) D) (erased (Level) E) (erased (Level) A)
        (erased (Predates (Level) E N) en)
        (erased (TyCtor ((Nat) n) -> Type) Q)
        (erased (Fn D (erased (Nat) n) -> (erased (Or (Q n) (Fn E (erased (Q n) q) -> (erased (False) f))) r)) dec)
        (erased (Fn A (erased (Nat) n) (erased (Nat) m) (erased (Q n) qn) (erased (Q m) qm) -> (erased (Eq (Nat) n m) e)) amo) ->
        (erased (Or (Fn N (erased (Nat) n) (erased (Even n) e) (erased (Q n) q) -> (erased (False) f))
                    (Fn N (erased (Nat) n) (erased (Odd n) o) (erased (Q n) q) -> (erased (False) f))) r)) llpo) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl E)
  (def-lvl N)
  (let ((erased en)) (prove-predates E N))
  (def-adts $ (LQ : ((Nat) i) -> Type)
    enum
    (many MkQ0 : (many (Fn N (erased (Nat) n) (erased (Even n) e) (erased (LQ n) q) -> (erased (False) f)) er) -> (LQ (Zero)))
    (many MkQ1 : (many (Fn N (erased (Nat) n) (erased (Odd n) o) (erased (LQ n) q) -> (erased (False) f)) od) -> (LQ (Succ (Zero)))))
  (def-lvl A)
  (def-fns A $ (erased absurd amo : (erased (Nat) n) (erased (Nat) m) (erased (LQ n) qn) (erased (LQ m) qm) -> (erased (Eq (Nat) n m) e))
    (match erased qn _
      (absurd (MkQ0 er) (er (Zero) (EvZ) qn))
      (absurd (MkQ1 od) (od (Succ (Zero)) (OdO) qn))))
  (def-fns _ $ (erased absurd dec : (erased (Nat) n) -> (erased (Or (LQ n) (Fn E (erased (LQ n) q) -> (erased (False) f))) r))
    (match erased (llpo N (level-of dec) E A en LQ dec amo) _
      (absurd (Inl _ _ er) (er (Zero) (EvZ) (MkQ0 er)))
      (absurd (Inr _ _ od) (od (Succ (Zero)) (OdO) (MkQ1 od)))))
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (llpo N (level-of dec) E A en LQ dec amo) _
      (absurd (Inl _ _ er) (er (Zero) (EvZ) (MkQ0 er)))
      (absurd (Inr _ _ od) (od (Succ (Zero)) (OdO) (MkQ1 od)))))
  (values (level-of absurdity) absurdity))
