(def-fns _ $ (many no-llpo : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) D) (erased (Level) E) (erased (Level) A)
        (erased (Predates (Level) A N) an)
        (erased (TyCtor ((Nat) n) -> Type) Q)
        (erased (Fn D (erased (Nat) n) -> (erased (Or (Q n) (Fn E (erased (Q n) q) -> (erased (False) f))) r)) dec)
        (erased (Fn A (erased (Nat) n) (erased (Nat) m) (erased (Q n) qn) (erased (Q m) qm) -> (erased (Eq (Nat) n m) e)) amo) ->
        (erased (Or (Fn N (erased (Nat) n) (erased (Even n) e) (erased (Q n) q) -> (erased (False) f))
                    (Fn N (erased (Nat) n) (erased (Odd n) o) (erased (Q n) q) -> (erased (False) f))) r)) llpo) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl A)
  (def-lvl N)
  (let ((erased an)) (prove-predates A N))
  (def-adts $ (LQ : ((Nat) i) -> Type)
    enum
    (many MkQ0 : (many (Fn N (erased (Nat) n) (erased (Even n) e) (erased (LQ n) q) -> (erased (False) f)) er) -> (LQ (Zero)))
    (many MkQ1 : (many (Fn N (erased (Nat) n) (erased (Odd n) o) (erased (LQ n) q) -> (erased (False) f)) od) -> (LQ (Succ (Zero)))))
  (def-fns A
    ((erased absurd dec : (erased (Nat) n) -> (erased (Or (LQ n) (Fn A (erased (LQ n) q) -> (erased (False) f))) r))
      (match erased (llpo N A A A an LQ dec amo) _
        (absurd (Inl _ _ er) (er (Zero) (EvZ) (MkQ0 er)))
        (absurd (Inr _ _ od) (od (Succ (Zero)) (OdO) (MkQ1 od)))))
    ((erased absurd amo : (erased (Nat) n) (erased (Nat) m) (erased (LQ n) qn) (erased (LQ m) qm) -> (erased (Eq (Nat) n m) e))
      (match erased (llpo N A A A an LQ dec amo) _
        (absurd (Inl _ _ er) (er (Zero) (EvZ) (MkQ0 er)))
        (absurd (Inr _ _ od) (od (Succ (Zero)) (OdO) (MkQ1 od))))))
  (values))
