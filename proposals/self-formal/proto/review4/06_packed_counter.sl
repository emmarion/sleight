; Fourth review of 06: a closure state that packs its level L, a Predates from L to a stepper level S minted
; first, and an erased step counter. A step at S extends the closure at the same packed level L, and a function
; at S applies it. Needs std/list.sl, spec.sl and machine.sl first.
(def-lvl S)
(def-adts $ (PState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many PSt : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Nat) n)
     (erased (Level) L) (erased (Predates (Level) L S) pr) (erased (Predates (Level) (level-of step-back) L) pb)
     (erased (Fn L (subterm erased (Nat) j) (erased (Eq (Nat) j n) e) (erased (Mem) mf) (erased (RunsAll m k mf) a)
        -> (erased (Runs m0 c0 mf) d)) inv) -> (PState c0 m0)))
(def-adts $ (PAdv : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many PNext : (erased (Cmd) c0) (erased (Mem) m0) (many (PState c0 m0) st) -> (PAdv c0 m0))
  (many PEnd : (erased (Cmd) c0) (erased (Mem) m0) (many (Outcome c0 m0) o) -> (PAdv c0 m0)))
(def-fns S $ (many adv-p : (erased (Cmd) c0) (erased (Mem) m0) (many (PState c0 m0) st) -> (many (PAdv c0 m0) r))
  (let-match many st (PSt _ _ k m n L pr pb inv))
  (let-match many (step k m) (SNext _ _ k2 m2 s)
    ((SHalt _) (PEnd _ _ (Halted _ _ m (inv (predates pr) n (Refl _ n) m (RANil m)))))
    ((SStuck _ _) (PEnd _ _ (Stuck _ _))))
  (def-fns L $ (erased inv2 : (subterm erased (Nat) j) (erased (Eq (Nat) j (Succ n)) e) (erased (Mem) mf)
      (erased (RunsAll m2 k2 mf) a) -> (erased (Runs m0 c0 mf) d))
    (let-match erased e (Refl _ _))
    (inv n (Refl _ n) mf (step-back (predates pb) k k2 m m2 mf s a)))
  (PNext _ _ (PSt c0 m0 k2 m2 (Succ n) L pr pb inv2)))
