; Refused (third review): a packed-level closure state that also packs a Predates from its level to a
; stepper level S minted first. Applying it at S is fine, but a step cannot prove the fresh level below S.
; Needs std/list.sl, spec.sl and machine.sl first.
(def-lvl S)
(def-adts $ (HState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many HS : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Level) L)
     (erased (Predates (Level) L S) pr)
     (erased (Fn L (erased (Mem) mf) (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv) -> (HState c0 m0)))
(def-fns S $ (many use : (erased (Cmd) c0) (erased (Mem) m0) (many (HState c0 m0) st) -> (many (Outcome c0 m0) r))
  (let-match many st (HS _ _ k m L pr inv))
  (let-match many (step k m) (SHalt _) ((SNext _ _ k2 m2 s) (Stuck _ _)) ((SStuck _ _) (Stuck _ _)))
  (Halted _ _ m (inv (predates pr) m (RANil m))))
(def-fns S $ (many ext : (erased (Cmd) c0) (erased (Mem) m0) (many (HState c0 m0) st) -> (many (Nat) r))
  (let-match many st (HS _ _ k m L pr inv))
  (let-match many (step k m) (SNext _ _ k2 m2 s) ((SHalt _) 0) ((SStuck _ _) 1))
  (def-lvl L2)
  (let ((erased p2)) (prove-predates L2 S))
  2)
