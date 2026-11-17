; Refused: the stepper's own level is minted before any packed level, so it cannot apply the invariant
; at a halt. Needs std/list.sl, spec.sl and machine.sl first.
(def-adts $ (HState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many HS : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Level) L)
     (erased (Fn L (erased (Mem) mf) (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv) -> (HState c0 m0)))

(def-fns _ $ (many adv-ho : (erased (Cmd) c0) (erased (Mem) m0) (many (HState c0 m0) st) -> (many (Outcome c0 m0) r))
  (let-match many st (HS _ _ k m L inv))
  (let-match many (step k m) (SHalt _) ((SNext _ _ k2 m2 s) (Stuck _ _)) ((SStuck _ _) (Stuck _ _)))
  (Halted _ _ m (inv m (RANil m))))
