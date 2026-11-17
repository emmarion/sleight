; Accepted: with the invariant's level packed in the state, each step can mint a fresh level and a closure
; at it that extends the old one. Needs std/list.sl, spec.sl and machine.sl first.
(def-adts $ (HState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many HS : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Level) L)
     (erased (Fn L (erased (Mem) mf) (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv) -> (HState c0 m0)))

(def-fns _ $ (many adv-ho : (erased (Cmd) c0) (erased (Mem) m0) (many (HState c0 m0) st) -> (many (Nat) r))
  (let-match many st (HS _ _ k m L inv))
  (let-match many (step k m) (SNext _ _ k2 m2 s) ((SHalt _) 0) ((SStuck _ _) 1))
  (def-lvl L2)
  (def-fns L2 $ (erased inv2 : (erased (Mem) mf) (erased (RunsAll m2 k2 mf) a) -> (erased (Runs m0 c0 mf) d))
    (inv mf (step-back k k2 m m2 mf s a)))
  (let ((many st2)) (HS c0 m0 k2 m2 L2 inv2))
  2)
