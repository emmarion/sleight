; Refused: an invariant held as a closure at one fixed level L cannot be extended, since the new closure
; at L calls the old one at L. Needs std/list.sl, spec.sl and machine.sl first.
(def-lvl L)
(def-fns _ $ (many adv-ho : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m)
    (erased (Fn L (erased (Mem) mf) (erased (RunsAll m k mf) a) -> (erased (Runs m0 c0 mf) d)) inv) -> (many (Nat) r))
  (let-match many (step k m) (SNext _ _ k2 m2 s) ((SHalt _) 0) ((SStuck _ _) 1))
  (def-fns L $ (erased inv2 : (erased (Mem) mf) (erased (RunsAll m2 k2 mf) a) -> (erased (Runs m0 c0 mf) d))
    (inv mf (step-back k k2 m m2 mf s a)))
  2)
