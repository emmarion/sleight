; Under the default `--goal none` a `qed` is checked, and the driver prints the final value.
(goal erased (Eq (Nat) 2 2))
(def-fns _ $ (erased pf : -> (erased (Eq (Nat) 2 2) e)) (Refl (Nat) 2))
(qed (pf))
5
; expect: 5
