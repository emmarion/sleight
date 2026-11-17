; Accepted (third review): advance and run-total that always answer stuck have the theorems' types.
; Needs std/list.sl, spec.sl, machine.sl and complete.sl first.
(def-fns _ $ (many advance-stuck : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m)
    (erased (Trace (Cons (Cmd) c0 (Nil (Cmd))) m0 k m) t) -> (many (Advance c0 m0 k m) r))
  (Ended _ _ _ _ (Stuck _ _)))
(def-fns _ $ (many run-total-stuck : (many (Cmd) c0) (many (Mem) m0) (erased (Mem) mf) (erased (Runs m0 c0 mf) spec)
    -> (many (Agrees c0 m0 mf) a))
  (AgreeStuck _ _ _))
