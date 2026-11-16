(def-fns _
  ((many stack-depth : (erased (Env) env) (erased (Core) c) (erased (Env) env0) (erased (Core) c0) (subterm many (Stack env c env0 c0) k) (many (Nat) above) -> (many (Nat) depth))
    (match many k _
      ((KDone _ _) above)
      ((KAppHead _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KCallFn _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KCallBody _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KMatchScrut _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KMatchBody _ _ _ _ _ _ _ _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KListHead _ _ _ _ _ k2) (tail $ list-stack-depth _ _ _ _ k2 (Succ above)))
      ((KLetRhs _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KStmtRest _ _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))))
  ((many list-stack-depth : (erased (Env) env) (erased (List (Core)) cs) (erased (Env) env0) (erased (Core) c0) (subterm many (ListStack env cs env0 c0) k) (many (Nat) above) -> (many (Nat) depth))
    (match many k _
      ((KAppArgs _ _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KCallArgs _ _ _ _ _ _ _ _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KValues _ _ _ _ k2) (tail $ stack-depth _ _ _ _ k2 (Succ above)))
      ((KListTail _ _ _ _ _ _ _ k2) (tail $ list-stack-depth _ _ _ _ k2 (Succ above))))))

(def-fns _ $ (many state-depth : (erased (Env) env0) (erased (Core) c0) (many (State env0 c0) s) -> (many (Nat) depth))
  (match many s _
    ((SEval _ _ _ _ k) (stack-depth _ _ _ _ k 0))
    ((SEvalList _ _ _ _ k) (list-stack-depth _ _ _ _ k 0))
    ((SRet _ _ _ _ _ _ k) (stack-depth _ _ _ _ k 0))
    ((SRetList _ _ _ _ _ _ k) (list-stack-depth _ _ _ _ k 0))))
