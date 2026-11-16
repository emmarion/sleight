(def-fns _ $ (many rerun : (many (Nat) fuel) (many (Env) env) (many (Core) c) -> (many (Maybe (List (Val))) r))
  (match many (eval fuel env c) _
    ((EvalStuck _ _) (None _))
    ((MkEvaled _ _ vs p) (Some _ (eval-by env c vs p)))))

(rerun 1000 (ENil) program)
