(def-fns _ $ (many env-get : (subterm many (Env) env) (many (Nat) x) (erased (Val) v) (erased (EnvOf env x v) p) -> (many v is found))
  (let-match many env (ECons y w rest) (absurd (ENil) p))
  (match many (nat-dec x y) _
    ((NDSame _)
      (let-match erased p (EnvHere _ _ _))
      w)
    ((NDDiff _ _ n)
      (let-match erased p (EnvThere _ _ _ _ _ _ q) (absurd (EnvHere _ _ _) (neq-irrefl x n)))
      (tail $ env-get rest x v q))))

(def-fns _ $ (many bind-all-get : (many (Env) env) (subterm many (List (Nat)) ids) (many (List (Val)) vs) (erased (Env) out) (erased (BindAll env ids vs out) p) -> (many out is bound))
  (let-match many ids (Cons _ x rest) ((Nil _) (let-match erased p (BANil _)) env))
  (let-match many vs (Cons _ v vrest) (absurd (Nil _) p))
  (let-match erased p (BACons _ _ _ _ _ _ q))
  (tail $ bind-all-get (ECons x v env) rest vrest out q))

(def-fns _ $ (many bind-group-get : (many (Env) cenv) (many (List (FnDef)) group) (subterm many (List (FnDef)) defs) (many (Env) env) (erased (Env) out)
    (erased (BindGroup cenv group defs env out) p) -> (many out is bound))
  (let-match many defs (Cons _ def rest) ((Nil _) (let-match erased p (BGNil _ _ _)) env))
  (let-match many def (MkFnDef id ps body))
  (let-match erased p (BGCons _ _ _ _ _ _ _ _ q))
  (tail $ bind-group-get cenv group rest (ECons id (VClo cenv group (MkFnDef id ps body)) env) out q))

(def-fns _ $ (many bind-atoms-get : (many (Env) env) (subterm many (List (Nat)) ids) (erased (Env) out) (erased (BindAtoms env ids out) p) -> (many out is bound))
  (let-match many ids (Cons _ x rest) ((Nil _) (let-match erased p (BTNil _)) env))
  (let-match erased p (BTCons _ _ _ _ q))
  (tail $ bind-atoms-get (ECons x (VAtom x) env) rest out q))

(def-fns _ $ (many branch-get : (subterm many (List (Branch)) bs) (many (Nat) ctor) (erased (List (Nat)) fields) (erased (Core) body) (erased (BranchOf bs ctor fields body) p) ->
    (many fields is found-fields) (many body is found-body))
  (let-match many bs (Cons _ b rest) (absurd (Nil _) p))
  (let-match many b (MkBranch d fields2 body2))
  (match many (nat-dec ctor d) _
    ((NDSame _)
      (let-match erased p (BrHere _ _ _ _) (absurd (BrThere _ _ _ _ _ _ _ n _) (neq-irrefl ctor n)))
      (values fields2 body2))
    ((NDDiff _ _ n)
      (let-match erased p (BrThere _ _ _ _ _ _ _ _ q) (absurd (BrHere _ _ _ _) (neq-irrefl ctor n)))
      (tail $ branch-get rest ctor fields body q))))
