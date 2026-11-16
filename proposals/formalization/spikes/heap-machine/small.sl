(def-adts
  ((Stack : -> Type)
    enum
    (many KNil : -> (Stack))
    (many KLet : (many (List (Word)) env) (many (Code) body) (many (Stack) rest) -> (Stack)))
  ((Control : -> Type)
    enum
    (many KRun : (many (List (Word)) env) (many (Code) c) (many (Stack) k) -> (Control))
    (many KRet : (many (Word) w) (many (Stack) k) -> (Control))))

(def-adts
  ((Step : ((List (Code)) fns) ((Heap) h) ((Control) c) ((Label) l) ((Heap) h2) ((Control) c2) -> Type)
    enum
    (many StDo : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i) (erased (Stack) k)
       (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
       (erased (Prim h env i l h2 w) p) -> (Step fns h (KRun env (CDo i) k) l h2 (KRet w k)))
    (many StLet : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) rhs) (erased (Code) body) (erased (Stack) k)
       -> (Step fns h (KRun env (CLet rhs body) k) (LTau) h (KRun env rhs (KLet env body k))))
    (many StRet : (erased (List (Code)) fns) (erased (Heap) h) (erased (Word) w) (erased (List (Word)) env) (erased (Code) body) (erased (Stack) k)
       -> (Step fns h (KRet w (KLet env body k)) (LTau) h (KRun (Cons (Word) w env) body k)))
    (many StMatch : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Stack) k)
       (erased (Word) w) (erased (Code) body) (erased (List (Word)) fs) (erased (List (Word)) env2)
       (erased (AtomVal env a w) pa) (erased (Select h w blocks imms body fs) sel) (erased (Cat fs env env2) ct)
       -> (Step fns h (KRun env (CMatch a blocks imms) k) (LTau) h (KRun env2 body k)))
    (many StCall : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) f) (erased (List (Atom)) args) (erased (Stack) k)
       (erased (Code) body) (erased (List (Word)) ws)
       (erased (Nth (Code) fns f body) pf) (erased (AtomVals env args ws) pa)
       -> (Step fns h (KRun env (CCall f args) k) (LTau) h (KRun ws body k))))
  ((Steps : ((List (Code)) fns) ((Heap) h) ((Control) c) ((List (Label)) ls) ((Heap) h2) ((Control) c2) -> Type)
    enum
    (many StepsNil : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) -> (Steps fns h c (Nil (Label)) h c))
    (many StepsCons : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Label) l) (erased (Heap) h1) (erased (Control) c1)
       (erased (List (Label)) ls) (erased (Heap) h2) (erased (Control) c2)
       (erased (Step fns h c l h1 c1) p) (erased (Steps fns h1 c1 ls h2 c2) q) -> (Steps fns h c (Cons (Label) l ls) h2 c2))))
