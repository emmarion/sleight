(def-adts
  ((Choices : -> Type)
    enum
    (many ChOne : (many (Label) l) -> (Choices))
    (many ChSeq : (many (Choices) first) (many (Choices) rest) -> (Choices))))

(def-adts
  ((Run : ((List (Code)) fns) ((Heap) h) ((List (Word)) env) ((Code) c) ((Choices) ch) ((Heap) h2) ((Word) w) -> Type)
    enum
    (many RunDo : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Instr) i)
       (erased (Label) l) (erased (Heap) h2) (erased (Word) w)
       (erased (Prim h env i l h2 w) p) -> (Run fns h env (CDo i) (ChOne l) h2 w))
    (many RunLet : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) rhs) (erased (Code) body)
       (erased (Choices) ch1) (erased (Heap) h1) (erased (Word) w1) (erased (Choices) ch2) (erased (Heap) h2) (erased (Word) w2)
       (erased (Run fns h env rhs ch1 h1 w1) p) (erased (Run fns h1 (Cons (Word) w1 env) body ch2 h2 w2) q)
       -> (Run fns h env (CLet rhs body) (ChSeq ch1 ch2) h2 w2))
    (many RunMatch : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Word) w) (erased (Code) body) (erased (List (Word)) fs)
       (erased (List (Word)) env2) (erased (Choices) ch) (erased (Heap) h2) (erased (Word) w2)
       (erased (AtomVal env a w) pa) (erased (Select h w blocks imms body fs) sel) (erased (Cat fs env env2) ct)
       (erased (Run fns h env2 body ch h2 w2) q) -> (Run fns h env (CMatch a blocks imms) ch h2 w2))
    (many RunCall : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Nat) f) (erased (List (Atom)) args)
       (erased (Code) body) (erased (List (Word)) ws) (erased (Choices) ch) (erased (Heap) h2) (erased (Word) w)
       (erased (Nth (Code) fns f body) pf) (erased (AtomVals env args ws) pa) (erased (Run fns h ws body ch h2 w) q)
       -> (Run fns h env (CCall f args) ch h2 w))))
