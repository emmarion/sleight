(def-adts
  ((Ran : ((List (Code)) fns) ((Heap) h) ((List (Word)) env) ((Code) c) -> Type)
    enum
    (many RanOk : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c)
       (many (Heap) h2) (many (Nat) next2) (erased (Below h2 next2) inv2) (many (Word) w)
       (erased (Choices) ch) (erased (Run fns h env c ch h2 w) d) -> (Ran fns h env c))
    (many RanHalt : (erased (List (Code)) fns) (erased (Heap) h) (erased (List (Word)) env) (erased (Code) c) (many (Halt) why) -> (Ran fns h env c))))

(def-fns _ $ (many run : (subterm many (Nat) fuel) (many (List (Code)) fns) (many (Heap) h) (many (Nat) next) (erased (Below h next) inv)
    (many (List (Word)) env) (many (Code) c) -> (many (Ran fns h env c) r))
  (let-match many fuel (Succ f) ((Zero) (RanHalt _ _ _ _ (OutOfFuel))))
  (match many c _
    ((CDo i)
      (match many (prim h next inv env i) _
        ((PrimStuck _ _ _ why) (RanHalt _ _ _ _ (Stuck why)))
        ((PrimOk _ _ _ h2 next2 inv2 w l d) (RanOk _ _ _ _ h2 next2 inv2 w (ChOne l) $ RunDo fns h env i l h2 w d))))
    ((CLet rhs body)
      (let-match many (notail $ run f fns h next inv env rhs) (RanOk _ _ _ _ h1 next1 inv1 w1 ch1 d1) ((RanHalt _ _ _ _ why) (RanHalt _ _ _ _ why)))
      (match many (notail $ run f fns h1 next1 inv1 (Cons _ w1 env) body) _
        ((RanHalt _ _ _ _ why) (RanHalt _ _ _ _ why))
        ((RanOk _ _ _ _ h2 next2 inv2 w2 ch2 d2)
          (RanOk _ _ _ _ h2 next2 inv2 w2 (ChSeq ch1 ch2) $ RunLet fns h env rhs body ch1 h1 w1 ch2 h2 w2 d1 d2))))
    ((CMatch a blocks imms)
      (let-match many (atom-val env a) (AVHit _ _ w pa) ((AVMiss _ _) (RanHalt _ _ _ _ (Stuck (NoVar)))))
      (let-match many (select h w blocks imms) (SelHit _ _ _ _ body fs sel) ((SelMiss _ _ _ _ why) (RanHalt _ _ _ _ (Stuck why))))
      (let ((many env2) (erased ct)) (cat fs env))
      (match many (notail $ run f fns h next inv env2 body) _
        ((RanHalt _ _ _ _ why) (RanHalt _ _ _ _ why))
        ((RanOk _ _ _ _ h2 next2 inv2 w2 ch d)
          (RanOk _ _ _ _ h2 next2 inv2 w2 ch $ RunMatch fns h env a blocks imms w body fs env2 ch h2 w2 pa sel ct d))))
    ((CCall g args)
      (let-match many (nth-dec _ fns g) (NthHit _ _ _ body pf) ((NthMiss _ _ _ _) (RanHalt _ _ _ _ (Stuck (NoFn)))))
      (let-match many (atom-vals env args) (AVsHit _ _ ws pa) ((AVsMiss _ _) (RanHalt _ _ _ _ (Stuck (NoVar)))))
      (match many (notail $ run f fns h next inv ws body) _
        ((RanHalt _ _ _ _ why) (RanHalt _ _ _ _ why))
        ((RanOk _ _ _ _ h2 next2 inv2 w ch d)
          (RanOk _ _ _ _ h2 next2 inv2 w ch $ RunCall fns h env g args body ws ch h2 w pf pa d))))))
