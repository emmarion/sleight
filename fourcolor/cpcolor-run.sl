; Computes cpcolor-c for each of the 633 configurations under native-compute and checks its tree is red.sl's cpcolor tree.
; Load after cpcolor.sl and red/configs.sl.

(def-fns _ $ (many ct-eqb : (subterm many (Ctree) a) (many (Ctree) b) -> (many (Bool) r))
  (match many a _
    ((CEmpty) (match many b _ ((CEmpty) (BTrue)) (else (BFalse))))
    ((CLeaf la) (match many b _ ((CLeaf lb) (tail $ ct-eqb la lb)) (else (BFalse))))
    ((CNode a1 a2 a3) (match many b _ ((CNode b1 b2 b3) (andb (notail $ ct-eqb a1 b1) (andb (notail $ ct-eqb a2 b2) (notail $ ct-eqb a3 b3))))
      (else (BFalse))))))

(def-fns _ $ (many cpcolor-ok : (many (Config) cf) -> (many (Bool) b))
  (let-match many cf (MkConfig _ _ cp))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (BFalse)))
  (let ((many d) (many e) (many f) (many r) (erased cm)) (cpmap-c cp na))
  (let ((erased k) (erased lk) (erased cs)) (cpmap-size cp d e f r cm))
  (let ((many m) (erased lm)) (size-c _ r))
  (let-match erased (length-fn _ r k m lk lm) (Refl _ _))
  (let-match many m (Succ m1) ((Zero) (BFalse)))
  (let-match many m1 (Succ h) ((Zero) (BFalse)))
  (let ((many t) (erased ht) (erased rt)) (cpcolor-c h cp cs na))
  (ct-eqb t (cpcolor cp)))

(def-fns _ $ (many all-ok : (subterm many (List (Config)) cfs) -> (many (Bool) b))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (BTrue)))
  (match many (cpcolor-ok cf) _ ((BTrue) (tail $ all-ok rest)) ((BFalse) (BFalse))))

(def-fns _ $ (many chunks-ok : (subterm many (List (List (Config))) css) -> (many (Bool) b))
  (let-match many css (Cons _ cs rest) ((Nil _) (BTrue)))
  (match many (all-ok cs) _ ((BTrue) (tail $ chunks-ok rest)) ((BFalse) (BFalse))))

(def-fns _ $ (many j : -> (many (Bool) r)) (chunks-ok (config-chunks)))
(let ((many r)) (native-compute j))
(comptime-match many r (BTrue))
