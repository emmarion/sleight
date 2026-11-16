(def-adts $ (Counted : ((List (Tok)) src) -> Type)
  enum
  (many Finished : (erased (List (Tok)) src) (many (Verdict (Zero) src) v) -> (Counted src))
  (many Paused : (erased (List (Tok)) src) (many (Scan src) s) -> (Counted src)))

(def-fns _ $ (many run-counted : (subterm many (Nat) count) (erased (List (Tok)) src) (many (Scan src) s) -> (many (Counted src) r))
  (let-match many count (Succ fewer) ((Zero) (Paused src s)))
  (let ((many r) (erased _)) (step src s))
  (match many r _
    ((Done _ _ v) (Finished src v))
    ((More _ _ next) (tail $ run-counted fewer src next))))

(def-adts $ (Halts : ((List (Tok)) src) ((Scan src) s) -> Type)
  enum
  (many HaltDone : (erased (List (Tok)) src) (erased (Scan src) s) (erased (Verdict (Zero) src) v)
     (erased (StepsTo src s (Done Scan src v)) g) -> (Halts src s))
  (many HaltMore : (erased (List (Tok)) src) (erased (Scan src) s) (erased (Scan src) next)
     (erased (StepsTo src s (More Scan src next)) g) (erased (Halts src next) h) -> (Halts src s)))

(def-fns _ $ (erased steps-clash : (erased (List (Tok)) src) (erased (Scan src) s) (erased (Verdict (Zero) src) v) (erased (Scan src) next)
    (erased (StepsTo src s (Done Scan src v)) p) (erased (StepsTo src s (More Scan src next)) q) -> (erased (False) f))
  (match erased p _
    ((StAccept _ _ _) (match erased q _))
    ((StUnclosed _ _ _ _) (match erased q _))
    ((StExtraClose _ _ _ _) (match erased q _))))

(def-fns _ $ (erased steps-more-functional : (erased (List (Tok)) src) (erased (Scan src) s) (erased (Scan src) a) (erased (Scan src) b)
    (erased (StepsTo src s (More Scan src a)) p) (erased (StepsTo src s (More Scan src b)) q) -> (erased (Eq (Scan src) a b) e))
  (match erased p _
    ((StOpen _ _ _ _) (match erased q _ ((StOpen _ _ _ _) (Refl (Scan src) a))))
    ((StClose _ _ _ _) (match erased q _ ((StClose _ _ _ _) (Refl (Scan src) a))))))

(def-fns _ $ (many run-by : (erased (List (Tok)) src) (many (Scan src) s) (subterm erased (Halts src s) h) -> (many (Verdict (Zero) src) v))
  (let ((many r) (erased g)) (step src s))
  (let-match many r (More _ _ next) ((Done _ _ v) v))
  (let-match erased h (HaltMore _ _ expected g2 h2)
    (absurd (HaltDone _ _ v0 g0) (steps-clash src s v0 next g0 g)))
  (let-match erased (steps-more-functional src s expected next g2 g) (Refl _ _))
  (tail $ run-by src next h2))
