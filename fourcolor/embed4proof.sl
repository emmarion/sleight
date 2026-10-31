(def-fns _ $ (erased allgc-concat : (erased (List (List (Config))) css) (erased (List (Config)) cfs) (subterm erased (ConcatL css cfs) p)
    (erased (OnChunks AllGc css) a) -> (erased (AllGc cfs) r))
  (match erased p _
    ((ConcatNil) (AgNil))
    ((ConcatSkip css1 _ p1) (let-match erased a (OnCons _ _ _ _ a1)) (allgc-concat css1 cfs p1 a1))
    ((ConcatCons cf cs cfs1 css1 p1)
      (let-match erased a (OnCons _ _ _ ag a1))
      (let-match erased ag (AgCons _ _ c ag1))
      (AgCons cfs1 cf c (allgc-concat (Cons _ cs css1) cfs1 p1 (OnCons AllGc cs css1 ag1 a1))))))

(def-fns _ $ (many gc-of : (many (List (String)) ss) -> (many (Checked (Decoded AllGc ss)) r))
  (let-match many (dec-list ss) (POk _ _ _ _ cs _ d) (else (ChkNo _)))
  (let-match many (allgc-c cs) (ChkYes _ a) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (MkDecoded AllGc ss _ cs d a)))

(native-each allgc-srcs chunk-srcs (ss t r) (Checked (Decoded AllGc ss)) (gc-of ss) (ChkYes _ a) (SrcCons AllGc ss t a r) (SrcNil AllGc))
(native-then (let ((erased cfcerts-proof)) (cfcerts-of cfs (allgc-concat css cfs cl (on-chunks AllGc chunk-srcs _ css css-dec allgc-srcs)))))
