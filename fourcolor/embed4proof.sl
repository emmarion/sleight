; cfcerts-proof: notembed.sl's CfCerts for the cfs of fcopen.sl, from embed4.sl's AllGc, decided by one native.sl job per
; chunk of css, after native-run. Load after embed4.sl, fcopen.sl and native.sl.

(def-adts $ (AllGcC : ((List (List (Config))) css) -> Type)
  enum
  (many AgcNil : -> (AllGcC (Nil (List (Config)))))
  (many AgcCons : (erased (List (Config)) cs) (erased (List (List (Config))) css) (erased (AllGc cs) a) (erased (AllGcC css) rest)
      -> (AllGcC (Cons (List (Config)) cs css))))

(def-fns _ $ (erased allgc-concat : (erased (List (List (Config))) css) (erased (List (Config)) cfs) (subterm erased (ConcatL css cfs) p)
    (erased (AllGcC css) a) -> (erased (AllGc cfs) r))
  (match erased p _
    ((CLNil) (AgNil))
    ((CLSkip css1 _ p1) (let-match erased a (AgcCons _ _ _ a1)) (allgc-concat css1 cfs p1 a1))
    ((CLCons cf cs cfs1 css1 p1)
      (let-match erased a (AgcCons _ _ ag a1))
      (let-match erased ag (AgCons _ _ c ag1))
      (AgCons cfs1 cf c (allgc-concat (Cons _ cs css1) cfs1 p1 (AgcCons cs css1 ag1 a1))))))

(native-each allgc-css css (cs t r) (Checked (AllGc cs)) (allgc-c cs) (ChkYes _ a) (AgcCons cs t a r) (AgcNil))
(native-then (let ((erased cfcerts-proof)) (cfcerts-of cfs (allgc-concat css cfs cl allgc-css))))
