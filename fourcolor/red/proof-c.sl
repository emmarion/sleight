; all-red-proof: every configuration of configs.sl is C-reducible with its contract (cfreducible.v), by the certified check
; of ccheck.sl, one native.sl job per chunk string of config-srcs, run by native-run. Load after chunks.sl and native.sl.

(def-adts $ (RedC : ((List (Config)) cs) -> Type)
  enum
  (many MkRedC : (erased (List (Config)) cs) (erased (AllRed CRX cs) p) -> (RedC cs)))

(def-fns _ $ (many red-of : (many (String) s) -> (many (Chk (Decoded RedC s)) r))
  (let-match many (dec-chunk s) (POk _ _ _ _ cs _ d) (else (CkN _)))
  (let-match many (red-all-c cs (Nil _)) (CkY _ p) ((CkN _) (CkN _)))
  (CkY _ (MkDecoded RedC s _ cs d (MkRedC cs p))))

(def-fns _ $ (erased red-chunks : (erased (List (List (Config))) ks) (subterm erased (OnChunks RedC ks) o) -> (erased (AllRedC CRX ks) r))
  (let-match erased o (OnCons _ cs ks1 a o1) ((OnNil _) (ARCNil CRX)))
  (let-match erased a (MkRedC _ p))
  (ARCCons CRX cs ks1 p (red-chunks ks1 o1)))

(native-each red-srcs config-srcs (s t r) (Chk (Decoded RedC s)) (red-of s) (CkY _ a) (SrcCons RedC s t a r) (SrcNil RedC))
(native-then (let ((erased all-red-proof)) (red-chunks css (on-chunks RedC config-srcs _ css css-dec red-srcs))))
