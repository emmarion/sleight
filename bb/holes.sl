(def-adts $ (HCert : -> Type)
  enum
  (many HKeep : -> (HCert))
  (many HFar : (many (Bool) f) (many (List (Pair (Nat) (Nat))) dfa) -> (HCert))
  (many HWfar : (many (Bool) f) (many (Nat) maxd) (many (List (WR)) wl wr) -> (HCert))
  (many HSet : (many (Setting) se) -> (HCert))
  (many HCyc : (many (Bool) f) (many (Nat) t1 D P) -> (HCert))
  (many HPat : (many (Bool) f) (many (String) s) -> (HCert))
  (many HSk : -> (HCert)))

(def-adts
  ((HNode : ((Nat) n) ((Nat) k) ((List (List (PT))) hl) ((List (PT)) p) -> Type)
    enum
    (many HNT : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p) (erased (TNode n k hl p) tn) -> (HNode n k hl p))
    (many HNF : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p p2) (erased (Bool) f) (erased (Mir f p p2) mi)
       (erased (FarOK p2) fo) -> (HNode n k hl p))
    (many HNW : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p p2) (erased (Bool) f) (erased (Mir f p p2) mi)
       (erased (WOK p2) wo) -> (HNode n k hl p))
    (many HNP : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p p2) (erased (Bool) f) (erased (Mir f p p2) mi)
       (erased (PatOK p2) po) -> (HNode n k hl p))
    (many HNK : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p) (erased (SkOK p) sk) -> (HNode n k hl p))))

(def-adts
  ((HNs : ((Nat) n) ((Nat) k) ((List (List (PT))) hl) ((List (List (PT))) ps) -> Type)
    enum
    (many HNsNil : (erased (Nat) n k) (erased (List (List (PT))) hl) -> (HNs n k hl (Nil (List (PT)))))
    (many HNsCons : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p) (erased (List (List (PT))) ps)
       (erased (HNode n k hl p) hn) (erased (HNs n k hl ps) rest) -> (HNs n k hl (Cons (List (PT)) p ps)))))

(def-fns _ $ (erased hns-pick : (erased (Nat) n k) (erased (List (List (PT))) hl ps) (erased (List (PT)) p)
    (subterm erased (Mem (List (PT)) p ps) mh) (erased (HNs n k hl ps) hs) -> (erased (HNode n k hl p) hn))
  (match erased mh _
    ((MemHere _ _ _) (let-match erased hs (HNsCons _ _ _ _ _ hn _)) hn)
    ((MemThere _ _ _ rest mm) (let-match erased hs (HNsCons _ _ _ _ _ _ hs1)) (hns-pick n k hl rest p mm hs1))))

(def-fns _ $ (erased hns-good : (erased (Nat) n k s) (erased (List (List (PT))) hl ps) (erased (HNs n k hl ps) hs)
    (erased (Or (Lt s (Succ k)) (InHole n ps s)) o) -> (erased (Or (Lt s (Succ k)) (InHole n hl s)) r))
  (let-match erased o (InR _ _ ih) ((InL _ _ lt) (InL _ _ lt)))
  (let-match erased ih (MkIH _ _ _ p m mh ex wf hs1))
  (match erased (hns-pick n k hl ps p mh hs) _
    ((HNT _ _ _ _ tn) (tn-good n k hl p m s tn ex wf hs1))
    (absurd (HNF _ _ _ _ p2 f mi fo)
      (let ((erased m2) (erased ex2) (erased hs2)) (mir-halts f p p2 m mi ex s hs1))
      (never-far p2 m2 fo ex2 s hs2))
    (absurd (HNW _ _ _ _ p2 f mi wo)
      (let ((erased m2) (erased ex2) (erased hs2)) (mir-halts f p p2 m mi ex s hs1))
      (never-wfar p2 m2 wo ex2 s hs2))
    (absurd (HNP _ _ _ _ p2 f mi po)
      (let ((erased m2) (erased ex2) (erased hs2)) (mir-halts f p p2 m mi ex s hs1))
      (never-pat p2 m2 po ex2 s hs2))
    (absurd (HNK _ _ _ _ sk) (never-sk p m sk ex s hs1))))

(def-fns _ $ (many mir-of : (many (Bool) f) (many (List (PT)) p) -> (many (List (PT)) p2) (erased (Mir f p p2) mi))
  (let-match many f (BTrue) ((BFalse) (values p (MirN p))))
  (let ((many p3) (erased xp)) (flip-p p))
  (values p3 (MirY p p3 xp)))

(def-fns _ $ (many hn-of : (erased (Nat) n k) (erased (List (List (PT))) hl) (erased (List (PT)) p) (many (Res (TNode n k hl p)) r) -> (many (Res (HNode n k hl p)) r2))
  (match many r _ ((ROk _ tn) (ROk _ (HNT n k hl p tn))) ((RFail _) (RFail _))))

(def-fns _ $ (many close-one : (many (Nat) n k) (many (List (List (PT))) hl) (many (List (PT)) p) (many (HCert) hc) -> (many (Res (HNode n k hl p)) r))
  (match many hc _
    ((HKeep) (match many (find-hole p hl) _ ((Some _ mh) (ROk _ (HNT n k hl p (THole n k hl p mh)))) ((None _) (RFail _))))
    ((HSet se) (let ((many sr) (unique _)) (search p se 24 (ws-new))) (match many sr _ ((Some _ ct) (hn-of n k hl p (check-cert n k hl p ct))) ((None _) (RFail _))))
    ((HCyc f t1 D P) (hn-of n k hl p (check-cyc n k hl p f t1 D P)))
    ((HFar f dfa)
      (let ((many p2) (erased mi)) (mir-of f p))
      (match many (check-far p2 (far-gen p2 n dfa)) _ ((ROk _ fo) (ROk _ (HNF n k hl p p2 f mi fo))) ((RFail _) (RFail _))))
    ((HWfar f md wl wr)
      (let ((many p2) (erased mi)) (mir-of f p))
      (match many (check-wfar p2 (wfar-gen p2 md wl wr)) _ ((ROk _ wo) (ROk _ (HNW n k hl p p2 f mi wo))) ((RFail _) (RFail _))))
    ((HPat f s)
      (let ((many p2) (erased mi)) (mir-of f p))
      (match many (check-pat p2 (pat-cert s)) _ ((ROk _ po) (ROk _ (HNP n k hl p p2 f mi po))) ((RFail _) (RFail _))))
    ((HSk) (match many (check-sk p) _ ((ROk _ sk) (ROk _ (HNK n k hl p sk))) ((RFail _) (RFail _))))))

(def-fns _ $ (many hc : (many (String) s) (many (HCert) c) -> (many (Pair (List (PT)) (HCert)) r))
  (let ((many p) (many _)) (pts-of 10 s))
  (MkPair _ _ p c))

(def-fns _ $ (many hc-find : (many (List (PT)) p) (subterm many (List (Pair (List (PT)) (HCert))) cs) -> (many (HCert) c))
  (let-match many cs (Cons _ e rest) ((Nil _) (HKeep)))
  (let-match many e (MkPair _ _ q c))
  (match many (eq-pts p q) _ ((Some _ _) c) ((None _) (tail $ hc-find p rest))))

(def-fns _ $ (many keep-holes : (subterm many (List (List (PT))) ps) (many (List (Pair (List (PT)) (HCert))) cs) -> (many (List (List (PT))) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (Nil _)))
  (let ((many ks)) (notail $ keep-holes rest cs))
  (match many (hc-find p cs) _ ((HKeep) (Cons _ p ks)) (else ks)))

(def-fns _ $ (many close-holes : (many (Nat) n k) (many (List (List (PT))) hl) (subterm many (List (List (PT))) ps) (many (List (Pair (List (PT)) (HCert))) cs)
    -> (many (Res (HNs n k hl ps)) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (ROk _ (HNsNil n k hl))))
  (let-match many (close-one n k hl p (hc-find p cs)) (ROk _ hn) ((RFail _) (RFail _)))
  (let-match many (notail $ close-holes n k hl rest cs) (ROk _ hs) ((RFail _) (RFail _)))
  (ROk _ (HNsCons n k hl p rest hn hs)))
