(def-adts $ (EngE : -> Type)
  enum
  (many MkEngE : (many (Nat) h) (many (Maybe (Eng h)) e) -> (EngE)))

(def-fns _ $ (many r4-eng-lookup : (many (Nat) h) (subterm many (List (EngE)) cache) -> (many (Maybe (Maybe (Eng h))) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkEngE h2 e))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ e)) ((Unequal _ _ _ _ _) (tail $ r4-eng-lookup h rest))))

; red4's cached fcache h make_eng.
(def-fns _ $ (many r4-eng-for : (many (Nat) h) (many (List (EngE)) cache) (erased (List (MaybeUninit (WRow))) rp rb) (erased (List (Copy (Nat))) ns)
    (unique (Array (MaybeUninit (WRow)) rp) lp) (unique (Array (MaybeUninit (WRow)) rb) lb) (unique (Array (Copy (Nat)) ns) ln) (erased (WSt rp rb ns) st) ->
    (erased (List (MaybeUninit (WRow))) rp2 rb2) (erased (List (Copy (Nat))) ns2) (unique (Array (MaybeUninit (WRow)) rp2) lp2 at lp)
    (unique (Array (MaybeUninit (WRow)) rb2) lb2 at lb) (unique (Array (Copy (Nat)) ns2) ln2 at ln) (erased (WSt rp2 rb2 ns2) st2) (many (Maybe (Eng h)) e)
    (many (List (EngE)) cache2))
  (let-match many (r4-eng-lookup h cache) (None _) ((Some _ e) (values rp rb ns lp lb ln st e cache)))
  (let ((erased rp2) (erased rb2) (erased ns2) (unique lp2) (unique lb2) (unique ln2) (erased st2) (many e)) (r4-make-eng h rp rb ns lp lb ln st))
  (let ((many ret)) (Cons _ (MkEngE h e) cache))
  (values rp2 rb2 ns2 lp2 lb2 ln2 st2 e ret))

; red4's fcache with its module-level hits, gone and celems buffers and pair rows.
(def-adts $ (R4St : -> Type)
  enum
  (many MkR4St : (many (List (EngE)) cache) (erased (List (Nat)) Hs G T) (unique (Buf Hs) hb) (unique (Buf G) gb) (unique (Buf T) cel)
      (erased (List (MaybeUninit (WRow))) rp rb) (erased (List (Copy (Nat))) ns) (unique (Array (MaybeUninit (WRow)) rp) lp) (unique (Array (MaybeUninit (WRow)) rb) lb)
      (unique (Array (Copy (Nat)) ns) ln) (erased (WSt rp rb ns) st) -> (R4St)))

(def-fns _ $ (many r4k-st-new : -> (unique (R4St) s))
  (let ((erased rp) (unique lp) (erased rb) (unique lb) (erased ns) (unique ln) (erased st)) (r4-pairs))
  (MkR4St (Nil _) (Nil _) (Nil _) (Nil _) (r4-newbuf) (r4-newbuf) (r4-newbuf) rp rb ns lp lb ln st))

; The Kempe tree kt of cp, whose ring has h + 2 darts, is sound for the ring traces of cp's map.
(def-adts $ (KChk : ((List (Step)) cp) -> Type)
  enum
  (many KCYes : (erased (List (Step)) cp) (many (Nat) h) (erased (Ctree) kt) (many (R4Out h kt) ro) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
      (erased (Cprsize cp (Succ (Succ h))) cs) (erased (NoA cp) na) -> (KChk cp))
  (many KCNo : (erased (List (Step)) cp) -> (KChk cp)))

(def-fns _ $ (many kempe-tree-chk : (many (List (Step)) cp) (unique (R4St) s) -> (many (KChk cp) k) (unique (R4St) s2 at s))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (values (KCNo cp) s)))
  (let ((erased d) (erased e) (erased f) (many r) (erased cm)) (cpmap-c cp na))
  (let ((erased k) (erased lk) (erased cs)) (cpmap-size cp d e f r cm))
  (let ((many m) (erased lm)) (size-c _ r))
  (let-match erased (length-fn _ r k m lk lm) (Refl _ _))
  (let-match many m (Succ m1) ((Zero) (values (KCNo cp) s)))
  (let-match many m1 (Succ h) ((Zero) (values (KCNo cp) s)))
  (let-match unique s (MkR4St cache Hs G T hb gb cel rp rb ns lp lb ln st u))
  (let ((erased rp2) (erased rb2) (erased ns2) (unique lp2) (unique lb2) (unique ln2) (erased st2) (many me) (many cache2)) (r4-eng-for h cache rp rb ns lp lb ln st))
  (let-match many me (Some _ eg)
    ((None _) (values (KCNo cp) (u cache2 Hs G T (at) hb (at) gb (at) cel rp2 rb2 ns2 (at) lp2 (at) lb2 (at) ln2 st2))))
  (let ((many ctr) (erased hr) (erased cn) (erased rt) (erased _)) (cpcolor-c h cp cs na))
  (let ((erased Hs3) (unique hb3) (erased G3) (unique gb3) (erased T3) (unique cel3) (erased rp3) (erased rb3) (erased ns3) (unique lp3) (unique lb3) (unique ln3) (erased st3) (erased kt) (many ro) (erased ks))
    (r4k-kempe (MkPred (List (Step)) cp CpColR) h eg ctr cn (ctring-allp cp ctr (Nil _) rt) Hs hb G gb T cel rp2 rb2 ns2 lp2 lb2 ln2 st2))
  (values (KCYes cp h kt ro ks cs na) (u cache2 Hs3 G3 T3 (at) hb3 (at) gb3 (at) cel3 rp3 rb3 ns3 (at) lp3 (at) lb3 (at) ln3 st3)))
