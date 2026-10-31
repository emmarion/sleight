; Unavoidability in the shape of unavoidability.v, with the embedding of quiz.v: in every plain cubic connected pentagonal
; map of genus 0, a configuration of red/configs.sl has a preembedding of its kernel into the map or its mirror (CfEmbed).
; The computed part is split into independent jobs for native.sl: the certified walk of each hub arity 5 to 11 is cut into
; regions (regs), each walked from its context with the certified redpart of redc.sl on its obligations, and one job does
; the cap checks; each job builds the quiz tree with its evidence (qtree.sl) for itself. Once (native-run) has run them,
; unav-from puts their evidence together into unav-proof. The cfs in scope are those of qztcfs.sl or fcopen.sl. Load after unave.sl and data.sl.

(def-adts $ (AllRed : ((Qzt) qt) ((List (List (Sub))) obl) -> Type)
  enum
  (many ARNil : (erased (Qzt) qt) -> (AllRed qt (Nil (List (Sub)))))
  (many ARCons : (erased (Qzt) qt) (erased (List (Sub)) q) (erased (List (List (Sub))) rest) (erased (RedD qt q) dd) (erased (AllRed qt rest) r)
      -> (AllRed qt (Cons (List (Sub)) q rest))))

(def-fns _ $ (many allred-c : (many (Qzt) qt) (subterm many (List (List (Sub))) obl) -> (many (Bool) ok) (erased (IfT ok (AllRed qt obl)) w))
  (let-match many obl (Cons _ q rest) ((Nil _) (values (BTrue) (IfY _ (ARNil qt)))))
  (let ((many ok1) (erased w1)) (redp-c qt q))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let-match erased w1 (IfY _ dd))
  (let ((many ok2) (erased w2)) (tail $ allred-c qt rest))
  (values ok2 (match erased w2 _ ((IfY _ a) (IfY _ (ARCons qt q rest dd a))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased allred-mem : (erased (Qzt) qt) (erased (List (List (Sub))) obl) (erased (List (Sub)) q) (subterm erased (AllRed qt obl) a)
    (erased (Mem (List (Sub)) q obl) m) -> (erased (RedD qt q) r))
  (let-match erased a (ARCons _ q1 rest dd a1) (absurd (ARNil _) m))
  (match erased m _
    ((MemHere _ _ _) dd)
    ((MemThere _ _ _ _ m1) (allred-mem qt rest q a1 m1))))

; The obligations obl all pass redpart against some quiz tree built from cfs.
(def-adts $ (RedE : ((List (Config)) cfs) ((List (List (Sub))) obl) -> Type)
  enum
  (many MkRedE : (erased (List (Config)) cfs) (erased (List (List (Sub))) obl) (erased (Qzt) qt) (erased (QInv cfs (Nil (Nat)) qt) qi)
      (erased (AllRed qt obl) a) -> (RedE cfs obl)))

; The cap checks of cap.sl, with their obligations passing redpart.
(def-adts $ (CapOK : ((List (Config)) cfs) ((List (List (Sub))) drs) -> Type)
  enum
  (many MkCapOK : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs cobl) (erased (Small drs) sm) (erased (CapL drs (Nil (List (Sub))) cobl 5 9) cl)
      (erased (RedE cfs cobl) re) -> (CapOK cfs drs)))

(def-fns _ $ (erased hit-red : (erased (List (Config)) cfs) (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) obl) (erased (Geo d e n f ks) g)
    (erased (MapHit d e f ks obl) h) (erased (RedE cfs obl) re) -> (erased (CfEmbed cfs d e n f ks) r))
  (let-match erased h (MkMapHit _ z _ _ _ q _ lz m ex))
  (let-match erased re (MkRedE _ _ qt qi ar))
  (hit-embed cfs d e n f ks g (qzt-hit cfs d e n f ks qt qi g (red-sound d z e n f ks qt q (allred-mem qt obl q ar m) g lz ex))))

(def-fns _ $ (erased hit-red : (erased (List (Config)) cfs) (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) obl) (erased (Geo d e n f ks) g)
    (erased (MapHit d e f ks obl) h) (erased (RedE cfs obl) re) -> (erased (CfEmbed cfs d e n f ks) r))
  (let-match erased h (MkMapHit _ z _ _ _ q _ lz m ex))
  (let-match erased re (MkRedE _ _ qt qi ar))
  (hit-embed cfs d e n f ks g (qzt-hit cfs d e n f ks qt qi g (red-sound d z e n f ks qt q (allred-mem qt obl q ar m) g lz ex))))

; A region of a walk: the walk of the script s from its context (nhub to f1) as check2-c reaches it, with the cut list ct.
(def-adts $ (Region : ((List (List (Sub))) drs) -> Type)
  enum
  (many MkRegion : (erased (List (List (Sub))) drs) (many (Nat) nhub) (many (List (List (Sub))) rt rs ct acc) (many (List (Pr2)) env)
      (many (List (Sub)) p0 p mp0 mp) (many (Script) s) (erased (OfSize nhub drs rs) sz) (erased (Tgt nhub drs rt) tg)
      (erased (EnvE nhub rt rs ct acc env) ee) (erased (Forced nhub rt rs ct p0 p acc) f0) (erased (Forced nhub rt rs ct mp0 mp acc) f1)
      -> (Region drs)))

; h is contained in the part p or mp of a region, of the same length.
(def-adts $ (PartOf : ((List (List (Sub))) drs) ((Region drs) x) ((List (Sub)) h) -> Type)
  enum
  (many POP : (erased (List (List (Sub))) drs) (erased (Nat) nhub) (erased (List (List (Sub))) rt rs ct acc) (erased (List (Pr2)) env) (erased (List (Sub)) p0 p mp0 mp) (erased (Script) s)
      (erased (OfSize nhub drs rs) sz) (erased (Tgt nhub drs rt) tg) (erased (EnvE nhub rt rs ct acc env) ee) (erased (Forced nhub rt rs ct p0 p acc) f0)
      (erased (Forced nhub rt rs ct mp0 mp acc) f1) (erased (List (Sub)) h) (erased (Nat) m)
      (erased (Pw (Sub) (Sub) SubSub h p) sb) (erased (Length (Sub) h m) lh) (erased (Length (Sub) p m) lp) -> (PartOf drs (MkRegion drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1) h))
  (many POM : (erased (List (List (Sub))) drs) (erased (Nat) nhub) (erased (List (List (Sub))) rt rs ct acc) (erased (List (Pr2)) env) (erased (List (Sub)) p0 p mp0 mp) (erased (Script) s)
      (erased (OfSize nhub drs rs) sz) (erased (Tgt nhub drs rt) tg) (erased (EnvE nhub rt rs ct acc env) ee) (erased (Forced nhub rt rs ct p0 p acc) f0)
      (erased (Forced nhub rt rs ct mp0 mp acc) f1) (erased (List (Sub)) h) (erased (Nat) m)
      (erased (Pw (Sub) (Sub) SubSub h mp) sb) (erased (Length (Sub) h m) lh) (erased (Length (Sub) mp m) lp) -> (PartOf drs (MkRegion drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1) h)))

(def-adts $ (InRegs : ((List (List (Sub))) drs) ((List (Sub)) h) ((List (Region drs)) t) -> Type)
  enum
  (many MkInRegs : (erased (List (List (Sub))) drs) (erased (List (Sub)) h) (erased (List (Region drs)) t) (erased (Region drs) x) (erased (Mem (Region drs) x t) m)
      (erased (PartOf drs x h) po) -> (InRegs drs h t)))

(def-adts $ (CutsIn : ((List (List (Sub))) drs) ((List (List (Sub))) ct) ((List (Region drs)) t) -> Type)
  enum
  (many CINil : (erased (List (List (Sub))) drs) (erased (List (Region drs)) t) -> (CutsIn drs (Nil (List (Sub))) t))
  (many CICons : (erased (List (List (Sub))) drs ct) (erased (List (Sub)) h) (erased (List (Region drs)) t) (erased (InRegs drs h t) i) (erased (CutsIn drs ct t) r)
      -> (CutsIn drs (Cons (List (Sub)) h ct) t)))

(def-fns _ $ (erased cutsin-at : (erased (List (List (Sub))) drs ct) (erased (List (Sub)) h) (erased (List (Region drs)) t) (subterm erased (CutsIn drs ct t) c)
    (erased (Mem (List (Sub)) h ct) m) -> (erased (InRegs drs h t) r))
  (let-match erased c (CICons _ ct1 h1 _ i rest) (absurd (CINil _ _) m))
  (match erased m _ ((MemHere _ _ _) i) ((MemThere _ _ _ _ m1) (cutsin-at drs ct1 h t rest m1))))

(def-fns _ $ (many part-in : (many (List (Sub)) h q) -> (many (Bool) ok) (many (Nat) m)
    (erased (IfT ok (Both (Pw (Sub) (Sub) SubSub h q) (Both (Length (Sub) h m) (Length (Sub) q m)))) w))
  (let ((many m) (erased lh)) (list-count _ h))
  (let ((many m2) (erased lq)) (list-count _ q))
  (let-match many (nat-eq m m2) (Equal _ _ _) (else (values (BFalse) m (IfF _))))
  (let ((many c) (erased a)) (part-cmp h q))
  (let-match many c (PSub) (else (values (BFalse) m (IfF _))))
  (let-match erased a (AnsSub _ _ sb))
  (values (BTrue) m (IfY _ (MkBoth _ _ sb (MkBoth _ _ lh lq)))))

(def-fns _ $ (many part-of-c : (erased (List (List (Sub))) drs) (many (Region drs) x) (many (List (Sub)) h) -> (many (Bool) ok) (erased (IfT ok (PartOf drs x h)) w))
  (let-match many x (MkRegion _ nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1))
  (let ((many okp) (many m) (erased wp)) (part-in h p))
  (let-match many okp (BFalse) ((BTrue)
    (let-match erased wp (IfY _ b))
    (let-match erased b (MkBoth _ _ sb b2))
    (let-match erased b2 (MkBoth _ _ lh lp))
    (values (BTrue) (IfY _ (POP drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1 h m sb lh lp)))))
  (let ((many okm) (many m2) (erased wm)) (part-in h mp))
  (let-match many okm (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let-match erased wm (IfY _ b))
  (let-match erased b (MkBoth _ _ sb b2))
  (let-match erased b2 (MkBoth _ _ lh lp))
  (values (BTrue) (IfY _ (POM drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1 h m2 sb lh lp))))

(def-fns _ $ (many in-regs-c : (erased (List (List (Sub))) drs) (many (List (Sub)) h) (subterm many (List (Region drs)) t)
    -> (many (Bool) ok) (erased (IfT ok (InRegs drs h t)) w))
  (let-match many t (Cons _ x rest) ((Nil _) (values (BFalse) (IfF _))))
  (let ((many ok) (erased w)) (part-of-c drs x h))
  (let-match many ok (BFalse) ((BTrue) (let-match erased w (IfY _ po)) (values (BTrue) (IfY _ (MkInRegs drs h t x (MemHere _ x rest) po)))))
  (let ((many ok2) (erased w2)) (tail $ in-regs-c drs h rest))
  (values ok2 (match erased w2 _
    ((IfY _ i) (let-match erased i (MkInRegs _ _ _ x2 m2 po2)) (IfY _ (MkInRegs drs h t x2 (MemThere _ x2 x rest m2) po2)))
    ((IfF _) (IfF _)))))

(def-fns _ $ (many cuts-in-c : (erased (List (List (Sub))) drs) (subterm many (List (List (Sub))) ct) (many (List (Region drs)) t)
    -> (many (Bool) ok) (erased (IfT ok (CutsIn drs ct t)) w))
  (let-match many ct (Cons _ h rest) ((Nil _) (values (BTrue) (IfY _ (CINil drs t)))))
  (let ((many ok1) (erased w1)) (in-regs-c drs h t))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) (IfF _))))
  (let-match erased w1 (IfY _ i))
  (let ((many ok2) (erased w2)) (tail $ cuts-in-c drs rest t))
  (values ok2 (match erased w2 _ ((IfY _ c) (IfY _ (CICons drs rest h t i c))) ((IfF _) (IfF _)))))

; The walk of a region passes and its obligations pass redpart; its cut list holds parts of the regions in t.
(def-adts $ (RegOK : ((List (Config)) cfs) ((List (List (Sub))) drs) ((Region drs) x) ((List (Region drs)) t) -> Type)
  enum
  (many MkRegOK : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (Nat) nhub) (erased (List (List (Sub))) rt rs ct acc) (erased (List (Pr2)) env) (erased (List (Sub)) p0 p mp0 mp) (erased (Script) s)
      (erased (OfSize nhub drs rs) sz) (erased (Tgt nhub drs rt) tg) (erased (EnvE nhub rt rs ct acc env) ee) (erased (Forced nhub rt rs ct p0 p acc) f0)
      (erased (Forced nhub rt rs ct mp0 mp acc) f1) (erased (List (List (Sub))) out) (erased (Qzt) qt)
      (erased (QInv cfs (Nil (Nat)) qt) qi) (erased (Pres nhub rt rs ct p out) d0) (erased (Pres nhub rt rs ct mp out) d1) (erased (AllRed qt out) ar)
      (erased (List (Region drs)) t) (erased (CutsIn drs ct t) ci) -> (RegOK cfs drs (MkRegion drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1) t)))

(def-adts $ (AllReg : ((List (Config)) cfs) ((List (List (Sub))) drs) ((List (Region drs)) xs) -> Type)
  enum
  (many ARgNil : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) -> (AllReg cfs drs (Nil (Region drs))))
  (many ARgCons : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (Region drs) x) (erased (List (Region drs)) t) (erased (RegOK cfs drs x t) a)
      (erased (AllReg cfs drs t) r) -> (AllReg cfs drs (Cons (Region drs) x t))))

; A dart of positive dscore fitting a part of a region exactly has its CfEmbed.
(def-fns _ $ (erased reg-claim : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (List (Region drs)) xs) (subterm erased (AllReg cfs drs xs) al)
    (erased (Region drs) x) (erased (Mem (Region drs) x xs) mx) (erased (List (Sub)) h) (erased (PartOf drs x h) po) (erased (Nat) d y pos neg) (erased (List (Nat)) e n f ks)
    (erased (Geo d e n f ks) g) (erased (Lt y d) ly) (erased (DScore d e n f ks drs y pos neg) ds) (erased (Lt neg pos) lt) (erased (ExactAt e f ks y h) xh)
    -> (erased (CfEmbed cfs d e n f ks) r))
  (let-match erased al (ARgCons _ _ x1 t ok rest) (absurd (ARgNil _ _) mx))
  (let-match erased mx (MemHere _ _ _) ((MemThere _ _ _ _ m1) (reg-claim cfs drs t rest x m1 h po d y pos neg e n f ks g ly ds lt xh)))
  (let-match erased ok (MkRegOK _ _ nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1 out qt qi d0 d1 ar _ ci))
  (let ((erased q) (erased xq) (erased dq))
    (match erased po (((List (Sub)) q) ((ExactAt e f ks y q) xq) ((Pres nhub rt rs ct q out) dq))
      ((POP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m sb lh lp) (values p (exact-sub-at e f ks y m h p xh sb lh lp) d0))
      ((POM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m sb lh lp) (values mp (exact-sub-at e f ks y m h mp xh sb lh lp) d1))))
  (let ((erased ws) (erased iw)) (iota-exists d))
  (match erased (pres-sound d nhub e n f ks ws drs rt rs ct g sz iw (tgt-all d d nhub e n f ks ws drs rt g tg iw (lt-succ d)) y pos neg out q ly ds lt xq dq) _
    ((PHMap _ _ _ _ _ _ _ _ mh) (hit-red cfs d e n f ks out g mh (MkRedE cfs out qt qi ar)))
    ((PHPos _ z _ _ _ _ _ _ _ _ _ q2 lz _ _ x2 m2) (hit-red cfs d e n f ks out g (MkMapHit d z e f ks q2 out lz m2 x2) (MkRedE cfs out qt qi ar)))
    ((PHCut _ z pos2 neg2 _ _ _ _ _ _ _ h2 lz ds2 lt2 x2 m2)
      (let-match erased (cutsin-at drs ct h2 t ci m2) (MkInRegs _ _ _ x3 m3 po3))
      (reg-claim cfs drs t rest x3 m3 h2 po3 d z pos2 neg2 e n f ks g lz ds2 lt2 x2))))

; The root regions of arities m to hi - 1 in xs.
(def-adts $ (RootsL : ((List (List (Sub))) drs) ((List (Region drs)) xs) ((Nat) m hi) -> Type)
  enum
  (many RLNil : (erased (List (List (Sub))) drs) (erased (List (Region drs)) xs) (erased (Nat) m) -> (RootsL drs xs m m))
  (many RLCons : (erased (List (List (Sub))) drs) (erased (List (Region drs)) xs) (erased (Nat) m hi) (erased (Region drs) x) (erased (List (Sub)) p)
      (erased (Mem (Region drs) x xs) mx) (erased (Repeat (Sub) m sub59 p) rp) (erased (PartOf drs x p) po) (erased (RootsL drs xs (Succ m) hi) rest)
      -> (RootsL drs xs m hi)))

(def-fns _ $ (erased roots-look : (erased (List (List (Sub))) drs) (erased (List (Region drs)) xs) (erased (Nat) a m hi) (subterm erased (RootsL drs xs m hi) rl)
    (erased (Lt m (Succ a)) lo) (erased (Lt a hi) up)
    -> (erased (Region drs) x) (erased (Mem (Region drs) x xs) mx) (erased (List (Sub)) p) (erased (Repeat (Sub) a sub59 p) rp) (erased (PartOf drs x p) po))
  (let-match erased rl (RLCons _ _ _ _ x p mx rp po rest) (absurd (RLNil _ _ _) (lt-le-absurd a m up lo)))
  (match erased (nat-eq a m) _
    ((Equal _ _ _) (values x mx p rp po))
    ((Unequal _ _ _ _ ap)
      (match erased ap _
        (absurd (ApLt _ _ _ _ l) (lt-le-absurd a m l lo))
        ((ApGt _ _ _ _ l) (roots-look drs xs a (Succ m) hi rest (LtS m a l) up))))))

(def-fns _ $ (many roots-c : (erased (List (List (Sub))) drs) (many (List (Region drs)) xs) (many (Nat) m hi) (subterm many (Nat) fuel)
    -> (many (Checked (RootsL drs xs m hi)) r))
  (let-match many (nat-eq m hi) (Unequal _ _ _ _ _) ((Equal _ _ _) (ChkYes _ (RLNil drs xs m))))
  (let-match many fuel (Succ f1) ((Zero) (ChkNo _)))
  (let ((many p) (erased rp)) (nseq-c _ m sub59))
  (let ((many ok) (erased w)) (in-regs-c drs p xs))
  (let-match many ok (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased w (IfY _ i))
  (let-match erased i (MkInRegs _ _ _ x mx po))
  (let-match many (notail $ roots-c drs xs (Succ m) hi f1) (ChkYes _ rest) ((ChkNo _) (ChkNo _)))
  (ChkYes _ (RLCons drs xs m hi x p mx rp po rest)))

(def-fns _ $ (erased unav-from : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (List (Region drs)) xs) (erased (AllReg cfs drs xs) al)
    (erased (RootsL drs xs 5 12) rl) (erased (CapOK cfs drs) co) -> (erased (UnavE cfs) r))
  (let-match erased co (MkCapOK _ _ cobl sm cl rc))
  (def-fns _ $ (erased every : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Connected d e n f) cc)
      (erased (Genus d e n f (Zero)) gen) -> (erased (CfEmbed cfs d e n f ks) r))
    (let ((erased x) (erased pos) (erased neg) (erased lx) (erased dsc) (erased lt)) (posz-dscore d e n f ks drs g cc gen))
    (let-match erased g (MkGeo _ _ _ _ _ _ _ _ ol ab))
    (let ((erased a) (erased pa) (erased _)) (arity-at d x f ks ol lx))
    (match erased (le-dec 12 a) _
      ((LeY _ _ l12)
        (let-match erased l12 (LtS _ _ l11))
        (hit-red cfs d e n f ks cobl g (cap-sound d x a pos neg e n f ks drs (Nil _) cobl g lx dsc lt pa l11 sm cl) rc))
      ((LeN _ _ la)
        (let ((erased rg) (erased mr) (erased p) (erased rp) (erased po)) (roots-look drs xs a 5 12 rl (LtS 4 a (above-nth ks 4 x a ab pa)) la))
        (let ((erased os) (erased ob)) (obs-exists d x e n f ks g a lx))
        (reg-claim cfs drs xs al rg mr p po d x pos neg e n f ks g lx dsc lt (MkExactAt e f ks x a os p pa ob (root-exact d x a e n f ks os p g ob rp))))))
  (MkUnavE cfs (level-of every) every))

; The context check2-c reaches at the end of path (true for a right branch) from the one given.
(def-adts $ (RCtx : ((Nat) nhub) ((List (List (Sub))) rt rs ct) -> Type)
  enum
  (many MkRCtx : (erased (Nat) nhub) (erased (List (List (Sub))) rt rs ct) (many (List (List (Sub))) acc) (many (List (Pr2)) env) (many (List (Sub)) p0 p mp0 mp)
      (erased (EnvE nhub rt rs ct acc env) ee) (erased (Forced nhub rt rs ct p0 p acc) f0) (erased (Forced nhub rt rs ct mp0 mp acc) f1) -> (RCtx nhub rt rs ct)))

(def-fns _ $ (many ctx-c : (many (Nat) nhub) (many (List (List (Sub))) rt rs ct acc) (many (List (Pr2)) env) (erased (EnvE nhub rt rs ct acc env) ee)
    (many (List (Sub)) p0 p mp0 mp) (erased (Forced nhub rt rs ct p0 p acc) f0) (erased (Forced nhub rt rs ct mp0 mp acc) f1) (subterm many (List (Bool)) path)
    (many (Script) s) -> (many (RCtx nhub rt rs ct) c))
  (let ((many here)) (MkRCtx nhub rt rs ct acc env p0 p mp0 mp ee f0 f1))
  (let-match many path (Cons _ right rest) ((Nil _) here))
  (let-match many s (SSplit i j k lo lab l r) (else here))
  (let ((many i2) (many j2)) (mloc i j mp))
  (let ((many pl) (many pr) (many p0l) (erased ql) (erased qh) (erased w0) (erased s0) (erased fl0)) (side-split nhub rt rs ct acc i j k lo p0 p f0))
  (let ((many mpl) (many mpr) (many mp0l) (erased mql) (erased mqh) (erased w1) (erased s1) (erased fl1)) (side-split nhub rt rs ct acc i2 j2 k lo mp0 mp f1))
  (let-match many right (BTrue) ((BFalse) (tail $ ctx-c nhub rt rs ct acc env ee p0l pl mp0l mpl fl0 fl1 rest l)))
  (let ((many ok1) (many o1) (erased v1)) (check2-c nhub rt rs ct acc env ee p0l pl mp0l mpl fl0 fl1 l))
  (let-match many ok1 (BTrue) ((BFalse) here))
  (let-match erased v1 (IfY _ x1))
  (let-match erased x1 (MkW3 _ _ _ _ _ _ _ _ dl0 dl1 e1))
  (let ((erased ee1)) (env-ext nhub rt rs ct acc o1 env ee e1))
  (let ((many env2) (erased ee2))
    (match many lab (((List (Pr2)) env2) ((EnvE nhub rt rs ct o1 env2) ee2))
      ((BTrue) (values (Cons _ (MkPr2 p0l mp0l) env)
        (EECons nhub rt rs ct o1 acc o1 acc o1 p0l pl mp0l mpl env fl0 dl0 e1 (ExtRefl o1) fl1 dl1 e1 (ExtRefl o1) ee1)))
      ((BFalse) (values env ee1))))
  (let ((erased fr0)) (FRight nhub k rt rs ct o1 o1 p0 p ql qh pl pr (forced-ext nhub rt rs ct acc o1 p0 p f0 e1) w0 s0 dl0 (ExtRefl o1)))
  (let ((erased fr1)) (FRight nhub k rt rs ct o1 o1 mp0 mp mql mqh mpl mpr (forced-ext nhub rt rs ct acc o1 mp0 mp f1 e1) w1 s1 dl1 (ExtRefl o1)))
  (tail $ ctx-c nhub rt rs ct o1 env2 ee2 p0 pr mp0 mpr fr0 fr1 rest r))

(def-fns _ $ (many sc-leaves : (subterm many (Script) s) -> (many (Nat) n))
  (match many s _ ((SSplit _ _ _ _ _ l r) (nat-add (notail $ sc-leaves l) (notail $ sc-leaves r))) ((SRed) 1) ((SHub _) 1) (else 0)))

(def-adts $ (Cut : -> Type)
  enum
  (many MkCut : (many (List (Bool)) path) (many (Script) s) -> (Cut)))

; s with each largest subtree of small to big leaves cut out (SCut), and those subtrees with their paths, in walk order.
(def-fns _ $ (many cut-script : (many (Nat) small big) (many (List (Bool)) rpath) (subterm many (Script) s) -> (many (Script) skel) (many (List (Cut)) cuts))
  (let ((many n)) (sc-leaves s))
  (let-match many (andb (leb small n) (leb n big)) (BFalse) ((BTrue) (values (SCut) (Cons _ (MkCut (rev-onto _ rpath (Nil _)) s) (Nil _)))))
  (let-match many s (SSplit i j k lo lab l r) (else (values s (Nil _))))
  (let ((many sl) (many cl)) (notail $ cut-script small big (Cons _ (BFalse) rpath) l))
  (let ((many sr) (many cr)) (notail $ cut-script small big (Cons _ (BTrue) rpath) r))
  (values (SSplit i j k lo lab sl sr) (cat _ cl cr)))

(def-fns _ $ (many push-regs : (erased (List (List (Sub))) drs) (many (Nat) a) (many (List (List (Sub))) rt rs) (many (List (Sub)) p) (many (Script) skel)
    (erased (OfSize a drs rs) sz) (erased (Tgt a drs rt) tg) (many (List (List (Sub))) ct) (many (List (Region drs)) xs) (subterm many (List (Cut)) cs)
    -> (many (List (List (Sub))) ct2) (many (List (Region drs)) xs2))
  (let ((erased e0) (erased f0)) (values (EENil a rt rs ct (Nil _)) (FRoot a rt rs ct (Nil _) p)))
  (let-match many cs (Cons _ c rest) ((Nil _) (values ct (Cons _ (MkRegion drs a rt rs ct (Nil _) (Nil _) p p p p skel sz tg e0 f0 f0) xs))))
  (let-match many c (MkCut path sub))
  (let-match many (ctx-c a rt rs ct (Nil _) (Nil _) e0 p p p p f0 f0 path skel) (MkRCtx _ _ _ _ acc env q0 q mq0 mq ee g0 g1))
  (tail $ push-regs drs a rt rs p skel sz tg (Cons _ q $ Cons _ mq ct) (Cons _ (MkRegion drs a rt rs ct acc env q0 q mq0 mq sub sz tg ee g0 g1) xs) rest))

; The regions of the walk of arity a by s, cut at small to big leaves, pushed onto xs after the regions whose parts ct holds;
; the region of the walk's root, with the cut subtrees left as SCut, is pushed last.
(def-fns _ $ (many arity-regs : (many (List (List (Sub))) drs) (many (Nat) a small big) (many (Script) s) (many (List (List (Sub))) ct)
    (many (List (Region drs)) xs) -> (many (List (List (Sub))) ct2) (many (List (Region drs)) xs2))
  (let ((many rs) (erased sz)) (of-size-c a drs))
  (let ((many rt) (erased tg)) (pick-target-c a drs))
  (let ((many p) (erased _)) (nseq-c _ a sub59))
  (let ((many skel) (many cuts))
    (match many (leb (sc-leaves s) big) (((Script) skel) ((List (Cut)) cuts)) ((BTrue) (values s (Nil _))) ((BFalse) (cut-script small big (Nil _) s))))
  (push-regs drs a rt rs p skel sz tg ct xs cuts))

(def-fns _ $ (many all-regs : (many (List (List (Sub))) drs) (many (Nat) a small big) (subterm many (List (Script)) ss) (many (List (List (Sub))) ct)
    (many (List (Region drs)) xs) -> (many (List (Region drs)) xs2))
  (let-match many ss (Cons _ s rest) ((Nil _) xs))
  (let ((many ct2) (many xs2)) (arity-regs drs a small big s ct xs))
  (tail $ all-regs drs (Succ a) small big rest ct2 xs2))

(let ((many drs)) (symmetrize (base-drules)))

; One job per region.
(def-fns _ $ (many reg-c : (many (Region drs) x) (many (List (Region drs)) t) -> (many (Checked (RegOK cfs drs x t)) r))
  (let-match many x (MkRegion _ nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1))
  (let ((many ok) (many out) (erased w)) (check2-c nhub rt rs ct acc env ee p0 p mp0 mp f0 f1 s))
  (let-match many ok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many cok) (erased cw)) (cuts-in-c drs ct t))
  (let-match many cok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many qt) (many qc))
    (match many out (((Qzt) qt) ((Checked (QInv cfs (Nil (Nat)) qt)) qc)) ((Nil _) (values (QztNil) (ChkYes _ (QINil cfs (Nil _))))) (else (quiz-tree-c cfs))))
  (let-match many qc (ChkYes _ qi) ((ChkNo _) (ChkNo _)))
  (let ((many rok) (erased rw)) (allred-c qt out))
  (let-match many rok (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased w (IfY _ w3))
  (let-match erased w3 (MkW3 _ _ _ _ _ _ _ _ d0 d1 _))
  (let-match erased cw (IfY _ ci))
  (let-match erased rw (IfY _ ar))
  (ChkYes _ (MkRegOK cfs drs nhub rt rs ct acc env p0 p mp0 mp s sz tg ee f0 f1 out qt qi d0 d1 ar t ci)))

(def-fns _ $ (many cap-run : -> (many (Checked (CapOK cfs drs)) r))
  (let ((many qt) (many qc)) (quiz-tree-c cfs))
  (let-match many qc (ChkYes _ qi) ((ChkNo _) (ChkNo _)))
  (let ((many sok) (erased sw)) (small-c drs))
  (let-match many sok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many cok) (many cobl) (erased cw)) (cap-c drs (Nil _) 5 9 4))
  (let-match many cok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many rok) (erased rw)) (allred-c qt cobl))
  (let-match many rok (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased sw (IfY _ sm))
  (let-match erased cw (IfY _ cl))
  (let-match erased rw (IfY _ ar))
  (ChkYes _ (MkCapOK cfs drs cobl sm cl (MkRedE cfs cobl qt qi ar))))

(let ((many regs))
  (all-regs drs 5 100 800 (Cons _ (script5) $ Cons _ (script6) $ Cons _ (script7) $ Cons _ (script8) $ Cons _ (script9) $ Cons _ (script10) $ Cons _ (script11) $ Nil _)
    (Nil _) (Nil _)))
(comptime-match many (roots-c drs regs 5 12 7) (ChkYes _ regs-roots))
(native-each unav-regs regs (x t r) (Checked (RegOK cfs drs x t)) (reg-c x t) (ChkYes _ a) (ARgCons cfs drs x t a r) (ARgNil cfs drs))
(native-jobs unav-cap ac (cap-run (ChkYes _ ac)))
(native-then (let ((erased unav-proof)) (unav-from cfs drs regs unav-regs regs-roots unav-cap)))
