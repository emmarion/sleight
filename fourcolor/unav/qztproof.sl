; Unavoidability in the shape of unavoidability.v, with the embedding of quiz.v: in every plain cubic connected pentagonal
; map of genus 0, a configuration of red/configs.sl has a preembedding of its kernel into the map or its mirror (CfEmbed).
; The computed part is split into independent jobs for native.sl, one per hub arity 5 to 11 (the certified walk of that
; arity and the certified redpart of redc.sl on each of its obligations) and one for the cap checks; each builds the quiz
; tree with its evidence (qtree.sl) for itself. Once (native-run) has run them, unav-from puts their evidence together into
; unav-proof. The cfs in scope are those of qztcfs.sl or fcopen.sl. Load after unave.sl and data.sl.

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

(def-adts $ (RedEW : ((List (Config)) cfs) ((List (List (List (Sub)))) wobl) -> Type)
  enum
  (many REWNil : (erased (List (Config)) cfs) -> (RedEW cfs (Nil (List (List (Sub))))))
  (many REWCons : (erased (List (Config)) cfs) (erased (List (List (Sub))) obl) (erased (List (List (List (Sub)))) rest) (erased (RedE cfs obl) a)
      (erased (RedEW cfs rest) r) -> (RedEW cfs (Cons (List (List (Sub))) obl rest))))

(def-fns _ $ (erased redew-nth : (erased (List (Config)) cfs) (erased (List (List (List (Sub)))) wobl) (erased (Nat) i) (erased (List (List (Sub))) obl)
    (subterm erased (RedEW cfs wobl) a) (erased (Nth (List (List (Sub))) wobl i obl) pn) -> (erased (RedE cfs obl) r))
  (let-match erased a (REWCons _ o1 rest a0 a1) (absurd (REWNil _) pn))
  (let-match erased pn (NthThere _ _ _ i1 _ pn1) ((NthHere _ _ _) a0))
  (redew-nth cfs rest i1 obl a1 pn1))

; The certified walk of arity a, with its obligations passing redpart.
(def-adts $ (ArityOK : ((List (Config)) cfs) ((List (List (Sub))) drs) ((Nat) a) -> Type)
  enum
  (many MkArityOK : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs rs rt out) (erased (Nat) a) (erased (List (Sub)) p)
      (erased (OfSize a drs rs) sz) (erased (Tgt a drs rt) tg) (erased (Repeat (Sub) a sub59 p) rp) (erased (Pres a rt rs (Nil (List (Sub))) p out) pr)
      (erased (RedE cfs out) re) -> (ArityOK cfs drs a)))

(def-adts $ (ArityL : ((List (Config)) cfs) ((List (List (Sub))) drs) ((Nat) m hi) -> Type)
  enum
  (many ALNil : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (Nat) m) -> (ArityL cfs drs m m))
  (many ALCons : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (Nat) m hi) (erased (ArityOK cfs drs m) a)
      (erased (ArityL cfs drs (Succ m) hi) r) -> (ArityL cfs drs m hi)))

(def-fns _ $ (erased arity-walk : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (Nat) m hi) (subterm erased (ArityL cfs drs m hi) al)
    -> (erased (List (List (List (Sub)))) wobl) (erased (WalkL drs wobl m hi) wl) (erased (RedEW cfs wobl) rw))
  (let-match erased al (ALCons _ _ _ _ a r) ((ALNil _ _ _) (values (Nil _) (WLNil drs m) (REWNil cfs))))
  (let-match erased a (MkArityOK _ _ rs rt out _ p sz tg rp pr re))
  (let ((erased wobl) (erased wl) (erased rw)) (arity-walk cfs drs (Succ m) hi r))
  (values (Cons _ out wobl) (WLCons drs rs rt out wobl m hi p sz tg rp pr wl) (REWCons cfs out wobl re rw)))

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

(def-fns _ $ (erased unav-from : (erased (List (Config)) cfs) (erased (List (List (Sub))) drs) (erased (ArityL cfs drs 5 12) al) (erased (CapOK cfs drs) co)
    -> (erased (UnavE cfs) r))
  (let ((erased wobl) (erased wl) (erased rw)) (arity-walk cfs drs 5 12 al))
  (let-match erased co (MkCapOK _ _ cobl sm cl rc))
  (def-fns _ $ (erased every : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Connected d e n f) cc)
      (erased (Genus d e n f (Zero)) gen) -> (erased (CfEmbed cfs d e n f ks) r))
    (let ((erased x) (erased pos) (erased neg) (erased lx) (erased dsc) (erased lt)) (posz-dscore d e n f ks drs g cc gen))
    (match erased (unav-dart d x pos neg e n f ks drs (Nil _) cobl wobl sm wl cl g lx dsc lt) _
      ((UWalk _ _ _ i _ _ _ _ _ obl _ _ pn h) (hit-red cfs d e n f ks obl g h (redew-nth cfs wobl i obl rw pn)))
      ((UCap _ _ _ _ _ _ _ _ _ _ h) (hit-red cfs d e n f ks cobl g h rc))))
  (MkUnavE cfs (level-of every) every))

(let ((many drs)) (symmetrize (base-drules)))

(def-fns _ $ (many arity-c : (many (Nat) a) (many (Script) s) -> (many (Checked (ArityOK cfs drs a)) r))
  (let ((many qt) (many qc)) (quiz-tree-c cfs))
  (let-match many qc (ChkYes _ qi) ((ChkNo _) (ChkNo _)))
  (let ((many rs) (erased sz)) (of-size-c a drs))
  (let ((many rt) (erased tg)) (pick-target-c a drs))
  (let ((many p) (erased rp)) (nseq-c _ a sub59))
  (let ((many ok1) (many out) (erased w1))
    (check2-c a rt rs (Nil (List (Sub))) (Nil _) (Nil _) (EENil a rt rs (Nil (List (Sub))) (Nil _)) p p p p (FRoot a rt rs (Nil (List (Sub))) (Nil _) p) (FRoot a rt rs (Nil (List (Sub))) (Nil _) p) s))
  (let-match many ok1 (BTrue) ((BFalse) (ChkNo _)))
  (let ((many rok) (erased rw)) (allred-c qt out))
  (let-match many rok (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased w1 (IfY _ w3))
  (let-match erased w3 (MkW3 _ _ _ _ _ _ _ _ pr _ _))
  (let-match erased rw (IfY _ ar))
  (ChkYes _ (MkArityOK cfs drs rs rt out a p sz tg rp pr (MkRedE cfs out qt qi ar))))

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

(def-fns _ $ (many arity5-run : -> (many (Checked (ArityOK cfs drs 5)) r)) (arity-c 5 (script5)))
(def-fns _ $ (many arity6-run : -> (many (Checked (ArityOK cfs drs 6)) r)) (arity-c 6 (script6)))
(def-fns _ $ (many arity7-run : -> (many (Checked (ArityOK cfs drs 7)) r)) (arity-c 7 (script7)))
(def-fns _ $ (many arity8-run : -> (many (Checked (ArityOK cfs drs 8)) r)) (arity-c 8 (script8)))
(def-fns _ $ (many arity9-run : -> (many (Checked (ArityOK cfs drs 9)) r)) (arity-c 9 (script9)))
(def-fns _ $ (many arity10-run : -> (many (Checked (ArityOK cfs drs 10)) r)) (arity-c 10 (script10)))
(def-fns _ $ (many arity11-run : -> (many (Checked (ArityOK cfs drs 11)) r)) (arity-c 11 (script11)))

(unary 6 5)
(unary 7 6)
(unary 8 7)
(unary 9 8)
(unary 10 9)
(unary 11 10)
(unary 12 11)
(native-jobs unav-proof
  (unav-from cfs drs (ALCons cfs drs 5 12 a5 $ ALCons cfs drs 6 12 a6 $ ALCons cfs drs 7 12 a7 $ ALCons cfs drs 8 12 a8 $ ALCons cfs drs 9 12 a9 $
    ALCons cfs drs 10 12 a10 $ ALCons cfs drs 11 12 a11 $ ALNil cfs drs 12) ac)
  (arity5-run (ChkYes _ a5)) (arity6-run (ChkYes _ a6)) (arity7-run (ChkYes _ a7)) (arity8-run (ChkYes _ a8)) (arity9-run (ChkYes _ a9))
  (arity10-run (ChkYes _ a10)) (arity11-run (ChkYes _ a11)) (cap-run (ChkYes _ ac)))
