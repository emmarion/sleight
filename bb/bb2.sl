(def-adts $ (Flag : -> Type)
  enum
  (many FZ : -> (Flag))
  (many FT : -> (Flag)))

(def-adts $ (Side : -> Type)
  enum
  (many MkSide : (many (List (Bool)) seg) (many (Flag) f) -> (Side)))

(def-adts $ (ACfg : -> Type)
  enum
  (many MkA : (many (Nat) q) (many (Side) l) (many (Bool) h) (many (Side) r) -> (ACfg)))

(def-adts
  ((AllZero : ((List (Bool)) xs) -> Type)
    enum
    (many AZNil : -> (AllZero (Nil (Bool))))
    (many AZCons : (erased (List (Bool)) xs) (erased (AllZero xs) p) -> (AllZero (Cons (Bool) (BFalse) xs)))))

(def-adts
  ((GS : ((Side) s) ((List (Bool)) xs) -> Type)
    enum
    (many GZ : (erased (List (Bool)) xs) (erased (AllZero xs) z) -> (GS (MkSide (Nil (Bool)) (FZ)) xs))
    (many GT : (erased (List (Bool)) xs) -> (GS (MkSide (Nil (Bool)) (FT)) xs))
    (many GC1 : (erased (List (Bool)) seg xs) (erased (Flag) f) (erased (Bool) b) (erased (GS (MkSide seg f) xs) g)
       -> (GS (MkSide (Cons (Bool) b seg) f) (Cons (Bool) b xs)))
    (many GC0 : (erased (List (Bool)) seg) (erased (Flag) f) (erased (GS (MkSide seg f) (Nil (Bool))) g)
       -> (GS (MkSide (Cons (Bool) (BFalse) seg) f) (Nil (Bool))))))

(def-adts
  ((GCfg : ((ACfg) a) ((Conf) c) -> Type)
    enum
    (many MkGCfg : (erased (Nat) q) (erased (Side) sl sr) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (GS sl l) gl) (erased (GS sr r) gr) -> (GCfg (MkA q sl h sr) (MkConf q l h r)))))

(def-adts
  ((APop : ((Side) s) ((Bool) b) ((Side) s2) -> Type)
    enum
    (many APZ : -> (APop (MkSide (Nil (Bool)) (FZ)) (BFalse) (MkSide (Nil (Bool)) (FZ))))
    (many APT : (erased (Bool) b) -> (APop (MkSide (Nil (Bool)) (FT)) b (MkSide (Nil (Bool)) (FT))))
    (many APC : (erased (List (Bool)) seg) (erased (Flag) f) (erased (Bool) b)
       -> (APop (MkSide (Cons (Bool) b seg) f) b (MkSide seg f)))))

(def-adts
  ((DropLast : ((List (Bool)) xs) ((Bool) x) ((List (Bool)) ys) -> Type)
    enum
    (many DL1 : (erased (Bool) x) -> (DropLast (Cons (Bool) x (Nil (Bool))) x (Nil (Bool))))
    (many DL2 : (erased (List (Bool)) xs ys) (erased (Bool) x b) (erased (DropLast xs x ys) p)
       -> (DropLast (Cons (Bool) b xs) x (Cons (Bool) b ys)))))

(def-adts
  ((FlagAfter : ((Flag) f) ((Bool) x) ((Flag) g) -> Type)
    enum
    (many FAZ : -> (FlagAfter (FZ) (BFalse) (FZ)))
    (many FAT : (erased (Flag) f) (erased (Bool) x) -> (FlagAfter f x (FT)))))

(def-adts
  ((APush : ((Side) s) ((Bool) w) ((Side) s2) -> Type)
    enum
    (many PKeep : (erased (List (Bool)) seg) (erased (Flag) f) (erased (Bool) w)
       -> (APush (MkSide seg f) w (MkSide (Cons (Bool) w seg) f)))
    (many PDrop : (erased (List (Bool)) seg seg2) (erased (Flag) f f2) (erased (Bool) w x)
       (erased (DropLast (Cons (Bool) w seg) x seg2) dl) (erased (FlagAfter f x f2) fa)
       -> (APush (MkSide seg f) w (MkSide seg2 f2)))))

(def-fns _ $ (erased pop-sound : (erased (Side) s) (erased (List (Bool)) xs ys) (erased (Bool) b)
    (erased (GS s xs) g) (erased (Pull xs b ys) p) ->
    (erased (Side) s2) (erased (APop s b s2) ap) (erased (GS s2 ys) g2))
  (match erased g _
    ((GZ xs1 z)
      (match erased p _
        ((PullNil) (values (MkSide (Nil (Bool)) (FZ)) (APZ) (GZ (Nil (Bool)) (AZNil))))
        ((PullCons b1 ys1)
          (let-match erased z (AZCons _ z1))
          (values (MkSide (Nil (Bool)) (FZ)) (APZ) (GZ ys z1)))))
    ((GT xs1) (values (MkSide (Nil (Bool)) (FT)) (APT b) (GT ys)))
    ((GC1 seg xs1 f b1 g1) (let-match erased p (PullCons _ _)) (values (MkSide seg f) (APC seg f b) g1))
    ((GC0 seg f g1) (let-match erased p (PullNil)) (values (MkSide seg f) (APC seg f b) g1))))

(def-fns _ $ (erased drop-sound : (erased (List (Bool)) seg seg2 xs) (erased (Flag) f f2) (erased (Bool) x)
    (erased (GS (MkSide seg f) xs) g) (subterm erased (DropLast seg x seg2) dl) (erased (FlagAfter f x f2) fa) ->
    (erased (GS (MkSide seg2 f2) xs) g2))
  (match erased dl _
    ((DL1 x1)
      (match erased fa _
        ((FAZ)
          (match erased g _
            ((GC1 _ xs1 _ _ g1) (let-match erased g1 (GZ _ z)) (GZ xs (AZCons xs1 z)))
            ((GC0 _ _ g1) (GZ xs (AZNil)))))
        ((FAT _ _) (GT xs))))
    ((DL2 segt segt2 x1 b dl1)
      (match erased g _
        ((GC1 _ xs1 _ _ g1) (GC1 segt2 xs1 f2 b (drop-sound segt segt2 xs1 f f2 x g1 dl1 fa)))
        ((GC0 _ _ g1) (GC0 segt2 f2 (drop-sound segt segt2 (Nil (Bool)) f f2 x g1 dl1 fa)))))))

(def-fns _ $ (erased push-sound : (erased (Side) s s2) (erased (List (Bool)) xs) (erased (Bool) w)
    (erased (GS s xs) g) (erased (APush s w s2) ap) -> (erased (GS s2 (Cons (Bool) w xs)) g2))
  (match erased ap _
    ((PKeep seg f _) (GC1 seg xs f w g))
    ((PDrop seg seg2 f f2 _ x dl fa)
      (drop-sound (Cons (Bool) w seg) seg2 (Cons (Bool) w xs) f f2 x (GC1 seg xs f w g) dl fa))))

(def-adts
  ((Place : ((Mv) d) ((Nat) q) ((Side) p) ((Bool) b) ((Side) o) ((ACfg) a) -> Type)
    enum
    (many PlL : (erased (Nat) q) (erased (Side) p o) (erased (Bool) b) -> (Place (DL) q p b o (MkA q p b o)))
    (many PlR : (erased (Nat) q) (erased (Side) p o) (erased (Bool) b) -> (Place (DR) q p b o (MkA q o b p)))))

(def-adts
  ((AllPop : ((List (ACfg)) S) ((Mv) d) ((Nat) q) ((Side) p) ((Side) o) -> Type)
    enum
    (many AllZ : (erased (List (ACfg)) S) (erased (Mv) d) (erased (Nat) q) (erased (Side) o) (erased (ACfg) a)
       (erased (Place d q (MkSide (Nil (Bool)) (FZ)) (BFalse) o a) pl) (erased (Mem (ACfg) a S) mm)
       -> (AllPop S d q (MkSide (Nil (Bool)) (FZ)) o))
    (many AllT : (erased (List (ACfg)) S) (erased (Mv) d) (erased (Nat) q) (erased (Side) o) (erased (ACfg) a0 a1)
       (erased (Place d q (MkSide (Nil (Bool)) (FT)) (BFalse) o a0) pl0) (erased (Mem (ACfg) a0 S) mm0)
       (erased (Place d q (MkSide (Nil (Bool)) (FT)) (BTrue) o a1) pl1) (erased (Mem (ACfg) a1 S) mm1)
       -> (AllPop S d q (MkSide (Nil (Bool)) (FT)) o))
    (many AllC : (erased (List (ACfg)) S) (erased (Mv) d) (erased (Nat) q) (erased (Side) o) (erased (ACfg) a)
       (erased (List (Bool)) seg) (erased (Flag) f) (erased (Bool) b)
       (erased (Place d q (MkSide seg f) b o a) pl) (erased (Mem (ACfg) a S) mm)
       -> (AllPop S d q (MkSide (Cons (Bool) b seg) f) o))))

(def-adts
  ((AOK : ((List (Tr)) m) ((List (ACfg)) S) ((ACfg) a) -> Type)
    enum
    (many AOKL : (erased (List (Tr)) m) (erased (List (ACfg)) S) (erased (Nat) q q2) (erased (Side) l r r2) (erased (Bool) h w)
       (erased (Look m q h (Mov w (DL) q2)) lk) (erased (APush r w r2) ap) (erased (AllPop S (DL) q2 l r2) al)
       -> (AOK m S (MkA q l h r)))
    (many AOKR : (erased (List (Tr)) m) (erased (List (ACfg)) S) (erased (Nat) q q2) (erased (Side) l r l2) (erased (Bool) h w)
       (erased (Look m q h (Mov w (DR) q2)) lk) (erased (APush l w l2) ap) (erased (AllPop S (DR) q2 r l2) al)
       -> (AOK m S (MkA q l h r)))))

(def-adts
  ((Closed : ((List (Tr)) m) ((List (ACfg)) S) ((List (ACfg)) T) -> Type)
    enum
    (many CNil : (erased (List (Tr)) m) (erased (List (ACfg)) S) -> (Closed m S (Nil (ACfg))))
    (many CCons : (erased (List (Tr)) m) (erased (List (ACfg)) S T) (erased (ACfg) a)
       (erased (AOK m S a) ok) (erased (Closed m S T) rest) -> (Closed m S (Cons (ACfg) a T)))))

(def-fns _ $ (erased closed-get : (erased (List (Tr)) m) (erased (List (ACfg)) S T) (erased (ACfg) a)
    (erased (Closed m S T) cl) (subterm erased (Mem (ACfg) a T) mm) -> (erased (AOK m S a) ok))
  (match erased mm _
    ((MemHere _ _ rest) (let-match erased cl (CCons _ _ _ _ ok _)) ok)
    ((MemThere _ _ y rest mm1) (let-match erased cl (CCons _ _ _ _ _ cl1)) (closed-get m S rest a cl1 mm1))))

(def-fns _ $ (erased allpop-mem : (erased (List (ACfg)) S) (erased (Mv) d) (erased (Nat) q) (erased (Side) p o p2) (erased (Bool) b)
    (erased (AllPop S d q p o) al) (erased (APop p b p2) ap) ->
    (erased (ACfg) a) (erased (Place d q p2 b o a) pl) (erased (Mem (ACfg) a S) mm))
  (match erased ap _
    ((APZ) (let-match erased al (AllZ _ _ _ _ a pl mm)) (values a pl mm))
    ((APT _)
      (let-match erased al (AllT _ _ _ _ a0 a1 pl0 mm0 pl1 mm1))
      (match erased b _
        ((BFalse) (values a0 pl0 mm0))
        ((BTrue) (values a1 pl1 mm1))))
    ((APC seg f _) (let-match erased al (AllC _ _ _ _ a _ _ _ pl mm)) (values a pl mm))))

(def-fns _ $ (erased never : (erased (List (Tr)) m) (erased (List (ACfg)) S) (erased (Closed m S S) cl)
    (erased (ACfg) a) (erased (Mem (ACfg) a S) mm) (erased (Conf) c) (erased (GCfg a c) g)
    (erased (Nat) s) (subterm erased (HaltsAt m c s) hs) -> (erased (False) f))
  (let-match erased g (MkGCfg q sl sr l r h gl gr))
  (let ((erased ok)) (closed-get m S S a cl mm))
  (match erased hs _
    ((HStop _ _ _ _ _ lk)
      (match erased ok _
        (absurd (AOKL _ _ _ _ _ _ _ _ _ lk2 _ _) (look-fn m q h _ _ lk lk2))
        (absurd (AOKR _ _ _ _ _ _ _ _ _ lk2 _ _) (look-fn m q h _ _ lk lk2))))
    ((HMove _ _ d s1 st hs1)
      (match erased st _
        ((StepL _ _ q2 _ _ l2 _ w h2 lk pp)
          (match erased ok _
            ((AOKL _ _ _ qa _ _ r2 _ wa lk2 ap al)
              (let-match erased (look-fn m q h _ _ lk lk2) (Refl _ _))
              (let ((erased p2) (erased app) (erased gl2)) (pop-sound sl l l2 h2 gl pp))
              (let ((erased gr2)) (push-sound sr r2 r w gr ap))
              (let ((erased a2) (erased pl) (erased mm2)) (allpop-mem S (DL) q2 sl r2 p2 h2 al app))
              (let-match erased pl (PlL _ _ _ _))
              (never m S cl a2 mm2 d (MkGCfg q2 p2 r2 l2 (Cons (Bool) w r) h2 gl2 gr2) s1 hs1))
            (absurd (AOKR _ _ _ _ _ _ _ _ _ lk2 _ _) (look-fn m q h _ _ lk lk2))))
        ((StepR _ _ q2 _ _ r2 _ w h2 lk pp)
          (match erased ok _
            (absurd (AOKL _ _ _ _ _ _ _ _ _ lk2 _ _) (look-fn m q h _ _ lk lk2))
            ((AOKR _ _ _ qa _ _ l2 _ wa lk2 ap al)
              (let-match erased (look-fn m q h _ _ lk lk2) (Refl _ _))
              (let ((erased p2) (erased app) (erased gr2)) (pop-sound sr r r2 h2 gr pp))
              (let ((erased gl2)) (push-sound sl l2 l w gl ap))
              (let ((erased a2) (erased pl) (erased mm2)) (allpop-mem S (DR) q2 sr l2 p2 h2 al app))
              (let-match erased pl (PlR _ _ _ _))
              (never m S cl a2 mm2 d (MkGCfg q2 l2 p2 (Cons (Bool) w l) r2 h2 gl2 gr2) s1 hs1))))))))

(def-adts
  ((LookR : ((List (Tr)) m) ((Nat) q) ((Bool) b) -> Type)
    enum
    (many LFound : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (many (Tr) t) (erased (Look m q b t) p) -> (LookR m q b))
    (many LMiss : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) -> (LookR m q b))))

(def-fns _ $ (many look : (subterm many (List (Tr)) m) (many (Nat) q) (many (Bool) b) -> (many (LookR m q b) r))
  (let-match many m (Cons _ t0 m1) ((Nil _) (LMiss m q b)))
  (let-match many m1 (Cons _ t1 rest) ((Nil _) (LMiss m q b)))
  (match many q _
    ((Zero)
      (match many b _
        ((BFalse) (LFound m q b t0 (Look0 t0 t1 rest)))
        ((BTrue) (LFound m q b t1 (Look1 t0 t1 rest)))))
    ((Succ q1)
      (let-match many (notail $ look rest q1 b) (LFound _ _ _ t p) ((LMiss _ _ _) (LMiss m q b)))
      (LFound m q b t (LookS t0 t1 rest q1 b t p)))))

(def-fns _ $ (many pop : (many (List (Bool)) xs) -> (many (Bool) b) (many (List (Bool)) ys) (erased (Pull xs b ys) p))
  (match many xs _
    ((Nil _) (values (BFalse) (Nil (Bool)) (PullNil)))
    ((Cons _ b ys) (values b ys (PullCons b ys)))))

(def-fns _ $ (many sim : (many (List (Tr)) m) (subterm many (Nat) fuel)
    (many (Nat) q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r) -> (many (SimR m (MkConf q l h r)) res))
  (let-match many fuel (Succ f) ((Zero) (SRun m (MkConf q l h r))))
  (let-match many (look m q h) (LFound _ _ _ t lk) ((LMiss _ _ _) (SRun m (MkConf q l h r))))
  (let-match many t (Mov w d q2) ((Hlt) (SHalt m (MkConf q l h r) (Succ (Zero)) (HStop m q l r h lk))))
  (match many d _
    ((DL)
      (let ((many h2) (many l2) (erased pp)) (pop l))
      (let-match many (notail $ sim m f q2 l2 h2 (Cons (Bool) w r)) (SHalt _ _ s p) ((SRun _ _) (SRun m (MkConf q l h r))))
      (SHalt m (MkConf q l h r) (Succ s) (HMove m (MkConf q l h r) _ s (StepL m q q2 l r l2 h w h2 lk pp) p)))
    ((DR)
      (let ((many h2) (many r2) (erased pp)) (pop r))
      (let-match many (notail $ sim m f q2 (Cons (Bool) w l) h2 r2) (SHalt _ _ s p) ((SRun _ _) (SRun m (MkConf q l h r))))
      (SHalt m (MkConf q l h r) (Succ s) (HMove m (MkConf q l h r) _ s (StepR m q q2 l r r2 h w h2 lk pp) p)))))

(def-fns _ $ (many eq-flag : (many (Flag) x) (many (Flag) y) -> (many (Maybe (Eq (Flag) x y)) r))
  (match many x _
    ((FZ) (match many y _ ((FZ) (Some _ (Refl (Flag) x))) ((FT) (None _))))
    ((FT) (match many y _ ((FT) (Some _ (Refl (Flag) x))) ((FZ) (None _))))))

(def-fns _ $ (many eq-bits : (subterm many (List (Bool)) x) (many (List (Bool)) y) -> (many (Maybe (Eq (List (Bool)) x y)) r))
  (match many x _
    ((Nil _) (match many y _ ((Nil _) (Some _ (Refl (List (Bool)) x))) (else (None _))))
    ((Cons _ a xs)
      (let-match many y (Cons _ b ys) ((Nil _) (None _)))
      (let-match many (eq-bit a b) (Some _ e1) ((None _) (None _)))
      (let-match many (notail $ eq-bits xs ys) (Some _ e2) ((None _) (None _)))
      (let-match many e1 (Refl _ _))
      (let-match many e2 (Refl _ _))
      (Some _ (Refl (List (Bool)) x)))))

(def-fns _ $ (many eq-side : (many (Side) x) (many (Side) y) -> (many (Maybe (Eq (Side) x y)) r))
  (let-match many x (MkSide s1 f1))
  (let-match many y (MkSide s2 f2))
  (let-match many (eq-bits s1 s2) (Some _ e1) ((None _) (None _)))
  (let-match many (eq-flag f1 f2) (Some _ e2) ((None _) (None _)))
  (let-match many e1 (Refl _ _))
  (let-match many e2 (Refl _ _))
  (Some _ (Refl (Side) x)))

(def-fns _ $ (many eq-acfg : (many (ACfg) x) (many (ACfg) y) -> (many (Maybe (Eq (ACfg) x y)) r))
  (let-match many x (MkA q1 l1 h1 r1))
  (let-match many y (MkA q2 l2 h2 r2))
  (let-match many (eq-nat q1 q2) (Some _ e1) ((None _) (None _)))
  (let-match many (eq-side l1 l2) (Some _ e2) ((None _) (None _)))
  (let-match many (eq-bit h1 h2) (Some _ e3) ((None _) (None _)))
  (let-match many (eq-side r1 r2) (Some _ e4) ((None _) (None _)))
  (let-match many e1 (Refl _ _))
  (let-match many e2 (Refl _ _))
  (let-match many e3 (Refl _ _))
  (let-match many e4 (Refl _ _))
  (Some _ (Refl (ACfg) x)))

(def-fns _ $ (many find : (many (ACfg) a) (subterm many (List (ACfg)) S) -> (many (Res (Mem (ACfg) a S)) r))
  (let-match many S (Cons _ b rest) ((Nil _) (RFail _)))
  (match many (eq-acfg a b) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (ACfg) a rest)))
    ((None _)
      (let-match many (notail $ find a rest) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (ACfg) a b rest mm)))))

(def-fns _ $ (many shorter : (many (List (Bool)) xs) (subterm many (Nat) n) -> (many (Bool) b))
  (let-match many n (Succ n1) ((Zero) (BFalse)))
  (match many xs _
    ((Nil _) (BTrue))
    ((Cons _ _ rest) (tail $ shorter rest n1))))

(def-adts
  ((DropR : ((List (Bool)) xs) -> Type)
    enum
    (many DLOk : (erased (List (Bool)) xs) (many (Bool) x) (many (List (Bool)) ys) (erased (DropLast xs x ys) p) -> (DropR xs))
    (many DLNone : (erased (List (Bool)) xs) -> (DropR xs))))

(def-fns _ $ (many drop-last : (subterm many (List (Bool)) xs) -> (many (DropR xs) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (DLNone xs)))
  (match many (notail $ drop-last rest) _
    ((DLOk _ x ys p) (DLOk xs x (Cons (Bool) b ys) (DL2 rest ys x b p)))
    ((DLNone _) (let-match many rest (Nil _) ((Cons _ _ _) (DLNone xs))) (DLOk xs b (Nil (Bool)) (DL1 b)))))

(def-fns _ $ (many flag-after : (many (Flag) f) (many (Bool) x) -> (many (Flag) g) (erased (FlagAfter f x g) p))
  (match many f _
    ((FZ) (match many x _ ((BFalse) (values (FZ) (FAZ))) ((BTrue) (values (FT) (FAT f x)))))
    ((FT) (values (FT) (FAT f x)))))

(def-fns _ $ (many apush : (many (Nat) rad) (many (Side) s) (many (Bool) w) -> (many (Side) s2) (erased (APush s w s2) p))
  (let-match many s (MkSide seg f))
  (match many (shorter seg rad) _
    ((BTrue) (values (MkSide (Cons (Bool) w seg) f) (PKeep seg f w)))
    ((BFalse)
      (let-match many (drop-last (Cons (Bool) w seg)) (DLOk _ x seg2 dl) ((DLNone _) (values (MkSide (Cons (Bool) w seg) f) (PKeep seg f w))))
      (let ((many f2) (erased fa)) (flag-after f x))
      (values (MkSide seg2 f2) (PDrop seg seg2 f f2 w x dl fa)))))

(def-fns _ $ (many place : (many (Mv) d) (many (Nat) q) (many (Side) p) (many (Bool) b) (many (Side) o) ->
    (many (ACfg) a) (erased (Place d q p b o a) pl))
  (match many d _
    ((DL) (values (MkA q p b o) (PlL q p o b)))
    ((DR) (values (MkA q o b p) (PlR q p o b)))))

(def-fns _ $ (many all-pop : (many (List (ACfg)) S) (many (Mv) d) (many (Nat) q) (many (Side) p) (many (Side) o) ->
    (many (Res (AllPop S d q p o)) r))
  (let-match many p (MkSide seg f))
  (match many seg _
    ((Nil _)
      (match many f _
        ((FZ)
          (let ((many a) (erased pl)) (place d q p (BFalse) o))
          (let-match many (find a S) (ROk _ mm) ((RFail _) (RFail _)))
          (ROk _ (AllZ S d q o a pl mm)))
        ((FT)
          (let ((many a0) (erased pl0)) (place d q p (BFalse) o))
          (let-match many (find a0 S) (ROk _ mm0) ((RFail _) (RFail _)))
          (let ((many a1) (erased pl1)) (place d q p (BTrue) o))
          (let-match many (find a1 S) (ROk _ mm1) ((RFail _) (RFail _)))
          (ROk _ (AllT S d q o a0 a1 pl0 mm0 pl1 mm1)))))
    ((Cons _ b seg1)
      (let ((many a) (erased pl)) (place d q (MkSide seg1 f) b o))
      (let-match many (find a S) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (AllC S d q o a seg1 f b pl mm)))))

(def-fns _ $ (many aok : (many (Nat) rad) (many (List (Tr)) m) (many (List (ACfg)) S) (many (ACfg) a) -> (many (Res (AOK m S a)) r))
  (let-match many a (MkA q l h r))
  (let-match many (look m q h) (LFound _ _ _ t lk) ((LMiss _ _ _) (RFail _)))
  (let-match many t (Mov w d q2) ((Hlt) (RFail _)))
  (match many d _
    ((DL)
      (let ((many r2) (erased ap)) (apush rad r w))
      (let-match many (all-pop S (DL) q2 l r2) (ROk _ al) ((RFail _) (RFail _)))
      (ROk _ (AOKL m S q q2 l r r2 h w lk ap al)))
    ((DR)
      (let ((many l2) (erased ap)) (apush rad l w))
      (let-match many (all-pop S (DR) q2 r l2) (ROk _ al) ((RFail _) (RFail _)))
      (ROk _ (AOKR m S q q2 l r l2 h w lk ap al)))))

(def-fns _ $ (many closed : (many (Nat) rad) (many (List (Tr)) m) (many (List (ACfg)) S) (subterm many (List (ACfg)) T) ->
    (many (Res (Closed m S T)) r))
  (let-match many T (Cons _ a rest) ((Nil _) (ROk _ (CNil m S))))
  (let-match many (aok rad m S a) (ROk _ ok) ((RFail _) (RFail _)))
  (let-match many (notail $ closed rad m S rest) (ROk _ cl) ((RFail _) (RFail _)))
  (ROk _ (CCons m S rest a ok cl)))

(def-fns _ $ (many pops : (many (Mv) d) (many (Nat) q) (many (Side) p) (many (Side) o) -> (many (List (ACfg)) as))
  (let-match many p (MkSide seg f))
  (match many seg _
    ((Nil _)
      (let ((many a0) (erased _)) (place d q p (BFalse) o))
      (match many f _
        ((FZ) (Cons _ a0 (Nil (ACfg))))
        ((FT)
          (let ((many a1) (erased _)) (place d q p (BTrue) o))
          (Cons _ a0 $ Cons _ a1 $ Nil (ACfg)))))
    ((Cons _ b seg1)
      (let ((many a) (erased _)) (place d q (MkSide seg1 f) b o))
      (Cons _ a (Nil (ACfg))))))

(def-fns _ $ (many succs : (many (Nat) rad) (many (List (Tr)) m) (many (ACfg) a) -> (many (Maybe (List (ACfg))) r))
  (let-match many a (MkA q l h r))
  (let-match many (look m q h) (LFound _ _ _ t _) ((LMiss _ _ _) (None _)))
  (let-match many t (Mov w d q2) ((Hlt) (None _)))
  (match many d _
    ((DL) (let ((many r2) (erased _)) (apush rad r w)) (Some _ (pops (DL) q2 l r2)))
    ((DR) (let ((many l2) (erased _)) (apush rad l w)) (Some _ (pops (DR) q2 r l2)))))

(def-fns _ $ (many app : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) zs))
  (match many xs _
    ((Nil _) ys)
    ((Cons _ x rest) (Cons A x (notail $ app A rest ys)))))

(def-fns _ $ (many explore : (many (Nat) rad) (many (List (Tr)) m) (subterm many (Nat) fuel)
    (many (List (ACfg)) todo) (many (List (ACfg)) seen) -> (many (Maybe (List (ACfg))) r))
  (let-match many fuel (Succ f) ((Zero) (None _)))
  (let-match many todo (Cons _ a rest) ((Nil _) (Some _ seen)))
  (match many (find a seen) _
    ((ROk _ _) (tail $ explore rad m f rest seen))
    ((RFail _)
      (let-match many (succs rad m a) (Some _ ns) ((None _) (None _)))
      (tail $ explore rad m f (app _ ns rest) (Cons _ a seen)))))

(def-adts
  ((Good : ((Nat) k) ((List (Tr)) m) -> Type)
    enum
    (many GHalt : (erased (Nat) k s) (erased (List (Tr)) m)
       (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) (erased (Lt s (Succ k)) lt) -> (Good k m))
    (many GNever : (erased (Nat) k) (erased (List (Tr)) m) (erased (List (ACfg)) S) (erased (Closed m S S) cl)
       (erased (ACfg) a) (erased (Mem (ACfg) a S) mm) (erased (GCfg a (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)))) g)
       -> (Good k m))))

(def-fns _ $ (many decide : (many (Nat) rad) (many (Nat) simfuel) (many (Nat) expfuel) (many (Nat) k) (many (List (Tr)) m) ->
    (many (Res (Good k m)) r))
  (match many (sim m simfuel (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) _
    ((SHalt _ _ s h)
      (let-match many (lt-dec s (Succ k)) (Yes _ _ _ _ lt) ((No _ _ _ _ _) (RFail _)))
      (ROk _ (GHalt k s m h lt)))
    ((SRun _ _)
      (let ((many a0)) (MkA (Zero) (MkSide (Nil (Bool)) (FZ)) (BFalse) (MkSide (Nil (Bool)) (FZ))))
      (let-match many (explore rad m expfuel (Cons _ a0 (Nil (ACfg))) (Nil (ACfg))) (Some _ S) ((None _) (RFail _)))
      (let-match many (closed rad m S S) (ROk _ cl) ((RFail _) (RFail _)))
      (let-match many (find a0 S) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (GNever k m S cl a0 mm
        (MkGCfg (Zero) (MkSide (Nil (Bool)) (FZ)) (MkSide (Nil (Bool)) (FZ)) (Nil (Bool)) (Nil (Bool)) (BFalse)
          (GZ (Nil (Bool)) (AZNil)) (GZ (Nil (Bool)) (AZNil))))))))

(def-adts
  ((Slots2 : ((Nat) n) ((Nat) j) ((List (Tr)) m) -> Type)
    enum
    (many FlZ : (erased (Nat) n) -> (Slots2 n (Zero) (Nil (Tr))))
    (many FlS : (erased (Nat) n j) (erased (Tr) t) (erased (List (Tr)) rest) (erased (TrOK n t) ok) (erased (Slots2 n j rest) p)
       -> (Slots2 n (Succ j) (Cons (Tr) t rest)))))

(def-fns _ $ (erased rows-flat : (erased (Nat) n k j) (erased (List (Tr)) m) (subterm erased (Rows n k m) rw) (erased (Double k j) dj) ->
    (erased (Slots2 n j m) fl))
  (match erased rw _
    ((RowsZ _) (let-match erased dj (D0)) (FlZ n))
    ((RowsS _ k1 t0 t1 rest o0 o1 rw1)
      (let-match erased dj (DS _ j1 dj1))
      (FlS n (Succ j1) t0 (Cons (Tr) t1 rest) o0 (FlS n j1 t1 rest o1 (rows-flat n k1 j1 rest rw1 dj1))))))

(def-adts
  ((RA : ((List (Tr)) acc) ((List (Tr)) rest) ((List (Tr)) m) -> Type)
    enum
    (many RA0 : (erased (List (Tr)) m) -> (RA (Nil (Tr)) m m))
    (many RA1 : (erased (List (Tr)) acc rest m) (erased (Tr) t) (erased (RA acc (Cons (Tr) t rest) m) p)
       -> (RA (Cons (Tr) t acc) rest m))))

(def-fns _ $ (many rev-onto : (subterm many (List (Tr)) acc) (many (List (Tr)) rest) -> (many (List (Tr)) m) (erased (RA acc rest m) p))
  (let-match many acc (Cons _ t acc1) ((Nil _) (values rest (RA0 rest))))
  (let ((many m) (erased p)) (tail $ rev-onto acc1 (Cons (Tr) t rest)))
  (values m (RA1 acc1 rest m t p)))

(def-fns _ $ (erased ra-fn : (erased (List (Tr)) acc rest m m2) (subterm erased (RA acc rest m) p) (erased (RA acc rest m2) p2) ->
    (erased (Eq (List (Tr)) m m2) e))
  (match erased p _
    ((RA0 _) (let-match erased p2 (RA0 _)) (Refl (List (Tr)) m))
    ((RA1 acc1 _ _ t p1) (let-match erased p2 (RA1 _ _ _ _ p21)) (ra-fn acc1 (Cons (Tr) t rest) m m2 p1 p21))))

(def-adts
  ((Cov : ((Nat) k) ((List (Tr)) O) ((List (Tr)) acc) ((Nat) j) -> Type)
    enum
    (many CovDone : (erased (Nat) k) (erased (List (Tr)) O acc m) (erased (RA acc (Nil (Tr)) m) ra) (erased (Good k m) g)
       -> (Cov k O acc (Zero)))
    (many CovStep : (erased (Nat) k j) (erased (List (Tr)) O acc) (erased (CovAll k O acc j O) ca) -> (Cov k O acc (Succ j))))
  ((CovAll : ((Nat) k) ((List (Tr)) O) ((List (Tr)) acc) ((Nat) j) ((List (Tr)) os) -> Type)
    enum
    (many CANil : (erased (Nat) k j) (erased (List (Tr)) O acc) -> (CovAll k O acc j (Nil (Tr))))
    (many CACons : (erased (Nat) k j) (erased (List (Tr)) O acc os) (erased (Tr) t)
       (erased (Cov k O (Cons (Tr) t acc) j) c) (erased (CovAll k O acc j os) rest) -> (CovAll k O acc j (Cons (Tr) t os)))))

(def-fns _
  ((many cov : (subterm many (Nat) j) (subterm many (List (Tr)) os) (many (Nat) rad simf expf k) (many (List (Tr)) O acc) ->
       (many (Res (Cov k O acc j)) r))
    (match many j _
      ((Zero)
        (let ((many m) (erased ra)) (rev-onto acc (Nil (Tr))))
        (let-match many (decide rad simf expf k m) (ROk _ g) ((RFail _) (RFail _)))
        (ROk _ (CovDone k O acc m ra g)))
      ((Succ j1)
        (let-match many (notail $ cov-all j1 O rad simf expf k O acc) (ROk _ ca) ((RFail _) (RFail _)))
        (ROk _ (CovStep k j1 O acc ca)))))
  ((many cov-all : (subterm many (Nat) j) (subterm many (List (Tr)) os) (many (Nat) rad simf expf k) (many (List (Tr)) O acc) ->
       (many (Res (CovAll k O acc j os)) r))
    (let-match many os (Cons _ t rest) ((Nil _) (ROk _ (CANil k j O acc))))
    (let-match many (notail $ cov j rest rad simf expf k O (Cons (Tr) t acc)) (ROk _ c) ((RFail _) (RFail _)))
    (let-match many (notail $ cov-all j rest rad simf expf k O acc) (ROk _ ca) ((RFail _) (RFail _)))
    (ROk _ (CACons k j O acc rest t c ca))))

(def-fns _
  ((erased cov-good : (erased (Nat) n k j) (erased (List (Nat)) xs) (erased (List (Tr)) O acc rest m)
       (subterm erased (Cov k O acc j) cv) (erased (Slots2 n j rest) fl) (erased (Range n xs) rg) (erased (Opts xs O) op)
       (erased (RA acc rest m) ra) -> (erased (Good k m) g))
    (match erased cv _
      ((CovDone _ _ _ m2 ra2 g2)
        (let-match erased fl (FlZ _))
        (let-match erased (ra-fn acc rest m m2 ra ra2) (Refl _ _))
        g2)
      ((CovStep _ j1 _ _ ca)
        (let-match erased fl (FlS _ _ t rest1 ok fl1))
        (cov-pick n k j1 xs O acc rest1 m O t ca (tr-mem n xs O t ok rg op) fl1 rg op ra))))
  ((erased cov-pick : (erased (Nat) n k j) (erased (List (Nat)) xs) (erased (List (Tr)) O acc rest m os) (erased (Tr) t)
       (subterm erased (CovAll k O acc j os) ca) (erased (Mem (Tr) t os) mm) (erased (Slots2 n j rest) fl) (erased (Range n xs) rg)
       (erased (Opts xs O) op) (erased (RA acc (Cons (Tr) t rest) m) ra) -> (erased (Good k m) g))
    (match erased mm _
      ((MemHere _ _ os1)
        (let-match erased ca (CACons _ _ _ _ _ _ c _))
        (cov-good n k j xs O (Cons (Tr) t acc) rest m c fl rg op (RA1 acc rest m t ra)))
      ((MemThere _ _ y os1 mm1)
        (let-match erased ca (CACons _ _ _ _ _ _ _ ca1))
        (cov-pick n k j xs O acc rest m os1 t ca1 mm1 fl rg op ra)))))

(def-fns _ $ (erased bound-of : (erased (Nat) n k j) (erased (List (Nat)) xs) (erased (List (Tr)) O)
    (erased (Cov k O (Nil (Tr)) j) cv) (erased (Double n j) dj) (erased (Range n xs) rg) (erased (Opts xs O) op)
    (erased (List (Tr)) m) (erased (Rows n n m) w) (erased (Nat) s)
    (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) -> (erased (Lt s (Succ k)) p))
  (let ((erased g)) (cov-good n k j xs O (Nil (Tr)) m m cv (rows-flat n n j m w dj) rg op (RA0 m)))
  (match erased g _
    ((GHalt _ s2 _ h2 lt) (let-match erased (halts-fn m _ s s2 h h2) (Refl _ _)) lt)
    (absurd (GNever _ _ S cl a mm ga) (never m S cl a mm _ ga s h))))

(unary 2)

(let ((many xs) (erased rg)) (range 2))

(let ((many O) (erased op)) (opts xs))

(let ((many j) (erased dj)) (double 2))

(let ((many res)) (cov j O 1 100 1000 6 O (Nil (Tr))))

(comptime-match many res (ROk _ cv))

(let ((many champ)) (Cons _ (Mov (BTrue) (DR) 1) $ Cons _ (Mov (BTrue) (DL) 1) $ Cons _ (Mov (BTrue) (DL) 0) $ Cons _ (Hlt) $ Nil (Tr)))

(let ((many cs)) (sim champ 100 (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))))

(comptime-match many cs (SHalt _ _ s6 ch))

(comptime-match many (nat-eq s6 6) (Equal _ _ _))

(let ((erased l12)) (prove-literal-lt 1 2))

(let ((erased l02)) (prove-literal-lt 0 2))

(let ((erased cw)) (RowsS 2 (Succ (Zero)) (Mov (BTrue) (DR) 1) (Mov (BTrue) (DL) 1) _ (OKGo 2 1 (BTrue) (DR) l12) (OKGo 2 1 (BTrue) (DL) l12)
                     (RowsS 2 (Zero) (Mov (BTrue) (DL) 0) (Hlt) (Nil (Tr)) (OKGo 2 0 (BTrue) (DL) l02) (OKHalt 2) (RowsZ 2))))

(def-fns _ $ (erased bound : (erased (List (Tr)) m) (erased (Rows 2 2 m) w) (erased (Nat) s)
    (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) -> (erased (Lt s (Succ 6)) p))
  (bound-of 2 6 j xs O cv dj rg op m w s h))

(goal erased (BBIs 2 6))

(qed (MkBB 2 6 champ cw ch (level-of bound) bound))
