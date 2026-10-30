; From the co-closure KC on partial traces of kempe.sl to one on complete traces stated after chromogram.v, and from that
; to Kempe_coclosure itself, for every Kempe-closed set.

(def-fns _ $ (erased third-fn : (erased (Col) a b c d) (erased (Third a b c) p) (erased (Third a b d) q) -> (erased (Eq (Col) c d) e))
  (match erased p _
    ((T123) (let-match erased q (T123)) (Refl _ c))
    ((T132) (let-match erased q (T132)) (Refl _ c))
    ((T213) (let-match erased q (T213)) (Refl _ c))
    ((T231) (let-match erased q (T231)) (Refl _ c))
    ((T312) (let-match erased q (T312)) (Refl _ c))
    ((T321) (let-match erased q (T321)) (Refl _ c))))

(def-fns _ $ (erased third-12 : (erased (Col) a b c) (erased (Third a b c) p) -> (erased (Third b a c) q))
  (match erased p _ ((T123) (T213)) ((T132) (T312)) ((T213) (T123)) ((T231) (T321)) ((T312) (T132)) ((T321) (T231))))

(def-fns _ $ (erased third-23 : (erased (Col) a b c) (erased (Third a b c) p) -> (erased (Third a c b) q))
  (match erased p _ ((T123) (T132)) ((T132) (T123)) ((T213) (T231)) ((T231) (T213)) ((T312) (T321)) ((T321) (T312))))

(def-fns _ $ (erased perm-third : (erased (Col) p1 p2 p3) (erased (IsPerm (MkPerm p1 p2 p3)) ip) -> (erased (Third p1 p2 p3) t))
  (match erased ip _ ((IP123) (T123)) ((IP132) (T132)) ((IP213) (T213)) ((IP231) (T231)) ((IP312) (T312)) ((IP321) (T321))))

(def-fns _ $ (erased third-perm : (erased (Perm) g) (erased (Col) a b c a2 b2 c2) (erased (IsPerm g) ip) (erased (Third a b c) t)
    (erased (PermC g a a2) pa) (erased (PermC g b b2) pb) (erased (PermC g c c2) pc) -> (erased (Third a2 b2 c2) r))
  (let-match erased g (MkPerm p1 p2 p3))
  (let ((erased u)) (perm-third p1 p2 p3 ip))
  (match erased t _
    ((T123) (let-match erased pa (PC1 _ _ _)) (let-match erased pb (PC2 _ _ _)) (let-match erased pc (PC3 _ _ _)) u)
    ((T132) (let-match erased pa (PC1 _ _ _)) (let-match erased pb (PC3 _ _ _)) (let-match erased pc (PC2 _ _ _)) (third-23 p1 p2 p3 u))
    ((T213) (let-match erased pa (PC2 _ _ _)) (let-match erased pb (PC1 _ _ _)) (let-match erased pc (PC3 _ _ _)) (third-12 p1 p2 p3 u))
    ((T231) (let-match erased pa (PC2 _ _ _)) (let-match erased pb (PC3 _ _ _)) (let-match erased pc (PC1 _ _ _))
      (third-23 p2 p1 p3 (third-12 p1 p2 p3 u)))
    ((T312) (let-match erased pa (PC3 _ _ _)) (let-match erased pb (PC1 _ _ _)) (let-match erased pc (PC2 _ _ _))
      (third-12 p1 p3 p2 (third-23 p1 p2 p3 u)))
    ((T321) (let-match erased pa (PC3 _ _ _)) (let-match erased pb (PC2 _ _ _)) (let-match erased pc (PC1 _ _ _))
      (third-12 p2 p3 p1 (third-23 p2 p1 p3 (third-12 p1 p2 p3 u))))))

(def-fns _ $ (erased addc-fn : (erased (Col) a b c d) (erased (AddK a b c) p) (erased (AddK a b d) q) -> (erased (Eq (Col) c d) e))
  (match erased p _
    ((AZL _) (match erased q _ ((AZL _) (Refl _ c)) ((AZR _) (Refl _ c)) ((ASame _) (Refl _ c)) (absurd (AThird _ _ _ t) t)))
    ((AZR _) (match erased q _ ((AZL _) (Refl _ c)) ((AZR _) (Refl _ c)) ((ASame _) (Refl _ c)) (absurd (AThird _ _ _ t) t)))
    ((ASame _) (match erased q _ ((AZL _) (Refl _ c)) ((AZR _) (Refl _ c)) ((ASame _) (Refl _ c)) (absurd (AThird _ _ _ t) t)))
    ((AThird _ _ _ t)
      (match erased q _ (absurd (AZL _) t) (absurd (AZR _) t) (absurd (ASame _) t) ((AThird _ _ _ u) (third-fn a b c d t u))))))

(def-fns _ $ (erased addc-total : (erased (Col) a b) -> (erased (Col) c) (erased (AddK a b c) p))
  (match erased a _
    ((C0) (values b (AZL b)))
    ((C1) (match erased b _ ((C0) (values a (AZR a))) ((C1) (values (C0) (ASame a)))
      ((C2) (values (C3) (AThird a b (C3) (T123)))) ((C3) (values (C2) (AThird a b (C2) (T132))))))
    ((C2) (match erased b _ ((C0) (values a (AZR a))) ((C1) (values (C3) (AThird a b (C3) (T213))))
      ((C2) (values (C0) (ASame a))) ((C3) (values (C1) (AThird a b (C1) (T231))))))
    ((C3) (match erased b _ ((C0) (values a (AZR a))) ((C1) (values (C2) (AThird a b (C2) (T312))))
      ((C2) (values (C1) (AThird a b (C1) (T321)))) ((C3) (values (C0) (ASame a)))))))

; A colour permutation is a group automorphism.
(def-fns _ $ (erased perm-add : (erased (Perm) g) (erased (Col) a b c a2 b2 c2) (erased (IsPerm g) ip) (erased (PermC g a a2) pa)
    (erased (PermC g b b2) pb) (erased (AddK a b c) p) (erased (AddK a2 b2 c2) q) -> (erased (PermC g c c2) r))
  (match erased p _
    ((AZL _) (let-match erased pa (PC0 _)) (let-match erased (addc-fn a2 b2 c2 b2 q (AZL b2)) (Refl _ _)) pb)
    ((AZR _) (let-match erased pb (PC0 _)) (let-match erased (addc-fn a2 b2 c2 a2 q (AZR a2)) (Refl _ _)) pa)
    ((ASame _)
      (let-match erased (permc-fn g a a2 b2 pa pb) (Refl _ _))
      (let-match erased (addc-fn a2 b2 c2 (C0) q (ASame a2)) (Refl _ _))
      (PC0 g))
    ((AThird _ _ _ t)
      (let ((erased c3) (erased pc)) (permc-total g c))
      (let-match erased (addc-fn a2 b2 c2 c3 q (AThird a2 b2 c3 (third-perm g a b c a2 b2 c3 ip t pa pb pc))) (Refl _ _))
      pc)))

(def-fns _ $ (erased ctr-exists : (erased (Col) s) (subterm erased (List (Col)) et) -> (erased (List (Col)) ct) (erased (Ctr s et ct) c))
  (let-match erased et (Cons _ e et1) ((Nil _) (values (Cons _ s (Nil _)) (CtrNil s))))
  (let ((erased s2) (erased a)) (addc-total s e))
  (let ((erased ct) (erased c)) (ctr-exists s2 et1))
  (values (Cons _ e ct) (CtrCons s e s2 et1 ct a c)))

(def-fns _ $ (erased ctr-fn : (erased (Col) s) (erased (List (Col)) et ct ct2) (subterm erased (Ctr s et ct) p) (erased (Ctr s et ct2) q) ->
    (erased (Eq (List (Col)) ct ct2) e))
  (match erased p _
    ((CtrNil _) (let-match erased q (CtrNil _)) (Refl _ ct))
    ((CtrCons _ e s2 et1 ct1 a p1)
      (let-match erased q (CtrCons _ _ s3 _ ct3 a2 q1))
      (let-match erased (addc-fn s e s2 s3 a a2) (Refl _ _))
      (let-match erased (ctr-fn s2 et1 ct1 ct3 p1 q1) (Refl _ _))
      (Refl _ ct))))

; After permt and ctrace of color.v: permuting a trace permutes its completion.
(def-fns _ $ (erased perm-ctr : (erased (Perm) g) (erased (IsPerm g) ip) (erased (Col) s s2) (erased (List (Col)) et et2 ct ct2)
    (subterm erased (PermT g et et2) pt) (erased (PermC g s s2) ps) (erased (Ctr s et ct) c) (erased (Ctr s2 et2 ct2) c2) -> (erased (PermT g ct ct2) r))
  (match erased pt _
    ((PTNil _) (let-match erased c (CtrNil _)) (let-match erased c2 (CtrNil _)) (PTCons g s s2 (Nil _) (Nil _) ps (PTNil g)))
    ((PTCons _ e e2 et1 et3 pe pt1)
      (let-match erased c (CtrCons _ _ t _ ct1 a c1))
      (let-match erased c2 (CtrCons _ _ t2 _ ct3 a2 c3))
      (PTCons g e e2 ct1 ct3 pe (perm-ctr g ip t t2 et1 et3 ct1 ct3 pt1 (perm-add g s e t s2 e2 t2 ip ps pe a a2) c1 c3)))))

; A colour as two bits, C1 = (F, T), C2 = (T, F) and C3 = (T, T), so that addition is bitwise.
(def-adts $ (CB : ((Col) c) ((Bool) x) ((Bool) y) -> Type)
  enum
  (many CB0 : -> (CB (C0) (BFalse) (BFalse)))
  (many CB1 : -> (CB (C1) (BFalse) (BTrue)))
  (many CB2 : -> (CB (C2) (BTrue) (BFalse)))
  (many CB3 : -> (CB (C3) (BTrue) (BTrue))))

(def-adts $ (Xor : ((Bool) a) ((Bool) b) ((Bool) c) -> Type)
  enum
  (many XFF : -> (Xor (BFalse) (BFalse) (BFalse)))
  (many XFT : -> (Xor (BFalse) (BTrue) (BTrue)))
  (many XTF : -> (Xor (BTrue) (BFalse) (BTrue)))
  (many XTT : -> (Xor (BTrue) (BTrue) (BFalse))))

(def-fns _ $ (erased cb-exists : (erased (Col) c) -> (erased (Bool) x y) (erased (CB c x y) p))
  (match erased c _ ((C0) (values (BFalse) (BFalse) (CB0))) ((C1) (values (BFalse) (BTrue) (CB1))) ((C2) (values (BTrue) (BFalse) (CB2))) ((C3) (values (BTrue) (BTrue) (CB3)))))

(def-fns _ $ (erased cb-fn : (erased (Col) c) (erased (Bool) x y x2 y2) (erased (CB c x y) p) (erased (CB c x2 y2) q) ->
    (erased (Eq (Bool) x x2) e) (erased (Eq (Bool) y y2) f))
  (match erased p _
    ((CB0) (let-match erased q (CB0)) (values (Refl _ x) (Refl _ y)))
    ((CB1) (let-match erased q (CB1)) (values (Refl _ x) (Refl _ y)))
    ((CB2) (let-match erased q (CB2)) (values (Refl _ x) (Refl _ y)))
    ((CB3) (let-match erased q (CB3)) (values (Refl _ x) (Refl _ y)))))

(def-fns _ $ (erased xor-fl : (erased (Bool) a) -> (erased (Xor (BFalse) a a) r)) (match erased a _ ((BTrue) (XFT)) ((BFalse) (XFF))))
(def-fns _ $ (erased xor-fr : (erased (Bool) a) -> (erased (Xor a (BFalse) a) r)) (match erased a _ ((BTrue) (XTF)) ((BFalse) (XFF))))
(def-fns _ $ (erased xor-self : (erased (Bool) a) -> (erased (Xor a a (BFalse)) r)) (match erased a _ ((BTrue) (XTT)) ((BFalse) (XFF))))

(def-fns _ $ (erased xor-t : (erased (Bool) a b) (erased (Xor a (BTrue) b) p) -> (erased (Not a b) n))
  (match erased p _ ((XFT) (NotF)) ((XTT) (NotT))))

(def-fns _ $ (erased xor-f : (erased (Bool) a b) (erased (Xor a (BFalse) b) p) -> (erased (Eq (Bool) b a) e))
  (match erased p _ ((XFF) (Refl _ b)) ((XTF) (Refl _ b))))

(def-fns _ $ (erased not-not : (erased (Bool) a b c) (erased (Not a b) p) (erased (Not b c) q) -> (erased (Eq (Bool) c a) e))
  (match erased p _ ((NotT) (let-match erased q (NotF)) (Refl _ c)) ((NotF) (let-match erased q (NotT)) (Refl _ c))))

(def-fns _ $ (erased not-sym : (erased (Bool) a b) (erased (Not a b) p) -> (erased (Not b a) q))
  (match erased p _ ((NotT) (NotF)) ((NotF) (NotT))))

(def-fns _ $ (erased xor-nn : (erased (Bool) b z y b2 y2) (erased (Xor b z y) p) (erased (Not b b2) nb) (erased (Not y y2) ny) -> (erased (Xor b2 z y2) r))
  (match erased p _
    ((XFF) (let-match erased nb (NotF)) (let-match erased ny (NotF)) (XTF))
    ((XFT) (let-match erased nb (NotF)) (let-match erased ny (NotT)) (XTT))
    ((XTF) (let-match erased nb (NotT)) (let-match erased ny (NotT)) (XFF))
    ((XTT) (let-match erased nb (NotT)) (let-match erased ny (NotF)) (XFT))))

(def-fns _ $ (erased xor-zn : (erased (Bool) b z y z2 y2) (erased (Xor b z y) p) (erased (Not z z2) nz) (erased (Not y y2) ny) -> (erased (Xor b z2 y2) r))
  (match erased p _
    ((XFF) (let-match erased nz (NotF)) (let-match erased ny (NotF)) (XFT))
    ((XFT) (let-match erased nz (NotT)) (let-match erased ny (NotT)) (XFF))
    ((XTF) (let-match erased nz (NotF)) (let-match erased ny (NotT)) (XTT))
    ((XTT) (let-match erased nz (NotT)) (let-match erased ny (NotF)) (XTF))))

(def-fns _ $ (erased xor-bz : (erased (Bool) b z y b2 z2) (erased (Xor b z y) p) (erased (Not b b2) nb) (erased (Not z z2) nz) -> (erased (Xor b2 z2 y) r))
  (match erased p _
    ((XFF) (let-match erased nb (NotF)) (let-match erased nz (NotF)) (XTT))
    ((XFT) (let-match erased nb (NotF)) (let-match erased nz (NotT)) (XTF))
    ((XTF) (let-match erased nb (NotT)) (let-match erased nz (NotF)) (XFT))
    ((XTT) (let-match erased nb (NotT)) (let-match erased nz (NotT)) (XFF))))

(def-fns _ $ (erased addc-bits : (erased (Col) s e s2) (erased (Bool) x y xe ye) (erased (AddK s e s2) a) (erased (CB s x y) p) (erased (CB e xe ye) q)
    -> (erased (Bool) x2 y2) (erased (Xor x xe x2) r1) (erased (Xor y ye y2) r2) (erased (CB s2 x2 y2) r3))
  (match erased a _
    ((AZL _) (let-match erased p (CB0)) (values xe ye (xor-fl xe) (xor-fl ye) q))
    ((AZR _) (let-match erased q (CB0)) (values x y (xor-fr x) (xor-fr y) p))
    ((ASame _)
      (let ((erased ex) (erased ey)) (cb-fn s x y xe ye p q))
      (let-match erased ex (Refl _ _))
      (let-match erased ey (Refl _ _))
      (values (BFalse) (BFalse) (xor-self x) (xor-self y) (CB0)))
    ((AThird _ _ _ t)
      (match erased t _
        ((T123) (let-match erased p (CB1)) (let-match erased q (CB2)) (values (BTrue) (BTrue) (XFT) (XTF) (CB3)))
        ((T132) (let-match erased p (CB1)) (let-match erased q (CB3)) (values (BTrue) (BFalse) (XFT) (XTT) (CB2)))
        ((T213) (let-match erased p (CB2)) (let-match erased q (CB1)) (values (BTrue) (BTrue) (XTF) (XFT) (CB3)))
        ((T231) (let-match erased p (CB2)) (let-match erased q (CB3)) (values (BFalse) (BTrue) (XTT) (XFT) (CB1)))
        ((T312) (let-match erased p (CB3)) (let-match erased q (CB1)) (values (BTrue) (BFalse) (XTF) (XTT) (CB2)))
        ((T321) (let-match erased p (CB3)) (let-match erased q (CB2)) (values (BFalse) (BTrue) (XTT) (XTF) (CB1)))))))

; bs has d entries, x is the parity of d and z that of the Color3 pushes in bs. Along a matching, the bits (x, y) of the trace sum
; satisfy y = b xor z, b the parity of gram_balanced.
(def-adts $ (SInv : ((Bstack) bs) ((Nat) d) ((Bool) x) ((Bool) z) -> Type)
  enum
  (many SINil : -> (SInv (BS0) (Zero) (BFalse) (BFalse)))
  (many SI0 : (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) x x2 z) (erased (SInv bs d x z) p) (erased (Not x x2) n)
      -> (SInv (BP0 bs) (Succ d) x2 z))
  (many SI1 : (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) x x2 z z2) (erased (SInv bs d x z) p) (erased (Not x x2) n) (erased (Not z z2) m)
      -> (SInv (BP1 bs) (Succ d) x2 z2)))

(def-fns _ $ (erased inv-step : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (Nat) d d2) (erased (Bool) b b2 x y z xe ye x2 y2)
    (erased (Sym s bs e bs2) sy) (erased (GStep d b s d2 b2) st) (erased (CB e xe ye) ce) (erased (Xor x xe x2) rx) (erased (Xor y ye y2) ry)
    (erased (SInv bs d x z) si) (erased (Xor b z y) xb) -> (erased (Bool) z2) (erased (SInv bs2 d2 x2 z2) si2) (erased (Xor b2 z2 y2) xb2))
  (match erased sy _
    ((SSkip _)
      (let-match erased ce (CB1))
      (let-match erased st (GStSkip _ _ _ nb))
      (let-match erased (xor-f x x2 rx) (Refl _ _))
      (values z si (xor-nn b z y b2 y2 xb nb (xor-t y y2 ry))))
    ((SPush2 _)
      (let-match erased ce (CB2))
      (let-match erased st (GStPush _ _))
      (let-match erased (xor-f y y2 ry) (Refl _ _))
      (values z (SI0 bs d x x2 z si (xor-t x x2 rx)) xb))
    ((SPush3 _)
      (let-match erased ce (CB3))
      (let-match erased st (GStPush _ _))
      (let ((erased z2) (erased nz)) (not-exists z))
      (values z2 (SI1 bs d x x2 z z2 si (xor-t x x2 rx) nz) (xor-zn b z y z2 y2 xb nz (xor-t y y2 ry))))
    ((SPop02 _)
      (let-match erased ce (CB2))
      (let-match erased st (GStPop0 _ _))
      (let-match erased si (SI0 _ _ x1 _ _ si1 n1))
      (let-match erased (not-not x1 x x2 n1 (xor-t x x2 rx)) (Refl _ _))
      (let-match erased (xor-f y y2 ry) (Refl _ _))
      (values z si1 xb))
    ((SPop03 _)
      (let-match erased ce (CB3))
      (let-match erased st (GStPop0 _ _))
      (let-match erased si (SI1 _ _ x1 _ z1 _ si1 n1 m1))
      (let-match erased (not-not x1 x x2 n1 (xor-t x x2 rx)) (Refl _ _))
      (values z1 si1 (xor-zn b z y z1 y2 xb (not-sym z1 z m1) (xor-t y y2 ry))))
    ((SPop13 _)
      (let-match erased ce (CB3))
      (let-match erased st (GStPop1 _ _ _ nb))
      (let-match erased si (SI0 _ _ x1 _ _ si1 n1))
      (let-match erased (not-not x1 x x2 n1 (xor-t x x2 rx)) (Refl _ _))
      (values z si1 (xor-nn b z y b2 y2 xb nb (xor-t y y2 ry))))
    ((SPop12 _)
      (let-match erased ce (CB2))
      (let-match erased st (GStPop1 _ _ _ nb))
      (let-match erased si (SI1 _ _ x1 _ z1 _ si1 n1 m1))
      (let-match erased (not-not x1 x x2 n1 (xor-t x x2 rx)) (Refl _ _))
      (let-match erased (xor-f y y2 ry) (Refl _ _))
      (values z1 si1 (xor-bz b z y b2 z1 xb nb (not-sym z1 z m1))))))

(def-fns _ $ (erased inv-next : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (Nat) d d2) (erased (Bool) b b2) (erased (Col) c c2)
    (erased (Bool) x y z) (erased (Sym s bs e bs2) sy) (erased (GStep d b s d2 b2) st) (erased (AddK c e c2) a) (erased (CB c x y) cb)
    (erased (SInv bs d x z) si) (erased (Xor b z y) xb) ->
    (erased (Bool) x2 y2 z2) (erased (SInv bs2 d2 x2 z2) si2) (erased (Xor b2 z2 y2) xb2) (erased (CB c2 x2 y2) cb2))
  (let ((erased xe) (erased ye) (erased ce)) (cb-exists e))
  (let ((erased x2) (erased y2) (erased rx) (erased ry) (erased cb2)) (addc-bits c e c2 x y xe ye a cb ce))
  (let ((erased z2) (erased si2) (erased xb2)) (inv-step s bs bs2 e d d2 b b2 x y z xe ye x2 y2 sy st ce rx ry si xb))
  (values x2 y2 z2 si2 xb2 cb2))

; The last symbol of cgram of chromogram.v, after a chromogram leaving d open chords and parity b.
(def-adts $ (Last : ((Nat) d) ((Bool) b) ((Gsym) s) -> Type)
  enum
  (many LastSkip : -> (Last (Zero) (BTrue) (GSkip)))
  (many LastPop0 : -> (Last (Succ (Zero)) (BFalse) (GPop0)))
  (many LastPop1 : -> (Last (Succ (Zero)) (BTrue) (GPop1))))

; A last step that empties the stack ends a balanced chromogram with the symbol cgram restores.
(def-fns _ $ (erased end-inv : (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) c) (erased (Nat) d) (erased (Bool) b x y z)
    (erased (Sym s bs c (BS0)) sy) (erased (SInv bs d x z) si) (erased (Xor b z y) xb) (erased (CB c x y) cb) ->
    (erased (GBal d b (Nil (Gsym))) g) (erased (Last d b s) l))
  (match erased sy _
    ((SSkip _) (let-match erased si (SINil)) (let-match erased cb (CB1)) (let-match erased xb (XTF)) (values (GBEnd0) (LastSkip)))
    ((SPop02 _) (let-match erased si (SI0 _ _ _ _ _ si1 _)) (let-match erased si1 (SINil)) (let-match erased cb (CB2)) (let-match erased xb (XFF))
      (values (GBEnd1 b) (LastPop0)))
    ((SPop03 _) (let-match erased si (SI1 _ _ _ _ _ _ si1 _ m)) (let-match erased si1 (SINil)) (let-match erased m (NotF)) (let-match erased cb (CB3))
      (let-match erased xb (XFT)) (values (GBEnd1 b) (LastPop0)))
    ((SPop12 _) (let-match erased si (SI1 _ _ _ _ _ _ si1 _ m)) (let-match erased si1 (SINil)) (let-match erased m (NotF)) (let-match erased cb (CB2))
      (let-match erased xb (XTT)) (values (GBEnd1 b) (LastPop1)))
    ((SPop13 _) (let-match erased si (SI0 _ _ _ _ _ si1 _)) (let-match erased si1 (SINil)) (let-match erased cb (CB3)) (let-match erased xb (XTF))
      (values (GBEnd1 b) (LastPop1)))))

(def-fns _ $ (erased end-sym : (erased (Nat) d) (erased (Bool) b) (erased (Gsym) s) (erased (Last d b s) l) (erased (Bstack) bs) (erased (Col) c)
    (erased (Bool) x y z) (erased (SInv bs d x z) si) (erased (Xor b z y) xb) (erased (CB c x y) cb) -> (erased (Sym s bs c (BS0)) sy))
  (match erased l _
    ((LastSkip) (let-match erased si (SINil)) (let-match erased xb (XTF)) (let-match erased cb (CB1)) (SSkip (BS0)))
    ((LastPop0)
      (match erased si _
        ((SI0 _ _ _ _ _ si1 n) (let-match erased si1 (SINil)) (let-match erased n (NotF)) (let-match erased xb (XFF)) (let-match erased cb (CB2))
          (SPop02 (BS0)))
        ((SI1 _ _ _ _ _ _ si1 n m) (let-match erased si1 (SINil)) (let-match erased n (NotF)) (let-match erased m (NotF)) (let-match erased xb (XFT))
          (let-match erased cb (CB3)) (SPop03 (BS0)))))
    ((LastPop1)
      (match erased si _
        ((SI0 _ _ _ _ _ si1 n) (let-match erased si1 (SINil)) (let-match erased n (NotF)) (let-match erased xb (XTF)) (let-match erased cb (CB3))
          (SPop13 (BS0)))
        ((SI1 _ _ _ _ _ _ si1 n m) (let-match erased si1 (SINil)) (let-match erased n (NotF)) (let-match erased m (NotF)) (let-match erased xb (XTT))
          (let-match erased cb (CB2)) (SPop12 (BS0)))))))

; cgram of chromogram.v appends s to w, from d open chords and parity b.
(def-adts $ (Closes : ((Nat) d) ((Bool) b) ((List (Gsym)) w) ((Gsym) s) -> Type)
  enum
  (many CloNil : (erased (Nat) d) (erased (Bool) b) (erased (Gsym) s) (erased (Last d b s) l) -> (Closes d b (Nil (Gsym)) s))
  (many CloCons : (erased (Nat) d d2) (erased (Bool) b b2) (erased (Gsym) s0 s) (erased (List (Gsym)) w) (erased (GStep d b s0 d2 b2) st)
      (erased (Closes d2 b2 w s) c) -> (Closes d b (Cons (Gsym) s0 w) s)))

(def-fns _ $ (erased closes-gpre : (erased (Nat) d0 d) (erased (Bool) b0 b) (erased (List (Gsym)) pre u fw) (erased (Gsym) s)
    (subterm erased (GPre d0 b0 pre d b) p) (erased (Closes d b u s) c) (erased (RevApp (Gsym) pre u fw) rw) -> (erased (Closes d0 b0 fw s) r))
  (match erased p _
    ((GPreNil _ _) (let-match erased rw (RANil _ _)) c)
    ((GPreCons _ d1 _ _ b1 _ pre1 s0 p1 st)
      (let-match erased rw (RACons _ _ _ _ _ rw1))
      (closes-gpre d0 d1 b0 b1 pre1 (Cons _ s0 u) fw s p1 (CloCons d1 d b1 b s0 s u st c) rw1))))

(def-fns _ $ (erased revapp-snoc : (erased Type A) (erased A x) (erased (List A) pre u u2 r r2) (subterm erased (RevApp A pre u r) p)
    (erased (Snoc A u x u2) q) (erased (RevApp A pre u2 r2) p2) -> (erased (Snoc A r x r2) res))
  (match erased p _
    ((RANil _ _) (let-match erased p2 (RANil _ _)) q)
    ((RACons _ a pre1 _ _ p1)
      (let-match erased p2 (RACons _ _ _ _ _ q1))
      (revapp-snoc A x pre1 (Cons A a u) (Cons A a u2) r r2 p1 (SnocCons A a x u u2 q) q1))))

; After matchg of chromogram.v, with the bit stack a Bstack.
(def-adts $ (MatchG : ((Bstack) bs) ((List (Col)) ct) ((List (Gsym)) cw) -> Type)
  enum
  (many MGNil : -> (MatchG (BS0) (Nil (Col)) (Nil (Gsym))))
  (many MGCons : (erased (Bstack) bs bs2) (erased (Col) e) (erased (Gsym) s) (erased (List (Col)) ct) (erased (List (Gsym)) cw)
      (erased (Sym s bs e bs2) p) (erased (MatchG bs2 ct cw) q) -> (MatchG bs (Cons (Col) e ct) (Cons (Gsym) s cw))))

; After matchg_pg of chromogram.v: a partial match whose completion is balanced completes to a match of the trace completion.
(def-fns _ $ (erased pg-g : (erased (Bstack) bs) (erased (List (Col)) et ct) (erased (List (Gsym)) w) (erased (Gsym) s) (erased (Col) c) (erased (Nat) d)
    (erased (Bool) b x y z) (subterm erased (MatchPG bs et w) mt) (erased (Ctr c et ct) cr) (erased (CB c x y) cb) (erased (SInv bs d x z) si)
    (erased (Xor b z y) xb) (erased (Closes d b w s) cl) -> (erased (List (Gsym)) cw) (erased (Snoc (Gsym) w s cw) sn) (erased (MatchG bs ct cw) mg))
  (match erased mt _
    ((MPNil _)
      (let-match erased cr (CtrNil _))
      (let-match erased cl (CloNil _ _ _ l))
      (values (Cons _ s (Nil _)) (SnocNil _ s) (MGCons bs (BS0) c s (Nil _) (Nil _) (end-sym d b s l bs c x y z si xb cb) (MGNil))))
    ((MPCons _ bs2 e s0 et1 w1 sy mt1)
      (let-match erased cr (CtrCons _ _ c2 _ ct1 a cr1))
      (let-match erased cl (CloCons _ d2 _ b2 _ _ _ st cl1))
      (let ((erased x2) (erased y2) (erased z2) (erased si2) (erased xb2) (erased cb2)) (inv-next s0 bs bs2 e d d2 b b2 c c2 x y z sy st a cb si xb))
      (let ((erased cw1) (erased sn) (erased mg)) (pg-g bs2 et1 ct1 w1 s c2 d2 b2 x2 y2 z2 mt1 cr1 cb2 si2 xb2 cl1))
      (values (Cons _ s0 cw1) (SnocCons _ s0 s w1 cw1 sn) (MGCons bs bs2 e s0 ct1 cw1 sy mg)))))

; The Kempe co-closure of Q on complete traces (after Kempe_coclosure of chromogram.v), as the least set holding Q, holding each trace
; that a colour permutation sends into it, and holding each trace all of whose matching chromograms are matched by a trace in it.
; AMC Q bs ct pre: every chromogram w matching ct from the stack bs has its whole chromogram (the reverse of pre, then w) matched by
; a trace of the set.
(def-adts
  ((KCC : (Pred Q) ((List (Col)) ct) -> Type)
    enum
    (many KCIn : (erased Pred Q) (erased (List (Col)) ct) (erased (Holds Q ct) q) -> (KCC Q ct))
    (many KCPerm : (erased Pred Q) (erased (List (Col)) ct ct2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g ct ct2) pt)
        (erased (KCC Q ct2) k) -> (KCC Q ct))
    (many KCGram : (erased Pred Q) (erased (List (Col)) ct) (erased (AMC Q (BS0) ct (Nil (Gsym))) a) -> (KCC Q ct)))
  ((AMC : (Pred Q) ((Bstack) bs) ((List (Col)) ct) ((List (Gsym)) pre) -> Type)
    enum
    (many AMCEnd : (erased Pred Q) (erased (List (Gsym)) pre w) (erased (RevApp (Gsym) pre (Nil (Gsym)) w) ra) (erased (WitC Q w) wt)
        -> (AMC Q (BS0) (Nil (Col)) pre))
    (many AMCOpen : (erased Pred Q) (erased (Bstack) bs b) (erased (Popped bs b) pp) (erased (List (Gsym)) pre) -> (AMC Q bs (Nil (Col)) pre))
    (many AMC0 : (erased Pred Q) (erased (Bstack) bs) (erased (List (Col)) ct) (erased (List (Gsym)) pre) -> (AMC Q bs (Cons (Col) (C0) ct) pre))
    (many AMC1 : (erased Pred Q) (erased (Bstack) bs) (erased (List (Col)) ct) (erased (List (Gsym)) pre) (erased (AMC Q bs ct (Cons (Gsym) (GSkip) pre)) a)
        -> (AMC Q bs (Cons (Col) (C1) ct) pre))
    (many AMC23 : (erased Pred Q) (erased (Bstack) bs bs1) (erased (Col) e) (erased (List (Col)) ct) (erased (List (Gsym)) pre)
        (erased (Sym (GPush) bs e bs1) y) (erased (AMC Q bs1 ct (Cons (Gsym) (GPush) pre)) a) (erased (AMCPop Q bs e ct pre) ap)
        -> (AMC Q bs (Cons (Col) e ct) pre)))
  ((AMCPop : (Pred Q) ((Bstack) bs) ((Col) e) ((List (Col)) ct) ((List (Gsym)) pre) -> Type)
    enum
    (many APCNone : (erased Pred Q) (erased (Col) e) (erased (List (Col)) ct) (erased (List (Gsym)) pre) -> (AMCPop Q (BS0) e ct pre))
    (many APCSome : (erased Pred Q) (erased (Bstack) bs b0) (erased (Gsym) s) (erased (Col) e) (erased (List (Col)) ct) (erased (List (Gsym)) pre)
        (erased (Popped bs b0) pp) (erased (Sym s bs e b0) z) (erased (AMC Q b0 ct (Cons (Gsym) s pre)) a) -> (AMCPop Q bs e ct pre)))
  ((WitC : (Pred Q) ((List (Gsym)) cw) -> Type)
    enum
    (many MkWitC : (erased Pred Q) (erased (List (Gsym)) cw) (erased (List (Col)) ct) (erased (MatchG (BS0) ct cw) m) (erased (KCC Q ct) k)
        -> (WitC Q cw))))

; At the end of a partial trace, either the chromogram so far cannot be balanced, or it has a witness completed below.
(def-adts $ (EW : (Pred P) ((Nat) d) ((Bool) b) ((List (Gsym)) pre) -> Type)
  enum
  (many EWBad : (erased Pred P) (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) pre) (erased (EndBad d b) e) -> (EW P d b pre))
  (many EWOk : (erased Pred P) (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) pre w) (erased (RevApp (Gsym) pre (Nil (Gsym)) w) ra)
      (erased (GPre (Zero) (BFalse) pre d b) gp) (erased (List (Col)) et ct) (erased (MatchPG (BS0) et w) mt) (erased (Ctr (C0) et ct) cr)
      (erased (KCC P ct) k) -> (EW P d b pre)))

(def-fns _ $ (erased end-wit : (erased Pred P) (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) c) (erased (Nat) d) (erased (Bool) b x y z)
    (erased (List (Gsym)) pre) (erased (Sym s bs c (BS0)) sy) (erased (SInv bs d x z) si) (erased (Xor b z y) xb) (erased (CB c x y) cb)
    (erased (EW P d b pre) ew) -> (erased (List (Gsym)) full) (erased (RevApp (Gsym) (Cons (Gsym) s pre) (Nil (Gsym)) full) rf) (erased (WitC P full) wt))
  (let ((erased g) (erased l)) (end-inv s bs c d b x y z sy si xb cb))
  (let-match erased ew (EWOk _ _ _ _ w ra gp et ct mt cr k) (absurd (EWBad _ _ _ _ e) (endbad-bal d b e g)))
  (let ((erased full) (erased rf)) (revapp-exists (Gsym) (Cons _ s pre) (Nil _)))
  (let-match erased rf (RACons _ _ _ _ _ rf1))
  (let ((erased cw) (erased sn) (erased mg))
    (pg-g (BS0) et ct w s (C0) (Zero) (BFalse) (BFalse) (BFalse) (BFalse) mt cr (CB0) (SINil) (XFF)
      (closes-gpre (Zero) d (BFalse) b pre (Nil _) w s gp (CloNil d b s l) ra)))
  (let-match erased (snoc-fn (Gsym) w full cw s (revapp-snoc (Gsym) s pre (Nil _) (Cons _ s (Nil _)) w full ra (SnocNil _ s) rf1) sn) (Refl _ _))
  (values full rf (MkWitC P full ct mg k)))

(def-fns _ $ (erased amc-nil : (erased Pred P) (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) c) (erased (Nat) d) (erased (Bool) b x y z)
    (erased (List (Gsym)) pre) (erased (Sym s bs c bs2) sy) (erased (SInv bs d x z) si) (erased (Xor b z y) xb) (erased (CB c x y) cb)
    (erased (EW P d b pre) ew) -> (erased (AMC P bs2 (Nil (Col)) (Cons (Gsym) s pre)) r))
  (let-match erased bs2 (BS0)
    ((BP0 b0) (AMCOpen P bs2 b0 (Popped0 b0) (Cons _ s pre)))
    ((BP1 b0) (AMCOpen P bs2 b0 (Popped1 b0) (Cons _ s pre))))
  (let ((erased full) (erased rf) (erased wt)) (end-wit P s bs c d b x y z pre sy si xb cb ew))
  (AMCEnd P (Cons _ s pre) full rf wt))

(def-fns _ $ (erased amc-last : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b x y z) (erased (Col) c) (erased (List (Gsym)) pre)
    (erased (SInv bs d x z) si) (erased (Xor b z y) xb) (erased (CB c x y) cb) (erased (EW P d b pre) ew) ->
    (erased (AMC P bs (Cons (Col) c (Nil (Col))) pre) r))
  (let ((erased nil)) (Nil (Col)))
  (match erased (col-kind c bs) _
    ((K0 _) (AMC0 P bs nil pre))
    ((K1 _) (AMC1 P bs nil pre (amc-nil P (GSkip) bs bs c d b x y z pre (SSkip bs) si xb cb ew)))
    ((K23 _ _ bs1 y1 po)
      (AMC23 P bs bs1 c nil pre y1 (amc-nil P (GPush) bs bs1 c d b x y z pre y1 si xb cb ew)
        (match erased po _
          ((PNone _) (APCNone P c nil pre))
          ((PSome _ b0 _ s pp z1) (APCSome P bs b0 s c nil pre pp z1 (amc-nil P s bs b0 c d b x y z pre z1 si xb cb ew))))))))

; Every trace of the co-closure on partial traces has its completion in the co-closure on complete traces.
(def-fns _
  ((erased kc-kcc : (erased Pred P) (erased (List (Col)) et ct) (subterm erased (KC P et) k) (erased (Ctr (C0) et ct) cr) -> (erased (KCC P ct) r))
    (match erased k _
      ((KIn _ _ ct2 cr2 p) (let-match erased (ctr-fn (C0) et ct2 ct cr2 cr) (Refl _ _)) (KCIn P ct p))
      ((KPerm _ _ et2 g ip pt k2)
        (let ((erased ct2) (erased cr2)) (ctr-exists (C0) et2))
        (KCPerm P ct ct2 g ip (perm-ctr g ip (C0) (C0) et et2 ct ct2 pt (PC0 g) cr cr2) (kc-kcc P et2 ct2 k2 cr2)))
      ((KGram _ _ a)
        (KCGram P ct (am-amc P (BS0) (Zero) (BFalse) et (Nil _) a (BFalse) (BFalse) (BFalse) (C0) ct (SINil) (XFF) (CB0) cr (GPreNil (Zero) (BFalse)))))))
  ((erased am-amc : (erased Pred P) (erased (Bstack) bs) (erased (Nat) d) (erased (Bool) b) (erased (List (Col)) et) (erased (List (Gsym)) pre)
      (subterm erased (AM P bs d b et pre) a) (erased (Bool) x y z) (erased (Col) c) (erased (List (Col)) ct) (erased (SInv bs d x z) si)
      (erased (Xor b z y) xb) (erased (CB c x y) cb) (erased (Ctr c et ct) cr) (erased (GPre (Zero) (BFalse) pre d b) gp) -> (erased (AMC P bs ct pre) r))
    (match erased a _
      ((AMEndOk _ _ _ _ _ w _ ra wt)
        (let-match erased cr (CtrNil _))
        (let-match erased wt (MkWit _ _ et2 mt k))
        (let ((erased ct2) (erased cr2)) (ctr-exists (C0) et2))
        (amc-last P bs d b x y z c pre si xb cb (EWOk P d b pre w ra gp et2 ct2 mt cr2 (kc-kcc P et2 ct2 k cr2))))
      ((AMEndBad _ _ _ _ _ eb) (let-match erased cr (CtrNil _)) (amc-last P bs d b x y z c pre si xb cb (EWBad P d b pre eb)))
      ((AM0 _ _ _ _ _ _) (let-match erased cr (CtrCons _ _ _ _ ct1 _ _)) (AMC0 P bs ct1 pre))
      ((AM1 _ _ _ _ b2 et1 _ nb a1)
        (let-match erased cr (CtrCons _ _ c2 _ ct1 ad cr1))
        (let ((erased st)) (GStSkip d b b2 nb))
        (let ((erased x2) (erased y2) (erased z2) (erased si2) (erased xb2) (erased cb2)) (inv-next (GSkip) bs bs (C1) d d b b2 c c2 x y z (SSkip bs) st ad cb si xb))
        (AMC1 P bs ct1 pre (am-amc P bs d b2 et1 (Cons _ (GSkip) pre) a1 x2 y2 z2 c2 ct1 si2 xb2 cb2 cr1 (GPreCons (Zero) d d (BFalse) b b2 pre (GSkip) gp st))))
      ((AM23 _ _ bs1 _ _ e et1 _ sy a1 ap)
        (let-match erased cr (CtrCons _ _ c2 _ ct1 ad cr1))
        (let ((erased st)) (GStPush d b))
        (let ((erased x2) (erased y2) (erased z2) (erased si2) (erased xb2) (erased cb2)) (inv-next (GPush) bs bs1 e d (Succ d) b b c c2 x y z sy st ad cb si xb))
        (AMC23 P bs bs1 e ct1 pre sy
          (am-amc P bs1 (Succ d) b et1 (Cons _ (GPush) pre) a1 x2 y2 z2 c2 ct1 si2 xb2 cb2 cr1 (GPreCons (Zero) d (Succ d) (BFalse) b b pre (GPush) gp st))
          (match erased ap _
            ((APNone _ _ _ _ _ _) (APCNone P e ct1 pre))
            ((APZero _ _ _ _ _ _) (let-match erased si (SINil)) (APCNone P e ct1 pre))
            ((APSome _ _ b0 d1 _ b3 s _ _ _ pp zs par a2)
              (let ((erased (GStep d b s d1 b3) st2)) (match erased par _ ((PPar0 _) (GStPop0 d1 b)) ((PPar1 _ _ n) (GStPop1 d1 b b3 n))))
              (let ((erased x3) (erased y3) (erased z3) (erased si3) (erased xb3) (erased cb3)) (inv-next s bs b0 e d d1 b b3 c c2 x y z zs st2 ad cb si xb))
              (APCSome P bs b0 s e ct1 pre pp zs
                (am-amc P b0 d1 b3 et1 (Cons _ s pre) a2 x3 y3 z3 c2 ct1 si3 xb3 cb3 cr1 (GPreCons (Zero) d d1 (BFalse) b b3 pre s gp st2))))))))))

; Soundness half of Kempe_treeP of kempetree.v, on complete traces: the completion of a trace of length h + 1 whose even normal form has
; multiplicity zero in the Kempe tree is in the co-closure of P.
(def-fns _ $ (erased kempe-treeP-c : (erased Pred P) (erased (Nat) h) (erased (Ctree) kt) (erased (KSound P h kt) ks)
    (erased (List (Col)) et et2 ct) (erased (Length (Col) et (Succ h)) len) (erased (ETrace et et2) e) (erased (CtSub kt et2 (Zero)) s)
    (erased (Ctr (C0) et ct) cr) -> (erased (KCC P ct) r))
  (kc-kcc P et ct (kempe-treeP P h kt ks et et2 len e s) cr))

(def-fns _ $ (erased kempe-tree-sound-c : (erased Pred P) (erased (Nat) h) (erased (Ctree) kt ct) (erased (KSound P h kt) ks)
    (erased (CtDisj kt ct) dj) (erased (List (Col)) et ctc) (erased (CtMem ct et) m) (erased (EvenT et (BTrue)) ev)
    (erased (Length (Col) et (Succ h)) len) (erased (Ctr (C0) et ctc) cr) -> (erased (KCC P ctc) r))
  (kc-kcc P et ctc (kempe-tree-sound P h kt ct ks dj et m ev len) cr))

; A relation between traces and chromograms with one parameter, as data, like PredC.
(def-adts $ (RelC : -> Type)
  enum
  (many MkRel : (erased Type X) (erased X x) (erased (TyCtor (X x) ((List (Col)) ct) ((List (Gsym)) w) -> Type) R) -> (RelC)))

(let ((erased Rel)) (RelC))

(def-adts $ (HoldsR : ((RelC) R) ((List (Col)) ct) ((List (Gsym)) w) -> Type)
  enum
  (many MkHoldsR : (erased Type X) (erased X x) (erased (TyCtor (X x) ((List (Col)) ct) ((List (Gsym)) w) -> Type) R) (erased (List (Col)) ct)
      (erased (List (Gsym)) w) (erased (R x ct w) h) -> (HoldsR (MkRel X x R) ct w)))

; After Kempe_closed of chromogram.v, by functions at level L, with R naming the chromogram the definition asks for: the colour
; permutations of each trace of P2 are in P2, and each trace of P2 matches a chromogram w with R ct w, every trace matching which is in P2.
(def-adts $ (KClosed : ((Level) L) (Pred P2) (Rel R) -> Type)
  enum
  (many MkKClosed : (erased (Level) L) (erased Pred P2) (erased Rel R)
      (erased (Fn L (erased (List (Col)) ct ct2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g ct ct2) pt) (erased (Holds P2 ct) p) ->
          (erased (Holds P2 ct2) q)) cp)
      (erased (Fn L (erased (List (Col)) ct) (erased (Holds P2 ct) p) -> (erased (List (Gsym)) w) (erased (MatchG (BS0) ct w) m) (erased (HoldsR R ct w) r)) cg)
      (erased (Fn L (erased (List (Col)) ct ct2) (erased (List (Gsym)) w) (erased (HoldsR R ct w) r) (erased (MatchG (BS0) ct2 w) m) -> (erased (Holds P2 ct2) q)) cm)
      -> (KClosed L P2 R)))

; After Kempe_coclosure of chromogram.v: for the sets closed at a level L, the co-closure KCC meets every closed set holding the trace.
(def-fns _ $ (erased kcc-coclosure : (erased (Level) L) -> (erased (Level) M)
    (erased (Fn M (erased Pred Q P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (List (Col)) ct) (subterm erased (KCC Q ct) k) (erased (Holds P2 ct) p) ->
        (erased (List (Col)) ct2) (erased (Holds Q ct2) q) (erased (Holds P2 ct2) p2)) f))
  (def-lvl M)
  (def-fns M
    ((erased kcc-walk : (erased Pred Q P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (List (Col)) ct) (subterm erased (KCC Q ct) k)
        (erased (Holds P2 ct) p) -> (erased (List (Col)) ct2) (erased (Holds Q ct2) q) (erased (Holds P2 ct2) p2))
      (let-match erased cl (MkKClosed _ _ _ cp cg _))
      (let-match erased k (KCGram _ _ a)
        ((KCIn _ _ q) (values ct q p))
        ((KCPerm _ _ ct2 g ip pt k2) (kcc-walk Q P2 R cl ct2 k2 (cp ct ct2 g ip pt p))))
      (let ((erased w) (erased m) (erased r)) (cg ct p))
      (amc-walk Q P2 R cl ct w r (BS0) ct (Nil _) w a m (RANil _ w)))
    ((erased amc-walk : (erased Pred Q P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (List (Col)) ct0) (erased (List (Gsym)) w0)
        (erased (HoldsR R ct0 w0) r) (erased (Bstack) bs) (erased (List (Col)) ct) (erased (List (Gsym)) pre u) (subterm erased (AMC Q bs ct pre) a)
        (erased (MatchG bs ct u) m) (erased (RevApp (Gsym) pre u w0) ra) -> (erased (List (Col)) ct2) (erased (Holds Q ct2) q) (erased (Holds P2 ct2) p2))
      (let-match erased cl (MkKClosed _ _ _ _ _ cm))
      (match erased m _
        ((MGNil)
          (let-match erased a (AMCEnd _ _ w2 ra2 wt) (absurd (AMCOpen _ _ _ pp _) pp))
          (let-match erased (revapp-fn (Gsym) pre u w0 w2 ra ra2) (Refl _ _))
          (let-match erased wt (MkWitC _ _ ct2 m2 k2))
          (kcc-walk Q P2 R cl ct2 k2 (cm ct0 ct2 w0 r m2)))
        ((MGCons _ bs2 e s ct1 u1 y m1)
          (let ((erased ra1)) (RACons (Gsym) s pre u1 w0 ra))
          (match erased (sym-cls s bs bs2 e y) _
            ((SCSkip _)
              (let-match erased a (AMC1 _ _ _ _ a1) (absurd (AMC23 _ _ _ _ _ _ y1 _ _) y1))
              (amc-walk Q P2 R cl ct0 w0 r bs ct1 (Cons _ (GSkip) pre) u1 a1 m1 ra1))
            ((SCPush _ _ _ _)
              (let-match erased a (AMC23 _ _ bs1 _ _ _ y1 a1 _) (absurd (AMC0 _ _ _ _) y) (absurd (AMC1 _ _ _ _ _) y))
              (let-match erased (sym-fn (GPush) bs bs2 bs1 e y y1) (Refl _ _))
              (amc-walk Q P2 R cl ct0 w0 r bs2 ct1 (Cons _ (GPush) pre) u1 a1 m1 ra1))
            ((SCPop _ _ _ _ pp _)
              (let-match erased a (AMC23 _ _ _ _ _ _ _ _ ap) (absurd (AMC0 _ _ _ _) y) (absurd (AMC1 _ _ _ _ _) (let-match erased y (SSkip _)) pp))
              (let-match erased ap (APCSome _ _ b0 t _ _ _ pp2 z a1) (absurd (APCNone _ _ _ _) pp))
              (let-match erased (popped-fn bs bs2 b0 pp pp2) (Refl _ _))
              (let-match erased (pop-fn s t bs bs2 e pp y z) (Refl _ _))
              (amc-walk Q P2 R cl ct0 w0 r bs2 ct1 (Cons _ s pre) u1 a1 m1 ra1)))))))
  (values M kcc-walk))
