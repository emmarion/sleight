; A planar hypermap has no Moebius path (planar_Jordan of jordan.v), by dart-preserving Walkup transforms: the dart z
; removed stays as a dart fixed by all three permutations.

; f is determined by e and n: e b = a and n c = b give f a = c.
(def-fns _ $ (erased hyper-third : (erased (Nat) d a b c) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    (erased (Nth (Nat) e b a) pe) (erased (Nth (Nat) n c b) pn) -> (erased (Nth (Nat) f a c) r))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf2 io cfe ke cen kn cnf kf))
  (let ((erased lb)) (perm-val d c b n ni pmn pn))
  (let ((erased w) (erased pw)) (nth-exists _ fe d b (respects-length f e fe d cfe le) lb))
  (let ((erased fw)) (respects-nth f e fe b a w cfe pe pw))
  (let ((erased nw)) (respects-nth n fe ids b w b ke pw (iota-nth d b ids io lb)))
  (let-match erased (perm-inj d c w b n ni pmn pn nw) (Refl _ _))
  fw)

(def-fns _ $ (erased skip-keep : (erased (Nat) z a b) (erased (List (Nat)) p p2) (erased (Skip p z p2) sk)
    (erased (Nth (Nat) p a b) pa) (erased (Apart (Nat) Lt a z) na) (erased (Apart (Nat) Lt b z) nb) -> (erased (Nth (Nat) p2 a b) r))
  (let-match erased sk (SkipCut _ _ _ w u pw pz nwz up) ((SkipFixed _ _ _) pa))
  (let-match erased (nat-eq a w) (Unequal _ _ _ _ ne)
    (absurd (Equal _ _ _) (let-match erased (nth-fn _ p a b z pa pw) (Refl _ _)) (apart-irrefl b nb)))
  (upd2-other p p2 w u z z a b up pa ne na))

(def-fns _ $ (erased skip-cut-at : (erased (Nat) d z w c) (erased (List (Nat)) p q p2) (erased (Perm d p q) pm) (erased (Skip p z p2) sk)
    (erased (Nth (Nat) p w z) pw) (erased (Nth (Nat) p z c) pz) (erased (Apart (Nat) Lt w z) ne) -> (erased (Nth (Nat) p2 w c) r))
  (match erased sk _
    (absurd (SkipFixed _ _ pzz) (let-match erased (perm-inj d w z z p q pm pw pzz) (Refl _ _)) (apart-irrefl w ne))
    ((SkipCut _ _ _ w1 u pw1 pz1 _ up)
      (let-match erased (perm-inj d w w1 z p q pm pw pw1) (Refl _ _))
      (let-match erased (nth-fn _ p z c u pz pz1) (Refl _ _))
      (upd2-a p p2 w c z z up))))

; Every dart of s is fixed by p.
(def-adts $ (FixedIn : ((List (Nat)) p s) -> Type)
  enum
  (many FixNil : (erased (List (Nat)) p) -> (FixedIn p (Nil (Nat))))
  (many FixCons : (erased (List (Nat)) p s) (erased (Nat) x) (erased (Nth (Nat) p x x) px) (erased (FixedIn p s) rest)
      -> (FixedIn p (Cons (Nat) x s))))

(def-fns _ $ (erased fixed-at : (erased (List (Nat)) p s) (erased (Nat) x) (subterm erased (FixedIn p s) fx) (erased (In x s) pin)
    -> (erased (Nth (Nat) p x x) r))
  (let-match erased fx (FixCons _ s1 y py fx1) (absurd (FixNil _) pin))
  (let-match erased pin (InThere _ _ _ pin1) ((InHere _ _) py))
  (fixed-at p s1 x fx1 pin1))

(def-fns _ $ (erased fixed-skip : (erased (List (Nat)) p p2 s) (erased (Nat) z) (subterm erased (FixedIn p s) fx) (erased (Skip p z p2) sk)
    (erased (NotIn z s) out) -> (erased (FixedIn p2 s) r))
  (let-match erased fx (FixCons _ s1 x px fx1) ((FixNil _) (FixNil p2)))
  (let-match erased out (NotInCons _ _ _ ne out1))
  (let ((erased nx)) (apart-sym z x ne))
  (FixCons p2 s1 x (skip-keep z x x p p2 sk px nx nx) (fixed-skip p p2 s1 z fx1 sk out1)))

(def-fns _ $ (erased fixed-third : (erased (Nat) d) (erased (List (Nat)) e n f s) (erased (Hypermap d e n f) h)
    (subterm erased (FixedIn e s) fe) (erased (FixedIn n s) fn) -> (erased (FixedIn f s) r))
  (let-match erased fe (FixCons _ s1 x px fe1) ((FixNil _) (FixNil f)))
  (let-match erased fn (FixCons _ _ _ qx fn1))
  (FixCons f s1 x (hyper-third d x x x e n f h px qx) (fixed-third d e n f s1 h fe1 fn1)))

; The darts s, k of them, are fixed by e, n and f, and m more could be.
(def-adts $ (Fuel : ((Nat) d) ((List (Nat)) e n f) ((Nat) m) -> Type)
  enum
  (many MkFuel : (erased (Nat) d m k) (erased (List (Nat)) e n f s) (erased (FixedIn e s) fe) (erased (FixedIn n s) fn)
      (erased (FixedIn f s) ff) (erased (Distinct s) ds) (erased (Length (Nat) s k) ls) (erased (Under s d) us) (erased (Add k m d) a)
      -> (Fuel d e n f m)))

(def-fns _ $ (erased fuel-rot : (erased (Nat) d m) (erased (List (Nat)) e n f) (erased (Fuel d e n f m) fu) -> (erased (Fuel d n f e m) r))
  (let-match erased fu (MkFuel _ _ k _ _ _ s fe fn ff ds ls us a))
  (MkFuel d m k n f e s fn ff fe ds ls us a))

; Some dart other than z is sent to z by p.
(def-adts $ (Moved : ((List (Nat)) p) ((Nat) z) -> Type)
  enum
  (many MkMoved : (erased (List (Nat)) p) (erased (Nat) z a) (erased (Nth (Nat) p a z) pa) (erased (Apart (Nat) Lt a z) ne) -> (Moved p z)))

(def-fns _ $ (erased moved-out : (erased (Nat) d z) (erased (List (Nat)) p q s) (erased (Perm d p q) pm) (erased (FixedIn p s) fx)
    (erased (Moved p z) mv) -> (erased (Lt z d) lz) (erased (NotIn z s) out))
  (let-match erased mv (MkMoved _ _ a pa ne))
  (let-match erased (in-dec z s) (OrR _ _ out)
    (absurd (OrL _ _ pin) (let-match erased (perm-inj d a z z p q pm pa (fixed-at p s z fx pin)) (Refl _ _)) (apart-irrefl a ne)))
  (values (perm-val d a z p q pm pa) out))

(def-fns _ $ (erased under-sub : (erased (List (Nat)) xs ids) (erased (Nat) d) (subterm erased (Under xs d) u) (erased (Iota d ids) io)
    -> (erased (Sub xs ids) r))
  (let-match erased u (UnderCons xs1 x _ lx u1) ((UnderNil _) (SubNil ids)))
  (SubCons x xs1 ids (iota-in d x ids io lx) (under-sub xs1 ids d u1 io)))

(def-fns _ $ (erased fuel-step : (erased (Nat) d k m z) (erased (List (Nat)) s) (erased (Add k m d) a) (erased (Length (Nat) s k) ls)
    (erased (Distinct (Cons (Nat) z s)) ds) (erased (Under (Cons (Nat) z s) d) us)
    -> (erased (Nat) m1) (erased (Eq (Nat) m (Succ m1)) e) (erased (Add (Succ k) m1 d) r))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased lt)) (pigeonhole (Cons _ z s) ids (Succ k) d ds (under-sub (Cons _ z s) ids d us io) (LengthCons _ z s k ls) (iota-length d ids io)))
  (let-match erased m (Succ m1)
    (absurd (Zero) (let-match erased (add-fn k (Zero) d k a (add-zero-right k)) (Refl _ _)) (lt-irrefl (Succ d) lt)))
  (values m1 (Refl _ m) (add-succ-left k m1 d a)))

; WalkupE at a dart z that p sends some other dart to: z is cut out of n and f, and the fuel drops by one.
(def-fns _ $ (erased walk-fuel : (erased (Nat) d m z) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Fuel d e n f m) fu) (erased (Or (Moved n z) (Moved f z)) mv)
    -> (erased (List (Nat)) e2 n2 f2) (erased (Nat) m1) (erased (Skip n z n2) skn) (erased (Skip f z f2) skf) (erased (Hypermap d e2 n2 f2) h2)
    (erased (Genus d e2 n2 f2 (Zero)) g2) (erased (Eq (Nat) m (Succ m1)) em) (erased (Fuel d e2 n2 f2 m1) fu2))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let-match erased fu (MkFuel _ _ k _ _ _ s fe fn ff ds ls us a))
  (let ((erased lz) (erased out)) (match erased mv (((Lt z d) lz) ((NotIn z s) out))
    ((OrL _ _ mn) (moved-out d z n ni s pn fn mn))
    ((OrR _ _ mf) (moved-out d z f fi s pf ff mf))))
  (let ((erased e2) (erased n2) (erased f2) (erased gen2) (erased skn) (erased skf) (erased h2) (erased g2) (erased le))
    (walkup-iso d (Zero) z e n f h g lz))
  (let-match erased (lt-one gen2 le) (Refl _ _))
  (let ((erased ds2)) (DistCons z s out ds))
  (let ((erased us2)) (UnderCons s z d lz us))
  (let ((erased m1) (erased em) (erased a2)) (fuel-step d k m z s a ls ds2 us2))
  (let ((erased fn2)) (FixCons n2 s z (skip-fixed n n2 z skn) (fixed-skip n n2 s z fn skn out)))
  (let ((erased ff2)) (FixCons f2 s z (skip-fixed f f2 z skf) (fixed-skip f f2 s z ff skf out)))
  (values e2 n2 f2 m1 skn skf h2 g2 em
    (MkFuel d m1 (Succ k) e2 n2 f2 (Cons _ z s) (fixed-third d n2 f2 e2 (Cons _ z s) (hyper-rot d e2 n2 f2 h2) fn2 ff2) fn2 ff2 ds2
      (LengthCons _ z s k ls) us2 a2)))

; WalkupF: z cut out of e and n.
(def-fns _ $ (erased walk-fuel-f : (erased (Nat) d m z) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Fuel d e n f m) fu) (erased (Or (Moved e z) (Moved n z)) mv)
    -> (erased (List (Nat)) e2 n2 f2) (erased (Nat) m1) (erased (Skip e z e2) ske) (erased (Skip n z n2) skn) (erased (Hypermap d e2 n2 f2) h2)
    (erased (Genus d e2 n2 f2 (Zero)) g2) (erased (Eq (Nat) m (Succ m1)) em) (erased (Fuel d e2 n2 f2 m1) fu2))
  (let ((erased hr) (erased gr)) (genus-rot2 d (Zero) e n f h g))
  (let ((erased f2) (erased e2) (erased n2) (erased m1) (erased ske) (erased skn) (erased h2) (erased g2) (erased em) (erased fu2))
    (walk-fuel d m z f e n hr gr (fuel-rot d m n f e (fuel-rot d m e n f fu)) mv))
  (values e2 n2 f2 m1 ske skn (hyper-rot d f2 e2 n2 h2) (genus-rot d (Zero) f2 e2 n2 h2 g2) em (fuel-rot d m1 f2 e2 n2 fu2)))

; WalkupN: z cut out of f and e.
(def-fns _ $ (erased walk-fuel-n : (erased (Nat) d m z) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
    (erased (Fuel d e n f m) fu) (erased (Or (Moved f z) (Moved e z)) mv)
    -> (erased (List (Nat)) e2 n2 f2) (erased (Nat) m1) (erased (Skip f z f2) skf) (erased (Skip e z e2) ske) (erased (Hypermap d e2 n2 f2) h2)
    (erased (Genus d e2 n2 f2 (Zero)) g2) (erased (Eq (Nat) m (Succ m1)) em) (erased (Fuel d e2 n2 f2 m1) fu2))
  (let ((erased n2) (erased f2) (erased e2) (erased m1) (erased skf) (erased ske) (erased h2) (erased g2) (erased em) (erased fu2))
    (walk-fuel d m z n f e (hyper-rot d e n f h) (genus-rot d (Zero) e n f h g) (fuel-rot d m e n f fu) mv))
  (let ((erased h3) (erased g3)) (genus-rot2 d (Zero) n2 f2 e2 h2 g2))
  (values e2 n2 f2 m1 skf ske h3 g3 em (fuel-rot d m1 f2 e2 n2 (fuel-rot d m1 n2 f2 e2 fu2))))

; A clink path that avoids z is one of WalkupE z.
(def-fns _ $ (erased lift-e : (erased (Nat) z a b) (erased (List (Nat)) n f n2 f2 q) (subterm erased (CPath n f a q b) cp)
    (erased (Skip n z n2) skn) (erased (Skip f z f2) skf) (erased (NotIn z (Cons (Nat) a q)) out) -> (erased (CPath n2 f2 a q b) r))
  (match erased cp _
    ((CPNil _ _ _) (CPNil n2 f2 a))
    ((CPNode _ _ q1 _ y _ pn rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (CPNode n2 f2 q1 a y b (skip-keep z y a n n2 skn pn (apart-sym z y ny) (apart-sym z a na)) (lift-e z y b n f n2 f2 q1 rest skn skf out1)))
    ((CPFace _ _ q1 _ y _ pf rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (CPFace n2 f2 q1 a y b (skip-keep z a y f f2 skf pf (apart-sym z a na) (apart-sym z y ny)) (lift-e z y b n f n2 f2 q1 rest skn skf out1)))))

; A clink path that avoids z, and the face step after the edge image w of z, is one of WalkupF z.
(def-fns _ $ (erased lift-f : (erased (Nat) d z a b w w2) (erased (List (Nat)) e n f e2 n2 f2 q) (erased (Hypermap d e n f) h)
    (erased (Hypermap d e2 n2 f2) h2) (subterm erased (CPath n f a q b) cp) (erased (Skip e z e2) ske) (erased (Skip n z n2) skn)
    (erased (NotIn z (Cons (Nat) a q)) out) (erased (Nth (Nat) e z w) pw) (erased (Nth (Nat) f w w2) pw2) (erased (NotIn w2 q) out2)
    -> (erased (CPath n2 f2 a q b) r))
  (match erased cp _
    ((CPNil _ _ _) (CPNil n2 f2 a))
    ((CPNode _ _ q1 _ y _ pn rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (let-match erased out2 (NotInCons _ _ _ _ out3))
      (CPNode n2 f2 q1 a y b (skip-keep z y a n n2 skn pn (apart-sym z y ny) (apart-sym z a na))
        (lift-f d z y b w w2 e n f e2 n2 f2 q1 h h2 rest ske skn out1 pw pw2 out3)))
    ((CPFace _ _ q1 _ y _ pf rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (let-match erased out2 (NotInCons _ _ _ nw2 out3))
      (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
      (let ((erased c) (erased pc) (erased _)) (perm-nth d y n ni pmn (perm-val d a y f fi pmf pf)))
      (let ((erased ec)) (hyper-third d c y a n f e (hyper-rot d e n f h) pc pf))
      (let-match erased (nat-eq c z) (Unequal _ _ _ _ ncz)
        (absurd (Equal _ _ _)
          (let-match erased (nth-fn _ e z a w ec pw) (Refl _ _))
          (let-match erased (nth-fn _ f a y w2 pf pw2) (Refl _ _))
          (apart-irrefl y nw2)))
      (CPFace n2 f2 q1 a y b
        (hyper-third d a c y e2 n2 f2 h2 (skip-keep z c a e e2 ske ec ncz (apart-sym z a na)) (skip-keep z y c n n2 skn pc (apart-sym z y ny) ncz))
        (lift-f d z y b w w2 e n f e2 n2 f2 q1 h h2 rest ske skn out1 pw pw2 out3)))))

; A clink path that avoids z and its face image w is one of WalkupN z.
(def-fns _ $ (erased lift-n : (erased (Nat) d z a b w) (erased (List (Nat)) e n f e2 n2 f2 q) (erased (Hypermap d e n f) h)
    (erased (Hypermap d e2 n2 f2) h2) (subterm erased (CPath n f a q b) cp) (erased (Skip f z f2) skf) (erased (Skip e z e2) ske)
    (erased (NotIn z (Cons (Nat) a q)) out) (erased (Nth (Nat) f z w) pw) (erased (NotIn w q) out2)
    -> (erased (CPath n2 f2 a q b) r))
  (match erased cp _
    ((CPNil _ _ _) (CPNil n2 f2 a))
    ((CPFace _ _ q1 _ y _ pf rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (let-match erased out2 (NotInCons _ _ _ _ out3))
      (CPFace n2 f2 q1 a y b (skip-keep z a y f f2 skf pf (apart-sym z a na) (apart-sym z y ny))
        (lift-n d z y b w e n f e2 n2 f2 q1 h h2 rest skf ske out1 pw out3)))
    ((CPNode _ _ q1 _ y _ pn rest)
      (let-match erased out (NotInCons _ _ _ na out1))
      (let-match erased out1 (NotInCons _ _ _ ny _))
      (let-match erased out2 (NotInCons _ _ _ nw out3))
      (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pme) (erased pmn) (erased pmf)) (hyper-core d e n f h))
      (let ((erased c) (erased pc) (erased _)) (perm-nth d a e nf pme (perm-val d y a n ni pmn pn)))
      (let ((erased fc)) (hyper-third d c a y e n f h pc pn))
      (let-match erased (nat-eq c z) (Unequal _ _ _ _ ncz)
        (absurd (Equal _ _ _) (let-match erased (nth-fn _ f z y w fc pw) (Refl _ _)) (apart-irrefl y nw)))
      (CPNode n2 f2 q1 a y b
        (hyper-third d y c a f2 e2 n2 (hyper-rot d n2 f2 e2 (hyper-rot d e2 n2 f2 h2))
          (skip-keep z c y f f2 skf fc ncz (apart-sym z y ny)) (skip-keep z a c e e2 ske pc (apart-sym z a na) ncz))
        (lift-n d z y b w e n f e2 n2 f2 q1 h h2 rest skf ske out1 pw out3)))))
