(def-adts $ (Elem : (Type A) (A x) ((List A) xs) -> Type)
  enum
  (many ElHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Elem A x (Cons A x rest)))
  (many ElThere : (erased Type A) (erased A x y) (erased (List A) rest) (erased (Elem A x rest) p) -> (Elem A x (Cons A y rest))))

; r is a suffix of rr.
(def-adts $ (Suffix : (Type A) ((List A) r) ((List A) rr) -> Type)
  enum
  (many SufHere : (erased Type A) (erased (List A) rr) -> (Suffix A rr rr))
  (many SufNext : (erased Type A) (erased A x) (erased (List A) r rr) (erased (Suffix A (Cons A x r) rr) p) -> (Suffix A r rr)))

(def-fns _ $ (erased suffix-elem : (erased Type A) (erased A x) (erased (List A) r rr) (subterm erased (Suffix A r rr) p) (erased (Elem A x r) e) ->
    (erased (Elem A x rr) q))
  (match erased p _
    ((SufHere _ _) e)
    ((SufNext _ y _ _ p1) (suffix-elem A x (Cons A y r) rr p1 (ElThere A x y r e)))))

(let ((erased RC)) (Rx (Ctree)))

(def-adts $ (Hits : ((List RC) r) ((List (Gsym)) w) -> Type)
  enum
  (many MkHits : (erased (List RC) r) (erased (List (Gsym)) w) (erased (Bstack) bs) (erased (Ctree) t) (erased (List (Col)) et)
      (erased (Elem RC (MkRx (Ctree) bs t) r) el) (erased (CtMem t et) m) (erased (MatchPG bs et w) mt) -> (Hits r w)))

; Each restriction in r2 is one in r advanced by the symbol s.
(def-adts $ (RJust : ((Gsym) s) ((List RC) r) ((List RC) r2) -> Type)
  enum
  (many RJNil : (erased (Gsym) s) (erased (List RC) r) -> (RJust s r (Nil RC)))
  (many RJCons : (erased (Gsym) s) (erased (List RC) r r2) (erased (Bstack) bs bs2) (erased (Ctree) t t2) (erased (Col) e)
      (erased (Elem RC (MkRx (Ctree) bs t) r) el) (erased (Sym s bs e bs2) y) (erased (CtSel t e t2) sl) (erased (RJust s r r2) j)
      -> (RJust s r (Cons RC (MkRx (Ctree) bs2 t2) r2))))

(def-fns _ $ (erased rjust-hits : (erased (Gsym) s) (erased (List RC) r r2) (erased (List (Gsym)) w) (subterm erased (RJust s r r2) j)
    (erased (Hits r2 w) h) -> (erased (Hits r (Cons (Gsym) s w)) res))
  (let-match erased h (MkHits _ _ bs2 t2 et el m mt))
  (let-match erased j (RJCons _ _ r3 bs _ t _ e el1 y sl j1) (absurd (RJNil _ _) el))
  (match erased el _
    ((ElHere _ _ _) (MkHits r (Cons _ s w) bs t (Cons _ e et) el1 (mem-cons t t2 e et sl m) (MPCons bs bs2 e s et w y mt)))
    ((ElThere _ _ _ _ el2) (rjust-hits s r r3 w j1 (MkHits r3 w bs2 t2 et el2 m mt)))))

; Every chromogram of gs is hit by r.
(def-adts
  ((GHit : ((GSet) gs) ((List RC) r) -> Type)
    enum
    (many GHE : (erased (List RC) r) -> (GHit (GSG (GEmpty)) r))
    (many GHOne : (erased (List RC) r) (erased (Hits r (Nil (Gsym))) h) -> (GHit (GSOne) r))
    (many GHS : (erased (Gtree) g) (erased (List RC) r) (erased (GHitAt (GSG g) r (GPush)) h0) (erased (GHitAt (GSG g) r (GSkip)) h1)
        (erased (GHitAt (GSG g) r (GPop0)) h2) (erased (GHitAt (GSG g) r (GPop1)) h3) -> (GHit (GSG g) r)))
  ((GHitAt : ((GSet) gs) ((List RC) r) ((Gsym) s) -> Type)
    enum
    (many MkGHitAt : (erased (GSet) gs gs2) (erased (List RC) r r2) (erased (Gsym) s) (erased (GSel gs s gs2) p) (erased (RJust s r r2) j)
        (erased (GHit gs2 r2) h) -> (GHitAt gs r s))))

(def-fns _ $ (erased absurd gmem-empty : (subterm erased (List (Gsym)) w) (erased (GMem (GSG (GEmpty)) w) m) -> (erased (False) f))
  (let-match erased m (GMCons _ g1 s w1 p m1))
  (let-match erased (sel-gempty s g1 p) (Refl _ _))
  (gmem-empty w1 m1))

(def-fns _ $ (erased ghit-mem : (erased (GSet) gs) (erased (List RC) r) (subterm erased (List (Gsym)) w) (erased (GHit gs r) h)
    (erased (GMem gs w) m) -> (erased (Hits r w) res))
  (match erased m _
    ((GMNil) (let-match erased h (GHOne _ hs)) hs)
    ((GMCons _ gs2 s w1 sl m1)
      (match erased h _
        (absurd (GHE _) (let-match erased (sel-gempty s gs2 sl) (Refl _ _)) (gmem-empty w1 m1))
        (absurd (GHOne _ _) (let-match erased sl (GSelOne _)) (gmem-empty w1 m1))
        ((GHS _ _ h0 h1 h2 h3)
          (let-match erased (match erased s (((GHitAt gs r s) k)) ((GPush) h0) ((GSkip) h1) ((GPop0) h2) ((GPop1) h3))
            (MkGHitAt _ gs3 _ r2 _ sl2 j h4))
          (let-match erased (gsel-fn gs gs2 gs3 s sl sl2) (Refl _ _))
          (rjust-hits s r r2 w1 j (ghit-mem gs2 r2 w1 h4 m1)))))))

(def-fns _
  ((erased part-sym : (erased (GSet) gs a b) (subterm erased (GPart gs a b) p) -> (erased (GPart gs b a) q))
    (match erased p _
      ((GPE) p)
      ((GPS _ _ _ n x y rg ra rb s p0 p1 p2 p3)
        (GPS gs b a n y x rg rb ra (add-comm x y n s) (partat-sym gs a b (GPush) p0) (partat-sym gs a b (GSkip) p1)
          (partat-sym gs a b (GPop0) p2) (partat-sym gs a b (GPop1) p3)))))
  ((erased partat-sym : (erased (GSet) gs a b) (erased (Gsym) s) (subterm erased (GPartAt gs a b s) p) -> (erased (GPartAt gs b a s) q))
    (let-match erased p (MkGPartAt _ _ _ g1 a1 b1 _ sg sa sb q1))
    (MkGPartAt gs b a g1 b1 a1 s sg sb sa (part-sym g1 a1 b1 q1))))

(def-fns _ $ (erased one-part : -> (erased (GPart (GSOne) (GSOne) (GSG (GEmpty))) p))
  (let ((erased e)) (GSG (GEmpty)))
  (GPS (GSOne) (GSOne) e (Succ (Zero)) (Succ (Zero)) (Zero) (GROne) (GROne) (GRG (GEmpty)) (AddSucc (Zero) (Zero) (Zero) (AddZero (Zero)))
    (MkGPartAt (GSOne) (GSOne) e e e e (GPush) (GSelOne (GPush)) (GSelOne (GPush)) (sel-gempty-mk (GPush)) (GPE))
    (MkGPartAt (GSOne) (GSOne) e e e e (GSkip) (GSelOne (GSkip)) (GSelOne (GSkip)) (sel-gempty-mk (GSkip)) (GPE))
    (MkGPartAt (GSOne) (GSOne) e e e e (GPop0) (GSelOne (GPop0)) (GSelOne (GPop0)) (sel-gempty-mk (GPop0)) (GPE))
    (MkGPartAt (GSOne) (GSOne) e e e e (GPop1) (GSelOne (GPop1)) (GSelOne (GPop1)) (sel-gempty-mk (GPop1)) (GPE))))

(def-adts $ (BitPart : ((Bool) b) ((Bool) x) ((Bool) y) -> Type)
  enum
  (many BPL : -> (BitPart (BTrue) (BTrue) (BFalse)))
  (many BPR : -> (BitPart (BTrue) (BFalse) (BTrue)))
  (many BPN : -> (BitPart (BFalse) (BFalse) (BFalse))))

(def-fns _ $ (erased bset-part : (erased (Bool) b x y) (erased (GSet) gs ga gb) (erased (BitPart b x y) bp) (erased (BSet b gs) s)
    (erased (BSet x ga) sa) (erased (BSet y gb) sb) -> (erased (GPart gs ga gb) p))
  (match erased bp _
    ((BPL) (let-match erased s (BSetT)) (let-match erased sa (BSetT)) (let-match erased sb (BSetF)) (one-part))
    ((BPR) (let-match erased s (BSetT)) (let-match erased sa (BSetF)) (let-match erased sb (BSetT)) (part-sym gs gb ga (one-part)))
    ((BPN) (let-match erased s (BSetF)) (let-match erased sa (BSetF)) (let-match erased sb (BSetF)) (GPE))))

(def-fns _ $ (erased leaf-part-at : (erased (Gtree) l a b) (erased (Bool) l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3 lb ab bb) (erased (Gsym) s)
    (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll) (erased (LeafSet a (MkBits a0 a1 a2 a3)) la) (erased (LeafSet b (MkBits b0 b1 b2 b3)) lb2)
    (erased (Pick4 (Bool) s l0 l1 l2 l3 lb) pl) (erased (Pick4 (Bool) s a0 a1 a2 a3 ab) pa) (erased (Pick4 (Bool) s b0 b1 b2 b3 bb) pb)
    (erased (BitPart lb ab bb) bp) -> (erased (GPartAt (GSG l) (GSG a) (GSG b) s) r))
  (let ((erased gl) (erased sl)) (bset-exists lb))
  (let ((erased ga) (erased sa)) (bset-exists ab))
  (let ((erased gb) (erased sb)) (bset-exists bb))
  (MkGPartAt (GSG l) (GSG a) (GSG b) gl ga gb s (GSelL l l0 l1 l2 l3 lb s gl ll pl sl) (GSelL a a0 a1 a2 a3 ab s ga la pa sa)
    (GSelL b b0 b1 b2 b3 bb s gb lb2 pb sb) (bset-part lb ab bb gl ga gb bp sl sa sb)))

(def-fns _ $ (erased leaf-part : (erased (Gtree) l a b) (erased (Bool) l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3)
    (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll) (erased (LeafSet a (MkBits a0 a1 a2 a3)) la) (erased (LeafSet b (MkBits b0 b1 b2 b3)) lb)
    (erased (BitPart l0 a0 b0) q0) (erased (BitPart l1 a1 b1) q1) (erased (BitPart l2 a2 b2) q2) (erased (BitPart l3 a3 b3) q3) ->
    (erased (GPart (GSG l) (GSG a) (GSG b)) r))
  (GPS (GSG l) (GSG a) (GSG b) (Zero) (Zero) (Zero) (GRG l) (GRG a) (GRG b) (AddZero (Zero))
    (leaf-part-at l a b l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3 l0 a0 b0 (GPush) ll la lb
      (PkPush _ l0 l1 l2 l3) (PkPush _ a0 a1 a2 a3) (PkPush _ b0 b1 b2 b3) q0)
    (leaf-part-at l a b l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3 l1 a1 b1 (GSkip) ll la lb
      (PkSkip _ l0 l1 l2 l3) (PkSkip _ a0 a1 a2 a3) (PkSkip _ b0 b1 b2 b3) q1)
    (leaf-part-at l a b l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3 l2 a2 b2 (GPop0) ll la lb
      (PkPop0 _ l0 l1 l2 l3) (PkPop0 _ a0 a1 a2 a3) (PkPop0 _ b0 b1 b2 b3) q2)
    (leaf-part-at l a b l0 l1 l2 l3 a0 a1 a2 a3 b0 b1 b2 b3 l3 a3 b3 (GPop1) ll la lb
      (PkPop1 _ l0 l1 l2 l3) (PkPop1 _ a0 a1 a2 a3) (PkPop1 _ b0 b1 b2 b3) q3)))

(def-fns _ $ (erased node-part : (erased (Gtree) t0 t1 t2 t3 a0 a1 a2 a3 b0 b1 b2 b3)
    (erased (GPart (GSG t0) (GSG a0) (GSG b0)) p0) (erased (GPart (GSG t1) (GSG a1) (GSG b1)) p1)
    (erased (GPart (GSG t2) (GSG a2) (GSG b2)) p2) (erased (GPart (GSG t3) (GSG a3) (GSG b3)) p3) ->
    (erased (GPart (GSG (GNode t0 t1 t2 t3)) (GSG (GNode a0 a1 a2 a3)) (GSG (GNode b0 b1 b2 b3))) r))
  (let ((erased t) (erased a) (erased b)) (values (GNode t0 t1 t2 t3) (GNode a0 a1 a2 a3) (GNode b0 b1 b2 b3)))
  (GPS (GSG t) (GSG a) (GSG b) (Zero) (Zero) (Zero) (GRG t) (GRG a) (GRG b) (AddZero (Zero))
    (MkGPartAt (GSG t) (GSG a) (GSG b) (GSG t0) (GSG a0) (GSG b0) (GPush) (GSelN t0 t1 t2 t3 t0 (GPush) (PkPush _ t0 t1 t2 t3))
      (GSelN a0 a1 a2 a3 a0 (GPush) (PkPush _ a0 a1 a2 a3)) (GSelN b0 b1 b2 b3 b0 (GPush) (PkPush _ b0 b1 b2 b3)) p0)
    (MkGPartAt (GSG t) (GSG a) (GSG b) (GSG t1) (GSG a1) (GSG b1) (GSkip) (GSelN t0 t1 t2 t3 t1 (GSkip) (PkSkip _ t0 t1 t2 t3))
      (GSelN a0 a1 a2 a3 a1 (GSkip) (PkSkip _ a0 a1 a2 a3)) (GSelN b0 b1 b2 b3 b1 (GSkip) (PkSkip _ b0 b1 b2 b3)) p1)
    (MkGPartAt (GSG t) (GSG a) (GSG b) (GSG t2) (GSG a2) (GSG b2) (GPop0) (GSelN t0 t1 t2 t3 t2 (GPop0) (PkPop0 _ t0 t1 t2 t3))
      (GSelN a0 a1 a2 a3 a2 (GPop0) (PkPop0 _ a0 a1 a2 a3)) (GSelN b0 b1 b2 b3 b2 (GPop0) (PkPop0 _ b0 b1 b2 b3)) p2)
    (MkGPartAt (GSG t) (GSG a) (GSG b) (GSG t3) (GSG a3) (GSG b3) (GPop1) (GSelN t0 t1 t2 t3 t3 (GPop1) (PkPop1 _ t0 t1 t2 t3))
      (GSelN a0 a1 a2 a3 a3 (GPop1) (PkPop1 _ a0 a1 a2 a3)) (GSelN b0 b1 b2 b3 b3 (GPop1) (PkPop1 _ b0 b1 b2 b3)) p3)))

(def-fns _ $ (erased part-l : (subterm erased (Gtree) g) -> (erased (GPart (GSG g) (GSG g) (GSG (GEmpty))) p))
  (let ((erased e)) (GEmpty))
  (match erased g _
    ((GNode t0 t1 t2 t3)
      (GPS (GSG g) (GSG g) (GSG e) (Zero) (Zero) (Zero) (GRG g) (GRG g) (GRG e) (AddZero (Zero))
        (MkGPartAt (GSG g) (GSG g) (GSG e) (GSG t0) (GSG t0) (GSG e) (GPush) (GSelN t0 t1 t2 t3 t0 (GPush) (PkPush _ t0 t1 t2 t3))
          (GSelN t0 t1 t2 t3 t0 (GPush) (PkPush _ t0 t1 t2 t3)) (sel-gempty-mk (GPush)) (part-l t0))
        (MkGPartAt (GSG g) (GSG g) (GSG e) (GSG t1) (GSG t1) (GSG e) (GSkip) (GSelN t0 t1 t2 t3 t1 (GSkip) (PkSkip _ t0 t1 t2 t3))
          (GSelN t0 t1 t2 t3 t1 (GSkip) (PkSkip _ t0 t1 t2 t3)) (sel-gempty-mk (GSkip)) (part-l t1))
        (MkGPartAt (GSG g) (GSG g) (GSG e) (GSG t2) (GSG t2) (GSG e) (GPop0) (GSelN t0 t1 t2 t3 t2 (GPop0) (PkPop0 _ t0 t1 t2 t3))
          (GSelN t0 t1 t2 t3 t2 (GPop0) (PkPop0 _ t0 t1 t2 t3)) (sel-gempty-mk (GPop0)) (part-l t2))
        (MkGPartAt (GSG g) (GSG g) (GSG e) (GSG t3) (GSG t3) (GSG e) (GPop1) (GSelN t0 t1 t2 t3 t3 (GPop1) (PkPop1 _ t0 t1 t2 t3))
          (GSelN t0 t1 t2 t3 t3 (GPop1) (PkPop1 _ t0 t1 t2 t3)) (sel-gempty-mk (GPop1)) (part-l t3))))
    ((GL0) (leaf-part g g e (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS0) (LS0) (LSE) (BPL) (BPN) (BPN) (BPN)))
    ((GL1) (leaf-part g g e (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS1) (LS1) (LSE) (BPN) (BPL) (BPN) (BPN)))
    ((GL2) (leaf-part g g e (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS2) (LS2) (LSE) (BPN) (BPN) (BPL) (BPN)))
    ((GL3) (leaf-part g g e (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS3) (LS3) (LSE) (BPN) (BPN) (BPN) (BPL)))
    ((GL01) (leaf-part g g e (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS01) (LS01) (LSE) (BPL) (BPL) (BPN) (BPN)))
    ((GL12) (leaf-part g g e (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS12) (LS12) (LSE) (BPN) (BPL) (BPL) (BPN)))
    ((GL13) (leaf-part g g e (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS13) (LS13) (LSE) (BPN) (BPL) (BPN) (BPL)))
    ((GL23) (leaf-part g g e (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse)
      (LS23) (LS23) (LSE) (BPN) (BPN) (BPL) (BPL)))
    ((GEmpty) (GPE))))

(def-fns _ $ (erased part-r : (erased (Gtree) g) -> (erased (GPart (GSG g) (GSG (GEmpty)) (GSG g)) p))
  (part-sym (GSG g) (GSG g) (GSG (GEmpty)) (part-l g)))

(def-fns _ $ (erased hits-one : (erased (List RC) r) (erased (Gsym) s) (erased (Hits r (Cons (Gsym) s (Nil (Gsym)))) h) ->
    (erased (List RC) r1) (erased (RJust s r r1) j) (erased (Hits r1 (Nil (Gsym))) h1))
  (let-match erased h (MkHits _ _ bs t _ el m mt))
  (let-match erased mt (MPCons _ bs2 e _ _ _ y mt1))
  (let-match erased mt1 (MPNil _))
  (let ((erased t2) (erased sl)) (sel-exists t e))
  (let ((erased r1)) (Cons RC (MkRx (Ctree) bs2 t2) (Nil RC)))
  (values r1 (RJCons s r (Nil RC) bs bs2 t t2 e el y sl (RJNil s r))
    (MkHits r1 (Nil _) bs2 t2 (Nil _) (ElHere RC (MkRx (Ctree) bs2 t2) (Nil RC)) (mem-sel t t2 e (Nil _) m sl) (MPNil bs2))))

(def-adts $ (BitHits : ((Bool) b) ((List RC) r) ((Gsym) s) -> Type)
  enum
  (many BHT : (erased (List RC) r) (erased (Gsym) s) (erased (Hits r (Cons (Gsym) s (Nil (Gsym)))) h) -> (BitHits (BTrue) r s))
  (many BHF : (erased (List RC) r) (erased (Gsym) s) -> (BitHits (BFalse) r s)))

(def-fns _ $ (erased leaf-hit-at : (erased (Gtree) l) (erased (Bool) l0 l1 l2 l3 b) (erased (List RC) r) (erased (Gsym) s)
    (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll) (erased (Pick4 (Bool) s l0 l1 l2 l3 b) pk) (erased (BitHits b r s) bh) ->
    (erased (GHitAt (GSG l) r s) res))
  (let-match erased bh (BHT _ _ h)
    ((BHF _ _)
      (MkGHitAt (GSG l) (GSG (GEmpty)) r (Nil RC) s (GSelL l l0 l1 l2 l3 b s (GSG (GEmpty)) ll pk (BSetF)) (RJNil s r) (GHE (Nil RC)))))
  (let ((erased r1) (erased j) (erased h1)) (hits-one r s h))
  (MkGHitAt (GSG l) (GSOne) r r1 s (GSelL l l0 l1 l2 l3 b s (GSOne) ll pk (BSetT)) j (GHOne r1 h1)))

(def-fns _ $ (erased leaf-hit : (erased (Gtree) l) (erased (Bool) l0 l1 l2 l3) (erased (List RC) r) (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll)
    (erased (BitHits l0 r (GPush)) h0) (erased (BitHits l1 r (GSkip)) h1) (erased (BitHits l2 r (GPop0)) h2) (erased (BitHits l3 r (GPop1)) h3) ->
    (erased (GHit (GSG l) r) res))
  (GHS l r (leaf-hit-at l l0 l1 l2 l3 l0 r (GPush) ll (PkPush _ l0 l1 l2 l3) h0) (leaf-hit-at l l0 l1 l2 l3 l1 r (GSkip) ll (PkSkip _ l0 l1 l2 l3) h1)
    (leaf-hit-at l l0 l1 l2 l3 l2 r (GPop0) ll (PkPop0 _ l0 l1 l2 l3) h2) (leaf-hit-at l l0 l1 l2 l3 l3 r (GPop1) ll (PkPop1 _ l0 l1 l2 l3) h3)))

(def-fns _ $ (erased node-ghit : (erased (Gtree) x0 x1 x2 x3) (erased (List RC) r r0 r1 r2 r3)
    (erased (RJust (GPush) r r0) j0) (erased (RJust (GSkip) r r1) j1) (erased (RJust (GPop0) r r2) j2) (erased (RJust (GPop1) r r3) j3)
    (erased (GHit (GSG x0) r0) h0) (erased (GHit (GSG x1) r1) h1) (erased (GHit (GSG x2) r2) h2) (erased (GHit (GSG x3) r3) h3) ->
    (erased (GHit (GSG (GNode x0 x1 x2 x3)) r) res))
  (let ((erased x)) (GSG (GNode x0 x1 x2 x3)))
  (GHS (GNode x0 x1 x2 x3) r
    (MkGHitAt x (GSG x0) r r0 (GPush) (GSelN x0 x1 x2 x3 x0 (GPush) (PkPush _ x0 x1 x2 x3)) j0 h0)
    (MkGHitAt x (GSG x1) r r1 (GSkip) (GSelN x0 x1 x2 x3 x1 (GSkip) (PkSkip _ x0 x1 x2 x3)) j1 h1)
    (MkGHitAt x (GSG x2) r r2 (GPop0) (GSelN x0 x1 x2 x3 x2 (GPop0) (PkPop0 _ x0 x1 x2 x3)) j2 h2)
    (MkGHitAt x (GSG x3) r r3 (GPop1) (GSelN x0 x1 x2 x3 x3 (GPop1) (PkPop1 _ x0 x1 x2 x3)) j3 h3)))

(def-fns _ $ (erased pat-hit-e : (erased (GSet) gs b) (erased (Gsym) s)
    (erased (GPartAt gs (GSG (GNode (GEmpty) (GEmpty) (GEmpty) (GEmpty))) b s) p) -> (erased (GPartAt gs (GSG (GEmpty)) b s) q))
  (let-match erased p (MkGPartAt _ _ _ g2 a2 b2 _ sg sa sb t))
  (let-match erased sa (GSelN _ _ _ _ _ _ pk) (absurd (GSelL _ _ _ _ _ _ _ _ l _ _) l))
  (let ((erased e)) (sel-gempty-mk s))
  (match erased pk _
    ((PkPush _ _ _ _ _) (MkGPartAt gs (GSG (GEmpty)) b g2 a2 b2 s sg e sb t))
    ((PkSkip _ _ _ _ _) (MkGPartAt gs (GSG (GEmpty)) b g2 a2 b2 s sg e sb t))
    ((PkPop0 _ _ _ _ _) (MkGPartAt gs (GSG (GEmpty)) b g2 a2 b2 s sg e sb t))
    ((PkPop1 _ _ _ _ _) (MkGPartAt gs (GSG (GEmpty)) b g2 a2 b2 s sg e sb t))))

(def-fns _ $ (erased part-hit-e : (erased (GSet) gs b) (erased (GPart gs (GSG (GNode (GEmpty) (GEmpty) (GEmpty) (GEmpty))) b) p) ->
    (erased (GPart gs (GSG (GEmpty)) b) q))
  (let-match erased p (GPS _ _ _ n x y rg ra rb s p0 p1 p2 p3))
  (let-match erased ra (GRG _))
  (GPS gs (GSG (GEmpty)) b n x y rg (GRG (GEmpty)) rb s (pat-hit-e gs b (GPush) p0) (pat-hit-e gs b (GSkip) p1) (pat-hit-e gs b (GPop0) p2)
    (pat-hit-e gs b (GPop1) p3)))

; a is the node of a0 to a3, or empty when all four are.
(def-adts $ (GCn : ((Gtree) a0) ((Gtree) a1) ((Gtree) a2) ((Gtree) a3) ((Gtree) a) -> Type)
  enum
  (many GCnE : -> (GCn (GEmpty) (GEmpty) (GEmpty) (GEmpty) (GEmpty)))
  (many GCnN : (erased (Gtree) a0 a1 a2 a3) -> (GCn a0 a1 a2 a3 (GNode a0 a1 a2 a3))))

(def-fns _ $ (erased bp-sym : (erased (Bool) l x y) (erased (BitPart l x y) p) -> (erased (BitPart l y x) q))
  (match erased p _ ((BPL) (BPR)) ((BPR) (BPL)) ((BPN) (BPN))))

(def-fns _ $ (erased leaf-sub : (erased (Gtree) l) (erased (Bool) l0 l1 l2 l3 x0 x1 x2 x3 y0 y1 y2 y3) (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll)
    (erased (BitPart l0 x0 y0) q0) (erased (BitPart l1 x1 y1) q1) (erased (BitPart l2 x2 y2) q2) (erased (BitPart l3 x3 y3) q3) ->
    (erased (Gtree) g) (erased (LeafSet g (MkBits x0 x1 x2 x3)) lg))
  (match erased ll _
    ((LSE) (let-match erased q0 (BPN)) (let-match erased q1 (BPN)) (let-match erased q2 (BPN)) (let-match erased q3 (BPN)) (values (GEmpty) (LSE)))
    ((LS0) (let-match erased q1 (BPN)) (let-match erased q2 (BPN)) (let-match erased q3 (BPN))
      (match erased q0 _ ((BPL) (values (GL0) (LS0))) ((BPR) (values (GEmpty) (LSE)))))
    ((LS1) (let-match erased q0 (BPN)) (let-match erased q2 (BPN)) (let-match erased q3 (BPN))
      (match erased q1 _ ((BPL) (values (GL1) (LS1))) ((BPR) (values (GEmpty) (LSE)))))
    ((LS2) (let-match erased q0 (BPN)) (let-match erased q1 (BPN)) (let-match erased q3 (BPN))
      (match erased q2 _ ((BPL) (values (GL2) (LS2))) ((BPR) (values (GEmpty) (LSE)))))
    ((LS3) (let-match erased q0 (BPN)) (let-match erased q1 (BPN)) (let-match erased q2 (BPN))
      (match erased q3 _ ((BPL) (values (GL3) (LS3))) ((BPR) (values (GEmpty) (LSE)))))
    ((LS01) (let-match erased q2 (BPN)) (let-match erased q3 (BPN))
      (match erased q0 _
        ((BPL) (match erased q1 _ ((BPL) (values (GL01) (LS01))) ((BPR) (values (GL0) (LS0)))))
        ((BPR) (match erased q1 _ ((BPL) (values (GL1) (LS1))) ((BPR) (values (GEmpty) (LSE)))))))
    ((LS12) (let-match erased q0 (BPN)) (let-match erased q3 (BPN))
      (match erased q1 _
        ((BPL) (match erased q2 _ ((BPL) (values (GL12) (LS12))) ((BPR) (values (GL1) (LS1)))))
        ((BPR) (match erased q2 _ ((BPL) (values (GL2) (LS2))) ((BPR) (values (GEmpty) (LSE)))))))
    ((LS13) (let-match erased q0 (BPN)) (let-match erased q2 (BPN))
      (match erased q1 _
        ((BPL) (match erased q3 _ ((BPL) (values (GL13) (LS13))) ((BPR) (values (GL1) (LS1)))))
        ((BPR) (match erased q3 _ ((BPL) (values (GL3) (LS3))) ((BPR) (values (GEmpty) (LSE)))))))
    ((LS23) (let-match erased q0 (BPN)) (let-match erased q1 (BPN))
      (match erased q2 _
        ((BPL) (match erased q3 _ ((BPL) (values (GL23) (LS23))) ((BPR) (values (GL2) (LS2)))))
        ((BPR) (match erased q3 _ ((BPL) (values (GL3) (LS3))) ((BPR) (values (GEmpty) (LSE)))))))))

(def-fns _ $ (erased part-cn : (erased (Gtree) t a0 a1 a2 a3 b0 b1 b2 b3 a b) (erased (GPart (GSG t) (GSG (GNode a0 a1 a2 a3)) (GSG (GNode b0 b1 b2 b3))) p)
    (erased (GCn a0 a1 a2 a3 a) ca) (erased (GCn b0 b1 b2 b3 b) cb) -> (erased (GPart (GSG t) (GSG a) (GSG b)) r))
  (let ((erased p1)) (match erased ca (((GPart (GSG t) (GSG a) (GSG (GNode b0 b1 b2 b3))) q)) ((GCnE) (part-hit-e (GSG t) _ p)) ((GCnN _ _ _ _) p)))
  (match erased cb _ ((GCnE) (part-sym (GSG t) _ _ (part-hit-e (GSG t) _ (part-sym (GSG t) _ _ p1)))) ((GCnN _ _ _ _) p1)))

(def-fns _ $ (erased ghit-cn : (erased (Gtree) a0 a1 a2 a3 a) (erased (List RC) r) (erased (GCn a0 a1 a2 a3 a) ca) (erased (GHit (GSG (GNode a0 a1 a2 a3)) r) h)
    -> (erased (GHit (GSG a) r) res))
  (match erased ca _ ((GCnE) (GHE r)) ((GCnN _ _ _ _) h)))
