
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
  (let-match erased j (RJCons _ _ r3 bs c t c2 e el1 y sl j1) (absurd (RJNil _ _) el))
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
        ((GHS g _ h0 h1 h2 h3)
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

(def-fns _ $ (erased ghit-sel : (erased (GSet) a a1) (erased (List RC) r) (erased (Gsym) s) (erased (GHit a r) h) (erased (GSel a s a1) sa) ->
    (erased (List RC) r1) (erased (RJust s r r1) j) (erased (GHit a1 r1) h1))
  (match erased h _
    ((GHE _) (let-match erased (sel-gempty s a1 sa) (Refl _ _)) (values (Nil RC) (RJNil s r) (GHE (Nil RC))))
    ((GHOne _ _) (let-match erased sa (GSelOne _)) (values (Nil RC) (RJNil s r) (GHE (Nil RC))))
    ((GHS g _ h0 h1 h2 h3)
      (let-match erased (match erased s (((GHitAt a r s) k)) ((GPush) h0) ((GSkip) h1) ((GPop0) h2) ((GPop1) h3))
        (MkGHitAt _ a2 _ r2 _ sa2 j h4))
      (let-match erased (gsel-fn a a1 a2 s sa sa2) (Refl _ _))
      (values r2 j h4))))

(def-fns _
  ((erased ghit-part : (erased (GSet) gs a) (erased (List RC) r) (subterm erased (GPart gs a (GSG (GEmpty))) p) (erased (GHit a r) h) ->
      (erased (GHit gs r) res))
    (match erased p _
      ((GPE) (GHE r))
      ((GPS _ _ _ n x y rg ra rb s p0 p1 p2 p3)
        (let-match erased rb (GRG _))
        (match erased gs _
          ((GSOne)
            (let-match erased rg (GROne))
            (let-match erased (add-fn x (Zero) x (Succ (Zero)) (add-zero-right x) s) (Refl _ _))
            (let-match erased ra (GROne))
            (let-match erased h (GHOne _ hs))
            (GHOne r hs))
          ((GSG g)
            (GHS g r (ghitat-part gs a r (GPush) p0 h) (ghitat-part gs a r (GSkip) p1 h) (ghitat-part gs a r (GPop0) p2 h)
              (ghitat-part gs a r (GPop1) p3 h)))))))
  ((erased ghitat-part : (erased (GSet) gs a) (erased (List RC) r) (erased (Gsym) s) (subterm erased (GPartAt gs a (GSG (GEmpty)) s) p)
      (erased (GHit a r) h) -> (erased (GHitAt gs r s) res))
    (let-match erased p (MkGPartAt _ _ _ g1 a1 b1 _ sg sa sb q))
    (let-match erased (sel-gempty s b1 sb) (Refl _ _))
    (let ((erased r1) (erased j) (erased h1)) (ghit-sel a a1 r s h sa))
    (MkGHitAt gs g1 r r1 s sg j (ghit-part g1 a1 r1 q h1))))

(def-fns _ $ (erased hits-one : (erased (List RC) r) (erased (Gsym) s) (erased (Hits r (Cons (Gsym) s (Nil (Gsym)))) h) ->
    (erased (List RC) r1) (erased (RJust s r r1) j) (erased (Hits r1 (Nil (Gsym))) h1))
  (let-match erased h (MkHits _ _ bs t et el m mt))
  (let-match erased mt (MPCons _ bs2 e _ et1 _ y mt1))
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
  (match erased bh _
    ((BHT _ _ h)
      (let ((erased r1) (erased j) (erased h1)) (hits-one r s h))
      (MkGHitAt (GSG l) (GSOne) r r1 s (GSelL l l0 l1 l2 l3 b s (GSOne) ll pk (BSetT)) j (GHOne r1 h1)))
    ((BHF _ _)
      (MkGHitAt (GSG l) (GSG (GEmpty)) r (Nil RC) s (GSelL l l0 l1 l2 l3 b s (GSG (GEmpty)) ll pk (BSetF)) (RJNil s r) (GHE (Nil RC))))))

(def-fns _ $ (erased leaf-hit : (erased (Gtree) l) (erased (Bool) l0 l1 l2 l3) (erased (List RC) r) (erased (LeafSet l (MkBits l0 l1 l2 l3)) ll)
    (erased (BitHits l0 r (GPush)) h0) (erased (BitHits l1 r (GSkip)) h1) (erased (BitHits l2 r (GPop0)) h2) (erased (BitHits l3 r (GPop1)) h3) ->
    (erased (GHit (GSG l) r) res))
  (GHS l r (leaf-hit-at l l0 l1 l2 l3 l0 r (GPush) ll (PkPush _ l0 l1 l2 l3) h0) (leaf-hit-at l l0 l1 l2 l3 l1 r (GSkip) ll (PkSkip _ l0 l1 l2 l3) h1)
    (leaf-hit-at l l0 l1 l2 l3 l2 r (GPop0) ll (PkPop0 _ l0 l1 l2 l3) h2) (leaf-hit-at l l0 l1 l2 l3 l3 r (GPop1) ll (PkPop1 _ l0 l1 l2 l3) h3)))

(def-fns _ $ (many gtree-live : (many (Gtree) t) -> (many (Bool) b))
  (match many t _ ((GEmpty) (BFalse)) (else (BTrue))))

(def-fns _ $ (many rx-cons : (many (Bool) w) (erased (Gsym) s) (erased (List RC) rr) (erased (Bstack) bs) (erased (Ctree) t) (erased (Col) e)
    (many (Bstack) bs2) (many (Ctree) t2) (many (List RC) acc)
    (erased (Elem RC (MkRx (Ctree) bs t) rr) el) (erased (Sym s bs e bs2) y) (erased (CtSel t e t2) sl) (erased (RJust s rr acc) j) ->
    (many (List RC) acc2) (erased (RJust s rr acc2) k))
  (let-match many w (BTrue) ((BFalse) (values acc j)))
  (match many t2 _
    ((CEmpty) (values acc j))
    (else (values (Cons _ (MkRx _ bs2 t2) acc) (RJCons s rr acc bs bs2 t t2 e el y sl j)))))

(def-fns _ $ (many grpop : (many (Bool) w2 w3) (erased (List RC) rr) (many (Bstack) bs) (erased (Ctree) t1) (many (Ctree) t2 t3) (many (List RC) r2 r3)
    (erased (Elem RC (MkRx (Ctree) bs (CNode t1 t2 t3)) rr) el) (erased (RJust (GPop0) rr r2) j2) (erased (RJust (GPop1) rr r3) j3) ->
    (many (List RC) a2 a3) (erased (RJust (GPop0) rr a2) k2) (erased (RJust (GPop1) rr a3) k3))
  (let ((erased t)) (CNode t1 t2 t3))
  (match many bs _
    ((BS0) (values r2 r3 j2 j3))
    ((BP0 b)
      (let ((many a2) (erased k2)) (rx-cons w2 (GPop0) rr bs t (C2) b t2 r2 el (SPop02 b) (SelN2 t1 t2 t3) j2))
      (let ((many a3) (erased k3)) (rx-cons w3 (GPop1) rr bs t (C3) b t3 r3 el (SPop13 b) (SelN3 t1 t2 t3) j3))
      (values a2 a3 k2 k3))
    ((BP1 b)
      (let ((many a2) (erased k2)) (rx-cons w2 (GPop0) rr bs t (C3) b t3 r2 el (SPop03 b) (SelN3 t1 t2 t3) j2))
      (let ((many a3) (erased k3)) (rx-cons w3 (GPop1) rr bs t (C2) b t2 r3 el (SPop12 b) (SelN2 t1 t2 t3) j3))
      (values a2 a3 k2 k3))))

(def-fns _ $ (many gtr-split-c : (many (Bool) w0 w1 w2 w3) (erased (List RC) rr) (many (List RC) r0 r1 r2 r3) (subterm many (List RC) r)
    (erased (Suffix RC r rr) sf) (erased (RJust (GPush) rr r0) j0) (erased (RJust (GSkip) rr r1) j1) (erased (RJust (GPop0) rr r2) j2)
    (erased (RJust (GPop1) rr r3) j3) ->
    (many (List RC) s0 s1 s2 s3) (erased (RJust (GPush) rr s0) k0) (erased (RJust (GSkip) rr s1) k1) (erased (RJust (GPop0) rr s2) k2)
    (erased (RJust (GPop1) rr s3) k3))
  (let-match many r (Cons _ x rest) ((Nil _) (values r0 r1 r2 r3 j0 j1 j2 j3)))
  (let ((erased sf1)) (SufNext RC x rest rr sf))
  (let-match many x (MkRx _ bs t))
  (let-match many t (CNode t1 t2 t3) (else (tail $ gtr-split-c w0 w1 w2 w3 rr r0 r1 r2 r3 rest sf1 j0 j1 j2 j3)))
  (let ((erased el)) (suffix-elem RC x r rr sf (ElHere RC x rest)))
  (let ((many a2) (many a3) (erased k2) (erased k3)) (grpop w2 w3 rr bs t1 t2 t3 r2 r3 el j2 j3))
  (let ((many c0) (erased q0)) (rx-cons w0 (GPush) rr bs t (C3) (BP1 bs) t3 r0 el (SPush3 bs) (SelN3 t1 t2 t3) j0))
  (let ((many d0) (erased l0)) (rx-cons w0 (GPush) rr bs t (C2) (BP0 bs) t2 c0 el (SPush2 bs) (SelN2 t1 t2 t3) q0))
  (let ((many d1) (erased l1)) (rx-cons w1 (GSkip) rr bs t (C1) bs t1 r1 el (SSkip bs) (SelN1 t1 t2 t3) j1))
  (tail $ gtr-split-c w0 w1 w2 w3 rr d0 d1 a2 a3 rest sf1 l0 l1 k2 k3))

(def-adts $ (Hit1 : ((Bstack) bs) ((Ctree) t) ((Gsym) s) -> Type)
  enum
  (many H1Yes : (erased (Bstack) bs) (erased (Ctree) t) (erased (Gsym) s) (erased (List (Col)) et) (erased (CtMem t et) m)
      (erased (MatchPG bs et (Cons (Gsym) s (Nil (Gsym)))) mt) -> (Hit1 bs t s))
  (many H1No : (erased (Bstack) bs) (erased (Ctree) t) (erased (Gsym) s) -> (Hit1 bs t s)))

(def-fns _ $ (many leaf-hit1 : (erased (Bstack) bs bs2) (erased (Ctree) t) (erased (Gsym) s) (erased (Col) e) (many (Ctree) c)
    (erased (CtSel t e c) sl) (erased (Sym s bs e bs2) y) -> (many (Hit1 bs t s) h))
  (match many c _
    ((CLeaf lf) (H1Yes bs t s (Cons _ e (Nil _)) (mem-cons t c e (Nil _) sl (leaf-mem lf)) (MPCons bs bs2 e s (Nil _) (Nil _) y (MPNil bs2))))
    (else (H1No bs t s))))

(def-fns _ $ (many sym-hit-c : (many (Gsym) s) (many (Bstack) bs) (many (Ctree) t) -> (many (Hit1 bs t s) h))
  (let-match many t (CNode t1 t2 t3) (else (H1No bs t s)))
  (match many s _
    ((GPush)
      (let-match many (leaf-hit1 bs (BP0 bs) t s (C2) t2 (SelN2 t1 t2 t3) (SPush2 bs)) (H1No _ _ _) ((H1Yes _ _ _ et m mt) (H1Yes bs t s et m mt)))
      (leaf-hit1 bs (BP1 bs) t s (C3) t3 (SelN3 t1 t2 t3) (SPush3 bs)))
    ((GSkip) (leaf-hit1 bs bs t s (C1) t1 (SelN1 t1 t2 t3) (SSkip bs)))
    ((GPop0)
      (match many bs _
        ((BS0) (H1No bs t s))
        ((BP0 b) (leaf-hit1 bs b t s (C2) t2 (SelN2 t1 t2 t3) (SPop02 b)))
        ((BP1 b) (leaf-hit1 bs b t s (C3) t3 (SelN3 t1 t2 t3) (SPop03 b)))))
    ((GPop1)
      (match many bs _
        ((BS0) (H1No bs t s))
        ((BP0 b) (leaf-hit1 bs b t s (C3) t3 (SelN3 t1 t2 t3) (SPop13 b)))
        ((BP1 b) (leaf-hit1 bs b t s (C2) t2 (SelN2 t1 t2 t3) (SPop12 b)))))))

(def-adts $ (HitRes : ((List RC) r) ((Gsym) s) -> Type)
  enum
  (many HYes : (erased (List RC) r) (erased (Gsym) s) (erased (Hits r (Cons (Gsym) s (Nil (Gsym)))) h) -> (HitRes r s))
  (many HNo : (erased (List RC) r) (erased (Gsym) s) -> (HitRes r s)))

(def-fns _ $ (many gtr-match-c : (many (Gsym) s) (erased (List RC) rr) (subterm many (List RC) r) (erased (Suffix RC r rr) sf) -> (many (HitRes rr s) res))
  (let-match many r (Cons _ x rest) ((Nil _) (HNo rr s)))
  (let-match many x (MkRx _ bs t))
  (match many (sym-hit-c s bs t) _
    ((H1Yes _ _ _ et m mt) (HYes rr s (MkHits rr (Cons _ s (Nil _)) bs t et (suffix-elem RC x r rr sf (ElHere RC x rest)) m mt)))
    ((H1No _ _ _) (tail $ gtr-match-c s rr rest (SufNext RC x rest rr sf)))))


(def-adts $ (Empty4 : ((Gtree) a) ((Gtree) b) ((Gtree) c) ((Gtree) d) -> Type)
  enum
  (many E4Yes : -> (Empty4 (GEmpty) (GEmpty) (GEmpty) (GEmpty)))
  (many E4No : (erased (Gtree) a b c d) -> (Empty4 a b c d)))

(def-fns _ $ (many gtree-empty4 : (many (Gtree) a b c d) -> (many (Empty4 a b c d) r))
  (let-match many a (GEmpty) (else (E4No a b c d)))
  (let-match many b (GEmpty) (else (E4No a b c d)))
  (let-match many c (GEmpty) (else (E4No a b c d)))
  (let-match many d (GEmpty) (else (E4No a b c d)))
  (E4Yes))

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

(def-fns _ $ (many gleaf-restrict-c : (many (Gtree) t) (many (List RC) r) ->
    (many (Gtree) hit miss) (erased (GPart (GSG t) (GSG hit) (GSG miss)) p) (erased (GHit (GSG hit) r) h))
  (let ((erased sf)) (SufHere RC r))
  (match many t _
    ((GL0) (match many (gtr-match-c (GPush) r r sf) _
      ((HYes _ _ h0) (values t (GEmpty) (part-l t) (leaf-hit t (BTrue) (BFalse) (BFalse) (BFalse) r (LS0) (BHT r (GPush) h0) (BHF r (GSkip)) (BHF r (GPop0)) (BHF r (GPop1)))))
      ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))
    ((GL1) (match many (gtr-match-c (GSkip) r r sf) _
      ((HYes _ _ h1) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BTrue) (BFalse) (BFalse) r (LS1) (BHF r (GPush)) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHF r (GPop1)))))
      ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))
    ((GL2) (match many (gtr-match-c (GPop0) r r sf) _
      ((HYes _ _ h2) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BFalse) (BTrue) (BFalse) r (LS2) (BHF r (GPush)) (BHF r (GSkip)) (BHT r (GPop0) h2) (BHF r (GPop1)))))
      ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))
    ((GL3) (match many (gtr-match-c (GPop1) r r sf) _
      ((HYes _ _ h3) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BFalse) (BFalse) (BTrue) r (LS3) (BHF r (GPush)) (BHF r (GSkip)) (BHF r (GPop0)) (BHT r (GPop1) h3))))
      ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))
    ((GL01)
      (match many (gtr-match-c (GPush) r r sf) _
        ((HYes _ _ h0)
          (match many (gtr-match-c (GSkip) r r sf) _
            ((HYes _ _ h1) (values t (GEmpty) (part-l t) (leaf-hit t (BTrue) (BTrue) (BFalse) (BFalse) r (LS01) (BHT r (GPush) h0) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHF r (GPop1)))))
            ((HNo _ _) (values (GL0) (GL1)
              (leaf-part t (GL0) (GL1) (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (LS01) (LS0) (LS1) (BPL) (BPR) (BPN) (BPN))
              (leaf-hit (GL0) (BTrue) (BFalse) (BFalse) (BFalse) r (LS0) (BHT r (GPush) h0) (BHF r (GSkip)) (BHF r (GPop0)) (BHF r (GPop1)))))))
        ((HNo _ _)
          (match many (gtr-match-c (GSkip) r r sf) _
            ((HYes _ _ h1) (values (GL1) (GL0)
              (leaf-part t (GL1) (GL0) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (LS01) (LS1) (LS0) (BPR) (BPL) (BPN) (BPN))
              (leaf-hit (GL1) (BFalse) (BTrue) (BFalse) (BFalse) r (LS1) (BHF r (GPush)) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHF r (GPop1)))))
            ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))))
    ((GL12)
      (match many (gtr-match-c (GSkip) r r sf) _
        ((HYes _ _ h1)
          (match many (gtr-match-c (GPop0) r r sf) _
            ((HYes _ _ h2) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BTrue) (BTrue) (BFalse) r (LS12) (BHF r (GPush)) (BHT r (GSkip) h1) (BHT r (GPop0) h2) (BHF r (GPop1)))))
            ((HNo _ _) (values (GL1) (GL2)
              (leaf-part t (GL1) (GL2) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (LS12) (LS1) (LS2) (BPN) (BPL) (BPR) (BPN))
              (leaf-hit (GL1) (BFalse) (BTrue) (BFalse) (BFalse) r (LS1) (BHF r (GPush)) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHF r (GPop1)))))))
        ((HNo _ _)
          (match many (gtr-match-c (GPop0) r r sf) _
            ((HYes _ _ h2) (values (GL2) (GL1)
              (leaf-part t (GL2) (GL1) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (LS12) (LS2) (LS1) (BPN) (BPR) (BPL) (BPN))
              (leaf-hit (GL2) (BFalse) (BFalse) (BTrue) (BFalse) r (LS2) (BHF r (GPush)) (BHF r (GSkip)) (BHT r (GPop0) h2) (BHF r (GPop1)))))
            ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))))
    ((GL13)
      (match many (gtr-match-c (GSkip) r r sf) _
        ((HYes _ _ h1)
          (match many (gtr-match-c (GPop1) r r sf) _
            ((HYes _ _ h3) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BTrue) (BFalse) (BTrue) r (LS13) (BHF r (GPush)) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHT r (GPop1) h3))))
            ((HNo _ _) (values (GL1) (GL3)
              (leaf-part t (GL1) (GL3) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BFalse) (BTrue) (LS13) (LS1) (LS3) (BPN) (BPL) (BPN) (BPR))
              (leaf-hit (GL1) (BFalse) (BTrue) (BFalse) (BFalse) r (LS1) (BHF r (GPush)) (BHT r (GSkip) h1) (BHF r (GPop0)) (BHF r (GPop1)))))))
        ((HNo _ _)
          (match many (gtr-match-c (GPop1) r r sf) _
            ((HYes _ _ h3) (values (GL3) (GL1)
              (leaf-part t (GL3) (GL1) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BTrue) (BFalse) (BFalse) (LS13) (LS3) (LS1) (BPN) (BPR) (BPN) (BPL))
              (leaf-hit (GL3) (BFalse) (BFalse) (BFalse) (BTrue) r (LS3) (BHF r (GPush)) (BHF r (GSkip)) (BHF r (GPop0)) (BHT r (GPop1) h3))))
            ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))))
    ((GL23)
      (match many (gtr-match-c (GPop0) r r sf) _
        ((HYes _ _ h2)
          (match many (gtr-match-c (GPop1) r r sf) _
            ((HYes _ _ h3) (values t (GEmpty) (part-l t) (leaf-hit t (BFalse) (BFalse) (BTrue) (BTrue) r (LS23) (BHF r (GPush)) (BHF r (GSkip)) (BHT r (GPop0) h2) (BHT r (GPop1) h3))))
            ((HNo _ _) (values (GL2) (GL3)
              (leaf-part t (GL2) (GL3) (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BFalse) (BFalse) (BTrue) (LS23) (LS2) (LS3) (BPN) (BPN) (BPL) (BPR))
              (leaf-hit (GL2) (BFalse) (BFalse) (BTrue) (BFalse) r (LS2) (BHF r (GPush)) (BHF r (GSkip)) (BHT r (GPop0) h2) (BHF r (GPop1)))))))
        ((HNo _ _)
          (match many (gtr-match-c (GPop1) r r sf) _
            ((HYes _ _ h3) (values (GL3) (GL2)
              (leaf-part t (GL3) (GL2) (BFalse) (BFalse) (BTrue) (BTrue) (BFalse) (BFalse) (BFalse) (BTrue) (BFalse) (BFalse) (BTrue) (BFalse) (LS23) (LS3) (LS2) (BPN) (BPN) (BPR) (BPL))
              (leaf-hit (GL3) (BFalse) (BFalse) (BFalse) (BTrue) r (LS3) (BHF r (GPush)) (BHF r (GSkip)) (BHF r (GPop0)) (BHT r (GPop1) h3))))
            ((HNo _ _) (values (GEmpty) t (part-r t) (GHE r)))))))
    (else (values (GEmpty) t (part-r t) (GHE r)))))

(def-fns _ $ (many gtree-restrict-c : (subterm many (Gtree) t) (many (List RC) r) ->
    (many (Gtree) hit miss) (erased (GPart (GSG t) (GSG hit) (GSG miss)) p) (erased (GHit (GSG hit) r) h))
  (let-match many r (Cons _ _ _) ((Nil _) (values (GEmpty) t (part-r t) (GHE r))))
  (let-match many t (GNode t0 t1 t2 t3) (else (gleaf-restrict-c t r)))
  (let ((many r0) (many r1) (many r2) (many r3) (erased j0) (erased j1) (erased j2) (erased j3))
    (gtr-split-c (gtree-live t0) (gtree-live t1) (gtree-live t2) (gtree-live t3) r (Nil _) (Nil _) (Nil _) (Nil _) r (SufHere RC r) (RJNil (GPush) r) (RJNil (GSkip) r) (RJNil (GPop0) r) (RJNil (GPop1) r)))
  (let ((many a0) (many b0) (erased p0) (erased h0)) (notail $ gtree-restrict-c t0 r0))
  (let ((many a1) (many b1) (erased p1) (erased h1)) (notail $ gtree-restrict-c t1 r1))
  (let ((many a2) (many b2) (erased p2) (erased h2)) (notail $ gtree-restrict-c t2 r2))
  (let ((many a3) (many b3) (erased p3) (erased h3)) (notail $ gtree-restrict-c t3 r3))
  (let-match many (gtree-empty4 a0 a1 a2 a3) (E4No _ _ _ _) ((E4Yes) (values (GEmpty) t (part-r t) (GHE r))))
  (let-match many (gtree-empty4 b0 b1 b2 b3) (E4No _ _ _ _)
    ((E4Yes) (values t (GEmpty) (part-l t)
      (node-ghit t0 t1 t2 t3 r r0 r1 r2 r3 j0 j1 j2 j3 (ghit-part (GSG t0) (GSG a0) r0 p0 h0) (ghit-part (GSG t1) (GSG a1) r1 p1 h1)
        (ghit-part (GSG t2) (GSG a2) r2 p2 h2) (ghit-part (GSG t3) (GSG a3) r3 p3 h3)))))
  (values (GNode a0 a1 a2 a3) (GNode b0 b1 b2 b3) (node-part t0 t1 t2 t3 a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3)
    (node-ghit a0 a1 a2 a3 r r0 r1 r2 r3 j0 j1 j2 j3 h0 h1 h2 h3)))

(def-fns _ $ (erased pat-hit-e : (erased (GSet) gs b) (erased (Gsym) s)
    (erased (GPartAt gs (GSG (GNode (GEmpty) (GEmpty) (GEmpty) (GEmpty))) b s) p) -> (erased (GPartAt gs (GSG (GEmpty)) b s) q))
  (let-match erased p (MkGPartAt _ _ _ g2 a2 b2 _ sg sa sb t))
  (let-match erased sa (GSelN _ _ _ _ u _ pk) (absurd (GSelL _ _ _ _ _ _ _ _ l _ _) l))
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

; A gtree whose nodes are held unique, so that gtree-restrict-u rewrites them in place; UGLeaf holds any gtree as it is.
(def-adts $ (UGtree : -> Type)
  enum
  (many UGNode : (unique (UGtree) x0 x1 x2 x3) -> (UGtree))
  (many UGLeaf : (many (Gtree) g) -> (UGtree))
  (many UGEmpty : -> (UGtree)))

; u holds g.
(def-adts $ (UG : ((UGtree) u) ((Gtree) g) -> Type)
  enum
  (many UGE : -> (UG (UGEmpty) (GEmpty)))
  (many UGL : (erased (Gtree) g) -> (UG (UGLeaf g) g))
  (many UGN : (erased (UGtree) x0 x1 x2 x3) (erased (Gtree) g0 g1 g2 g3) (erased (UG x0 g0) p0) (erased (UG x1 g1) p1) (erased (UG x2 g2) p2)
      (erased (UG x3 g3) p3) -> (UG (UGNode x0 x1 x2 x3) (GNode g0 g1 g2 g3))))

(def-adts $ (GKeep : ((Gtree) g) -> Type)
  enum
  (many GKEmpty : -> (GKeep (GEmpty)))
  (many GKLive : (erased (Gtree) g) -> (GKeep g)))

(def-fns _ $ (many gkeep : (many (Gtree) g) -> (many (GKeep g) k))
  (match many g _ ((GEmpty) (GKEmpty)) (else (GKLive g))))

(def-fns _ $ (many gkeep4 : (erased (Gtree) a b c d) (many (GKeep a) w) (many (GKeep b) x) (many (GKeep c) y) (many (GKeep d) z) ->
    (many (Empty4 a b c d) r))
  (let-match many w (GKEmpty) (else (E4No a b c d)))
  (let-match many x (GKEmpty) (else (E4No a b c d)))
  (let-match many y (GKEmpty) (else (E4No a b c d)))
  (let-match many z (GKEmpty) (else (E4No a b c d)))
  (E4Yes))

(def-fns _ $ (many ug-of : (subterm many (Gtree) g) -> (unique (UGtree) u) (erased (UG u g) p) (many (GKeep g) e))
  (let-match many g (GNode t0 t1 t2 t3) ((GEmpty) (values (UGEmpty) (UGE) (GKEmpty))) (else (values (UGLeaf g) (UGL g) (GKLive g))))
  (let ((unique x0) (erased p0) (many _)) (notail $ ug-of t0))
  (let ((unique x1) (erased p1) (many _)) (notail $ ug-of t1))
  (let ((unique x2) (erased p2) (many _)) (notail $ ug-of t2))
  (let ((unique x3) (erased p3) (many _)) (notail $ ug-of t3))
  (values (UGNode x0 x1 x2 x3) (UGN x0 x1 x2 x3 t0 t1 t2 t3 p0 p1 p2 p3) (GKLive g)))

(def-fns _ $ (many gt-of : (subterm unique (UGtree) u) (erased (Gtree) g) (erased (UG u g) p) -> (many g is c))
  (match unique u _
    ((UGEmpty) (let-match erased p (UGE)) (GEmpty))
    ((UGLeaf g1) (let-match erased p (UGL _)) g1)
    ((UGNode x0 x1 x2 x3)
      (let-match erased p (UGN _ _ _ _ g0 g1 g2 g3 p0 p1 p2 p3))
      (let ((many c0)) (notail $ gt-of x0 g0 p0))
      (let ((many c1)) (notail $ gt-of x1 g1 p1))
      (let ((many c2)) (notail $ gt-of x2 g2 p2))
      (let ((many c3)) (notail $ gt-of x3 g3 p3))
      (GNode c0 c1 c2 c3))))

(def-fns _ $ (many ug-live : (unique (UGtree) u) -> (unique u is u2) (many (Bool) w))
  (match unique u _
    ((UGEmpty) (values (UGEmpty) (BFalse)))
    ((UGLeaf g cell) (values (at unique (cell g)) (gtree-live g)))
    ((UGNode x0 x1 x2 x3 cell) (values (at unique (cell x0 x1 x2 x3)) (BTrue)))))

(def-fns _ $ (many gtree-restrict-u : (subterm unique (UGtree) u) (erased (Gtree) t) (erased (UG u t) ut) (many (List RC) r) ->
    (many (Gtree) hit) (unique (UGtree) mu) (erased (Gtree) miss) (erased (UG mu miss) um) (erased (GPart (GSG t) (GSG hit) (GSG miss)) p)
    (erased (GHit (GSG hit) r) h) (many (GKeep miss) e))
  (match unique u _
    ((UGEmpty) (let-match erased ut (UGE)) (values (GEmpty) (UGEmpty) (GEmpty) (UGE) (part-r t) (GHE r) (GKEmpty)))
    ((UGLeaf g cell)
      (let-match erased ut (UGL _))
      (let ((many a) (many b) (erased p) (erased h)) (gtree-restrict-c g r))
      (values a (cell b) b (UGL b) p h (gkeep b)))
    ((UGNode x0 x1 x2 x3 cell)
      (let-match erased ut (UGN _ _ _ _ t0 t1 t2 t3 q0 q1 q2 q3))
      (let-match many r (Cons _ _ _) ((Nil _) (values (GEmpty) (at unique (cell x0 x1 x2 x3)) t ut (part-r t) (GHE r) (GKLive t))))
      (let ((unique y0) (many w0)) (ug-live x0))
      (let ((unique y1) (many w1)) (ug-live x1))
      (let ((unique y2) (many w2)) (ug-live x2))
      (let ((unique y3) (many w3)) (ug-live x3))
      (let ((many r0) (many r1) (many r2) (many r3) (erased j0) (erased j1) (erased j2) (erased j3))
        (gtr-split-c w0 w1 w2 w3 r (Nil _) (Nil _) (Nil _) (Nil _) r (SufHere RC r) (RJNil (GPush) r) (RJNil (GSkip) r) (RJNil (GPop0) r) (RJNil (GPop1) r)))
      (let ((many a0) (unique z0) (erased b0) (erased m0) (erased p0) (erased h0) (many e0)) (notail $ gtree-restrict-u y0 t0 q0 r0))
      (let ((many a1) (unique z1) (erased b1) (erased m1) (erased p1) (erased h1) (many e1)) (notail $ gtree-restrict-u y1 t1 q1 r1))
      (let ((many a2) (unique z2) (erased b2) (erased m2) (erased p2) (erased h2) (many e2)) (notail $ gtree-restrict-u y2 t2 q2 r2))
      (let ((many a3) (unique z3) (erased b3) (erased m3) (erased p3) (erased h3) (many e3)) (notail $ gtree-restrict-u y3 t3 q3 r3))
      (let ((erased pt)) (node-part t0 t1 t2 t3 a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3))
      (let ((erased mg)) (UGN z0 z1 z2 z3 b0 b1 b2 b3 m0 m1 m2 m3))
      (let-match many (gtree-empty4 a0 a1 a2 a3) (E4No _ _ _ _)
        ((E4Yes) (values (GEmpty) (cell z0 z1 z2 z3) (GNode b0 b1 b2 b3) mg (part-hit-e (GSG t) _ pt) (GHE r) (GKLive (GNode b0 b1 b2 b3)))))
      (let ((erased hs)) (node-ghit a0 a1 a2 a3 r r0 r1 r2 r3 j0 j1 j2 j3 h0 h1 h2 h3))
      (let-match many (gkeep4 b0 b1 b2 b3 e0 e1 e2 e3) (E4No _ _ _ _)
        ((E4Yes) (values (GNode a0 a1 a2 a3) (UGEmpty) (GEmpty) (UGE) (part-sym (GSG t) _ _ (part-hit-e (GSG t) _ (part-sym (GSG t) _ _ pt))) hs (GKEmpty))))
      (values (GNode a0 a1 a2 a3) (cell z0 z1 z2 z3) (GNode b0 b1 b2 b3) mg pt hs (GKLive (GNode b0 b1 b2 b3))))))
