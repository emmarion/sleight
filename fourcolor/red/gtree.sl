; A set of partial chromograms: those of a gtree, or the set holding only the empty one.
(def-adts $ (GSet : -> Type)
  enum
  (many GSG : (many (Gtree) g) -> (GSet))
  (many GSOne : -> (GSet)))

(def-adts $ (Pick4 : (Type A) ((Gsym) s) (A x0) (A x1) (A x2) (A x3) (A x) -> Type)
  enum
  (many PkPush : (erased Type A) (erased A x0 x1 x2 x3) -> (Pick4 A (GPush) x0 x1 x2 x3 x0))
  (many PkSkip : (erased Type A) (erased A x0 x1 x2 x3) -> (Pick4 A (GSkip) x0 x1 x2 x3 x1))
  (many PkPop0 : (erased Type A) (erased A x0 x1 x2 x3) -> (Pick4 A (GPop0) x0 x1 x2 x3 x2))
  (many PkPop1 : (erased Type A) (erased A x0 x1 x2 x3) -> (Pick4 A (GPop1) x0 x1 x2 x3 x3)))

; The one-symbol chromograms a gtree leaf holds, flagged in the order GPush GSkip GPop0 GPop1.
(def-adts $ (Bits : -> Type)
  enum
  (many MkBits : (many (Bool) b0 b1 b2 b3) -> (Bits)))

(def-adts $ (LeafSet : ((Gtree) g) ((Bits) q) -> Type)
  enum
  (many LS0 : -> (LeafSet (GL0) (MkBits (BTrue) (BFalse) (BFalse) (BFalse))))
  (many LS1 : -> (LeafSet (GL1) (MkBits (BFalse) (BTrue) (BFalse) (BFalse))))
  (many LS2 : -> (LeafSet (GL2) (MkBits (BFalse) (BFalse) (BTrue) (BFalse))))
  (many LS3 : -> (LeafSet (GL3) (MkBits (BFalse) (BFalse) (BFalse) (BTrue))))
  (many LS01 : -> (LeafSet (GL01) (MkBits (BTrue) (BTrue) (BFalse) (BFalse))))
  (many LS12 : -> (LeafSet (GL12) (MkBits (BFalse) (BTrue) (BTrue) (BFalse))))
  (many LS13 : -> (LeafSet (GL13) (MkBits (BFalse) (BTrue) (BFalse) (BTrue))))
  (many LS23 : -> (LeafSet (GL23) (MkBits (BFalse) (BFalse) (BTrue) (BTrue))))
  (many LSE : -> (LeafSet (GEmpty) (MkBits (BFalse) (BFalse) (BFalse) (BFalse)))))

(def-adts $ (BSet : ((Bool) b) ((GSet) gs) -> Type)
  enum
  (many BSetT : -> (BSet (BTrue) (GSOne)))
  (many BSetF : -> (BSet (BFalse) (GSG (GEmpty)))))

; The chromograms w such that s :: w is in gs.
(def-adts $ (GSel : ((GSet) gs) ((Gsym) s) ((GSet) gs2) -> Type)
  enum
  (many GSelN : (erased (Gtree) t0 t1 t2 t3 u) (erased (Gsym) s) (erased (Pick4 (Gtree) s t0 t1 t2 t3 u) p)
      -> (GSel (GSG (GNode t0 t1 t2 t3)) s (GSG u)))
  (many GSelL : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3 b) (erased (Gsym) s) (erased (GSet) gs)
      (erased (LeafSet g (MkBits b0 b1 b2 b3)) l) (erased (Pick4 (Bool) s b0 b1 b2 b3 b) p) (erased (BSet b gs) q)
      -> (GSel (GSG g) s gs))
  (many GSelOne : (erased (Gsym) s) -> (GSel (GSOne) s (GSG (GEmpty)))))

(def-adts $ (GRoot : ((GSet) gs) ((Nat) n) -> Type)
  enum
  (many GROne : -> (GRoot (GSOne) (Succ (Zero))))
  (many GRG : (erased (Gtree) g) -> (GRoot (GSG g) (Zero))))

(def-adts $ (GMem : ((GSet) gs) ((List (Gsym)) w) -> Type)
  enum
  (many GMNil : -> (GMem (GSOne) (Nil (Gsym))))
  (many GMCons : (erased (GSet) gs gs2) (erased (Gsym) s) (erased (List (Gsym)) w) (erased (GSel gs s gs2) p) (erased (GMem gs2 w) q)
      -> (GMem gs (Cons (Gsym) s w))))

(def-adts $ (Popped : ((Bstack) bs) ((Bstack) b) -> Type)
  enum
  (many Popped0 : (erased (Bstack) b) -> (Popped (BP0 b) b))
  (many Popped1 : (erased (Bstack) b) -> (Popped (BP1 b) b)))

; After match_count of gtree.v: n chromograms of gs match et from the stack bs.
(def-adts $ (MC : ((GSet) gs) ((Bstack) bs) ((List (Col)) et) ((Nat) n) -> Type)
  enum
  (many MCNil : (erased (GSet) gs) (erased (Bstack) bs) (erased (Nat) n) (erased (GRoot gs n) p) -> (MC gs bs (Nil (Col)) n))
  (many MC0 : (erased (GSet) gs) (erased (Bstack) bs) (erased (List (Col)) et) -> (MC gs bs (Cons (Col) (C0) et) (Zero)))
  (many MCSkip : (erased (GSet) gs g1) (erased (Bstack) bs) (erased (List (Col)) et) (erased (Nat) n) (erased (GSel gs (GSkip) g1) p)
      (erased (MC g1 bs et n) q) -> (MC gs bs (Cons (Col) (C1) et) n))
  (many MCPush : (erased (GSet) gs g1) (erased (Bstack) bs1) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n)
      (erased (Sym (GPush) (BS0) e bs1) y) (erased (GSel gs (GPush) g1) p) (erased (MC g1 bs1 et n) q)
      -> (MC gs (BS0) (Cons (Col) e et) n))
  (many MCPP : (erased (GSet) gs g1 g2) (erased (Bstack) bs b bs1) (erased (Gsym) s) (erased (Col) e) (erased (List (Col)) et)
      (erased (Nat) n1 n2 n) (erased (Popped bs b) pp) (erased (Sym (GPush) bs e bs1) y1) (erased (GSel gs (GPush) g1) p1)
      (erased (MC g1 bs1 et n1) q1) (erased (Sym s bs e b) y2) (erased (GSel gs s g2) p2) (erased (MC g2 b et n2) q2)
      (erased (Add n1 n2 n) a) -> (MC gs bs (Cons (Col) e et) n)))

; a and b partition gs (after sgtree_partition of gtree.v).
(def-adts
  ((GPart : ((GSet) gs) ((GSet) a) ((GSet) b) -> Type)
    enum
    (many GPE : -> (GPart (GSG (GEmpty)) (GSG (GEmpty)) (GSG (GEmpty))))
    (many GPS : (erased (GSet) gs a b) (erased (Nat) n x y) (erased (GRoot gs n) rg) (erased (GRoot a x) ra) (erased (GRoot b y) rb)
        (erased (Add x y n) s) (erased (GPartAt gs a b (GPush)) p0) (erased (GPartAt gs a b (GSkip)) p1)
        (erased (GPartAt gs a b (GPop0)) p2) (erased (GPartAt gs a b (GPop1)) p3) -> (GPart gs a b)))
  ((GPartAt : ((GSet) gs) ((GSet) a) ((GSet) b) ((Gsym) s) -> Type)
    enum
    (many MkGPartAt : (erased (GSet) gs a b gs2 a2 b2) (erased (Gsym) s) (erased (GSel gs s gs2) p) (erased (GSel a s a2) q)
        (erased (GSel b s b2) r) (erased (GPart gs2 a2 b2) t) -> (GPartAt gs a b s))))

(def-fns _ $ (erased pick4-fn : (erased Type A) (erased (Gsym) s) (erased A x0 x1 x2 x3 x y)
    (erased (Pick4 A s x0 x1 x2 x3 x) p) (erased (Pick4 A s x0 x1 x2 x3 y) q) -> (erased (Eq A x y) e))
  (match erased p _
    ((PkPush _ _ _ _ _) (let-match erased q (PkPush _ _ _ _ _)) (Refl _ x))
    ((PkSkip _ _ _ _ _) (let-match erased q (PkSkip _ _ _ _ _)) (Refl _ x))
    ((PkPop0 _ _ _ _ _) (let-match erased q (PkPop0 _ _ _ _ _)) (Refl _ x))
    ((PkPop1 _ _ _ _ _) (let-match erased q (PkPop1 _ _ _ _ _)) (Refl _ x))))

(def-fns _ $ (erased pick4-exists : (erased Type A) (erased (Gsym) s) (erased A x0 x1 x2 x3) -> (erased A x) (erased (Pick4 A s x0 x1 x2 x3 x) p))
  (match erased s _
    ((GPush) (values x0 (PkPush A x0 x1 x2 x3)))
    ((GSkip) (values x1 (PkSkip A x0 x1 x2 x3)))
    ((GPop0) (values x2 (PkPop0 A x0 x1 x2 x3)))
    ((GPop1) (values x3 (PkPop1 A x0 x1 x2 x3)))))

(def-fns _ $ (erased bset-exists : (erased (Bool) b) -> (erased (GSet) gs) (erased (BSet b gs) p))
  (match erased b _ ((BTrue) (values (GSOne) (BSetT))) ((BFalse) (values (GSG (GEmpty)) (BSetF)))))

(def-fns _ $ (erased bset-fn : (erased (Bool) b) (erased (GSet) u v) (erased (BSet b u) p) (erased (BSet b v) q) -> (erased (Eq (GSet) u v) e))
  (match erased p _
    ((BSetT) (let-match erased q (BSetT)) (Refl _ u))
    ((BSetF) (let-match erased q (BSetF)) (Refl _ u))))

(def-fns _ $ (erased leaf-sel : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3) (erased (Gsym) s) (erased (LeafSet g (MkBits b0 b1 b2 b3)) l) ->
    (erased (GSet) gs) (erased (GSel (GSG g) s gs) p))
  (let ((erased b) (erased pk)) (pick4-exists (Bool) s b0 b1 b2 b3))
  (let ((erased gs) (erased q)) (bset-exists b))
  (values gs (GSelL g b0 b1 b2 b3 b s gs l pk q)))

(def-fns _ $ (erased gsel-exists : (erased (GSet) gs) (erased (Gsym) s) -> (erased (GSet) gs2) (erased (GSel gs s gs2) p))
  (let-match erased gs (GSG g) ((GSOne) (values (GSG (GEmpty)) (GSelOne s))))
  (let-match erased g (GNode t0 t1 t2 t3)
    ((GL0) (leaf-sel g (BTrue) (BFalse) (BFalse) (BFalse) s (LS0)))
    ((GL1) (leaf-sel g (BFalse) (BTrue) (BFalse) (BFalse) s (LS1)))
    ((GL2) (leaf-sel g (BFalse) (BFalse) (BTrue) (BFalse) s (LS2)))
    ((GL3) (leaf-sel g (BFalse) (BFalse) (BFalse) (BTrue) s (LS3)))
    ((GL01) (leaf-sel g (BTrue) (BTrue) (BFalse) (BFalse) s (LS01)))
    ((GL12) (leaf-sel g (BFalse) (BTrue) (BTrue) (BFalse) s (LS12)))
    ((GL13) (leaf-sel g (BFalse) (BTrue) (BFalse) (BTrue) s (LS13)))
    ((GL23) (leaf-sel g (BFalse) (BFalse) (BTrue) (BTrue) s (LS23)))
    ((GEmpty) (leaf-sel g (BFalse) (BFalse) (BFalse) (BFalse) s (LSE))))
  (let ((erased u) (erased p)) (pick4-exists (Gtree) s t0 t1 t2 t3))
  (values (GSG u) (GSelN t0 t1 t2 t3 u s p)))

(def-fns _ $ (erased leafset-fn : (erased (Gtree) g) (erased (Bits) q r) (erased (LeafSet g q) la) (erased (LeafSet g r) lb) ->
    (erased (Eq (Bits) q r) e))
  (match erased la _
    ((LS0) (let-match erased lb (LS0)) (Refl _ q))
    ((LS1) (let-match erased lb (LS1)) (Refl _ q))
    ((LS2) (let-match erased lb (LS2)) (Refl _ q))
    ((LS3) (let-match erased lb (LS3)) (Refl _ q))
    ((LS01) (let-match erased lb (LS01)) (Refl _ q))
    ((LS12) (let-match erased lb (LS12)) (Refl _ q))
    ((LS13) (let-match erased lb (LS13)) (Refl _ q))
    ((LS23) (let-match erased lb (LS23)) (Refl _ q))
    ((LSE) (let-match erased lb (LSE)) (Refl _ q))))

(def-fns _ $ (erased gsel-fn : (erased (GSet) gs u v) (erased (Gsym) s) (erased (GSel gs s u) p) (erased (GSel gs s v) q) ->
    (erased (Eq (GSet) u v) e))
  (match erased p _
    ((GSelN t0 t1 t2 t3 a _ pa)
      (let-match erased q (GSelN _ _ _ _ b _ pb) (absurd (GSelL _ c0 c1 c2 c3 c _ _ lb pb bb) lb))
      (let-match erased (pick4-fn (Gtree) s t0 t1 t2 t3 a b pa pb) (Refl _ _))
      (Refl _ u))
    ((GSelL g b0 b1 b2 b3 b _ _ la pa ba)
      (let-match erased q (GSelL _ c0 c1 c2 c3 c _ _ lb pb bb) (absurd (GSelN _ _ _ _ _ _ _) la))
      (let-match erased (leafset-fn g (MkBits b0 b1 b2 b3) (MkBits c0 c1 c2 c3) la lb) (Refl _ _))
      (let-match erased (pick4-fn (Bool) s b0 b1 b2 b3 b c pa pb) (Refl _ _))
      (bset-fn b u v ba bb))
    ((GSelOne _) (let-match erased q (GSelOne _)) (Refl _ u))))

(def-fns _ $ (erased groot-fn : (erased (GSet) gs) (erased (Nat) n m) (erased (GRoot gs n) p) (erased (GRoot gs m) q) -> (erased (Eq (Nat) n m) e))
  (match erased p _
    ((GROne) (let-match erased q (GROne)) (Refl _ n))
    ((GRG _) (let-match erased q (GRG _)) (Refl _ n))))

(def-fns _ $ (erased groot-exists : (erased (GSet) gs) -> (erased (Nat) n) (erased (GRoot gs n) p))
  (match erased gs _ ((GSOne) (values (Succ (Zero)) (GROne))) ((GSG g) (values (Zero) (GRG g)))))

(def-fns _ $ (erased sym-fn : (erased (Gsym) s) (erased (Bstack) bs x y) (erased (Col) e) (erased (Sym s bs e x) p) (erased (Sym s bs e y) q) ->
    (erased (Eq (Bstack) x y) r))
  (match erased p _
    ((SSkip _) (let-match erased q (SSkip _)) (Refl _ x))
    ((SPush2 _) (let-match erased q (SPush2 _)) (Refl _ x))
    ((SPush3 _) (let-match erased q (SPush3 _)) (Refl _ x))
    ((SPop02 _) (let-match erased q (SPop02 _)) (Refl _ x))
    ((SPop12 _) (let-match erased q (SPop12 _)) (Refl _ x))
    ((SPop03 _) (let-match erased q (SPop03 _)) (Refl _ x))
    ((SPop13 _) (let-match erased q (SPop13 _)) (Refl _ x))))

(def-fns _ $ (erased pop-fn : (erased (Gsym) s t) (erased (Bstack) bs b) (erased (Col) e) (erased (Popped bs b) pp)
    (erased (Sym s bs e b) p) (erased (Sym t bs e b) q) -> (erased (Eq (Gsym) s t) r))
  (match erased p _
    (absurd (SSkip _) pp)
    (absurd (SPush2 _) pp)
    (absurd (SPush3 _) pp)
    ((SPop02 _) (let-match erased q (SPop02 _)) (Refl _ s))
    ((SPop12 _) (let-match erased q (SPop12 _)) (Refl _ s))
    ((SPop03 _) (let-match erased q (SPop03 _)) (Refl _ s))
    ((SPop13 _) (let-match erased q (SPop13 _)) (Refl _ s))))

(def-fns _ $ (erased popped-fn : (erased (Bstack) bs b c) (erased (Popped bs b) p) (erased (Popped bs c) q) -> (erased (Eq (Bstack) b c) r))
  (match erased p _
    ((Popped0 _) (let-match erased q (Popped0 _)) (Refl _ b))
    ((Popped1 _) (let-match erased q (Popped1 _)) (Refl _ b))))

(def-adts $ (PopOpt : ((Bstack) bs) ((Col) e) -> Type)
  enum
  (many PNone : (erased (Col) e) -> (PopOpt (BS0) e))
  (many PSome : (erased (Bstack) bs b) (erased (Col) e) (erased (Gsym) s) (erased (Popped bs b) pp) (erased (Sym s bs e b) y)
      -> (PopOpt bs e)))

; How a colour can be matched from a stack: never, by a skip, or by a push and at most one pop.
(def-adts $ (ColKind : ((Col) e) ((Bstack) bs) -> Type)
  enum
  (many K0 : (erased (Bstack) bs) -> (ColKind (C0) bs))
  (many K1 : (erased (Bstack) bs) -> (ColKind (C1) bs))
  (many K23 : (erased (Col) e) (erased (Bstack) bs bs1) (erased (Sym (GPush) bs e bs1) y) (erased (PopOpt bs e) po) -> (ColKind e bs)))

(def-fns _ $ (erased col-kind : (erased (Col) e) (erased (Bstack) bs) -> (erased (ColKind e bs) k))
  (match erased e _
    ((C0) (K0 bs))
    ((C1) (K1 bs))
    ((C2) (K23 e bs (BP0 bs) (SPush2 bs)
      (match erased bs _
        ((BS0) (PNone e))
        ((BP0 b) (PSome bs b e (GPop0) (Popped0 b) (SPop02 b)))
        ((BP1 b) (PSome bs b e (GPop1) (Popped1 b) (SPop12 b))))))
    ((C3) (K23 e bs (BP1 bs) (SPush3 bs)
      (match erased bs _
        ((BS0) (PNone e))
        ((BP0 b) (PSome bs b e (GPop1) (Popped0 b) (SPop13 b)))
        ((BP1 b) (PSome bs b e (GPop0) (Popped1 b) (SPop03 b))))))))

(def-adts $ (SymCls : ((Gsym) s) ((Bstack) bs) ((Col) e) ((Bstack) bs2) -> Type)
  enum
  (many SCSkip : (erased (Bstack) bs) -> (SymCls (GSkip) bs (C1) bs))
  (many SCPush : (erased (Bstack) bs bs2) (erased (Col) e) (erased (Sym (GPush) bs e bs2) y) -> (SymCls (GPush) bs e bs2))
  (many SCPop : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (Popped bs bs2) pp) (erased (Sym s bs e bs2) y)
      -> (SymCls s bs e bs2)))

(def-fns _ $ (erased sym-cls : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (Sym s bs e bs2) y) -> (erased (SymCls s bs e bs2) c))
  (match erased y _
    ((SSkip _) (SCSkip bs))
    ((SPush2 _) (SCPush bs bs2 e y))
    ((SPush3 _) (SCPush bs bs2 e y))
    ((SPop02 _) (SCPop s bs bs2 e (Popped0 bs2) y))
    ((SPop12 _) (SCPop s bs bs2 e (Popped1 bs2) y))
    ((SPop03 _) (SCPop s bs bs2 e (Popped1 bs2) y))
    ((SPop13 _) (SCPop s bs bs2 e (Popped0 bs2) y))))

(def-fns _ $ (erased mc-inv-0 : (erased (GSet) gs) (erased (Bstack) bs) (erased (List (Col)) et) (erased (Nat) n)
    (erased (MC gs bs (Cons (Col) (C0) et) n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased m _
    ((MC0 _ _ _) (Refl _ n))
    (absurd (MCPush _ _ _ _ _ _ y _ _) y)
    (absurd (MCPP _ _ _ _ _ _ _ _ _ _ _ _ _ y _ _ _ _ _ _) y)))

(def-fns _ $ (erased mc-inv-skip : (erased (GSet) gs) (erased (Bstack) bs) (erased (List (Col)) et) (erased (Nat) n)
    (erased (MC gs bs (Cons (Col) (C1) et) n) m) -> (erased (GSet) g1) (erased (GSel gs (GSkip) g1) p) (erased (MC g1 bs et n) q))
  (match erased m _
    ((MCSkip _ g1 _ _ _ p q) (values g1 p q))
    (absurd (MCPush _ _ _ _ _ _ y _ _) y)
    (absurd (MCPP _ _ _ _ _ _ _ _ _ _ _ _ _ y _ _ _ _ _ _) y)))

(def-fns _ $ (erased mc-inv-push : (erased (GSet) gs) (erased (Bstack) bs1) (erased (Col) e) (erased (List (Col)) et) (erased (Nat) n)
    (erased (Sym (GPush) (BS0) e bs1) y) (erased (MC gs (BS0) (Cons (Col) e et) n) m) ->
    (erased (GSet) g1) (erased (GSel gs (GPush) g1) p) (erased (MC g1 bs1 et n) q))
  (let-match erased m (MCPush _ g1 c1 _ _ _ y1 p q)
    (absurd (MC0 _ _ _) y)
    (absurd (MCSkip _ _ _ _ _ _ _) y)
    (absurd (MCPP _ _ _ _ _ _ _ _ _ _ _ _ pp _ _ _ _ _ _ _) pp))
  (let-match erased (sym-fn (GPush) (BS0) bs1 c1 e y y1) (Refl _ _))
  (values g1 p q))

(def-fns _ $ (erased mc-inv-pp : (erased (GSet) gs) (erased (Bstack) bs b bs1) (erased (Gsym) s) (erased (Col) e) (erased (List (Col)) et)
    (erased (Nat) n) (erased (Sym (GPush) bs e bs1) y) (erased (Popped bs b) pp) (erased (Sym s bs e b) z)
    (erased (MC gs bs (Cons (Col) e et) n) m) ->
    (erased (Nat) n1 n2) (erased (GSet) g1 g2) (erased (GSel gs (GPush) g1) p1) (erased (MC g1 bs1 et n1) q1)
    (erased (GSel gs s g2) p2) (erased (MC g2 b et n2) q2) (erased (Add n1 n2 n) a))
  (let-match erased m (MCPP _ g1 g2 _ c c1 t _ _ n1 n2 _ pp1 y1 p1 q1 z1 p2 q2 a)
    (absurd (MC0 _ _ _) y)
    (absurd (MCSkip _ _ _ _ _ _ _) y)
    (absurd (MCPush _ _ _ _ _ _ _ _ _) pp))
  (let-match erased (sym-fn (GPush) bs bs1 c1 e y y1) (Refl _ _))
  (let-match erased (popped-fn bs b c pp pp1) (Refl _ _))
  (let-match erased (pop-fn s t bs b e pp z z1) (Refl _ _))
  (values n1 n2 g1 g2 p1 q1 p2 q2 a))

(def-fns _ $ (erased mc-exists : (erased (GSet) gs) (erased (Bstack) bs) (subterm erased (List (Col)) et) -> (erased (Nat) n) (erased (MC gs bs et n) m))
  (let-match erased et (Cons _ e et1) ((Nil _) (let ((erased n) (erased r)) (groot-exists gs)) (values n (MCNil gs bs n r))))
  (match erased (col-kind e bs) _
    ((K0 _) (values (Zero) (MC0 gs bs et1)))
    ((K1 _)
      (let ((erased g1) (erased p)) (gsel-exists gs (GSkip)))
      (let ((erased n) (erased q)) (mc-exists g1 bs et1))
      (values n (MCSkip gs g1 bs et1 n p q)))
    ((K23 _ _ bs1 y po)
      (let ((erased g1) (erased p1)) (gsel-exists gs (GPush)))
      (let ((erased n1) (erased q1)) (mc-exists g1 bs1 et1))
      (let-match erased po (PSome _ b _ s pp z)
        ((PNone _) (values n1 (MCPush gs g1 bs1 e et1 n1 y p1 q1))))
      (let ((erased g2) (erased p2)) (gsel-exists gs s))
      (let ((erased n2) (erased q2)) (mc-exists g2 b et1))
      (let ((erased n) (erased a)) (add n1 n2))
      (values n (MCPP gs g1 g2 bs b bs1 s e et1 n1 n2 n pp y p1 q1 z p2 q2 a)))))

(def-fns _ $ (erased mc-fn : (erased (GSet) gs) (erased (Bstack) bs) (subterm erased (List (Col)) et) (erased (Nat) n m)
    (erased (MC gs bs et n) p) (erased (MC gs bs et m) q) -> (erased (Eq (Nat) n m) r))
  (let-match erased et (Cons _ e et1)
    ((Nil _) (let-match erased p (MCNil _ _ _ rp)) (let-match erased q (MCNil _ _ _ rq)) (groot-fn gs n m rp rq)))
  (match erased (col-kind e bs) _
    ((K0 _) (let-match erased (mc-inv-0 gs bs et1 n p) (Refl _ _)) (let-match erased (mc-inv-0 gs bs et1 m q) (Refl _ _)) (Refl _ n))
    ((K1 _)
      (let ((erased g1) (erased p1) (erased q1)) (mc-inv-skip gs bs et1 n p))
      (let ((erased h1) (erased p2) (erased q2)) (mc-inv-skip gs bs et1 m q))
      (let-match erased (gsel-fn gs g1 h1 (GSkip) p1 p2) (Refl _ _))
      (mc-fn g1 bs et1 n m q1 q2))
    ((K23 _ _ bs1 y po)
      (match erased po _
        ((PNone _)
          (let ((erased g1) (erased p1) (erased q1)) (mc-inv-push gs bs1 e et1 n y p))
          (let ((erased h1) (erased p2) (erased q2)) (mc-inv-push gs bs1 e et1 m y q))
          (let-match erased (gsel-fn gs g1 h1 (GPush) p1 p2) (Refl _ _))
          (mc-fn g1 bs1 et1 n m q1 q2))
        ((PSome _ b _ s pp z)
          (let ((erased n1) (erased n2) (erased g1) (erased g2) (erased s1) (erased c1) (erased s2) (erased c2) (erased a))
            (mc-inv-pp gs bs b bs1 s e et1 n y pp z p))
          (let ((erased m1) (erased m2) (erased h1) (erased h2) (erased t1) (erased d1) (erased t2) (erased d2) (erased a2))
            (mc-inv-pp gs bs b bs1 s e et1 m y pp z q))
          (let-match erased (gsel-fn gs g1 h1 (GPush) s1 t1) (Refl _ _))
          (let-match erased (gsel-fn gs g2 h2 s s2 t2) (Refl _ _))
          (let-match erased (mc-fn g1 bs1 et1 n1 m1 c1 d1) (Refl _ _))
          (let-match erased (mc-fn g2 b et1 n2 m2 c2 d2) (Refl _ _))
          (add-fn n1 n2 n m a a2))))))

(def-fns _ $ (erased sel-gempty : (erased (Gsym) s) (erased (GSet) u) (erased (GSel (GSG (GEmpty)) s u) p) -> (erased (Eq (GSet) u (GSG (GEmpty))) e))
  (let-match erased p (GSelL _ b0 b1 b2 b3 b _ _ la pa ba))
  (let-match erased la (LSE))
  (match erased pa _
    ((PkPush _ _ _ _ _) (let-match erased ba (BSetF)) (Refl _ u))
    ((PkSkip _ _ _ _ _) (let-match erased ba (BSetF)) (Refl _ u))
    ((PkPop0 _ _ _ _ _) (let-match erased ba (BSetF)) (Refl _ u))
    ((PkPop1 _ _ _ _ _) (let-match erased ba (BSetF)) (Refl _ u))))

(def-fns _ $ (erased mc-zero : (erased (Bstack) bs) (erased (List (Col)) et) (erased (Nat) n) (subterm erased (MC (GSG (GEmpty)) bs et n) m) ->
    (erased (Eq (Nat) n (Zero)) r))
  (match erased m _
    ((MCNil _ _ _ rp) (let-match erased rp (GRG _)) (Refl _ n))
    ((MC0 _ _ _) (Refl _ n))
    ((MCSkip _ g1 _ et1 _ p q) (let-match erased (sel-gempty (GSkip) g1 p) (Refl _ _)) (mc-zero bs et1 n q))
    ((MCPush _ g1 bs1 _ et1 _ _ p q) (let-match erased (sel-gempty (GPush) g1 p) (Refl _ _)) (mc-zero bs1 et1 n q))
    ((MCPP _ g1 g2 _ b bs1 s _ et1 n1 n2 _ _ _ p1 q1 _ p2 q2 a)
      (let-match erased (sel-gempty (GPush) g1 p1) (Refl _ _))
      (let-match erased (sel-gempty s g2 p2) (Refl _ _))
      (let-match erased (mc-zero bs1 et1 n1 q1) (Refl _ _))
      (let-match erased (mc-zero b et1 n2 q2) (Refl _ _))
      (let-match erased a (AddZero _))
      (Refl _ n))))

(def-fns _ $ (erased add-pos-r : (erased (Nat) a b c) (subterm erased (Add a b c) p) (erased (Lt (Zero) b) l) -> (erased (Lt (Zero) c) r))
  (match erased p _ ((AddZero _) l) ((AddSucc a1 _ c1 _) (LtZ c1))))

(def-fns _ $ (erased add-pos-l : (erased (Nat) a b c) (erased (Add a b c) p) (erased (Lt (Zero) a) l) -> (erased (Lt (Zero) c) r))
  (add-pos-r b a c (add-comm a b c p) l))

(def-fns _ $ (erased mc-pos : (erased (GSet) gs) (erased (Bstack) bs) (erased (List (Col)) et) (subterm erased (List (Gsym)) w) (erased (Nat) n)
    (erased (GMem gs w) g) (erased (MatchPG bs et w) mt) (erased (MC gs bs et n) m) -> (erased (Lt (Zero) n) r))
  (match erased g _
    ((GMNil) (let-match erased mt (MPNil _)) (let-match erased m (MCNil _ _ _ rp)) (let-match erased rp (GROne)) (LtZ (Zero)))
    ((GMCons _ gs2 s w1 sl g1)
      (let-match erased mt (MPCons _ bs2 e _ et1 _ y mt1))
      (match erased (sym-cls s bs bs2 e y) _
        ((SCSkip _)
          (let ((erased u) (erased p) (erased q)) (mc-inv-skip gs bs et1 n m))
          (let-match erased (gsel-fn gs gs2 u s sl p) (Refl _ _))
          (mc-pos gs2 bs et1 w1 n g1 mt1 q))
        ((SCPush _ _ _ _)
          (let-match erased (col-kind e bs) (K23 _ _ bs1 y1 po)
            (absurd (K0 _) y)
            (absurd (K1 _) y))
          (let-match erased (sym-fn (GPush) bs bs2 bs1 e y y1) (Refl _ _))
          (match erased po _
            ((PNone _)
              (let ((erased u) (erased p) (erased q)) (mc-inv-push gs bs2 e et1 n y m))
              (let-match erased (gsel-fn gs gs2 u s sl p) (Refl _ _))
              (mc-pos gs2 bs2 et1 w1 n g1 mt1 q))
            ((PSome _ b _ t pp z)
              (let ((erased n1) (erased n2) (erased u1) (erased u2) (erased p1) (erased q1) (erased p2) (erased q2) (erased a))
                (mc-inv-pp gs bs b bs2 t e et1 n y pp z m))
              (let-match erased (gsel-fn gs gs2 u1 s sl p1) (Refl _ _))
              (add-pos-l n1 n2 n a (mc-pos gs2 bs2 et1 w1 n1 g1 mt1 q1)))))
        ((SCPop _ _ _ _ pp _)
          (match erased (col-kind e bs) _
            (absurd (K0 _) y)
            (absurd (K1 _) (let-match erased y (SSkip _)) pp)
            ((K23 _ _ bs1 y1 po)
              (let-match erased po (PSome _ b _ t pp2 z)
                (absurd (PNone _) pp))
              (let-match erased (popped-fn bs bs2 b pp pp2) (Refl _ _))
              (let-match erased (pop-fn s t bs bs2 e pp y z) (Refl _ _))
              (let ((erased n1) (erased n2) (erased u1) (erased u2) (erased p1) (erased q1) (erased p2) (erased q2) (erased a))
                (mc-inv-pp gs bs bs2 bs1 s e et1 n y1 pp z m))
              (let-match erased (gsel-fn gs gs2 u2 s sl p2) (Refl _ _))
              (add-pos-r n1 n2 n a (mc-pos gs2 bs2 et1 w1 n2 g1 mt1 q2)))))))))

(def-fns _ $ (erased add-assoc-back : (erased (Nat) a b c bc abc) (subterm erased (Add a bc abc) p) (erased (Add b c bc) q) ->
    (erased (Nat) ab) (erased (Add a b ab) r) (erased (Add ab c abc) s))
  (let-match erased p (AddSucc a1 _ abc1 p1) ((AddZero _) (values b (AddZero b) q)))
  (let ((erased ab) (erased r) (erased s)) (add-assoc-back a1 b c bc abc1 p1 q))
  (values (Succ ab) (AddSucc a1 b ab r) (AddSucc ab c abc1 s)))

(def-fns _ $ (erased add-swap : (erased (Nat) x1 y1 n1 x2 y2 n2 n x y) (erased (Add x1 y1 n1) p1) (erased (Add x2 y2 n2) p2)
    (erased (Add n1 n2 n) p) (erased (Add x1 x2 x) px) (erased (Add y1 y2 y) py) -> (erased (Add x y n) r))
  (let ((erased t1) (erased q1) (erased q2)) (add-assoc x1 y1 n2 n1 n p1 p))
  (let ((erased ab) (erased q3) (erased q4)) (add-assoc-back y1 x2 y2 n2 t1 q1 p2))
  (let ((erased bc) (erased q5) (erased q6)) (add-assoc x2 y1 y2 ab t1 (add-comm y1 x2 ab q3) q4))
  (let-match erased (add-fn y1 y2 bc y q5 py) (Refl _ _))
  (let ((erased ab2) (erased q7) (erased q8)) (add-assoc-back x1 x2 y t1 n q2 q6))
  (let-match erased (add-fn x1 x2 ab2 x q7 px) (Refl _ _))
  q8)

(def-fns _ $ (erased sel-gempty-mk : (erased (Gsym) s) -> (erased (GSel (GSG (GEmpty)) s (GSG (GEmpty))) p))
  (let ((erased f)) (BFalse))
  (let ((erased b) (erased pk)) (pick4-exists (Bool) s f f f f))
  (match erased pk _
    ((PkPush _ _ _ _ _) (GSelL (GEmpty) f f f f b s (GSG (GEmpty)) (LSE) pk (BSetF)))
    ((PkSkip _ _ _ _ _) (GSelL (GEmpty) f f f f b s (GSG (GEmpty)) (LSE) pk (BSetF)))
    ((PkPop0 _ _ _ _ _) (GSelL (GEmpty) f f f f b s (GSG (GEmpty)) (LSE) pk (BSetF)))
    ((PkPop1 _ _ _ _ _) (GSelL (GEmpty) f f f f b s (GSG (GEmpty)) (LSE) pk (BSetF)))))

(def-fns _ $ (erased part-step : (erased (GSet) gs a b g1 a1 b1) (erased (Gsym) s) (erased (GPart gs a b) p)
    (erased (GSel gs s g1) sg) (erased (GSel a s a1) sa) (erased (GSel b s b1) sb) -> (erased (GPart g1 a1 b1) r))
  (let ((erased e) (erased pa))
    (match erased p (((GSet) e) ((GPartAt gs a b s) pa))
      ((GPE) (let ((erased e) (erased m)) (values (GSG (GEmpty)) (sel-gempty-mk s)))
        (values (GSG (GEmpty)) (MkGPartAt gs a b e e e s m m m (GPE))))
      ((GPS _ _ _ _ _ _ _ _ _ _ p0 p1 p2 p3)
        (values gs (match erased s _ ((GPush) p0) ((GSkip) p1) ((GPop0) p2) ((GPop1) p3))))))
  (let-match erased pa (MkGPartAt _ _ _ g2 a2 b2 _ tg ta tb q))
  (let-match erased (gsel-fn gs g1 g2 s sg tg) (Refl _ _))
  (let-match erased (gsel-fn a a1 a2 s sa ta) (Refl _ _))
  (let-match erased (gsel-fn b b1 b2 s sb tb) (Refl _ _))
  q)

(def-fns _ $ (erased part-mc : (erased (GSet) gs a b) (erased (Bstack) bs) (subterm erased (List (Col)) et) (erased (Nat) n x y)
    (erased (GPart gs a b) p) (erased (MC gs bs et n) mg) (erased (MC a bs et x) ma) (erased (MC b bs et y) mb) -> (erased (Add x y n) r))
  (let-match erased et (Cons _ e et1)
    ((Nil _)
      (let-match erased mg (MCNil _ _ _ rg))
      (let-match erased ma (MCNil _ _ _ ra))
      (let-match erased mb (MCNil _ _ _ rb))
      (match erased p _
        ((GPE) (let-match erased rg (GRG _)) (let-match erased ra (GRG _)) (let-match erased rb (GRG _)) (AddZero (Zero)))
        ((GPS _ _ _ n0 x0 y0 rg0 ra0 rb0 s _ _ _ _)
          (let-match erased (groot-fn gs n n0 rg rg0) (Refl _ _))
          (let-match erased (groot-fn a x x0 ra ra0) (Refl _ _))
          (let-match erased (groot-fn b y y0 rb rb0) (Refl _ _))
          s))))
  (match erased (col-kind e bs) _
    ((K0 _)
      (let-match erased (mc-inv-0 gs bs et1 n mg) (Refl _ _))
      (let-match erased (mc-inv-0 a bs et1 x ma) (Refl _ _))
      (let-match erased (mc-inv-0 b bs et1 y mb) (Refl _ _))
      (AddZero (Zero)))
    ((K1 _)
      (let ((erased g1) (erased sg) (erased qg)) (mc-inv-skip gs bs et1 n mg))
      (let ((erased a1) (erased sa) (erased qa)) (mc-inv-skip a bs et1 x ma))
      (let ((erased b1) (erased sb) (erased qb)) (mc-inv-skip b bs et1 y mb))
      (part-mc g1 a1 b1 bs et1 n x y (part-step gs a b g1 a1 b1 (GSkip) p sg sa sb) qg qa qb))
    ((K23 _ _ bs1 y0 po)
      (match erased po _
        ((PNone _)
          (let ((erased g1) (erased sg) (erased qg)) (mc-inv-push gs bs1 e et1 n y0 mg))
          (let ((erased a1) (erased sa) (erased qa)) (mc-inv-push a bs1 e et1 x y0 ma))
          (let ((erased b1) (erased sb) (erased qb)) (mc-inv-push b bs1 e et1 y y0 mb))
          (part-mc g1 a1 b1 bs1 et1 n x y (part-step gs a b g1 a1 b1 (GPush) p sg sa sb) qg qa qb))
        ((PSome _ c _ s pp z)
          (let ((erased n1) (erased n2) (erased g1) (erased g2) (erased sg1) (erased qg1) (erased sg2) (erased qg2) (erased ag))
            (mc-inv-pp gs bs c bs1 s e et1 n y0 pp z mg))
          (let ((erased x1) (erased x2) (erased a1) (erased a2) (erased sa1) (erased qa1) (erased sa2) (erased qa2) (erased aa))
            (mc-inv-pp a bs c bs1 s e et1 x y0 pp z ma))
          (let ((erased z1) (erased z2) (erased b1) (erased b2) (erased sb1) (erased qb1) (erased sb2) (erased qb2) (erased ab))
            (mc-inv-pp b bs c bs1 s e et1 y y0 pp z mb))
          (add-swap x1 z1 n1 x2 z2 n2 n x y
            (part-mc g1 a1 b1 bs1 et1 n1 x1 z1 (part-step gs a b g1 a1 b1 (GPush) p sg1 sa1 sb1) qg1 qa1 qb1)
            (part-mc g2 a2 b2 c et1 n2 x2 z2 (part-step gs a b g2 a2 b2 s p sg2 sa2 sb2) qg2 qa2 qb2)
            ag aa ab))))))

(def-fns _ $ (erased part-mem : (erased (GSet) gs a b) (subterm erased (List (Gsym)) w) (erased (GPart gs a b) p) (erased (GMem gs w) m) ->
    (erased (Or (GMem a w) (GMem b w)) r))
  (match erased m _
    ((GMNil)
      (let-match erased p (GPS _ _ _ n0 x0 y0 rg ra rb s _ _ _ _))
      (let-match erased rg (GROne))
      (let-match erased ra (GRG _)
        ((GROne) (InL _ _ (GMNil))))
      (let-match erased s (AddZero _))
      (let-match erased rb (GROne))
      (InR _ _ (GMNil)))
    ((GMCons _ g1 s w1 sg m1)
      (let ((erased a1) (erased sa)) (gsel-exists a s))
      (let ((erased b1) (erased sb)) (gsel-exists b s))
      (match erased (part-mem g1 a1 b1 w1 (part-step gs a b g1 a1 b1 s p sg sa sb) m1) _
        ((InL _ _ ma) (InL _ _ (GMCons a a1 s w1 sa ma)))
        ((InR _ _ mb) (InR _ _ (GMCons b b1 s w1 sb mb)))))))
