; Entry i of us is n.
(def-adts $ (Ent : ((List Cnt) us) ((Nat) i) ((Nat) n) -> Type)
  enum
  (many MkEnt : (erased (List Cnt) us) (erased (Nat) i n) (erased (Lt n u62-modulus) nb) (erased (Nth Cnt us i (MkCopy (U62) (MkU62 n nb))) x)
      -> (Ent us i n)))

; vs is us with entry i set to n.
(def-adts $ (Upd : ((List Cnt) us) ((Nat) i) ((Nat) n) ((List Cnt) vs) -> Type)
  enum
  (many MkUpd : (erased (List Cnt) us vs) (erased (Nat) i n) (erased (Lt n u62-modulus) nb)
      (erased (SetNth Cnt us i (MkCopy (U62) (MkU62 n nb)) vs) s) -> (Upd us i n vs)))

(def-fns _ $ (erased ent-fn : (erased (List Cnt) us) (erased (Nat) i n m) (erased (Ent us i n) a) (erased (Ent us i m) b) -> (erased (Eq (Nat) n m) e))
  (let-match erased a (MkEnt _ _ _ na x))
  (let-match erased b (MkEnt _ _ _ mb y))
  (let-match erased (nth-fn _ us i _ _ x y) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased upd-ent : (erased (List Cnt) us vs) (erased (Nat) i n) (erased (Upd us i n vs) u) -> (erased (Ent vs i n) e))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (MkEnt vs i n nb (setnth-nth _ us i _ vs s)))

(def-fns _ $ (erased upd-other : (erased (List Cnt) us vs) (erased (Nat) j n i m) (erased (Upd us j n vs) u) (erased (Apart (Nat) Lt j i) ap)
    (erased (Ent us i m) e) -> (erased (Ent vs i m) r))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (let-match erased e (MkEnt _ _ _ mb x))
  (MkEnt vs i m mb
    (match erased ap _
      ((ApLt _ _ _ _ l) (setnth-nth-gt _ us j i _ _ vs s x l))
      ((ApGt _ _ _ _ l) (setnth-nth-lt _ us j i _ _ vs s x l)))))

(def-fns _ $ (erased upd-len : (erased (List Cnt) us vs) (erased (Nat) i n len) (erased (Upd us i n vs) u) (erased (Length Cnt us len) l)
    -> (erased (Length Cnt vs len) r))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (setnth-length _ us i len _ vs s l))

(def-fns _ $ (erased monus-one : (erased (Nat) a k m m2) (erased (Monus a k m) p) (erased (Monus m (Succ (Zero)) m2) q) -> (erased (Monus a (Succ k) m2) r))
  (monus-add a k m (Succ (Zero)) m2 (Succ k) p q (add-succ-right k (Zero) k (add-zero-right k))))

(def-fns _ $ (erased monus-uniq : (erased (Nat) a k m m2) (subterm erased (Monus a k m) p) (erased (Monus a k m2) q) -> (erased (Eq (Nat) m m2) e))
  (match erased p _
    ((MoZ _) (let-match erased q (MoZ _)) (Refl _ m))
    ((MoE _) (let-match erased q (MoE _)) (Refl _ m))
    ((MoS a1 k1 _ p1) (let-match erased q (MoS _ _ _ q1)) (monus-uniq a1 k1 m m2 p1 q1))))

; After k decrements from (n0, 0), an entry and its gone entry are (n, x): x is n0 once a decrement has reached a live entry.
(def-adts $ (Ds : ((Nat) n0) ((Nat) k) ((Nat) n) ((Nat) x) -> Type)
  enum
  (many DsU : (erased (Nat) n0) -> (Ds n0 (Zero) n0 (Zero)))
  (many DsT : (erased (Nat) n1 k1 n) (erased (Monus (Succ n1) (Succ k1) n) o) -> (Ds (Succ n1) (Succ k1) n (Succ n1)))
  (many DsE : (erased (Nat) k) -> (Ds (Zero) k (Zero) (Zero))))

; One decrement: (n, x) becomes (n2, x2).
(def-adts $ (Dk : ((Nat) n) ((Nat) x) ((Nat) n2) ((Nat) x2) -> Type)
  enum
  (many DkZ : (erased (Nat) x) -> (Dk (Zero) x (Zero) x))
  (many DkF : (erased (Nat) n1) -> (Dk (Succ n1) (Zero) n1 (Succ n1)))
  (many DkS : (erased (Nat) n1 x1) -> (Dk (Succ n1) (Succ x1) n1 (Succ x1))))

(def-fns _ $ (erased ds-dk : (erased (Nat) n0 k n x n2 x2) (erased (Ds n0 k n x) s) (erased (Dk n x n2 x2) d) -> (erased (Ds n0 (Succ k) n2 x2) r))
  (match erased d _
    ((DkZ _)
      (match erased s _
        ((DsU _) (DsE (Succ (Zero))))
        ((DsT n1 k1 _ o) (DsT n1 (Succ k1) (Zero) (monus-one (Succ n1) (Succ k1) (Zero) (Zero) o (MoE (Zero)))))
        ((DsE _) (DsE (Succ k)))))
    ((DkF n1) (let-match erased s (DsU _)) (DsT n1 (Zero) n1 (MoS n1 (Zero) n1 (MoZ n1))))
    ((DkS n1 x1)
      (let-match erased s (DsT m1 k1 _ o))
      (DsT m1 (Succ k1) n1 (monus-one (Succ m1) (Succ k1) (Succ n1) n1 o (MoS n1 (Zero) n1 (MoZ n1)))))))

(def-adts $ (HasT : ((Nat) x) ((List (Nat)) T) ((Nat) i) -> Type)
  enum
  (many HtZ : (erased (List (Nat)) T) (erased (Nat) i) -> (HasT (Zero) T i))
  (many HtE : (erased (Nat) x i) (erased (List (Nat)) T) (erased (Elem (Nat) i T) e) -> (HasT x T i)))

(def-fns _ $ (erased has-cons : (erased (Nat) x i j) (erased (List (Nat)) T) (erased (HasT x T i) h) -> (erased (HasT x (Cons (Nat) j T) i) r))
  (match erased h _
    ((HtZ _ _) (HtZ (Cons _ j T) i))
    ((HtE _ _ _ e) (HtE x i (Cons _ j T) (ElThere _ i j T e)))))

; The walk's state: counts, gone entries, and the indices whose gone entry it set.
(def-adts $ (Sv : -> Type)
  enum
  (many MkSv : (many (List Cnt) us ws) (many (List (Nat)) T) -> (Sv)))

; Trace index i of s started from count n0 and has had k decrements.
(def-adts $ (TrS : ((Sv) s) ((Nat) i) ((Nat) n0) ((Nat) k) -> Type)
  enum
  (many MkTrS : (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Nat) i n0 k n x) (erased (Ent us i n) eu) (erased (Ent ws i x) ew)
      (erased (Ds n0 k n x) st) (erased (HasT x T i) ht) -> (TrS (MkSv us ws T) i n0 k)))

; One decrement of index i.
(def-adts $ (Tick : ((Nat) i) ((Sv) s) ((Sv) s2) -> Type)
  enum
  (many TkZ : (erased (Nat) i) (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Ent us i (Zero)) e)
      -> (Tick i (MkSv us ws T) (MkSv us ws T)))
  (many TkF : (erased (Nat) i n1) (erased (List Cnt) us ws us2 ws2) (erased (List (Nat)) T) (erased (Ent us i (Succ n1)) e) (erased (Ent ws i (Zero)) f)
      (erased (Upd us i n1 us2) u) (erased (Upd ws i (Succ n1) ws2) w) -> (Tick i (MkSv us ws T) (MkSv us2 ws2 (Cons (Nat) i T))))
  (many TkS : (erased (Nat) i n1 x1) (erased (List Cnt) us ws us2) (erased (List (Nat)) T) (erased (Ent us i (Succ n1)) e) (erased (Ent ws i (Succ x1)) f)
      (erased (Upd us i n1 us2) u) -> (Tick i (MkSv us ws T) (MkSv us2 ws T))))

(def-fns _ $ (erased tick-same : (erased (Nat) i n0 k) (erased (Sv) s s2) (erased (Tick i s s2) tk) (erased (TrS s i n0 k) tr) -> (erased (TrS s2 i n0 (Succ k)) r))
  (let-match erased tr (MkTrS us ws T _ _ _ n x eu ew st ht))
  (match erased tk _
    ((TkZ _ _ _ _ e)
      (let-match erased (ent-fn us i n (Zero) eu e) (Refl _ _))
      (MkTrS us ws T i n0 (Succ k) n x eu ew (ds-dk n0 k n x n x st (DkZ x)) ht))
    ((TkF _ n1 _ _ us2 ws2 _ e f u w)
      (let-match erased (ent-fn us i n (Succ n1) eu e) (Refl _ _))
      (let-match erased (ent-fn ws i x (Zero) ew f) (Refl _ _))
      (MkTrS us2 ws2 (Cons _ i T) i n0 (Succ k) n1 (Succ n1) (upd-ent us us2 i n1 u) (upd-ent ws ws2 i (Succ n1) w)
        (ds-dk n0 k n x n1 (Succ n1) st (DkF n1)) (HtE (Succ n1) i (Cons _ i T) (ElHere _ i T))))
    ((TkS _ n1 x1 _ _ us2 _ e f u)
      (let-match erased (ent-fn us i n (Succ n1) eu e) (Refl _ _))
      (let-match erased (ent-fn ws i x (Succ x1) ew f) (Refl _ _))
      (MkTrS us2 ws T i n0 (Succ k) n1 x (upd-ent us us2 i n1 u) ew (ds-dk n0 k n x n1 x st (DkS n1 x1)) ht))))

(def-fns _ $ (erased tick-other : (erased (Nat) j i n0 k) (erased (Sv) s s2) (erased (Tick j s s2) tk) (erased (Apart (Nat) Lt j i) ap)
    (erased (TrS s i n0 k) tr) -> (erased (TrS s2 i n0 k) r))
  (let-match erased tr (MkTrS us ws T _ _ _ n x eu ew st ht))
  (match erased tk _
    ((TkZ _ _ _ _ _) tr)
    ((TkF _ n1 _ _ us2 ws2 _ _ _ u w)
      (MkTrS us2 ws2 (Cons _ j T) i n0 k n x (upd-other us us2 j n1 i n u ap eu) (upd-other ws ws2 j (Succ n1) i x w ap ew) st (has-cons x i j T ht)))
    ((TkS _ n1 _ _ _ us2 _ _ _ u) (MkTrS us2 ws T i n0 k n x (upd-other us us2 j n1 i n u ap eu) ew st ht))))

; A trace prefix p with its bit stack, whose block in us0, of j more colours, holds t.
(def-adts $ (Pr : ((List Cnt) us0) ((Nat) j) -> Type)
  enum
  (many MkPr : (erased (List Cnt) us0) (erased (Nat) j) (many (Nat) p) (many (Bstack) bs) (erased (Ctree) t) (erased (Tally us0 j p t) tb) -> (Pr us0 j)))

(def-adts $ (IsPop : ((Gsym) s) -> Type)
  enum
  (many IP0 : -> (IsPop (GPop0)))
  (many IP1 : -> (IsPop (GPop1))))

; Q is Q0 after the pairs that x steps to under the symbol s.
(def-adts $ (Ch : ((List Cnt) us0) ((Nat) j) ((Gsym) s) ((Pr us0 (Succ j)) x) ((List (Pr us0 j)) Q0) ((List (Pr us0 j)) Q) -> Type)
  enum
  (many ChSkip : (erased (List Cnt) us0) (erased (Nat) j p q) (erased (Bstack) bs) (erased (Ctree) t u) (erased (Tally us0 (Succ j) p t) tb)
      (erased (Tally us0 j q u) ub) (erased (Kid p (C1) q) k) (erased (List (Pr us0 j)) Q0)
      -> (Ch us0 j (GSkip) (MkPr us0 (Succ j) p bs t tb) Q0 (Cons (Pr us0 j) (MkPr us0 j q bs u ub) Q0)))
  (many ChPush : (erased (List Cnt) us0) (erased (Nat) j p q2 q3) (erased (Bstack) bs) (erased (Ctree) t u2 u3) (erased (Tally us0 (Succ j) p t) tb)
      (erased (Tally us0 j q2 u2) b2) (erased (Tally us0 j q3 u3) b3) (erased (Kid p (C2) q2) k2) (erased (Kid p (C3) q3) k3) (erased (List (Pr us0 j)) Q0)
      -> (Ch us0 j (GPush) (MkPr us0 (Succ j) p bs t tb) Q0
           (Cons (Pr us0 j) (MkPr us0 j q2 (BP0 bs) u2 b2) (Cons (Pr us0 j) (MkPr us0 j q3 (BP1 bs) u3 b3) Q0))))
  (many ChPop : (erased (List Cnt) us0) (erased (Nat) j p q) (erased (Gsym) s) (erased (Col) e) (erased (Bstack) bs b) (erased (Ctree) t u)
      (erased (Tally us0 (Succ j) p t) tb) (erased (Tally us0 j q u) ub) (erased (Popped bs b) pp) (erased (Sym s bs e b) y) (erased (Kid p e q) k)
      (erased (List (Pr us0 j)) Q0) -> (Ch us0 j s (MkPr us0 (Succ j) p bs t tb) Q0 (Cons (Pr us0 j) (MkPr us0 j q b u ub) Q0)))
  (many ChNone : (erased (List Cnt) us0) (erased (Nat) j p) (erased (Gsym) s) (erased (Ctree) t) (erased (IsPop s) ip) (erased (Tally us0 (Succ j) p t) tb)
      (erased (List (Pr us0 j)) Q0) -> (Ch us0 j s (MkPr us0 (Succ j) p (BS0) t tb) Q0 Q0)))

; Q holds the pairs that those of P step to under s.
(def-adts $ (Stp : ((List Cnt) us0) ((Nat) j) ((Gsym) s) ((List (Pr us0 (Succ j))) P) ((List (Pr us0 j)) Q) -> Type)
  enum
  (many StpNil : (erased (List Cnt) us0) (erased (Nat) j) (erased (Gsym) s) -> (Stp us0 j s (Nil (Pr us0 (Succ j))) (Nil (Pr us0 j))))
  (many StpCons : (erased (List Cnt) us0) (erased (Nat) j) (erased (Gsym) s) (erased (Pr us0 (Succ j)) x) (erased (List (Pr us0 (Succ j))) P)
      (erased (List (Pr us0 j)) Q0 Q) (erased (Stp us0 j s P Q0) st) (erased (Ch us0 j s x Q0 Q) ch) -> (Stp us0 j s (Cons (Pr us0 (Succ j)) x P) Q)))

(def-adts $ (ColNe : ((Col) e) ((Col) f) -> Type)
  enum
  (many N12 : -> (ColNe (C1) (C2)))
  (many N13 : -> (ColNe (C1) (C3)))
  (many N21 : -> (ColNe (C2) (C1)))
  (many N23 : -> (ColNe (C2) (C3)))
  (many N31 : -> (ColNe (C3) (C1)))
  (many N32 : -> (ColNe (C3) (C2))))

(def-adts $ (KidCmp : ((Col) e) ((Col) f) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many KcSame : (erased (Col) e) (erased (Nat) a) -> (KidCmp e e a a))
  (many KcNe : (erased (Col) e f) (erased (Nat) a b) (erased (ColNe e f) ne) (erased (Apart (Nat) Lt a b) ap) -> (KidCmp e f a b)))

(def-fns _ $ (erased kid-dec : (erased (Nat) p a b) (erased (Col) e f) (erased (Kid p e a) ka) (erased (Kid p f b) kb) -> (erased (KidCmp e f a b) r))
  (match erased ka _
    ((Ki1 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N12) (ApLt _ _ a b (lt-succ a))))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N13) (ApLt _ _ a b (lt-weaken a (Succ a) (lt-succ a)))))))
    ((Ki2 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N21) (ApGt _ _ a b (lt-succ b))))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N23) (ApLt _ _ a b (lt-succ a))))))
    ((Ki3 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N31) (ApGt _ _ a b (lt-weaken b (Succ b) (lt-succ b)))))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N32) (ApGt _ _ a b (lt-succ b))))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))))))

; No chromogram symbol s matches the colour e from the stack bs.
(def-adts $ (NoSym : ((Gsym) s) ((Bstack) bs) ((Col) e) -> Type)
  enum
  (many NsSk2 : (erased (Bstack) bs) -> (NoSym (GSkip) bs (C2)))
  (many NsSk3 : (erased (Bstack) bs) -> (NoSym (GSkip) bs (C3)))
  (many NsPu1 : (erased (Bstack) bs) -> (NoSym (GPush) bs (C1)))
  (many NsP01 : (erased (Bstack) bs) -> (NoSym (GPop0) bs (C1)))
  (many NsP11 : (erased (Bstack) bs) -> (NoSym (GPop1) bs (C1)))
  (many NsP0E : (erased (Col) e) -> (NoSym (GPop0) (BS0) e))
  (many NsP1E : (erased (Col) e) -> (NoSym (GPop1) (BS0) e))
  (many NsP03 : (erased (Bstack) b) -> (NoSym (GPop0) (BP0 b) (C3)))
  (many NsP02 : (erased (Bstack) b) -> (NoSym (GPop0) (BP1 b) (C2)))
  (many NsP12 : (erased (Bstack) b) -> (NoSym (GPop1) (BP0 b) (C2)))
  (many NsP13 : (erased (Bstack) b) -> (NoSym (GPop1) (BP1 b) (C3))))

(def-fns _ $ (erased absurd nosym-sym : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e) (erased (NoSym s bs e) ns) (erased (Sym s bs e b) y)
    -> (erased (False) f))
  (match erased y _
    (absurd (SSkip _) ns) (absurd (SPush2 _) ns) (absurd (SPush3 _) ns) (absurd (SPop02 _) ns)
    (absurd (SPop12 _) ns) (absurd (SPop03 _) ns) (absurd (SPop13 _) ns)))

(def-fns _ $ (erased pop-nosym : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e2 e) (erased (Popped bs b) pp) (erased (Sym s bs e2 b) y)
    (erased (ColNe e2 e) ne) -> (erased (NoSym s bs e) r))
  (match erased y _
    (absurd (SSkip _) pp) (absurd (SPush2 _) pp) (absurd (SPush3 _) pp)
    ((SPop02 _) (match erased ne _ ((N21) (NsP01 bs)) ((N23) (NsP03 b))))
    ((SPop12 _) (match erased ne _ ((N21) (NsP11 bs)) ((N23) (NsP13 b))))
    ((SPop03 _) (match erased ne _ ((N31) (NsP01 bs)) ((N32) (NsP02 b))))
    ((SPop13 _) (match erased ne _ ((N31) (NsP11 bs)) ((N32) (NsP12 b))))))

; c counts the chromograms of gs matching rest from the stack that s leaves after matching e from bs, or is 0 when s cannot.
(def-adts $ (SymC : ((Gsym) s) ((Bstack) bs) ((Col) e) ((GSet) gs) ((List (Col)) rest) ((Nat) c) -> Type)
  enum
  (many ScY : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
      (erased (Sym s bs e bs2) y) (erased (MC gs bs2 rest c) m) -> (SymC s bs e gs rest c))
  (many ScN : (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (NoSym s bs e) ns)
      -> (SymC s bs e gs rest (Zero))))

(def-fns _ $ (erased symc-none : (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
    (erased (SymC s bs e gs rest c) sc) (erased (NoSym s bs e) ns) -> (erased (Eq (Nat) c (Zero)) r))
  (let-match erased sc (ScN _ _ _ _ _ _) (absurd (ScY _ _ b _ _ _ _ y _) (nosym-sym s bs b e ns y)))
  (Refl _ c))

(def-fns _ $ (erased symc-some : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
    (erased (SymC s bs e gs rest c) sc) (erased (Sym s bs e b) y) -> (erased (MC gs b rest c) r))
  (let-match erased sc (ScY _ _ b2 _ _ _ _ y2 m) (absurd (ScN _ _ _ _ _ ns) (nosym-sym s bs b e ns y)))
  (let-match erased (sym-fn s bs b2 b e y2 y) (Refl _ _))
  m)

(def-adts $ (Sum4 : ((Nat) c0) ((Nat) c1) ((Nat) c2) ((Nat) c3) ((Nat) n) -> Type)
  enum
  (many MkSum4 : (erased (Nat) c0 c1 c2 c3 n x y) (erased (Add c0 c1 x) a1) (erased (Add x c2 y) a2) (erased (Add y c3 n) a3) -> (Sum4 c0 c1 c2 c3 n)))

(def-fns _ $ (erased sum4-pp : (erased (Nat) a b) -> (erased (Nat) n) (erased (Add a b n) ad) (erased (Sum4 a (Zero) b (Zero) n) s2)
    (erased (Sum4 a (Zero) (Zero) b n) s3))
  (let ((erased n) (erased ad)) (add a b))
  (values n ad (MkSum4 a (Zero) b (Zero) n a n (add-zero-right a) ad (add-zero-right n)) (MkSum4 a (Zero) (Zero) b n a a (add-zero-right a) (add-zero-right a) ad)))

; k counts, over the pairs of P at the prefix q, the chromograms of gs that match rest from their stacks.
(def-adts $ (PairCnt : ((List Cnt) us0) ((Nat) j) ((List (Pr us0 j)) P) ((GSet) gs) ((Nat) q) ((List (Col)) rest) ((Nat) k) -> Type)
  enum
  (many PaNil : (erased (List Cnt) us0) (erased (Nat) j q) (erased (GSet) gs) (erased (List (Col)) rest) -> (PairCnt us0 j (Nil (Pr us0 j)) gs q rest (Zero)))
  (many PaHit : (erased (List Cnt) us0) (erased (Nat) j q) (erased (Bstack) bs) (erased (Ctree) t) (erased (Tally us0 j q t) tb) (erased (List (Pr us0 j)) P)
      (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) a c k) (erased (MC gs bs rest a) m) (erased (PairCnt us0 j P gs q rest c) pc) (erased (Add a c k) ad)
      -> (PairCnt us0 j (Cons (Pr us0 j) (MkPr us0 j q bs t tb) P) gs q rest k))
  (many PaMiss : (erased (List Cnt) us0) (erased (Nat) j p q) (erased (Bstack) bs) (erased (Ctree) t) (erased (Tally us0 j p t) tb) (erased (List (Pr us0 j)) P)
      (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) k) (erased (Apart (Nat) Lt p q) ap) (erased (PairCnt us0 j P gs q rest k) pc)
      -> (PairCnt us0 j (Cons (Pr us0 j) (MkPr us0 j p bs t tb) P) gs q rest k)))

(def-fns _ $ (erased pc-hit : (erased (List Cnt) us0) (erased (Nat) j q r) (erased (Bstack) bs) (erased (Ctree) u) (erased (Tally us0 j q u) ub)
    (erased (List (Pr us0 j)) Q0) (erased (GSet) gs) (erased (List (Col)) rest) (erased (PairCnt us0 j Q0 gs q rest r) pc) ->
    (erased (Nat) a k) (erased (MC gs bs rest a) m) (erased (Add a r k) ad) (erased (PairCnt us0 j (Cons (Pr us0 j) (MkPr us0 j q bs u ub) Q0) gs q rest k) pk))
  (let ((erased a) (erased m)) (mc-exists gs bs rest))
  (let ((erased k) (erased ad)) (add a r))
  (values a k m ad (PaHit us0 j q bs u ub Q0 gs rest a r k m pc ad)))

(def-fns _ $ (erased ch-symc : (erased (List Cnt) us0) (erased (Nat) j p q r) (erased (Gsym) s) (erased (Bstack) bs) (erased (Ctree) t)
    (erased (Tally us0 (Succ j) p t) tb) (erased (List (Pr us0 j)) Q0 Q) (erased (GSet) gs) (erased (Col) e) (erased (List (Col)) rest)
    (erased (Ch us0 j s (MkPr us0 (Succ j) p bs t tb) Q0 Q) ch) (erased (Kid p e q) kq) (erased (PairCnt us0 j Q0 gs q rest r) pc) ->
    (erased (Nat) c k) (erased (SymC s bs e gs rest c) sc) (erased (Add c r k) ad) (erased (PairCnt us0 j Q gs q rest k) pk))
  (match erased ch _
    ((ChSkip _ _ _ q1 _ _ u1 _ ub1 k1 _)
      (let-match erased (kid-dec p q1 q (C1) e k1 kq) (KcSame _ _)
        ((KcNe _ _ _ _ ne ap)
          (values (Zero) r (ScN (GSkip) bs e gs rest (match erased ne _ ((N12) (NsSk2 bs)) ((N13) (NsSk3 bs)))) (AddZero r)
            (PaMiss us0 j q1 q bs u1 ub1 Q0 gs rest r ap pc))))
      (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 j q r bs u1 ub1 Q0 gs rest pc))
      (values a k (ScY (GSkip) bs bs (C1) gs rest a (SSkip bs) m) ad pk))
    ((ChPush _ _ _ q3 q4 _ _ u3 u4 _ b3 b4 k3 k4 _)
      (match erased (kid-dec p q3 q (C2) e k3 kq) _
        ((KcSame _ _)
          (let-match erased (kid-dec p q4 q (C3) (C2) k4 kq) (KcNe _ _ _ _ _ ap4))
          (let ((erased a) (erased k) (erased m) (erased ad) (erased pk))
            (pc-hit us0 j q r (BP0 bs) u3 b3 _ gs rest (PaMiss us0 j q4 q (BP1 bs) u4 b4 Q0 gs rest r ap4 pc)))
          (values a k (ScY (GPush) bs (BP0 bs) (C2) gs rest a (SPush2 bs) m) ad pk))
        ((KcNe _ _ _ _ ne3 ap3)
          (match erased (kid-dec p q4 q (C3) e k4 kq) _
            ((KcSame _ _)
              (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 j q r (BP1 bs) u4 b4 Q0 gs rest pc))
              (values a k (ScY (GPush) bs (BP1 bs) (C3) gs rest a (SPush3 bs) m) ad (PaMiss us0 j q3 q (BP0 bs) u3 b3 _ gs rest k ap3 pk)))
            ((KcNe _ _ _ _ ne4 ap4)
              (let-match erased ne3 (N21) (absurd (N23) ne4))
              (values (Zero) r (ScN (GPush) bs (C1) gs rest (NsPu1 bs)) (AddZero r)
                (PaMiss us0 j q3 q (BP0 bs) u3 b3 _ gs rest r ap3 (PaMiss us0 j q4 q (BP1 bs) u4 b4 Q0 gs rest r ap4 pc))))))))
    ((ChPop _ _ _ q1 _ e2 _ b1 _ u1 _ ub1 pp y k1 _)
      (let-match erased (kid-dec p q1 q e2 e k1 kq) (KcSame _ _)
        ((KcNe _ _ _ _ ne ap)
          (values (Zero) r (ScN s bs e gs rest (pop-nosym s bs b1 e2 e pp y ne)) (AddZero r) (PaMiss us0 j q1 q b1 u1 ub1 Q0 gs rest r ap pc))))
      (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 j q r b1 u1 ub1 Q0 gs rest pc))
      (values a k (ScY s bs b1 e gs rest a y m) ad pk))
    ((ChNone _ _ _ _ _ ip _ _)
      (values (Zero) r (ScN s bs e gs rest (match erased ip _ ((IP0) (NsP0E e)) ((IP1) (NsP1E e)))) (AddZero r) pc))))

(def-fns _ $ (erased ch-miss : (erased (List Cnt) us0) (erased (Nat) j p q q2 r) (erased (Gsym) s) (erased (Bstack) bs) (erased (Ctree) t)
    (erased (Tally us0 (Succ j) p t) tb) (erased (List (Pr us0 j)) Q0 Q) (erased (GSet) gs) (erased (Col) e) (erased (List (Col)) rest)
    (erased (Ch us0 j s (MkPr us0 (Succ j) p bs t tb) Q0 Q) ch) (erased (Apart (Nat) Lt p q) ap) (erased (Kid q e q2) kq)
    (erased (PairCnt us0 j Q0 gs q2 rest r) pc) -> (erased (PairCnt us0 j Q gs q2 rest r) pk))
  (match erased ch _
    ((ChSkip _ _ _ q1 _ _ u1 _ ub1 k1 _) (PaMiss us0 j q1 q2 bs u1 ub1 Q0 gs rest r (kid-apart p q q1 q2 (C1) e ap k1 kq) pc))
    ((ChPush _ _ _ q3 q4 _ _ u3 u4 _ b3 b4 k3 k4 _)
      (PaMiss us0 j q3 q2 (BP0 bs) u3 b3 _ gs rest r (kid-apart p q q3 q2 (C2) e ap k3 kq)
        (PaMiss us0 j q4 q2 (BP1 bs) u4 b4 Q0 gs rest r (kid-apart p q q4 q2 (C3) e ap k4 kq) pc)))
    ((ChPop _ _ _ q1 _ e2 _ b1 _ u1 _ ub1 _ _ k1 _) (PaMiss us0 j q1 q2 b1 u1 ub1 Q0 gs rest r (kid-apart p q q1 q2 e2 e ap k1 kq) pc))
    ((ChNone _ _ _ _ _ _ _ _) pc)))

(def-fns _ $ (erased mc-sum : (erased (GSet) gs g0 g1 g2 g3) (erased (Bstack) bs) (erased (Col) e) (erased (List (Col)) rest) (erased (Nat) c0 c1 c2 c3 q q2)
    (erased (Kid q e q2) kq) (erased (GSel gs (GPush) g0) s0) (erased (GSel gs (GSkip) g1) s1) (erased (GSel gs (GPop0) g2) s2) (erased (GSel gs (GPop1) g3) s3)
    (erased (SymC (GPush) bs e g0 rest c0) y0) (erased (SymC (GSkip) bs e g1 rest c1) y1) (erased (SymC (GPop0) bs e g2 rest c2) y2)
    (erased (SymC (GPop1) bs e g3 rest c3) y3) -> (erased (Nat) n) (erased (Sum4 c0 c1 c2 c3 n) sm) (erased (MC gs bs (Cons (Col) e rest) n) r))
  (let ((erased none) (erased some)) (values symc-none symc-some))
  (match erased e _
    (absurd (C0) kq)
    ((C1)
      (let-match erased (none _ _ _ _ _ c0 y0 (NsPu1 bs)) (Refl _ _))
      (let-match erased (none _ _ _ _ _ c2 y2 (NsP01 bs)) (Refl _ _))
      (let-match erased (none _ _ _ _ _ c3 y3 (NsP11 bs)) (Refl _ _))
      (values c1 (MkSum4 (Zero) c1 (Zero) (Zero) c1 c1 c1 (AddZero c1) (add-zero-right c1) (add-zero-right c1))
        (MCSkip gs g1 bs rest c1 s1 (some _ _ bs _ _ _ c1 y1 (SSkip bs)))))
    ((C2)
      (let-match erased (none _ _ _ _ _ c1 y1 (NsSk2 bs)) (Refl _ _))
      (match erased bs _
        ((BS0)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP0E (C2))) (Refl _ _))
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP1E (C2))) (Refl _ _))
          (values c0 (MkSum4 c0 (Zero) (Zero) (Zero) c0 c0 c0 (add-zero-right c0) (add-zero-right c0) (add-zero-right c0))
            (MCPush gs g0 (BP0 bs) (C2) rest c0 (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs)))))
        ((BP0 b)
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP12 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased sm) (erased _)) (sum4-pp c0 c2))
          (values n sm (MCPP gs g0 g2 bs b (BP0 bs) (GPop0) (C2) rest c0 c2 n (Popped0 b) (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs))
            (SPop02 b) s2 (some _ _ b _ _ _ c2 y2 (SPop02 b)) ad)))
        ((BP1 b)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP02 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased _) (erased sm)) (sum4-pp c0 c3))
          (values n sm (MCPP gs g0 g3 bs b (BP0 bs) (GPop1) (C2) rest c0 c3 n (Popped1 b) (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs))
            (SPop12 b) s3 (some _ _ b _ _ _ c3 y3 (SPop12 b)) ad)))))
    ((C3)
      (let-match erased (none _ _ _ _ _ c1 y1 (NsSk3 bs)) (Refl _ _))
      (match erased bs _
        ((BS0)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP0E (C3))) (Refl _ _))
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP1E (C3))) (Refl _ _))
          (values c0 (MkSum4 c0 (Zero) (Zero) (Zero) c0 c0 c0 (add-zero-right c0) (add-zero-right c0) (add-zero-right c0))
            (MCPush gs g0 (BP1 bs) (C3) rest c0 (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs)))))
        ((BP0 b)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP03 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased _) (erased sm)) (sum4-pp c0 c3))
          (values n sm (MCPP gs g0 g3 bs b (BP1 bs) (GPop1) (C3) rest c0 c3 n (Popped0 b) (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs))
            (SPop13 b) s3 (some _ _ b _ _ _ c3 y3 (SPop13 b)) ad)))
        ((BP1 b)
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP13 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased sm) (erased _)) (sum4-pp c0 c2))
          (values n sm (MCPP gs g0 g2 bs b (BP1 bs) (GPop0) (C3) rest c0 c2 n (Popped1 b) (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs))
            (SPop03 b) s2 (some _ _ b _ _ _ c2 y2 (SPop03 b)) ad)))))))

(def-fns _ $ (erased sum4-add : (erased (Nat) c0 c1 c2 c3 r0 r1 r2 r3 k0 k1 k2 k3 a b k) (erased (Add c0 r0 k0) d0) (erased (Add c1 r1 k1) d1)
    (erased (Add c2 r2 k2) d2) (erased (Add c3 r3 k3) d3) (erased (Sum4 c0 c1 c2 c3 a) sa) (erased (Sum4 r0 r1 r2 r3 b) sb) (erased (Add a b k) ad)
    -> (erased (Sum4 k0 k1 k2 k3 k) r))
  (let-match erased sa (MkSum4 _ _ _ _ _ cx cy a1 a2 a3))
  (let-match erased sb (MkSum4 _ _ _ _ _ rx ry b1 b2 b3))
  (let ((erased kx) (erased e1)) (add k0 k1))
  (let ((erased ky) (erased e2)) (add kx k2))
  (let ((erased kz) (erased e3)) (add ky k3))
  (let ((erased f1)) (add-swap c0 r0 k0 c1 r1 k1 kx cx rx d0 d1 e1 a1 b1))
  (let ((erased f2)) (add-swap cx rx kx c2 r2 k2 ky cy ry f1 d2 e2 a2 b2))
  (let-match erased (add-fn a b kz k (add-swap cy ry ky c3 r3 k3 kz a b f2 d3 e3 a3 b3) ad) (Refl _ _))
  (MkSum4 k0 k1 k2 k3 k kx ky e1 e2 e3))

(def-fns _ $ (erased pcnt-split : (erased (List Cnt) us0) (erased (Nat) j q q2 c) (erased (List (Pr us0 (Succ j))) P) (erased (GSet) gs g0 g1 g2 g3)
    (erased (GSel gs (GPush) g0) s0) (erased (GSel gs (GSkip) g1) s1) (erased (GSel gs (GPop0) g2) s2) (erased (GSel gs (GPop1) g3) s3)
    (erased (Col) e) (erased (List (Col)) rest) (erased (Kid q e q2) kq) (erased (List (Pr us0 j)) Ps0 Ps1 Ps2 Ps3)
    (erased (Stp us0 j (GPush) P Ps0) t0) (erased (Stp us0 j (GSkip) P Ps1) t1) (erased (Stp us0 j (GPop0) P Ps2) t2) (erased (Stp us0 j (GPop1) P Ps3) t3)
    (subterm erased (PairCnt us0 (Succ j) P gs q (Cons (Col) e rest) c) pc) ->
    (erased (Nat) k0 k1 k2 k3) (erased (PairCnt us0 j Ps0 g0 q2 rest k0) p0) (erased (PairCnt us0 j Ps1 g1 q2 rest k1) p1) (erased (PairCnt us0 j Ps2 g2 q2 rest k2) p2)
    (erased (PairCnt us0 j Ps3 g3 q2 rest k3) p3) (erased (Sum4 k0 k1 k2 k3 c) sm))
  (let ((erased z)) (Zero))
  (let-match erased t0 (StpCons _ _ _ x Pt Q0 _ u0 h0)
    ((StpNil _ _ _)
      (let-match erased t1 (StpNil _ _ _))
      (let-match erased t2 (StpNil _ _ _))
      (let-match erased t3 (StpNil _ _ _))
      (let-match erased pc (PaNil _ _ _ _ _))
      (values z z z z (PaNil us0 j q2 g0 rest) (PaNil us0 j q2 g1 rest) (PaNil us0 j q2 g2 rest) (PaNil us0 j q2 g3 rest)
        (MkSum4 z z z z z z z (AddZero z) (AddZero z) (AddZero z)))))
  (let-match erased t1 (StpCons _ _ _ _ _ Q1 _ u1 h1))
  (let-match erased t2 (StpCons _ _ _ _ _ Q2 _ u2 h2))
  (let-match erased t3 (StpCons _ _ _ _ _ Q3 _ u3 h3))
  (match erased pc _
    ((PaHit _ _ _ bs t tb _ _ _ a cr _ m pc1 ad)
      (let ((erased r0) (erased r1) (erased r2) (erased r3) (erased w0) (erased w1) (erased w2) (erased w3) (erased sr))
        (pcnt-split us0 j q q2 cr Pt gs g0 g1 g2 g3 s0 s1 s2 s3 e rest kq Q0 Q1 Q2 Q3 u0 u1 u2 u3 pc1))
      (let ((erased c0) (erased k0) (erased y0) (erased d0) (erased v0)) (ch-symc us0 j q q2 r0 (GPush) bs t tb Q0 Ps0 g0 e rest h0 kq w0))
      (let ((erased c1) (erased k1) (erased y1) (erased d1) (erased v1)) (ch-symc us0 j q q2 r1 (GSkip) bs t tb Q1 Ps1 g1 e rest h1 kq w1))
      (let ((erased c2) (erased k2) (erased y2) (erased d2) (erased v2)) (ch-symc us0 j q q2 r2 (GPop0) bs t tb Q2 Ps2 g2 e rest h2 kq w2))
      (let ((erased c3) (erased k3) (erased y3) (erased d3) (erased v3)) (ch-symc us0 j q q2 r3 (GPop1) bs t tb Q3 Ps3 g3 e rest h3 kq w3))
      (let ((erased n) (erased sc) (erased mn)) (mc-sum gs g0 g1 g2 g3 bs e rest c0 c1 c2 c3 q q2 kq s0 s1 s2 s3 y0 y1 y2 y3))
      (let-match erased (mc-fn gs bs (Cons _ e rest) n a mn m) (Refl _ _))
      (values k0 k1 k2 k3 v0 v1 v2 v3 (sum4-add c0 c1 c2 c3 r0 r1 r2 r3 k0 k1 k2 k3 n cr c d0 d1 d2 d3 sc sr ad)))
    ((PaMiss _ _ p _ bs t tb _ _ _ _ ap pc1)
      (let ((erased r0) (erased r1) (erased r2) (erased r3) (erased w0) (erased w1) (erased w2) (erased w3) (erased sr))
        (pcnt-split us0 j q q2 c Pt gs g0 g1 g2 g3 s0 s1 s2 s3 e rest kq Q0 Q1 Q2 Q3 u0 u1 u2 u3 pc1))
      (values r0 r1 r2 r3 (ch-miss us0 j p q q2 r0 (GPush) bs t tb Q0 Ps0 g0 e rest h0 ap kq w0)
        (ch-miss us0 j p q q2 r1 (GSkip) bs t tb Q1 Ps1 g1 e rest h1 ap kq w1) (ch-miss us0 j p q q2 r2 (GPop0) bs t tb Q2 Ps2 g2 e rest h2 ap kq w2)
        (ch-miss us0 j p q q2 r3 (GPop1) bs t tb Q3 Ps3 g3 e rest h3 ap kq w3) sr))))

; No chromogram of gs matches a trace of j colours.
(def-adts $ (NoMC : ((GSet) gs) ((Nat) j) -> Type)
  enum
  (many NmE : (erased (Nat) j) -> (NoMC (GSG (GEmpty)) j))
  (many NmOne : (erased (Nat) j) -> (NoMC (GSOne) (Succ j)))
  (many NmG0 : (erased (Gtree) g) -> (NoMC (GSG g) (Zero)))
  (many NmLeaf : (erased (Gtree) g) (erased (Bits) q) (erased (Nat) j) (erased (LeafSet g q) l) -> (NoMC (GSG g) (Succ (Succ j)))))

(def-fns _ $ (erased nomc-mc : (erased (GSet) gs) (erased (Nat) j n) (erased (Bstack) bs) (erased (List (Col)) rest) (erased (NoMC gs j) z)
    (erased (Length (Col) rest j) le) (erased (MC gs bs rest n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased z _
    ((NmE _) (mc-zero bs rest n m))
    ((NmOne _) (let-match erased le (LengthCons _ e et _ _)) (mc-one-long bs e et n m))
    ((NmG0 _) (let-match erased le (LengthNil _)) (let-match erased m (MCNil _ _ _ rp)) (let-match erased rp (GRG _)) (Refl _ n))
    ((NmLeaf g q _ l)
      (let-match erased le (LengthCons _ e et _ le1))
      (let-match erased le1 (LengthCons _ e2 et2 _ _))
      (mc-leaf-long g q bs e e2 et2 n l m))))

(def-fns _ $ (erased pcnt-zero : (erased (List Cnt) us0) (erased (Nat) j q c) (erased (List (Pr us0 j)) P) (erased (GSet) gs) (erased (List (Col)) rest)
    (erased (NoMC gs j) z) (erased (Length (Col) rest j) le) (subterm erased (PairCnt us0 j P gs q rest c) pc) -> (erased (Eq (Nat) c (Zero)) r))
  (let-match erased pc (PaHit _ _ _ bs _ _ Pt _ _ a c1 _ m pc1 ad)
    ((PaNil _ _ _ _ _) (Refl _ c))
    ((PaMiss _ _ _ _ _ _ _ Pt _ _ _ _ pc1) (pcnt-zero us0 j q c Pt gs rest z le pc1)))
  (let-match erased (nomc-mc gs j a bs rest z le m) (Refl _ _))
  (let-match erased (pcnt-zero us0 j q c1 Pt gs rest z le pc1) (Refl _ _))
  (let-match erased ad (AddZero _))
  (Refl _ c))

; R is P, or nothing when gs is empty.
(def-adts $ (Pruned : ((List Cnt) us0) ((Nat) j) ((GSet) gs) ((List (Pr us0 j)) P) ((List (Pr us0 j)) R) -> Type)
  enum
  (many PrKeep : (erased (List Cnt) us0) (erased (Nat) j) (erased (GSet) gs) (erased (List (Pr us0 j)) P) -> (Pruned us0 j gs P P))
  (many PrDrop : (erased (List Cnt) us0) (erased (Nat) j) (erased (List (Pr us0 j)) P) -> (Pruned us0 j (GSG (GEmpty)) P (Nil (Pr us0 j)))))

(def-fns _ $ (erased prune-pc : (erased (List Cnt) us0) (erased (Nat) j q k) (erased (GSet) gs) (erased (List (Pr us0 j)) P R) (erased (List (Col)) rest)
    (erased (Pruned us0 j gs P R) pr) (erased (PairCnt us0 j P gs q rest k) pc) (erased (Length (Col) rest j) le) -> (erased (PairCnt us0 j R gs q rest k) r))
  (let-match erased pr (PrDrop _ _ _) ((PrKeep _ _ _ _) pc))
  (let-match erased (pcnt-zero us0 j q k P gs rest (NmE j) le pc) (Refl _ _))
  (PaNil us0 j q gs rest))

(def-adts $ (HitAll : ((List Cnt) us0) ((List (Pr us0 (Zero))) P) ((Sv) s) ((Sv) s2) -> Type)
  enum
  (many HaNil : (erased (List Cnt) us0) (erased (Sv) s) -> (HitAll us0 (Nil (Pr us0 (Zero))) s s))
  (many HaCons : (erased (List Cnt) us0) (erased (Nat) p) (erased (Bstack) bs) (erased (Ctree) t) (erased (Tally us0 (Zero) p t) tb)
      (erased (List (Pr us0 (Zero))) P) (erased (Sv) s s1 s2) (erased (Tick p s s1) tk) (erased (HitAll us0 P s1 s2) h)
      -> (HitAll us0 (Cons (Pr us0 (Zero)) (MkPr us0 (Zero) p bs t tb) P) s s2)))

; The walk of the pairs P down the chromograms gs, for traces of j more colours, takes s to s2.
(def-adts
  ((Wk : ((List Cnt) us0) ((Nat) j) ((GSet) gs) ((List (Pr us0 j)) P) ((Sv) s) ((Sv) s2) -> Type)
    enum
    (many WkNil : (erased (List Cnt) us0) (erased (Nat) j) (erased (GSet) gs) (erased (Sv) s) -> (Wk us0 j gs (Nil (Pr us0 j)) s s))
    (many WkZero : (erased (List Cnt) us0) (erased (Nat) j) (erased (GSet) gs) (erased (List (Pr us0 j)) P) (erased (Sv) s) (erased (NoMC gs j) z)
        -> (Wk us0 j gs P s s))
    (many WkHit : (erased (List Cnt) us0) (erased (List (Pr us0 (Zero))) P) (erased (Sv) s s2) (erased (HitAll us0 P s s2) h) -> (Wk us0 (Zero) (GSOne) P s s2))
    (many WkStep : (erased (List Cnt) us0) (erased (Nat) j) (erased (GSet) gs) (erased (List (Pr us0 (Succ j))) P) (erased (Sv) s0 s1 s2 s3 s4)
        (erased (WkSym us0 j gs P (GPush) s0 s1) w0) (erased (WkSym us0 j gs P (GSkip) s1 s2) w1) (erased (WkSym us0 j gs P (GPop0) s2 s3) w2)
        (erased (WkSym us0 j gs P (GPop1) s3 s4) w3) -> (Wk us0 (Succ j) gs P s0 s4)))
  ((WkSym : ((List Cnt) us0) ((Nat) j) ((GSet) gs) ((List (Pr us0 (Succ j))) P) ((Gsym) sym) ((Sv) s) ((Sv) s2) -> Type)
    enum
    (many MkWkSym : (erased (List Cnt) us0) (erased (Nat) j) (erased (GSet) gs gs1) (erased (List (Pr us0 (Succ j))) P) (erased (Gsym) sym)
        (erased (List (Pr us0 j)) Ps1 Ps2) (erased (Sv) s s2) (erased (GSel gs sym gs1) sl) (erased (Stp us0 j sym P Ps1) st) (erased (Pruned us0 j gs1 Ps1 Ps2) pr)
        (erased (Wk us0 j gs1 Ps2 s s2) w) -> (WkSym us0 j gs P sym s s2))))

(def-fns _ $ (erased hitall-trace : (erased (List Cnt) us0) (erased (List (Pr us0 (Zero))) P) (erased (Sv) s s2) (subterm erased (HitAll us0 P s s2) ha)
    (erased (Nat) i n0 k c) (erased (TrS s i n0 k) tr) (erased (PairCnt us0 (Zero) P (GSOne) i (Nil (Col)) c) pc) ->
    (erased (Nat) k2) (erased (Add k c k2) ad) (erased (TrS s2 i n0 k2) tr2))
  (match erased ha _
    ((HaNil _ _) (let-match erased pc (PaNil _ _ _ _ _)) (values k (add-zero-right k) tr))
    ((HaCons _ p _ _ _ Pt _ s1 _ tk ha1)
      (let-match erased pc (PaHit _ _ _ _ _ _ _ _ _ _ c1 _ m pc1 ad)
        ((PaMiss _ _ _ _ _ _ _ _ _ _ _ ap pc1) (hitall-trace us0 Pt s1 s2 ha1 i n0 k c (tick-other p i n0 k s s1 tk ap tr) pc1)))
      (let-match erased m (MCNil _ _ _ rp))
      (let-match erased rp (GROne))
      (let-match erased ad (AddSucc _ _ _ a0))
      (let-match erased a0 (AddZero _))
      (let ((erased k2) (erased a2) (erased tr2)) (hitall-trace us0 Pt s1 s2 ha1 i n0 (Succ k) c1 (tick-same i n0 k s s1 tk tr) pc1))
      (let-match erased a2 (AddSucc _ _ k3 a3))
      (values k2 (add-succ-right k c1 k3 a3) tr2))))

(def-fns _ $ (erased add4 : (erased (Nat) k k0 k1 k2 k3 a b c d s) (erased (Add k k0 a) p0) (erased (Add a k1 b) p1) (erased (Add b k2 c) p2)
    (erased (Add c k3 d) p3) (erased (Sum4 k0 k1 k2 k3 s) sm) -> (erased (Add k s d) r))
  (let-match erased sm (MkSum4 _ _ _ _ _ x y a1 a2 a3))
  (let ((erased x1) (erased q1) (erased r1)) (add-assoc k k0 k1 a b p0 p1))
  (let-match erased (add-fn k0 k1 x1 x q1 a1) (Refl _ _))
  (let ((erased y1) (erased q2) (erased r2)) (add-assoc k x k2 b c r1 p2))
  (let-match erased (add-fn x k2 y1 y q2 a2) (Refl _ _))
  (let ((erased z1) (erased q3) (erased r3)) (add-assoc k y k3 c d r2 p3))
  (let-match erased (add-fn y k3 z1 s q3 a3) (Refl _ _))
  r3)

(def-fns _ $ (erased wk-trace : (erased (List Cnt) us0) (erased (Nat) j i q n0 k c) (erased (GSet) gs) (erased (List (Pr us0 j)) P) (erased (Sv) s s2)
    (subterm erased (Wk us0 j gs P s s2) w) (erased (List (Col)) rest) (erased (TIdx q rest i) ti) (erased (Length (Col) rest j) le)
    (erased (TrS s i n0 k) tr) (erased (PairCnt us0 j P gs q rest c) pc) -> (erased (Nat) k2) (erased (Add k c k2) ad) (erased (TrS s2 i n0 k2) tr2))
  (match erased w _
    ((WkNil _ _ _ _) (let-match erased pc (PaNil _ _ _ _ _)) (values k (add-zero-right k) tr))
    ((WkZero _ _ _ _ _ z) (let-match erased (pcnt-zero us0 j q c P gs rest z le pc) (Refl _ _)) (values k (add-zero-right k) tr))
    ((WkHit _ _ _ _ ha) (let-match erased le (LengthNil _)) (let-match erased ti (TINil _)) (hitall-trace us0 P s s2 ha i n0 k c tr pc))
    ((WkStep _ j1 _ _ _ sa sb sc _ w0 w1 w2 w3)
      (let-match erased le (LengthCons _ e rest1 _ le1))
      (let-match erased ti (TICons _ q2 _ _ _ kq ti1))
      (let-match erased w0 (MkWkSym _ _ _ g0 _ _ Ps0 R0 _ _ sl0 st0 pr0 x0))
      (let-match erased w1 (MkWkSym _ _ _ g1 _ _ Ps1 R1 _ _ sl1 st1 pr1 x1))
      (let-match erased w2 (MkWkSym _ _ _ g2 _ _ Ps2 R2 _ _ sl2 st2 pr2 x2))
      (let-match erased w3 (MkWkSym _ _ _ g3 _ _ Ps3 R3 _ _ sl3 st3 pr3 x3))
      (let ((erased k0) (erased k1) (erased k2) (erased k3) (erased p0) (erased p1) (erased p2) (erased p3) (erased sm))
        (pcnt-split us0 j1 q q2 c P gs g0 g1 g2 g3 sl0 sl1 sl2 sl3 e rest1 kq Ps0 Ps1 Ps2 Ps3 st0 st1 st2 st3 pc))
      (let ((erased ka) (erased a0) (erased tra)) (wk-trace us0 j1 i q2 n0 k k0 g0 R0 s sa x0 rest1 ti1 le1 tr (prune-pc us0 j1 q2 k0 g0 Ps0 R0 rest1 pr0 p0 le1)))
      (let ((erased kb) (erased a1) (erased trb)) (wk-trace us0 j1 i q2 n0 ka k1 g1 R1 sa sb x1 rest1 ti1 le1 tra (prune-pc us0 j1 q2 k1 g1 Ps1 R1 rest1 pr1 p1 le1)))
      (let ((erased kc) (erased a2) (erased trc)) (wk-trace us0 j1 i q2 n0 kb k2 g2 R2 sb sc x2 rest1 ti1 le1 trb (prune-pc us0 j1 q2 k2 g2 Ps2 R2 rest1 pr2 p2 le1)))
      (let ((erased kd) (erased a3) (erased trd)) (wk-trace us0 j1 i q2 n0 kc k3 g3 R3 sc s2 x3 rest1 ti1 le1 trc (prune-pc us0 j1 q2 k3 g3 Ps3 R3 rest1 pr3 p3 le1)))
      (values kd (add4 k k0 k1 k2 k3 ka kb kc kd c a0 a1 a2 a3 sm) trd))))

; Clearing, for each index of T in turn, its gone entry in ws when its count in us is not 0, gives ws2.
(def-adts $ (Clears : ((List (Nat)) T) ((List Cnt) us) ((List Cnt) ws) ((List Cnt) ws2) -> Type)
  enum
  (many ClsNil : (erased (List Cnt) us ws) -> (Clears (Nil (Nat)) us ws ws))
  (many ClsZ : (erased (Nat) j) (erased (List (Nat)) T) (erased (List Cnt) us ws ws2) (erased (Ent us j (Zero)) e) (erased (Clears T us ws ws2) f)
      -> (Clears (Cons (Nat) j T) us ws ws2))
  (many ClsS : (erased (Nat) j n1) (erased (List (Nat)) T) (erased (List Cnt) us ws ws1 ws2) (erased (Ent us j (Succ n1)) e) (erased (Upd ws j (Zero) ws1) u)
      (erased (Clears T us ws1 ws2) f) -> (Clears (Cons (Nat) j T) us ws ws2)))

; x is x0 once cleared against the count n.
(def-adts $ (Fixed : ((Nat) n) ((Nat) x0) ((Nat) x) -> Type)
  enum
  (many FdS : (erased (Nat) n1 x0) -> (Fixed (Succ n1) x0 (Zero)))
  (many FdZ : (erased (Nat) x0) -> (Fixed (Zero) x0 x0)))

; The gone entry x of one index during the clearing: cleared, or still x0 with the index still to come in T.
(def-adts $ (Clr : ((Nat) n) ((Nat) x0) ((Nat) x) ((List (Nat)) T) ((Nat) i) -> Type)
  enum
  (many ClrDone : (erased (Nat) n x0 x i) (erased (List (Nat)) T) (erased (Fixed n x0 x) fd) -> (Clr n x0 x T i))
  (many ClrWait : (erased (Nat) n x0 i) (erased (List (Nat)) T) (erased (Elem (Nat) i T) el) -> (Clr n x0 x0 T i)))

(def-fns _ $ (erased has-clr : (erased (Nat) n x i) (erased (List (Nat)) T) (erased (HasT x T i) ht) -> (erased (Clr n x x T i) r))
  (match erased ht _
    ((HtZ _ _) (ClrDone n x x i T (match erased n _ ((Zero) (FdZ x)) ((Succ n1) (FdS n1 x)))))
    ((HtE _ _ _ el) (ClrWait n x i T el))))

(def-fns _ $ (erased clr-other : (erased (Nat) n x0 x i j) (erased (List (Nat)) T) (erased (Clr n x0 x (Cons (Nat) j T) i) p) (erased (Apart (Nat) Lt j i) ap)
    -> (erased (Clr n x0 x T i) r))
  (let-match erased p (ClrWait _ _ _ _ el) ((ClrDone _ _ _ _ _ fd) (ClrDone n x0 x i T fd)))
  (let-match erased el (ElThere _ _ _ _ el1) (absurd (ElHere _ _ _) (apart-irrefl i ap)))
  (ClrWait n x0 i T el1))

(def-fns _ $ (erased fix-trace : (erased (List (Nat)) T) (erased (List Cnt) us ws ws2) (subterm erased (Clears T us ws ws2) fx) (erased (Nat) i n x0 x)
    (erased (Ent us i n) eu) (erased (Ent ws i x) ew) (erased (Clr n x0 x T i) p) -> (erased (Nat) xf) (erased (Ent ws2 i xf) ef) (erased (Fixed n x0 xf) fd))
  (match erased fx _
    ((ClsNil _ _) (let-match erased p (ClrDone _ _ _ _ _ fd) (absurd (ClrWait _ _ _ _ el) el)) (values x ew fd))
    ((ClsZ j Tt _ _ _ ej fx1)
      (let-match erased (nat-eq j i) (Equal _ _ _)
        ((Unequal _ _ _ _ ap) (fix-trace Tt us ws ws2 fx1 i n x0 x eu ew (clr-other n x0 x i j Tt p ap))))
      (let-match erased (ent-fn us i n (Zero) eu ej) (Refl _ _))
      (fix-trace Tt us ws ws2 fx1 i n x0 x eu ew
        (ClrDone n x0 x i Tt (match erased p _ ((ClrDone _ _ _ _ _ fd) fd) ((ClrWait _ _ _ _ _) (FdZ x0))))))
    ((ClsS j n1 Tt _ _ ws1 _ ej uw fx1)
      (let-match erased (nat-eq j i) (Equal _ _ _)
        ((Unequal _ _ _ _ ap) (fix-trace Tt us ws1 ws2 fx1 i n x0 x eu (upd-other ws ws1 j (Zero) i x uw ap ew) (clr-other n x0 x i j Tt p ap))))
      (let-match erased (ent-fn us i n (Succ n1) eu ej) (Refl _ _))
      (fix-trace Tt us ws1 ws2 fx1 i n x0 (Zero) eu (upd-ent ws ws1 i (Zero) uw) (ClrDone n x0 (Zero) i Tt (FdS n1 x0))))))

; The gone entry g of a trace that had count n and keeps m: n if it lost its last count, otherwise 0.
(def-adts $ (GoneCnt : ((Nat) n) ((Nat) m) ((Nat) g) -> Type)
  enum
  (many GcGone : (erased (Nat) n) -> (GoneCnt n (Zero) n))
  (many GcKeep : (erased (Nat) n m1) -> (GoneCnt n (Succ m1) (Zero))))

(def-fns _ $ (erased gonecnt-fn : (erased (Nat) n m a b) (erased (GoneCnt n m a) p) (erased (GoneCnt n m b) q) -> (erased (Eq (Nat) a b) r))
  (match erased p _
    ((GcGone _) (let-match erased q (GcGone _)) (Refl _ a))
    ((GcKeep _ _) (let-match erased q (GcKeep _ _)) (Refl _ a))))

(def-fns _ $ (erased ds-final : (erased (Nat) n0 k n x0 xf) (erased (Ds n0 k n x0) st) (erased (Fixed n x0 xf) fd) ->
    (erased (Monus n0 k n) o) (erased (GoneCnt n0 n xf) gc))
  (let-match erased st (DsE _)
    ((DsU _) (values (MoZ n0) (match erased fd _ ((FdS n1 _) (GcKeep n0 n1)) ((FdZ _) (GcGone n0)))))
    ((DsT _ _ _ o) (values o (match erased fd _ ((FdS n1 _) (GcKeep n0 n1)) ((FdZ _) (GcGone n0))))))
  (let-match erased fd (FdZ _))
  (values (monus-zero k) (GcGone (Zero))))

; gone holds the traces of t of height j that keep lacks, with their counts in t.
(def-adts $ (GoneOf : ((Nat) j) ((Ctree) t) ((Ctree) keep) ((Ctree) gone) -> Type)
  enum
  (many GoE : (erased (Nat) j) (erased (Ctree) keep) -> (GoneOf j (CEmpty) keep (CEmpty)))
  (many GoL0 : (erased (Ctree) t) -> (GoneOf (Zero) t (CEmpty) t))
  (many GoL1 : (erased (Ctree) t lf) -> (GoneOf (Zero) t (CLeaf lf) (CEmpty)))
  (many GoN : (erased (Nat) j) (erased (Ctree) t1 t2 t3 keep k1 k2 k3 g1 g2 g3 gone) (erased (CtSel keep (C1) k1) s1) (erased (CtSel keep (C2) k2) s2)
      (erased (CtSel keep (C3) k3) s3) (erased (GoneOf j t1 k1 g1) o1) (erased (GoneOf j t2 k2 g2) o2) (erased (GoneOf j t3 k3 g3) o3)
      (erased (CtCons g1 g2 g3 gone) c) -> (GoneOf (Succ j) (CNode t1 t2 t3) keep gone)))

(def-fns _ $ (erased sel0-empty : (erased (Ctree) t v) (erased (CtSel t (C0) v) s) -> (erased (Eq (Ctree) v (CEmpty)) r))
  (match erased s _ ((SelN0 _ _ _) (Refl _ v)) ((SelL _ _) (Refl _ v)) ((SelE _) (Refl _ v))))

(def-fns _ $ (erased gone-sub : (erased (Nat) j n m) (erased (Ctree) t keep gone) (erased (List (Col)) et) (subterm erased (GoneOf j t keep gone) go)
    (erased (CtSub t et n) st) (erased (CtSub keep et m) sk) (erased (Length (Col) et j) le) -> (erased (Nat) g) (erased (CtSub gone et g) sg) (erased (GoneCnt n m g) gc))
  (match erased go _
    ((GoE _ _)
      (let-match erased (sub-fn (CEmpty) et n (Zero) st (empty-sub et)) (Refl _ _))
      (values (Zero) (empty-sub et) (match erased m _ ((Zero) (GcGone (Zero))) ((Succ m1) (GcKeep (Zero) m1)))))
    ((GoL0 _)
      (let-match erased le (LengthNil _))
      (let-match erased sk (SubNil _ _ rk))
      (let-match erased rk (RootE))
      (values n st (GcGone n)))
    ((GoL1 _ lf)
      (let-match erased le (LengthNil _))
      (let-match erased sk (SubNil _ _ rk))
      (let-match erased rk (RootL _ m1 _))
      (values (Zero) (SubNil (CEmpty) (Zero) (RootE)) (GcKeep n m1)))
    ((GoN j1 t1 t2 t3 _ k1 k2 k3 g1 g2 g3 _ s1 s2 s3 o1 o2 o3 c)
      (let-match erased le (LengthCons _ e et1 _ le1))
      (let-match erased st (SubCons _ u _ _ _ su st1))
      (let-match erased sk (SubCons _ v _ _ _ sv sk1))
      (match erased su _
        ((SelN0 _ _ _)
          (let-match erased (sub-fn (CEmpty) et1 n (Zero) st1 (empty-sub et1)) (Refl _ _))
          (let-match erased (sel0-empty keep v sv) (Refl _ _))
          (let-match erased (sub-fn (CEmpty) et1 m (Zero) sk1 (empty-sub et1)) (Refl _ _))
          (values (Zero) (SubCons gone (CEmpty) (C0) et1 (Zero) (cons-sel-back g1 g2 g3 gone (CEmpty) (C0) c (SelN0 g1 g2 g3)) (empty-sub et1))
            (GcGone (Zero))))
        ((SelN1 _ _ _)
          (let-match erased (sel-fn keep v k1 (C1) sv s1) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t1 k1 g1 et1 o1 st1 sk1 le1))
          (values g (SubCons gone g1 (C1) et1 g (cons-sel-back g1 g2 g3 gone g1 (C1) c (SelN1 g1 g2 g3)) sg) gc))
        ((SelN2 _ _ _)
          (let-match erased (sel-fn keep v k2 (C2) sv s2) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t2 k2 g2 et1 o2 st1 sk1 le1))
          (values g (SubCons gone g2 (C2) et1 g (cons-sel-back g1 g2 g3 gone g2 (C2) c (SelN2 g1 g2 g3)) sg) gc))
        ((SelN3 _ _ _)
          (let-match erased (sel-fn keep v k3 (C3) sv s3) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t3 k3 g3 et1 o3 st1 sk1 le1))
          (values g (SubCons gone g3 (C3) et1 g (cons-sel-back g1 g2 g3 gone g3 (C3) c (SelN3 g1 g2 g3)) sg) gc))))))

(def-fns _ $ (erased cons-sel3 : (erased (Ctree) a1 a2 a3 t) (erased (CtCons a1 a2 a3 t) c) ->
    (erased (CtSel t (C1) a1) s1) (erased (CtSel t (C2) a2) s2) (erased (CtSel t (C3) a3) s3))
  (values (cons-sel-back a1 a2 a3 t a1 (C1) c (SelN1 a1 a2 a3)) (cons-sel-back a1 a2 a3 t a2 (C2) c (SelN2 a1 a2 a3))
    (cons-sel-back a1 a2 a3 t a3 (C3) c (SelN3 a1 a2 a3))))

(def-fns _ $ (erased gone-self : (erased (Nat) j) (erased (Ctree) t) (subterm erased (CtH j t) k) -> (erased (GoneOf j t t (CEmpty)) r))
  (let-match erased k (HN j1 t1 t2 t3 k1 k2 k3) ((HE _) (GoE j (CEmpty))) ((HL lf _) (GoL1 t lf)))
  (let ((erased e)) (CEmpty))
  (GoN j1 t1 t2 t3 t t1 t2 t3 e e e e (SelN1 t1 t2 t3) (SelN2 t1 t2 t3) (SelN3 t1 t2 t3) (gone-self j1 t1 k1) (gone-self j1 t2 k2) (gone-self j1 t3 k3)
    (CCEmpty)))

(def-fns _ $ (erased ife-tight : (erased (Ctree) t l) (erased (CtH (Zero) t) ht) (erased (CtH (Zero) l) hl) ->
    (erased (Ctree) g) (erased (IfE t l g) f) (erased (GoneOf (Zero) t l g) go) (erased (CtH (Zero) g) hg))
  (match erased l _
    ((CEmpty) (values t (IEY t) (GoL0 t) ht))
    ((CLeaf lf) (values (CEmpty) (IEN t l) (GoL1 t lf) (HE (Zero))))
    (absurd (CNode _ _ _) hl)))

(def-fns _ $ (erased gone-tight : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (subterm erased (CRes h t r keep gone) c)
    (erased (CtCanon (Succ h) t) ct) -> (erased (Ctree) gone2) (erased (CRes h t r keep gone2) c2) (erased (CtCanon (Succ h) gone2) cg)
    (erased (GoneOf (Succ h) t keep gone2) go))
  (match erased c _
    ((CRNil _ _) (values (CEmpty) c (canon-empty (Succ h)) (gone-self (Succ h) t (canon-h (Succ h) t ct))))
    ((CRE _ _) (values (CEmpty) c (canon-empty (Succ h)) (GoE (Succ h) keep)))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 ck _)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let ((erased e1) (erased d1) (erased n1) (erased o1)) (gone-tight h1 t1 a1 b1 r1 c1 q1))
      (let ((erased e2) (erased d2) (erased n2) (erased o2)) (gone-tight h1 t2 a2 b2 r2 c2 q2))
      (let ((erased e3) (erased d3) (erased n3) (erased o3)) (gone-tight h1 t3 a3 b3 r3 c3 q3))
      (let ((erased g) (erased gc)) (cn-c e1 e2 e3))
      (let ((erased cs)) (cn-cons e1 e2 e3 g gc))
      (let ((erased k1) (erased k2) (erased k3)) (cons-sel3 a1 a2 a3 keep ck))
      (values g (CRS h1 t1 t2 t3 a1 a2 a3 e1 e2 e3 keep g r r1 r2 r3 s1 s2 s3 d1 d2 d3 ck cs) (CanN (Succ h1) e1 e2 e3 g n1 n2 n3 gc)
        (GoN (Succ h1) t1 t2 t3 keep a1 a2 a3 e1 e2 e3 g k1 k2 k3 o1 o2 o3 cs)))
    ((CRZ t1 t2 t3 l1 l2 l3 _ _ _ _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 ck _ _ _ _)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let-match erased q1 (CanL _ h1))
      (let-match erased q2 (CanL _ h2))
      (let-match erased q3 (CanL _ h3))
      (let-match erased d1 (MkDecrAll _ _ _ _ _ _ _ m1 _ _))
      (let-match erased d2 (MkDecrAll _ _ _ _ _ _ _ m2 _ _))
      (let-match erased d3 (MkDecrAll _ _ _ _ _ _ _ m3 _ _))
      (let ((erased e1) (erased f1) (erased o1) (erased y1)) (ife-tight t1 l1 h1 m1))
      (let ((erased e2) (erased f2) (erased o2) (erased y2)) (ife-tight t2 l2 h2 m2))
      (let ((erased e3) (erased f3) (erased o3) (erased y3)) (ife-tight t3 l3 h3 m3))
      (let ((erased g) (erased gc)) (cn-c e1 e2 e3))
      (let ((erased cs)) (cn-cons e1 e2 e3 g gc))
      (let ((erased k1) (erased k2) (erased k3)) (cons-sel3 l1 l2 l3 keep ck))
      (values g (CRZ t1 t2 t3 l1 l2 l3 e1 e2 e3 keep g r n1 n2 n3 p1 p2 p3 d1 d2 d3 ck f1 f2 f3 cs)
        (CanN (Zero) e1 e2 e3 g (CanL e1 y1) (CanL e2 y2) (CanL e3 y3) gc) (GoN (Zero) t1 t2 t3 keep l1 l2 l3 e1 e2 e3 g k1 k2 k3 o1 o2 o3 cs)))))

; L entries of us are not 0.
(def-adts $ (NzCnt : ((List Cnt) us) ((Nat) L) -> Type)
  enum
  (many NzNil : -> (NzCnt (Nil Cnt) (Zero)))
  (many NzZ : (erased (Lt (Zero) u62-modulus) b) (erased (List Cnt) us) (erased (Nat) L) (erased (NzCnt us L) z)
      -> (NzCnt (Cons Cnt (MkCopy (U62) (MkU62 (Zero) b)) us) L))
  (many NzS : (erased (Nat) n L) (erased (Lt (Succ n) u62-modulus) b) (erased (List Cnt) us) (erased (NzCnt us L) z)
      -> (NzCnt (Cons Cnt (MkCopy (U62) (MkU62 (Succ n) b)) us) (Succ L))))

; L2 is L less one when n is 0.
(def-adts $ (Drop : ((Nat) n) ((Nat) L) ((Nat) L2) -> Type)
  enum
  (many DrZ : (erased (Nat) L) -> (Drop (Zero) (Succ L) L))
  (many DrS : (erased (Nat) m L) -> (Drop (Succ m) L L)))

(def-fns _ $ (erased drop-succ : (erased (Nat) n L L2) (erased (Drop n L L2) d) -> (erased (Drop n (Succ L) (Succ L2)) r))
  (match erased d _ ((DrZ _) (DrZ (Succ L2))) ((DrS m _) (DrS m (Succ L)))))

(def-fns _ $ (erased nz-set : (erased (List Cnt) us vs) (erased (Nat) i n1 L) (erased (Lt (Succ n1) u62-modulus) b) (erased (Lt n1 u62-modulus) b1)
    (erased (NzCnt us L) z) (erased (Nth Cnt us i (MkCopy (U62) (MkU62 (Succ n1) b))) x)
    (subterm erased (SetNth Cnt us i (MkCopy (U62) (MkU62 n1 b1)) vs) s) -> (erased (Nat) L2) (erased (NzCnt vs L2) z2) (erased (Drop n1 L L2) d))
  (match erased s _
    ((SetHere _ _ _ rest)
      (let-match erased x (NthHere _ _ _))
      (let-match erased z (NzS _ L1 _ _ z1))
      (match erased n1 _
        ((Zero) (values L1 (NzZ b1 rest L1 z1) (DrZ L1)))
        ((Succ m) (values L (NzS m L1 b1 rest z1) (DrS m L)))))
    ((SetThere _ _ rest ix _ rest2 s1)
      (let-match erased x (NthThere _ _ _ _ _ x1))
      (match erased z _
        ((NzZ c _ _ z1) (let ((erased L2) (erased z2) (erased d)) (nz-set rest rest2 ix n1 L b b1 z1 x1 s1)) (values L2 (NzZ c rest2 L2 z2) d))
        ((NzS m L1 c _ z1)
          (let ((erased L2) (erased z2) (erased d)) (nz-set rest rest2 ix n1 L1 b b1 z1 x1 s1))
          (values (Succ L2) (NzS m L2 c rest2 z2) (drop-succ n1 L1 L2 d)))))))

(def-fns _ $ (erased nz-zero : (erased (List Cnt) us) (erased (Nat) i n) (erased (Lt n u62-modulus) b) (erased (NzCnt us (Zero)) z)
    (subterm erased (Nth Cnt us i (MkCopy (U62) (MkU62 n b))) x) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased x _
    ((NthHere _ _ _) (let-match erased z (NzZ _ _ _ _)) (Refl _ n))
    ((NthThere _ _ rest ix _ x1) (let-match erased z (NzZ _ _ _ z1)) (nz-zero rest ix n b z1 x1))))

(def-fns _ $ (erased tally-zero : (erased (List Cnt) us) (erased (Nat) j p) (erased (Ctree) t) (erased (NzCnt us (Zero)) z) (subterm erased (Tally us j p t) tb)
    -> (erased (Eq (Ctree) t (CEmpty)) r))
  (match erased tb _
    ((TaL _ _ n nb _ x rt k)
      (let-match erased (nz-zero us p n nb z x) (Refl _ _))
      (let-match erased rt (RootE) (absurd (RootN _ _ _) k))
      (Refl _ t))
    ((TaN _ j1 _ q t1 t2 t3 _ _ b1 b2 b3 cn)
      (let-match erased (tally-zero us j1 q t1 z b1) (Refl _ _))
      (let-match erased (tally-zero us j1 (Succ q) t2 z b2) (Refl _ _))
      (let-match erased (tally-zero us j1 (Succ (Succ q)) t3 z b3) (Refl _ _))
      (let-match erased cn (CnE) (absurd (CnN _ _ _ o) (occ3-empty o)))
      (Refl _ t))))

; What the walk keeps true of its whole state: both arrays of length len, T within them, L live counts.
(def-adts $ (Glob : ((Nat) len) ((Sv) s) ((Nat) L) -> Type)
  enum
  (many MkGlob : (erased (Nat) len L) (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Length Cnt us len) lu) (erased (Length Cnt ws len) lw)
      (erased (AllLt T len) al) (erased (NzCnt us L) z) -> (Glob len (MkSv us ws T) L)))

(def-fns _ $ (many drop-c : (many (Nat) n L) (erased (Nat) L2) (erased (Drop n L L2) d) -> (many L2 is r))
  (let-match many n (Zero) ((Succ _) (let-match erased d (DrS _ _)) L))
  (let-match erased d (DrZ _))
  (let-match many L (Succ L1))
  L1)

(def-fns _ $ (many tick-c : (erased (Nat) len) (many (Nat) i) (erased (Lt i len) il) (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g)
    (many (List (Nat)) T) (many (Nat) L) (erased (Glob len (MkSv us ws T) L) gl) ->
    (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2) (many (Nat) L2)
    (erased (Glob len (MkSv us2 ws2 T2) L2) gl2) (erased (Tick i (MkSv us ws T) (MkSv us2 ws2 T2)) tk))
  (let-match erased gl (MkGlob _ _ _ _ _ lu lw al z))
  (let ((erased ou) (erased xu)) (nth-exists _ us len i lu il))
  (let-match erased ou (MkCopy _ vu))
  (let-match erased vu (MkU62 n nb))
  (let ((many w) (unique a1)) (array-get _ us a i vu xu))
  (let-match many w (MkU62 m _))
  (let-match many m (Succ n1) ((Zero) (values us ws a1 g T L gl (TkZ i us ws T (MkEnt us i (Zero) nb xu)))))
  (let ((erased nb1)) (lt-trans n1 (Succ n1) u62-modulus (lt-succ n1) nb))
  (let ((unique x)) (MkCopy (U62) (MkU62 n1 nb1)))
  (let ((erased us2) (unique a2) (erased su)) (array-place-imm _ us a1 i x ou xu (imm-cnt ou) (imm-cnt x)))
  (let ((erased uu)) (MkUpd us us2 i n1 nb1 su))
  (let ((erased lu2)) (upd-len us us2 i n1 len uu lu))
  (let ((erased L2) (erased z2) (erased dr)) (nz-set us us2 i n1 L nb nb1 z xu su))
  (let ((many L3)) (drop-c n1 L L2 dr))
  (let ((erased og) (erased xg)) (nth-exists _ ws len i lw il))
  (let-match erased og (MkCopy _ vg))
  (let-match erased vg (MkU62 x0 xb))
  (let ((many wg) (unique g1)) (array-get _ ws g i vg xg))
  (let-match many wg (MkU62 mg _))
  (let ((erased eu)) (MkEnt us i (Succ n1) nb xu))
  (let-match many mg (Zero)
    ((Succ x1) (values us2 ws a2 g1 T L3 (MkGlob len L2 us2 ws T lu2 lw al z2) (TkS i n1 x1 us ws us2 T eu (MkEnt ws i (Succ x1) xb xg) uu))))
  (let ((unique y)) (MkCopy (U62) w))
  (let ((erased ws2) (unique g2) (erased sg)) (array-place-imm _ ws g1 i y og xg (imm-cnt og) (imm-cnt y)))
  (let ((erased uw)) (MkUpd ws ws2 i (Succ n1) nb sg))
  (values us2 ws2 a2 g2 (Cons _ i T) L3 (MkGlob len L2 us2 ws2 (Cons _ i T) lu2 (upd-len ws ws2 i (Succ n1) len uw lw) (ALCons i len T il al) z2)
    (TkF i n1 us ws us2 ws2 T eu (MkEnt ws i (Zero) xb xg) uu uw)))

(def-fns _ $ (many hitall-c : (erased (List Cnt) us0) (erased (Nat) len) (erased (Length Cnt us0 len) l0) (subterm many (List (Pr us0 (Zero))) P)
    (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g) (many (List (Nat)) T) (many (Nat) L) (erased (Glob len (MkSv us ws T) L) gl) ->
    (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2) (many (Nat) L2)
    (erased (Glob len (MkSv us2 ws2 T2) L2) gl2) (erased (HitAll us0 P (MkSv us ws T) (MkSv us2 ws2 T2)) h))
  (let-match many P (Cons _ x Pt) ((Nil _) (values us ws a g T L gl (HaNil us0 (MkSv us ws T)))))
  (let-match many x (MkPr _ _ i bs t tb))
  (let ((erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (many L1) (erased gl1) (erased tk))
    (tick-c len i (tally-lt us0 (Zero) i len t tb l0) us ws a g T L gl))
  (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (many L2) (erased gl2) (erased h)) (tail $ hitall-c us0 len l0 Pt us1 ws1 a1 g1 T1 L1 gl1))
  (values us2 ws2 a2 g2 T2 L2 gl2 (HaCons us0 i bs t tb Pt (MkSv us ws T) (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h)))

(def-fns _ $ (many pick4-s : (erased Type A) (many (Gsym) s) (many A x0 x1 x2 x3) -> (many A x) (erased (Pick4 A s x0 x1 x2 x3 x) p))
  (match many s _
    ((GPush) (values x0 (PkPush A x0 x1 x2 x3)))
    ((GSkip) (values x1 (PkSkip A x0 x1 x2 x3)))
    ((GPop0) (values x2 (PkPop0 A x0 x1 x2 x3)))
    ((GPop1) (values x3 (PkPop1 A x0 x1 x2 x3)))))

(def-fns _ $ (many gsel-s : (many (GSet) gs) (many (Gsym) s) -> (many (GSet) gs2) (erased (GSel gs s gs2) p))
  (let-match many gs (GSG g) ((GSOne) (values (GSG (GEmpty)) (GSelOne s))))
  (match many (gtree-kind g) _
    ((GKNode _ _ _ _ _ eq)
      (let-match erased eq (Refl _ _))
      (let-match many g (GNode t0 t1 t2 t3))
      (let ((many u) (erased pk)) (pick4-s (Gtree) s t0 t1 t2 t3))
      (values (GSG u) (GSelN t0 t1 t2 t3 u s pk)))
    ((GKLeaf _ q l)
      (let ((many b0) (many b1) (many b2) (many b3) (erased gb)) (gbits-c g))
      (let-match erased gb (GBLeaf _ _ l2) (absurd (GBNode _ _ _ _) l))
      (let-match erased (leafset-fn g q (MkBits b0 b1 b2 b3) l l2) (Refl _ _))
      (let ((many b) (erased pk)) (pick4-s (Bool) s b0 b1 b2 b3))
      (match many b _
        ((BTrue) (values (GSOne) (GSelL g b0 b1 b2 b3 b s (GSOne) l pk (BSetT))))
        ((BFalse) (values (GSG (GEmpty)) (GSelL g b0 b1 b2 b3 b s (GSG (GEmpty)) l pk (BSetF))))))))

(def-fns _ $ (many pr-kid : (erased (List Cnt) us0) (erased (Nat) j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb) (many (Nat) p)
    (erased (Ctree) t) (erased (Tally us0 (Succ j) p t) tb) (many (Col) e) (erased (Nat) q) (erased (Kid p e q) k) (many (Bstack) bs) ->
    (erased (Ctree) u) (erased (Tally us0 j q u) ub) (many (MkPr us0 j q bs u ub) is y))
  (let ((erased u) (erased ub) (erased _)) (tally-down us0 j p q t e tb k))
  (values u ub (MkPr us0 j (kid-c p e q k (lt-trans q len u62-modulus (tally-lt us0 j q len u ub l0) lb)) bs u ub)))

(def-fns _ $ (many pr-pop : (erased (List Cnt) us0) (erased (Nat) j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb) (many (Nat) p)
    (erased (Bstack) bs) (many (Bstack) b) (erased (Ctree) t) (erased (Tally us0 (Succ j) p t) tb) (erased (Gsym) s) (many (Col) e) (erased (Nat) q)
    (erased (Kid p e q) k) (erased (Popped bs b) pp) (erased (Sym s bs e b) y) (many (List (Pr us0 j)) Q0) ->
    (many (List (Pr us0 j)) Q) (erased (Ch us0 j s (MkPr us0 (Succ j) p bs t tb) Q0 Q) ch))
  (let ((erased u) (erased ub) (many z)) (pr-kid us0 j len l0 lb p t tb e q k b))
  (values (Cons _ z Q0) (ChPop us0 j p q s e bs b t u tb ub pp y k Q0)))

(def-fns _ $ (many pr-ch : (erased (List Cnt) us0) (erased (Nat) j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb) (many (Gsym) s)
    (many (Pr us0 (Succ j)) x) (many (List (Pr us0 j)) Q0) -> (many (List (Pr us0 j)) Q) (erased (Ch us0 j s x Q0 Q) ch))
  (let-match many x (MkPr _ _ p bs t tb))
  (let ((erased q) (erased tq)) (thrice-exists p))
  (let ((erased k1) (erased k2) (erased k3)) (values (Ki1 p q tq) (Ki2 p q tq) (Ki3 p q tq)))
  (match many s _
    ((GSkip)
      (let ((erased u) (erased ub) (many z)) (pr-kid us0 j len l0 lb p t tb (C1) q k1 bs))
      (values (Cons _ z Q0) (ChSkip us0 j p q bs t u tb ub k1 Q0)))
    ((GPush)
      (let ((erased u2) (erased b2) (many z2)) (pr-kid us0 j len l0 lb p t tb (C2) (Succ q) k2 (BP0 bs)))
      (let ((erased u3) (erased b3) (many z3)) (pr-kid us0 j len l0 lb p t tb (C3) (Succ (Succ q)) k3 (BP1 bs)))
      (values (Cons _ z2 (Cons _ z3 Q0)) (ChPush us0 j p (Succ q) (Succ (Succ q)) bs t u2 u3 tb b2 b3 k2 k3 Q0)))
    ((GPop0)
      (match many bs _
        ((BS0) (values Q0 (ChNone us0 j p s t (IP0) tb Q0)))
        ((BP0 b) (pr-pop us0 j len l0 lb p bs b t tb s (C2) (Succ q) k2 (Popped0 b) (SPop02 b) Q0))
        ((BP1 b) (pr-pop us0 j len l0 lb p bs b t tb s (C3) (Succ (Succ q)) k3 (Popped1 b) (SPop03 b) Q0))))
    ((GPop1)
      (match many bs _
        ((BS0) (values Q0 (ChNone us0 j p s t (IP1) tb Q0)))
        ((BP0 b) (pr-pop us0 j len l0 lb p bs b t tb s (C3) (Succ (Succ q)) k3 (Popped0 b) (SPop13 b) Q0))
        ((BP1 b) (pr-pop us0 j len l0 lb p bs b t tb s (C2) (Succ q) k2 (Popped1 b) (SPop12 b) Q0))))))

(def-fns _ $ (many pr-step : (erased (List Cnt) us0) (erased (Nat) j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb) (many (Gsym) s)
    (subterm many (List (Pr us0 (Succ j))) P) -> (many (List (Pr us0 j)) Q) (erased (Stp us0 j s P Q) st))
  (let-match many P (Cons _ x Pt) ((Nil _) (values (Nil _) (StpNil us0 j s))))
  (let ((many Q0) (erased st0)) (notail $ pr-step us0 j len l0 lb s Pt))
  (let ((many Q) (erased ch)) (pr-ch us0 j len l0 lb s x Q0))
  (values Q (StpCons us0 j s x Pt Q0 Q st0 ch)))

(def-fns _ $ (many gs-void : (many (GSet) gs) -> (many (Try (Eq (GSet) gs (GSG (GEmpty)))) r))
  (let-match many gs (GSG g) ((GSOne) (TryNo _)))
  (let-match many g (GEmpty) (else (TryNo _)))
  (TryOk _ (Refl _ gs)))

(def-fns _ $ (many prep : (erased (List Cnt) us0) (erased (Nat) j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb) (many (Gsym) s)
    (many (GSet) gs) (many (List (Pr us0 (Succ j))) P) -> (many (GSet) gs1) (erased (GSel gs s gs1) sl) (erased (List (Pr us0 j)) Ps1)
    (erased (Stp us0 j s P Ps1) st) (many (List (Pr us0 j)) R) (erased (Pruned us0 j gs1 Ps1 R) pr))
  (let ((many gs1) (erased sl)) (gsel-s gs s))
  (let-match many (gs-void gs1) (TryNo _)
    ((TryOk _ eq)
      (let-match erased eq (Refl _ _))
      (let ((erased Ps1) (erased st)) (pr-step us0 j len l0 lb s P))
      (values gs1 sl Ps1 st (Nil _) (PrDrop us0 j Ps1))))
  (let ((many Q) (erased st)) (pr-step us0 j len l0 lb s P))
  (values gs1 sl Q st Q (PrKeep us0 j gs1 Q)))

(def-fns _ $ (many skip-c : (many (GSet) gs) (many (Nat) j) -> (many (Try (NoMC gs j)) r))
  (let-match many gs (GSG g) ((GSOne) (match many j _ ((Zero) (TryNo _)) ((Succ j1) (TryOk _ (NmOne j1))))))
  (let-match many j (Succ j1) ((Zero) (TryOk _ (NmG0 g))))
  (let-match many (gtree-kind g) (GKLeaf _ q l) ((GKNode _ _ _ _ _ _) (TryNo _)))
  (match many j1 _ ((Zero) (TryNo _)) ((Succ j2) (TryOk _ (NmLeaf g q j2 l)))))

(def-fns _ $ (many swalk : (erased (List Cnt) us0) (erased (Nat) len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (subterm many (Nat) j) (many (GSet) gs) (many (List (Pr us0 j)) P) (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g)
    (many (List (Nat)) T) (many (Nat) L) (erased (Glob len (MkSv us ws T) L) gl) ->
    (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2) (many (Nat) L2)
    (erased (Glob len (MkSv us2 ws2 T2) L2) gl2) (erased (Wk us0 j gs P (MkSv us ws T) (MkSv us2 ws2 T2)) w))
  (let ((erased s)) (MkSv us ws T))
  (let-match many P (Cons _ _ _) ((Nil _) (values us ws a g T L gl (WkNil us0 j gs s))))
  (let-match many (skip-c gs j) (TryNo _) ((TryOk _ z) (values us ws a g T L gl (WkZero us0 j gs P s z))))
  (let-match many j (Succ j1)
    ((Zero)
      (let-match many gs (GSOne) ((GSG gt) (values us ws a g T L gl (WkZero us0 j gs P s (NmG0 gt)))))
      (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (many L2) (erased gl2) (erased h)) (hitall-c us0 len l0 P us ws a g T L gl))
      (values us2 ws2 a2 g2 T2 L2 gl2 (WkHit us0 P s (MkSv us2 ws2 T2) h))))
  (let ((many gs0) (erased sl0) (erased Ps0) (erased st0) (many R0) (erased pr0)) (prep us0 j1 len l0 lb (GPush) gs P))
  (let ((erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (many L1) (erased gl1) (erased x0))
    (notail $ swalk us0 len l0 lb j1 gs0 R0 us ws a g T L gl))
  (let ((many gs1) (erased sl1) (erased Ps1) (erased st1) (many R1) (erased pr1)) (prep us0 j1 len l0 lb (GSkip) gs P))
  (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (many L2) (erased gl2) (erased x1))
    (notail $ swalk us0 len l0 lb j1 gs1 R1 us1 ws1 a1 g1 T1 L1 gl1))
  (let ((many gs2) (erased sl2) (erased Ps2) (erased st2) (many R2) (erased pr2)) (prep us0 j1 len l0 lb (GPop0) gs P))
  (let ((erased us3) (erased ws3) (unique a3) (unique g3) (many T3) (many L3) (erased gl3) (erased x2))
    (notail $ swalk us0 len l0 lb j1 gs2 R2 us2 ws2 a2 g2 T2 L2 gl2))
  (let ((many gs3) (erased sl3) (erased Ps3) (erased st3) (many R3) (erased pr3)) (prep us0 j1 len l0 lb (GPop1) gs P))
  (let ((erased us4) (erased ws4) (unique a4) (unique g4) (many T4) (many L4) (erased gl4) (erased x3))
    (tail $ swalk us0 len l0 lb j1 gs3 R3 us3 ws3 a3 g3 T3 L3 gl3))
  (let ((erased s1) (erased s2) (erased s3) (erased s4)) (values (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) (MkSv us3 ws3 T3) (MkSv us4 ws4 T4)))
  (values us4 ws4 a4 g4 T4 L4 gl4
    (WkStep us0 j1 gs P s s1 s2 s3 s4 (MkWkSym us0 j1 gs gs0 P (GPush) Ps0 R0 s s1 sl0 st0 pr0 x0) (MkWkSym us0 j1 gs gs1 P (GSkip) Ps1 R1 s1 s2 sl1 st1 pr1 x1)
      (MkWkSym us0 j1 gs gs2 P (GPop0) Ps2 R2 s2 s3 sl2 st2 pr2 x2) (MkWkSym us0 j1 gs gs3 P (GPop1) Ps3 R3 s3 s4 sl3 st3 pr3 x3))))

(def-fns _ $ (many fix-c : (erased (Nat) len) (subterm many (List (Nat)) T) (erased (AllLt T len) al) (erased (List Cnt) us ws) (unique (Array Cnt us) a)
    (unique (Array Cnt ws) g) (erased (Length Cnt us len) lu) (erased (Length Cnt ws len) lw) ->
    (erased (List Cnt) ws2) (unique a is a2 at a) (unique (Array Cnt ws2) g2 at g) (erased (Length Cnt ws2 len) lw2) (erased (Clears T us ws ws2) fx))
  (let-match many T (Cons _ j Tt) ((Nil _) (values ws a g lw (ClsNil us ws))))
  (let-match erased al (ALCons _ _ _ jl al1))
  (let ((erased ou) (erased xu)) (nth-exists _ us len j lu jl))
  (let-match erased ou (MkCopy _ vu))
  (let-match erased vu (MkU62 n nb))
  (let ((many w) (unique a1)) (array-get _ us a j vu xu))
  (let-match many w (MkU62 m _))
  (let-match many m (Succ n1)
    ((Zero)
      (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (tail $ fix-c len Tt al1 us ws a1 g lu lw))
      (values ws2 a2 g2 lw2 (ClsZ j Tt us ws ws2 (MkEnt us j (Zero) nb xu) fx))))
  (let ((erased og) (erased xg)) (nth-exists _ ws len j lw jl))
  (let ((unique y)) (MkCopy (U62) (MkU62 (Zero) u62-modulus-pos)))
  (let ((erased ws1) (unique g1) (erased sg)) (array-place-imm _ ws g j y og xg (imm-cnt og) (imm-cnt y)))
  (let ((erased uw)) (MkUpd ws ws1 j (Zero) u62-modulus-pos sg))
  (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (tail $ fix-c len Tt al1 us ws1 a1 g1 lu (upd-len ws ws1 j (Zero) len uw lw)))
  (values ws2 a2 g2 lw2 (ClsS j n1 Tt us ws ws1 ws2 (MkEnt us j (Succ n1) nb xu) uw fx)))

; What a finished S walk from us and the zero array ws to us1 and ws2 established, with the restriction of ctu by gtr.
(def-adts $ (SDone : ((Nat) h) ((List Cnt) us1) ((List Cnt) ws2) ((Ctree) keep) ((Ctree) gone) -> Type)
  enum
  (many MkSDone : (erased (Nat) h) (erased (Ctree) ctu keep gone) (erased (Gtree) gtr) (erased (List Cnt) us ws us1 ws1 ws2) (erased (List (Nat)) T)
      (erased (Tally us (Succ h) (Zero) ctu) tb) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz)
      (erased (Wk us (Succ h) (GSG gtr) (Cons (Pr us (Succ h)) (MkPr us (Succ h) (Zero) (BS0) ctu tb) (Nil (Pr us (Succ h)))) (MkSv us ws (Nil (Nat)))
        (MkSv us1 ws1 T)) w)
      (erased (Clears T us1 ws1 ws2) fx) (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) c) (erased (CtH (Succ h) ctu) hc)
      (erased (GoneOf (Succ h) ctu keep gone) go) -> (SDone h us1 ws2 keep gone)))

(def-fns _ $ (erased trace-final : (erased (Nat) h i) (erased (List Cnt) us1 ws2) (erased (Ctree) keep gone) (erased (SDone h us1 ws2 keep gone) dn)
    (erased (List (Col)) et) (erased (TIdx (Zero) et i) ti) (erased (Length (Col) et (Succ h)) le) ->
    (erased (Nat) n x) (erased (Ent us1 i n) eu) (erased (CtSub keep et n) sk) (erased (Ent ws2 i x) ew) (erased (CtSub gone et x) sg))
  (let-match erased dn (MkSDone _ ctu _ _ gtr us ws _ ws1 _ T tb wz w fx c hc go))
  (let ((erased n0) (erased nb0) (erased x0) (erased s0)) (tally-sub us (Succ h) (Zero) i ctu et tb ti le))
  (let ((erased z) (erased zb) (erased xz) (erased sz)) (tally-sub ws (Succ h) (Zero) i (CEmpty) et wz ti le))
  (let-match erased (sub-fn (CEmpty) et z (Zero) sz (empty-sub et)) (Refl _ _))
  (let ((erased a) (erased m)) (mc-exists (GSG gtr) (BS0) et))
  (let ((erased k2) (erased ad) (erased tr))
    (wk-trace us (Succ h) i (Zero) n0 (Zero) a (GSG gtr) _ _ _ w et ti le
      (MkTrS us ws (Nil _) i n0 (Zero) n0 (Zero) (MkEnt us i n0 nb0 x0) (MkEnt ws i (Zero) zb xz) (DsU n0) (HtZ (Nil _) i))
      (PaHit us (Succ h) (Zero) (BS0) ctu tb (Nil _) (GSG gtr) et a (Zero) a m (PaNil us (Succ h) (Zero) (GSG gtr) et) (add-zero-right a))))
  (let-match erased ad (AddZero _))
  (let-match erased tr (MkTrS _ _ _ _ _ _ n xa eu ew st ht))
  (let ((erased x) (erased ew2) (erased fd)) (fix-trace T us1 ws1 ws2 fx i n xa xa eu ew (has-clr n xa i T ht)))
  (let ((erased o) (erased gc)) (ds-final n0 a n xa x st fd))
  (let-match erased (cres-sub h ctu keep gone (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) et n0 a c hc le s0
      (RCCons (BS0) gtr (Nil RG) et a (Zero) a m (RCNil et) (add-zero-right a))) (MkKeepSub _ _ _ _ m2 o2 sk))
  (let-match erased (monus-uniq n0 a n m2 o o2) (Refl _ _))
  (let ((erased g) (erased sg) (erased gc2)) (gone-sub (Succ h) n0 n ctu keep gone et go s0 sk le))
  (let-match erased (gonecnt-fn n0 n x g gc gc2) (Refl _ _))
  (values n x eu sk ew2 sg))

(def-fns _ $ (erased rev-exists : (subterm erased (List (Col)) pre) (erased (List (Col)) w) -> (erased (List (Col)) et) (erased (RevApp (Col) pre w et) ra))
  (let-match erased pre (Cons _ e pre1) ((Nil _) (values w (RANil _ w))))
  (let ((erased et) (erased ra)) (rev-exists pre1 (Cons _ e w)))
  (values et (RACons _ e pre1 w et ra)))

(def-fns _ $ (erased rev-len : (erased (List (Col)) pre w et) (erased (Nat) a b c) (subterm erased (RevApp (Col) pre w et) ra) (erased (Length (Col) pre a) la)
    (erased (Length (Col) w b) lw) (erased (Add a b c) ad) -> (erased (Length (Col) et c) r))
  (match erased ra _
    ((RANil _ _) (let-match erased la (LengthNil _)) (let-match erased ad (AddZero _)) lw)
    ((RACons _ e pre1 _ _ ra1)
      (let-match erased la (LengthCons _ _ _ a1 la1))
      (let-match erased ad (AddSucc _ _ c1 ad1))
      (rev-len pre1 (Cons _ e w) et a1 (Succ b) c ra1 la1 (LengthCons _ e w b lw) (add-succ-right a1 b c1 ad1)))))

(def-fns _ $ (erased pw-both : (erased (Nat) h) (erased (List Cnt) us1 ws2) (erased (Ctree) keep gone) (erased (SDone h us1 ws2 keep gone) dn)
    (subterm erased (Nat) j) (erased (Nat) p d) (erased (List (Col)) pre) (erased (RIdx pre p) ri) (erased (Length (Col) pre d) lp)
    (erased (Add j d (Succ h)) ad) -> (erased (Pointwise us1 keep j p pre) pk) (erased (Pointwise ws2 gone j p pre) pg))
  (let-match erased j (Succ j1)
    ((Zero)
      (let-match erased ad (AddZero _))
      (let ((erased et) (erased ra)) (rev-exists pre (Nil _)))
      (let ((erased ti)) (ridx-tidx pre (Nil _) et p p ri ra (TINil p)))
      (let ((erased n) (erased x) (erased eu) (erased sk) (erased ew) (erased sg))
        (trace-final h p us1 ws2 keep gone dn et ti (rev-len pre (Nil _) et d (Zero) d ra lp (LengthNil _) (add-zero-right d))))
      (let-match erased eu (MkEnt _ _ _ nb xn))
      (let-match erased ew (MkEnt _ _ _ xb xx))
      (values (PwL us1 keep p n nb pre et ra sk xn) (PwL ws2 gone p x xb pre et ra sg xx))))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (let ((erased ad2)) (add-succ-right j1 d h ad1))
  (let ((erased q) (erased tq)) (thrice-exists p))
  (let ((erased k1) (erased g1)) (pw-both h us1 ws2 keep gone dn j1 q (Succ d) (Cons _ (C1) pre) (RICons pre p q (C1) ri (Ki1 p q tq)) (LengthCons _ (C1) pre d lp) ad2))
  (let ((erased k2) (erased g2))
    (pw-both h us1 ws2 keep gone dn j1 (Succ q) (Succ d) (Cons _ (C2) pre) (RICons pre p (Succ q) (C2) ri (Ki2 p q tq)) (LengthCons _ (C2) pre d lp) ad2))
  (let ((erased k3) (erased g3))
    (pw-both h us1 ws2 keep gone dn j1 (Succ (Succ q)) (Succ d) (Cons _ (C3) pre) (RICons pre p (Succ (Succ q)) (C3) ri (Ki3 p q tq)) (LengthCons _ (C3) pre d lp) ad2))
  (values (PwN us1 keep j1 p q pre tq k1 k2 k3) (PwN ws2 gone j1 p q pre tq g1 g2 g3)))

(def-fns _ $ (many srestrict : (many (Nat) h) (many (Gtree) gtr) (erased (Ctree) ctu) (erased (Nat) len) (erased (Lt len u62-modulus) lb)
    (erased (List Cnt) us) (unique (Array Cnt us) a) (erased (Tally us (Succ h) (Zero) ctu) tb) (erased (Length Cnt us len) lu)
    (many (Nat) L) (erased (NzCnt us L) z)
    (erased (List Cnt) ws) (unique (Array Cnt ws) g) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz) (erased (Length Cnt ws len) lw) ->
    (erased (Ctree) keep gone) (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) c)
    (erased (CtH (Succ h) keep) hk) (erased (CtH (Succ h) gone) hg) (many (KeepE keep) e)
    (erased (List Cnt) us2) (unique (Array Cnt us2) a2 at a) (erased (Tally us2 (Succ h) (Zero) keep) tk) (erased (Length Cnt us2 len) lu2)
    (erased (Fit us2) fk) (many (Nat) L2) (erased (NzCnt us2 L2) z2)
    (erased (List Cnt) ws2) (unique (Array Cnt ws2) g2 at g) (erased (Tally ws2 (Succ h) (Zero) gone) tg) (erased (Length Cnt ws2 len) lw2)
    (erased (Fit ws2) fg) (many (List (Nat)) T))
  (let ((erased r)) (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)))
  (let ((erased ct)) (tally-canon us (Succ h) (Zero) ctu tb))
  (let ((erased hc)) (canon-h (Succ h) ctu ct))
  (let ((erased u0) (erased ut) (erased _)) (ut-of h ctu hc))
  (let ((erased _) (erased gone0) (erased keep0) (erased _) (erased c0) (erased _) (erased _))
    (ctree-restrict-u h u0 ctu ut r (RxCons (Gtree) (BS0) gtr (Nil RG) (RxNil (Gtree)))))
  (let ((erased keep) (erased c1) (erased kc)) (cres-canon h ctu keep0 gone0 r c0 ct))
  (let ((erased gone) (erased c) (erased gc) (erased go)) (gone-tight h ctu keep gone0 r c1 ct))
  (let ((many Ps0)) (Cons _ (MkPr us (Succ h) (Zero) (BS0) ctu tb) (Nil _)))
  (let ((erased us1) (erased ws1) (unique a1) (unique g1) (many T) (many L2) (erased gl) (erased w))
    (swalk us len lu lb (Succ h) (GSG gtr) Ps0 us ws a g (Nil _) L (MkGlob len L us ws (Nil _) lu lw (ALNil len) z)))
  (let-match erased gl (MkGlob _ _ _ _ _ lu1 lw1 al z2))
  (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (fix-c len T al us1 ws1 a1 g1 lu1 lw1))
  (let ((erased dn)) (MkSDone h ctu keep gone gtr us ws us1 ws1 ws2 T tb wz w fx c hc go))
  (let ((erased pk) (erased pg)) (pw-both h us1 ws2 keep gone dn (Succ h) (Zero) (Zero) (Nil _) (RINil) (LengthNil _) (add-zero-right (Succ h))))
  (let ((erased tk)) (tally-of-pointwise us1 keep keep (Succ h) (Zero) (Nil _) pk kc (AtNil keep)))
  (let ((many e))
    (match many L2 (((KeepE keep) e))
      ((Zero) (let-match erased (tally-zero us1 (Succ h) (Zero) keep z2 tk) (Refl _ _)) (KEmpty))
      ((Succ _) (KLive keep))))
  (values keep gone c (canon-h (Succ h) keep kc) (canon-h (Succ h) gone gc) e us1 a2 tk lu1 (MkFit us1 len lu1 lb) L2 z2
    ws2 g2 (tally-of-pointwise ws2 gone gone (Succ h) (Zero) (Nil _) pg gc (AtNil gone)) lw2 (MkFit ws2 len lw2 lb) T))

; r is us from index i on.
(def-adts $ (Sfx : ((List Cnt) us) ((Nat) i) ((List Cnt) r) -> Type)
  enum
  (many SfZ : (erased (List Cnt) us) -> (Sfx us (Zero) us))
  (many SfS : (erased Cnt x) (erased (List Cnt) rest r) (erased (Nat) i) (erased (Sfx rest i r) s) -> (Sfx (Cons Cnt x rest) (Succ i) r)))

(def-fns _ $ (erased sfx-nth : (erased (List Cnt) us r) (erased (Nat) i) (erased Cnt x) (subterm erased (Sfx us i (Cons Cnt x r)) s) -> (erased (Nth Cnt us i x) q))
  (match erased s _
    ((SfZ _) (NthHere _ x r))
    ((SfS y rest _ ix s1) (NthThere _ y rest ix x (sfx-nth rest r ix x s1)))))

(def-fns _ $ (erased sfx-step : (erased (List Cnt) us r) (erased (Nat) i) (erased Cnt x) (subterm erased (Sfx us i (Cons Cnt x r)) s) -> (erased (Sfx us (Succ i) r) q))
  (match erased s _
    ((SfZ _) (SfS x r r (Zero) (SfZ r)))
    ((SfS y rest _ ix s1) (SfS y rest r (Succ ix) (sfx-step rest r ix x s1)))))

(def-fns _ $ (many live-loop : (erased (List Cnt) us) (unique (Array Cnt us) a) (many (Nat) i) (erased (List Cnt) r) (erased (Sfx us i r) sf)
    (subterm many (Nat) k) (erased (Length Cnt r k) le) -> (many (Nat) L) (erased (NzCnt r L) z) (unique a is a2 at a))
  (let-match many k (Succ k1) ((Zero) (let-match erased le (LengthNil _)) (values (Zero) (NzNil) a)))
  (let-match erased le (LengthCons _ x r1 _ le1))
  (let-match erased x (MkCopy _ v))
  (let-match erased v (MkU62 n nb))
  (let ((many w) (unique a1)) (array-get _ us a i v (sfx-nth us r1 i x sf)))
  (let ((many L1) (erased z1) (unique a2)) (notail $ live-loop us a1 (Succ i) r1 (sfx-step us r1 i x sf) k1 le1))
  (let-match many w (MkU62 m _))
  (match many m _ ((Zero) (values L1 (NzZ nb r1 L1 z1) a2)) ((Succ m1) (values (Succ L1) (NzS m1 L1 nb r1 z1) a2))))

(def-fns _ $ (erased tally-zeros : (erased (List Cnt) us ws) (erased (Nat) j p len) (erased (Ctree) t) (subterm erased (Tally us j p t) tb)
    (erased (Length Cnt us len) lu) (erased (Repeat Cnt len (MkCopy (U62) (MkU62 (Zero) u62-modulus-pos)) ws) rp) -> (erased (Tally ws j p (CEmpty)) r))
  (let-match erased tb (TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 _)
    ((TaL _ _ _ _ _ x _ _) (TaL ws p (Zero) u62-modulus-pos (CEmpty) (repeat-nth _ len p _ ws rp (nth-lt-length _ us p len _ x lu)) (RootE) (HE (Zero)))))
  (let ((erased e)) (CEmpty))
  (TaN ws j1 p q e e e e tq (tally-zeros us ws j1 q len t1 b1 lu rp) (tally-zeros us ws j1 (Succ q) len t2 b2 lu rp)
    (tally-zeros us ws j1 (Succ (Succ q)) len t3 b3 lu rp) (CnE)))

; What srestrict needs of its arrays, as sinit makes them from ctu.
(def-adts $ (SInit : ((Nat) h) ((Ctree) ctu) ((List Cnt) us) ((List Cnt) ws) ((Nat) L) -> Type)
  enum
  (many MkSInit : (erased (Nat) h) (erased (Ctree) ctu) (erased (List Cnt) us ws) (erased (Nat) len L) (erased (Lt len u62-modulus) lb)
      (erased (Tally us (Succ h) (Zero) ctu) tb) (erased (Length Cnt us len) lu) (erased (NzCnt us L) z) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz)
      (erased (Length Cnt ws len) lw) -> (SInit h ctu us ws L)))

(def-fns _ $ (many sinit : (many (Nat) h) (many (Ctree) ctu) (erased (CtH (Succ h) ctu) hc) ->
    (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g) (many (Nat) L) (many (Try (SInit h ctu us ws L)) r))
  (let ((erased us) (unique a) (many r)) (ctree-tally (Succ h) ctu hc))
  (let ((many len) (erased lu) (unique a1)) (array-length _ us a))
  (let ((erased ws) (unique g) (erased rp)) (array-make (U62) len (MkU62 (Zero) u62-modulus-pos)))
  (let ((many L) (erased z) (unique a2)) (live-loop us a1 (Zero) us (SfZ us) len lu))
  (let-match many r (TryOk _ pk) ((TryNo _) (values us ws a2 g L (TryNo _))))
  (let-match erased pk (MkPacked _ _ _ tb f))
  (let-match erased f (MkFit _ len2 l2 lb))
  (let-match erased (length-fn _ us len len2 lu l2) (Refl _ _))
  (values us ws a2 g L (TryOk _ (MkSInit h ctu us ws len L lb tb lu z (tally-zeros us ws (Succ h) (Zero) len ctu tb lu rp) (repeat-length _ len _ ws rp)))))
