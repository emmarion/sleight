; mini/base.sl -- decided equality on Nat and Bool, and list indexing with evidence, for the
; relations of mini/. Plain SL over the prelude; nothing here is settled design.

(def-adts
  ((Neq : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NeqLt : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Neq a b))
    (many NeqGt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (Neq a b)))
  ((NatDec : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NDSame : (erased (Nat) a) -> (NatDec a a))
    (many NDDiff : (erased (Nat) a) (erased (Nat) b) (erased (Neq a b) p) -> (NatDec a b))))

(def-fns _ $ (many nat-dec : (many (Nat) a) (many (Nat) b) -> (many (NatDec a b) r))
  (match many (nat-cmp a b) _
    ((CLt t r x y p) (NDDiff _ _ $ NeqLt _ _ p))
    ((CEq t r x) (NDSame _))
    ((CGt t r x y q) (NDDiff _ _ $ NeqGt _ _ q))))

(def-fns _ $ (erased neq-irrefl : (erased (Nat) x) (erased (Neq x x) n) -> (erased (False) f))
  (match erased n _
    ((NeqLt a b p) (lt-asym x x p (lt-succ x)))
    ((NeqGt a b q) (lt-asym x x q (lt-succ x)))))

(def-fns _ $ (erased neq-sym : (erased (Nat) x) (erased (Nat) y) (erased (Neq x y) n) -> (erased (Neq y x) m))
  (match erased n _
    ((NeqLt a b p) (NeqGt y x p))
    ((NeqGt a b q) (NeqLt y x q))))

(def-fns _ $ (erased lt-neq : (erased (Nat) x) (erased (Nat) y) (erased (Lt x y) p) -> (erased (Neq x y) n))
  (NeqLt x y p))

; a <= b is written (Lt a (Succ b)), as the prelude does.
(def-fns _ $ (erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r))
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ (erased lt-le : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a b) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a c) r))
  (lt-le-trans a b c p q))

(def-adts
  ((BoolNeq : ((Bool) a) ((Bool) b) -> Type)
    enum
    (many BNeqTF : -> (BoolNeq (BTrue) (BFalse)))
    (many BNeqFT : -> (BoolNeq (BFalse) (BTrue))))
  ((BoolDec : ((Bool) a) ((Bool) b) -> Type)
    enum
    (many BDSame : (erased (Bool) a) -> (BoolDec a a))
    (many BDDiff : (erased (Bool) a) (erased (Bool) b) (erased (BoolNeq a b) p) -> (BoolDec a b))))

(def-fns _ $ (many bool-dec : (many (Bool) a) (many (Bool) b) -> (many (BoolDec a b) r))
  (match many a _
    ((BTrue) (match many b _ ((BTrue) (BDSame _)) ((BFalse) (BDDiff _ _ (BNeqTF)))))
    ((BFalse) (match many b _ ((BTrue) (BDDiff _ _ (BNeqFT))) ((BFalse) (BDSame _))))))

; The length of a list, and the layout of a substitution or abstraction list: [r] leading [None]s, then
; [Some]s only, [n] items in all. Addition, for the depth a telescope ends at.
; Two lists of one length.
(def-adts
  ((LenEq : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type)
    enum
    (many LENil : (erased Type A) (erased Type B) -> (LenEq A B (Nil A) (Nil B)))
    (many LECons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (LenEq A B xs ys) p) -> (LenEq A B (Cons A x xs) (Cons B y ys)))))

(def-adts
  ((Length : (Type A) ((List A) xs) ((Nat) n) -> Type)
    enum
    (many LenNil : (erased Type A) -> (Length A (Nil A) (Zero)))
    (many LenCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) n) (erased (Length A xs n) p) -> (Length A (Cons A x xs) (Succ n))))
  ((Layout : (Type A) ((List (Maybe A)) xs) ((Nat) r) ((Nat) n) -> Type)
    enum
    (many LayNil : (erased Type A) -> (Layout A (Nil (Maybe A)) (Zero) (Zero)))
    (many LaySome : (erased Type A) (erased A x) (erased (List (Maybe A)) rest) (erased (Nat) n) (erased (Layout A rest (Zero) n) p)
       -> (Layout A (Cons (Maybe A) (Some A x) rest) (Zero) (Succ n)))
    (many LayNone : (erased Type A) (erased (List (Maybe A)) rest) (erased (Nat) r) (erased (Nat) n) (erased (Layout A rest r n) p)
       -> (Layout A (Cons (Maybe A) (None A) rest) (Succ r) (Succ n))))
  ((Plus : ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
    enum
    (many PlusZ : (erased (Nat) b) -> (Plus (Zero) b b))
    (many PlusS : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Plus a b c) p) -> (Plus (Succ a) b (Succ c)))))

(def-fns _ $ (many list-len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) p))
  (match many xs _
    ((Nil a) (values (Zero) (LenNil _)))
    ((Cons a x rest) (let ((many n) (erased p)) (notail $ list-len _ rest)) (values (Succ n) (LenCons _ x rest n p)))))
(def-fns _ $ (erased layout-length : (erased Type A) (erased (List (Maybe A)) xs) (erased (Nat) r) (erased (Nat) n) (subterm erased (Layout A xs r n) p) -> (erased (Length (Maybe A) xs n) q))
  (match erased p _
    ((LayNil a) (LenNil _))
    ((LaySome a x rest m q) (LenCons _ (Some _ x) rest m (layout-length _ rest (Zero) m q)))
    ((LayNone a rest r2 m q) (LenCons _ (None _) rest m (layout-length _ rest r2 m q)))))
(def-fns _ $ (erased layout-le : (erased Type A) (erased (List (Maybe A)) xs) (erased (Nat) r) (erased (Nat) n) (subterm erased (Layout A xs r n) p) -> (erased (Lt r (Succ n)) q))
  (match erased p _
    ((LayNil a) (LtZ (Zero)))
    ((LaySome a x rest m q) (LtZ (Succ m)))
    ((LayNone a rest r2 m q) (LtS r2 (Succ m) (layout-le _ rest r2 m q)))))
(def-fns _ $ (erased plus-zero : (subterm erased (Nat) a) -> (erased (Plus a (Zero) a) p))
  (match erased a _
    ((Zero) (PlusZ (Zero)))
    ((Succ b) (PlusS b (Zero) b (plus-zero b)))))
(def-fns _ $ (erased plus-shift : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Plus (Succ a) b c) p) -> (erased (Plus a (Succ b) c) q))
  (match erased p _
    ((PlusS a2 b2 c2 p2)
      (match erased p2 _
        ((PlusZ d) (PlusZ (Succ b)))
        ((PlusS a3 b3 c3 p3) (PlusS a3 (Succ b) (Succ c3) (plus-shift a3 b (Succ c3) p2)))))))

; The i-th element of a list, or evidence that there is none.
(def-adts
  ((Nth : (Type A) ((List A) xs) ((Nat) i) (A x) -> Type)
    enum
    (many NthHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Nth A (Cons A x rest) (Zero) x))
    (many NthThere : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased A x) (erased (Nth A rest i x) p)
       -> (Nth A (Cons A y rest) (Succ i) x)))
  ((NoNth : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many NoNthNil : (erased Type A) (erased (Nat) i) -> (NoNth A (Nil A) i))
    (many NoNthCons : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased (NoNth A rest i) p) -> (NoNth A (Cons A y rest) (Succ i))))
  ((NthDec : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many NthHit : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthDec A xs i))
    (many NthMiss : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (NoNth A xs i) p) -> (NthDec A xs i))))

(def-fns _ $ (many nth-dec : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthDec A xs i) r))
  (match many xs _
    ((Nil a) (NthMiss _ _ _ $ NoNthNil _ i))
    ((Cons a y rest)
      (match many i _
        ((Zero) (NthHit _ _ _ y $ NthHere _ y rest))
        ((Succ j)
          (match many (notail $ nth-dec _ rest j) _
            ((NthHit b l k x p) (NthHit _ _ _ x $ NthThere _ y rest j x p))
            ((NthMiss b l k p) (NthMiss _ _ _ $ NoNthCons _ y rest j p))))))))

(def-fns _ $ (erased no-nth-lt : (erased Type A) (erased (List A) xs) (erased (Nat) n) (erased (Nat) k) (erased (Length A xs n) ln) (erased (Lt k n) lt) (subterm erased (NoNth A xs k) p) -> (erased (False) f))
  (match erased p _
    ((NoNthNil a i) (match erased ln _ ((LenNil b) (match erased lt _))))
    ((NoNthCons a y rest i q) (match erased ln _ ((LenCons b x xs2 m l2) (match erased lt _ ((LtS c d lt2) (no-nth-lt _ rest m i l2 lt2 q))))))))
(def-fns _ $ (erased nth-none-lt : (erased Type A) (erased (List (Maybe A)) xs) (erased (Nat) r) (erased (Nat) n) (erased (Nat) k) (erased (Layout A xs r n) ly) (subterm erased (Nth (Maybe A) xs k (None A)) p) ->
    (erased (Lt k r) q))
  (match erased p _
    ((NthHere a x rest) (match erased ly _ ((LayNone b rest2 r2 m q) (LtZ r2))))
    ((NthThere a y rest i x q)
      (match erased ly _
        ((LaySome b x2 rest2 m q2) (match erased (nth-none-lt _ rest2 (Zero) m i q2 q) _))
        ((LayNone b rest2 r2 m q2) (LtS i r2 (nth-none-lt _ rest2 r2 m i q2 q)))))))
(def-fns _ $ (erased index-lt : (erased Type A) (erased (List A) xs) (erased (Nat) n) (erased (Nat) k) (erased A x) (erased (Length A xs n) ln) (subterm erased (Nth A xs k x) p) -> (erased (Lt k n) q))
  (match erased p _
    ((NthHere a y rest) (match erased ln _ ((LenCons b z xs2 m l2) (LtZ m))))
    ((NthThere a y rest i z q) (match erased ln _ ((LenCons b w xs2 m l2) (LtS i m (index-lt _ rest m i x l2 q)))))))

(MkUnit)
