; mini/base.sl -- booleans, decided equality on Nat and Bool, list indexing, lengths and appending with
; evidence, for the relations of mini/. Plain SL over the prelude; nothing here is settled design.

(def-adts $ Bool : -> Type
  enum
  (many BTrue : -> (Bool))
  (many BFalse : -> (Bool)))

(def-adts
  (Neq : ((Nat) a) ((Nat) b) -> Type
    enum
    (many NeqLt : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Neq a b))
    (many NeqGt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (Neq a b)))
  (NatDec : ((Nat) a) ((Nat) b) -> Type
    enum
    (many NDSame : (erased (Nat) a) -> (NatDec a a))
    (many NDDiff : (erased (Nat) a) (erased (Nat) b) (erased (Neq a b) p) -> (NatDec a b))))

(def-fns _ $ many nat-dec : (many (Nat) a) (many (Nat) b) -> (many (NatDec a b) r)
  (match many (nat-cmp a b) _
    ((CLt t r x y p) (NDDiff _ _ $ NeqLt _ _ p))
    ((CEq t r x) (NDSame _))
    ((CGt t r x y q) (NDDiff _ _ $ NeqGt _ _ q))))

(def-fns _ $ erased neq-irrefl : (erased (Nat) x) (erased (Neq x x) n) -> (erased (False) f)
  (match erased n _
    ((NeqLt a b p) (lt-asym x x p (lt-succ x)))
    ((NeqGt a b q) (lt-asym x x q (lt-succ x)))))

(def-adts
  (BoolNeq : ((Bool) a) ((Bool) b) -> Type
    enum
    (many BNeqTF : -> (BoolNeq (BTrue) (BFalse)))
    (many BNeqFT : -> (BoolNeq (BFalse) (BTrue))))
  (BoolDec : ((Bool) a) ((Bool) b) -> Type
    enum
    (many BDSame : (erased (Bool) a) -> (BoolDec a a))
    (many BDDiff : (erased (Bool) a) (erased (Bool) b) (erased (BoolNeq a b) p) -> (BoolDec a b))))

(def-fns _ $ many bool-dec : (many (Bool) a) (many (Bool) b) -> (many (BoolDec a b) r)
  (match many a _
    ((BTrue) (match many b _ ((BTrue) (BDSame _)) ((BFalse) (BDDiff _ _ (BNeqTF)))))
    ((BFalse) (match many b _ ((BTrue) (BDDiff _ _ (BNeqFT))) ((BFalse) (BDSame _))))))

; The i-th element of a list, or evidence that there is none.
(def-adts
  (Nth : (Type A) ((List A) xs) ((Nat) i) (A x) -> Type
    enum
    (many NthHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Nth A (Cons A x rest) (Zero) x))
    (many NthThere : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased A x) (erased (Nth A rest i x) p) ->
       (Nth A (Cons A y rest) (Succ i) x)))
  (NoNth : (Type A) ((List A) xs) ((Nat) i) -> Type
    enum
    (many NoNthNil : (erased Type A) (erased (Nat) i) -> (NoNth A (Nil A) i))
    (many NoNthCons : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased (NoNth A rest i) p) -> (NoNth A (Cons A y rest) (Succ i))))
  (NthDec : (Type A) ((List A) xs) ((Nat) i) -> Type
    enum
    (many NthHit : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthDec A xs i))
    (many NthMiss : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (NoNth A xs i) p) -> (NthDec A xs i))))

(def-fns _ $ many nth-dec : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthDec A xs i) r)
  (match many xs _
    ((Nil a) (NthMiss _ _ _ $ NoNthNil _ i))
    ((Cons a y rest)
      (match many i _
        ((Zero) (NthHit _ _ _ y $ NthHere _ y rest))
        ((Succ j)
          (match many (nth-dec _ rest j) _
            ((NthHit b l k x p) (NthHit _ _ _ x $ NthThere _ y rest j x p))
            ((NthMiss b l k p) (NthMiss _ _ _ $ NoNthCons _ y rest j p))))))))

; Appending one element, a list's length, and two lists of one length or evidence that they differ.
(def-adts
  (Snoc : (Type A) ((List A) xs) (A x) ((List A) out) -> Type
    enum
    (many SnocNil : (erased Type A) (erased A x) -> (Snoc A (Nil A) x (Cons A x (Nil A))))
    (many SnocCons : (erased Type A) (erased A y) (erased (List A) ys) (erased A x) (erased (List A) out) (erased (Snoc A ys x out) p) -> (Snoc A (Cons A y ys) x (Cons A y out))))
  (Length : (Type A) ((List A) xs) ((Nat) n) -> Type
    enum
    (many LenNil : (erased Type A) -> (Length A (Nil A) (Zero)))
    (many LenCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (Nat) n) (erased (Length A xs n) p) -> (Length A (Cons A x xs) (Succ n))))
  (LenMismatch : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LMNilCons : (erased Type A) (erased Type B) (erased B y) (erased (List B) ys) -> (LenMismatch A B (Nil A) (Cons B y ys)))
    (many LMConsNil : (erased Type A) (erased Type B) (erased A x) (erased (List A) xs) -> (LenMismatch A B (Cons A x xs) (Nil B)))
    (many LMCons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (LenMismatch A B xs ys) p) ->
       (LenMismatch A B (Cons A x xs) (Cons B y ys))))
  (LenDec : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LenSame : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) -> (LenDec A B xs ys))
    (many LenDiff : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (LenMismatch A B xs ys) p) -> (LenDec A B xs ys))))

(def-fns _ $ many snoc : (erased Type A) (subterm many (List A) xs) (many A x) -> (many (List A) out) (erased (Snoc A xs x out) p)
  (match many xs _
    ((Nil a) (values (Cons _ x (Nil _)) (SnocNil _ x)))
    ((Cons a y ys) (let (many out) (erased p) (snoc _ ys x)) (values (Cons _ y out) (SnocCons _ y ys x out p)))))

(def-fns _ $ many list-len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LenNil _)))
    ((Cons a x rest) (let (many n) (erased p) (list-len _ rest)) (values (Succ n) (LenCons _ x rest n p)))))

(def-fns _ $ many len-dec : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) -> (many (LenDec A B xs ys) r)
  (match many xs _
    ((Nil a) (match many ys _ ((Nil b) (LenSame _ _ _ _)) ((Cons b y ys2) (LenDiff _ _ _ _ (LMNilCons _ _ y ys2)))))
    ((Cons a x xs2)
      (match many ys _
        ((Nil b) (LenDiff _ _ _ _ (LMConsNil _ _ x xs2)))
        ((Cons b y ys2)
          (match many (len-dec _ _ xs2 ys2) _
            ((LenSame c d e f) (LenSame _ _ _ _))
            ((LenDiff c d e f p) (LenDiff _ _ _ _ (LMCons _ _ x y xs2 ys2 p)))))))))

(MkUnit)
