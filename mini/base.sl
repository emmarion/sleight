; mini/base.sl -- booleans, decided equality on Nat and Bool, and list indexing with evidence, for the
; relations of mini/. Plain SL over the prelude; nothing here is settled design.

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

(MkUnit)
