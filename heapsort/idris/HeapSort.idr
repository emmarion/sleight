module HeapSort

import Arr
import Control.Relation
import Control.WellFounded
import Data.DPair
import Decidable.Equality

%default total

public export
data Swap : Nat -> Nat -> Vect n a -> Vect n a -> Type where
  MkSwap : Nth i x xs -> Nth j y xs -> Upd i y xs zs -> Upd j x zs ys -> Swap i j xs ys

public export
data Perm : Vect n a -> Vect n a -> Type where
  PNil : Perm xs xs
  PSwap : Perm xs ys -> Swap i j ys zs -> Perm xs zs

public export
data Sorted : Vect n Int -> Type where
  SNil : Sorted []
  SOne : Sorted [x]
  SCons : So (x <= y) -> Sorted (y :: ys) -> Sorted (x :: y :: ys)

public export
data Ex : (Vect n Int -> Type) -> Type where
  MkEx : (0 ys : Vect n Int) -> (0 _ : p ys) -> (1 _ : Arr ys) -> Ex p

data Or : Type -> Type -> Type where
  L : (0 _ : p) -> Or p q
  R : (0 _ : q) -> Or p q

%inline
ifSo : (b : Bool) -> (0 _ : So b -> p) -> (0 _ : So (not b) -> q) -> Or p q
ifSo True f _ = L (f Oh)
ifSo False _ g = R (g Oh)

0 leRefl : (x : Int) -> So (x <= x)
leRefl x = either id leFlip (choose (x <= x))

0 soLt : {i, m : Nat} -> So (i < m) -> LT i m
soLt {i = 0} {m = 0} p = absurd p
soLt {i = 0} {m = S _} _ = LTESucc LTEZero
soLt {i = S _} {m = 0} p = absurd p
soLt {i = S _} {m = S _} p = LTESucc (soLt p)

0 soGe : {i, m : Nat} -> So (not (i < m)) -> LTE m i
soGe {m = 0} _ = LTEZero
soGe {i = 0} {m = S _} p = absurd p
soGe {i = S _} {m = S _} p = LTESucc (soGe p)

%inline
ltNat : (i, m : Nat) -> Or (LT i m) (LTE m i)
ltNat i m = ifSo (i < m) soLt soGe

%inline
leInt : (x, y : Int) -> Or (So (x <= y)) (So (y <= x))
leInt x y = ifSo (x <= y) id leFlip

0 ltIrr : LT i i -> Void
ltIrr = succNotLTEpred

0 ltNe : LT i j -> Not (i = j)
ltNe p Refl = ltIrr p

0 lteNe : LTE k p -> Not (p = k) -> LT k p
lteNe {p = 0} LTEZero ne = absurd (ne Refl)
lteNe {p = S _} LTEZero _ = LTESucc LTEZero
lteNe (LTESucc q) ne = LTESucc (lteNe q (\e => ne (cong S e)))

0 nthFun : Nth i x xs -> Nth i y xs -> x = y
nthFun Here Here = Refl
nthFun (There p) (There q) = nthFun p q

0 nthLt : Nth {n} i x xs -> LT i n
nthLt Here = LTESucc LTEZero
nthLt (There p) = LTESucc (nthLt p)

0 updSame : Upd i y xs ys -> Nth i z ys -> z = y
updSame UHere Here = Refl
updSame (UThere u) (There p) = updSame u p

0 updOther : Not (k = i) -> Upd i y xs ys -> Nth k z ys -> Nth k z xs
updOther ne UHere Here = absurd (ne Refl)
updOther _ UHere (There p) = There p
updOther _ (UThere _) Here = Here
updOther ne (UThere u) (There p) = There (updOther (\e => ne (cong S e)) u p)

data Moved : Nat -> Nat -> Nat -> Nat -> Type where
  MJ : Moved i j j i
  MI : Moved i j i j
  MO : Not (k = i) -> Not (k = j) -> Moved i j k k

0 swapNth : Swap i j xs ys -> Nth k z ys -> (k2 ** (Nth k2 z xs, Moved i j k k2))
swapNth {k} (MkSwap {i, j} px py u1 u2) a = case decEq k j of
  Yes Refl => rewrite updSame u2 a in (i ** (px, MJ))
  No nj => let a = updOther nj u2 a in case decEq k i of
    Yes Refl => rewrite updSame u1 a in (j ** (py, MI))
    No ni => (k ** (updOther ni u1 a, MO ni nj))

data Child : Nat -> Nat -> Type where
  C1 : Child 0 1
  C2 : Child 0 2
  CS : Child p j -> Child (S p) (S (S j))

0 childL : (i : Nat) -> Child i (S (i + i))
childL 0 = C1
childL (S i) = rewrite sym (plusSuccRightSucc i i) in CS (childL i)

0 childR : (i : Nat) -> Child i (S (S (i + i)))
childR 0 = C2
childR (S i) = rewrite sym (plusSuccRightSucc i i) in CS (childR i)

0 childIs : Child i j -> Either (j = S (i + i)) (j = S (S (i + i)))
childIs C1 = Left Refl
childIs C2 = Right Refl
childIs (CS {p} c) = rewrite sym (plusSuccRightSucc p p) in case childIs c of
  Left Refl => Left Refl
  Right Refl => Right Refl

0 childGe : Child i j -> LTE (S (i + i)) j
childGe c = case childIs c of
  Left Refl => reflexive
  Right Refl => lteSuccRight reflexive

0 childGt : Child p j -> LT p j
childGt c = transitive (LTESucc (lteAddRight _)) (childGe c)

0 noChild0 : Child p 0 -> Void
noChild0 C1 impossible
noChild0 C2 impossible
noChild0 (CS _) impossible

0 childUniq : Child p j -> Child q j -> p = q
childUniq C1 C1 = Refl
childUniq C2 C2 = Refl
childUniq C2 (CS d) = absurd (noChild0 d)
childUniq (CS c) C2 = absurd (noChild0 c)
childUniq (CS c) (CS d) = cong S (childUniq c d)

0 parent : (a : Nat) -> (p ** Child p (S a))
parent 0 = (0 ** C1)
parent 1 = (0 ** C2)
parent (S (S a)) = let (p ** c) = parent a in (S p ** CS c)

0 HeapOn : (Nat -> Type) -> Vect n Int -> Nat -> Type
HeapOn ok xs m = {p, j : Nat} -> {x, y : Int} ->
  ok p -> Child p j -> LT j m -> Nth j x xs -> Nth p y xs -> So (x <= y)

0 Heap : Vect n Int -> Nat -> Nat -> Type
Heap xs k = HeapOn (LTE k) xs

0 HeapEx : Vect n Int -> Nat -> Nat -> Nat -> Type
HeapEx xs k i = HeapOn (\p => (LTE k p, Not (p = i))) xs

0 Grand : Vect n Int -> Nat -> Nat -> Nat -> Type
Grand xs k i m = {q, j : Nat} -> {x, y : Int} ->
  LTE k q -> Child q i -> Child i j -> LT j m -> Nth j x xs -> Nth q y xs -> So (x <= y)

0 grandNone : Grand xs k k m
grandNone kq c _ _ _ _ = absurd (ltIrr (transitive (childGt c) kq))

0 CMax : Vect n Int -> Nat -> Nat -> Int -> Type
CMax xs i m w = {j : Nat} -> {x : Int} -> Child i j -> LT j m -> Nth j x xs -> So (x <= w)

0 Suffix : Vect n Int -> Nat -> Type
Suffix xs m = {i, j : Nat} -> {x, y : Int} -> LT i j -> LTE m j -> Nth i x xs -> Nth j y xs -> So (x <= y)

data Stay : Nat -> Nat -> Nat -> Type where
  Above : LTE m k -> Stay m k k
  Below : LT k m -> LT k2 m -> Stay m k k2

0 Stays : Vect n Int -> Vect n Int -> Nat -> Type
Stays xs ys m = {k : Nat} -> {z : Int} -> Nth k z ys -> (k2 ** (Nth k2 z xs, Stay m k k2))

0 stay : (m, k : Nat) -> Stay m k k
stay m k = case isLT k m of
  Yes p => Below p p
  No p => Above (notLTImpliesGTE p)

0 staysId : Stays xs xs m
staysId a = (_ ** (a, stay _ _))

0 stayLt : Stay b k k2 -> LT k j -> LTE b j -> LT k2 j
stayLt (Above _) p _ = p
stayLt (Below _ q) _ r = transitive q r

0 stayAt : Stay b k k2 -> LTE b k -> k2 = k
stayAt (Above _) _ = Refl
stayAt (Below p _) q = absurd (ltIrr (transitive p q))

0 staysTrans : Stays xs ys m -> Stays ys zs m -> Stays xs zs m
staysTrans s t a = let (k1 ** (a1, st1)) = t a; (k2 ** (a2, st2)) = s a1 in (k2 ** (a2, go st1 st2))
  where
    go : Stay m k k1 -> Stay m k1 k2 -> Stay m k k2
    go (Above _) st = st
    go (Below p q) st = Below p (stayLt st q reflexive)

0 swapStays : LT i m -> LT j m -> Swap i j xs ys -> Stays xs ys m
swapStays pi pj sw a = case swapNth sw a of
  (_ ** (a, MJ)) => (_ ** (a, Below pj pi))
  (_ ** (a, MI)) => (_ ** (a, Below pi pj))
  (_ ** (a, MO _ _)) => (_ ** (a, stay _ _))

0 cmax : Nth (S (i + i)) v1 xs -> So (v1 <= w) ->
         Either (LTE m (S (S (i + i)))) (v2 ** (Nth (S (S (i + i))) v2 xs, So (v2 <= w))) -> CMax xs i m w
cmax p1 l1 r c jm a = case childIs c of
  Left e => rewrite nthFun (rewrite sym e in a) p1 in l1
  Right e => case r of
    Left nr => absurd (ltIrr (transitive (rewrite sym e in jm) nr))
    Right (_ ** (p2, l2)) => rewrite nthFun (rewrite sym e in a) p2 in l2

0 noKids : LTE m (S (i + i)) -> CMax xs i m w
noKids nl c jm _ = absurd (ltIrr (transitive jm (transitive nl (childGe c))))

0 closeHeap : HeapEx xs k i m -> CMax xs i m w -> Nth i v xs -> So (w <= v) -> Heap xs k m
closeHeap hh cm pv le {p} kp c jm a b = case decEq p i of
  Yes Refl => rewrite nthFun b pv in leTrans (cm c jm a) le
  No ne => hh (kp, ne) c jm a b

0 siftHeap : LTE k i -> Child i c -> LT c m -> Swap i c xs ys -> Nth i vi xs -> Nth c vc xs ->
             So (vi <= vc) -> HeapEx xs k i m -> Grand xs k i m -> CMax xs i m vc -> HeapEx ys k c m
siftHeap ki ci cm sw pi pc le hh hg cx (kp, nc) cj jm a b = case (swapNth sw b, swapNth sw a) of
  ((_ ** (_, MJ)), _) => absurd (nc Refl)
  ((_ ** (b, MI)), (_ ** (a, MJ))) => rewrite nthFun b pc in rewrite nthFun a pi in le
  ((_ ** (_, MI)), (_ ** (_, MI))) => absurd (ltIrr (childGt cj))
  ((_ ** (b, MI)), (_ ** (a, MO _ _))) => rewrite nthFun b pc in cx cj jm a
  ((_ ** (_, MO ni _)), (_ ** (_, MJ))) => absurd (ni (childUniq cj ci))
  ((_ ** (b, MO _ _)), (_ ** (a, MI))) => hg kp cj ci cm a b
  ((_ ** (b, MO ni _)), (_ ** (a, MO _ _))) => hh (kp, ni) cj jm a b

0 siftGrand : LTE k i -> Child i c -> Swap i c xs ys -> HeapEx xs k i m -> Grand ys k c m
siftGrand ki ci sw hh kq cq cj jm a b = case (swapNth sw b, swapNth sw a) of
  ((_ ** (_, MO ni _)), _) => absurd (ni (childUniq cq ci))
  ((_ ** (_, MJ)), _) => absurd (ltNe (childGt ci) (sym (childUniq cq ci)))
  (_, (_ ** (_, MJ))) => absurd (ltIrr (childGt cj))
  (_, (_ ** (_, MI))) => absurd (ltIrr (transitive (childGt ci) (lteSuccLeft (childGt cj))))
  ((_ ** (b, MI)), (_ ** (a, MO _ _))) =>
    hh (transitive ki (lteSuccLeft (childGt ci)), \e => ltNe (childGt ci) (sym e)) cj jm a b

0 rootMax : Heap xs 0 m -> Nth 0 r xs -> Nth a x xs -> LT a m -> Accessible LT a -> So (x <= r)
rootMax _ pr Here _ _ = rewrite nthFun pr Here in leRefl _
rootMax {xs = v :: vs} hh pr pa@(There _) am (Access rec) =
  let (p ** c) = parent _
      (_ ** py) = nth (transitive (childGt c) (lteSuccLeft (nthLt pa))) (v :: vs)
  in leTrans (hh LTEZero c am pa py) (rootMax hh pr py (transitive (childGt c) (lteSuccLeft am)) (rec _ (childGt c)))

0 Up : Nat -> Nat -> Nat -> Type
Up m c i = (LT i c, LT c m)

0 upAcc : (f : Nat) -> LTE m (f + i) -> Accessible (Up m) i
upAcc f h = Access $ \c, (ic, cm) => case f of
  0 => absurd (ltIrr (transitive ic (transitive (lteSuccLeft cm) h)))
  S f => upAcc f (transitive h (rewrite plusSuccRightSucc f i in plusLteMonotoneLeft f _ _ ic))

%inline
swap : (i, j : Nat) -> (0 _ : LT i n) -> (0 _ : LT j n) -> (x, y : Int) -> (0 _ : Nth i x xs) -> (0 _ : Nth j y xs) ->
       (1 _ : Arr {n} xs) -> (1 _ : (0 ys : Vect n Int) -> (0 _ : Swap i j xs ys) -> (1 _ : Arr ys) -> r) -> r
swap i j pi pj x y px py a k = set i pi y a $ \_, u1, a => set j pj x a $ \ys, u2, a => k ys (MkSwap px py u1 u2) a

%inline
child : (m, i : Nat) -> (0 _ : LTE m n) -> (0 _ : LT (S (i + i)) m) -> (v1 : Int) -> (0 _ : Nth (S (i + i)) v1 xs) ->
        (1 _ : Arr {n} xs) -> (1 _ : (c : Nat) -> (vc : Int) -> (0 _ : Child i c) -> (0 _ : LT c m) ->
        (0 _ : Nth c vc xs) -> (0 _ : CMax xs i m vc) -> (1 _ : Arr xs) -> r) -> r
child m i mn lm v1 p1 a k = case ltNat (S (S (i + i))) m of
  L rm => get (S (S (i + i))) (transitive rm mn) a $ \v2, p2, a => case leInt v1 v2 of
    L le => k _ v2 (childR i) rm p2 (cmax p1 le (Right (v2 ** (p2, leRefl v2)))) a
    R ge => k _ v1 (childL i) lm p1 (cmax p1 (leRefl v1) (Right (v2 ** (p2, ge)))) a
  R nr => k _ v1 (childL i) lm p1 (cmax p1 (leRefl v1) (Left nr)) a

sift : (m, i : Nat) -> (0 _ : Accessible (Up m) i) -> (0 _ : LTE k i) -> (0 _ : LT i m) -> (0 _ : LTE m n) ->
       (0 _ : HeapEx xs k i m) -> (0 _ : Grand xs k i m) -> (0 _ : Stays xs0 xs m) -> (0 _ : Perm xp xs) ->
       (1 _ : Arr {n} xs) -> Ex (\ys => (Heap ys k m, Stays xs0 ys m, Perm xp ys))
sift m i (Access acc) ki im mn hh hg hs hp a =
  let 0 pi = transitive im mn in
  case ltNat (S (i + i)) m of
    R nl => let 0 v = nth pi xs in MkEx _ (closeHeap hh (noKids nl) (snd v) (leRefl (fst v)), hs, hp) a
    L lm => get (S (i + i)) (transitive lm mn) a $ \v1, a1, a => child m i mn lm v1 a1 a $ \c, vc, ci, cm, ac, cx, a =>
      get i pi a $ \vi, ai, a => case leInt vc vi of
        L le => MkEx _ (closeHeap hh cx ai le, hs, hp) a
        R ge => swap i c pi (transitive cm mn) vi vc ai ac a $ \_, sw, a =>
          sift m c (acc c (childGt ci, cm)) (transitive ki (lteSuccLeft (childGt ci))) cm mn
            (siftHeap ki ci cm sw ai ac ge hh hg cx) (siftGrand ki ci sw hh)
            (staysTrans hs (swapStays im cm sw)) (PSwap hp sw) a

heapify : (n, k : Nat) -> {0 xs, xp : Vect n Int} -> (0 _ : LTE k n) -> (0 _ : Heap xs k n) -> (0 _ : Perm xp xs) ->
          (1 _ : Arr {n} xs) -> Ex (\ys => (Heap ys 0 n, Perm xp ys))
heapify n 0 _ hh hp a = MkEx _ (hh, hp) a
heapify n (S k) kn hh hp a =
  case sift n k (upAcc n (lteAddRight n)) reflexive kn reflexive
         (\(kp, ne) => hh (lteNe kp ne)) grandNone staysId hp a of
    MkEx _ q a => heapify n k (lteSuccLeft kn) (fst q) (snd (snd q)) a

0 downHeap : Swap 0 (S m) xs ys -> Heap xs 0 (S (S m)) -> HeapEx ys 0 0 (S m)
downHeap sw hh (_, p0) cj jm a b = case (swapNth sw a, swapNth sw b) of
  ((_ ** (_, MJ)), _) => absurd (ltIrr jm)
  ((_ ** (_, MI)), _) => absurd (noChild0 cj)
  (_, (_ ** (_, MJ))) => absurd (ltIrr (transitive (childGt cj) (lteSuccLeft jm)))
  (_, (_ ** (_, MI))) => absurd (p0 Refl)
  ((_ ** (a, MO _ _)), (_ ** (b, MO _ _))) => hh LTEZero cj (lteSuccRight jm) a b

0 downSuffix : Heap xs 0 (S (S m)) -> Nth 0 r xs -> Suffix xs (S (S m)) -> Swap 0 (S m) xs ys ->
               Stays ys zs (S m) -> Suffix zs (S m)
downSuffix {m} hh pr hs sw st {j} ij mj a b =
  let (_ ** (a, sa)) = st a
      (j2 ** (b, sb)) = st b
      (_ ** (a, sa2)) = swapStays (LTESucc LTEZero) reflexive sw a
  in case stayAt sb mj of
    Refl => case decEq j (S m) of
      Yes Refl => case swapNth sw b of
        (_ ** (b, MJ)) => rewrite nthFun b pr in
          rootMax hh pr a (stayLt sa2 (lteSuccRight (stayLt sa ij reflexive)) reflexive) (wellFounded _)
        (_ ** (_, MO _ nj)) => absurd (nj Refl)
      No nj => let mj = lteNe mj nj in case swapStays (LTESucc LTEZero) reflexive sw b of
        (_ ** (b, sb2)) => case stayAt sb2 mj of
          Refl => hs (stayLt sa2 (stayLt sa ij (lteSuccLeft mj)) mj) mj a b

sortdown : (m : Nat) -> (0 _ : LTE m n) -> (0 _ : Heap xs 0 m) -> (0 _ : Suffix xs m) -> (0 _ : Perm xp xs) ->
           (1 _ : Arr {n} xs) -> Ex (\ys => (Suffix ys 1, Perm xp ys))
sortdown 0 _ _ hs hp a = MkEx _ (\ij, _ => hs ij LTEZero, hp) a
sortdown 1 _ _ hs hp a = MkEx _ (hs, hp) a
sortdown (S (S m)) mn hh hs hp a =
  let 0 p0 = transitive (LTESucc LTEZero) mn
      0 pm = transitive reflexive mn in
  get 0 p0 a $ \r, pr, a => get (S m) pm a $ \t, pt, a => swap 0 (S m) p0 pm r t pr pt a $ \_, sw, a =>
    case sift (S m) 0 (upAcc (S m) (rewrite plusZeroRightNeutral m in reflexive)) LTEZero (LTESucc LTEZero)
           (lteSuccLeft mn) (downHeap sw hh) grandNone staysId
           (PSwap hp sw) a of
      MkEx _ q a => sortdown (S m) (lteSuccLeft mn) (fst q) (downSuffix hh pr hs sw (fst (snd q))) (snd (snd q)) a

0 sorted : {xs : Vect n Int} -> Suffix xs 1 -> Sorted xs
sorted {xs = []} _ = SNil
sorted {xs = [_]} _ = SOne
sorted {xs = _ :: _ :: _} s = SCons (s reflexive reflexive Here (There Here))
  (sorted (\ij, _, a, b => s (LTESucc ij) (LTESucc LTEZero) (There a) (There b)))

half : (n : Nat) -> Subset Nat (\k => (LTE k n, LTE n (S (k + k))))
half n = let k = integerToNat (natToInteger n `div` 2) in case (ltNat k (S n), ltNat n (S (S (k + k)))) of
  (L p, L q) => Element k (fromLteSucc p, fromLteSucc q)
  _ => Element n (reflexive, lteSuccRight (lteAddRight n))

export
heapSort : (n : Nat) -> {0 xs : Vect n Int} -> (1 _ : Arr xs) -> Ex (\ys => (Perm xs ys, Sorted ys))
heapSort n a =
  let Element k q = half n in
  case heapify n k (fst q) (\kp, c, jm, _, _ => absurd (ltIrr (transitive jm (transitive (snd q)
         (transitive (LTESucc (plusLteMonotone kp kp)) (childGe c)))))) PNil a of
    MkEx _ q a => case sortdown n reflexive (fst q) (\_, nj, _, b => absurd (ltIrr (transitive (nthLt b) nj))) (snd q) a of
      MkEx _ q a => MkEx _ (snd q, sorted (fst q)) a
