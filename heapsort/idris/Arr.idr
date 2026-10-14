module Arr

import public Data.So
import public Data.Vect
import public Data.Nat
import Data.IOArray.Prims

%default total

public export
data Nth : Nat -> a -> Vect n a -> Type where
  Here : Nth 0 x (x :: xs)
  There : Nth i x xs -> Nth (S i) x (y :: xs)

public export
data Upd : Nat -> a -> Vect n a -> Vect n a -> Type where
  UHere : Upd 0 y (x :: xs) (y :: xs)
  UThere : Upd i y xs ys -> Upd (S i) y (x :: xs) (x :: ys)

export
0 leTrans : {x, y, z : Int} -> So (x <= y) -> So (y <= z) -> So (x <= z)
leTrans _ _ = believe_me Oh

export
0 leFlip : {x, y : Int} -> So (not (x <= y)) -> So (y <= x)
leFlip _ = believe_me Oh

0 upd : Nth {n} i x xs -> (y : a) -> (ys : Vect n a ** Upd i y xs ys)
upd Here y = (_ ** UHere)
upd (There p) y = let (_ ** u) = upd p y in (_ ** UThere u)

export
0 nth : LT i n -> (xs : Vect n a) -> (x ** Nth i x xs)
nth {i = 0} _ (x :: _) = (x ** Here)
nth {i = S _} (LTESucc p) (_ :: xs) = let (x ** q) = nth p xs in (x ** There q)

export
data Arr : Vect n Int -> Type where
  MkArr : ArrayData Int -> Arr xs

export
data Done : Type where
  MkDone : ArrayData Int -> Done

%foreign "scheme:(lambda (a i) (vector-ref a i))"
prim__get : ArrayData Int -> Nat -> PrimIO Int

%foreign "scheme:(lambda (a i x) (vector-set! a i x))"
prim__set : ArrayData Int -> Nat -> Int -> PrimIO ()

export %inline
get : (i : Nat) -> (0 _ : LT i n) -> (1 _ : Arr {n} xs) ->
      (1 _ : (x : Int) -> (0 _ : Nth i x xs) -> (1 _ : Arr xs) -> r) -> r
get i _ (MkArr a) k = case prim__get a i %MkWorld of MkIORes x _ => k x (believe_me ()) (MkArr a)

export %inline
set : (i : Nat) -> (0 _ : LT i n) -> (y : Int) -> (1 _ : Arr {n} xs) ->
      (1 _ : (0 ys : Vect n Int) -> (0 _ : Upd i y xs ys) -> (1 _ : Arr ys) -> r) -> r
set i p y (MkArr a) k = case prim__set a i y %MkWorld of
  MkIORes () _ => k (fst (upd (snd (nth p xs)) y)) (snd (upd (snd (nth p xs)) y)) (MkArr a)

export
done : (1 _ : Arr xs) -> Done
done (MkArr a) = MkDone a

export
withArr : ArrayData Int -> (n : Nat) -> (1 _ : {0 xs : Vect n Int} -> (1 _ : Arr xs) -> Done) -> PrimIO (ArrayData Int)
withArr a n k w = case k {xs = replicate n 0} (MkArr a) of MkDone a => MkIORes a w
