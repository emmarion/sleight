module Main

import Data.IOArray.Prims
import System.Clock

Arr : Type
Arr = ArrayData Int

get : Arr -> Int -> IO Int
get a i = primIO (prim__arrayGet a i)

set : Arr -> Int -> Int -> IO ()
set a i x = primIO (prim__arraySet a i x)

sift : Arr -> Int -> Int -> IO ()
sift a m i = do
  let l = 2 * i + 1
  if l < m
    then do
      c <- if l + 1 < m
             then do x <- get a l; y <- get a (l + 1); pure (if x <= y then l + 1 else l)
             else pure l
      vc <- get a c
      vi <- get a i
      if vc > vi then do set a i vc; set a c vi; sift a m c else pure ()
    else pure ()

build : Arr -> Int -> Int -> IO ()
build a n k = if k < 0 then pure () else do sift a n k; build a n (k - 1)

extract : Arr -> Int -> IO ()
extract a m = if m < 2 then pure () else do
  t <- get a 0
  u <- get a (m - 1)
  set a 0 u
  set a (m - 1) t
  sift a (m - 1) 0
  extract a (m - 1)

fill : Arr -> Int -> Int -> Int -> IO ()
fill a n j s = if j >= n then pure () else do
  let s' = (s * 1103515245 + 12345) `mod` 1073741824
  set a (n - 1 - j) s'
  fill a n (j + 1) s'

checksum : Arr -> Int -> Int -> Integer -> IO Integer
checksum a n i acc = if i >= n then pure acc else do
  x <- get a i
  checksum a n (i + 1) (acc + cast (i + 1) * cast x)

main : IO ()
main = do
  let n = 1048576
  a <- primIO (prim__newArray n 0)
  fill a n 0 42
  t0 <- clockTime Monotonic
  build a n (n `div` 2 - 1)
  extract a n
  t1 <- clockTime Monotonic
  let d = timeDifference t1 t0
  s <- checksum a n 0 0
  putStrLn ("ms " ++ show (cast {to=Double} (seconds d * 1000000000 + nanoseconds d) / 1.0e6) ++ " checksum " ++ show s)
