module Main

import Arr
import HeapSort
import Data.Bits
import Data.IOArray.Prims
import Data.List
import System
import System.Clock

sortArr : ArrayData Int -> Nat -> IO (ArrayData Int)
sortArr a n = primIO $ withArr a n $ \h => case heapSort n h of MkEx _ _ h => done h

fromList : List Int -> IO (ArrayData Int)
fromList xs = do
  a <- primIO (prim__newArray (cast (length xs)) 0)
  for_ (zip [0 .. cast (length xs) - 1] xs) $ \(i, x) => primIO (prim__arraySet a i x)
  pure a

toList : ArrayData Int -> Int -> IO (List Int)
toList a n = for [0 .. n - 1] $ \i => primIO (prim__arrayGet a i)

series : (a -> a) -> a -> Nat -> List a
series f s 0 = []
series f s (S k) = let s = f s in s :: series f s k

bench : IO ()
bench = do
  let n = 1048576
  a <- fromList (reverse (series (\s => (s * 1103515245 + 12345) `mod` 1073741824) 42 (cast n)))
  t0 <- clockTime Monotonic
  a <- sortArr a (cast n)
  t1 <- clockTime Monotonic
  let d = timeDifference t1 t0
  ys <- toList a (cast n)
  let s = sum (zipWith (\i, x => cast {to=Integer} i * cast x) [the Int 1 .. cast n] ys)
  putStrLn ("ms " ++ show (cast {to=Double} (seconds d * 1000000000 + nanoseconds d) / 1.0e6) ++ " checksum " ++ show s)

difftest : IO ()
difftest = do
  let cases = [(n, r) | n <- [1 .. 2999], r <- [2, 3, 1000000007]]
  fails <- go cases 1 0
  putStrLn ("difftest: " ++ show (length cases) ++ " cases, " ++ show fails ++ " mismatches")
  when (fails /= 0) (exitWith (ExitFailure 1))
where
  go : List (Int, Bits64) -> Bits64 -> Nat -> IO Nat
  go [] _ f = pure f
  go ((n, r) :: cs) s f = do
    let ss = series (\s => s * 6364136223846793005 + 1442695040888963407) s (cast n)
        xs = map (\s => cast ((s `shiftR` 33) `mod` r)) ss
    ys <- fromList xs >>= \a => sortArr a (cast n) >>= \a => toList a n
    let ok = ys == sort xs
    unless ok (putStrLn ("MISMATCH n=" ++ show n ++ " range=" ++ show r))
    go cs (fromMaybe s (last' ss)) (if ok then f else S f)

main : IO ()
main = getArgs >>= \args => if drop 1 args == ["test"] then difftest else bench
