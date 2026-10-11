import MSort

def gen : Nat → Nat → List UInt64 → List UInt64
  | 0, _, acc => acc
  | k+1, seed, acc =>
    let x := (seed * 1103515245 + 12345) % 1073741824
    gen k x (x.toUInt64 :: acc)

def checksum : List UInt64 → Nat → Nat → Nat
  | [], _, acc => acc
  | x :: xs, i, acc => checksum xs (i + 1) (acc + i * x.toNat)

@[noinline] def sortWith (which : String) (xs : List UInt64) : IO (List UInt64) :=
  if which == "core" then return xs.mergeSort else if which == "none" then return xs else return MSort.msort xs

def main (args : List String) : IO Unit := do
  let which := args.headD "ours"
  let size := ((args.drop 1).head?.bind String.toNat?).getD 1000000
  let xs := gen size 42 []
  let t0 ← IO.monoNanosNow
  let r ← sortWith which xs
  let t1 ← IO.monoNanosNow
  IO.println s!"checksum {checksum r 0 0}\nsort-ns {t1 - t0}"
