import Int63

def gen (n : Nat) : Array Int63 := Id.run do
  let mut s : Nat := 42
  let mut a := Array.replicate n (Int63.ofInt 0)
  for j in [0:n] do
    s := (s * 1103515245 + 12345) % 2^30
    a := a.set! (n - 1 - j) (Int63.ofInt s)
  return a

def main : IO Unit := do
  let n := 2^20
  let a ← IO.lazyPure fun _ => gen n
  let t0 ← IO.monoNanosNow
  let r := Int63.heapSort a
  if r.size != n then throw <| .userError "size"
  let t1 ← IO.monoNanosNow
  let mut sum : Nat := 0
  for i in [0:n] do
    sum := sum + (i + 1) * (r[i]!).toInt.toNat
  IO.println s!"ms {(t1 - t0).toFloat / 1e6} checksum {sum}"
