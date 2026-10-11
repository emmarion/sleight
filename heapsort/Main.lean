import Int63

#print axioms Int63.heapSort_correct

def gen (n : Nat) : Array Int63 := Id.run do
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  let mut a := Array.emptyWithCapacity n
  for _ in [0:n] do
    s := s ^^^ (s <<< 13); s := s ^^^ (s >>> 7); s := s ^^^ (s <<< 17)
    a := a.push (Int63.ofInt (s >>> 1).toNat)
  return a

def main : IO Unit := do
  let n := 2^20
  for _ in [0:5] do
    let a ← IO.lazyPure fun _ => gen n
    let t0 ← IO.monoNanosNow
    let r := Int63.heapSort a
    if r.size != n then throw <| .userError "size"
    let t1 ← IO.monoNanosNow
    IO.println s!"{(t1 - t0).toFloat / 1e6} ms  min {r[0]!} median {r[n/2]!} max {r[n-1]!}"
