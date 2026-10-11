import HeapSort

structure Int63 where
  enc : Nat
  lt : enc < 2^63

namespace Int63

def toInt (x : Int63) : Int := x.enc - 2^62

def ofInt (i : Int) : Int63 := ⟨((i + 2^62) % 2^63).toNat, by omega⟩

instance : LE Int63 := ⟨fun x y => x.toInt ≤ y.toInt⟩

theorem le_iff_enc_le {x y : Int63} : x ≤ y ↔ x.enc ≤ y.enc :=
  show x.toInt ≤ y.toInt ↔ _ by simp only [toInt]; omega

instance : DecidableLE Int63 := fun _ _ => decidable_of_iff _ le_iff_enc_le.symm

instance : Inhabited Int63 := ⟨ofInt 0⟩

instance : ToString Int63 := ⟨fun x => toString x.toInt⟩

def heapSort (a : Array Int63) : Array Int63 := HeapSort.heapSort (fun x y => decide (x ≤ y)) a

theorem heapSort_correct (a : Array Int63) :
    (heapSort a).Perm a ∧ (heapSort a).toList.Pairwise (· ≤ ·) := by
  have h := HeapSort.heapSort_correct (fun x y : Int63 => decide (x ≤ y))
    (fun x y => by simp only [decide_eq_true_eq, le_iff_enc_le]; omega)
    (fun x y z => by simp only [decide_eq_true_eq, le_iff_enc_le]; omega) a
  simpa [heapSort] using h

end Int63
