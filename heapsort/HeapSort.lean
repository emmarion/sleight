namespace HeapSort

variable {α : Type} (le : α → α → Bool)

@[inline] def child (a : Array α) (m i : Nat) (hm : m ≤ a.size) : Nat :=
  if h : 2*i+2 < m then
    if le (a[2*i+1]'(by omega)) (a[2*i+2]'(by omega)) then 2*i+2 else 2*i+1
  else 2*i+1

theorem child_bounds (a : Array α) (m i hm) (hl : 2*i+1 < m) :
    (child le a m i hm = 2*i+1 ∨ child le a m i hm = 2*i+2) ∧ child le a m i hm < m := by
  unfold child; split <;> (try split) <;> omega

@[specialize] def siftDown (a : Array α) (m : Nat) (hm : m ≤ a.size) (i : Nat) : Array α :=
  if hl : 2*i+1 < m then
    let c := child le a m i hm
    have hc := child_bounds le a m i hm hl
    if le (a[c]'(by omega)) (a[i]'(by omega)) then a
    else siftDown (a.swap i c (by omega) (by omega)) m (by simp; omega) c
  else a
termination_by m - i
decreasing_by omega

inductive SwapsBelow (m : Nat) : Array α → Array α → Prop
  | refl a : SwapsBelow m a a
  | step a b i j (hi : i < m) (hj : j < m) (hia : i < a.size) (hja : j < a.size) :
      SwapsBelow m (a.swap i j) b → SwapsBelow m a b

namespace SwapsBelow
variable {m : Nat} {a b : Array α}

theorem size (h : SwapsBelow m a b) : b.size = a.size := by
  induction h <;> simp_all

theorem perm (h : SwapsBelow m a b) : b.Perm a := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ _ hia hja _ ih => exact ih.trans (Array.swap_perm hia hja)

theorem getElem_ge (h : SwapsBelow m a b) (x : Nat) (hx : m ≤ x) (hxa : x < a.size) :
    b[x]'(h.size ▸ hxa) = a[x] := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ _ _ _ _ ih =>
    rw [ih (by simpa using hxa), Array.getElem_swap]; split <;> (try split) <;> first | omega | rfl

theorem forall_lt (h : SwapsBelow m a b) (Q : α → Prop) (hm : m ≤ a.size)
    (hQ : ∀ x (hx : x < m), Q (a[x]'(by omega))) : ∀ x (hx : x < m), Q (b[x]'(by have := h.size; omega)) := by
  induction h with
  | refl => exact hQ
  | step _ _ _ _ hi hj _ _ _ ih =>
    apply ih (by simpa using hm)
    intro x hx
    simp only [Array.getElem_swap]
    split
    · exact hQ _ hj
    · split
      · exact hQ _ hi
      · exact hQ _ hx

end SwapsBelow

theorem siftDown_swaps (a : Array α) (m hm i) : SwapsBelow m a (siftDown le a m hm i) := by
  fun_induction siftDown le a m hm i with
  | case1 => exact .refl _
  | case2 a hm i hl c hc _ ih => exact .step _ _ _ _ (by omega) hc.2 (by omega) (by omega) ih
  | case3 => exact .refl _

theorem size_siftDown (a : Array α) (m hm i) : (siftDown le a m hm i).size = a.size :=
  (siftDown_swaps le a m hm i).size

theorem SwapsBelow.trans {m : Nat} {a b c : Array α} (h₁ : SwapsBelow m a b) (h₂ : SwapsBelow m b c) :
    SwapsBelow m a c := by
  induction h₁ with
  | refl => exact h₂
  | step _ _ _ _ hi hj hia hja _ ih => exact .step _ _ _ _ hi hj hia hja (ih h₂)

theorem SwapsBelow.weaken {m m' : Nat} {a b : Array α} (hm : m ≤ m') (h : SwapsBelow m a b) :
    SwapsBelow m' a b := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ hi hj hia hja _ ih => exact .step _ _ _ _ (by omega) (by omega) hia hja ih

def HeapAt (a : Array α) (m j : Nat) : Prop :=
  ∀ c (_ : c < m) (hca : c < a.size) (hja : j < a.size), (c = 2*j+1 ∨ c = 2*j+2) → le a[c] a[j]

section
variable {le} (htot : ∀ x y, le x y ∨ le y x) (htrans : ∀ x y z, le x y → le y z → le x z)
include htot

theorem le_refl' (x : α) : le x x := (htot x x).elim id id

theorem le_of_not_le {x y : α} (h : ¬ le x y) : le y x := (htot x y).resolve_left h

theorem child_max (a : Array α) (m i hm) (hl : 2*i+1 < m) (c') (hc' : c' < m)
    (h' : c' = 2*i+1 ∨ c' = 2*i+2) :
    le (a[c']'(by omega)) (a[child le a m i hm]'(by have := child_bounds le a m i hm hl; omega)) := by
  unfold child
  split
  · split
    · rcases h' with rfl | rfl
      · assumption
      · exact le_refl' htot _
    · rcases h' with rfl | rfl
      · exact le_refl' htot _
      · exact le_of_not_le htot ‹_›
  · rcases h' with rfl | rfl
    · exact le_refl' htot _
    · omega

include htrans

theorem siftDown_heap (a : Array α) (m hm i lo) (hlo : lo ≤ i)
    (hpre : ∀ j, lo ≤ j → j ≠ i → HeapAt le a m j)
    (hgp : ∀ p cc (hp : p < a.size) (hcc : cc < a.size), lo ≤ p → (i = 2*p+1 ∨ i = 2*p+2) →
      (cc = 2*i+1 ∨ cc = 2*i+2) → cc < m → le a[cc] a[p]) :
    ∀ j, lo ≤ j → HeapAt le (siftDown le a m hm i) m j := by
  fun_induction siftDown le a m hm i generalizing lo with
  | case1 a hm i hl c hc hle =>
    intro j hj
    by_cases hji : j = i
    · subst hji
      intro c' hc' _ _ h'
      exact htrans _ _ _ (child_max htot a m j hm hl c' hc' h') hle
    · exact hpre j hj hji
  | case2 a hm i hl c hc hle ih =>
    have hca := le_of_not_le htot hle
    apply ih lo (by omega)
    · intro j hj hjc c' hc' hca' hja' h'
      simp only [Array.getElem_swap]
      by_cases hji : j = i
      · subst hji
        have := child_max htot a m j hm hl c' hc' h'
        grind
      · by_cases hjp : i = 2*j+1 ∨ i = 2*j+2
        · have := hgp j (child le a m i hm) (by omega) (by omega) hj hjp hc.1 hc.2
          have := hpre j hj hji c' hc' (by simpa using hca') (by simpa using hja') h'
          grind
        · have := hpre j hj hji c' hc' (by simpa using hca') (by simpa using hja') h'
          grind
    · intro p cc hp hcc _ hp' hcc' hccm
      simp only [Array.getElem_swap]
      have : p = i := by omega
      subst this
      have := hpre (child le a m p hm) (by omega) (by omega) cc hccm (by simpa using hcc) (by omega) hcc'
      grind
  | case3 a hm i hl =>
    intro j hj
    by_cases hji : j = i
    · subst hji; intro c' hc' _ _ h'; omega
    · exact hpre j hj hji

theorem heap_max (a : Array α) (m) (hm : m ≤ a.size) (h : ∀ j, HeapAt le a m j) :
    ∀ x (hx : x < m), le (a[x]'(by omega)) (a[0]'(by omega)) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    rcases x with _ | x
    · exact le_refl' htot _
    · exact htrans _ _ _ (h (x/2) (x+1) hx (by omega) (by omega) (by omega)) (ih (x/2) (by omega) (by omega))

end

@[specialize] def buildHeap (a : Array α) : Nat → Array α
  | 0 => a
  | k+1 => buildHeap (siftDown le a a.size (Nat.le_refl _) k) k

theorem buildHeap_swaps (a : Array α) (k) : SwapsBelow a.size a (buildHeap le a k) := by
  induction k generalizing a with
  | zero => exact .refl _
  | succ k ih =>
    have := ih (siftDown le a a.size (Nat.le_refl _) k)
    rw [size_siftDown] at this
    exact (siftDown_swaps ..).trans this

theorem size_buildHeap (a : Array α) (k) : (buildHeap le a k).size = a.size :=
  (buildHeap_swaps le a k).size

@[specialize] def extract (a : Array α) : (m : Nat) → m ≤ a.size → Array α
  | 0, _ | 1, _ => a
  | m+2, h =>
    extract (siftDown le (a.swap 0 (m+1) (by omega) (by omega)) (m+1) (by simp; omega) 0) (m+1)
      (by rw [size_siftDown]; simp; omega)

theorem extract_swaps (a : Array α) (m h) : SwapsBelow m a (extract le a m h) := by
  fun_induction extract le a m h with
  | case1 | case2 => exact .refl _
  | case3 a m h ih =>
    exact .step _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (((siftDown_swaps ..).trans ih).weaken (by omega))

@[specialize] def heapSort (a : Array α) : Array α :=
  let b := buildHeap le a (a.size / 2)
  extract le b b.size (Nat.le_refl _)

theorem heapSort_perm (a : Array α) : (heapSort le a).Perm a :=
  (extract_swaps ..).perm.trans (buildHeap_swaps le a _).perm

def SortedFrom (a : Array α) (m : Nat) : Prop :=
  ∀ x y (_ : m ≤ x) (_ : x < y) (hy : y < a.size), le (a[x]'(by omega)) a[y]

def Below (a : Array α) (m : Nat) : Prop :=
  ∀ x y (_ : x < m) (_ : m ≤ y) (hy : y < a.size), le (a[x]'(by omega)) a[y]

section
variable {le} (htot : ∀ x y, le x y ∨ le y x) (htrans : ∀ x y z, le x y → le y z → le x z)
include htot htrans

theorem buildHeap_heap (a : Array α) (k) (h : ∀ j, k ≤ j → HeapAt le a a.size j) :
    ∀ j, HeapAt le (buildHeap le a k) (buildHeap le a k).size j := by
  induction k generalizing a with
  | zero => simpa [buildHeap] using h
  | succ k ih =>
    apply ih
    rw [size_siftDown]
    exact siftDown_heap htot htrans a _ _ k k (Nat.le_refl _) (fun j hj hjk => h j (by omega))
      (fun p _ _ _ hp hi => by omega)

theorem extract_sorted (a : Array α) (m h) (hh : ∀ j, HeapAt le a m j) (hs : SortedFrom le a m)
    (hb : Below le a m) : SortedFrom le (extract le a m h) 0 := by
  fun_induction extract le a m h with
  | case1 => intro x y _ _ _; exact hs x y (by omega) ‹_› ‹_›
  | case2 =>
    intro x y _ _ _
    by_cases hx : x = 0
    · subst hx; exact hb 0 y (by omega) (by omega) _
    · exact hs x y (by omega) ‹_› ‹_›
  | case3 a m h ih =>
    have hmax := heap_max htot htrans a (m+2) h hh
    have hsw := siftDown_swaps le (a.swap 0 (m+1) (by omega) (by omega)) (m+1) (by simp; omega) 0
    have hsz := hsw.size
    simp only [Array.size_swap] at hsz
    have hsz2 : (a.swap 0 (m+1) (by omega) (by omega)).size = a.size := by simp
    apply ih
    · intro j
      refine siftDown_heap htot htrans _ _ _ _ 0 (Nat.le_refl _) ?_ ?_ j (Nat.zero_le _)
      · intro j _ hj0 c hc hca hja hcj
        have := hh j c (by omega) (by simpa using hca) (by simpa using hja) hcj
        simp only [Array.getElem_swap]
        grind
      · intro p _ _ _ _ hp; omega
    · intro x y hx hxy hy
      rw [hsw.getElem_ge x hx (by omega), hsw.getElem_ge y (by omega) (by omega)]
      simp only [Array.getElem_swap]
      have := hs x y
      have := hb 0 y
      grind
    · intro x y hx hy hya
      rw [hsw.getElem_ge y hy (by omega)]
      revert x
      refine hsw.forall_lt (fun v => le v ((a.swap 0 (m+1) (by omega) (by omega))[y]'(by omega)))
        (by simp; omega) ?_
      intro x hx
      simp only [Array.getElem_swap]
      have := hmax x
      have := hmax (m+1)
      have := hb x y
      have := hb (m+1) y
      have := hmax 0
      grind

theorem heapSort_sorted (a : Array α) : (heapSort le a).toList.Pairwise (le · ·) := by
  rw [List.pairwise_iff_getElem]
  intro x y hx hy hxy
  simp only [Array.getElem_toList]
  apply extract_sorted htot htrans
  · apply buildHeap_heap htot htrans
    intro j hj c hc
    omega
  · intro x y hx hxy hy; omega
  · intro x y hx hy; omega
  all_goals simp_all [heapSort]

end

theorem heapSort_correct (htot : ∀ x y, le x y ∨ le y x)
    (htrans : ∀ x y z, le x y → le y z → le x z) (a : Array α) :
    (heapSort le a).Perm a ∧ (heapSort le a).toList.Pairwise (le · ·) :=
  ⟨heapSort_perm le a, heapSort_sorted htot htrans a⟩

end HeapSort
