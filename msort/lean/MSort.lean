namespace MSort

def LeHead (x : UInt64) (l : List UInt64) : Prop := ∀ y ∈ l.head?, x ≤ y

inductive Sorted : List UInt64 → Prop
  | nil : Sorted []
  | cons : LeHead x l → Sorted l → Sorted (x :: l)

def merge : List UInt64 → List UInt64 → List UInt64
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

def mergeGo : List UInt64 → List UInt64 → List UInt64 → List UInt64
  | [], ys, acc => acc.reverseAux ys
  | x :: xs, [], acc => acc.reverseAux (x :: xs)
  | x :: xs, y :: ys, acc =>
    if x ≤ y then mergeGo xs (y :: ys) (x :: acc) else mergeGo (x :: xs) ys (y :: acc)

def mergeTR (xs ys : List UInt64) : List UInt64 := mergeGo xs ys []

theorem mergeGo_eq (xs ys acc : List UInt64) : mergeGo xs ys acc = acc.reverseAux (merge xs ys) := by
  fun_induction mergeGo xs ys acc with
  | case3 x xs y ys acc h ih => simp [merge, h, ih, List.reverseAux_eq]
  | case4 x xs y ys acc h ih => simp [merge, h, ih, List.reverseAux_eq]
  | _ => simp [merge, List.reverseAux_eq]

@[csimp] theorem merge_eq_mergeTR : @merge = @mergeTR := by
  funext xs ys; simp [mergeTR, mergeGo_eq]

theorem merge_perm (xs ys : List UInt64) : (merge xs ys).Perm (xs ++ ys) := by
  fun_induction merge xs ys with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys h ih => simpa using ih.cons x
  | case4 x xs y ys h ih =>
    exact (ih.cons y).trans (by simpa using (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm)

theorem leHead_merge (h1 : LeHead z xs) (h2 : LeHead z ys) : LeHead z (merge xs ys) := by
  fun_cases merge xs ys <;> simp_all [LeHead]

theorem merge_sorted (xs ys : List UInt64) (hx : Sorted xs) (hy : Sorted ys) : Sorted (merge xs ys) := by
  fun_induction merge xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 x xs y ys h ih =>
    cases hx with
    | cons hh ht => exact .cons (leHead_merge hh (by simp [LeHead, h])) (ih ht hy)
  | case4 x xs y ys h ih =>
    cases hy with
    | cons hh ht => exact .cons (leHead_merge (by simp [LeHead]; exact UInt64.le_of_lt (UInt64.not_le.mp h)) hh) (ih hx ht)

def lenGo : List UInt64 → UInt64 → UInt64
  | [], acc => acc
  | _ :: t, acc => lenGo t (acc + 1)

theorem lenGo_toNat (l : List UInt64) (acc : UInt64) (h : l.length + acc.toNat < 2 ^ 64) :
    (lenGo l acc).toNat = l.length + acc.toNat := by
  induction l generalizing acc with
  | nil => simp [lenGo]
  | cons x t ih =>
    simp only [List.length_cons] at h
    have : (acc + 1).toNat = acc.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    simp [lenGo, ih (acc + 1) (by omega), this]; omega

def splitGo : UInt64 → List UInt64 → List UInt64 → List UInt64 × List UInt64
  | _, [], acc => (acc.reverse, [])
  | k, x :: t, acc => if k = 0 then (acc.reverse, x :: t) else splitGo (k - 1) t (x :: acc)

theorem splitGo_eq (k : UInt64) (l acc : List UInt64) :
    splitGo k l acc = (acc.reverse ++ l.take k.toNat, l.drop k.toNat) := by
  induction l generalizing k acc with
  | nil => simp [splitGo]
  | cons x t ih =>
    by_cases hk : k = 0
    · simp [splitGo, hk]
    · have : k.toNat = (k - 1).toNat + 1 := by
        have : k.toNat ≠ 0 := by intro h; apply hk; exact UInt64.toNat_inj.mp (by simpa using h)
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp; omega
      simp [splitGo, hk, ih, this]

theorem half_facts (n : UInt64) (hn : ¬ n < 2) :
    (n >>> 1).toNat = n.toNat / 2 ∧ (n - (n >>> 1)).toNat = n.toNat - n.toNat / 2 ∧ 2 ≤ n.toNat := by
  have h2 : 2 ≤ n.toNat := by simp [UInt64.lt_iff_toNat_lt] at hn; omega
  have hq : (n >>> 1).toNat = n.toNat / 2 := by simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨hq, ?_, h2⟩
  rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le, hq]; omega), hq]

def msortN (n : UInt64) (l : List UInt64) (h : l.length = n.toNat) : List UInt64 :=
  if hn : n < 2 then l else
  let q := n >>> 1
  let p := splitGo (n - q) l []
  merge (msortN (n - q) p.1 (by have := half_facts n hn; simp [p, splitGo_eq, q]; omega))
    (msortN q p.2 (by have := half_facts n hn; simp [p, splitGo_eq, q]; omega))
termination_by n.toNat
decreasing_by all_goals (have := half_facts n hn; omega)

def msort (l : List UInt64) (h : l.length < 2 ^ 64) : List UInt64 :=
  msortN (lenGo l 0) l (by rw [lenGo_toNat l 0 (by simpa using h)]; simp)

theorem msortN_sorted (n : UInt64) (l : List UInt64) (h) : Sorted (msortN n l h) := by
  fun_induction msortN n l h with
  | case1 n l h hn =>
    match l, h with
    | [], _ => exact .nil
    | [a], _ => exact .cons (by simp [LeHead]) .nil
    | _ :: _ :: _, h => simp [UInt64.lt_iff_toNat_lt] at h hn; omega
  | case2 n l h hn q p ih1 ih2 => exact merge_sorted _ _ ih1 ih2

theorem msortN_perm (n : UInt64) (l : List UInt64) (h) : (msortN n l h).Perm l := by
  fun_induction msortN n l h with
  | case1 => exact .refl _
  | case2 n l h hn q p ih1 ih2 =>
    refine (merge_perm _ _).trans ((ih1.append ih2).trans ?_)
    simp [p, splitGo_eq, List.take_append_drop]

theorem msort_sorted (l : List UInt64) (h) : Sorted (msort l h) := msortN_sorted ..
theorem msort_perm (l : List UInt64) (h) : (msort l h).Perm l := msortN_perm ..

end MSort
