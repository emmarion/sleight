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

def msort : List UInt64 → List UInt64
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    let p := (a :: b :: t).splitAt ((t.length + 3) / 2)
    merge (msort p.1) (msort p.2)
termination_by l => l.length
decreasing_by all_goals simp [List.splitAt_eq]; omega

theorem msort_sorted (l : List UInt64) : Sorted (msort l) := by
  fun_induction msort l with
  | case1 => exact .nil
  | case2 a => exact .cons (by simp [LeHead]) .nil
  | case3 a b t p ih1 ih2 => exact merge_sorted _ _ ih1 ih2

theorem msort_perm (l : List UInt64) : (msort l).Perm l := by
  fun_induction msort l with
  | case1 => exact .nil
  | case2 a => exact .refl _
  | case3 a b t p ih1 ih2 =>
    refine (merge_perm _ _).trans ((ih1.append ih2).trans ?_)
    simp [p, List.splitAt_eq, List.take_append_drop]

end MSort
