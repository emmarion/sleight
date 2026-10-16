import Minimal.EvalH
import Minimal.Lemmas

namespace Minimal

def Tm.ptrBelow (n : Nat) : Tm → Bool
  | .ptr a => a < n
  | .cons h t | .app h t => h.ptrBelow n && t.ptrBelow n
  | .tyc _ ls | .vc _ _ ls => ls.ptrBelow n
  | .bind _ a r => a.ptrBelow n && r.ptrBelow n
  | .tyCtor p | .valCtor p => p.ptrBelow n
  | .predates A x L => A.ptrBelow n && x.ptrBelow n && L.ptrBelow n
  | .subterm A a B b => A.ptrBelow n && a.ptrBelow n && B.ptrBelow n && b.ptrBelow n
  | .fn l _ t _ _ => l.ptrBelow n && t.ptrBelow n
  | .mtbl _ _ _ _ T cs => T.ptrBelow n && cs.ptrBelow n
  | .clo env _ _ => env.ptrBelow n
  | _ => true

theorem Tm.ptrBelow_mono {n m : Nat} (h : n ≤ m) : ∀ t : Tm, t.ptrBelow n → t.ptrBelow m := by
  intro t; induction t <;> simp_all [ptrBelow] <;> omega

namespace FHeap

def OK (H : FHeap) : Prop :=
  ∀ a t, H.blk a = some t → a < H.next ∧ t.ptrBelow a ∧ ∃ d c ls args, t = .app (.vc d c ls) args

def Ext (H H' : FHeap) : Prop := H.next ≤ H'.next ∧ ∀ a, a < H.next → H'.blk a = H.blk a

theorem Ext.refl (H : FHeap) : H.Ext H := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {H1 H2 H3 : FHeap} (a : H1.Ext H2) (b : H2.Ext H3) : H1.Ext H3 :=
  ⟨Nat.le_trans a.1 b.1, fun x hx => (b.2 x (Nat.lt_of_lt_of_le hx a.1)).trans (a.2 x hx)⟩

theorem dec_noPtr (H : FHeap) : ∀ (n : Nat) (t : Tm), t.ptrBelow 0 → H.dec n t = t := by
  intro n t; induction t generalizing n <;> intro h <;> cases n <;> simp_all [dec, Tm.ptrBelow]

theorem dec_fuel {H : FHeap} (hH : H.OK) : ∀ k n (t : Tm), t.ptrBelow k → k ≤ n → H.dec n t = H.dec k t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
    intro n t
    induction t generalizing n <;> intro ht hkn <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
    case ptr a =>
      simp only [decide_eq_true_eq] at ht
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [dec]
      cases hb : H.blk a with
      | none => rfl
      | some t' =>
        obtain ⟨-, hb', -⟩ := hH a t' hb
        show H.dec n' t' = H.dec k' t'
        rw [ihk k' (by omega) n' t' (Tm.ptrBelow_mono (by omega) t' hb') (by omega),
          ihk k' (by omega) k' t' (Tm.ptrBelow_mono (by omega) t' hb') (Nat.le_refl _)]
    all_goals (cases n <;> cases k <;> simp_all [dec])

theorem dec_ext {H H' : FHeap} (hH : H.OK) (he : H.Ext H') : ∀ n (t : Tm), t.ptrBelow H.next → H'.dec n t = H.dec n t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro t
    induction t <;> intro ht <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
    case ptr a =>
      simp only [decide_eq_true_eq] at ht
      cases n with
      | zero => simp [dec]
      | succ n' =>
        simp only [dec, he.2 a ht]
        cases hb : H.blk a with
        | none => simp
        | some t' =>
          obtain ⟨-, hb', -⟩ := hH a t' hb
          exact ihn n' (by omega) t' (Tm.ptrBelow_mono (by omega) t' hb')
    all_goals (cases n <;> simp_all [dec])

theorem slotOf_dec {H : FHeap} (hH : H.OK) (n : Nat) (w : Tm) : Tm.slotOf (H.dec n w) = Tm.slotOf w := by
  cases w <;> cases n <;> simp [dec, Tm.slotOf]
  rename_i a n
  cases hb : H.blk a with
  | none => simp
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec]

theorem dec_subst {H : FHeap} (hH : H.OK) (n : Nat) (f : Nat → Tm) : ∀ t : Tm, t.ptrBelow 0 →
    H.dec n (t.subst f) = t.subst (fun i => H.dec n (f i)) := by
  intro t; induction t generalizing n <;> intro ht <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
  case fv i => simp [Tm.subst]
  case sfv i =>
    simp only [Tm.subst, slotOf_dec hH]
    cases f i <;> cases n <;> simp [Tm.slotOf, dec, Tm.vacant]
  case ptr => simp at ht
  all_goals (cases n <;> simp_all [Tm.subst, dec, dec_noPtr])

theorem env_map_dec (H : FHeap) (n : Nat) (ρ : List Tm) :
    (fun i => H.dec n (Tm.env ρ i)) = Tm.env (ρ.map (H.dec n)) := by
  funext i; simp only [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ρ[i]? <;> cases n <;> simp [dec]

end FHeap

end Minimal
