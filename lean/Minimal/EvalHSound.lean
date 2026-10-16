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

theorem alloc_ok {H : FHeap} (hH : H.OK) {d c : Nat} {ls args : Tm} (hp : (Tm.app (.vc d c ls) args).ptrBelow H.next) :
    (H.alloc (.app (.vc d c ls) args)).1.OK ∧ H.Ext (H.alloc (.app (.vc d c ls) args)).1 := by
  refine ⟨fun a t h => ?_, by simp [alloc], fun a ha => by simp [alloc]; omega⟩
  simp only [alloc] at h ⊢
  split at h
  · cases h; subst_vars; exact ⟨by omega, hp, d, c, ls, args, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hH a t h; exact ⟨by omega, h2, h3⟩

theorem alloc_next (H : FHeap) (t : Tm) : (H.alloc t).1.next = H.next + 1 := rfl

theorem alloc_dec (H : FHeap) (t : Tm) (n : Nat) : (H.alloc t).1.dec (n + 1) (.ptr (H.alloc t).2) = (H.alloc t).1.dec n t := by
  simp [alloc, dec]

theorem decode_eq {H : FHeap} (hH : H.OK) {t : Tm} (ht : t.ptrBelow H.next) {k : Nat} (hk : H.next ≤ k) :
    H.dec k t = H.decode t := dec_fuel hH _ _ _ ht hk

theorem decode_ext {H H' : FHeap} (hH : H.OK) (he : H.Ext H') {t : Tm} (ht : t.ptrBelow H.next) :
    H'.decode t = H.decode t := by
  simp only [decode]; rw [dec_ext hH he _ t ht]; exact dec_fuel hH _ _ _ ht he.1

theorem box_spec {H : FHeap} (hH : H.OK) : ∀ t : Tm, t.ptrBelow H.next →
    (H.box t).1.OK ∧ H.Ext (H.box t).1 ∧ (H.box t).2.ptrBelow (H.box t).1.next ∧
      (H.box t).1.decode (H.box t).2 = H.decode t := by
  intro t
  induction t generalizing H with
  | cons h t ihh iht =>
    intro hp; simp only [Tm.ptrBelow, Bool.and_eq_true] at hp
    obtain ⟨o1, e1, p1, d1⟩ := ihh hH hp.1
    obtain ⟨o2, e2, p2, d2⟩ := iht o1 (Tm.ptrBelow_mono e1.1 _ hp.2)
    simp only [box]
    refine ⟨o2, e1.trans e2, by simp [Tm.ptrBelow, p2, Tm.ptrBelow_mono e2.1 _ p1], ?_⟩
    have a1 := (decode_ext o1 e2 p1).trans d1
    have a2 := d2.trans (decode_ext hH e1 hp.2)
    simp only [decode, dec] at a1 a2 ⊢
    rw [a1, a2]
  | app h args ihh iha =>
    intro hp
    cases h with
    | vc d c ls =>
      simp only [Tm.ptrBelow, Bool.and_eq_true] at hp
      obtain ⟨o1, e1, p1, d1⟩ := iha hH hp.2
      have hb : (Tm.app (.vc d c ls) (H.box args).2).ptrBelow (H.box args).1.next := by
        simp [Tm.ptrBelow, p1, Tm.ptrBelow_mono e1.1 _ hp.1]
      obtain ⟨o2, e2⟩ := alloc_ok o1 hb
      simp only [box]
      refine ⟨o2, e1.trans e2, by simp [Tm.ptrBelow, alloc], ?_⟩
      have hls := decode_ext hH e1 hp.1
      simp only [decode] at d1 hls ⊢
      rw [alloc_next, alloc_dec]
      simp only [dec]
      rw [dec_ext o1 e2 _ _ p1, dec_ext o1 e2 _ _ (Tm.ptrBelow_mono e1.1 _ hp.1), d1, hls]
    | _ => exact ⟨hH, Ext.refl H, hp, rfl⟩
  | _ => intro hp; exact ⟨hH, Ext.refl H, hp, rfl⟩

theorem boxList_spec {H : FHeap} (hH : H.OK) : ∀ ts : List Tm, (∀ t ∈ ts, t.ptrBelow H.next) →
    (H.boxList ts).1.OK ∧ H.Ext (H.boxList ts).1 ∧ (∀ w ∈ (H.boxList ts).2, w.ptrBelow (H.boxList ts).1.next) ∧
      (H.boxList ts).2.map (H.boxList ts).1.decode = ts.map H.decode := by
  intro ts
  induction ts generalizing H with
  | nil => intro; exact ⟨hH, Ext.refl H, by simp [boxList], by simp [boxList]⟩
  | cons t ts ih =>
    intro hp
    obtain ⟨o1, e1, p1, d1⟩ := box_spec hH t (hp t (by simp))
    obtain ⟨o2, e2, p2, d2⟩ := ih o1 (fun u hu => Tm.ptrBelow_mono e1.1 _ (hp u (by simp [hu])))
    simp only [boxList]
    refine ⟨o2, e1.trans e2, ?_, ?_⟩
    · simp only [List.mem_cons]; rintro w (rfl | hw)
      · exact Tm.ptrBelow_mono e2.1 _ p1
      · exact p2 w hw
    · simp only [List.map_cons, d2, decode_ext o1 e2 p1, d1, List.cons.injEq, true_and]
      exact List.map_congr_left (fun u hu => decode_ext hH e1 (hp u (by simp [hu])))

end FHeap

end Minimal
