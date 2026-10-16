import Minimal.Lemmas

namespace Minimal

def Sat (f : Nat → Tm) (σ : Nat → Option Tm) : Prop := ∀ e t, σ e = some t → f e = t.subst f

namespace Tm

theorem size_le_occurs (f : Nat → Tm) (e : Nat) : ∀ t : Tm, e ∈ t.occ → (f e).size ≤ (t.subst f).size := by
  intro t; induction t <;> simp_all [occ, subst, size] <;> grind

theorem size_lt_occurs (f : Nat → Tm) (e : Nat) (t : Tm) (h : e ∈ t.occ) (hne : t ≠ fv e) :
    (f e).size < (t.subst f).size := by
  cases t <;> simp_all [occ, subst, size] <;> grind [size_le_occurs]

theorem kids_subst (f : Nat → Tm) (a : Tm) (h : ∀ i, a ≠ fv i) (hs : a.isSlot = false) :
    (a.subst f).kids = a.kids.map (subst f) := by
  cases a <;> simp_all [subst, kids, isSlot]

theorem subst_ne_of_head (f : Nat → Tm) (a b : Tm) (ha : ∀ i, a ≠ fv i) (hb : ∀ i, b ≠ fv i)
    (has : a.isSlot = false) (hbs : b.isSlot = false)
    (h : a.sameHead b = false) : a.subst f ≠ b.subst f := by
  cases a <;> cases b <;> simp_all [sameHead, subst, isSlot]

theorem kids_eq_of_subst (f : Nat → Tm) (a b : Tm) (ha : ∀ i, a ≠ fv i) (hb : ∀ i, b ≠ fv i)
    (has : a.isSlot = false) (hbs : b.isSlot = false)
    (_ : a.sameHead b = true) (e : a.subst f = b.subst f) :
    ∀ p ∈ a.kids.zip b.kids, p.1.subst f = p.2.subst f := by
  have := congrArg kids e
  rw [kids_subst f a ha has, kids_subst f b hb hbs] at this
  generalize a.kids = xs, b.kids = ys at this
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at this
      intro p hp; simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact this.1
      · exact ih ys this.2 p hp

theorem bound_of_subst (f : Nat → Tm) : ∀ (t : Tm) d, (t.subst f).bound d = true → t.bound d = true := by
  intro t; induction t <;> intro d h <;> simp_all [subst, bound]

theorem bound_of_lc : ∀ (t : Tm) d, t.lc d → t.bound d = true := by
  intro t; induction t <;> intro d h <;> simp_all [lc, bound]

end Tm

theorem varSide_spec {a b : Tm} {e : Nat} {t : Tm} (h : varSide a b = some (e, t)) :
    (a = .fv e ∧ t = b) ∨ (b = .fv e ∧ t = a) := by
  unfold varSide at h; split at h <;> simp_all

theorem varSide_none {a b : Tm} (h : varSide a b = none) : (∀ i, a ≠ .fv i) ∧ (∀ i, b ≠ .fv i) := by
  unfold varSide at h; split at h <;> simp_all

theorem substOne_subst (f : Nat → Tm) (e : Nat) (t u : Tm) (h : f e = t.subst f) :
    (substOne e t u).subst f = u.subst f := by
  simp only [substOne, Tm.subst_subst]
  congr 1; funext i; split <;> simp_all [Tm.subst]

theorem canonBy_sound {σ : Nat → Option Tm} {f : Nat → Tm} (h : Sat f σ) (t : Tm) : (canonBy σ t).subst f = t.subst f := by
  simp only [canonBy]
  induction t with
  | fv i => cases e : σ i with
    | none => simp [Tm.subst2, Tm.subst, e]
    | some u => simp [Tm.subst2, Tm.subst, e, h i u e]
  | _ => simp_all [Tm.subst2, Tm.subst]

theorem Tm.sameHead_of_subst {f : Nat → Tm} {a b : Tm} (ha : a.isHead = true) (hb : b.isHead = true)
    (h : a.subst f = b.subst f) : a.sameHead b = true := by
  cases a <;> cases b <;> simp_all [Tm.isHead, Tm.subst, Tm.sameHead]

theorem step_assign {atoms : Atoms} {σ : Nat → Option Tm} {a b t : Tm} {e : Nat} {keep : List (Tm × Tm)} {f : Nat → Tm}
    (h : step atoms σ a b = .assign e t keep) (hab : a.subst f = b.subst f) :
    varSide a b = some (e, t) ∧ f e = t.subst f ∧ keep = [] := by
  unfold step at h
  split at h
  · rename_i hv; cases h
    exact ⟨hv, by rcases varSide_spec hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Tm.subst], rfl⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hs
        split at h
        · rename_i hh; simp only [Bool.and_eq_true] at hh; exact absurd (Tm.sameHead_of_subst hh.1 hh.2 hab) hs
        · cases h

theorem step_split {atoms : Atoms} {σ : Nat → Option Tm} {a b : Tm} (h : step atoms σ a b = .split) :
    varSide a b = none ∧ a.isSlot = false ∧ b.isSlot = false ∧ a.sameHead b = true := by
  unfold step at h
  split at h
  · cases h
  · rename_i hv
    split at h
    · cases h
    · rename_i hsl; simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hsl
      refine ⟨hv, hsl.1, hsl.2, ?_⟩
      split at h
      · assumption
      · split at h
        · split at h <;> (try split at h) <;> cases h
        · cases h

theorem step_other {atoms : Atoms} {σ : Nat → Option Tm} {a b : Tm} (h : step atoms σ a b = .stop) :
    varSide a b = none ∧ a.isSlot = false ∧ b.isSlot = false ∧ a.sameHead b = false := by
  unfold step at h
  split at h
  · simp at h
  · rename_i hv
    split at h
    · simp at h
    · rename_i hsl; simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hsl
      refine ⟨hv, hsl.1, hsl.2, ?_⟩
      split at h
      · simp at h
      · simp_all

def AtomSound (f : Nat → Tm) (atoms : Atoms) : Prop :=
  ∀ σ, Sat f σ → ∀ a b, a.subst f = b.subst f →
    ∃ more, atoms σ a b = some more ∧ ∀ p ∈ more, p.1.subst f = p.2.subst f

theorem unify_sound (f : Nat → Tm) (hf : ∀ i, (f i).bound 0 = true) (n : Nat) (atoms : Atoms) (ha : AtomSound f atoms) :
    ∀ σ dom eqs, Sat f σ → (∀ p ∈ eqs, p.1.subst f = p.2.subst f) →
    (∀ σ', unify n atoms σ dom eqs = .ok σ' → Sat f σ') ∧ unify n atoms σ dom eqs ≠ .contra := by
  intro σ dom eqs
  induction σ, dom, eqs using unify.induct n atoms with
  | case1 σ dom => intro hs _; simp [unify]; exact hs
  | case2 σ dom b rest ih => intro hs he; rw [unify]; simp only [ite_true]; exact ih hs fun p hp => he p (by simp [hp])
  | case3 σ dom a b rest hab e t keep hp hocc =>
    intro hs he; exfalso
    have hab' := he (a, b) (by simp)
    obtain ⟨hv, -, -⟩ := step_assign hp hab'
    rcases hocc with hocc | hb
    · rcases varSide_spec hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have := Tm.size_lt_occurs f e t hocc (Ne.symm hab); simp [Tm.subst] at hab'; rw [hab'] at this; omega
      · have := Tm.size_lt_occurs f e t hocc hab; simp [Tm.subst] at hab'; rw [← hab'] at this; omega
    · have het : f e = t.subst f := by
        rcases varSide_spec hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Tm.subst]
      have := Tm.bound_of_subst f t 0 (het ▸ hf e)
      simp_all
  | case4 σ dom a b rest hab e t keep hp hocc hnone =>
    intro hs he; exfalso
    obtain ⟨-, het, -⟩ := step_assign hp (he (a, b) (by simp))
    obtain ⟨more, hm, _⟩ := ha σ hs (.fv e) t (by simpa [Tm.subst] using het)
    rw [hm] at hnone; cases hnone
  | case5 σ dom a b rest hab e t keep hp hocc more hmore hok ih =>
    intro hs he
    obtain ⟨-, het, rfl⟩ := step_assign hp (he (a, b) (by simp))
    obtain ⟨more', hm, hmo⟩ := ha σ hs (.fv e) t (by simpa [Tm.subst] using het)
    rw [hm] at hmore; cases hmore
    rw [unify]; simp only [hab, ite_false, hp, hocc, hm, hok]
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map, List.append_nil] at ih ⊢
    apply ih
    · intro x u hx
      simp only [assign] at hx; split at hx
      · subst_vars; simp_all
      · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hx
        rw [substOne_subst f e t u' het]; exact hs x u' hu'
    · intro p hp; simp only [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp
      simp only [substOne_subst f e t _ het]
      rcases List.mem_append.mp hq with hq | hq
      · exact hmo q hq
      · exact he q (by simp [hq])
  | case6 σ dom a b rest hab e t keep hp hocc more hmore hok =>
    intro _ _; rw [unify]; simp [hab, hp, hocc, hmore, hok]
  | case7 σ dom a b rest hab hp ih =>
    intro hs he
    obtain ⟨hv, has, hbs, hsh⟩ := step_split hp
    rw [unify]; simp only [hab, ite_false, hp]
    apply ih hs
    intro p hp; rcases List.mem_append.mp hp with hp | hp
    · exact Tm.kids_eq_of_subst f a b (varSide_none hv).1 (varSide_none hv).2 has hbs hsh (he (a, b) (by simp)) p hp
    · exact he p (by simp [hp])
  | case8 σ dom a b rest hab hp ih =>
    intro hs he
    rw [unify]; simp only [hab, ite_false, hp]
    exact ih hs fun p hp => he p (by simp [hp])
  | case9 σ dom a b rest hab hp =>
    intro _ he; exfalso
    obtain ⟨hv, has, hbs, hsh⟩ := step_other hp
    exact Tm.subst_ne_of_head f a b (varSide_none hv).1 (varSide_none hv).2 has hbs (by simpa using hsh) (he (a, b) (by simp))

theorem Tm.static_subst {n : Nat} {f : Nat → Tm} : ∀ (u : Tm) d, u.static n d → (∀ i ∈ u.fvs, (f i).static n 0) →
    (u.subst f).static n d := by
  intro u; induction u with
  | fv i => intro d _ h; exact Tm.static_mono (Nat.le_refl _) _ (Nat.zero_le _) (h i (by simp [Tm.fvs]))
  | bind _ a r iha ihr =>
    intro d h hf; simp only [Tm.static, Bool.and_eq_true, Tm.subst, Tm.fvs, List.mem_append] at *
    exact ⟨iha d h.1 fun i hi => hf i (.inl hi), ihr (d + 1) h.2 fun i hi => hf i (.inr hi)⟩
  | sfv i => intro d _ h; exact Tm.slotOf_static d (h i (by simp [Tm.fvs]))
  | _ => intro d h hf; simp_all [Tm.static, Tm.subst, Tm.fvs]

theorem Tm.static_subst2 {n : Nat} {f g : Nat → Tm} : ∀ (u : Tm) d, u.static n d →
    (∀ i ∈ u.fvs, (f i).static n 0 ∧ (g i).static n 0) → (u.subst2 f g).static n d := by
  intro u; induction u with
  | fv i => intro d _ h; exact Tm.static_mono (Nat.le_refl _) _ (Nat.zero_le _) (h i (by simp [Tm.fvs])).1
  | sfv i => intro d _ h; exact Tm.static_mono (Nat.le_refl _) _ (Nat.zero_le _) (h i (by simp [Tm.fvs])).2
  | bind _ a r iha ihr =>
    intro d h hf; simp only [Tm.static, Bool.and_eq_true, Tm.subst2, Tm.fvs, List.mem_append] at *
    exact ⟨iha d h.1 fun i hi => hf i (.inl hi), ihr (d + 1) h.2 fun i hi => hf i (.inr hi)⟩
  | _ => intro d h hf; simp_all [Tm.static, Tm.subst2, Tm.fvs]

def RulesWF (n : Nat) (σ : Nat → Option Tm) : Prop := ∀ e t, σ e = some t → e < n ∧ t.static n 0

theorem unify_wf (n : Nat) (atoms : Atoms) : ∀ σ dom eqs σ', RulesWF n σ → unify n atoms σ dom eqs = .ok σ' → RulesWF n σ' := by
  intro σ dom eqs
  induction σ, dom, eqs using unify.induct n atoms with
  | case1 σ dom => intro σ' h e; simp [unify] at e; exact e ▸ h
  | case2 σ dom b rest ih => intro σ' h e; rw [unify] at e; simp only [ite_true] at e; exact ih σ' h e
  | case3 σ dom a b rest hab e t keep hv hocc => intro σ' _ h; rw [unify] at h; simp [hab, hv, hocc] at h
  | case4 σ dom a b rest hab e t keep hv hocc hnone => intro σ' _ h; rw [unify] at h; simp [hab, hv, hocc, hnone] at h
  | case5 σ dom a b rest hab e t keep hv hocc more hmore hok ih =>
    intro σ' hw h
    rw [unify] at h; simp only [hab, ite_false, hv, hocc, hmore, hok, and_self] at h
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map] at ih h
    refine ih σ' (fun x u hx => ?_) h
    simp only [assign] at hx; split at hx
    · cases hx; subst_vars; exact ⟨hok.2.2.1, hok.2.2.2⟩
    · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hx
      refine ⟨(hw x u' hu').1, Tm.static_subst u' 0 (hw x u' hu').2 fun i hi => ?_⟩
      split
      · exact hok.2.2.2
      · simp [Tm.static]; exact Tm.fvs_static u' 0 (hw x u' hu').2 i hi
  | case6 σ dom a b rest hab e t keep hv hocc more hmore hok => intro σ' _ h; rw [unify] at h; simp [hab, hv, hocc, hmore, hok] at h
  | case7 σ dom a b rest hab hv ih =>
    intro σ' hw h; rw [unify] at h; simp only [hab, ite_false, hv] at h; exact ih σ' hw h
  | case8 σ dom a b rest hab hv ih =>
    intro σ' hw h; rw [unify] at h; simp only [hab, ite_false, hv] at h; exact ih σ' hw h
  | case9 σ dom a b rest hab hv => intro σ' _ h; rw [unify] at h; simp [hab, hv] at h

end Minimal
