import Minimal.Lemmas

namespace Minimal

def Sat (f : Nat → Tm) (σ : Nat → Option Tm) : Prop := ∀ e t, σ e = some t → f e = t.subst f

namespace Tm

theorem size_le_occurs (f : Nat → Tm) (e : Nat) : ∀ t : Tm, e ∈ t.fvs → (f e).size ≤ (t.subst f).size := by
  intro t; induction t <;> simp_all [fvs, subst, size] <;> grind

theorem size_lt_occurs (f : Nat → Tm) (e : Nat) (t : Tm) (h : e ∈ t.fvs) (hne : t ≠ fv e) :
    (f e).size < (t.subst f).size := by
  cases t <;> simp_all [fvs, subst, size] <;> grind [size_le_occurs]

theorem kids_subst (f : Nat → Tm) (a : Tm) (h : ∀ i, a ≠ fv i) : (a.subst f).kids = a.kids.map (subst f) := by
  cases a <;> simp_all [subst, kids]

theorem subst_ne_of_head (f : Nat → Tm) (a b : Tm) (ha : ∀ i, a ≠ fv i) (hb : ∀ i, b ≠ fv i)
    (h : a.sameHead b = false) : a.subst f ≠ b.subst f := by
  cases a <;> cases b <;> simp_all [sameHead, subst]

theorem kids_eq_of_subst (f : Nat → Tm) (a b : Tm) (ha : ∀ i, a ≠ fv i) (hb : ∀ i, b ≠ fv i)
    (_ : a.sameHead b = true) (e : a.subst f = b.subst f) :
    ∀ p ∈ a.kids.zip b.kids, p.1.subst f = p.2.subst f := by
  have := congrArg kids e
  rw [kids_subst f a ha, kids_subst f b hb] at this
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

theorem unify_sound (f : Nat → Tm) (n : Nat) : ∀ σ dom eqs, Sat f σ → (∀ p ∈ eqs, p.1.subst f = p.2.subst f) →
    (∀ σ', unify n σ dom eqs = .ok σ' → Sat f σ') ∧ unify n σ dom eqs ≠ .contra := by
  intro σ dom eqs
  induction σ, dom, eqs using unify.induct n with
  | case1 σ dom => intro hs _; simp [unify]; exact hs
  | case2 σ dom b rest ih => intro hs he; rw [unify]; simp only [ite_true]; exact ih hs fun p hp => he p (by simp [hp])
  | case3 σ dom a b rest hab e t hv hocc =>
    intro hs he; exfalso
    have hab' := he (a, b) (by simp)
    rcases varSide_spec hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := Tm.size_lt_occurs f e t hocc (Ne.symm hab); simp [Tm.subst] at hab'; rw [hab'] at this; omega
    · have := Tm.size_lt_occurs f e t hocc hab; simp [Tm.subst] at hab'; rw [← hab'] at this; omega
  | case4 σ dom a b rest hab e t hv hocc hok ih =>
    intro hs he
    have hab' := he (a, b) (by simp)
    have het : f e = t.subst f := by
      rcases varSide_spec hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Tm.subst]
    rw [unify]; simp only [hab, ite_false, hv, hocc, hok]
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map] at ih ⊢
    apply ih
    · intro x u hx
      simp only [assign] at hx; split at hx
      · subst_vars; simp_all
      · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hx
        rw [substOne_subst f e t u' het]; exact hs x u' hu'
    · intro p hp; simp only [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp
      simp only [substOne_subst f e t _ het]; exact he q (by simp [hq])
  | case5 σ dom a b rest hab e t hv hocc hok =>
    intro _ _; rw [unify]; simp [hab, hv, hocc, hok]
  | case6 σ dom a b rest hab hv hsh ih =>
    intro hs he
    rw [unify]; simp only [hab, ite_false, hv, hsh, ite_true]
    apply ih hs
    intro p hp; rcases List.mem_append.mp hp with hp | hp
    · exact Tm.kids_eq_of_subst f a b (varSide_none hv).1 (varSide_none hv).2 hsh (he (a, b) (by simp)) p hp
    · exact he p (by simp [hp])
  | case7 σ dom a b rest hab hv hsh =>
    intro _ he; exfalso
    exact Tm.subst_ne_of_head f a b (varSide_none hv).1 (varSide_none hv).2 (by simpa using hsh) (he (a, b) (by simp))

theorem Tm.static_subst {n : Nat} {f : Nat → Tm} : ∀ (u : Tm) d, u.static n d → (∀ i ∈ u.fvs, (f i).static n 0) →
    (u.subst f).static n d := by
  intro u; induction u with
  | fv i => intro d _ h; exact Tm.static_mono (Nat.le_refl _) _ (Nat.zero_le _) (h i (by simp [Tm.fvs]))
  | bind _ a r iha ihr =>
    intro d h hf; simp only [Tm.static, Bool.and_eq_true, Tm.subst, Tm.fvs, List.mem_append] at *
    exact ⟨iha d h.1 fun i hi => hf i (.inl hi), ihr (d + 1) h.2 fun i hi => hf i (.inr hi)⟩
  | _ => intro d h hf; simp_all [Tm.static, Tm.subst, Tm.fvs]

def RulesWF (n : Nat) (σ : Nat → Option Tm) : Prop := ∀ e t, σ e = some t → e < n ∧ t.static n 0

theorem unify_wf (n : Nat) : ∀ σ dom eqs σ', RulesWF n σ → unify n σ dom eqs = .ok σ' → RulesWF n σ' := by
  intro σ dom eqs
  induction σ, dom, eqs using unify.induct n with
  | case1 σ dom => intro σ' h e; simp [unify] at e; exact e ▸ h
  | case2 σ dom b rest ih => intro σ' h e; rw [unify] at e; simp only [ite_true] at e; exact ih σ' h e
  | case3 σ dom a b rest hab e t hv hocc => intro σ' _ h; rw [unify] at h; simp [hab, hv, hocc] at h
  | case4 σ dom a b rest hab e t hv hocc hok ih =>
    intro σ' hw h
    rw [unify] at h; simp only [hab, ite_false, hv, hocc, hok, and_self] at h
    simp only [List.map_attach_eq_pmap, List.pmap_eq_map] at ih h
    refine ih σ' (fun x u hx => ?_) h
    simp only [assign] at hx; split at hx
    · cases hx; subst_vars; exact ⟨hok.2.2.1, hok.2.2.2⟩
    · obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hx
      refine ⟨(hw x u' hu').1, Tm.static_subst u' 0 (hw x u' hu').2 fun i hi => ?_⟩
      split
      · exact hok.2.2.2
      · simp [Tm.static]; exact Tm.fvs_static u' 0 (hw x u' hu').2 i hi
  | case5 σ dom a b rest hab e t hv hocc hok => intro σ' _ h; rw [unify] at h; simp [hab, hv, hocc, hok] at h
  | case6 σ dom a b rest hab hv hsh ih =>
    intro σ' hw h; rw [unify] at h; simp only [hab, ite_false, hv, hsh, ite_true] at h; exact ih σ' hw h
  | case7 σ dom a b rest hab hv hsh => intro σ' _ h; rw [unify] at h; simp [hab, hv, hsh] at h

end Minimal
