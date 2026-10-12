import Minimal.Typing

namespace Minimal.Tm

theorem size_inst_fv (t : Tm) (i k : Nat) : (t.inst (.fv i) k).size = t.size := by
  induction t generalizing k <;> simp [inst, size, *] <;> split <;> (try split) <;> simp [size]

theorem subst_static0 (f : Nat → Tm) : ∀ (t : Tm) d, t.static 0 d → t.subst f = t := by
  intro t; induction t <;> intro d h <;> simp_all [static, subst] <;> grind

theorem inst_static {u : Tm} (n : Nat) : ∀ (t : Tm) d k, t.static n d → d ≤ k → t.inst u k = t := by
  intro t; induction t with
  | bind m a r iha ihr =>
    intro d k h hk; simp only [static, Bool.and_eq_true] at h
    simp [inst, iha d k h.1 hk, ihr (d + 1) (k + 1) h.2 (by omega)]
  | _ => intro d k h hk; simp_all [static, inst] <;> grind

theorem static_mono {n n' : Nat} (hn : n ≤ n') : ∀ (t : Tm) {d d'}, d ≤ d' → t.static n d → t.static n' d' := by
  intro t; induction t with
  | bind _ a r iha ihr =>
    intro d d' hd h; simp only [static, Bool.and_eq_true] at *
    exact ⟨iha hd h.1, ihr (by omega) h.2⟩
  | _ => intro d d' hd h; simp_all [static] <;> grind

theorem inst_lc {u : Tm} : ∀ (t : Tm) d k, t.lc d → d ≤ k → t.inst u k = t := by
  intro t; induction t with
  | bind m a r iha ihr =>
    intro d k h hk; simp only [lc] at h
    simp [inst, iha d k h.1 hk, ihr (d + 1) (k + 1) h.2 (by omega)]
  | _ => intro d k h hk; simp_all [lc, inst] <;> grind

theorem subst_lc (f : Nat → Tm) : ∀ (t : Tm) d, t.lc d → t.subst f = t := by
  intro t; induction t <;> intro d h <;> simp_all [lc, subst] <;> grind

theorem subst_subst (f g : Nat → Tm) (t : Tm) : (t.subst g).subst f = t.subst fun i => (g i).subst f := by
  induction t <;> simp_all [subst]

theorem subst_inst (f : Nat → Tm) (hf : ∀ i, (f i).lc 0) (u : Tm) :
    ∀ (t : Tm) k, (t.inst u k).subst f = (t.subst f).inst (u.subst f) k := by
  intro t; induction t with
  | fv i => intro k; simp [inst, subst, inst_lc (f i) 0 k (hf i) (Nat.zero_le _)]
  | bv i => intro k; simp only [inst]; split <;> (try split) <;> simp [subst, inst, *]
  | _ => intro k; simp_all [inst, subst]

theorem subst_ext {f g : Nat → Tm} : ∀ (t : Tm), (∀ i ∈ t.fvs, f i = g i) → t.subst f = t.subst g := by
  intro t; induction t <;> intro h <;> simp_all [subst, fvs]

theorem fvs_static {n : Nat} : ∀ (t : Tm) d, t.static n d → ∀ i ∈ t.fvs, i < n := by
  intro t; induction t <;> intro d h i hi <;> simp_all [static, fvs] <;> grind

theorem static_inst {n : Nat} {u : Tm} (hu : u.static n 0) :
    ∀ (t : Tm) d, t.static n (d + 1) → (t.inst u d).static n d := by
  intro t; induction t with
  | bv i => intro d h; simp only [static, inst] at *; split <;> (try split) <;> simp_all [static] <;>
      first | omega | exact static_mono (Nat.le_refl _) u (Nat.zero_le _) hu
  | bind m a r iha ihr =>
    intro d h; simp only [static, inst, Bool.and_eq_true] at *; exact ⟨iha d h.1, ihr (d + 1) h.2⟩
  | _ => intro d h; simp_all [static, inst]

theorem lc_mono : ∀ (t : Tm) {d d'}, d ≤ d' → t.lc d → t.lc d' := by
  intro t; induction t with
  | bind _ a r iha ihr => intro d d' hd h; simp only [lc] at *; exact ⟨iha hd h.1, ihr (by omega) h.2⟩
  | _ => intro d d' hd h; simp_all [lc] <;> grind

theorem lc_inst {u : Tm} (hu : u.lc 0) : ∀ (t : Tm) d, t.lc (d + 1) → (t.inst u d).lc d := by
  intro t; induction t with
  | bv i => intro d h; simp only [lc, inst] at *; split <;> (try split) <;> simp_all [lc] <;>
      first | omega | exact lc_mono u (Nat.zero_le _) hu
  | bind m a r iha ihr =>
    intro d h; simp only [lc, inst] at *; exact ⟨iha d h.1, ihr (d + 1) h.2⟩
  | _ => intro d h; simp_all [lc, inst]

theorem lc_subst {f : Nat → Tm} (hf : ∀ i, (f i).lc 0) : ∀ (t : Tm) d n, t.static n d → (t.subst f).lc d := by
  intro t; induction t with
  | fv i => intro d n _; exact lc_mono _ (Nat.zero_le _) (hf i)
  | bind _ a r iha ihr =>
    intro d n h; simp only [static, Bool.and_eq_true, subst, lc] at *; exact ⟨iha d n h.1, ihr (d + 1) n h.2⟩
  | _ => intro d n h; simp_all [lc, subst, static] <;> grind

theorem psub_subst (f : Nat → Tm) {a b : Tm} (h : PSub a b) : PSub (a.subst f) (b.subst f) := by
  induction h with
  | trans _ _ i1 i2 => exact .trans i1 i2
  | _ => constructor

theorem psub_size {a b : Tm} (h : PSub a b) : a.size < b.size := by
  induction h <;> (try simp [size]) <;> omega

theorem psub_levels {a b : Tm} (h : PSub a b) : ∀ n ∈ a.levels, n ∈ b.levels := by
  induction h <;> simp_all [levels]

theorem strictSub_psub (a : Tm) : ∀ b, a.strictSub b → PSub a b := by
  intro b; induction b with
  | cons h t ih1 ih2 =>
    simp only [strictSub, Bool.or_eq_true, beq_iff_eq]
    rintro (((rfl | rfl) | h) | h)
    · exact .head
    · exact .tail
    · exact .trans (ih1 h) .head
    · exact .trans (ih2 h) .tail
  | app _ x _ ih =>
    simp only [strictSub, Bool.or_eq_true, beq_iff_eq]
    rintro (rfl | h)
    · constructor
    · exact .trans (ih h) (by constructor)
  | _ => simp [strictSub]

end Minimal.Tm
