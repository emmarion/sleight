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

end Minimal.Tm
