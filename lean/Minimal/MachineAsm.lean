import Minimal.MachineRun

namespace Minimal

def Cert (P : Prog) (env : List Tm) (gid : Nat) : Prop :=
  ∃ (Gd : UCtx) (Gr : Group) (O : Uses) (K : Caps), P.groups[gid]? = some Gr ∧ EnvOK P env Gd.Γ ∧
    GroupOK P gid Gd.Γ Gr ∧ Gd.fill = false ∧ Gd.Γ.ghost = false ∧ (∀ j, Gd.uq.contains j = true → j < Gd.Γ.n) ∧
    usesFns P gid Gd Gr Gr.fns = some (O, K) ∧ Gd.defOK Gr O = true

def CloOK (P : Prog) : Tm → Prop
  | .clo env gid _ => Cert P env.toList gid ∧ CloOK P env
  | .cons a b | .app a b | .bind _ a b => CloOK P a ∧ CloOK P b
  | .tyc _ a | .vc _ _ a | .tyCtor a | .valCtor a => CloOK P a
  | .predates a b c => CloOK P a ∧ CloOK P b ∧ CloOK P c
  | .subterm a b c d => CloOK P a ∧ CloOK P b ∧ CloOK P c ∧ CloOK P d
  | .fn a _ b _ _ | .mtbl _ _ _ _ a b => CloOK P a ∧ CloOK P b
  | _ => True

def Tm.noClo : Tm → Bool
  | .clo .. => false
  | .cons a b | .app a b | .bind _ a b => a.noClo && b.noClo
  | .tyc _ a | .vc _ _ a | .tyCtor a | .valCtor a => a.noClo
  | .predates a b c => a.noClo && b.noClo && c.noClo
  | .subterm a b c d => a.noClo && b.noClo && c.noClo && d.noClo
  | .fn a _ b _ _ | .mtbl _ _ _ _ a b => a.noClo && b.noClo
  | _ => true

variable {P : Prog}

theorem CloOK.subst {f : Nat → Tm} (hf : ∀ i, CloOK P (f i)) : ∀ t : Tm, t.noClo = true → CloOK P (t.subst f)
  | .fv i, _ => hf i
  | .clo .., h => by simp [Tm.noClo] at h
  | .cons a b, h | .app a b, h | .bind _ a b, h => by
    simp only [Tm.noClo, Bool.and_eq_true] at h
    exact ⟨CloOK.subst hf a h.1, CloOK.subst hf b h.2⟩
  | .tyc _ a, h | .vc _ _ a, h | .tyCtor a, h | .valCtor a, h => by
    simp only [Tm.noClo] at h; exact CloOK.subst hf a h
  | .predates a b c, h => by
    simp only [Tm.noClo, Bool.and_eq_true] at h
    exact ⟨CloOK.subst hf a h.1.1, CloOK.subst hf b h.1.2, CloOK.subst hf c h.2⟩
  | .subterm a b c d, h => by
    simp only [Tm.noClo, Bool.and_eq_true] at h
    exact ⟨CloOK.subst hf a h.1.1.1, CloOK.subst hf b h.1.1.2, CloOK.subst hf c h.1.2, CloOK.subst hf d h.2⟩
  | .fn a _ b _ _, h | .mtbl _ _ _ _ a b, h => by
    simp only [Tm.noClo, Bool.and_eq_true] at h
    exact ⟨CloOK.subst hf a h.1, CloOK.subst hf b h.2⟩
  | .bv _, _ | .nil, _ | .univ, _ | .level, _ | .lvl _, _ | .tok, _ | .nat _, _ | .ptr _, _ => trivial

theorem Tm.noClo_static : ∀ (t : Tm) (n d : Nat), t.static n d = true → t.noClo = true
  | .cons a b, n, d, h | .app a b, n, d, h => by
    simp only [Tm.static, Bool.and_eq_true] at h; simp [Tm.noClo, Tm.noClo_static a n d h.1, Tm.noClo_static b n d h.2]
  | .bind _ a b, n, d, h => by
    simp only [Tm.static, Bool.and_eq_true] at h
    simp [Tm.noClo, Tm.noClo_static a n d h.1, Tm.noClo_static b n (d + 1) h.2]
  | .tyc _ a, n, d, h | .vc _ _ a, n, d, h | .tyCtor a, n, d, h | .valCtor a, n, d, h => by
    simp only [Tm.static] at h; simp [Tm.noClo, Tm.noClo_static a n d h]
  | .predates a b c, n, d, h => by
    simp only [Tm.static, Bool.and_eq_true] at h
    simp [Tm.noClo, Tm.noClo_static a n d h.1.1, Tm.noClo_static b n d h.1.2, Tm.noClo_static c n d h.2]
  | .subterm a b c e, n, d, h => by
    simp only [Tm.static, Bool.and_eq_true] at h
    simp [Tm.noClo, Tm.noClo_static a n d h.1.1.1, Tm.noClo_static b n d h.1.1.2, Tm.noClo_static c n d h.1.2,
      Tm.noClo_static e n d h.2]
  | .fn a _ b _ _, n, d, h | .mtbl _ _ _ _ a b, n, d, h => by
    simp only [Tm.static, Bool.and_eq_true] at h; simp [Tm.noClo, Tm.noClo_static a n d h.1, Tm.noClo_static b n d h.2]
  | .clo .., _, _, h => by simp [Tm.static] at h
  | .fv _, _, _, _ | .bv _, _, _, _ | .nil, _, _, _ | .univ, _, _, _ | .level, _, _, _ | .lvl _, _, _, _
  | .tok, _, _, _ | .nat _, _, _, _ | .ptr _, _, _, _ => rfl

mutual
theorem TmTy.noClo {Γ : Ctx} {t T : Tm} : TmTy P Γ t T → t.noClo = true
  | .fv _ | .fvIs .. | .univ | .level => rfl
  | .tyc _ _ ha | .vc _ _ ha => by simp only [Tm.noClo]; exact ArgsTy.noClo ha
  | .tyApp hh _ ha | .vcApp hh _ ha => by simp only [Tm.noClo, Bool.and_eq_true]; exact ⟨TmTy.noClo hh, ArgsTy.noClo ha⟩
  | .tyCtor _ hs | .valCtor _ hs _ | .fn _ _ _ _ hs | .mtbl hs => Tm.noClo_static _ _ _ hs
  | .predates h1 _ h2 _ h3 _ => by simp only [Tm.noClo, Bool.and_eq_true]; exact ⟨⟨TmTy.noClo h1, TmTy.noClo h2⟩, TmTy.noClo h3⟩
  | .subterm h1 _ h2 _ h3 _ h4 _ => by
    simp only [Tm.noClo, Bool.and_eq_true]; exact ⟨⟨⟨TmTy.noClo h1, TmTy.noClo h2⟩, TmTy.noClo h3⟩, TmTy.noClo h4⟩

theorem ArgsTy.noClo {Γ : Ctx} {args t out : Tm} : ArgsTy P Γ args t out → args.noClo = true
  | .nil => rfl
  | .cons h _ ha | .isCons h _ ha | .anyCons h ha => by
    simp only [Tm.noClo, Bool.and_eq_true]; exact ⟨TmTy.noClo h, ArgsTy.noClo ha⟩
end

theorem usesFns_spec {gid : Nat} {G : UCtx} {Gr : Group} : ∀ (Fs : List FnDef) (O : Uses) (K : Caps),
    usesFns P gid G Gr Fs = some (O, K) → ∀ (k : Nat) (F : FnDef), Fs[k]? = some F →
    ∃ U K', usesCore P gid (G.fnCtx Gr F) ((teleUs F.tele).drop F.np) (G.Γ.body Gr F).2 F.body = some (U, K') ∧
      (U.below G.Γ.n).Sub O ∧ (F.u = false → ∀ i, (U.below G.Γ.n).lookup i ≠ some true) ∧
      (∀ (k' : Nat) (F' : FnDef), Gr.fns[k']? = some F' → F'.u = true → U.lookup (G.Γ.n + k') = none) ∧
      (∀ i, O.lookup i = some true → ((U.below G.Γ.n).lookup i).isSome → (U.below G.Γ.n).lookup i = some true)
  | [], _, _, _, k, F, h => by simp at h
  | F :: Fs, O, K, h, k, F', hk => by
    rw [usesFns] at h
    obtain ⟨⟨U, K0⟩, hU, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_true,
      not_or, not_exists, not_and] at hc
    obtain ⟨⟨R, KR⟩, hR, h⟩ := Option.bind_eq_some_iff.mp h
    have hseq := UR.seq_fst h
    simp only [UR.below] at hseq
    obtain ⟨sA, sR⟩ := Uses.seq_sub hseq
    have hfree := (Uses.seq_spec hseq).1
    have hlk := (Uses.seq_spec hseq).2
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
      refine ⟨U, K0, hU, sA, fun hu i hi => ?_, fun k' F'' hF'' hu => ?_, fun i hO hi => ?_⟩
      · have := hc.1 hu; simp only [UR.below] at this
        exact this _ (lookup_mem hi) rfl
      · have := hc.2 (F'', k') (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hF''))
        simp only [hu] at this
        cases hl : U.lookup (G.Γ.n + k') with
        | none => rfl
        | some _ => simp [hl] at this
      · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
        cases u
        · rw [hlk i, hu] at hO
          cases hr : R.lookup i with
          | none => simp [Uses.merge, hr] at hO
          | some v =>
            cases v
            · simp [Uses.merge, hr] at hO
            · have := (hfree i).2 hr; rw [hu] at this; cases this
        · exact hu
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨U', K', hU', hsub, hmany, hsib, htrue⟩ := usesFns_spec Fs R KR hR k F' hk
      refine ⟨U', K', hU', ⟨fun i h => sR.1 i (hsub.1 i h), fun i h => sR.2 i (hsub.2 i h)⟩, hmany, hsib,
        fun i hO hi => htrue i ?_ hi⟩
      have hRi := hsub.1 i hi
      rw [hlk i] at hO
      cases ha : (UR.below (U, K0) G.Γ.n).1.lookup i with
      | none => simp only [UR.below] at ha; simpa [Uses.merge, ha] using hO
      | some a =>
        cases a
        · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hRi
          simp only [UR.below] at ha
          rw [ha, hv] at hO; simp [Uses.merge] at hO; subst hO; exact hv
        · simp only [UR.below] at ha
          have := (hfree i).1 ha; rw [this] at hRi; cases hRi

end Minimal
