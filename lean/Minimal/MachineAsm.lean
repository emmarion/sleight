import Minimal.MachineRun

namespace Minimal

def Cert (P : Prog) (env : List Tm) (gid : Nat) : Prop :=
  ∃ (Gd : UCtx) (Gr : Group) (O : Uses) (K : Caps), P.groups[gid]? = some Gr ∧ EnvOK P env Gd.Γ ∧
    GroupOK P gid Gd.Γ Gr ∧ Gd.fill = false ∧ Gd.Γ.ghost = false ∧ (∀ j, Gd.uq.contains j = true → j < Gd.Γ.n) ∧
    usesFns P gid Gd Gr Gr.fns = some (O, K) ∧ Gd.defOK Gr O = true

def CloOK (P : Prog) : Tm → Prop
  | .clo env gid _ => (∀ Gr, P.groups[gid]? = some Gr → Gr.ghost = false → Cert P env.toList gid) ∧ CloOK P env
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

theorem Uses.sub_spec {A B : Uses} (h : Uses.sub A B = true) {i : Nat} {u : Bool} (hA : A.lookup i = some u) :
    ∃ v, B.lookup i = some v ∧ (u = true → v = true) := by
  have := List.all_eq_true.mp h _ (lookup_mem hA)
  simp only at this
  cases hB : B.lookup i with
  | none => simp [hB] at this
  | some v => refine ⟨v, rfl, fun hu => ?_⟩; subst hu; simpa [hB] using this

theorem cert_body {gid j : Nat} {Gd : UCtx} {Gr : Group} {F : FnDef} {O : Uses} {K : Caps}
    (hGr : P.groups[gid]? = some Gr) (hF : Gr.fns[j]? = some F) (hdn : F.dele = none)
    (hfill : Gd.fill = false) (huq : ∀ j, Gd.uq.contains j = true → j < Gd.Γ.n)
    (hbn : (Gd.Γ.body Gr F).1.n = Gd.Γ.n + Gr.fns.length + F.np)
    (hus : usesFns P gid Gd Gr Gr.fns = some (O, K)) (hok : Gd.defOK Gr O = true) :
    ∃ Ub Kb, usesCore P gid (Gd.fnCtx Gr F) ((teleUs F.tele).drop F.np) (Gd.Γ.body Gr F).2 F.body = some (Ub, Kb) ∧
      (∀ i < Gd.Γ.n, (Ub.lookup i).isSome → P.rd gid j i = true) ∧
      (∀ i < Gd.Γ.n, Ub.lookup i = some true → P.rdU gid j i = true) ∧
      (∀ k < Gr.fns.length, (Ub.lookup (Gd.Γ.n + k)).isSome →
        (Gr.fns[k]?.map (·.u)) = some false ∧ Ub.lookup (Gd.Γ.n + k) ≠ some true) ∧
      (∀ k < F.np, Ub.lookup (Gd.Γ.n + Gr.fns.length + k) = some true → (teleUs F.tele).getD k false = true) := by
  obtain ⟨Ub, Kb, hUb, hsub, hmany, hsib, htrue⟩ := usesFns_spec Gr.fns O K hus j F hF
  simp only [UCtx.defOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hOC, hCO⟩, -⟩, -⟩, -⟩ := hok
  have huqOK := usesCore_uq gid (Gd.fnCtx Gr F) _ _ F.body (by simp [UCtx.fnCtx, hfill]) Ub Kb hUb
  have hbl : ∀ i, i < Gd.Γ.n → (Ub.below Gd.Γ.n).lookup i = Ub.lookup i := fun i hi => Uses.below_lookup hi
  have hFu : (∃ i, (Ub.below Gd.Γ.n).lookup i = some true) → F.u = true := fun ⟨i, hi⟩ => by
    cases hu : F.u
    · exact absurd hi (hmany hu i)
    · rfl
  have hfnU : F.u = true → P.fnU gid j = true := fun hu => by simp [Prog.fnU, hGr, hF, hu, hdn]
  have huqc : ∀ i, (i, true) ∈ Ub → (Gd.uq.contains i = true ∨
      ∃ k, k < F.np ∧ (teleUs F.tele).getD k false = true ∧ i = Gd.Γ.n + Gr.fns.length + k) ∨
      Gd.Γ.n + Gr.fns.length + F.np ≤ i := fun i hi => by
    rcases huqOK i hi with h | h
    · simp only [UCtx.fnCtx, List.contains_append, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl (.inl h)
      · simp only [List.contains_iff_mem, List.mem_filterMap, Prod.exists] at h
        obtain ⟨u, k, hm, he⟩ := h
        split at he
        · rename_i hu
          simp only [Option.some.injEq] at he; subst he
          have hk := (List.mem_zipIdx' hm)
          have hlt : k < F.np := by simp at hk; omega
          refine .inl (.inr ⟨k, hlt, ?_, rfl⟩)
          have := List.getElem?_eq_some_iff.mpr ⟨hk.1, hk.2.symm⟩
          simp only [List.getElem?_take, hlt, ite_true] at this
          simp [List.getD_eq_getElem?_getD, this, hu]
        · cases he
    · simp only [UCtx.fnCtx, hbn] at h; exact .inr h
  refine ⟨Ub, Kb, hUb, fun i hi h => ?_, fun i hi h => ?_, fun k hk h => ?_, fun k hk h => ?_⟩
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨uO, hO⟩ := Option.isSome_iff_exists.mp (hsub.1 i (by rw [hbl i hi, hu]; rfl))
    obtain ⟨v, hv, -⟩ := Uses.sub_spec hOC hO
    simp only [Prog.rd, hGr, Option.map_some, Option.getD_some, hv, Option.any_some, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    cases v
    · exact .inl rfl
    · obtain ⟨v', hv', hvv⟩ := Uses.sub_spec hCO hv
      rw [hO] at hv'; cases hv'
      have := htrue i (by rw [hO, hvv rfl]) (by rw [hbl i hi, hu]; rfl)
      exact .inr (hfnU (hFu ⟨i, this⟩))
  · have hb : (Ub.below Gd.Γ.n).lookup i = some true := by rw [hbl i hi, h]
    obtain ⟨v, hv, hvv⟩ := Uses.sub_spec hOC (hsub.2 i hb)
    simp [Prog.rdU, hGr, hfnU (hFu ⟨i, hb⟩), hv, hvv rfl]
  · constructor
    · cases hFk : Gr.fns[k]? with
      | none => simp at hFk; omega
      | some F' =>
        cases hu : F'.u
        · simp [hu]
        · rw [hsib k F' hFk hu] at h; cases h
    · intro ht
      rcases huqc _ (lookup_mem ht) with (h1 | ⟨k', hk', -, he⟩) | h1
      · have := huq _ h1; omega
      · omega
      · omega
  · rcases huqc _ (lookup_mem h) with (h1 | ⟨k', hk', hu, he⟩) | h1
    · have := huq _ h1; omega
    · have : k' = k := by omega
      subst this; exact hu
    · omega

theorem CloOK.ofList : ∀ {l : List Tm}, (∀ v ∈ l, CloOK P v) → CloOK P (Tm.ofList l)
  | [], _ => trivial
  | v :: l, h => ⟨h v (by simp), CloOK.ofList fun w hw => h w (by simp [hw])⟩

theorem CloOK.toList : ∀ {t : Tm}, CloOK P t → ∀ v ∈ t.toList, CloOK P v
  | .cons a b, h, v, hv => by
    simp only [Tm.toList, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.1
    · exact CloOK.toList h.2 v hv
  | .nil, _, v, hv | .fv _, _, v, hv | .bv _, _, v, hv | .bind .., _, v, hv | .app .., _, v, hv | .tyc .., _, v, hv
  | .vc .., _, v, hv | .tyCtor _, _, v, hv | .valCtor _, _, v, hv | .univ, _, v, hv | .level, _, v, hv
  | .predates .., _, v, hv | .subterm .., _, v, hv | .fn .., _, v, hv | .mtbl .., _, v, hv | .lvl _, _, v, hv
  | .tok, _, v, hv | .clo .., _, v, hv | .nat _, _, v, hv | .ptr _, _, v, hv => by simp [Tm.toList] at hv

theorem CloOK.env {ρ : List Tm} (h : ∀ v ∈ ρ, CloOK P v) (i : Nat) : CloOK P (Tm.env ρ i) := by
  unfold Tm.env
  rw [List.getD_eq_getElem?_getD]
  cases hi : ρ[i]? with
  | none => trivial
  | some v => exact h v (List.mem_of_getElem? hi)

theorem CloOK.defFns {G : UCtx} {ρ : List Tm} {gid : Nat} {Gr : Group}
    (hE : EnvOK P ρ G.Γ) (hGr : P.groups[gid]? = some Gr) (hok : GroupOK P gid G.Γ Gr) (hf : G.fill = false)
    (hus : G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧ ∃ O K, usesFns P gid G Gr Gr.fns = some (O, K) ∧
      G.defOK Gr O = true) (hC : ∀ v ∈ ρ, CloOK P v) :
    ∀ v ∈ closures ρ gid Gr, CloOK P v := by
  intro v hv
  simp only [closures, List.mem_map] at hv
  obtain ⟨k, -, rfl⟩ := hv
  refine ⟨fun Gr' hGr' hgr => ?_, CloOK.ofList hC⟩
  rw [hGr] at hGr'; cases hGr'
  have hg : G.Γ.ghost = false := by cases hok with | mk _ _ _ _ _ _ hgg _ => rw [hgg]; exact hgr
  obtain ⟨huq, O, K, hus, hd⟩ := hus hg
  rw [Tm.toList_ofList]; exact ⟨G, Gr, O, K, hGr, hE, hok, hf, hg, huq, hus, hd⟩

theorem Tm.noClo_toList : ∀ {t : Tm}, t.noClo = true → ∀ x ∈ t.toList, x.noClo = true
  | .cons a b, h, x, hx => by
    simp only [Tm.noClo, Bool.and_eq_true] at h
    simp only [Tm.toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact Tm.noClo_toList h.2 x hx
  | .nil, _, x, hx | .fv _, _, x, hx | .bv _, _, x, hx | .bind .., _, x, hx | .app .., _, x, hx | .tyc .., _, x, hx
  | .vc .., _, x, hx | .tyCtor _, _, x, hx | .valCtor _, _, x, hx | .univ, _, x, hx | .level, _, x, hx
  | .predates .., _, x, hx | .subterm .., _, x, hx | .fn .., _, x, hx | .mtbl .., _, x, hx | .lvl _, _, x, hx
  | .tok, _, x, hx | .clo .., _, x, hx | .nat _, _, x, hx | .ptr _, _, x, hx => by simp [Tm.toList] at hx

theorem CloOK.subst_list {ρ : List Tm} (hC : ∀ v ∈ ρ, CloOK P v) {ts : Tm} (h : ts.noClo = true) :
    ∀ v ∈ ts.toList.map (·.subst (Tm.env ρ)), CloOK P v := by
  intro v hv
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
  exact CloOK.subst (CloOK.env hC) t (Tm.noClo_toList h t ht)

theorem MRun.of_ghost {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {c : Core} {ρ vs : List Tm}
    (hg : G.Γ.ghost = true) : MRun P b G ru rets c ρ vs :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG => absurd hG.ghost (by simp [hg])

theorem UCtx.next_uqlt {G : UCtx} {Γ' : Ctx} {us : List Bool} (huq : ∀ j, G.uq.contains j = true → j < G.Γ.n)
    (hn : G.Γ.n ≤ Γ'.n) : ∀ j, (G.next Γ' us).uq.contains j = true → j < (G.next Γ' us).Γ.n := by
  intro j hj
  simp only [UCtx.next, List.contains_append, Bool.or_eq_true] at hj
  simp only [UCtx.next]
  rcases hj with hj | hj
  · have := huq j hj; omega
  · simp at hj
    obtain ⟨k, hk, e⟩ := hj
    have := (List.mem_zipIdx' hk).1
    simp only [List.length_take] at this
    omega

theorem usesCore_defFns {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {gid : Nat} {rest : Core} {Gr : Group}
    (hGr : P.groups[gid]? = some Gr) (hf : G.fill = false) {U : Uses} {K : Caps}
    (h : usesCore P b G ru rets (.defFns gid rest) = some (U, K)) :
    ∃ O K', usesFns P gid G Gr Gr.fns = some (O, K') ∧ G.defOK Gr O = true ∧
      (usesCore P b (G.next (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)) (if G.Γ.ghost then [] else Gr.fns.map (·.u)))
        ru rets rest).isSome := by
  rw [usesCore] at h
  simp only [hGr, Option.bind_eq_bind, Option.bind_some, hf, Bool.false_eq_true, ite_false] at h
  obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  case isFalse => cases h
  obtain ⟨⟨O, K'⟩, hO, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  case isFalse => cases h
  rename_i _ hd
  exact ⟨O, K', hO, hd, by rw [hC]; rfl⟩

theorem Except.bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem Pend.split (pd : Pend) (p : Prim) : Pend.Inert P pd p ∨ (∃ y A', pd = some (.alloc, y) ∧ p = .axm A') ∨
    (∃ m t A', (m = .cellOf ∨ m = .write true) ∧ pd = some (m, t) ∧ p = .axm A') ∨
    ∃ x t, pd = some (.reuse true, .fv x) ∧ p = .tm t := by
  rcases pd with _ | ⟨m, t⟩
  · exact .inl fun _ _ => rfl
  · cases m <;> (try rename_i bb; cases bb) <;> cases p <;> (try cases t) <;>
      first | exact .inl fun _ _ => rfl | simp

theorem machine_primF (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core}
    {ρ vs : List Tm} (hE : EnvOK P ρ G.Γ) (hrt : p.rt P G.Γ = true)
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P (p.evalS P ρS) (p.eval ρ)) (hval : PrimVal P G ρ p)
    (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim T false p) (.prim p false rest)) [G.ents.headD false]) ru rets rest
        (ρ ++ [p.eval ρ]) vs) :
    MRun P b G ru rets (.prim p false rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  rcases Pend.split (P := P) pd p with hin | ⟨y, A', rfl, rfl⟩ | ⟨m, t, A', hm, rfl, rfl⟩ | ⟨x, t, rfl, rfl⟩
  · exact machine_prim_inert hreal ih hval U K hU ρS vsS hS hrun H ρM Res Out Shr pd hin hM hG
  · exact machine_prim_alloc hreal ih U K hU ρS vsS hS hrun H ρM Res Out Shr hM hG
  · exact machine_prim_cell hm hreal ih U K hU ρS vsS hS hrun H ρM Res Out Shr hM hG
  · exact machine_prim_reuse hP hE (by simpa [Prim.rt] using hrt) hreal ih U K hU ρS vsS hS hrun H ρM Res Out Shr hM hG

theorem natTm'_cloOK (d : Nat) : ∀ n, CloOK P (natTm' d n)
  | 0 => by simp [natTm', CloOK]
  | k + 1 => by simp [natTm', CloOK, natTm'_cloOK d k]

theorem PrimTy.cloOK {Γ : Ctx} {ρ : List Tm} {p : Prim} {T : Tm} (hp : PrimTy P Γ p T) (hC : ∀ v ∈ ρ, CloOK P v) :
    CloOK P (p.eval ρ) := by
  have hs := CloOK.subst (P := P) (CloOK.env hC)
  cases hp with
  | tm ht | lit ht => exact hs _ ht.noClo
  | coerce _ _ _ _ _ hb => exact hs _ hb.noClo
  | assert _ h0 => rw [Prim.eval, ← Tm.subst_static0 (Tm.env ρ) _ 0 h0]; exact hs _ (Tm.noClo_static _ 0 0 h0)
  | num => exact natTm'_cloOK _ _
  | _ => simp [Prim.eval, CloOK]

theorem UCtx.primTy_check {G : UCtx} {p : Prim} {T : Tm} {hp : PrimTy P G.Γ p T}
    (h : checkPrim P G.Γ p = .ok ⟨T, hp⟩) : G.primTy P p = some T := by
  unfold UCtx.primTy; split
  · cases hp; rfl
  · rw [h]

def CoerceVal (P : Prog) : Prop := ∀ (G : UCtx) ρ a b q T, EnvOK P ρ G.Γ → PrimTy P G.Γ (.coerce a b q) T →
  (Prim.coerce a b q).rt P G.Γ = true → PrimVal P G ρ (.coerce a b q)
theorem checkCore_opn {b : Nat} {Γ : Ctx} {oe : Bool} {m : Nat} {x : Tm} {rest : Core} {rs : Tm ⊕ Nat} {rets : Tm} {h}
    (hck : checkCore P b Γ (.chk (.opn oe) (.fv m) x rest) rs = .ok ⟨rets, h⟩) :
    (∃ M u nt ex ph H cs, Γ.tys[m]? = some M ∧ Γ.canon M = .mtbl u nt ex ph H cs ∧ (¬ cs.toList.Nodup ∨
      unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .contra)) ∨
    ∃ u nt ex ph H cs σ' h', (Γ.tys[m]?).map Γ.canon = some (.mtbl u nt ex ph H cs) ∧
      unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .ok σ' ∧
      checkCore P b { Γ with opened := (m, oe) :: Γ.opened, σ := σ' } rest rs = .ok ⟨rets, h'⟩ := by
  cases rs <;> (first | rw [checkCore.eq_13] at hck | rw [checkCore.eq_14] at hck)
  all_goals split at hck <;> try cases hck
  all_goals split at hck <;> try cases hck
  all_goals rename_i M hM u nt ex ph H cs hc
  all_goals cases rest
  all_goals try dsimp only at hck
  all_goals first
    | (obtain ⟨⟨hn⟩, -, hck⟩ := Except.bind_ok hck
       try dsimp only at hck
       split at hck
       · obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
         cases hck
         exact .inr ⟨u, nt, ex, ph, H, cs, _, _, by simp [hM, hc], ‹_›, hr'⟩
       all_goals cases hck)
    | (split at hck
       · split at hck
         · exact .inl ⟨M, u, nt, ex, ph, H, cs, hM, hc, .inr ‹_›⟩
         · cases hck
       · exact .inl ⟨M, u, nt, ex, ph, H, cs, hM, hc, .inl ‹_›⟩)

theorem checkBranches_live {b : Nat} {Γ : Ctx} {fe : Bool} {g : Bool → Bool} {s H idx R0 : Tm} {brs : List Br}
    {els : Bool} : ∀ arms base r, checkBranches P b Γ fe g s H idx R0 brs els arms base = .ok r →
    ∀ c k sig p body, arms[c]? = some (k, sig, p) → lookupBr brs (base + c) = some body → body = .dead ∨
    ∃ Γf σ h', ({ Γ with ghost := g p } : Ctx).branch P s k H idx sig = (Γf, .ok σ) ∧
      checkCore P b { ({ Γ with ghost := g p } : Ctx).advBr P (({ Γ with ghost := g p } : Ctx).setErs { Γf with σ := σ }
        (if fe then some (List.replicate (sig.len - 1) true) else none)) s k fe (sig.len - 1) with cmode := false }
        body (.inl R0) = .ok ⟨R0, h'⟩
  | [], _, _, _, c, k, sig, p, body, ha, _ => by simp at ha
  | (k0, sig0, p0) :: cs, base, r, h, c, k, sig, p, body, ha, hl => by
    rw [checkBranches] at h
    obtain ⟨⟨hh⟩, hm, h⟩ := Except.bind_ok h
    obtain ⟨⟨ht⟩, hr, -⟩ := Except.bind_ok h
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      simp only [Nat.add_zero] at hl
      clear h ht hr
      revert hh hm hl
      generalize lookupBr brs base = o
      intro hh hm hl
      split at hm
      · exact .inl (Option.some.inj hl).symm
      · cases hl
        split at hm
        · obtain ⟨⟨R, hr2, e⟩, hc, -⟩ := Except.bind_ok hm
          have := e.1 R0 rfl; subst this
          exact .inr ⟨_, _, _, ‹_›, hc⟩
        all_goals cases hm
      · cases hl
    | succ c =>
      exact checkBranches_live cs (base + 1) _ hr c k sig p body (by simpa using ha)
        (by rwa [show base + 1 + c = base + (c + 1) by omega])

def MSound (P : Prog) (μ : Option (List Nat)) (ρ : List Tm) (cnt : Nat) (c : Core) : Prop :=
  ∀ b (G : UCtx) (Γ : Ctx) ru rs rets h, G.fill = false →
    G.Γ = Γ → checkCore P b Γ c rs = .ok ⟨rets, h⟩ → EnvOK P ρ Γ → LvlBound ρ cnt → MuOK μ Γ ρ → rets.static Γ.n 0 →
    (∀ v ∈ ρ, CloOK P v) →
    ∀ vs cnt', eval P μ ρ cnt c = .ok (vs, cnt') →
    MRun P b G ru rets c ρ vs ∧ ((G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
      (usesCore P b G ru rets c).isSome = true) → ∀ v ∈ vs, CloOK P v)

theorem MSound.ret (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {ts : Tm}
     :
    MSound P μ ρ cnt (.ret ts) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [eval] at h; cases h
  cases hh.1 with
  | ret ha hok =>
  refine ⟨fun U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG => ?_, fun _ => CloOK.subst_list hC (ArgsTy.noClo ha)⟩
  rw [usesCore] at hU
  simp only [hG.ghost, Bool.false_eq_true, ite_false, UR.lift, Option.map_eq_some_iff, Prod.mk.injEq] at hU
  obtain ⟨U', hU', rfl, -⟩ := hU
  simp only [Ctx.ok, hG.ghost, Bool.false_or] at hok
  cases hrun with
  | ret => exact machine_ret hP hok hE hS rfl hU' hM pd

theorem MSound.seq (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {R : Tm} {body rest : Core} {outs : List Tm} {cnt1 : Nat}
    (hev : eval P μ ρ cnt body = .ok (outs, cnt1)) (ihb : MSound P μ ρ cnt body) (ihr : MSound P μ (ρ ++ outs) cnt1 rest) :
    MSound P μ ρ cnt (.seq R body rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [checkCore] at hck
  obtain ⟨⟨_⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hRs⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hRt⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨R1, hb, e⟩, hb', hck⟩ := Except.bind_ok hck
  obtain ⟨⟨R2, hr, e2⟩, hr', hck⟩ := Except.bind_ok hck
  cases hck
  have eR : R1 = R := e.1 R rfl
  subst R1
  rw [eval] at h; simp only [hev] at h
  have hres := eval_sound hP μ ρ cnt body b G.Γ R hb hE hlb hm hRs
  obtain ⟨hE', hlb', hm', hrs', -, -, hol⟩ := seq_setup hE hlb hm hrs hRs hRt hres hev
  have ihb' := ihb b { G with ents := [], uscr := none, cellOk := false, rebind := none } G.Γ G.ents (.inl R) R _ hf rfl hb' hE
    hlb hm hRs hC outs cnt1 hev
  have hΓ : (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents)).Γ =
      Ctx.adv P G.Γ (G.Γ.pushTele R) (.seq R body rest) := by simp [UCtx.next, UCtx.adv, hf]
  have ihr' := fun hCo => ihr b (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents))
    _ ru rs rets _ hf hΓ hr' hE' hlb' hm' hrs' hCo vs cnt' h
  have hsplit : ∀ U K, usesCore P b G ru rets (.seq R body rest) = some (U, K) →
      (usesCore P b { G with ents := [], uscr := none, cellOk := false, rebind := none } G.ents R body).isSome ∧
      (usesCore P b (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents))
        ru rets rest).isSome := fun U K hU => by
    rw [usesCore] at hU
    obtain ⟨⟨BU, BK⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
    obtain ⟨⟨CU, CK⟩, hC', -⟩ := Option.bind_eq_some_iff.mp hU
    exact ⟨by rw [hB]; rfl, by rw [hC']; rfl⟩
  have hn : G.Γ.n ≤ (G.adv P (G.Γ.pushTele R) (.seq R body rest)).n := by
    rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hRt]; omega
  have hCo : (G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
      (usesCore P b G ru rets (.seq R body rest)).isSome = true) → ∀ v ∈ ρ ++ outs, CloOK P v := fun hpre v hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact hC v hv
    · refine ihb'.2 (fun hg => ?_) v hv
      obtain ⟨huq, hus⟩ := hpre hg
      obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
      exact ⟨huq, (hsplit U K hU).1⟩
  refine ⟨fun U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG => ?_, fun hpre => ?_⟩
  · have hCo' := hCo fun _ => ⟨hG.uqlt, by rw [hU]; rfl⟩
    exact machine_seq hRt hol (fun ρS hS => hres.2 hG.ghost ρS hS outs cnt1 hev) ihb'.1 (ihr' hCo').1
      U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  · refine (ihr' (hCo hpre)).2 fun hg' => ?_
    have hg : G.Γ.ghost = false := by
      simpa only [UCtx.next, UCtx.adv_ghost' hf, (Ctx.pushTele_er G.Γ R none hRt).1] using hg'
    obtain ⟨huq, hus⟩ := hpre hg
    obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
    exact ⟨UCtx.next_uqlt huq hn, (hsplit U K hU).2⟩

theorem MSound.prim (hP : ProgOK P) (hco : CoerceVal P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {p : Prim} {er : Bool} {rest : Core}
    (ih : MSound P μ (ρ ++ [p.eval ρ]) cnt rest) :
    MSound P μ ρ cnt (.prim p er rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [checkCore] at hck
  obtain ⟨⟨T, hp⟩, hpe, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hok⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨R2, hr, e2⟩, hr', hck⟩ := Except.bind_ok hck
  cases hck
  rw [eval] at h
  obtain ⟨hE', hlb', hm', hrs', -, -⟩ := prim_setup (rest := rest) hP hE hlb hm hrs hp hok
  have hT := UCtx.primTy_check hpe
  have hΓ : ∀ us, (G.next (G.adv P (G.Γ.pushPrim T er p) (.prim p er rest)) us).Γ =
      Ctx.adv P G.Γ (G.Γ.pushPrim T er p) (.prim p er rest) := fun us => by simp [UCtx.next, UCtx.adv, hf]
  have hCo : ∀ v ∈ ρ ++ [p.eval ρ], CloOK P v := fun v hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact hC v hv
    · simp at hv; subst hv; exact hp.cloOK hC
  have ih' := fun us => ih b (G.next (G.adv P (G.Γ.pushPrim T er p) (.prim p er rest)) us) _ ru rs rets _ hf (hΓ us) hr'
    hE' hlb' hm' hrs' hCo vs cnt' h
  have hn : G.Γ.n ≤ (G.adv P (G.Γ.pushPrim T er p) (.prim p er rest)).n := by rw [UCtx.adv_n' hf, Ctx.pushPrim_n]; omega
  refine ⟨?_, fun hpre => ?_⟩
  · cases er
    · intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0
      have hrt : p.rt P G.Γ = true := by simpa [Ctx.ok, hG0.ghost] using hok
      have hval : PrimVal P G ρ p := by
        by_cases hc : ∃ a b q, p = .coerce a b q
        · obtain ⟨a, b, q, rfl⟩ := hc; exact hco G ρ a b q T hE hp hrt
        · exact prim_val hP hE hrt fun a b q e => hc ⟨a, b, q, e⟩
      exact machine_primF hP hE hrt (fun ρS hS => prim_real hP hE hS hp hrt) hval
        (fun T' hT' => by rw [hT] at hT'; cases hT'; exact (ih' _).1) U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0
    · exact machine_primE (v := p.eval ρ) fun T' hT' => by rw [hT] at hT'; cases hT'; exact (ih' []).1
  · refine (ih' (if er || G.Γ.ghost then [] else [G.ents.headD false])).2 fun hg' => ?_
    have hg : G.Γ.ghost = false := by simpa only [UCtx.next, UCtx.adv_ghost' hf, Ctx.pushPrim_ghost] using hg'
    obtain ⟨huq, hus⟩ := hpre hg
    obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
    rw [usesCore] at hU
    obtain ⟨T', hT', hU⟩ := Option.bind_eq_some_iff.mp hU
    rw [hT] at hT'; cases hT'
    simp only at hU
    obtain ⟨⟨CU, CK⟩, hC', -⟩ := Option.bind_eq_some_iff.mp hU
    exact ⟨UCtx.next_uqlt huq hn, by rw [hC']; rfl⟩

theorem MSound.defLvl {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {rest : Core}
    (ih : MSound P μ (ρ ++ [.lvl cnt]) (cnt + 1) rest) :
    MSound P μ ρ cnt (.defLvl rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [checkCore] at hck
  obtain ⟨⟨R2, hr, e2⟩, hr', hck⟩ := Except.bind_ok hck
  cases hck
  rw [eval] at h
  have hl := hE.len
  have hh : HeadSim P G.Γ G.Γ.pushMint ρ [.lvl cnt] (.defLvl rest) rest := by
    intro ρS hg hS
    refine ⟨[.tok], fun vs' h => by simp [stepS] at h; exact h.symm, fun out h => .defLvl h, rfl,
      fun k a b ha hb _ => ?_⟩
    cases k with
    | succ => simp at ha
    | zero => simp at ha hb; subst ha hb; exact .other (by simp) (by simp) (by simp)
  have hΓ : (G.next (G.adv P G.Γ.pushMint (.defLvl rest)) []).Γ = Ctx.adv P G.Γ G.Γ.pushMint (.defLvl rest) := by
    simp [UCtx.next, UCtx.adv, hf]
  have ih' := ih b (G.next (G.adv P G.Γ.pushMint (.defLvl rest)) []) _ ru rs rets _ hf hΓ hr'
    (hE.adv (hE.pushMint hlb) rfl hh) (LvlBound.append.mpr ⟨hlb.mono (Nat.le_succ _), by simp [LvlBound, Tm.levels]⟩)
    (hm.append hE.wf hl (by simp [Ctx.pushMint, Ctx.push]) (by simp [Ctx.pushMint, Ctx.push]))
    (Tm.static_mono (by simp [Ctx.pushMint, Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hrs)
    (fun v hv => by rcases List.mem_append.mp hv with hv | hv
                    · exact hC v hv
                    · simp at hv; subst hv; trivial) vs cnt' h
  refine ⟨machine_defLvl ih'.1, fun hpre => ih'.2 fun hg' => ?_⟩
  obtain ⟨huq, hus⟩ := hpre (by simpa [UCtx.next, UCtx.adv_ghost' hf, Ctx.pushMint, Ctx.push] using hg')
  refine ⟨UCtx.next_uqlt huq ?_, by rw [usesCore] at hus; exact hus⟩
  rw [UCtx.adv_n' hf]; simp [Ctx.pushMint, Ctx.push, Ctx.n]

theorem MSound.defFns (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt gid : Nat} {rest : Core} {Gr : Group}
    (hG : P.groups[gid]? = some Gr) (ih : MSound P μ (ρ ++ closures ρ gid Gr) cnt rest) :
    MSound P μ ρ cnt (.defFns gid rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [checkCore] at hck
  obtain ⟨⟨_⟩, -, hck⟩ := Except.bind_ok hck
  split at hck
  split at hck
  rotate_left; · cases hck
  rename_i Gr' hG'
  rw [hG] at hG'; cases hG'
  obtain ⟨⟨hok⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨R2, hr, e2⟩, hr', hck⟩ := Except.bind_ok hck
  cases hck
  rw [eval, hG] at h
  have hl := hE.len
  have hh : HeadSim P G.Γ (G.Γ.pushFns Gr) ρ (closures ρ gid Gr) (.defFns gid rest) rest := by
    intro ρS hg hS
    cases hok with
    | mk _ _ _ _ _ hGe hGg hd =>
    refine ⟨closuresS ρS gid Gr, fun vs' h => by simp [stepS, hG] at h; exact h.symm, fun out h => .defFns hG h,
      by simp [closures, closuresS_length], fun k a b ha hb he => ?_⟩
    obtain ⟨hk, -⟩ := closures_get hb
    obtain ⟨Fk, hFk⟩ : ∃ Fk, Gr.fns[k]? = some Fk := ⟨_, List.getElem?_eq_getElem hk⟩
    simp only [Ctx.pushFns] at he
    rw [if_pos (by omega), show G.Γ.n + k - G.Γ.n = k by omega, hFk] at he
    refine closuresS_real hG (by rw [← hGg, hg]) (by rw [hl]; exact hd) (by rw [hS.1]) (fun i hi => ?_) k a b Fk hFk
      (by simpa using he) ha hb
    by_cases hin : i < G.Γ.n
    · rw [← hGe i hin] at hi; exact hS.2 i hi
    · have : Tm.env ρ i = .nil := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ρ.length ≤ i by omega)]
      rw [this]; exact Real.nil' _
  have hΓ : ∀ us, (G.next (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)) us).Γ =
      Ctx.adv P G.Γ (G.Γ.pushFns Gr) (.defFns gid rest) := fun us => by simp [UCtx.next, UCtx.adv, hf]
  have ih' := fun us hCo => ih b (G.next (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)) us) _ ru rs rets _ hf
    (hΓ us) hr' (hE.adv (hE.pushFns hP hG hok) rfl hh)
    (LvlBound.append.mpr ⟨hlb, fun v hv x hx => by
      simp only [closures, List.mem_map] at hv
      obtain ⟨j, _, rfl⟩ := hv
      obtain ⟨w, hw, hx'⟩ := Tm.levels_ofList ρ x (by simpa [Tm.levels] using hx)
      exact hlb w hw x hx'⟩)
    (hm.append hE.wf hl (by simp [Ctx.pushFns]) (by simp [Ctx.pushFns]))
    (Tm.static_mono (by simp [Ctx.pushFns, Ctx.n]) _ (Nat.le_refl 0) hrs) hCo vs cnt' h
  have hCo : (G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
      (usesCore P b G ru rets (.defFns gid rest)).isSome = true) → ∀ v ∈ ρ ++ closures ρ gid Gr, CloOK P v :=
    fun hpre v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact hC v hv
      · refine CloOK.defFns hE hG hok hf (fun hg => ?_) hC v hv
        obtain ⟨huq, hus⟩ := hpre hg
        obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
        obtain ⟨O, K', hO, hd, -⟩ := usesCore_defFns hG hf hU
        exact ⟨huq, O, K', hO, hd⟩
  have hdk : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.dele = some t → t < G.Γ.n + k :=
    fun k F t hF hd => by
      cases hok with
      | mk _ _ _ _ _ _ _ hdo => have := (Group.deleOK_spec hdo hF hd).1; omega
  have hn : G.Γ.n ≤ (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)).n := by
    rw [UCtx.adv_n' hf]; simp [Ctx.pushFns, Ctx.n]
  refine ⟨fun U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0 => ?_, fun hpre => ?_⟩
  · have hg := hG0.ghost
    have hCo' := hCo fun _ => ⟨hG0.uqlt, by rw [hU]; rfl⟩
    have ih'' := ih' (if G.Γ.ghost then [] else Gr.fns.map (·.u)) hCo'
    simp only [hg, Bool.false_eq_true, ite_false] at ih''
    refine machine_defFns hG hdk (fun ρS hS => ?_) ih''.1 U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0
    obtain ⟨outsS, hst, -, hlen, hre⟩ := hh ρS hg hS
    have : outsS = closuresS ρS gid Gr := (hst _ (by simp [stepS, hG])).symm
    subst this
    refine hS.extend (by rw [hlen]) (fun i hi => ?_) fun k a b ha hb he => hre k a b ha hb ?_
    · rw [UCtx.adv_er' hf]; simp only [Ctx.pushFns]; rw [if_neg (by omega)]
    · rw [UCtx.adv_er' hf, hl] at he; exact he
  · refine (ih' (if G.Γ.ghost then [] else Gr.fns.map (·.u)) (hCo hpre)).2 fun hg' => ?_
    obtain ⟨huq, hus⟩ := hpre (by simpa [UCtx.next, UCtx.adv_ghost' hf, Ctx.pushFns] using hg')
    obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨O, K', hO, hd, hrest⟩ := usesCore_defFns hG hf hU
    exact ⟨UCtx.next_uqlt huq hn, hrest⟩

theorem MSound.chk (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {k : Chk} {a e : Tm} {rest : Core}
    (ih : MSound P μ ρ cnt rest ∧ ∀ p r, rest = .prim p false r → MSound P μ (ρ ++ [p.eval ρ]) cnt r) :
    MSound P μ ρ cnt (.chk k a e rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs cnt' h
  subst hGΓ
  rw [eval] at h
  have step : ∀ (G' : UCtx) h', G'.fill = false → checkCore P b G'.Γ rest rs = .ok ⟨rets, h'⟩ → EnvOK P ρ G'.Γ →
      G'.Γ.cur = G.Γ.cur → G'.Γ.subs = G.Γ.subs → G'.Γ.n = G.Γ.n → G'.Γ.ghost = G.Γ.ghost → G'.uq = G.uq →
      (MRun P b G' ru rets rest ρ vs → MRun P b G ru rets (.chk k a e rest) ρ vs) →
      (∀ U K, usesCore P b G ru rets (.chk k a e rest) = some (U, K) → (usesCore P b G' ru rets rest).isSome = true) →
      MRun P b G ru rets (.chk k a e rest) ρ vs ∧ ((G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
        (usesCore P b G ru rets (.chk k a e rest)).isSome = true) → ∀ v ∈ vs, CloOK P v) :=
    fun G' h' hf' hck' hE' hc hs hn hg hu hrun hus => by
      have ih' := ih.1 b G' G'.Γ ru rs rets h' hf' rfl hck' hE' hlb (by unfold MuOK at hm ⊢; rw [hc, hs]; exact hm)
        (hn ▸ hrs) hC vs cnt' h
      refine ⟨hrun ih'.1, fun hpre => ih'.2 fun hg0 => ?_⟩
      obtain ⟨huq, hus0⟩ := hpre (hg.symm.trans hg0)
      obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus0
      exact ⟨by rw [hn, hu]; exact huq, hus U K hU⟩
  have same : ∀ (G' : UCtx), G'.fill = false → G'.Γ = G.Γ → G'.uq = G.uq → ∀ h', checkCore P b G.Γ rest rs = .ok ⟨rets, h'⟩ →
      (MRun P b G' ru rets rest ρ vs → MRun P b G ru rets (.chk k a e rest) ρ vs) →
      (∀ U K, usesCore P b G ru rets (.chk k a e rest) = some (U, K) → (usesCore P b G' ru rets rest).isSome = true) →
      MRun P b G ru rets (.chk k a e rest) ρ vs ∧ ((G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
        (usesCore P b G ru rets (.chk k a e rest)).isSome = true) → ∀ v ∈ vs, CloOK P v) :=
    fun G' hf' hΓ hu h' hck' => by
      cases G'; simp only at hΓ; subst hΓ; exact step _ h' hf' hck' hE rfl rfl rfl rfl hu
  have isS : ∀ {o : Option (Uses × Caps)} {U K}, o = some (U, K) → o.isSome = true := fun h => by rw [h]; rfl
  cases k with
  | mark m =>
    rw [checkCore] at hck
    obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
    cases hck
    cases m with
    | uq ms => exact same { G with ents := ms } hf rfl rfl _ hr' machine_uq (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
    | uqScr => exact same { G with scr := true } hf rfl rfl _ hr' machine_uqScr (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
    | skip => exact same G hf rfl rfl _ hr' machine_skip (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
    | alloc =>
      exact same { G with cellOk := true } hf rfl rfl _ hr' machine_alloc
        (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
    | cellOf =>
      exact same { G with cellOk := true, uscr := none } hf rfl rfl _ hr' machine_cellOf
        (fun U K hU => by rw [usesCore] at hU; split at hU; exact isS hU; cases hU)
    | reuse u | write u =>
      by_cases ha : ∃ i, a = .fv i
      · obtain ⟨i, rfl⟩ := ha
        refine same { G with cellOk := true } hf rfl rfl _ hr' (fun ihr => ?_) (fun U K hU => ?_)
        · cases u
          · exact machine_markMany (by simp) ihr
          · exact machine_markU hP (by simp) hE ihr
        · rw [usesCore] at hU
          split at hU
          · cases hU
          · obtain ⟨⟨CU, CK⟩, hC', -⟩ := Option.bind_eq_some_iff.mp hU
            exact isS hC'
      · have ha' : ∀ i, a ≠ .fv i := fun i e => ha ⟨i, e⟩
        refine same G hf rfl rfl _ hr' (fun ihr => ?_)
          (fun U K hU => by rw [usesCore_markNF (by first | exact .inl rfl | exact .inr rfl) ha'] at hU; exact isS hU)
        cases u
        · exact machine_chkSame (fun m e => by cases e; rfl)
            (fun U K hU => by rw [usesCore_markNF (by first | exact .inl rfl | exact .inr rfl) ha'] at hU; exact hU) ihr
        · exact machine_markNF (by simp) ha' ihr
    | rebind =>
      by_cases hx : ∃ t rest', rest = .prim (.tm t) false rest' ∧ G.rebind = some t
      · obtain ⟨t, rest', rfl, hrb⟩ := hx
        rw [checkCore] at hr'
        obtain ⟨⟨T, hp⟩, hpe, hr'⟩ := Except.bind_ok hr'
        obtain ⟨⟨hok⟩, -, hr'⟩ := Except.bind_ok hr'
        obtain ⟨⟨R2, hr2, e2⟩, hr'', hr'⟩ := Except.bind_ok hr'
        cases hr'
        rw [eval] at h
        obtain ⟨hE', hlb', hm', hrs', -, -⟩ := prim_setup (rest := rest') hP hE hlb hm hrs hp hok
        have hT := UCtx.primTy_check hpe
        have hΓ : (G.next (G.adv P (G.Γ.pushPrim T false (.tm t)) (.prim (.tm t) false rest')) (G.ents.take 1)).Γ =
            Ctx.adv P G.Γ (G.Γ.pushPrim T false (.tm t)) (.prim (.tm t) false rest') := by simp [UCtx.next, UCtx.adv, hf]
        have hCo : ∀ v ∈ ρ ++ [(Prim.tm t).eval ρ], CloOK P v := fun v hv => by
          rcases List.mem_append.mp hv with hv | hv
          · exact hC v hv
          · simp at hv; subst hv; exact hp.cloOK hC
        have ih' := (ih.2 (.tm t) rest' rfl) b
          (G.next (G.adv P (G.Γ.pushPrim T false (.tm t)) (.prim (.tm t) false rest')) (G.ents.take 1)) _ ru rs rets _ hf hΓ hr'' hE' hlb' hm' hrs' hCo vs cnt' h
        have hn : G.Γ.n ≤ (G.adv P (G.Γ.pushPrim T false (.tm t)) (.prim (.tm t) false rest')).n := by
          rw [UCtx.adv_n' hf, Ctx.pushPrim_n]; omega
        refine ⟨fun U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0 => ?_, fun hpre => ?_⟩
        · have hrt : (Prim.tm t).rt P G.Γ = true := by simpa [Ctx.ok, hG0.ghost] using hok
          exact machine_rebind hrb (fun ρS hS => prim_real hP hE hS hp hrt)
            (fun T' hT' => by rw [hT] at hT'; cases hT'; exact ih'.1) U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG0
        · refine ih'.2 fun hg' => ?_
          obtain ⟨huq, hus⟩ := hpre (by simpa only [UCtx.next, UCtx.adv_ghost' hf, Ctx.pushPrim_ghost] using hg')
          obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
          rw [usesCore] at hU
          simp only [hrb, beq_self_eq_true, ite_true] at hU
          obtain ⟨T', hT', hU⟩ := Option.bind_eq_some_iff.mp hU
          rw [hT] at hT'; cases hT'
          exact ⟨UCtx.next_uqlt huq hn, isS hU⟩
      · have hne : ∀ t r', rest = .prim (.tm t) false r' → G.rebind ≠ some t := fun t r' e hrb => hx ⟨t, r', e, hrb⟩
        exact same G hf rfl rfl _ hr' (machine_rebindSkip hne) (fun U K hU => isS (usesCore_rebindSkip hne U K hU))
  | opn oe =>
    by_cases ha : ∃ i, a = .fv i
    · obtain ⟨x, rfl⟩ := ha
      rcases checkCore_opn hck with ⟨M, u, nt, ex, ph, H, cs, hM, hc, hfl⟩ | ⟨u, nt, ex, ph, H, cs, σ', h', hm', hu, hr'⟩
      · exact (hE.openFail hP hM hc hfl).elim
      · exact step { G with Γ := { G.Γ with opened := (x, oe) :: G.Γ.opened, σ := σ' } } h' hf hr' (hE.opened hP hu)
          rfl rfl rfl rfl rfl (machine_opn hm' hu)
          (fun U K hU => by rw [usesCore] at hU; simp only [hm', hu] at hU; exact isS hU)
    · rw [checkCore.eq_15 _ _ _ _ _ _ _ _ (fun m e => ha ⟨m, e⟩)] at hck; cases hck
  | cm =>
    rw [checkCore] at hck
    obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
    cases hck
    exact step { G with Γ := { G.Γ with cmode := true } } _ hf hr' (hE.congr _ rfl rfl rfl rfl rfl) rfl rfl rfl rfl rfl
      machine_cm (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
  | is =>
    rw [checkCore] at hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
    cases hck
    exact same G hf rfl rfl _ hr' (machine_chkPlain (by simp))
      (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
  | ty =>
    rw [checkCore] at hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
    cases hck
    exact same G hf rfl rfl _ hr' (machine_chkPlain (by simp))
      (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))
  | rt =>
    rw [checkCore] at hck
    obtain ⟨_, -, hck⟩ := Except.bind_ok hck
    obtain ⟨⟨R, hr, eq⟩, hr', hck⟩ := Except.bind_ok hck
    cases hck
    exact same G hf rfl rfl _ hr' (machine_chkPlain (by simp))
      (fun U K hU => by rw [usesCore] at hU <;> first | exact isS hU | (intros; contradiction))

theorem UCtx.branchCtx_Γ {G Gb : UCtx} {s k H idx sig : Tm} {fe ph us cell : Bool} (hf : G.fill = false)
    (h : G.branchCtx P s k H idx sig fe ph us cell = some Gb) :
    ∃ Γf σ, ({ G.Γ with ghost := G.Γ.ghost || ph } : Ctx).branch P s k H idx sig = (Γf, .ok σ) ∧ Gb.fill = false ∧
      Gb.Γ = { ({ G.Γ with ghost := G.Γ.ghost || ph } : Ctx).advBr P (({ G.Γ with ghost := G.Γ.ghost || ph } : Ctx).setErs
        { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)) s k fe (sig.len - 1)
        with cmode := false } := by
  unfold UCtx.branchCtx at h
  simp only at h
  split at h
  · rename_i Γf σ hb
    cases h
    exact ⟨Γf, σ, hb, hf, by simp [UCtx.next, hf]⟩
  · cases h

theorem UCtx.arms_check {G : UCtx} {s St H idx : Tm} {er ntf : Bool} {shp : List Arm} {hs : TmTy P G.Γ s St}
    {hsh : Shape P G.Γ er H shp ntf} (hst : checkTm P G.Γ s = .ok ⟨St, hs⟩) (hS : G.Γ.canon St = .app H idx)
    (hsh' : shapeOf P G.Γ er H = .ok ⟨shp, ntf, hsh⟩) : G.arms P s er = some (H, idx, shp) := by
  simp [UCtx.arms, hst, hS, hsh', Except.toOption]

theorem branch_uses {G : UCtx} {b : Nat} {ru : List Bool} {R s H idx k sig : Tm} {shp : List Arm} {fe cell ph : Bool}
    {brs : List Br} {BU : Uses} {BK : Caps} {c : Nat} {body : Core} {Γf : Ctx} {σ : Nat → Option Tm}
    (hf : G.fill = false) (huq : ∀ j, G.uq.contains j = true → j < G.Γ.n) (hsigT : sig.isTele)
    (hB : usesArms P b G ru R s H idx shp fe cell brs = some (BU, BK)) (hlk : lookupBr brs c = some body)
    (hshp : shp[c]? = some (k, sig, ph))
    (hbr : ({ G.Γ with ghost := G.Γ.ghost || (!fe && ph) } : Ctx).branch P s k H idx sig = (Γf, .ok σ)) :
    ∃ Gb, G.branchCtx P s k H idx sig fe (!fe && ph) G.scr cell = some Gb ∧ Gb.fill = false ∧
      Gb.Γ = { ({ G.Γ with ghost := G.Γ.ghost || (!fe && ph) } : Ctx).advBr P (({ G.Γ with ghost := G.Γ.ghost || (!fe && ph) } : Ctx).setErs
        { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)) s k fe (sig.len - 1)
        with cmode := false } ∧
      (Gb.Γ.ghost = false → ∀ j, Gb.uq.contains j = true → j < Gb.Γ.n) ∧ (usesCore P b Gb ru R body).isSome = true := by
  obtain ⟨Gb, hGbs⟩ : ∃ Gb, G.branchCtx P s k H idx sig fe (!fe && ph) G.scr cell = some Gb := by
    unfold UCtx.branchCtx; simp only [hbr]; exact ⟨_, rfl⟩
  obtain ⟨BU', BK', hBU, -⟩ := usesArms_sel brs BU BK hB c body hlk k sig ph hshp Gb hGbs
  obtain ⟨Γf2, σ2, hb2, hGbf, hGbΓ⟩ := UCtx.branchCtx_Γ hf hGbs
  rw [hbr] at hb2; simp only [Prod.mk.injEq, UResult.ok.injEq] at hb2; obtain ⟨rfl, rfl⟩ := hb2
  refine ⟨Gb, hGbs, hGbf, hGbΓ, fun hgb j hj => ?_, by rw [hBU]; rfl⟩
  cases fe
  · have hfg : Γf.ghost = (G.Γ.ghost || (!false && ph)) := by
      have := hbr; rw [Ctx.branch_ghost] at this
      simp only [Prod.mk.injEq] at this; rw [← this.1]
    have hph : ph = false := by rw [hGbΓ] at hgb; simp at hgb; simp [hfg] at hgb; exact hgb.2
    subst hph
    simp only [Bool.and_false] at hGbs
    obtain ⟨hGn, -, -, -, -, -, -, hGuq⟩ := branchCtx_fld hf hsigT hGbs
    rcases hGuq j hj with h | ⟨i, rfl, hi, -⟩
    · have := huq j h; omega
    · omega
  · obtain ⟨hGn, -, -, -, -, -, -, hGuq⟩ := branchCtx_erf hf hsigT hGbs
    rw [hGuq] at hj; have := huq j hj; omega

theorem MSound.mtch (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {s R : Tm} {brs : List Br}
    {els : Option Core} {er : Bool} {rest : Core} {d c : Nat} {ls vs : Tm} {pre : List Tm} {body : Core}
    {outs : List Tm} {cnt1 : Nat}
    (hs : s.subst (Tm.env ρ) = .app (.vc d c ls) vs) (hb : selectBr brs els c vs.toList = some (pre, body))
    (hev : eval P μ (ρ ++ pre) cnt body = .ok (outs, cnt1))
    (ihb : MSound P μ (ρ ++ pre) cnt body) (ihr : MSound P μ (ρ ++ outs) cnt1 rest) :
    MSound P μ ρ cnt (.mtch s R brs els er rest) := by
  intro b G Γ ru rs rets hh hf hGΓ hck hE hlb hm hrs hC vs' cnt' h
  subst hGΓ
  rw [eval] at h; simp only [hs] at h
  split at h
  rotate_left; · rename_i hno; rw [hb] at hno; cases hno
  rename_i pre'' body'' hb''
  rw [hb] at hb''; cases hb''
  simp only [hev] at h
  rw [checkCore] at hck
  obtain ⟨⟨St, hst⟩, hst', hck⟩ := Except.bind_ok hck
  split at hck
  rename_i T0 ht0 heqT
  cases heqT
  split at hck
  rotate_left; · cases hck
  rename_i H idx hS
  obtain ⟨⟨shp, ntf, hsh⟩, hsh', hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hnt⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hl⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hR⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hRs⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hRt⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hok⟩, -, hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hbr⟩, hbr', hck⟩ := Except.bind_ok hck
  obtain ⟨⟨hel⟩, hel', hck⟩ := Except.bind_ok hck
  obtain ⟨⟨R2, hr, e2⟩, hr', hck⟩ := Except.bind_ok hck
  cases hck
  have hbr0 : ∀ c k sig p, shp[c]? = some (k, sig, p) → BranchOK P b false { G.Γ with ghost := G.Γ.ghost || er || p }
      s k H idx sig R (lookupBr brs c) els.isSome := fun c k sig p h1 => by simpa using hbr c k sig p h1
  obtain ⟨d', c', ls', vs'', hsv, hntd, harm, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', hg', he1, he2, hlen, hctx⟩ :=
    match_setup (ge := G.Γ.ghost || er) hP hE hlb hm hst hS hsh hbr0 hel hRs
  rw [hs] at hsv; cases hsv
  rw [hb] at hb'; cases hb'
  have hres := eval_sound hP μ (ρ ++ pre) cnt body b Γ' R hcb hE' hlb' hm' hRs'
  obtain ⟨hE'', hlb'', hm'', hrs'', -, hle, hol⟩ :=
    mtch_setup (rest := rest) hP hE hlb hm hrs hRs hRt hok hnt hs hb hev hntd hg' he1 he2 hres
  have hcs : CloOK P (s.subst (Tm.env ρ)) := CloOK.subst (CloOK.env hC) s hst.noClo
  rw [hs] at hcs
  have hCpre : ∀ v ∈ ρ ++ pre, CloOK P v := fun v hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact hC v hv
    · unfold selectBr at hb
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb; obtain ⟨rfl, -⟩ := hb; exact CloOK.toList hcs.2 v hv
      · cases els <;> simp at hb; obtain ⟨rfl, -⟩ := hb; simp at hv
  obtain ⟨hcB, hckB⟩ : ∃ h', checkCore P b Γ' body (.inl R) = .ok ⟨R, h'⟩ := by
    rcases hctx with ⟨e, rfl, -, rfl, rfl⟩ | ⟨k, sig, Γf, σ, hshc, hlk, hbrc, rfl⟩
    · obtain ⟨_, -, hel'⟩ := Except.bind_ok hel'
      obtain ⟨⟨R1, h1, e1⟩, hc1, -⟩ := Except.bind_ok hel'
      have := e1.1 R rfl; subst this
      exact ⟨_, hc1⟩
    · rcases checkBranches_live _ _ _ hbr' c k sig _ body hshc (by simpa using hlk) with rfl | ⟨Γf', σ', h', hbrc', hc'⟩
      · rw [eval] at hev; cases hev
      · have := hbrc.symm.trans hbrc'
        simp only [Prod.mk.injEq, UResult.ok.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨h', hc'⟩
  have ihb' := fun (Gb : UCtx) (hGb : Gb.Γ = Γ') (hfb : Gb.fill = false) =>
    ihb b Gb Γ' G.ents (.inl R) R hcB hfb hGb hckB hE' hlb' hm' hRs' hCpre outs cnt1 hev
  have hΓr : ∀ us, (G.next (G.adv P (G.Γ.pushTele R (if er then some (List.replicate R.len true) else none))
      (.mtch s R brs els er rest)) us).Γ = Ctx.adv P G.Γ (G.Γ.pushTele R (if er then some (List.replicate R.len true)
      else none)) (.mtch s R brs els er rest) := fun us => by simp [UCtx.next, UCtx.adv, hf]
  have ihr' := fun us hCo => ihr b (G.next (G.adv P (G.Γ.pushTele R (if er then some (List.replicate R.len true)
      else none)) (.mtch s R brs els er rest)) us) _ ru rs rets _ hf (hΓr us) hr' hE'' hlb'' hm'' hrs'' hCo vs' cnt' h
  have hghost : Γ'.ghost = false → G.Γ.ghost = false ∧ er = false := fun h => by
    rcases hg' with e | e <;> rw [e] at h <;> simp_all
  have houtsG : Γ'.ghost = true → ∀ v ∈ ρ ++ outs, CloOK P v := fun hgt v hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact hC v hv
    · exact (ihb' { G with Γ := Γ' } rfl hf).2 (fun h => by rw [hgt] at h; cases h) v hv
  cases er with
  | true =>
    have hgt : Γ'.ghost = true := by rcases hg' with e | e <;> simp [e]
    refine ⟨machine_mtchE hRt hol (ihr' [] (houtsG hgt)).1, fun hpre => (ihr' [] (houtsG hgt)).2 fun hg'' => ?_⟩
    obtain ⟨huq, hus⟩ := hpre (by simpa [UCtx.next, UCtx.adv_ghost' hf, (Ctx.pushTele_er G.Γ R _ hRt).1] using hg'')
    obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
    rw [usesCore] at hU
    obtain ⟨⟨CU, CK⟩, hC', -⟩ := Option.bind_eq_some_iff.mp hU
    exact ⟨UCtx.next_uqlt huq (by rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hRt]; omega), by simp only [Bool.true_or, ite_true] at hC' ⊢; rw [hC']; rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at ihr' hΓr ⊢
    have hn : G.Γ.n ≤ (G.adv P (G.Γ.pushTele R none) (.mtch s R brs els false rest)).n := by
      rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hRt]; omega
    have harms := UCtx.arms_check hst' hS hsh'
    have hsplit : ∀ U K, G.Γ.ghost = false → usesCore P b G ru rets (.mtch s R brs els false rest) = some (U, K) →
        (usesCore P b (G.next (G.adv P (G.Γ.pushTele R none) (.mtch s R brs els false rest)) G.ents) ru rets rest).isSome ∧
        (∃ BU BK, usesArms P b G G.ents R s H idx shp false true brs = some (BU, BK)) ∧
        ∃ EU EK, usesEls P b G G.ents R s els = some (EU, EK) := fun U K hg hU => by
      rw [usesCore] at hU
      obtain ⟨⟨CU, CK⟩, hC', hU⟩ := Option.bind_eq_some_iff.mp hU
      simp only [Bool.false_or, hg, Bool.false_eq_true, ite_false] at hU hC'
      obtain ⟨⟨Hh', idx', shp'⟩, harms', hU⟩ := Option.bind_eq_some_iff.mp hU
      rw [harms] at harms'; cases harms'
      simp only at hU
      obtain ⟨S, -, hU⟩ := Option.bind_eq_some_iff.mp hU
      obtain ⟨⟨BU, BK⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
      obtain ⟨⟨EU, EK⟩, hE_, -⟩ := Option.bind_eq_some_iff.mp hU
      exact ⟨by rw [hC']; rfl, ⟨BU, BK, hB⟩, EU, EK, hE_⟩
    obtain ⟨k0, sig, sig0, hshc0, hctor, hll, hvt, hsigT⟩ := harm
    have hbodyU : G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) →
        (usesCore P b G ru rets (.mtch s R brs els false rest)).isSome = true →
        ∃ Gb : UCtx, Gb.Γ = Γ' ∧ Gb.fill = false ∧ (Gb.Γ.ghost = false → ∀ j, Gb.uq.contains j = true → j < Gb.Γ.n) ∧
          (usesCore P b Gb G.ents R body).isSome = true := by
      intro hg huq hus
      obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
      obtain ⟨-, ⟨BU, BK, hB⟩, EU, EK, hEl⟩ := hsplit U K hg hU
      rcases hctx with ⟨e, rfl, hlk, rfl, rfl⟩ | ⟨k', sig', Γf, σ, hshc, hlk, hbrc, rfl⟩
      · let Ge : UCtx := { G with scr := false, ents := [], rebind := if G.scr && s.isFv then some s else none, uscr := none, cellOk := false }
        refine ⟨Ge, by simp [Ge], hf, fun _ => huq, ?_⟩
        rw [usesEls] at hEl
        obtain ⟨⟨u1, k1⟩, h1, -⟩ := Option.bind_eq_some_iff.mp hEl
        rw [h1]; rfl
      · rw [hshc0] at hshc; cases hshc
        have hbrc' : ({ G.Γ with ghost := G.Γ.ghost || (!false && P.phantom d c) } : Ctx).branch P s k0 H idx sig =
            (Γf, .ok σ) := by simpa using hbrc
        obtain ⟨Gb, -, hGbf, hGbΓ, hGbuq, hGbU⟩ := branch_uses hf huq hsigT hB hlk hshc0 hbrc'
        exact ⟨Gb, by rw [hGbΓ]; simp, hGbf, hGbuq, hGbU⟩
    have houts : (G.Γ.ghost = false → (∀ j, G.uq.contains j = true → j < G.Γ.n) ∧
        (usesCore P b G ru rets (.mtch s R brs els false rest)).isSome = true) → ∀ v ∈ ρ ++ outs, CloOK P v := by
      intro hpre
      cases hgG : G.Γ.ghost
      · obtain ⟨huq, hus⟩ := hpre hgG
        obtain ⟨Gb, hGbΓ, hGbf, hGbuq, hGbU⟩ := hbodyU hgG huq hus
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hC v hv
        · exact (ihb' Gb hGbΓ hGbf).2 (fun hgb => ⟨hGbuq hgb, hGbU⟩) v hv
      · exact houtsG (by rcases hg' with e | e <;> simp [e, hgG])
    refine ⟨fun U K hU ρS vsS hS hrun Hh ρM Res Out Shr pd hM hG0 => ?_, fun hpre => (ihr' G.ents (houts hpre)).2 fun hg'' => ?_⟩
    · have hg := hG0.ghost
      have hrt : rt P G.Γ s = true := by simpa [Ctx.ok, hg] using hok
      have hCo := houts fun _ => ⟨hG0.uqlt, by rw [hU]; rfl⟩
      have hntf : P.isNt d = false := by rw [hntd]; simpa using hnt
      have hview : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∀ d' c' ls' vs', P.view (P.sub ρS s) = .app (.vc d' c' ls') vs' →
          d' = d ∧ c' = c := fun ρS hS d' c' ls' vs' hv => by
        have hR := rt_real hP hE hS s hrt; rw [hs] at hR
        obtain ⟨vsS, -, hsS, -⟩ := hR.con_inv hntf
        rw [hsS] at hv; simp only [Tm.app.injEq, Tm.vc.injEq] at hv; exact ⟨hv.1.1.symm, hv.1.2.1.symm⟩
      have hph : P.phantom d c = false := by
        have hR := rt_real hP hE hS s hrt; rw [hs] at hR
        obtain ⟨-, -, -, -, hp, -⟩ := hR.con_inv hntf
        exact hp
      have hgb : Γ'.ghost = false := by rcases hg' with e | e <;> simp [e, hg, hph]
      rcases hctx with ⟨e, rfl, hlk, rfl, rfl⟩ | ⟨k', sig', Γf, σ, hshc, hlk, hbrc, rfl⟩
      · have hpre : pre = [] := by simp [selectBr, hlk] at hb; exact hb
        subst hpre
        let Ge : UCtx := { G with scr := false, ents := [], rebind := if G.scr && s.isFv then some s else none, uscr := none, cellOk := false }
        refine machine_mtch_els hP hE hrt hRt hs hlk rfl hview hol (by have := (ihb' Ge (by simp [Ge]) hf).1; rwa [List.append_nil] at this)
          (fun ρS hS => ?_) (by simpa [hg] using (ihr' G.ents hCo).1) U K hU ρS vsS hS hrun Hh ρM Res Out Shr pd hM hG0
        simpa using hres.2 hgb ρS (by simpa using hS) outs cnt1 hev
      · rw [hshc0] at hshc; cases hshc
        have hl := hE.len
        have hpre : pre = vs.toList := by rw [selectBr_lookup hlk] at hb; simp at hb; exact hb.symm
        subst hpre
        have hbrc' : ({ G.Γ with ghost := G.Γ.ghost || false } : Ctx).branch P s k0 H idx sig = (Γf, .ok σ) := by
          simpa [hph] using hbrc
        obtain ⟨Gb, hGbs⟩ : ∃ Gb, G.branchCtx P s k0 H idx sig false false G.scr true = some Gb := by
          unfold UCtx.branchCtx; simp only [hbrc']; exact ⟨_, rfl⟩
        obtain ⟨Γf2, σ2, hb2, hGbf, hGbΓ⟩ := UCtx.branchCtx_Γ hf hGbs
        rw [hbrc'] at hb2; simp only [Prod.mk.injEq, UResult.ok.injEq] at hb2; obtain ⟨rfl, rfl⟩ := hb2
        have hGbΓ' : Gb.Γ = { ({ G.Γ with ghost := G.Γ.ghost || false || P.phantom d c } : Ctx).advBr P
            (({ G.Γ with ghost := G.Γ.ghost || false || P.phantom d c } : Ctx).setErs { Γf with σ := σ }
            (if false = true then some (List.replicate (sig.len - 1) true) else none)) s k0 false (sig.len - 1)
            with cmode := false } := by rw [hGbΓ]; simp [hph]
        obtain ⟨hse, hsl, hsu⟩ := hvt.skip (ctor_tele hP hctor)
        rw [hll] at hse hsl hsu
        obtain ⟨sig1, hc1, hpl⟩ := hlen (by simp [hlk])
        rw [hctor] at hc1; cases hc1
        have hlenF : vs.toList.length = sig.len - 1 := by rw [hpl, hsl, Tm.len_subst _ _ (.inl hsigT)]
        have hsig : ∀ j, j < sig.len - 1 → sig.ers.getD j true = (sig0.skip (P.lifted d)).ers.getD j true ∧
            sig.uAt j = (sig0.skip (P.lifted d)).uAt j := fun j _ =>
          ⟨by rw [hse, Tm.ers_subst _ _ hsigT], by rw [hsu, Tm.uAt_subst _ _ _ hsigT]⟩
        have hSb : ∀ ρS lsS vsS, SimEnv P G.Γ.er ρS ρ → P.view (P.sub ρS s) = .app (.vc d c lsS) vsS →
            SimEnv P Gb.Γ.er (ρS ++ vsS.toList) (ρ ++ vs.toList) := fun ρS lsS vsS hS' hv => by
          have hR := rt_real hP hE hS' s hrt; rw [hs] at hR
          obtain ⟨vsS', sig2, hsS, hsig2, -, hrv⟩ := hR.con_inv hntf
          rw [hsS] at hv; simp only [Tm.app.injEq, Tm.vc.injEq] at hv; obtain ⟨-, rfl⟩ := hv
          rw [hGbΓ']
          refine hS'.extend hrv.len (fun i hi => he1 i (hl ▸ hi)) fun k a b ha hb he => ?_
          rw [hl, he2 sig2 hsig2 k (List.getElem?_eq_some_iff.mp hb).1, Bool.false_or] at he
          exact hrv.get k a b ha hb he
        refine machine_mtch_fld hP hE hrt (fun x e => by subst e; simpa [Tm.static] using (tm_sound hP hE hst).2.1)
          hRt hs hlk hctor (Prog.wrapField_none hntf) hview hol (fun H' idx' shp' ha => ?_)
          (by simpa [hg] using (ihr' G.ents hCo).1) U K hU ρS vsS hS hrun Hh ρM Res Out Shr pd hM hG0
        rw [harms] at ha; cases ha
        exact ⟨k0, sig, by rw [hshc0, hph], hsigT, hlenF, hsig, Gb, hGbs, (ihb' Gb hGbΓ' hGbf).1, hSb,
          fun ρS' hS' => hres.2 hgb ρS' (hGbΓ' ▸ hS') outs cnt1 hev⟩
    · have hg : G.Γ.ghost = false := by
        simpa [UCtx.next, UCtx.adv_ghost' hf, (Ctx.pushTele_er G.Γ R _ hRt).1] using hg''
      obtain ⟨huq, hus⟩ := hpre hg
      obtain ⟨⟨U, K⟩, hU⟩ := Option.isSome_iff_exists.mp hus
      exact ⟨UCtx.next_uqlt huq hn, (hsplit U K hg hU).1⟩

end Minimal
