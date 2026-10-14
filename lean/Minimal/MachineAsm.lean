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

theorem CloOK.defFns {G : UCtx} {ρ : List Tm} {gid : Nat} {Gr : Group} {O : Uses} {K : Caps}
    (hE : EnvOK P ρ G.Γ) (hGr : P.groups[gid]? = some Gr) (hok : GroupOK P gid G.Γ Gr) (hf : G.fill = false)
    (hg : G.Γ.ghost = false) (huq : ∀ j, G.uq.contains j = true → j < G.Γ.n)
    (hus : usesFns P gid G Gr Gr.fns = some (O, K)) (hd : G.defOK Gr O = true) (hC : ∀ v ∈ ρ, CloOK P v) :
    ∀ v ∈ closures ρ gid Gr, CloOK P v := by
  intro v hv
  simp only [closures, List.mem_map] at hv
  obtain ⟨k, -, rfl⟩ := hv
  exact ⟨by rw [Tm.toList_ofList]; exact ⟨G, Gr, O, K, hGr, hE, hok, hf, hg, huq, hus, hd⟩, CloOK.ofList hC⟩

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

end Minimal
