import Minimal.MachineSound

namespace Minimal

variable {P : Prog}

theorem lookup_mem : ∀ {l : Uses} {i : Nat} {v : Bool}, l.lookup i = some v → (i, v) ∈ l
  | [], _, _, h => by simp at h
  | (j, u) :: l, i, v, h => by
    by_cases e : i = j
    · subst e; simp [List.lookup] at h; subst h; simp
    · have : (i == j) = false := by simpa using e
      simp only [List.lookup, this] at h; exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Uses.add_mem {U U' : Uses} {i j : Nat} {u : Bool} (h : Uses.add U i u = some U') (hm : (j, true) ∈ U') :
    (j, true) ∈ U ∨ (j = i ∧ u = true) := by
  unfold Uses.add at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact .inl hm
  · cases h
    rcases List.mem_cons.mp hm with e | e
    · cases e; exact .inr ⟨rfl, rfl⟩
    · exact .inl e

theorem Uses.seq_mem : ∀ {B A U : Uses} {j : Nat}, Uses.seq A B = some U → (j, true) ∈ U → (j, true) ∈ A ∨ (j, true) ∈ B
  | [], A, U, j, h, hm => by simp [Uses.seq] at h; subst h; exact .inl hm
  | (i, u) :: B, A, U, j, h, hm => by
    simp only [Uses.seq, List.foldlM_cons] at h
    obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rcases Uses.seq_mem (A := A1) (B := B) h2 hm with hm | hm
    · rcases Uses.add_mem h1 hm with hm | ⟨rfl, rfl⟩
      · exact .inl hm
      · exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ hm)

theorem Uses.join_mem : ∀ {B A : Uses} {j : Nat}, (j, true) ∈ Uses.join A B → (j, true) ∈ A ∨ (j, true) ∈ B
  | [], A, j, hm => .inl hm
  | (i, u) :: B, A, j, hm => by
    simp only [Uses.join, List.foldl_cons] at hm
    rcases Uses.join_mem (B := B) hm with hm | hm
    · split at hm
      · exact .inl hm
      · split at hm
        · rcases List.mem_cons.mp hm with e | e
          · cases e; subst u; exact .inr (List.mem_cons_self ..)
          · exact .inl (List.mem_filter.mp e).1
        · exact .inl hm
      · rcases List.mem_cons.mp hm with e | e
        · cases e; exact .inr (List.mem_cons_self ..)
        · exact .inl e
    · exact .inr (List.mem_cons_of_mem _ hm)

theorem Uses.below_mem {U : Uses} {n j : Nat} (h : (j, true) ∈ U.below n) : (j, true) ∈ U ∧ j < n := by
  have := List.mem_filter.mp h; simpa using this

def UqOK (G : UCtx) (U : Uses) : Prop := ∀ i, (i, true) ∈ U → G.uq.contains i = true ∨ G.Γ.n ≤ i

theorem UqOK.seq {G : UCtx} {A B U : Uses} (h : Uses.seq A B = some U) (ha : UqOK G A) (hb : UqOK G B) : UqOK G U :=
  fun i hi => (Uses.seq_mem h hi).elim (ha i) (hb i)

theorem UqOK.join {G : UCtx} {A B : Uses} (ha : UqOK G A) (hb : UqOK G B) : UqOK G (Uses.join A B) :=
  fun i hi => (Uses.join_mem hi).elim (ha i) (hb i)

theorem UqOK.nil {G : UCtx} : UqOK G [] := fun _ h => by simp at h

theorem UqOK.use {G : UCtx} {i : Nat} {u : Bool} {A : Uses} (h : G.use i u = some A) : UqOK G A := fun j hj => by
  simp only [UCtx.use] at h
  split at h
  · cases h
  · rename_i hc; cases h
    simp only [List.mem_singleton, Prod.mk.injEq] at hj; obtain ⟨rfl, rfl⟩ := hj
    exact .inl (by cases e : G.uq.contains j <;> simp_all)

mutual
theorem termUses_uq {G : UCtx} : ∀ {u : Bool} {t : Tm} {A : Uses}, G.termUses P u t = some A → UqOK G A
  | u, .fv j, A, h => UqOK.use h
  | u, .app hd args, A, h => by
    simp only [UCtx.termUses] at h
    split at h
    · obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      split at h2
      · obtain ⟨A0, h0, h3⟩ := Option.bind_eq_some_iff.mp h2
        exact UqOK.seq h3 (UqOK.use h0) (argsUses_uq h1)
      · cases h2; exact argsUses_uq h1
    · cases h
  | _, .bv _, _, h | _, .nil, _, h | _, .cons .., _, h | _, .bind .., _, h | _, .tyc .., _, h
  | _, .tyCtor _, _, h | _, .valCtor _, _, h | _, .univ, _, h | _, .level, _, h | _, .predates .., _, h
  | _, .subterm .., _, h | _, .fn .., _, h | _, .mtbl .., _, h | _, .lvl _, _, h | _, .tok, _, h
  | _, .clo .., _, h | _, .nat _, _, h | _, .ptr _, _, h | _, .vc .., _, h => by
    simp only [UCtx.termUses] at h; first | (cases h; exact UqOK.nil) | cases h

theorem argsUses_uq {G : UCtx} : ∀ {md : Ent → Bool} {args s : Tm} {A : Uses}, G.argsUses P md args s = some A →
    UqOK G A
  | md, .cons a as, .bind k _ r, A, h => by
    simp only [UCtx.argsUses] at h
    split at h <;> obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h <;>
      obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
    · cases h1; exact UqOK.seq h3 UqOK.nil (argsUses_uq hB)
    · exact UqOK.seq h3 (termUses_uq h1) (argsUses_uq hB)
  | md, .cons _ _, .nil, A, h | md, .cons _ _, .fv _, A, h | md, .cons _ _, .bv _, A, h
  | md, .cons _ _, .cons .., A, h | md, .cons _ _, .app .., A, h | md, .cons _ _, .tyc .., A, h
  | md, .cons _ _, .vc .., A, h | md, .cons _ _, .tyCtor _, A, h | md, .cons _ _, .valCtor _, A, h
  | md, .cons _ _, .univ, A, h | md, .cons _ _, .level, A, h | md, .cons _ _, .predates .., A, h
  | md, .cons _ _, .subterm .., A, h | md, .cons _ _, .fn .., A, h | md, .cons _ _, .mtbl .., A, h
  | md, .cons _ _, .lvl _, A, h | md, .cons _ _, .tok, A, h | md, .cons _ _, .clo .., A, h
  | md, .cons _ _, .nat _, A, h | md, .cons _ _, .ptr _, A, h
  | md, .nil, _, A, h | md, .fv _, _, A, h | md, .bv _, _, A, h | md, .bind .., _, A, h | md, .app .., _, A, h
  | md, .tyc .., _, A, h | md, .vc .., _, A, h | md, .tyCtor _, _, A, h | md, .valCtor _, _, A, h
  | md, .univ, _, A, h | md, .level, _, A, h | md, .predates .., _, A, h | md, .subterm .., _, A, h
  | md, .fn .., _, A, h | md, .mtbl .., _, A, h | md, .lvl _, _, A, h | md, .tok, _, A, h
  | md, .clo .., _, A, h | md, .nat _, _, A, h | md, .ptr _, _, A, h => by
    simp only [UCtx.argsUses] at h; cases h; exact UqOK.nil
end

theorem Ctx.openTele_n_le : ∀ m (Γ : Ctx) (t : Tm), Γ.n ≤ (Γ.openTele t m).1.n := by
  intro m; induction m with
  | zero => intro Γ t; cases t <;> simp [Ctx.openTele]
  | succ m ih =>
    intro Γ t
    cases t with
    | bind k A r => simp only [Ctx.openTele]; have := ih (Γ.pushEnt k A) (r.inst (.fv Γ.n) 0); rw [Γ.pushEnt_n] at this; omega
    | _ => simp [Ctx.openTele]

theorem Ctx.pushTele_n_le (Γ : Ctx) (R : Tm) (ov : Option (List Bool)) : Γ.n ≤ (Γ.pushTele R ov).n := by
  simp only [Ctx.pushTele, Ctx.setErs_n]; exact Ctx.openTele_n_le _ _ _

theorem Ctx.pushPrim_n_le (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : Γ.n ≤ (Γ.pushPrim T er p).n := by
  cases p <;> simp [Ctx.pushPrim, Ctx.push, Ctx.withRule, Ctx.n]

theorem UCtx.adv_n' {G : UCtx} (hf : G.fill = false) {Γ' : Ctx} {c : Core} : (G.adv P Γ' c).n = Γ'.n := by
  simp [UCtx.adv, hf]

theorem UCtx.next_uq {G : UCtx} {Γ' : Ctx} {us : List Bool} {i : Nat} (h : (G.next Γ' us).uq.contains i = true) :
    G.uq.contains i = true ∨ G.Γ.n ≤ i := by
  simp only [UCtx.next, List.contains_append, Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl h
  · right; simp at h; obtain ⟨k, -, e⟩ := h; omega

theorem UqOK.next {G : UCtx} {Γ' : Ctx} {us : List Bool} {U : Uses} (hn : G.Γ.n ≤ Γ'.n)
    (h : UqOK (G.next Γ' us) U) : UqOK G U := fun i hi => by
  rcases h i hi with h | h
  · exact UCtx.next_uq h
  · exact .inr (Nat.le_trans hn h)

theorem Ctx.branch_fst (Γ : Ctx) (s k H idx sig : Tm) : (Γ.branch P s k H idx sig).1 = (Γ.openTele sig (sig.len - 1)).1 := by
  rcases h : Γ.openTele sig (sig.len - 1) with ⟨Γf, rem⟩
  simp only [Ctx.branch, h]; split <;> rfl

theorem branchCtx_spec {G Gb : UCtx} {s k H idx sig : Tm} {fe ph uscr : Bool}
    (h : G.branchCtx P s k H idx sig fe ph uscr = some Gb) :
    G.Γ.n ≤ Gb.Γ.n ∧ (∀ i < G.Γ.n, Gb.uq.contains i = true → G.uq.contains i = true) ∧ Gb.fill = G.fill := by
  unfold UCtx.branchCtx at h
  simp only at h
  rcases hb : Ctx.branch P { G.Γ with ghost := G.Γ.ghost || ph } s k H idx sig with ⟨Γf, r⟩
  have hf : Γf = ({ G.Γ with ghost := G.Γ.ghost || ph }.openTele sig (sig.len - 1)).1 := by
    rw [← Ctx.branch_fst, hb]
  rw [hb] at h
  cases r with
  | ok σ =>
    simp only [Option.some.injEq] at h; subst h
    have hn : G.Γ.n ≤ Γf.n := by rw [hf]; exact Ctx.openTele_n_le _ { G.Γ with ghost := G.Γ.ghost || ph } _
    refine ⟨?_, fun i hi hc => ?_, rfl⟩
    · simp only [UCtx.next]; split <;> simpa [Ctx.n] using hn
    · rcases UCtx.next_uq hc with h | h
      · exact h
      · omega
  | _ => cases h


theorem UqOK.below {G Gb : UCtx} {U : Uses} (hn : G.Γ.n ≤ Gb.Γ.n)
    (huq : ∀ i, i < G.Γ.n → Gb.uq.contains i = true → G.uq.contains i = true) (h : UqOK Gb U) :
    UqOK G (U.below G.Γ.n) := fun i hi => by
  obtain ⟨hi, hlt⟩ := Uses.below_mem hi
  rcases h i hi with h | h
  · exact .inl (huq i hlt h)
  · omega

theorem UR.seq_fst {a b r : Uses × Caps} (h : UR.seq a b = some r) : Uses.seq a.1 b.1 = some r.1 := by
  simp only [UR.seq] at h
  obtain ⟨x, hx, e⟩ := Option.bind_eq_some_iff.mp h; cases e; exact hx

theorem UqOK.ur_seq {G : UCtx} {a b r : Uses × Caps} (h : UR.seq a b = some r) (ha : UqOK G a.1) (hb : UqOK G b.1) :
    UqOK G r.1 := UqOK.seq (UR.seq_fst h) ha hb

theorem retUses_uq {G : UCtx} (ru : List Bool) (ts rets : Tm) {A : Uses} (h : G.retUses P ru ts rets = some A) :
    UqOK G A := by
  induction ru, ts, rets using UCtx.retUses.induct (P := P) (G := G) generalizing A with
  | case1 u us a as k ty r hk ih | case3 x a as k ty r _ hk ih =>
    simp only [UCtx.retUses, hk, ite_true] at h
    obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp (by simpa using h)
    exact UqOK.seq h3 UqOK.nil (ih hB)
  | case2 u us a as k ty r hk ih | case4 x a as k ty r _ hk ih =>
    simp only [UCtx.retUses, hk] at h
    obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp (by simpa using h)
    obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
    exact UqOK.seq h3 (termUses_uq h1) (ih hB)
  | case5 t x x1 h1 h2 =>
    unfold UCtx.retUses at h; split at h
    · exact (h1 _ _ _ _ _ _ _ rfl rfl rfl).elim
    · exact (h2 _ _ _ _ _ rfl rfl).elim
    · cases h; exact UqOK.nil

theorem primUses_uq {G : UCtx} {u : Bool} {p : Prim} {A : Uses} (h : G.primUses P u p = some A) : UqOK G A := by
  unfold UCtx.primUses at h
  split at h
  · exact termUses_uq h
  · obtain ⟨su, -, h2⟩ := Option.bind_eq_some_iff.mp h
    split at h2
    · cases h2
    · exact termUses_uq h2
  · split at h <;> cases h; exact UqOK.nil
  · split at h
    · cases h
    · exact termUses_uq h
  · split at h <;> cases h; exact UqOK.nil

theorem usesCore_uq (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) (c : Core) :
    G.fill = false → ∀ U K, usesCore P b G ru rets c = some (U, K) → UqOK G U := by
  induction b, G, ru, rets, c using usesCore.induct (P := P) (motive2 := fun _ _ _ _ => True)
    (motive3 := fun b G ru R s els => G.fill = false → ∀ U K, usesEls P b G ru R s els = some (U, K) → UqOK G U)
    (motive4 := fun b G ru R s H idx shp fe brs => G.fill = false → ∀ U K,
      usesArms P b G ru R s H idx shp fe brs = some (U, K) → UqOK G U)
  all_goals first | trivial | (intro hf U K h; first | rw [usesCore] at h | rw [usesEls] at h | rw [usesArms] at h) | skip
  all_goals try assumption
  case case1 hg =>
    simp only [hg, ite_true, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case2 hg =>
    rw [if_neg hg] at h; simp only [UR.lift, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, e⟩ := h; cases e; exact retUses_uq _ _ _ hA
  case case3 b G ru rets f dec args er ms ve rest ih =>
    obtain ⟨⟨t, outs, uf⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ih outs
    simp only [dite_eq_ite, List.map_attach_eq_pmap, List.pmap_eq_map] at hC0
    have hC' : UqOK G CU := UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushTele_n_le ..) (hC0 hf CU CK hC)
    split at h
    · cases h; exact hC'
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨AB, hAB, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.seq hAB (termUses_uq hA) (argsUses_uq hB)) hC'
  case case4 b G ru rets s R brs els er rest ihr iha ihe =>
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ihr
    simp only [dite_eq_ite] at hC0
    have hC' : UqOK G CU := UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushTele_n_le ..) (hC0 hf CU CK hC)
    split at h
    · cases h; exact hC'
    · obtain ⟨⟨H, idx, shp⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨S, hS, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨BU, BK⟩, hB, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨EU, EK⟩, hE, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨SBE, hSBE, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.ur_seq hSBE (termUses_uq hS) (UqOK.join (iha H idx shp hf BU BK hB) (ihe hf EU EK hE))) hC'
  case case5 b G ru rets s brs els er nt hg =>
    simp only [hg, ite_true, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case6 b G ru rets s brs els er nt hg iha ihe =>
    rw [if_neg hg] at h
    obtain ⟨⟨H, idx, shp⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    have fin : ∀ S, UqOK G S → (do
        let B ← usesArms P b G ru rets s H idx shp er brs
        let E ← usesEls P b G ru rets s els
        UR.seq (S, []) (UR.join B E)) = some (U, K) → UqOK G U := fun S hS h => by
      obtain ⟨⟨BU, BK⟩, hB, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨EU, EK⟩, hE, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h hS (UqOK.join (iha H idx shp hf BU BK hB) (ihe hf EU EK hE))
    split at h
    · exact fin [] UqOK.nil (by simpa using h)
    · obtain ⟨S, hS, h⟩ := Option.bind_eq_some_iff.mp h
      exact fin S (termUses_uq hS) h
  case case7 b G ru rets R body rest ihb ihr =>
    obtain ⟨⟨BU, BK⟩, hB, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ihr
    simp only [dite_eq_ite] at hC0
    exact UqOK.ur_seq h (UqOK.below (Nat.le_refl _) (fun _ _ h => h) (ihb hf BU BK hB))
      (UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushTele_n_le ..) (hC0 hf CU CK hC))
  case case8 b G ru rets p er rest ih =>
    obtain ⟨T, -, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ih T
    simp only [dite_eq_ite] at hC0
    have hC' : UqOK G CU := UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushPrim_n_le ..) (hC0 hf CU CK hC)
    split at h
    · cases h; exact hC'
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (primUses_uq hA) hC'
  case case9 b G ru rets rest ih =>
    exact UqOK.next (by rw [UCtx.adv_n' hf]; simp [Ctx.pushMint, Ctx.push, Ctx.n]) (ih hf U K h)
  case case10 b G ru rets gid rest ihr ihf =>
    obtain ⟨Gr, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ihr Gr
    simp only [dite_eq_ite] at hC0
    have hC' : UqOK G CU := UqOK.next (by rw [UCtx.adv_n' hf]; simp [Ctx.pushFns, Ctx.n]) (hC0 hf CU CK hC)
    split at h
    · obtain ⟨⟨O, K'⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [hf, Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, List.all_eq_true] at hc
        refine UqOK.ur_seq h (fun i hi => ?_) hC'
        obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp (hc.2 _ hi)
        exact UqOK.use hA i (by simp only [UCtx.use] at hA; split at hA <;> cases hA; simp)
      · cases h
    · cases h
  case case11 b G ru rets a b1 rest ms ih => exact ih hf U K h
  case case12 b G ru rets a b1 rest ih => exact ih hf U K h
  case case13 b G ru rets a b1 p rest ih => exact ih hf U K h
  case case14 b G ru rets a b1 t rest' hr ih =>
    rw [if_pos hr] at h
    obtain ⟨T, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushPrim_n_le ..) (ih T hf U K h)
  case case15 b G ru rets a b1 t rest' hr => rw [if_neg hr] at h; cases h
  case case16 => cases h
  case case17 b G ru rets b1 rest u i ih =>
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact ih hf _ _ hC
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.use hA) (ih hf _ _ hC)
  case case18 b G ru rets b1 rest u i ih =>
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact ih hf _ _ hC
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.use hA) (ih hf _ _ hC)
  case case19 b G ru rets a b1 rest ih => exact ih hf U K h
  case case20 b G ru rets b1 rest x ih => exact ih hf U K h
  case case21 => rename_i ih; exact ih hf U K h
  case case22 =>
    rename_i Γo u nt ex ph H cs hm σ' hu ih
    simp only [hm] at h
    simp only [Γo] at hu
    simp only [hu] at h
    exact ih hf U K h
  case case23 =>
    rename_i Γo u nt ex ph H cs hm hu
    simp only [hm] at h
    simp only [Γo] at hu
    split at h
    · exact (hu _ ‹_›).elim
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case24 =>
    rename_i hm
    split at h
    · exact (hm _ _ _ _ _ _ ‹_›).elim
    · cases h
  case case25 => rename_i ih; exact ih hf U K h
  case case26 => rename_i ih; exact ih hf U K h
  case case27 => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case28 => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case31 =>
    rename_i hf U K h
    rw [usesEls] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case32 =>
    rename_i ih hf U K h
    rw [usesEls] at h
    obtain ⟨⟨EU, EK⟩, hE, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact UqOK.below (Nat.le_refl _) (fun _ _ h => h) (ih hf EU EK hE)
  case case33 =>
    rename_i hf U K h
    rw [usesArms] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case34 b G ru R s H idx shp fe f1 c f2 body brs k sig ph hshp Gb hbr ihr ihb hf U K h =>
    rw [usesArms] at h
    simp only [hshp, hbr] at h
    obtain ⟨⟨BU, BK⟩, hB, h⟩ := Option.bind_eq_some_iff.mp h
    rcases hR : usesArms P b G ru R s H idx shp fe brs with _ | ⟨RU, RK⟩ <;> rw [hR] at h
    · cases h

    simp only [bind, Option.bind, Option.some.injEq, UR.join, UR.below, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hn, huq, hfb⟩ := branchCtx_spec hbr
    exact UqOK.join (UqOK.below hn huq (ihb (hfb.trans hf) BU BK hB)) (ihr hf RU RK hR)
  case case35 b G ru R s H idx shp fe f1 c f2 body brs k sig ph hshp hbr ihr hf U K h =>
    rw [usesArms] at h
    simp only [hshp] at h
    rcases hR : usesArms P b G ru R s H idx shp fe brs with _ | ⟨RU, RK⟩ <;> rw [hR] at h
    · cases h
    simp only [bind, Option.bind, Option.some.injEq, UR.join, UR.below, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact UqOK.join UqOK.nil (ihr hf RU RK hR)
  case case36 =>
    rename_i hshp ihr hf U K h
    rw [usesArms] at h
    simp [hshp] at h



theorem Ctx.openTele_n_eq : ∀ m (Γ : Ctx) (t : Tm), t.isTele → m ≤ t.len → (Γ.openTele t m).1.n = Γ.n + m := by
  intro m; induction m with
  | zero => intro Γ t _ _; cases t <;> simp [Ctx.openTele]
  | succ m ih =>
    intro Γ t ht hm
    cases t with
    | bind k A r =>
      simp only [Tm.isTele] at ht; simp only [Tm.len] at hm
      simp only [Ctx.openTele]
      rw [ih _ _ (Tm.isTele_inst _ r 0 ht) (by rw [Tm.len_inst _ _ _ ht]; omega), Γ.pushEnt_n]; omega
    | _ => simp_all [Tm.len, Tm.isTele]

theorem Ctx.pushTele_n (Γ : Ctx) {R : Tm} (hR : R.isTele) (ov : Option (List Bool)) :
    (Γ.pushTele R ov).n = Γ.n + R.len := by
  simp only [Ctx.pushTele, Ctx.setErs_n]; exact Ctx.openTele_n_eq _ _ _ hR (Nat.le_refl _)

theorem UCtx.adv_er' {G : UCtx} (hf : G.fill = false) {Γ' : Ctx} {c : Core} : (G.adv P Γ' c).er = Γ'.er := by
  simp [UCtx.adv, hf]

theorem UCtx.adv_ghost' {G : UCtx} (hf : G.fill = false) {Γ' : Ctx} {c : Core} : (G.adv P Γ' c).ghost = Γ'.ghost := by
  simp [UCtx.adv, hf]

theorem UCtx.next_uq_new {G : UCtx} {Γ' : Ctx} {us : List Bool} {k : Nat}
    (h : (G.next Γ' us).uq.contains (G.Γ.n + k) = true) (hlt : ∀ j, G.uq.contains j = true → j < G.Γ.n) :
    us.getD k false = true := by
  simp only [UCtx.next, List.contains_append, Bool.or_eq_true] at h
  rcases h with h | h
  · have := hlt _ h; omega
  · simp at h
    have hv := List.mem_zipIdx_iff_getElem?.mp h
    rw [List.getElem?_take] at hv
    split at hv
    · simp [List.getD_eq_getElem?_getD, hv]
    · cases hv

theorem Uses.below_lookup {U : Uses} {n i : Nat} (h : i < n) : (U.below n).lookup i = U.lookup i := by
  induction U with
  | nil => rfl
  | cons p U ih =>
    obtain ⟨j, u⟩ := p
    simp only [Uses.below, List.filter_cons] at ih ⊢
    by_cases hj : j < n
    · simp only [hj, decide_true, ite_true, List.lookup]
      split <;> simp_all
    · simp only [hj, decide_false, Bool.false_eq_true, ite_false]
      rw [ih]
      have : (i == j) = false := by simp; omega
      simp [List.lookup, this]

def Uses.Eqb (A B : Uses) (n : Nat) : Prop := ∀ i < n, A.lookup i = B.lookup i

theorem Live.congr {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) {er : Nat → Bool} {H : Heap} {ρM ρS : List Tm} {a : Nat}
    (hl : Live P A n er H ρM ρS a) : Live P B n er H ρM ρS a := by
  obtain ⟨z, hz, hA, he, hf⟩ := hl; exact ⟨z, hz, by rw [← h z hz]; exact hA, he, hf⟩

theorem Own.congr {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm}
    {a : Nat} (hl : Own P A n er H ρM ρS ρ a) : Own P B n er H ρM ρS ρ a := by
  obtain ⟨z, hz, hA, he, hf⟩ := hl; exact ⟨z, hz, by rw [← h z hz]; exact hA, he, hf⟩

theorem Uses.Eqb.symm {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) : Uses.Eqb B A n := fun i hi => (h i hi).symm

theorem MFrame.congr {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm}
    {Res Out : Nat → Prop} (hM : MFrame P A n er H ρM ρS ρ Res Out) : MFrame P B n er H ρM ρS ρ Res Out :=
  ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, fun i hi hb he => hM.dec i hi (by rw [h i hi]; exact hb) he,
   fun x hx hb he => hM.wo x hx (by rw [h x hx]; exact hb) he,
   fun x hx z hz hne hbx hbz hex hez => hM.sep x hx z hz hne (by rw [h x hx]; exact hbx) (by rw [h z hz]; exact hbz) hex hez,
   fun x hx hb he => hM.out x hx (by rw [h x hx]; exact hb) he,
   ⟨fun a ha hl => hM.res.1 a ha (hl.congr h.symm), hM.res.2.1, fun a ha ho => hM.res.2.2.1 a ha (ho.congr h.symm),
    hM.res.2.2.2⟩, hM.outb⟩

theorem MOut.congr {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm}
    {Res : Nat → Prop} {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (hO : MOut P A n er H ρM ρS ρ Res rets ru H' vsM vsS vs) : MOut P B n er H ρM ρS ρ Res rets ru H' vsM vsS vs := by
  refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha (fun h' => ho (h'.congr h)) hr, hO.len, hO.dec,
    fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
  · rcases hO.foot k w u hw hu he b hf with h1 | h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (h1.congr h))
    · exact .inr (.inr (.inl h1))
    · exact .inr (.inr (.inr (h1.congr h)))
  · rcases hO.uspine k w u v hw hu hv he hr b hs with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (h1.congr h))
    · exact .inr (.inr h1)

def MRun (P : Prog) (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) (c : Core) (ρ vs : List Tm) : Prop :=
  ∀ U K, usesCore P b G ru rets c = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ → RunS P ρS c vsS →
    ∀ H ρM Res Out pd, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out → GOK P G pd H ρM ρS ρ Res →
    ∃ H' vsM, RunM P H ρM pd c H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res rets ru H' vsM vsS vs

theorem machine_seq {b : Nat} {G : UCtx} {ru : List Bool} {rets R : Tm} {body rest : Core} {ρ outs vs : List Tm}
    (hR : R.isTele) (hol : outs.length = R.len)
    (hsb : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∃ outsS, RunS P ρS body outsS ∧ Reals P (.ofList outsS) (.ofList outs) R)
    (ihb : MRun P b { G with ents := [], uscr := none, cellOk := false, rebind := none } G.ents R body ρ outs)
    (ihr : MRun P b (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents))
      ru rets rest (ρ ++ outs) vs) :
    MRun P b G ru rets (.seq R body rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hM hG
  rw [usesCore] at hU
  obtain ⟨⟨BU, BK⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseq := UR.seq_fst hU
  simp only [UR.below] at hseq
  cases hrun with
  | seq hb hr =>
  rename_i outsS
  obtain ⟨outsS', hb', hre⟩ := hsb ρS hS
  cases RunS.det hb hb'
  have hlS : outsS.length = R.len := by rw [← hol]; simpa [Tm.toList_ofList] using hre.len
  have hn := hM.lenF
  have hEq : Uses.Eqb BU (BU.below G.Γ.n) G.Γ.n := fun i hi => (Uses.below_lookup hi).symm
  have hMb := (hM.split hseq).congr hEq.symm
  have hGb : GOK P { G with ents := [], uscr := none, cellOk := false, rebind := none } none H ρM ρS ρ (fun _ => False) :=
    ⟨.inl rfl, fun _ h => (by cases h), fun _ h => (by cases h), hG.uqlt, hG.fill, hG.ghost⟩
  obtain ⟨H1, oM, hrb, hOb⟩ := ihb BU BK hB ρS outsS hS hb H ρM _ _ none hMb hGb
  have hf := hG.fill
  have hg := hG.ghost
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ R none hR
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushTele R) (.seq R body rest) := ⟨_, rfl⟩
  rw [← hΓ'] at ihr hC
  have her' : Γ'.er = (G.Γ.pushTele R).er := by rw [hΓ']; exact UCtx.adv_er' hf
  have hn' : Γ'.n = G.Γ.n + R.len := by rw [hΓ', UCtx.adv_n' hf, Ctx.pushTele_n _ hR]
  have huq := usesCore_uq b (G.next Γ' (if G.Γ.ghost then [] else G.ents)) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bind hseq (hOb.congr hEq) hlS hol (er' := Γ'.er)
    (fun i hi => by rw [her']; exact hpo i hi)
    (fun k hk _ he => by rw [her', hpn k hk] at he; simpa using he)
    (fun k hk hc _ => by
      rcases huq _ (lookup_mem hc) with h1 | h1
      · have := UCtx.next_uq_new h1 hG.uqlt
        simpa [hg] using this
      · simp only [UCtx.next] at h1; omega)
  have hS' : SimEnv P Γ'.er (ρS ++ outsS) (ρ ++ outs) := by
    rw [her']
    exact hS.pushTele (by rw [hn]) hR none hol (by rw [hlS, hol])
      (fun k a b ha hb he => hre.get k a b (by simpa [Tm.toList_ofList] using ha) (by simpa [Tm.toList_ofList] using hb)
        (by simpa using he))
  have hGr : GOK P (G.next Γ' (if G.Γ.ghost then [] else G.ents)) none H1 (ρM ++ oM) (ρS ++ outsS) (ρ ++ outs) Res := by
    refine ⟨.inl rfl, fun x hx => ?_, fun _ h => (by cases h), fun j hj => ?_, hf, ?_⟩
    · obtain ⟨hxn, hres⟩ := hG.uscr x hx
      refine ⟨by simp only [UCtx.next]; omega, fun a ha => hres a ?_⟩
      rwa [Tm.env_append (by rw [hM.lenM]; omega)] at ha
    · simp only [UCtx.next, List.contains_append, Bool.or_eq_true] at hj
      simp only [UCtx.next]
      rcases hj with hj | hj
      · have := hG.uqlt j hj; omega
      · simp at hj
        obtain ⟨k, hk, e⟩ := hj
        have := (List.mem_zipIdx' hk).1
        simp only [List.length_take] at this
        omega
    · simp only [UCtx.next]; rw [hΓ', UCtx.adv_ghost' hf, hpg]; exact hg
  have hMr' : MFrame P CU (G.next Γ' (if G.Γ.ghost then [] else G.ents)).Γ.n
      (G.next Γ' (if G.Γ.ghost then [] else G.ents)).Γ.er H1 (ρM ++ oM) (ρS ++ outsS) (ρ ++ outs) Res Out := by
    simp only [UCtx.next]; rw [hn']; exact hMr
  obtain ⟨H', vsM, hrr, hOr⟩ := ihr CU CK hC (ρS ++ outsS) vsS hS' hr H1 (ρM ++ oM) Res Out none hMr' hGr
  refine ⟨H', vsM, .seq hrb hrr, lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem GOK.next {G : UCtx} {Γ' : Ctx} {us : List Bool} {pd : Pend} {H H' : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res : Nat → Prop} (hG : GOK P G pd H ρM ρS ρ Res) (hn : G.Γ.n ≤ Γ'.n) (hl : ρM.length = G.Γ.n)
    (hg : Γ'.ghost = false) : GOK P (G.next Γ' us) none H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res := by
  refine ⟨.inl rfl, fun x hx => ?_, fun _ h => (by cases h), fun j hj => ?_, hG.fill, hg⟩
  · obtain ⟨hxn, hres⟩ := hG.uscr x hx
    refine ⟨by simp only [UCtx.next]; omega, fun a ha => hres a ?_⟩
    rwa [Tm.env_append (by rw [hl]; omega)] at ha
  · simp only [UCtx.next, List.contains_append, Bool.or_eq_true] at hj
    simp only [UCtx.next]
    rcases hj with hj | hj
    · have := hG.uqlt j hj; omega
    · simp at hj
      obtain ⟨k, hk, e⟩ := hj
      have := (List.mem_zipIdx' hk).1
      simp only [List.length_take] at this
      omega

theorem MFrame.pushE {U : Uses} {n m : Nat} {er er' : Nat → Bool} {H : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res Out : Nat → Prop} (hM : MFrame P U n er H ρM ρS ρ Res Out) (hlM : oM.length = m) (hlS : oS.length = m)
    (hlF : oF.length = m) (her : ∀ i < n, er' i = er i) (hnew : ∀ k < m, er' (n + k) = true) :
    MFrame P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res Out ∧
    ∀ {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm},
      MOut P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res rets ru H' vsM vsS vs →
      MOut P U n er H ρM ρS ρ Res rets ru H' vsM vsS vs := by
  have cls := fun {i} (hi : i < n + m) => env_cls hM.lenM hM.lenS hM.lenF hlM hlS hlF hi
  have key : ∀ {i}, i < n + m → er' i = false → i < n ∧ er i = false ∧
      Tm.env (ρM ++ oM) i = Tm.env ρM i ∧ Tm.env (ρS ++ oS) i = Tm.env ρS i ∧ Tm.env (ρ ++ oF) i = Tm.env ρ i :=
    fun hi he => by
      rcases cls hi with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, -⟩
      · exact ⟨hn, by rw [← her _ hn]; exact he, e1, e2, e3⟩
      · rw [hnew k hk] at he; cases he
  have fwd : ∀ {i}, i < n → er i = false → i < n + m ∧ er' i = false ∧
      Tm.env (ρM ++ oM) i = Tm.env ρM i ∧ Tm.env (ρS ++ oS) i = Tm.env ρS i ∧ Tm.env (ρ ++ oF) i = Tm.env ρ i :=
    fun {i} hi he => by
      rcases cls (show i < n + m by omega) with ⟨_, e1, e2, e3⟩ | ⟨k, _, e, -⟩
      · exact ⟨by omega, by rw [her _ hi]; exact he, e1, e2, e3⟩
      · omega
  have liveB : ∀ a, Live P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) a → Live P U n er H ρM ρS a :=
    fun a ⟨z, hz, hU, he, hf⟩ => by
      obtain ⟨hzn, he', e1, e2, -⟩ := key hz he; rw [e1, e2] at hf; exact ⟨z, hzn, hU, he', hf⟩
  have liveF : ∀ a, Live P U n er H ρM ρS a → Live P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) a :=
    fun a ⟨z, hz, hU, he, hf⟩ => by
      obtain ⟨hzn, he', e1, e2, -⟩ := fwd hz he; exact ⟨z, hzn, hU, he', by rw [e1, e2]; exact hf⟩
  have ownB : ∀ a, Own P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) a → Own P U n er H ρM ρS ρ a :=
    fun a ⟨z, hz, hU, he, hf⟩ => by
      obtain ⟨hzn, he', e1, e2, e3⟩ := key hz he; rw [e1, e2, e3] at hf; exact ⟨z, hzn, hU, he', hf⟩
  have ownF : ∀ a, Own P U n er H ρM ρS ρ a → Own P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) a :=
    fun a ⟨z, hz, hU, he, hf⟩ => by
      obtain ⟨hzn, he', e1, e2, e3⟩ := fwd hz he; exact ⟨z, hzn, hU, he', by rw [e1, e2, e3]; exact hf⟩
  refine ⟨⟨by simp [hM.lenM, hlM], by simp [hM.lenS, hlS], by simp [hM.lenF, hlF], hM.wf, fun i hi hU he => ?_,
    fun x hx hU he => ?_, fun x hx z hz hne hUx hUz hex hez => ?_, fun x hx hU he => ?_,
    ⟨fun a ha hl => hM.res.1 a ha (liveB a hl), hM.res.2.1, fun a ha ho => hM.res.2.2.1 a ha (ownB a ho),
     hM.res.2.2.2⟩, hM.outb⟩, fun {rets ru H' vsM vsS vs} hO => ?_⟩
  · obtain ⟨hn, he', e1, e2, -⟩ := key hi he; rw [e1, e2]; exact hM.dec i hn hU he'
  · obtain ⟨hn, he', e1, e2, e3⟩ := key hx he; rw [e1, e2, e3]; exact hM.wo x hn hU he'
  · obtain ⟨hxn, hex', e1, e2, e3⟩ := key hx hex
    obtain ⟨hzn, hez', f1, f2, -⟩ := key hz hez
    rw [e1, e2, e3, f1, f2]; exact hM.sep x hxn z hzn hne hUx hUz hex' hez'
  · obtain ⟨hn, he', e1, e2, e3⟩ := key hx he; rw [e1, e2, e3]; exact hM.out x hn hU he'
  · refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha (fun h => ho (ownB a h)) hr, hO.len, hO.dec,
      fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
    · rcases hO.foot k w u hw hu he b hf with h1 | h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl (ownB b h1))
      · exact .inr (.inr (.inl h1))
      · exact .inr (.inr (.inr (liveB b h1)))
    · rcases hO.uspine k w u v hw hu hv he hr b hs with h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl (ownB b h1))
      · exact .inr (.inr h1)

theorem machine_pushE {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {c rest : Core} {ρ vs : List Tm}
    {Γ' : Ctx} {us : List Bool} {m : Nat} {oF : List Tm} {U : Uses}
    (hlF : oF.length = m) (hn' : Γ'.n = G.Γ.n + m) (her : ∀ i < G.Γ.n, Γ'.er i = G.Γ.er i)
    (hnew : ∀ k < m, Γ'.er (G.Γ.n + k) = true) (hg : Γ'.ghost = false)
    (ih : MRun P b (G.next Γ' us) ru rets rest (ρ ++ oF) vs) {K' : Caps}
    (hU' : usesCore P b (G.next Γ' us) ru rets rest = some (U, K'))
    (hrun : ∀ ρS vsS, RunS P ρS c vsS → RunS P (ρS ++ List.replicate m .tok) rest vsS)
    (hstep : ∀ H ρM pd H' out, RunM P H (ρM ++ List.replicate m .tok) none rest H' out → RunM P H ρM pd c H' out) :
    ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ → RunS P ρS c vsS →
    ∀ H ρM Res Out pd, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out → GOK P G pd H ρM ρS ρ Res →
    ∃ H' vsM, RunM P H ρM pd c H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res rets ru H' vsM vsS vs := by
  intro ρS vsS hS hr H ρM Res Out pd hM hG
  obtain ⟨hM', lift⟩ := hM.pushE (oM := List.replicate m .tok) (oS := List.replicate m .tok) (oF := oF)
    (by simp) (by simp) hlF her hnew
  have hS' : SimEnv P Γ'.er (ρS ++ List.replicate m .tok) (ρ ++ oF) :=
    hS.extend (by simp [hlF]) (fun i hi => her i (by rw [← hM.lenF]; exact hi)) fun k a b ha hb he => by
      have hk : k < m := by rw [← hlF]; exact (List.getElem?_eq_some_iff.mp hb).1
      rw [hM.lenF, hnew k hk] at he; cases he
  have hG' : GOK P (G.next Γ' us) none H (ρM ++ List.replicate m .tok) (ρS ++ List.replicate m .tok) (ρ ++ oF) Res :=
    hG.next (by omega) hM.lenM hg
  obtain ⟨H', vsM, hrr, hO⟩ := ih U K' hU' _ vsS hS' (hrun ρS vsS hr) H _ Res Out none
    (by simp only [UCtx.next]; rw [hn']; exact hM') hG'
  exact ⟨H', vsM, hstep H ρM pd H' vsM hrr, lift (by simp only [UCtx.next] at hO; rw [hn'] at hO; exact hO)⟩

theorem machine_defLvl {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {rest : Core} {ρ vs : List Tm} {v : Tm}
    (ih : MRun P b (G.next (G.adv P G.Γ.pushMint (.defLvl rest)) []) ru rets rest (ρ ++ [v]) vs) :
    MRun P b G ru rets (.defLvl rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hM hG
  have hf := hG.fill
  rw [usesCore] at hU
  refine machine_pushE (Γ' := G.adv P G.Γ.pushMint (.defLvl rest)) (m := 1) (oF := [v]) rfl
    (by rw [UCtx.adv_n' hf]; simp [Ctx.pushMint, Ctx.push, Ctx.n])
    (fun i hi => by rw [UCtx.adv_er' hf]; simp [Ctx.pushMint, Ctx.push]; omega)
    (fun k hk => by rw [UCtx.adv_er' hf]; simp [Ctx.pushMint, Ctx.push]; omega)
    (by rw [UCtx.adv_ghost' hf]; simpa [Ctx.pushMint, Ctx.push] using hG.ghost) ih hU
    (fun ρS vsS h => by cases h with | defLvl h => exact h)
    (fun H ρM pd H' out h => .defLvl h) ρS vsS hS hrun H ρM Res Out pd hM hG

theorem Ctx.pushPrim_er' (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) (i : Nat) :
    (Γ.pushPrim T er p).er i = if i = Γ.n then er else Γ.er i := by
  cases p <;> simp [Ctx.pushPrim, Ctx.push, Ctx.withRule]

theorem Ctx.pushPrim_n (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : (Γ.pushPrim T er p).n = Γ.n + 1 := by
  cases p <;> simp [Ctx.pushPrim, Ctx.push, Ctx.withRule, Ctx.n]

theorem Ctx.pushPrim_ghost (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : (Γ.pushPrim T er p).ghost = Γ.ghost := by
  cases p <;> simp [Ctx.pushPrim, Ctx.push, Ctx.withRule]

theorem machine_callE {b : Nat} {G : UCtx} {ru : List Bool} {rets f args : Tm} {dec : Dec} {ms : List Bool}
    {ve : Option (List Bool)} {rest : Core} {ρ vs oF : List Tm}
    (hlen : ∀ t outs uf, G.callee P f args = some (t, outs, uf) → outs.isTele ∧ outs.len = ms.length)
    (hlF : oF.length = ms.length)
    (ih : ∀ t outs uf, G.callee P f args = some (t, outs, uf) →
      MRun P b (G.next (G.adv P (G.Γ.pushTele outs (some (ms.map (true || ·)))) (.call f dec args true ms ve rest)) [])
        ru rets rest (ρ ++ oF) vs) :
    MRun P b G ru rets (.call f dec args true ms ve rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hM hG
  have hf := hG.fill
  rw [usesCore] at hU
  obtain ⟨⟨t, outs, uf⟩, hc, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.true_or, ite_true, Option.some.injEq, Prod.mk.injEq] at hU
  obtain ⟨rfl, rfl⟩ := hU
  obtain ⟨hR, hl⟩ := hlen t outs uf hc
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ outs (some (ms.map (true || ·))) hR
  exact machine_pushE (m := ms.length) hlF
    (by rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hR, hl])
    (fun i hi => by rw [UCtx.adv_er' hf]; exact hpo i hi)
    (fun k hk => by rw [UCtx.adv_er' hf, hpn k (by omega)]; simp; cases ms[k]? <;> rfl)
    (by rw [UCtx.adv_ghost' hf, hpg]; exact hG.ghost) (ih t outs uf hc) (by simpa using hC)
    (fun ρS vsS h => by cases h with | callE h => exact h)
    (fun H ρM pd H' out h => .callE h) ρS vsS hS hrun H ρM Res Out pd hM hG

theorem machine_mtchE {b : Nat} {G : UCtx} {ru : List Bool} {rets s R : Tm} {brs : List Br} {els : Option Core}
    {rest : Core} {ρ vs oF : List Tm} (hR : R.isTele) (hlF : oF.length = R.len)
    (ih : MRun P b (G.next (G.adv P (G.Γ.pushTele R (some (List.replicate R.len true))) (.mtch s R brs els true rest)) [])
      ru rets rest (ρ ++ oF) vs) :
    MRun P b G ru rets (.mtch s R brs els true rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hM hG
  have hf := hG.fill
  rw [usesCore] at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.true_or, ite_true, Option.some.injEq, Prod.mk.injEq] at hU
  obtain ⟨rfl, rfl⟩ := hU
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ R (some (List.replicate R.len true)) hR
  exact machine_pushE (m := R.len) hlF
    (by rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hR])
    (fun i hi => by rw [UCtx.adv_er' hf]; exact hpo i hi)
    (fun k hk => by rw [UCtx.adv_er' hf, hpn k hk]; simp [hk])
    (by rw [UCtx.adv_ghost' hf, hpg]; exact hG.ghost) ih (by simpa using hC)
    (fun ρS vsS h => by cases h with | mtchE h => exact h)
    (fun H ρM pd H' out h => .mtchE h) ρS vsS hS hrun H ρM Res Out pd hM hG

theorem machine_primE {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core} {ρ vs : List Tm}
    {v : Tm} (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim T true p) (.prim p true rest)) []) ru rets rest (ρ ++ [v]) vs) :
    MRun P b G ru rets (.prim p true rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hM hG
  have hf := hG.fill
  rw [usesCore] at hU
  obtain ⟨T, hT, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.true_or, ite_true, Option.some.injEq, Prod.mk.injEq] at hU
  obtain ⟨rfl, rfl⟩ := hU
  exact machine_pushE (m := 1) (oF := [v]) rfl
    (by rw [UCtx.adv_n' hf, Ctx.pushPrim_n])
    (fun i hi => by rw [UCtx.adv_er' hf, Ctx.pushPrim_er', if_neg (by omega)])
    (fun k hk => by rw [UCtx.adv_er' hf, Ctx.pushPrim_er', if_pos (by omega)])
    (by rw [UCtx.adv_ghost' hf, Ctx.pushPrim_ghost]; exact hG.ghost) (ih T hT) (by simpa using hC)
    (fun ρS vsS h => by cases h with | prim h => simpa using h)
    (fun H ρM pd H' out h => .prim (by simp) h) ρS vsS hS hrun H ρM Res Out pd hM hG

theorem machine_same {b : Nat} {G G' : UCtx} {ru : List Bool} {rets : Tm} {c rest : Core} {ρ vs : List Tm}
    (hΓn : G'.Γ.n = G.Γ.n) (hΓer : G'.Γ.er = G.Γ.er) (hghost : G'.Γ.ghost = G.Γ.ghost) (huq : G'.uq = G.uq)
    (hfill : G'.fill = G.fill) (huscr : G'.uscr = G.uscr) (hreb : G'.rebind = G.rebind)
    (ih : MRun P b G' ru rets rest ρ vs)
    (hu : ∀ U K, usesCore P b G ru rets c = some (U, K) → ∃ U' K', usesCore P b G' ru rets rest = some (U', K') ∧
      Uses.Eqb U' U G.Γ.n)
    (hrun : ∀ ρS vsS, RunS P ρS c vsS → RunS P ρS rest vsS)
    (hstep : ∀ H ρM pd H' out, RunM P H ρM pd rest H' out → RunM P H ρM pd c H' out) :
    MRun P b G ru rets c ρ vs := by
  intro U K hU ρS vsS hS hr H ρM Res Out pd hM hG
  obtain ⟨U', K', hU', heq⟩ := hu U K hU
  have hG' : GOK P G' pd H ρM ρS ρ Res := ⟨hG.pend, fun x hx => by rw [hΓn]; exact hG.uscr x (huscr ▸ hx),
    fun x hx => hG.rebind x (hreb ▸ hx), fun j hj => by rw [hΓn]; exact hG.uqlt j (huq ▸ hj),
    hfill.trans hG.fill, hghost.trans hG.ghost⟩
  obtain ⟨H', vsM, hrr, hO⟩ := ih U' K' hU' ρS vsS (hΓer ▸ hS) (hrun ρS vsS hr) H ρM Res Out pd
    (by rw [hΓn, hΓer]; exact hM.congr heq.symm) hG'
  rw [hΓn, hΓer] at hO
  exact ⟨H', vsM, hstep H ρM pd H' vsM hrr, hO.congr heq⟩

theorem Uses.Eqb.refl (U : Uses) (n : Nat) : Uses.Eqb U U n := fun _ _ => rfl

theorem machine_chkPlain {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {k : Chk} {rest : Core}
    {ρ vs : List Tm} (hk : k = .is ∨ k = .ty ∨ k = .rt) (ih : MRun P b G ru rets rest ρ vs) :
    MRun P b G ru rets (.chk k a x rest) ρ vs :=
  machine_same rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rcases hk with rfl | rfl | rfl <;> (rw [usesCore] at h <;> first | exact h | (intros; contradiction)), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by rcases hk with rfl | rfl | rfl <;> cases e) h)

theorem machine_cm {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {rest : Core} {ρ vs : List Tm}
    (ih : MRun P b { G with Γ := { G.Γ with cmode := true } } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk .cm a x rest) ρ vs :=
  machine_same (G' := { G with Γ := { G.Γ with cmode := true } }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h <;> first | exact h | (intros; contradiction), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by cases e) h)

theorem machine_uq {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {ms : List Bool} {rest : Core}
    {ρ vs : List Tm} (ih : MRun P b { G with ents := ms } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark (.uq ms)) a x rest) ρ vs :=
  machine_same (G' := { G with ents := ms }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h <;> first | exact h | (intros; contradiction), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by cases e; rfl) h)

theorem machine_uqScr {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {rest : Core}
    {ρ vs : List Tm} (ih : MRun P b { G with scr := true } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark .uqScr) a x rest) ρ vs :=
  machine_same (G' := { G with scr := true }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h <;> first | exact h | (intros; contradiction), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by cases e; rfl) h)

theorem machine_skip {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {rest : Core}
    {ρ vs : List Tm} (ih : MRun P b G ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark .skip) a x rest) ρ vs :=
  machine_same rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h <;> first | exact h | (intros; contradiction), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by cases e; rfl) h)

abbrev ret1 (T : Tm) : Tm := .bind (.ty false false false) T .nil

def Pend.Inert (P : Prog) (pd : Pend) (p : Prim) : Prop := ∀ H ρ, P.evalP H ρ pd p = P.evalM H ρ p

theorem machine_prim_inert {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core}
    {ρ vs : List Tm}
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P (p.evalS P ρS) (p.eval ρ))
    (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim T false p) (.prim p false rest)) [G.ents.headD false]) ru rets rest
        (ρ ++ [p.eval ρ]) vs)
    (hval : ∀ T A, G.primTy P p = some T → G.primUses P (G.ents.headD false) p = some A →
      ∀ ρS H ρM Out', SimEnv P G.Γ.er ρS ρ → MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' →
      ∃ H1 w, P.evalM H ρM p = (H1, w) ∧ MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) (ret1 T)
        [G.ents.headD false] H1 [w] [p.evalS P ρS] [p.eval ρ]) :
    ∀ U K, usesCore P b G ru rets (.prim p false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim p false rest) vsS →
    ∀ H ρM Res Out pd, Pend.Inert P pd p → MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out → GOK P G pd H ρM ρS ρ Res →
    ∃ H' vsM, RunM P H ρM pd (.prim p false rest) H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res rets ru H' vsM vsS vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out pd hin hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  obtain ⟨T, hT, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.false_or, hg, Bool.false_eq_true, ite_false] at hU hC
  obtain ⟨A, hA, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseq := UR.seq_fst hU
  simp only at hseq
  cases hrun with
  | prim hr =>
  simp only [Bool.false_eq_true, ite_false] at hr
  obtain ⟨H1, w, hev, hO⟩ := hval T A hT hA ρS H ρM _ hS (hM.split hseq)
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushPrim T false p) (.prim p false rest) := ⟨_, rfl⟩
  rw [← hΓ'] at hC
  have her' : ∀ i, Γ'.er i = if i = G.Γ.n then false else G.Γ.er i := fun i => by
    rw [hΓ', UCtx.adv_er' hf, Ctx.pushPrim_er']
  have hn' : Γ'.n = G.Γ.n + 1 := by rw [hΓ', UCtx.adv_n' hf, Ctx.pushPrim_n]
  have huq := usesCore_uq b (G.next Γ' [G.ents.headD false]) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bind hseq hO (m := 1) rfl rfl (er' := Γ'.er)
    (fun i hi => by rw [her', if_neg (by omega)])
    (fun k hk _ _ => by obtain rfl : k = 0 := by omega
                        simp [Tm.ers, Ent.er])
    (fun k hk hc _ => by
      obtain rfl : k = 0 := by omega
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
  have hS' : SimEnv P Γ'.er (ρS ++ [p.evalS P ρS]) (ρ ++ [p.eval ρ]) :=
    hS.extend rfl (fun i hi => by rw [her', if_neg (by rw [← hM.lenF]; omega)]) fun k a b ha hb _ => by
      cases k with
      | zero => simp at ha hb; subst ha hb; exact hreal ρS hS
      | succ k => simp at ha
  have ihT := ih T hT
  rw [← hΓ'] at ihT
  obtain ⟨H', vsM, hrr, hOr⟩ := ihT CU CK hC (ρS ++ [p.evalS P ρS]) vsS hS' hr H1 (ρM ++ [w]) Res Out none
    (by simp only [UCtx.next]; rw [hn']; exact hMr) (hG.next (by omega) hM.lenM (by
      rw [hΓ', UCtx.adv_ghost' hf, Ctx.pushPrim_ghost]; exact hg))
  refine ⟨H', vsM, .prim (by simp only [Bool.false_eq_true, ite_false]; rw [hin]; exact hev) hrr, lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem prim_val_tm (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {t T : Tm} {u : Bool} {A : Uses}
    (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrt : rt P G.Γ t = true) (hA : G.termUses P u t = some A)
    {H : Heap} {Out' : Nat → Prop} (hM : MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out') :
    ∃ H1 w, P.build H (Tm.env ρM) t = (H1, w) ∧
      MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) (ret1 T) [u] H1 [w] [P.sub ρS t] [t.subst (Tm.env ρ)] := by
  obtain ⟨H', vsM, hr, hO⟩ := machine_ret hP (ts := .cons t .nil) (rets := ret1 T) (by simp [rtArgs, Ent.er, hrt])
    hE hS rfl (ru := [u]) (U := A) (by simp [UCtx.retUses, Ent.er, hA, Uses.seq]) hM none
  cases hr with
  | ret hb =>
  simp only [Tm.toList, Prog.buildList, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨_, _, rfl, by simpa [Tm.toList] using hO⟩

theorem MOut.imm {A : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Out' : Nat → Prop}
    (hM : MFrame P A n er H ρM ρS ρ (fun _ => False) Out') {T w uS v : Tm} {u : Bool} (hd : MDec P H w uS)
    (hf : ∀ b, ¬ Foot P H w uS b) :
    MOut P A n er H ρM ρS ρ (fun _ => False) (ret1 T) [u] H [w] [uS] [v] := by
  have hsp : ∀ b, ¬ Spine P H w uS v b := fun b h => hf b h.foot
  refine ⟨hM.wf, Nat.le_refl _, fun _ h => h, fun _ _ _ _ => rfl, rfl, fun k w' u' hw hu _ => ?_,
    fun k w' u' hw hu _ b h => ?_, fun k w' u' v' hw hu hv _ _ b h => ?_, fun k w' u' v' hw hu hv _ _ => ?_,
    fun k j _ _ _ _ _ hne hw _ _ hw' _ _ _ _ => ?_⟩
  all_goals first
    | (cases k with
        | zero => simp at hw hu; subst hw hu; first | exact hd | exact (hf b h).elim
        | succ k => simp at hw)
    | skip
  · cases k with
    | zero => simp at hw hu hv; subst hw hu hv; exact (hsp b h).elim
    | succ k => simp at hw
  · cases k with
    | zero => simp at hw hu hv; subst hw hu hv; exact .free hsp
    | succ k => simp at hw
  · cases k <;> cases j <;> simp_all

theorem prim_val (hP : ProgOK P) {G : UCtx} {ρ : List Tm} {p : Prim} (hE : EnvOK P ρ G.Γ)
    (hrt : p.rt P G.Γ = true) (hnc : ∀ a b q, p ≠ .coerce a b q) :
    ∀ T A, G.primTy P p = some T → G.primUses P (G.ents.headD false) p = some A →
      ∀ ρS H ρM Out', SimEnv P G.Γ.er ρS ρ → MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' →
      ∃ H1 w, P.evalM H ρM p = (H1, w) ∧ MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) (ret1 T)
        [G.ents.headD false] H1 [w] [p.evalS P ρS] [p.eval ρ] := by
  intro T A _ hA ρS H ρM Out' hS hM
  cases p with
  | tm t =>
    obtain ⟨H1, w, hb, hO⟩ := prim_val_tm hP hE hS (by simpa [Prim.rt] using hrt) hA hM
    exact ⟨H1, w, hb, hO⟩
  | lit t =>
    simp only [UCtx.primUses] at hA
    split at hA
    · cases hA
    · rename_i hu
      simp only [Bool.not_eq_true] at hu
      obtain ⟨H1, w, hb, hO⟩ := prim_val_tm hP hE hS (by simpa [Prim.rt] using hrt) hA hM
      exact ⟨H1, w, hb, by rw [hu]; exact hO⟩
  | coerce a b q => exact (hnc a b q rfl).elim
  | num d k => exact ⟨H, _, rfl, MOut.imm hM .nat fun b h => by cases h⟩
  | atom d => exact ⟨H, _, rfl, MOut.imm hM .imm fun b h => by cases h⟩
  | axm A' => exact ⟨H, _, rfl, MOut.imm hM (.tok (.inl rfl)) fun b h => by cases h⟩
  | mtblOf d ls => exact ⟨H, _, rfl, MOut.imm hM (.tok (.inl rfl)) fun b h => by cases h⟩
  | _ => simp [Prim.rt] at hrt

theorem MFrame.bindR {R0 : Nat → Prop} {U A C : Uses} {n m : Nat} {er er' : Nat → Bool} {H H' : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res Out : Nat → Prop} {rets : Tm} {ru : List Bool}
    (hM : MFrame P U n er H ρM ρS ρ Res Out) (h : Uses.seq A C = some U)
    (hO : MOut P A n er H ρM ρS ρ (fun _ => False) rets ru H' oM oS oF) (hlS : oS.length = m) (hlF : oF.length = m)
    (her : ∀ i < n, er' i = er i)
    (hers : ∀ k < m, (C.lookup (n + k)).isSome → er' (n + k) = false → rets.ers.getD k true = false)
    (hu : ∀ k < m, C.lookup (n + k) = some true → er' (n + k) = false → ru.getD k false = true)
    (hR0 : ∀ a, R0 a → H.next ≤ a ∨ Own P A n er H ρM ρS ρ a) (hR0b : ∀ a, R0 a → (H'.blk a).isSome)
    (hR0n : ∀ k w u, k < m → oM[k]? = some w → oS[k]? = some u → (C.lookup (n + k)).isSome → er' (n + k) = false →
      ∀ b, Foot P H' w u b → ¬ R0 b) :
    MFrame P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) (fun a => Res a ∨ R0 a) Out ∧
    ∀ {H'' : Heap} {vsM vsS vs : List Tm} {rets2 : Tm} {ru2 : List Bool},
      MOut P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) (fun a => Res a ∨ R0 a) rets2 ru2 H'' vsM vsS vs →
      MOut P U n er H ρM ρS ρ Res rets2 ru2 H'' vsM vsS vs := by
  obtain ⟨sA, sC⟩ := Uses.seq_sub h
  have hfree := (Uses.seq_spec h).1
  have hlM : oM.length = m := by rw [hO.len, hlS]
  have cls := fun {i} (hi : i < n + m) => env_cls hM.lenM hM.lenS hM.lenF hlM hlS hlF hi
  have er_old : ∀ {i}, i < n → er' i = false → er i = false := fun hi he => by rw [← her _ hi]; exact he
  have hOwn : ∀ i < n, (C.lookup i).isSome → er i = false → ∀ b, Foot P H (Tm.env ρM i) (Tm.env ρS i) b →
      ¬ Own P A n er H ρM ρS ρ b := fun i hi hC hei b hf ⟨x, hx, hA, hex, hs⟩ => by
    have hne : x ≠ i := fun e => by subst e; rw [(hfree x).1 hA] at hC; cases hC
    exact hM.sep x hx i hi hne (sA.2 x hA) (sC.1 i hC) hex hei b hs hf
  have hAg : ∀ i < n, (C.lookup i).isSome → er i = false → Agree H H' (Foot P H (Tm.env ρM i) (Tm.env ρS i)) :=
    fun i hi hC he b hf => hO.keep b (Foot.lt hM.wf (hM.dec i hi (sC.1 i hC) he) hf) (hOwn i hi hC he b hf) id
  have hRes : ∀ a, Res a → ¬ Own P A n er H ρM ρS ρ a := fun a ha ho => hM.res.2.2.1 a ha (ho.mono sA)
  have hResLt : ∀ a, Res a → a < H.next := fun a ha => by
    have := hM.res.2.2.2 a ha
    exact Nat.lt_of_not_le fun hc => by rw [hM.wf a hc] at this; cases this
  have newSp : ∀ k w u v, k < m → oM[k]? = some w → oS[k]? = some u → oF[k]? = some v →
      C.lookup (n + k) = some true → er' (n + k) = false → ∀ b, Spine P H' w u v b →
      H.next ≤ b ∨ Own P A n er H ρM ρS ρ b :=
    fun k w u v hk hw hu' hv hC he b hs => by
      rcases hO.uspine k w u v hw hu' hv (hers k hk (by simp [hC]) he) (hu k hk hC he) b hs with h | h | h
      · exact .inl h
      · exact .inr h
      · exact h.elim
  have newFt : ∀ k w u, k < m → oM[k]? = some w → oS[k]? = some u → (C.lookup (n + k)).isSome →
      er' (n + k) = false → ∀ b, Foot P H' w u b →
      H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Live P A n er H ρM ρS b :=
    fun k w u hk hw hu' hC he b hf => by
      rcases hO.foot k w u hw hu' (hers k hk hC he) b hf with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
      · exact .inr (.inr h)
  have oldSp : ∀ x < n, C.lookup x = some true → er x = false →
      ∀ b, Spine P H' (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b →
      Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b :=
    fun x hx hC he b hs => Spine.bwd (hAg x hx (by simp [hC]) he).spine hs
  have oldFt : ∀ z < n, (C.lookup z).isSome → er z = false → ∀ b, Foot P H' (Tm.env ρM z) (Tm.env ρS z) b →
      Foot P H (Tm.env ρM z) (Tm.env ρS z) b := fun z hz hC he b hf => Foot.bwd (hAg z hz hC he) hf
  have hLive : ∀ a, Live P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) a → H.next ≤ a ∨ Own P A n er H ρM ρS ρ a ∨
      Live P U n er H ρM ρS a := fun a ⟨z, hz, hC, hez, hf⟩ => by
    rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
    · rw [f1, f2] at hf
      have he := er_old hzn hez
      exact .inr (.inr ⟨z, hzn, sC.1 z hC, he, oldFt z hzn hC he a hf⟩)
    · rcases newFt j _ _ hj f1 f2 hC hez a hf with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (h.mono sA))
  have hOwnC : ∀ a, Own P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) a →
      H.next ≤ a ∨ Own P U n er H ρM ρS ρ a := fun a ⟨x, hx, hC, hex, hs⟩ => by
    rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · rw [e1, e2, e3] at hs
      have he := er_old hxn hex
      exact .inr ⟨x, hxn, sC.2 x hC, he, oldSp x hxn hC he a hs⟩
    · rcases newSp k _ _ _ hk e1 e2 e3 hC hex a hs with h | h
      · exact .inl h
      · exact .inr (h.mono sA)
  refine ⟨?_, fun {H'' vsM vsS vs rets2 ru2} hR => ?mo⟩
  case mo =>
    have hext : ∀ a, a < H.next → ¬ Own P U n er H ρM ρS ρ a → ¬ Res a → H'.blk a = H.blk a :=
      fun a ha ho hr => hO.keep a ha (fun h => ho (h.mono sA)) id
    refine ⟨hR.wf, Nat.le_trans hO.next hR.next, fun a ha => hR.blk a (hO.blk a ha), fun a ha ho hr => ?_, hR.len,
      hR.dec, fun k w u hw hu' he b hf => ?_, fun k w u v hw hu' hv he hr b hs => ?_, hR.uwo, hR.usep⟩
    · have hr0 : ¬ R0 a := fun h0 => by
        rcases hR0 a h0 with h0 | h0
        · omega
        · exact ho (h0.mono sA)
      rw [hR.keep a (Nat.lt_of_lt_of_le ha hO.next) (fun h => by
          rcases hOwnC a h with h | h
          · omega
          · exact ho h) (fun h => h.elim hr hr0), hext a ha ho hr]
    · rcases hR.foot k w u hw hu' he b hf with h | h | h | h
      · exact .inl (Nat.le_trans hO.next h)
      · rcases hOwnC b h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rcases h with h | h
        · exact .inr (.inr (.inl h))
        · rcases hR0 b h with h | h
          · exact .inl h
          · exact .inr (.inl (h.mono sA))
      · rcases hLive b h with h | h | h
        · exact .inl h
        · exact .inr (.inl (h.mono sA))
        · exact .inr (.inr (.inr h))
    · rcases hR.uspine k w u v hw hu' hv he hr b hs with h | h | h
      · exact .inl (Nat.le_trans hO.next h)
      · rcases hOwnC b h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rcases h with h | h
        · exact .inr (.inr h)
        · rcases hR0 b h with h | h
          · exact .inl h
          · exact .inr (.inl (h.mono sA))
  refine ⟨by simp [hM.lenM, hlM], by simp [hM.lenS, hlS], by simp [hM.lenF, hlF], hO.wf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hC he
    rcases cls hi with ⟨hn, e1, e2, -⟩ | ⟨k, hk, rfl, e1, e2, -⟩
    · have he' := er_old hn he
      rw [e1, e2]; exact (hM.dec i hn (sC.1 i hC) he').frame (hAg i hn hC he')
    · exact hO.dec k _ _ e1 e2 (hers k hk hC he)
  · intro x hx hC he
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3]; exact (hM.wo x hn (sC.2 x hC) he').fwd (hAg x hn (by simp [hC]) he')
    · exact hO.uwo k _ _ _ e1 e2 e3 (hers k hk (by simp [hC]) he) (hu k hk hC he)
  · intro x hx z hz hne hCx hCz hex hez b h1 h2
    rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩ <;>
      rcases cls hz with ⟨hzn, f1, f2, f3⟩ | ⟨j, hj, rfl, f1, f2, f3⟩
    · rw [e1, e2, e3] at h1; rw [f1, f2] at h2
      have hex' := er_old hxn hex
      have hez' := er_old hzn hez
      exact hM.sep x hxn z hzn hne (sC.2 x hCx) (sC.1 z hCz) hex' hez' b (oldSp x hxn hCx hex' b h1)
        (oldFt z hzn hCz hez' b h2)
    · rw [e1, e2, e3] at h1
      have hex' := er_old hxn hex
      have hs := oldSp x hxn hCx hex' b h1
      have hlt := Foot.lt hM.wf (hM.dec x hxn (sC.1 x (by simp [hCx])) hex') hs.foot
      have hAx : A.lookup x = none := (hfree x).2 (sC.2 x hCx ▸ hCx)
      rcases newFt j _ _ hj f1 f2 hCz hez b h2 with h | ⟨y, hy, hAy, hey, hsy⟩ | ⟨w, hw, hAw, hew, hfw⟩
      · omega
      · have hne' : y ≠ x := fun e => by subst e; rw [hAx] at hAy; cases hAy
        exact hM.sep y hy x hxn hne' (sA.2 y hAy) (sC.1 x (by simp [hCx])) hey hex' b hsy hs.foot
      · have hne' : x ≠ w := fun e => by subst e; rw [hAx] at hAw; cases hAw
        exact hM.sep x hxn w hw hne' (sC.2 x hCx) (sA.1 w hAw) hex' hew b hs hfw
    · rw [f1, f2] at h2
      have hez' := er_old hzn hez
      have hf := oldFt z hzn hCz hez' b h2
      rcases newSp k _ _ _ hk e1 e2 e3 hCx hex b h1 with h | ho
      · have := Foot.lt hM.wf (hM.dec z hzn (sC.1 z hCz) hez') hf; omega
      · exact hOwn z hzn hCz hez' b hf ho
    · exact hO.usep k j _ _ _ _ _ (fun e => hne (by rw [e])) e1 e2 e3 f1 f2 (hers k hk (by simp [hCx]) hex)
        (hers j hj hCz hez) (hu k hk hCx hex) b h1 h2
  · intro x hx hC he b h1 h2
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3] at h1; exact hM.out x hn (sC.2 x hC) he' b (oldSp x hn hC he' b h1) h2
    · rcases newSp k _ _ _ hk e1 e2 e3 hC he b h1 with h | ⟨y, hy, hAy, hey, hsy⟩
      · have := hM.outb b h2; omega
      · exact hM.out y hy (sA.2 y hAy) hey b hsy h2
  · have r0Live : ∀ a, R0 a → Live P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) a → False := fun a h0 ⟨z, hz, hC, hez, hf⟩ => by
      rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
      · rw [f1, f2] at hf
        have he := er_old hzn hez
        have hf' := oldFt z hzn hC he a hf
        rcases hR0 a h0 with h1 | h1
        · have := Foot.lt hM.wf (hM.dec z hzn (sC.1 z hC) he) hf'; omega
        · exact hOwn z hzn hC he a hf' h1
      · exact hR0n j _ _ hj f1 f2 hC hez a hf h0
    refine ⟨fun a ha hl => ?_, fun a ha ho => ?_, fun a ha ⟨x, hx, hC, hex, hs⟩ => ?_, fun a ha => ?_⟩
    · rcases ha with ha | ha
      · rcases hLive a hl with h | h | h
        · have := hResLt a ha; omega
        · exact hRes a ha h
        · exact hM.res.1 a ha h
      · exact r0Live a ha hl
    · rcases ha with ha | ha
      · exact hM.res.2.1 a ha ho
      · rcases hR0 a ha with h | ⟨x, hx, hA, hex, hs⟩
        · have := hM.outb a ho; omega
        · exact hM.out x hx (sA.2 x hA) hex a hs ho
    · rcases ha with ha | ha
      · rcases hLive a ⟨x, hx, by simp [hC], hex, hs.foot⟩ with h | h | h
        · have := hResLt a ha; omega
        · exact hRes a ha h
        · exact hM.res.1 a ha h
      · exact r0Live a ha ⟨x, hx, by simp [hC], hex, hs.foot⟩
    · rcases ha with ha | ha
      · rw [hO.keep a (hResLt a ha) (hRes a ha) id]; exact hM.res.2.2.2 a ha
      · exact hR0b a ha
  · intro a ha; exact Nat.lt_of_lt_of_le (hM.outb a ha) hO.next

end Minimal
