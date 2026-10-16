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

theorem UqOK.of_n {G G' : UCtx} {U : Uses} (h : UqOK G' U) (hu : G'.uq = G.uq) (hn : G'.Γ.n = G.Γ.n) : UqOK G U :=
  fun i hi => by rw [← hu, ← hn]; exact h i hi

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
  | _, .clo .., _, h | _, .nat _, _, h | _, .ptr _, _, h | _, .vc .., _, h | _, .sfv _, _, h => by
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
  | md, .cons _ _, .nat _, A, h | md, .cons _ _, .ptr _, A, h | md, .cons _ _, .wld _, A, h
  | md, .cons _ _, .sfv _, A, h | md, .cons _ _, .sbv _, A, h
  | md, .nil, _, A, h | md, .fv _, _, A, h | md, .bv _, _, A, h | md, .bind .., _, A, h | md, .app .., _, A, h
  | md, .tyc .., _, A, h | md, .vc .., _, A, h | md, .tyCtor _, _, A, h | md, .valCtor _, _, A, h
  | md, .univ, _, A, h | md, .level, _, A, h | md, .predates .., _, A, h | md, .subterm .., _, A, h
  | md, .fn .., _, A, h | md, .mtbl .., _, A, h | md, .lvl _, _, A, h | md, .tok, _, A, h
  | md, .clo .., _, A, h | md, .nat _, _, A, h | md, .ptr _, _, A, h | md, .wld _, _, A, h | md, .sfv _, _, A, h | md, .sbv _, _, A, h => by
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

theorem Ctx.pushPrim_n_le (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : Γ.n ≤ (Γ.pushPrim P T er p).n := by
  cases p <;> simp [Ctx.pushPrim, Ctx.pushPrim0, Ctx.push, Ctx.withRule, Ctx.n]

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

theorem Ctx.branch_fields (Γ : Ctx) (s k H idx sig : Tm) :
    (Γ.branch P s k H idx sig).1.ghost = (Γ.openTele sig (sig.len - 1)).1.ghost ∧
    (Γ.branch P s k H idx sig).1.er = (Γ.openTele sig (sig.len - 1)).1.er ∧
    (Γ.branch P s k H idx sig).1.n = (Γ.openTele sig (sig.len - 1)).1.n := by
  rcases h : Γ.openTele sig (sig.len - 1) with ⟨Γf, rem⟩
  obtain ⟨g1, e1, n1⟩ := Ctx.ntSlot_fields P Γ Γf s k
  simp only [Ctx.branch, h]
  split
  · split
    · simp only [Ctx.forceSlots_ghost, Ctx.forceSlots_er, Ctx.forceSlots_n]; exact ⟨g1, e1, n1⟩
    · exact ⟨g1, e1, n1⟩
  · exact ⟨g1, e1, n1⟩

theorem branchCtx_spec {G Gb : UCtx} {s k H idx sig : Tm} {fe ph uscr cell : Bool}
    (h : G.branchCtx P s k H idx sig fe ph uscr cell = some Gb) :
    G.Γ.n ≤ Gb.Γ.n ∧ (∀ i < G.Γ.n, Gb.uq.contains i = true → G.uq.contains i = true) ∧ Gb.fill = G.fill := by
  unfold UCtx.branchCtx at h
  simp only at h
  rcases hb : Ctx.branch P { G.Γ with ghost := G.Γ.ghost || ph } s k H idx sig with ⟨Γf, r⟩
  have hf := (Ctx.branch_fields { G.Γ with ghost := G.Γ.ghost || ph } s k H idx sig).2.2
  rw [hb] at hf; dsimp only at hf
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
  all_goals first
    | exact termUses_uq h
    | (cases h; exact UqOK.nil)
    | (obtain ⟨⟨su, tu⟩, -, h2⟩ := Option.bind_eq_some_iff.mp h
       simp only at h2; split at h2
       · cases h2
       · exact termUses_uq h2)
    | (split at h
       · cases h
       · first | exact termUses_uq h | (cases h; exact UqOK.nil))

theorem usesCore_uq (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) (c : Core) :
    G.fill = false → ∀ U K, usesCore P b G ru rets c = some (U, K) → UqOK G U := by
  induction b, G, ru, rets, c using usesCore.induct (P := P) (motive2 := fun _ _ _ _ => True)
    (motive3 := fun b G ru R s els => G.fill = false → ∀ U K, usesEls P b G ru R s els = some (U, K) → UqOK G U)
    (motive4 := fun b G ru R s H idx shp fe cell brs => G.fill = false → ∀ U K,
      usesArms P b G ru R s H idx shp fe cell brs = some (U, K) → UqOK G U)
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
        let B ← usesArms P b G ru rets s H idx shp er (!nt) brs
        let E ← usesEls P b { G with scr := G.scr && !er } ru rets s els
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
  case case9 b G ru rets w req rest ih =>
    obtain ⟨Tw, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨A, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC0 := ih Tw A
    simp only [dite_eq_ite] at hC0
    have hC' : UqOK G CU := UqOK.next (by rw [UCtx.adv_n' hf]; simp) (hC0 hf CU CK hC)
    split at h
    · cases h; exact hC'
    · split at h
      · obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨Y, hY, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨S, hS, h⟩ := Option.bind_eq_some_iff.mp h
        exact UqOK.ur_seq h (UqOK.seq hS (termUses_uq hX) (termUses_uq hY)) hC'
      · cases h
  case case10 b G ru rets rest ih =>
    exact UqOK.next (by rw [UCtx.adv_n' hf]; simp [Ctx.pushMint, Ctx.push, Ctx.n]) (ih hf U K h)
  case case11 b G ru rets gid rest ihr ihf =>
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
        simp only [UCtx.defOK, Bool.and_eq_true, List.all_eq_true] at hc
        refine UqOK.ur_seq h (fun i hi => ?_) hC'
        obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp (hc.1.1.2 _ hi)
        exact UqOK.use hA i (by simp only [UCtx.use] at hA; split at hA <;> cases hA; simp)
      · cases h
    · cases h
  case case12 b G ru rets a b1 rest ms ih => exact ih hf U K h
  case case13 b G ru rets a b1 rest ih => exact ih hf U K h
  case case14 b G ru rets a b1 p rest ih => exact ih hf U K h
  case case15 b G ru rets a b1 t rest' hr ih =>
    rw [if_pos hr] at h
    obtain ⟨T, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact UqOK.next (by rw [UCtx.adv_n' hf]; exact Ctx.pushPrim_n_le ..) (ih T hf U K h)
  case case16 =>
    rename_i h1 h2
    first | (rw [if_neg h1] at h; exact h2 hf U K h) | (rw [if_neg h2] at h; exact h1 hf U K h)
  case case17 => cases h
  case case19 b G ru rets b1 rest u i hc ih =>
    rw [if_neg hc] at h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC' : UqOK G _ := UqOK.of_n (G := G) (ih hf _ _ hC) rfl (by simp)
    split at h
    · cases h; exact hC'
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.use hA) hC'
  case case21 b G ru rets b1 rest u i hc ih =>
    rw [if_neg hc] at h
    obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
    have hC' : UqOK G _ := UqOK.of_n (G := G) (ih hf _ _ hC) rfl (by simp)
    split at h
    · cases h; exact hC'
    · obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      exact UqOK.ur_seq h (UqOK.use hA) hC'
  case case22 b G ru rets a b1 rest ih => exact ih hf U K h
  case case23 b G ru rets b1 rest x hc ih => rw [if_pos hc] at h; exact UqOK.of_n (G := G) (ih hf U K h) rfl (by simp)
  case case24 b G ru rets b1 rest x hc => rw [if_neg hc] at h; cases h
  case case18 b G ru rets b1 rest u i hc => rw [if_pos hc] at h; cases h
  case case20 b G ru rets b1 rest u i hc => rw [if_pos hc] at h; cases h
  case case25 => rename_i ih; exact ih hf U K h
  case case26 =>
    rename_i Γo u nt ex ph H cs hm σ' hu ih
    simp only [hm] at h
    simp only [Γo] at hu
    simp only [hu] at h
    exact ih hf U K h
  case case27 =>
    rename_i Γo u nt ex ph H cs hm hu
    simp only [hm] at h
    simp only [Γo] at hu
    split at h
    · exact (hu _ ‹_›).elim
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case28 =>
    rename_i hm
    split at h
    · exact (hm _ _ _ _ _ _ ‹_›).elim
    · cases h
  case case29 => rename_i ih; exact ih hf U K h
  case case30 =>
    rename_i hΓ ih; simp only [hΓ] at h
    have e := Ctx.slotSelf_eq hΓ; have := ih hf U K h; rw [e] at this; exact this
  case case31 => rename_i hΓ; simp only [hΓ] at h; cases h
  case case32 => rename_i ih; exact ih hf U K h
  case case33 => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case34 => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case37 =>
    rename_i hf U K h
    rw [usesEls] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case38 =>
    rename_i ih hf U K h
    rw [usesEls] at h
    obtain ⟨⟨EU, EK⟩, hE, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact UqOK.below (Nat.le_refl _) (fun _ _ h => h) (ih hf EU EK hE)
  case case39 =>
    rename_i hf U K h
    rw [usesArms] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact UqOK.nil
  case case40 b G ru R s H idx shp fe cell f1 c f2 body brs k sig ph hshp Gb hbr ihr ihb hf U K h =>
    rw [usesArms] at h
    simp only [hshp, hbr] at h
    obtain ⟨⟨BU, BK⟩, hB, h⟩ := Option.bind_eq_some_iff.mp h
    rcases hR : usesArms P b G ru R s H idx shp fe cell brs with _ | ⟨RU, RK⟩ <;> rw [hR] at h
    · cases h

    simp only [bind, Option.bind, Option.some.injEq, UR.join, UR.below, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hn, huq, hfb⟩ := branchCtx_spec hbr
    exact UqOK.join (UqOK.below hn huq (ihb (hfb.trans hf) BU BK hB)) (ihr hf RU RK hR)
  case case41 b G ru R s H idx shp fe cell f1 c f2 body brs k sig ph hshp hbr ihr hf U K h =>
    rw [usesArms] at h
    simp only [hshp] at h
    rcases hR : usesArms P b G ru R s H idx shp fe cell brs with _ | ⟨RU, RK⟩ <;> rw [hR] at h
    · cases h
    simp only [bind, Option.bind, Option.some.injEq, UR.join, UR.below, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact UqOK.join UqOK.nil (ihr hf RU RK hR)
  case case42 =>
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
    {Res Out Shr : Nat → Prop} (hM : MFrame P A n er H ρM ρS ρ Res Out Shr) : MFrame P B n er H ρM ρS ρ Res Out Shr :=
  ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, fun i hi hb he => hM.dec i hi (by rw [h i hi]; exact hb) he,
   fun x hx hb he => hM.wo x hx (by rw [h x hx]; exact hb) he,
   fun x hx z hz hne hbx hbz hex hez => hM.sep x hx z hz hne (by rw [h x hx]; exact hbx) (by rw [h z hz]; exact hbz) hex hez,
   fun x hx hb he => hM.out x hx (by rw [h x hx]; exact hb) he,
   ⟨fun a ha hl => hM.res.1 a ha (hl.congr h.symm), hM.res.2.1, fun a ha ho => hM.res.2.2.1 a ha (ho.congr h.symm),
    hM.res.2.2.2⟩, hM.outb, ⟨hM.shr.1, fun x hx hb he => hM.shr.2.1 x hx (by rw [h x hx]; exact hb) he, hM.shr.2.2⟩⟩

theorem MOut.congr {A B : Uses} {n : Nat} (h : Uses.Eqb A B n) {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm}
    {Res Shr : Nat → Prop} {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (hO : MOut P A n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs) : MOut P B n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha (fun h' => ho (h'.congr h)) hr, hO.len, hO.dec,
    fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
  · rcases hO.foot k w u hw hu he b hf with h1 | h1 | h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (h1.congr h))
    · exact .inr (.inr (.inl h1))
    · exact .inr (.inr (.inr (.inl (h1.congr h))))
    · exact .inr (.inr (.inr (.inr h1)))
  · rcases hO.uspine k w u v hw hu hv he hr b hs with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (h1.congr h))
    · exact .inr (.inr h1)

def MRun (P : Prog) (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) (c : Core) (ρ vs : List Tm) : Prop :=
  ∀ U K, usesCore P b G ru rets c = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ → RunS P ρS c vsS →
    ∀ H ρM Res Out Shr pd, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G pd H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM pd c H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs

theorem machine_seq {b : Nat} {G : UCtx} {ru : List Bool} {rets R : Tm} {body rest : Core} {ρ outs vs : List Tm}
    (hR : R.isTele) (hol : outs.length = R.len)
    (hsb : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∃ outsS, RunS P ρS body outsS ∧ Reals P (.ofList outsS) (.ofList outs) R)
    (ihb : MRun P b { G with ents := [], uscr := none, cellOk := false, rebind := none } G.ents R body ρ outs)
    (ihr : MRun P b (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents))
      ru rets rest (ρ ++ outs) vs) :
    MRun P b G ru rets (.seq R body rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
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
  have hGb : GOK P { G with ents := [], uscr := none, cellOk := false, rebind := none } none H ρM ρS ρ (fun _ => False) Shr :=
    ⟨.inl rfl, fun _ h => (by cases h), fun _ h => (by cases h), hG.uqlt, hG.fill, hG.ghost⟩
  obtain ⟨H1, oM, hrb, hOb⟩ := ihb BU BK hB ρS outsS hS hb H ρM _ _ Shr none hMb hGb
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
  have hGr : GOK P (G.next Γ' (if G.Γ.ghost then [] else G.ents)) none H1 (ρM ++ oM) (ρS ++ outsS) (ρ ++ outs) Res Shr := by
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
      (G.next Γ' (if G.Γ.ghost then [] else G.ents)).Γ.er H1 (ρM ++ oM) (ρS ++ outsS) (ρ ++ outs) Res Out Shr := by
    simp only [UCtx.next]; rw [hn']; exact hMr
  obtain ⟨H', vsM, hrr, hOr⟩ := ihr CU CK hC (ρS ++ outsS) vsS hS' hr H1 (ρM ++ oM) Res Out Shr none hMr' hGr
  refine ⟨H', vsM, .seq hrb hrr, lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem GOK.nextR {G : UCtx} {Γ' : Ctx} {us : List Bool} {pd : Pend} {H H' : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res R2 Shr : Nat → Prop} (hG : GOK P G pd H ρM ρS ρ Res Shr)
    (hR : ∀ x a, G.uscr = some (.fv x) → Tm.env ρM x = .ptr a → R2 a) (hn : G.Γ.n ≤ Γ'.n) (hl : ρM.length = G.Γ.n)
    (hg : Γ'.ghost = false) : GOK P (G.next Γ' us) none H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) R2 Shr := by
  refine ⟨.inl rfl, fun x hx => ?_, fun _ h => (by cases h), fun j hj => ?_, hG.fill, hg⟩
  · have hxn := (hG.uscr x hx).1
    refine ⟨by simp only [UCtx.next]; omega, fun a ha => hR x a hx ?_⟩
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

theorem GOK.next {G : UCtx} {Γ' : Ctx} {us : List Bool} {pd : Pend} {H H' : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res Shr : Nat → Prop} (hG : GOK P G pd H ρM ρS ρ Res Shr) (hn : G.Γ.n ≤ Γ'.n) (hl : ρM.length = G.Γ.n)
    (hg : Γ'.ghost = false) : GOK P (G.next Γ' us) none H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res Shr :=
  hG.nextR (fun x a hx ha => (hG.uscr x hx).2 a ha) hn hl hg

theorem MFrame.pushE {U : Uses} {n m : Nat} {er er' : Nat → Bool} {H : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res Out Shr : Nat → Prop} (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (hlM : oM.length = m) (hlS : oS.length = m)
    (hlF : oF.length = m) (her : ∀ i < n, er' i = er i) (hnew : ∀ k < m, er' (n + k) = true) :
    MFrame P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res Out Shr ∧
    ∀ {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm},
      MOut P U (n + m) er' H (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res Shr rets ru H' vsM vsS vs →
      MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
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
     hM.res.2.2.2⟩, hM.outb, ⟨hM.shr.1, fun x hx hU he => ?_, hM.shr.2.2⟩⟩, fun {rets ru H' vsM vsS vs} hO => ?_⟩
  · obtain ⟨hn, he', e1, e2, -⟩ := key hi he; rw [e1, e2]; exact hM.dec i hn hU he'
  · obtain ⟨hn, he', e1, e2, e3⟩ := key hx he; rw [e1, e2, e3]; exact hM.wo x hn hU he'
  · obtain ⟨hxn, hex', e1, e2, e3⟩ := key hx hex
    obtain ⟨hzn, hez', f1, f2, -⟩ := key hz hez
    rw [e1, e2, e3, f1, f2]; exact hM.sep x hxn z hzn hne hUx hUz hex' hez'
  · obtain ⟨hn, he', e1, e2, e3⟩ := key hx he; rw [e1, e2, e3]; exact hM.out x hn hU he'
  · obtain ⟨hn, he', e1, e2, e3⟩ := key hx he; rw [e1, e2, e3]; exact hM.shr.2.1 x hn hU he'
  · refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha (fun h => ho (ownB a h)) hr, hO.len, hO.dec,
      fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
    · rcases hO.foot k w u hw hu he b hf with h1 | h1 | h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl (ownB b h1))
      · exact .inr (.inr (.inl h1))
      · exact .inr (.inr (.inr (.inl (liveB b h1))))
      · exact .inr (.inr (.inr (.inr h1)))
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
    ∀ H ρM Res Out Shr pd, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G pd H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM pd c H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  intro ρS vsS hS hr H ρM Res Out Shr pd hM hG
  obtain ⟨hM', lift⟩ := hM.pushE (oM := List.replicate m .tok) (oS := List.replicate m .tok) (oF := oF)
    (by simp) (by simp) hlF her hnew
  have hS' : SimEnv P Γ'.er (ρS ++ List.replicate m .tok) (ρ ++ oF) :=
    hS.extend (by simp [hlF]) (fun i hi => her i (by rw [← hM.lenF]; exact hi)) fun k a b ha hb he => by
      have hk : k < m := by rw [← hlF]; exact (List.getElem?_eq_some_iff.mp hb).1
      rw [hM.lenF, hnew k hk] at he; cases he
  have hG' : GOK P (G.next Γ' us) none H (ρM ++ List.replicate m .tok) (ρS ++ List.replicate m .tok) (ρ ++ oF) Res Shr :=
    hG.next (by omega) hM.lenM hg
  obtain ⟨H', vsM, hrr, hO⟩ := ih U K' hU' _ vsS hS' (hrun ρS vsS hr) H _ Res Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hM') hG'
  exact ⟨H', vsM, hstep H ρM pd H' vsM hrr, lift (by simp only [UCtx.next] at hO; rw [hn'] at hO; exact hO)⟩

theorem machine_defLvl {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {rest : Core} {ρ vs : List Tm} {v : Tm}
    (ih : MRun P b (G.next (G.adv P G.Γ.pushMint (.defLvl rest)) []) ru rets rest (ρ ++ [v]) vs) :
    MRun P b G ru rets (.defLvl rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  rw [usesCore] at hU
  refine machine_pushE (Γ' := G.adv P G.Γ.pushMint (.defLvl rest)) (m := 1) (oF := [v]) rfl
    (by rw [UCtx.adv_n' hf]; simp [Ctx.pushMint, Ctx.push, Ctx.n])
    (fun i hi => by rw [UCtx.adv_er' hf]; simp; omega)
    (fun k hk => by rw [UCtx.adv_er' hf]; simp; omega)
    (by rw [UCtx.adv_ghost' hf]; simpa [Ctx.pushMint, Ctx.push] using hG.ghost) ih hU
    (fun ρS vsS h => by cases h with | defLvl h => exact h)
    (fun H ρM pd H' out h => .defLvl h) ρS vsS hS hrun H ρM Res Out Shr pd hM hG

theorem Ctx.pushPrim_er' (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) (i : Nat) :
    (Γ.pushPrim P T er p).er i = if i = Γ.n then er else Γ.er i := by
  simp only [Ctx.pushPrim, Ctx.slotIf_er]; show (Γ.pushPrim0 T er p).er i = _; cases p <;> simp [Ctx.pushPrim0]

theorem Ctx.pushPrim_n (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : (Γ.pushPrim P T er p).n = Γ.n + 1 := by
  cases p <;> simp [Ctx.pushPrim, Ctx.pushPrim0, Ctx.push, Ctx.withRule, Ctx.n]

theorem Ctx.pushPrim_ghost (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : (Γ.pushPrim P T er p).ghost = Γ.ghost := by
  cases p <;> simp [Ctx.pushPrim, Ctx.pushPrim0, Ctx.push, Ctx.withRule]

theorem machine_callE {b : Nat} {G : UCtx} {ru : List Bool} {rets f args : Tm} {dec : Dec} {ms : List Bool}
    {ve : Option (List Bool)} {rest : Core} {ρ vs oF : List Tm}
    (hlen : ∀ t outs uf, G.callee P f args = some (t, outs, uf) → outs.isTele ∧ outs.len = ms.length)
    (hlF : oF.length = ms.length)
    (ih : ∀ t outs uf, G.callee P f args = some (t, outs, uf) →
      MRun P b (G.next (G.adv P (G.Γ.pushTele outs (some (ms.map (true || ·)))) (.call f dec args true ms ve rest)) [])
        ru rets rest (ρ ++ oF) vs) :
    MRun P b G ru rets (.call f dec args true ms ve rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
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
    (fun H ρM pd H' out h => .callE h) ρS vsS hS hrun H ρM Res Out Shr pd hM hG

theorem machine_mtchE {b : Nat} {G : UCtx} {ru : List Bool} {rets s R : Tm} {brs : List Br} {els : Option Core}
    {rest : Core} {ρ vs oF : List Tm} (hR : R.isTele) (hlF : oF.length = R.len)
    (ih : MRun P b (G.next (G.adv P (G.Γ.pushTele R (some (List.replicate R.len true))) (.mtch s R brs els true rest)) [])
      ru rets rest (ρ ++ oF) vs) :
    MRun P b G ru rets (.mtch s R brs els true rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
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
    (fun H ρM pd H' out h => .mtchE h) ρS vsS hS hrun H ρM Res Out Shr pd hM hG

theorem machine_primE {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core} {ρ vs : List Tm}
    {v : Tm} (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T true p) (.prim p true rest)) []) ru rets rest (ρ ++ [v]) vs) :
    MRun P b G ru rets (.prim p true rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
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
    (fun H ρM pd H' out h => .prim (by simp) h) ρS vsS hS hrun H ρM Res Out Shr pd hM hG

theorem machine_same {b : Nat} {G G' : UCtx} {ru : List Bool} {rets : Tm} {c rest : Core} {ρ vs : List Tm}
    (hΓn : G'.Γ.n = G.Γ.n) (hΓer : G'.Γ.er = G.Γ.er) (hghost : G'.Γ.ghost = G.Γ.ghost) (huq : G'.uq = G.uq)
    (hfill : G'.fill = G.fill) (huscr : G'.uscr = G.uscr) (hreb : G'.rebind = G.rebind)
    (ih : MRun P b G' ru rets rest ρ vs)
    (hu : ∀ U K, usesCore P b G ru rets c = some (U, K) → ∃ U' K', usesCore P b G' ru rets rest = some (U', K') ∧
      Uses.Eqb U' U G.Γ.n)
    (hrun : ∀ ρS vsS, RunS P ρS c vsS → RunS P ρS rest vsS)
    (hstep : ∀ H ρM pd H' out, RunM P H ρM pd rest H' out → RunM P H ρM pd c H' out) :
    MRun P b G ru rets c ρ vs := by
  intro U K hU ρS vsS hS hr H ρM Res Out Shr pd hM hG
  obtain ⟨U', K', hU', heq⟩ := hu U K hU
  have hG' : GOK P G' pd H ρM ρS ρ Res Shr := ⟨huscr ▸ hG.pend, fun x hx => by rw [hΓn]; exact hG.uscr x (huscr ▸ hx),
    fun t ht => by rw [huscr]; exact hG.rebind t (hreb ▸ ht), fun j hj => by rw [hΓn]; exact hG.uqlt j (huq ▸ hj),
    hfill.trans hG.fill, hghost.trans hG.ghost⟩
  obtain ⟨H', vsM, hrr, hO⟩ := ih U' K' hU' ρS vsS (hΓer ▸ hS) (hrun ρS vsS hr) H ρM Res Out Shr pd
    (by rw [hΓn, hΓer]; exact hM.congr heq.symm) hG'
  rw [hΓn, hΓer] at hO
  exact ⟨H', vsM, hstep H ρM pd H' vsM hrr, hO.congr heq⟩

theorem Uses.Eqb.refl (U : Uses) (n : Nat) : Uses.Eqb U U n := fun _ _ => rfl

theorem machine_chkSame {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {k : Chk} {rest : Core}
    {ρ vs : List Tm} (hk : ∀ m, k = .mark m → m.pend = false)
    (hu : ∀ U K, usesCore P b G ru rets (.chk k a x rest) = some (U, K) → usesCore P b G ru rets rest = some (U, K))
    (ih : MRun P b G ru rets rest ρ vs) : MRun P b G ru rets (.chk k a x rest) ρ vs :=
  machine_same rfl rfl rfl rfl rfl rfl rfl ih (fun U K h => ⟨U, K, hu U K h, Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h) (fun H ρM pd H' out h => .chk hk h)

theorem machine_chkPlain {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {k : Chk} {rest : Core}
    {ρ vs : List Tm} (hk : k = .is ∨ k = .ty ∨ k = .rt) (ih : MRun P b G ru rets rest ρ vs) :
    MRun P b G ru rets (.chk k a x rest) ρ vs :=
  machine_chkSame (fun m e => by rcases hk with rfl | rfl | rfl <;> cases e)
    (fun U K h => by rcases hk with rfl | rfl | rfl <;> (rw [usesCore] at h <;> first | exact h | (intros; contradiction))) ih

theorem machine_slotAt {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {rest : Core} {ρ vs : List Tm}
    (ih : MRun P b { G with Γ := { G.Γ with pd := a.varSlot } } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk .slotAt a x rest) ρ vs :=
  machine_same (G' := { G with Γ := { G.Γ with pd := a.varSlot } }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h <;> first | exact h | (intros; contradiction), Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h)
    (fun H ρM pd H' out h => .chk (fun m e => by cases e) h)

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

theorem prim_val_tm (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {t T : Tm} {u : Bool} {A : Uses}
    (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrt : rt P G.Γ t = true) (hA : G.termUses P u t = some A)
    {H : Heap} {Out' Shr : Nat → Prop} (hM : MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' Shr) :
    ∃ H1 w, P.build H (Tm.env ρM) t = (H1, w) ∧
      MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (ret1 T) [u] H1 [w] [P.sub ρS t] [t.subst (Tm.env ρ)] := by
  obtain ⟨H', vsM, hr, hO⟩ := machine_ret hP (ts := .cons t .nil) (rets := ret1 T) (by simp [rtArgs, Ent.er, hrt])
    hE hS rfl (ru := [u]) (U := A) (by simp [UCtx.retUses, Ent.er, hA, Uses.seq]) hM none
  cases hr with
  | ret hb =>
  simp only [Tm.toList, Prog.buildList, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨_, _, rfl, by simpa [Tm.toList] using hO⟩

theorem MOut.imm {A : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Out' Shr : Nat → Prop}
    (hM : MFrame P A n er H ρM ρS ρ (fun _ => False) Out' Shr) {T w uS v : Tm} {u : Bool} (hd : MDec P H w uS)
    (hf : ∀ b, ¬ Foot P H w uS b) :
    MOut P A n er H ρM ρS ρ (fun _ => False) Shr (ret1 T) [u] H [w] [uS] [v] := by
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

def PrimVal (P : Prog) (G : UCtx) (ρ : List Tm) (p : Prim) : Prop :=
  ∀ T A, G.primTy P p = some T → G.primUses P (G.ents.headD false) p = some A →
    ∀ ρS H ρM Out' Shr, SimEnv P G.Γ.er ρS ρ → MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' Shr →
    ∃ H1 w, P.evalM H ρM p = (H1, w) ∧ MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (ret1 T)
      [G.ents.headD false] H1 [w] [p.evalS P ρS] [p.eval P ρ]

theorem prim_val (hP : ProgOK P) {G : UCtx} {ρ : List Tm} {p : Prim} (hE : EnvOK P ρ G.Γ)
    (hrt : p.rt P G.Γ = true) (hnc : ∀ a b q, p ≠ .coerce a b q) : PrimVal P G ρ p := by
  intro T A _ hA ρS H ρM Out' Shr hS hM
  cases p with
  | tm t | place t _ | unplace t _ =>
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
    {Res Out Shr : Nat → Prop} {rets : Tm} {ru : List Bool}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (sA : A.Sub U)
    (sC : ∀ i < n, ((C.lookup i).isSome → (U.lookup i).isSome) ∧ (C.lookup i = some true → U.lookup i = some true))
    (hfree : ∀ j < n, (A.lookup j = some true → C.lookup j = none) ∧ (C.lookup j = some true → A.lookup j = none))
    (hO : MOut P A n er H ρM ρS ρ (fun _ => False) Shr rets ru H' oM oS oF) (hlS : oS.length = m) (hlF : oF.length = m)
    (her : ∀ i < n, er' i = er i)
    (hers : ∀ k < m, (C.lookup (n + k)).isSome → er' (n + k) = false → rets.ers.getD k true = false)
    (hu : ∀ k < m, C.lookup (n + k) = some true → er' (n + k) = false → ru.getD k false = true)
    (hR0 : ∀ a, R0 a → H.next ≤ a ∨ Own P A n er H ρM ρS ρ a) (hR0b : ∀ a, R0 a → (H'.blk a).isSome)
    (hR0n : ∀ k w u, k < m → oM[k]? = some w → oS[k]? = some u → (C.lookup (n + k)).isSome → er' (n + k) = false →
      ∀ b, Foot P H' w u b → ¬ R0 b) :
    MFrame P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) (fun a => Res a ∨ R0 a) Out Shr ∧
    ∀ {H'' : Heap} {vsM vsS vs : List Tm} {rets2 : Tm} {ru2 : List Bool},
      MOut P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) (fun a => Res a ∨ R0 a) Shr rets2 ru2 H'' vsM vsS vs →
      MOut P U n er H ρM ρS ρ Res Shr rets2 ru2 H'' vsM vsS vs := by
  have hlM : oM.length = m := by rw [hO.len, hlS]
  have cls := fun {i} (hi : i < n + m) => env_cls hM.lenM hM.lenS hM.lenF hlM hlS hlF hi
  have er_old : ∀ {i}, i < n → er' i = false → er i = false := fun hi he => by rw [← her _ hi]; exact he
  have hOwn : ∀ i < n, (C.lookup i).isSome → er i = false → ∀ b, Foot P H (Tm.env ρM i) (Tm.env ρS i) b →
      ¬ Own P A n er H ρM ρS ρ b := fun i hi hC hei b hf ⟨x, hx, hA, hex, hs⟩ => by
    have hne : x ≠ i := fun e => by subst e; rw [(hfree x hx).1 hA] at hC; cases hC
    exact hM.sep x hx i hi hne (sA.2 x hA) ((sC i hi).1 hC) hex hei b hs hf
  have hAg : ∀ i < n, (C.lookup i).isSome → er i = false → Agree H H' (Foot P H (Tm.env ρM i) (Tm.env ρS i)) :=
    fun i hi hC he b hf => hO.keep b (Foot.lt hM.wf (hM.dec i hi ((sC i hi).1 hC) he) hf) (hOwn i hi hC he b hf) id
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
      H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Live P A n er H ρM ρS b ∨ Shr b :=
    fun k w u hk hw hu' hC he b hf => by
      rcases hO.foot k w u hw hu' (hers k hk hC he) b hf with h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
  have oldSp : ∀ x < n, C.lookup x = some true → er x = false →
      ∀ b, Spine P H' (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b →
      Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b :=
    fun x hx hC he b hs => Spine.bwd (hAg x hx (by simp [hC]) he).spine hs
  have oldFt : ∀ z < n, (C.lookup z).isSome → er z = false → ∀ b, Foot P H' (Tm.env ρM z) (Tm.env ρS z) b →
      Foot P H (Tm.env ρM z) (Tm.env ρS z) b := fun z hz hC he b hf => Foot.bwd (hAg z hz hC he) hf
  have hLive : ∀ a, Live P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) a → H.next ≤ a ∨ Own P A n er H ρM ρS ρ a ∨
      Live P U n er H ρM ρS a ∨ Shr a := fun a ⟨z, hz, hC, hez, hf⟩ => by
    rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
    · rw [f1, f2] at hf
      have he := er_old hzn hez
      exact .inr (.inr (.inl ⟨z, hzn, (sC z hzn).1 hC, he, oldFt z hzn hC he a hf⟩))
    · rcases newFt j _ _ hj f1 f2 hC hez a hf with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl (h.mono sA)))
      · exact .inr (.inr (.inr h))
  have hOwnC : ∀ a, Own P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) a →
      H.next ≤ a ∨ Own P U n er H ρM ρS ρ a := fun a ⟨x, hx, hC, hex, hs⟩ => by
    rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · rw [e1, e2, e3] at hs
      have he := er_old hxn hex
      exact .inr ⟨x, hxn, (sC x hxn).2 hC, he, oldSp x hxn hC he a hs⟩
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
    · rcases hR.foot k w u hw hu' he b hf with h | h | h | h | h
      · exact .inl (Nat.le_trans hO.next h)
      · rcases hOwnC b h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rcases h with h | h
        · exact .inr (.inr (.inl h))
        · rcases hR0 b h with h | h
          · exact .inl h
          · exact .inr (.inl (h.mono sA))
      · rcases hLive b h with h | h | h | h
        · exact .inl h
        · exact .inr (.inl (h.mono sA))
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))
      · exact .inr (.inr (.inr (.inr h)))
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
  refine ⟨by simp [hM.lenM, hlM], by simp [hM.lenS, hlS], by simp [hM.lenF, hlF], hO.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hC he
    rcases cls hi with ⟨hn, e1, e2, -⟩ | ⟨k, hk, rfl, e1, e2, -⟩
    · have he' := er_old hn he
      rw [e1, e2]; exact (hM.dec i hn ((sC i hn).1 hC) he').frame (hAg i hn hC he')
    · exact hO.dec k _ _ e1 e2 (hers k hk hC he)
  · intro x hx hC he
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3]; exact (hM.wo x hn ((sC x hn).2 hC) he').fwd (hAg x hn (by simp [hC]) he')
    · exact hO.uwo k _ _ _ e1 e2 e3 (hers k hk (by simp [hC]) he) (hu k hk hC he)
  · intro x hx z hz hne hCx hCz hex hez b h1 h2
    rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩ <;>
      rcases cls hz with ⟨hzn, f1, f2, f3⟩ | ⟨j, hj, rfl, f1, f2, f3⟩
    · rw [e1, e2, e3] at h1; rw [f1, f2] at h2
      have hex' := er_old hxn hex
      have hez' := er_old hzn hez
      exact hM.sep x hxn z hzn hne ((sC x hxn).2 hCx) ((sC z hzn).1 hCz) hex' hez' b (oldSp x hxn hCx hex' b h1)
        (oldFt z hzn hCz hez' b h2)
    · rw [e1, e2, e3] at h1
      have hex' := er_old hxn hex
      have hs := oldSp x hxn hCx hex' b h1
      have hlt := Foot.lt hM.wf (hM.dec x hxn ((sC x hxn).1 (by simp [hCx])) hex') hs.foot
      have hAx : A.lookup x = none := (hfree x hxn).2 hCx
      rcases newFt j _ _ hj f1 f2 hCz hez b h2 with h | ⟨y, hy, hAy, hey, hsy⟩ | ⟨w, hw, hAw, hew, hfw⟩ | h
      · omega
      · have hne' : y ≠ x := fun e => by subst e; rw [hAx] at hAy; cases hAy
        exact hM.sep y hy x hxn hne' (sA.2 y hAy) ((sC x hxn).1 (by simp [hCx])) hey hex' b hsy hs.foot
      · have hne' : x ≠ w := fun e => by subst e; rw [hAx] at hAw; cases hAw
        exact hM.sep x hxn w hw hne' ((sC x hxn).2 hCx) (sA.1 w hAw) hex' hew b hs hfw
      · exact hM.shr.2.1 x hxn ((sC x hxn).2 hCx) hex' b hs h
    · rw [f1, f2] at h2
      have hez' := er_old hzn hez
      have hf := oldFt z hzn hCz hez' b h2
      rcases newSp k _ _ _ hk e1 e2 e3 hCx hex b h1 with h | ho
      · have := Foot.lt hM.wf (hM.dec z hzn ((sC z hzn).1 hCz) hez') hf; omega
      · exact hOwn z hzn hCz hez' b hf ho
    · exact hO.usep k j _ _ _ _ _ (fun e => hne (by rw [e])) e1 e2 e3 f1 f2 (hers k hk (by simp [hCx]) hex)
        (hers j hj hCz hez) (hu k hk hCx hex) b h1 h2
  · intro x hx hC he b h1 h2
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3] at h1; exact hM.out x hn ((sC x hn).2 hC) he' b (oldSp x hn hC he' b h1) h2
    · rcases newSp k _ _ _ hk e1 e2 e3 hC he b h1 with h | ⟨y, hy, hAy, hey, hsy⟩
      · have := hM.outb b h2; omega
      · exact hM.out y hy (sA.2 y hAy) hey b hsy h2
  · have r0Live : ∀ a, R0 a → Live P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) a → False := fun a h0 ⟨z, hz, hC, hez, hf⟩ => by
      rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
      · rw [f1, f2] at hf
        have he := er_old hzn hez
        have hf' := oldFt z hzn hC he a hf
        rcases hR0 a h0 with h1 | h1
        · have := Foot.lt hM.wf (hM.dec z hzn ((sC z hzn).1 hC) he) hf'; omega
        · exact hOwn z hzn hC he a hf' h1
      · exact hR0n j _ _ hj f1 f2 hC hez a hf h0
    refine ⟨fun a ha hl => ?_, fun a ha ho => ?_, fun a ha ⟨x, hx, hC, hex, hs⟩ => ?_, fun a ha => ?_⟩
    · rcases ha with ha | ha
      · rcases hLive a hl with h | h | h | h
        · have := hResLt a ha; omega
        · exact hRes a ha h
        · exact hM.res.1 a ha h
        · exact hM.shr.1 a ha h
      · exact r0Live a ha hl
    · rcases ha with ha | ha
      · exact hM.res.2.1 a ha ho
      · rcases hR0 a ha with h | ⟨x, hx, hA, hex, hs⟩
        · have := hM.outb a ho; omega
        · exact hM.out x hx (sA.2 x hA) hex a hs ho
    · rcases ha with ha | ha
      · rcases hLive a ⟨x, hx, by simp [hC], hex, hs.foot⟩ with h | h | h | h
        · have := hResLt a ha; omega
        · exact hRes a ha h
        · exact hM.res.1 a ha h
        · exact hM.shr.1 a ha h
      · exact r0Live a ha ⟨x, hx, by simp [hC], hex, hs.foot⟩
    · rcases ha with ha | ha
      · rw [hO.keep a (hResLt a ha) (hRes a ha) id]; exact hM.res.2.2.2 a ha
      · exact hR0b a ha
  · intro a ha; exact Nat.lt_of_lt_of_le (hM.outb a ha) hO.next
  · refine ⟨fun a ha hs => ?_, fun x hx hC he b h1 h2 => ?_, fun a ha => Nat.lt_of_lt_of_le (hM.shr.2.2 a ha) hO.next⟩
    · rcases ha with ha | ha
      · exact hM.shr.1 a ha hs
      · rcases hR0 a ha with h | ⟨x, hx, hA, hex, hsx⟩
        · have := hM.shr.2.2 a hs; omega
        · exact hM.shr.2.1 x hx (sA.2 x hA) hex a hsx hs
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3] at h1; exact hM.shr.2.1 x hn ((sC x hn).2 hC) he' b (oldSp x hn hC he' b h1) h2
    · rcases newSp k _ _ _ hk e1 e2 e3 hC he b h1 with h | ⟨y, hy, hAy, hey, hsy⟩
      · have := hM.shr.2.2 b h2; omega
      · exact hM.shr.2.1 y hy (sA.2 y hAy) hey b hsy h2

theorem MDecs.length {H : Heap} : ∀ {ws vs : List Tm}, MDecs P H ws vs → ws.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]

theorem MOut.fields {S : Uses} {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {T : Tm} {scr : Bool}
    {w uS v : Tm} (hO : MOut P S n er H ρM ρS ρ (fun _ => False) Shr (ret1 T) [scr] H1 [w] [uS] [v])
    {d c : Nat} {lsM vsM lsS vsS lsF vsF sig : Tm} {ruF : List Bool}
    (hvM : P.viewM H1 w = .app (.vc d c lsM) vsM) (hvS : P.view uS = .app (.vc d c lsS) vsS)
    (hv : v = .app (.vc d c lsF) vsF) (hc : P.ctor d c = some sig) (hwf : P.wrapField d c = none)
    (hruF : ∀ k, ruF.getD k false = true → scr = true ∧ (sig.skip (P.lifted d)).uAt k = true) :
    MOut P S n er H ρM ρS ρ (fun _ => False) Shr (sig.skip (P.lifted d)) ruF H1 vsM.toList vsS.toList vsF.toList ∧
    (∀ a, scr = true → w = .ptr a → (H.next ≤ a ∨ Own P S n er H ρM ρS ρ a) ∧ (H1.blk a).isSome ∧
      ∀ (k : Nat) wk uk, vsM.toList[k]? = some wk → vsS.toList[k]? = some uk → ∀ b, Foot P H1 wk uk b → b ≠ a) := by
  have hd := hO.dec 0 w uS rfl rfl (by simp [Tm.ers, Ent.er])
  have hft := hO.foot 0 w uS rfl rfl (by simp [Tm.ers, Ent.er])
  have hsp := fun (h : scr = true) => hO.uspine 0 w uS v rfl rfl rfl (by simp [Tm.ers, Ent.er]) (by simp [h])
  have hwo := fun (h : scr = true) => hO.uwo 0 w uS v rfl rfl rfl (by simp [Tm.ers, Ent.er]) (by simp [h])
  have triv : (∀ (j : Nat) w u, vsM.toList[j]? = some w → vsS.toList[j]? = some u →
      (∃ m, w = .nat m ∧ u = .nat m)) → vsM.toList.length = vsS.toList.length →
      MOut P S n er H ρM ρS ρ (fun _ => False) Shr (sig.skip (P.lifted d)) ruF H1 vsM.toList vsS.toList vsF.toList := by
    intro nofoot hlen
    have nf : ∀ (j : Nat) w u, vsM.toList[j]? = some w → vsS.toList[j]? = some u → ∀ b, ¬ Foot P H1 w u b :=
      fun j w u hw hu b hf => by obtain ⟨m, rfl, rfl⟩ := nofoot j w u hw hu; cases hf
    refine ⟨hO.wf, hO.next, hO.blk, hO.keep, hlen, fun j w u hw hu _ => ?_, fun j w u hw hu _ b hf => (nf j w u hw hu b hf).elim,
      fun j w u v hw hu hv _ _ b hs => (nf j w u hw hu b hs.foot).elim, fun j w u v hw hu hv _ _ => .free fun b hs =>
        nf j w u hw hu b hs.foot, fun j i w u v w' u' _ hw hu _ _ _ _ _ _ b h1 _ => nf j w u hw hu b h1.foot⟩
    obtain ⟨m, rfl, rfl⟩ := nofoot j w u hw hu; exact .nat
  cases hd with
  | @ptr a d' c' ws vs' hb hms =>
    simp only [Prog.viewM, hb, Tm.app.injEq, Tm.vc.injEq] at hvM
    obtain ⟨⟨h1, h2, -⟩, rfl⟩ := hvM
    subst d' c'
    simp only [Prog.view, Tm.app.injEq, Tm.vc.injEq] at hvS
    obtain ⟨⟨-, -, -⟩, rfl⟩ := hvS
    subst hv
    simp only [Tm.toList_ofList]
    have hwoP : scr = true → WO P H1 (.ptr a) (.app (.vc d c .nil) (.ofList vs')) (.app (.vc d c lsF) vsF) →
        ∃ sig', P.ctor d c = some sig' ∧
        (∀ (k : Nat) w u, ws[k]? = some w → vs'[k]? = some u → ¬ Foot P H1 w u a) ∧
        (∀ (k : Nat) w u v, (sig'.skip (P.lifted d)).uAt k = true → ws[k]? = some w → vs'[k]? = some u →
          vsF.toList[k]? = some v → WO P H1 w u v) ∧
        (∀ (k : Nat) w u v, (sig'.skip (P.lifted d)).uAt k = true → ws[k]? = some w → vs'[k]? = some u →
          vsF.toList[k]? = some v → ∀ (j : Nat) w' u', j ≠ k → ws[j]? = some w' → vs'[j]? = some u' →
          Disj (Spine P H1 w u v) (Foot P H1 w' u')) := fun _ h => by
      cases h with
      | ptr hb' _ hc' h1 h2 h3 =>
        rw [hb] at hb'; cases hb'
        exact ⟨_, hc', fun k w u hw hu => h1 k w u hw (by simpa [Tm.toList_ofList] using hu),
          fun k w u v hk hw hu hv => h2 k w u v hk hw (by simpa [Tm.toList_ofList] using hu) hv,
          fun k w u v hk hw hu hv j w' u' hj hw' hu' => h3 k w u v hk hw (by simpa [Tm.toList_ofList] using hu) hv j w' u'
            hj hw' (by simpa [Tm.toList_ofList] using hu')⟩
      | wrap hw' => rw [hwf] at hw'; cases hw'
      | free hn => exact (hn a (.top hwf)).elim
    refine ⟨⟨hO.wf, hO.next, hO.blk, hO.keep, hms.length, fun k w u hw hu _ => hms.get k w u hw hu,
      fun k w u hw hu _ b hf => hft b (.field hb hw (by rwa [Tm.toList_ofList]) hf), fun k w u v hw hu hv _ hr b hs => ?_,
      fun k w u v hw hu hv _ hr => ?_, fun k j w u v w' u' hkj hw hu hv hw' hu' _ _ hr => ?_⟩, fun a' hs e => ?_⟩
    · obtain ⟨h1, h2⟩ := hruF k hr
      exact hsp h1 b (.field hb hwf hc h2 hw (by rwa [Tm.toList_ofList]) hv hs)
    · obtain ⟨h1, h2⟩ := hruF k hr
      obtain ⟨sig', hc', -, h3, -⟩ := hwoP h1 (hwo h1)
      rw [hc] at hc'; cases hc'
      exact h3 k w u v h2 hw hu hv
    · obtain ⟨h1, h2⟩ := hruF k hr
      obtain ⟨sig', hc', -, -, h4⟩ := hwoP h1 (hwo h1)
      rw [hc] at hc'; cases hc'
      exact h4 k w u v h2 hw hu hv j w' u' (Ne.symm hkj) hw' hu'
    · cases e
      obtain ⟨-, -, h1, -⟩ := hwoP hs (hwo hs)
      refine ⟨?_, by rw [hb]; rfl, fun k wk uk hk hk' b hf e => h1 k wk uk hk hk' (e ▸ hf)⟩
      rcases hsp hs a (.top hwf) with h | h | h
      · exact .inl h
      · exact .inr h
      · exact h.elim
  | @nat k =>
    simp only [Prog.viewM] at hvM
    have e := hvM.symm.trans hvS
    simp only [Tm.app.injEq, Tm.vc.injEq] at e
    obtain ⟨-, rfl⟩ := e
    refine ⟨triv (fun j w u hw hu => ?_) rfl, fun a _ e => by cases e⟩
    rw [hw] at hu; cases hu
    simp only [Prog.view] at hvS
    split at hvS
    · split at hvS <;> simp only [Tm.app.injEq, Tm.vc.injEq] at hvS <;> obtain ⟨-, rfl⟩ := hvS
      · simp [Tm.toList] at hw
      · cases j with
        | zero => simp [Tm.toList] at hw; subst hw; exact ⟨_, rfl, rfl⟩
        | succ j => simp [Tm.toList] at hw
    · cases hvS
  | imm =>
    simp only [Prog.viewM, Prog.view, Tm.app.injEq, Tm.vc.injEq] at hvM hvS
    obtain ⟨-, rfl⟩ := hvM
    obtain ⟨-, rfl⟩ := hvS
    exact ⟨triv (fun j w u hw => by simp [Tm.toList] at hw) rfl, fun a _ e => by cases e⟩
  | _ => simp [Prog.view] at hvS

theorem lookup_filter_ne {A : Uses} {i j : Nat} (h : i ≠ j) : (A.filter (·.1 != j)).lookup i = A.lookup i := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    obtain ⟨k, u⟩ := p
    by_cases hk : k = j
    · subst hk
      have : (i == k) = false := by simpa using h
      simp [List.filter_cons, List.lookup, this, ih]
    · have hk' : (k != j) = true := by simpa using hk
      simp only [List.filter_cons, hk', ite_true, List.lookup]
      split <;> simp_all

theorem Uses.join_spec : ∀ (B A : Uses) (i : Nat),
    (((A.lookup i).isSome → ((Uses.join A B).lookup i).isSome) ∧
     (A.lookup i = some true → (Uses.join A B).lookup i = some true)) ∧
    (∀ u, (i, u) ∈ B → ((Uses.join A B).lookup i).isSome) ∧ ((i, true) ∈ B → (Uses.join A B).lookup i = some true)
  | [], A, i => ⟨⟨id, id⟩, fun _ h => by simp at h, fun h => by simp at h⟩
  | (j, u) :: B, A, i => by
    simp only [Uses.join, List.foldl_cons]
    have step : ∀ A1 : Uses, ((A.lookup i).isSome → (A1.lookup i).isSome) → (A.lookup i = some true → A1.lookup i = some true) →
        (i = j → (A1.lookup i).isSome) → (i = j → u = true → A1.lookup i = some true) →
        (((A.lookup i).isSome → ((Uses.join A1 B).lookup i).isSome) ∧
         (A.lookup i = some true → (Uses.join A1 B).lookup i = some true)) ∧
        (∀ u', (i, u') ∈ (j, u) :: B → ((Uses.join A1 B).lookup i).isSome) ∧
        ((i, true) ∈ (j, u) :: B → (Uses.join A1 B).lookup i = some true) := by
      intro A1 h1 h2 h3 h4
      obtain ⟨⟨g1, g2⟩, g3, g4⟩ := Uses.join_spec B A1 i
      refine ⟨⟨fun h => g1 (h1 h), fun h => g2 (h2 h)⟩, fun u' hm => ?_, fun hm => ?_⟩
      · rcases List.mem_cons.mp hm with e | e
        · cases e; exact g1 (h3 rfl)
        · exact g3 u' e
      · rcases List.mem_cons.mp hm with e | e
        · cases e; exact g2 (h4 rfl rfl)
        · exact g4 e
    apply step <;> intros
    all_goals
      by_cases hij : i = j
      · subst hij
        cases hl : A.lookup i with
        | none => cases u <;> simp_all [List.lookup]
        | some x => cases x <;> cases u <;> simp_all [List.lookup]
      · have hb : (i == j) = false := by simpa using hij
        cases hl : A.lookup j with
        | none => simp only [hl, List.lookup, hb] at * <;> simp_all
        | some x => cases x <;> cases u <;> simp only [hl, List.lookup, hb, lookup_filter_ne hij, ite_true, ite_false,
            Bool.false_eq_true] at * <;> simp_all

def Uses.SubB (A B : Uses) (n : Nat) : Prop :=
  ∀ i < n, ((A.lookup i).isSome → (B.lookup i).isSome) ∧ (A.lookup i = some true → B.lookup i = some true)

theorem Uses.join_sub_left (A B : Uses) : A.Sub (Uses.join A B) :=
  ⟨fun i h => (Uses.join_spec B A i).1.1 h, fun i h => (Uses.join_spec B A i).1.2 h⟩

theorem Uses.join_sub_right (A B : Uses) : B.Sub (Uses.join A B) :=
  ⟨fun i h => by obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h; exact (Uses.join_spec B A i).2.1 u (lookup_mem hu),
   fun i h => (Uses.join_spec B A i).2.2 (lookup_mem h)⟩

theorem Uses.below_lookup_ge {U : Uses} {n i : Nat} (h : n ≤ i) : (U.below n).lookup i = none := by
  induction U with
  | nil => rfl
  | cons p U ih =>
    obtain ⟨j, u⟩ := p
    simp only [Uses.below, List.filter_cons] at ih ⊢
    split
    · have : (i == j) = false := by simp_all; omega
      simp [List.lookup, this, ih]
    · exact ih

theorem Uses.below_sub (U : Uses) (n : Nat) : (U.below n).Sub U := by
  refine ⟨fun i h => ?_, fun i h => ?_⟩ <;> by_cases hi : i < n
  · rwa [Uses.below_lookup hi] at h
  · rw [Uses.below_lookup_ge (by omega)] at h; cases h
  · rwa [Uses.below_lookup hi] at h
  · rw [Uses.below_lookup_ge (by omega)] at h; cases h

theorem Uses.Sub.subB {A B : Uses} (h : A.Sub B) (n : Nat) : Uses.SubB A B n := fun i _ => ⟨h.1 i, h.2 i⟩

theorem Uses.SubB.trans {A B C : Uses} {n : Nat} (h1 : Uses.SubB A B n) (h2 : Uses.SubB B C n) : Uses.SubB A C n :=
  fun i hi => ⟨fun h => (h2 i hi).1 ((h1 i hi).1 h), fun h => (h2 i hi).2 ((h1 i hi).2 h)⟩

theorem Uses.below_subB (U : Uses) (n : Nat) : Uses.SubB U (U.below n) n := fun i hi => by
  rw [Uses.below_lookup hi]; exact ⟨id, id⟩

theorem usesArms_sel {b : Nat} {G : UCtx} {ru : List Bool} {R s H idx : Tm} {shp : List Arm} {fe cell : Bool} :
    ∀ (brs : List Br) (B : Uses) (K : Caps), usesArms P b G ru R s H idx shp fe cell brs = some (B, K) →
    ∀ c body, lookupBr brs c = some body → ∀ k sig ph, shp[c]? = some (k, sig, ph) →
    ∀ Gb, G.branchCtx P s k H idx sig fe (!fe && ph) G.scr cell = some Gb →
    ∃ BU BK, usesCore P b Gb ru R body = some (BU, BK) ∧ (BU.below G.Γ.n).Sub B
  | [], _, _, _, c, body, hl, _, _, _, _, _, _ => by simp [lookupBr] at hl
  | (x, c', y, body') :: brs, B, K, h, c, body, hl, k, sig, ph, hshp, Gb, hb => by
    rw [usesArms] at h
    rcases hR : usesArms P b G ru R s H idx shp fe cell brs with _ | ⟨U2, K2⟩
    · exfalso
      split at h
      · split at h <;> simp [hR] at h
      · simp at h
    have hU2 : U2.Sub B := by
      split at h
      · split at h <;> simp only [hR, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        · obtain ⟨_, _, e⟩ := h
          have e' := congrArg Prod.fst e; simp only at e'; rw [← e']; exact Uses.join_sub_right _ _
        · have e' := congrArg Prod.fst h; simp only at e'; rw [← e']; exact Uses.join_sub_right _ _
      · simp at h
    by_cases hc : c' = c
    · subst hc
      simp [lookupBr, List.find?] at hl; subst hl
      rw [hshp] at h; simp only [hb] at h
      simp only [hR, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨BU, BK⟩, hBU, _, rfl, _, rfl, e⟩ := h
      refine ⟨BU, BK, hBU, ?_⟩
      have e' := congrArg Prod.fst e; simp only at e'; rw [← e']; exact Uses.join_sub_left _ _
    · have hc' : (c' == c) = false := by simpa using hc
      have hl' : lookupBr brs c = some body := by
        simpa [lookupBr, List.find?, hc'] using hl
      obtain ⟨BU, BK, h1, h2⟩ := usesArms_sel brs U2 K2 hR c body hl' k sig ph hshp Gb hb
      exact ⟨BU, BK, h1, h2.trans hU2⟩

theorem MFrame.subB {A U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Out Shr : Nat → Prop}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (h : Uses.SubB A U n) : MFrame P A n er H ρM ρS ρ Res Out Shr :=
  ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, fun i hi hb he => hM.dec i hi ((h i hi).1 hb) he,
   fun x hx hb he => hM.wo x hx ((h x hx).2 hb) he,
   fun x hx z hz hne hbx hbz hex hez => hM.sep x hx z hz hne ((h x hx).2 hbx) ((h z hz).1 hbz) hex hez,
   fun x hx hb he => hM.out x hx ((h x hx).2 hb) he,
   ⟨fun a ha ⟨z, hz, hA, he, hf⟩ => hM.res.1 a ha ⟨z, hz, (h z hz).1 hA, he, hf⟩, hM.res.2.1,
    fun a ha ⟨z, hz, hA, he, hf⟩ => hM.res.2.2.1 a ha ⟨z, hz, (h z hz).2 hA, he, hf⟩, hM.res.2.2.2⟩, hM.outb,
   ⟨hM.shr.1, fun x hx hb he => hM.shr.2.1 x hx ((h x hx).2 hb) he, hM.shr.2.2⟩⟩

theorem MOut.supB {A U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Shr : Nat → Prop}
    {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm} (h : Uses.SubB A U n)
    (hO : MOut P A n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs) : MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  have own : ∀ a, Own P A n er H ρM ρS ρ a → Own P U n er H ρM ρS ρ a :=
    fun a ⟨z, hz, hA, he, hf⟩ => ⟨z, hz, (h z hz).2 hA, he, hf⟩
  have live : ∀ a, Live P A n er H ρM ρS a → Live P U n er H ρM ρS a :=
    fun a ⟨z, hz, hA, he, hf⟩ => ⟨z, hz, (h z hz).1 hA, he, hf⟩
  refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha (fun h' => ho (own a h')) hr, hO.len, hO.dec,
    fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
  · rcases hO.foot k w u hw hu he b hf with h1 | h1 | h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (own b h1))
    · exact .inr (.inr (.inl h1))
    · exact .inr (.inr (.inr (.inl (live b h1))))
    · exact .inr (.inr (.inr (.inr h1)))
  · rcases hO.uspine k w u v hw hu hv he hr b hs with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl (own b h1))
    · exact .inr (.inr h1)

theorem teleUs_getD : ∀ (t : Tm) (k : Nat), (teleUs t).getD k false = t.uAt k
  | .bind _ _ r, 0 => rfl
  | .bind _ _ r, k + 1 => by have := teleUs_getD r k; simp only [List.getD_eq_getElem?_getD] at this; simp [teleUs, Tm.uAt, this]
  | .fv _, _ | .bv _, _ | .nil, _ | .cons .., _ | .app .., _ | .tyc .., _ | .vc .., _ | .tyCtor _, _ | .valCtor _, _
  | .univ, _ | .level, _ | .predates .., _ | .subterm .., _ | .fn .., _ | .mtbl .., _ | .lvl _, _ | .tok, _
  | .clo .., _ | .nat _, _ | .ptr _, _ | .wld _, _ | .sfv _, _ | .sbv _, _ => by cases ‹Nat› <;> rfl

theorem getD_dropLast {l : List Bool} {k : Nat} (h : l.dropLast.getD k false = true) : l.getD k false = true := by
  simp only [List.getD_eq_getElem?_getD] at h ⊢
  rw [List.getElem?_dropLast] at h
  split at h
  · exact h
  · simp at h

theorem viewM_of_view {H : Heap} {w uS : Tm} (hd : MDec P H w uS) {d c : Nat} {ls vs : Tm}
    (hv : P.view uS = .app (.vc d c ls) vs) : ∃ lsM vsM, P.viewM H w = .app (.vc d c lsM) vsM := by
  cases hd with
  | ptr hb _ =>
    simp only [Prog.view, Tm.app.injEq, Tm.vc.injEq] at hv
    obtain ⟨⟨rfl, rfl, -⟩, -⟩ := hv
    exact ⟨_, _, by simp only [Prog.viewM, hb]; rfl⟩
  | nat => exact ⟨_, _, by simpa [Prog.viewM] using hv⟩
  | imm => exact ⟨_, _, by simpa [Prog.viewM, Prog.view] using hv⟩
  | _ => simp [Prog.view] at hv

theorem selectBr_lookup {brs : List Br} {els : Option Core} {c : Nat} {body : Core} (h : lookupBr brs c = some body)
    (vs : List Tm) : selectBr brs els c vs = some (vs, body) := by
  simp [selectBr, h]

theorem branchCtx_fld {G Gb : UCtx} {s k H idx sig : Tm} {cell : Bool} (hf : G.fill = false) (hT : sig.isTele)
    (h : G.branchCtx P s k H idx sig false false G.scr cell = some Gb) :
    Gb.Γ.n = G.Γ.n + (sig.len - 1) ∧ (∀ i < G.Γ.n, Gb.Γ.er i = G.Γ.er i) ∧
    (∀ j < sig.len - 1, Gb.Γ.er (G.Γ.n + j) = sig.ers.getD j true) ∧ Gb.Γ.ghost = G.Γ.ghost ∧ Gb.fill = G.fill ∧
    Gb.rebind = none ∧ Gb.uscr = (if G.scr && cell then some s else none) ∧
    (∀ j, Gb.uq.contains j = true → G.uq.contains j = true ∨
      ∃ i, j = G.Γ.n + i ∧ i < Gb.Γ.n - G.Γ.n ∧ (if G.scr then (teleUs sig).dropLast else []).getD i false = true) := by
  unfold UCtx.branchCtx at h
  simp only at h
  rcases hb : Ctx.branch P { G.Γ with ghost := G.Γ.ghost || false } s k H idx sig with ⟨Γf, r⟩
  obtain ⟨eg, eer, en⟩ := Ctx.branch_fields { G.Γ with ghost := G.Γ.ghost || false } s k H idx sig
  rw [hb] at eg eer en; dsimp only at eg eer en
  rw [hb] at h
  cases r with
  | ok σ =>
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨g, h1, h2⟩ := Ctx.openTele_er (sig.len - 1) { G.Γ with ghost := G.Γ.ghost || false } sig hT
    have hn := Ctx.openTele_n_eq (sig.len - 1) { G.Γ with ghost := G.Γ.ghost || false } sig hT (by omega)
    rw [← eg] at g; rw [← eer] at h1 h2; rw [← en] at hn
    have hl := Tm.len_ers _ hT
    simp only [UCtx.next, hf, Bool.false_eq_true, ite_false, Bool.not_false, Bool.and_true, Ctx.advBr_n,
      Ctx.advBr_er, Ctx.advBr_ghost, Ctx.setErs_n, Ctx.setErs_ghost, Ctx.er_upd_cmode, Ctx.er_upd_ghost]
    refine ⟨by simpa [Ctx.n] using hn, fun i hi => ?_, fun j hj => ?_, by simpa using g,
      trivial, trivial, trivial, fun j hj => ?_⟩
    rotate_left 6
    · have h := h1 i hi; simp only [Ctx.er] at h ⊢; rw [Ctx.advBr_erA]; simpa [Ctx.setErs] using h
    · have h := h2 j hj (by omega); simp only [Ctx.er, Ctx.n] at h ⊢; rw [Ctx.advBr_erA]
      simpa [Ctx.setErs, Ctx.n] using h
    simp only [List.contains_append, Bool.or_eq_true] at hj
    rcases hj with hj | hj
    · exact .inl hj
    · right
      simp at hj
      obtain ⟨i, hi, e⟩ := hj
      have hv := List.mem_zipIdx_iff_getElem?.mp hi
      rw [List.getElem?_take] at hv
      split at hv
      · refine ⟨i, e.symm, by simpa [Ctx.n] using ‹_›, ?_⟩
        simp [List.getD_eq_getElem?_getD, hv]
      · cases hv
  | _ => cases h

theorem teleUs_length : ∀ (t : Tm), (teleUs t).length = t.ers.length
  | .bind _ _ r => by simp [teleUs, Tm.ers, teleUs_length r]
  | .fv _ | .bv _ | .nil | .cons .. | .app .. | .tyc .. | .vc .. | .tyCtor _ | .valCtor _
  | .univ | .level | .predates .. | .subterm .. | .fn .. | .mtbl .. | .lvl _ | .tok
  | .clo .. | .nat _ | .ptr _ | .wld _ | .sfv _ | .sbv _ => rfl

theorem machine_tail {b : Nat} {G : UCtx} {ru : List Bool} {rets R : Tm} {rest : Core} {ρ vs outsF : List Tm}
    {Γ' : Ctx} (hR : R.isTele) (hol : outsF.length = R.len) (hn' : Γ'.n = G.Γ.n + R.len)
    (hpo : ∀ i < G.Γ.n, Γ'.er i = G.Γ.er i) (hpn : ∀ k < R.len, Γ'.er (G.Γ.n + k) = R.ers.getD k true)
    (hpg : Γ'.ghost = G.Γ.ghost)
    (ihr : MRun P b (G.next Γ' G.ents) ru rets rest (ρ ++ outsF) vs)
    {U A CU : Uses} {CK : Caps} (hseqU : Uses.seq A CU = some U)
    (hC : usesCore P b (G.next Γ' G.ents) ru rets rest = some (CU, CK))
    {ρS vsS outsS ρM outsM : List Tm} {H H2 : Heap} {Res Out Shr : Nat → Prop} {pd : Pend}
    (hS : SimEnv P G.Γ.er ρS ρ) (hM : MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr) (hG : GOK P G pd H ρM ρS ρ Res Shr)
    (hOb : MOut P A G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr R G.ents H2 outsM outsS outsF)
    (hre : Reals P (.ofList outsS) (.ofList outsF) R) (hrest : RunS P (ρS ++ outsS) rest vsS) :
    ∃ H' vsM, RunM P H2 (ρM ++ outsM) none rest H' vsM ∧
      MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  have hf := hG.fill
  have hl := hM.lenF
  have hlS' : outsS.length = R.len := by rw [← hol]; simpa [Tm.toList_ofList] using hre.len
  have huq := usesCore_uq b (G.next Γ' G.ents) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bind hseqU hOb hlS' hol (er' := Γ'.er) hpo
    (fun k hk _ he => by rw [hpn k hk] at he; simpa using he)
    (fun k hk hc _ => by
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
  have hS' : SimEnv P Γ'.er (ρS ++ outsS) (ρ ++ outsF) :=
    hS.extend (by rw [hlS', hol]) (fun i hi => hpo i (by rw [← hl]; exact hi)) fun k a b ha hb he => by
      have hk : k < R.len := by rw [← hol]; exact (List.getElem?_eq_some_iff.mp hb).1
      rw [hl, hpn k hk] at he
      exact hre.get k a b (by simpa [Tm.toList_ofList] using ha) (by simpa [Tm.toList_ofList] using hb) (by simpa using he)
  have hGr := hG.next (Γ' := Γ') (us := G.ents) (H' := H2) (oM := outsM) (oS := outsS) (oF := outsF) (by omega)
    hM.lenM (by rw [hpg]; exact hG.ghost)
  obtain ⟨H', vsM', hrr, hOr⟩ := ihr CU CK hC (ρS ++ outsS) vsS hS' hrest H2 (ρM ++ outsM) Res Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr) hGr
  refine ⟨H', vsM', hrr, lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem MOut.drop {S : Uses} {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {T : Tm} {u : Bool}
    {w uS v : Tm} (hO : MOut P S n er H ρM ρS ρ (fun _ => False) Shr (ret1 T) [u] H1 [w] [uS] [v]) :
    MOut P S n er H ρM ρS ρ (fun _ => False) Shr .nil [] H1 [] [] [] :=
  ⟨hO.wf, hO.next, hO.blk, hO.keep, rfl, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h,
   fun _ _ _ _ h => by simp at h, fun _ _ _ _ h => by simp at h, fun _ _ _ _ _ _ _ _ h => by simp at h⟩

theorem branch_fld (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br}
    {ρ : List Tm} {d c : Nat} {lsF vsF sig0 : Tm} {body : Core} {outsF : List Tm} {cell : Bool}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true) (hslt : ∀ x, s = .fv x → x < G.Γ.n)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hlk : lookupBr brs c = some body)
    (hc : P.ctor d c = some sig0) (hwf : P.wrapField d c = none)
    (hf : G.fill = false) (hg : G.Γ.ghost = false) (huqlt : ∀ j, G.uq.contains j = true → j < G.Γ.n)
    {Hh idx : Tm} {shp : List Arm} {k sig : Tm} (hshp : shp[c]? = some (k, sig, false)) (hsigT : sig.isTele)
    (hlenF : vsF.toList.length = sig.len - 1)
    (hsig : ∀ j, j < sig.len - 1 → sig.ers.getD j true = (sig0.skip (P.lifted d)).ers.getD j true ∧
        sig.uAt j = (sig0.skip (P.lifted d)).uAt j)
    {Gb : UCtx} (hGb : G.branchCtx P s k Hh idx sig false false G.scr cell = some Gb)
    (ihb : MRun P b Gb ru rets body (ρ ++ vsF.toList) outsF)
    (hSb : ∀ ρS lsS vsS, SimEnv P G.Γ.er ρS ρ → P.view (P.sub ρS s) = .app (.vc d c lsS) vsS →
      SimEnv P Gb.Γ.er (ρS ++ vsS.toList) (ρ ++ vsF.toList))
    {S BU0 EU U0 : Uses} {BK0 : Caps} (hSu : G.termUses P G.scr s = some S)
    (hB : usesArms P b G ru rets s Hh idx shp false cell brs = some (BU0, BK0))
    (hseqS : Uses.seq S (Uses.join BU0 EU) = some U0)
    {ρS ρM : List Tm} {H : Heap} {Res0 Out0 Shr : Nat → Prop} (hS : SimEnv P G.Γ.er ρS ρ)
    (hM1 : MFrame P U0 G.Γ.n G.Γ.er H ρM ρS ρ Res0 Out0 Shr)
    {ls' vs' : Tm} (hv : P.view (P.sub ρS s) = .app (.vc d c ls') vs') {outsS : List Tm}
    (hbody : RunS P (ρS ++ vs'.toList) body outsS) :
    ∃ H1 w lsM vsM H2 outsM, P.build H (Tm.env ρM) s = (H1, w) ∧ P.viewM H1 w = .app (.vc d c lsM) vsM ∧
      RunM P H1 (ρM ++ vsM.toList) none body H2 outsM ∧
      MOut P U0 G.Γ.n G.Γ.er H ρM ρS ρ Res0 Shr rets ru H2 outsM outsS outsF := by
  obtain ⟨BU, BK, hBU, hBsub⟩ := usesArms_sel brs BU0 BK0 hB c body hlk k sig false hshp Gb (by simpa using hGb)
  obtain ⟨hGn, hGer, hGer', hGg, hGf, hGrb, hGus, hGuq⟩ := branchCtx_fld hf hsigT hGb
  have hM2 := hM1.split hseqS
  obtain ⟨H1, w, hbuild, hOs⟩ := prim_val_tm (T := .nil) hP hE hS hrt hSu hM2
  have hdw := hOs.dec 0 w (P.sub ρS s) rfl rfl (by simp [Tm.ers, Ent.er])
  obtain ⟨lsM, vsM, hvM⟩ := viewM_of_view hdw hv
  obtain ⟨ruF, hruF0⟩ : ∃ ruF : List Bool, ruF = if G.scr then (teleUs sig).dropLast else [] := ⟨_, rfl⟩
  have hruF : ∀ j, ruF.getD j false = true → G.scr = true ∧ (sig0.skip (P.lifted d)).uAt j = true := by
    intro j hj
    cases hscr : G.scr
    · simp [hruF0, hscr] at hj
    · simp only [hruF0, hscr, ite_true] at hj
      have hj' : j < sig.len - 1 := by
        have := (List.getElem?_eq_some_iff.mp (Option.isSome_iff_exists.mp (by
          simp only [List.getD_eq_getElem?_getD] at hj
          cases e : (teleUs sig).dropLast[j]? <;> simp_all)).choose_spec).1
        rw [List.length_dropLast, teleUs_length, Tm.len_ers _ hsigT] at this; omega
      refine ⟨rfl, ?_⟩
      rw [← (hsig j hj').2, ← teleUs_getD]; exact getD_dropLast hj
  obtain ⟨hOf, hR0⟩ := MOut.fields hOs hvM hv hsF hc hwf hruF
  have hSbS := hSb ρS ls' vs' hS hv
  have hlS : vs'.toList.length = sig.len - 1 := by
    have h1 := hSbS.1; have h2 := hS.1; simp only [List.length_append] at h1; omega
  have hF := (Uses.seq_spec hseqS).1
  have hjs := Uses.join_sub_left BU0 EU
  have hss := (Uses.seq_sub hseqS).2
  obtain ⟨hMb, liftb⟩ := hM1.bindR (A := S) (C := BU) (R0 := fun a => G.scr = true ∧ w = .ptr a) (m := sig.len - 1)
    (er' := Gb.Γ.er) (Uses.seq_sub hseqS).1
    (fun i hi => ⟨fun h => hss.1 i (hjs.1 i (hBsub.1 i (by rwa [Uses.below_lookup hi]))),
      fun h => hss.2 i (hjs.2 i (hBsub.2 i (by rwa [Uses.below_lookup hi])))⟩)
    (fun j hj => ⟨fun h => (by
        have h1 := (hF j).1 h
        cases e : BU.lookup j with
        | none => rfl
        | some x =>
          have := hjs.1 j (hBsub.1 j (by rw [Uses.below_lookup hj, e]; rfl))
          rw [h1] at this; cases this),
      fun h => (hF j).2 (hjs.2 j (hBsub.2 j (by rw [Uses.below_lookup hj]; exact h)))⟩)
    hOf hlS hlenF hGer
    (fun k' hk _ he => by rw [hGer' k' hk, (hsig k' hk).1] at he; exact he)
    (fun k' hk hc' _ => by
      rcases usesCore_uq b Gb ru rets body (hGf.trans hf) BU BK hBU _ (lookup_mem hc') with h1 | h1
      · rcases hGuq _ h1 with h2 | ⟨i, e, hi, h3⟩
        · have := huqlt _ h2; omega
        · have : i = k' := by omega
          subst this; rw [hruF0]; exact h3
      · rw [hGn] at h1; omega)
    (fun a ⟨h1, h2⟩ => (hR0 a h1 h2).1) (fun a ⟨h1, h2⟩ => (hR0 a h1 h2).2.1)
    (fun k' w' u' _ hw hu _ _ b' hft ⟨h1, h2⟩ => (hR0 b' h1 h2).2.2 k' w' u' hw hu b' hft rfl)
  have hGOK : GOK P Gb none H1 (ρM ++ vsM.toList) (ρS ++ vs'.toList) (ρ ++ vsF.toList)
      (fun a => Res0 a ∨ (G.scr = true ∧ w = .ptr a)) Shr := by
    refine ⟨.inl rfl, fun x hx => ?_, fun x hx => (by rw [hGrb] at hx; cases hx), fun j hj => ?_, hGf.trans hf,
      hGg.trans hg⟩
    · rw [hGus] at hx
      cases hscr : G.scr
      · simp [hscr] at hx
      · cases cell
        · simp at hx
        simp only [hscr, Bool.and_self, ite_true, Option.some.injEq] at hx
        have hxn := hslt x hx
        refine ⟨by rw [hGn]; omega, fun a ha => .inr ⟨rfl, ?_⟩⟩
        rw [Tm.env_append (by rw [hM1.lenM]; exact hxn)] at ha
        subst hx
        simp only [Prog.build, Prod.mk.injEq] at hbuild
        rw [← hbuild.2, ha]
    · rcases hGuq j hj with h2 | ⟨i, e, hi, -⟩
      · have := huqlt _ h2; rw [hGn]; omega
      · omega
  obtain ⟨H2, outsM, hrb, hOb⟩ := ihb BU BK hBU (ρS ++ vs'.toList) outsS hSbS hbody H1 (ρM ++ vsM.toList) _ _ Shr none
    (by rw [hGn]; exact hMb) hGOK
  rw [hGn] at hOb
  exact ⟨H1, w, lsM, vsM, H2, outsM, hbuild, hvM, hrb, liftb hOb⟩

theorem machine_mtch_fld (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s R : Tm} {brs : List Br}
    {els : Option Core} {rest : Core} {ρ vs : List Tm} {d c : Nat} {lsF vsF sig0 : Tm} {body : Core}
    {outsF : List Tm}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true) (hslt : ∀ x, s = .fv x → x < G.Γ.n) (hR : R.isTele)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hlk : lookupBr brs c = some body)
    (hc : P.ctor d c = some sig0) (hwf : P.wrapField d c = none)
    (hview : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∀ d' c' ls' vs', P.view (P.sub ρS s) = .app (.vc d' c' ls') vs' →
      d' = d ∧ c' = c)
    (hol : outsF.length = R.len)
    (hbr : ∀ H idx shp, G.arms P s false = some (H, idx, shp) → ∃ k sig, shp[c]? = some (k, sig, false) ∧
      sig.isTele ∧ vsF.toList.length = sig.len - 1 ∧
      (∀ j, j < sig.len - 1 → sig.ers.getD j true = (sig0.skip (P.lifted d)).ers.getD j true ∧
        sig.uAt j = (sig0.skip (P.lifted d)).uAt j) ∧
      ∃ Gb, G.branchCtx P s k H idx sig false false G.scr true = some Gb ∧
        MRun P b Gb G.ents R body (ρ ++ vsF.toList) outsF ∧
        (∀ ρS lsS vsS, SimEnv P G.Γ.er ρS ρ → P.view (P.sub ρS s) = .app (.vc d c lsS) vsS →
          SimEnv P Gb.Γ.er (ρS ++ vsS.toList) (ρ ++ vsF.toList)) ∧
        (∀ ρS', SimEnv P Gb.Γ.er ρS' (ρ ++ vsF.toList) →
          ∃ outsS, RunS P ρS' body outsS ∧ Reals P (.ofList outsS) (.ofList outsF) R))
    (ihr : MRun P b (G.next (G.adv P (G.Γ.pushTele R none) (.mtch s R brs els false rest)) G.ents)
      ru rets rest (ρ ++ outsF) vs) :
    MRun P b G ru rets (.mtch s R brs els false rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.false_or, hg, Bool.false_eq_true, ite_false] at hU hC
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU, EK⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨SBE, hSBE, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqU := UR.seq_fst hU
  have hseqS := UR.seq_fst hSBE
  simp only [UR.join] at hseqS
  obtain ⟨k, sig, hshp, hsigT, hlenF, hsig, Gb, hGb, ihb, hSb, hsb⟩ := hbr Hh idx shp harms
  cases hrun with
  | mtch hv hsel hbody hrest =>
  rename_i d' c' ls' vs' pre body' outsS
  obtain ⟨hd', hc'⟩ := hview ρS hS _ _ _ _ hv
  subst d' c'
  rw [selectBr_lookup hlk] at hsel
  simp only [Option.some.injEq, Prod.mk.injEq] at hsel
  obtain ⟨rfl, rfl⟩ := hsel
  obtain ⟨H1, w, lsM, vsM, H2, outsM, hbuild, hvM, hrb, hOb⟩ := branch_fld hP hE hrt hslt hsF hlk hc hwf hf hg hG.uqlt
    hshp hsigT hlenF hsig hGb ihb hSb hSu hB hseqS hS (hM.split hseqU) hv hbody
  obtain ⟨outsS2, hb2, hre⟩ := hsb _ (hSb ρS ls' vs' hS hv)
  cases RunS.det hbody hb2
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ R none hR
  obtain ⟨H', vsM', hrr, hO⟩ := machine_tail hR hol (Γ' := G.adv P (G.Γ.pushTele R none) (.mtch s R brs els false rest))
    (by rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hR]) (fun i hi => by rw [UCtx.adv_er' hf]; exact hpo i hi)
    (fun k hk => by rw [UCtx.adv_er' hf]; exact hpn k hk) (by rw [UCtx.adv_ghost' hf, hpg]) ihr hseqU hC hS hM hG
    hOb hre hrest
  exact ⟨H', vsM', .mtch hbuild hvM (selectBr_lookup hlk _) hrb hrr, hO⟩

theorem MFrame.addShr {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Out Shr X : Nat → Prop}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (h1 : Disj Res X)
    (h2 : ∀ x < n, U.lookup x = some true → er x = false → Disj (Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x)) X)
    (h3 : ∀ a, X a → a < H.next) : MFrame P U n er H ρM ρS ρ Res Out (fun a => Shr a ∨ X a) :=
  ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, hM.dec, hM.wo, hM.sep, hM.out, hM.res, hM.outb,
   ⟨fun a hr hs => hs.elim (hM.shr.1 a hr) (h1 a hr), fun x hx hU he a hs h => h.elim (hM.shr.2.1 x hx hU he a hs)
     (h2 x hx hU he a hs), fun a h => h.elim (hM.shr.2.2 a) (h3 a)⟩⟩

theorem MOut.dropShr {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Shr X : Nat → Prop}
    {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (hO : MOut P U n er H ρM ρS ρ Res (fun a => Shr a ∨ X a) rets ru H' vsM vsS vs)
    (hX : ∀ a, X a → Live P U n er H ρM ρS a) : MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  refine ⟨hO.wf, hO.next, hO.blk, hO.keep, hO.len, hO.dec, fun k w u hw hu he b hf => ?_, hO.uspine, hO.uwo, hO.usep⟩
  rcases hO.foot k w u hw hu he b hf with h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inr (.inr (.inr (.inl (hX b h))))

theorem branch_els (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm}
    {ρ : List Tm} {body : Core} {outsF : List Tm}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true)
    (hf : G.fill = false) (hg : G.Γ.ghost = false) (huqlt : ∀ j, G.uq.contains j = true → j < G.Γ.n)
    (ihb : MRun P b { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } ru rets body ρ outsF)
    {S BU0 EU U0 : Uses} {EK : Caps} (hSu : G.termUses P G.scr s = some S)
    (hEU : usesCore P b { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } ru rets body = some (EU, EK))
    (hseqS : Uses.seq S (Uses.join BU0 (EU.below G.Γ.n)) = some U0)
    {ρS ρM : List Tm} {H : Heap} {Res0 Out0 Shr : Nat → Prop} (hS : SimEnv P G.Γ.er ρS ρ)
    (hM1 : MFrame P U0 G.Γ.n G.Γ.er H ρM ρS ρ Res0 Out0 Shr) {outsS : List Tm}
    (hbody : RunS P ρS body outsS) :
    ∃ H1 w H2 outsM, P.build H (Tm.env ρM) s = (H1, w) ∧
      (∀ d c ls' vs', P.view (P.sub ρS s) = .app (.vc d c ls') vs' → ∃ lsM vsM, P.viewM H1 w = .app (.vc d c lsM) vsM) ∧
      RunM P H1 ρM none body H2 outsM ∧
      MOut P U0 G.Γ.n G.Γ.er H ρM ρS ρ Res0 Shr rets ru H2 outsM outsS outsF := by
  obtain ⟨H1, w, hbuild⟩ : ∃ H1 w, P.build H (Tm.env ρM) s = (H1, w) := ⟨_, _, rfl⟩
  have hX : ∀ a, (G.scr = true ∧ s.isFv = true ∧ Foot P H1 w (P.sub ρS s) a ∧
      ¬ Spine P H1 w (P.sub ρS s) (s.subst (Tm.env ρ)) a) → ∃ x, x < G.Γ.n ∧ G.Γ.er x = false ∧
      U0.lookup x = some true ∧ Foot P H (Tm.env ρM x) (Tm.env ρS x) a ∧
      ¬ Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) a := by
    rintro a ⟨h1, h2, hf, hns⟩
    cases s <;> simp only [Tm.isFv, Bool.false_eq_true] at h2
    rename_i x
    simp only [UCtx.termUses, UCtx.use, h1] at hSu
    split at hSu
    · cases hSu
    rename_i hc
    simp only [Option.some.injEq] at hSu; subst hSu
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hc
    simp only [Prog.build, Prod.mk.injEq] at hbuild; obtain ⟨rfl, rfl⟩ := hbuild
    exact ⟨x, by omega, by simpa using hc.1.2, (Uses.seq_sub hseqS).1.2 x (by simp [List.lookup]), hf, hns⟩
  have hM1 := hM1.addShr (X := fun a => G.scr = true ∧ s.isFv = true ∧ Foot P H1 w (P.sub ρS s) a ∧
      ¬ Spine P H1 w (P.sub ρS s) (s.subst (Tm.env ρ)) a)
    (fun a hr hxa => let ⟨x, hxn, hex, hU, hf, _⟩ := hX a hxa; hM1.res.1 a hr ⟨x, hxn, by simp [hU], hex, hf⟩)
    (fun z hz hzU hez a hs hxa => by
      obtain ⟨x, hxn, hex, hU, hf, hns⟩ := hX a hxa
      by_cases e : z = x
      · subst e; exact hns hs
      · exact hM1.sep z hz x hxn e hzU (by simp [hU]) hez hex a hs hf)
    (fun a hxa => let ⟨x, hxn, hex, hU, hf, _⟩ := hX a hxa; Foot.lt hM1.wf (hM1.dec x hxn (by simp [hU]) hex) hf)
  have hM2 := hM1.split hseqS
  obtain ⟨H1', w', hb', hOs⟩ := prim_val_tm (T := .nil) hP hE hS hrt hSu hM2
  rw [hbuild, Prod.mk.injEq] at hb'; obtain ⟨rfl, rfl⟩ := hb'
  have hdw := hOs.dec 0 w (P.sub ρS s) rfl rfl (by simp [Tm.ers, Ent.er])
  have hF := (Uses.seq_spec hseqS).1
  have hjs := Uses.join_sub_right BU0 (EU.below G.Γ.n)
  have hss := (Uses.seq_sub hseqS).2
  have hsp := fun (h : G.scr = true) => hOs.uspine 0 w (P.sub ρS s) (s.subst (Tm.env ρ)) rfl rfl rfl
    (by simp [Tm.ers, Ent.er]) (by simp [h])
  obtain ⟨hMb, liftb⟩ := hM1.bindR (A := S) (C := EU) (m := 0) (oM := []) (oS := []) (oF := []) (er' := G.Γ.er)
    (R0 := fun a => G.scr = true ∧ Spine P H1 w (P.sub ρS s) (s.subst (Tm.env ρ)) a) (Uses.seq_sub hseqS).1
    (fun i hi => ⟨fun h => hss.1 i (hjs.1 i (by rwa [Uses.below_lookup hi])),
      fun h => hss.2 i (hjs.2 i (by rwa [Uses.below_lookup hi]))⟩)
    (fun j hj => ⟨fun h => (by
        have h1 := (hF j).1 h
        cases e : EU.lookup j with
        | none => rfl
        | some x =>
          have := hjs.1 j (by rw [Uses.below_lookup hj, e]; rfl)
          rw [h1] at this; cases this),
      fun h => (hF j).2 (hjs.2 j (by rw [Uses.below_lookup hj]; exact h))⟩)
    hOs.drop rfl rfl (fun _ _ => rfl) (fun k hk => by omega) (fun k hk => by omega)
    (fun a ⟨h1, h2⟩ => by
      rcases hsp h1 a h2 with h | h | h
      · exact .inl h
      · exact .inr h
      · exact h.elim)
    (fun a ⟨_, h2⟩ => Foot.blk hdw h2.foot) (fun k _ _ hk => by omega)
  have hGOK : GOK P { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } none H1 (ρM ++ []) (ρS ++ []) (ρ ++ [])
      (fun a => Res0 a ∨ (G.scr = true ∧ Spine P H1 w (P.sub ρS s) (s.subst (Tm.env ρ)) a))
      (fun a => Shr a ∨ (G.scr = true ∧ s.isFv = true ∧ Foot P H1 w (P.sub ρS s) a ∧
        ¬ Spine P H1 w (P.sub ρS s) (s.subst (Tm.env ρ)) a)) := by
    refine ⟨.inl rfl, fun x hx => (by cases hx), fun t ht => ?_, huqlt, hf, hg⟩
    cases hscr : G.scr <;> cases hfv : s.isFv <;> simp [hscr, hfv] at ht
    subst ht
    cases s <;> simp only [Tm.isFv, Bool.false_eq_true] at hfv
    rename_i x
    simp only [Prog.build, Prod.mk.injEq] at hbuild; obtain ⟨rfl, rfl⟩ := hbuild
    simp only [List.append_nil]
    refine ⟨x, rfl, by simp, fun b' h => .inr ⟨by simp, h⟩, fun b' hf' => ?_,
      hOs.uwo 0 _ _ _ rfl rfl rfl (by simp [Tm.ers, Ent.er]) (by simp [hscr]), hdw⟩
    by_cases hsp' : Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b'
    · exact .inl hsp'
    · exact .inr (.inr ⟨by simp [hscr], by simp [hfv], hf', hsp'⟩)
  obtain ⟨H2, outsM, hrb, hOb⟩ := ihb EU EK hEU ρS outsS (by simpa using hS) (by simpa using hbody) H1 ρM _ _ _ none
    (by simpa using hMb) (by simpa using hGOK)
  exact ⟨H1, w, H2, outsM, hbuild, fun _ _ _ _ hv => viewM_of_view hdw hv, by simpa using hrb, (liftb (by simpa using hOb)).dropShr
    fun a hxa => let ⟨x, hxn, hex, hU, hf, _⟩ := hX a hxa; ⟨x, hxn, by simp [hU], hex, hf⟩⟩

theorem machine_mtch_els (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s R : Tm} {brs : List Br}
    {els : Option Core} {rest : Core} {ρ vs : List Tm} {d c : Nat} {lsF vsF : Tm} {body : Core} {outsF : List Tm}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true) (hR : R.isTele)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hlk : lookupBr brs c = none) (hel : els = some body)
    (hview : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∀ d' c' ls' vs', P.view (P.sub ρS s) = .app (.vc d' c' ls') vs' →
      d' = d ∧ c' = c)
    (hol : outsF.length = R.len)
    (ihb : MRun P b { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } G.ents R body ρ outsF)
    (hsb : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∃ outsS, RunS P ρS body outsS ∧ Reals P (.ofList outsS) (.ofList outsF) R)
    (ihr : MRun P b (G.next (G.adv P (G.Γ.pushTele R none) (.mtch s R brs els false rest)) G.ents)
      ru rets rest (ρ ++ outsF) vs) :
    MRun P b G ru rets (.mtch s R brs els false rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [Bool.false_or, hg, Bool.false_eq_true, ite_false] at hU hC
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU0, EK0⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨SBE, hSBE, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqU := UR.seq_fst hU
  have hseqS := UR.seq_fst hSBE
  simp only [UR.join] at hseqS
  subst hel
  rw [usesEls] at hEl
  obtain ⟨⟨EU, EK⟩, hEU, hEl⟩ := Option.bind_eq_some_iff.mp hEl
  simp only [Option.some.injEq, UR.below, Prod.mk.injEq] at hEl
  obtain ⟨rfl, -⟩ := hEl
  cases hrun with
  | mtch hv hsel hbody hrest =>
  rename_i d' c' ls' vs' pre body' outsS
  obtain ⟨hd', hc'⟩ := hview ρS hS _ _ _ _ hv
  subst d' c'
  simp only [selectBr, hlk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsel
  obtain ⟨rfl, rfl⟩ := hsel
  obtain ⟨H1, w, H2, outsM, hbuild, hvw, hrb, hOb⟩ := branch_els hP hE hrt hf hg hG.uqlt ihb
    hSu hEU hseqS hS (hM.split hseqU) (by simpa using hbody)
  obtain ⟨lsM, vsM, hvM⟩ := hvw _ _ _ _ hv
  obtain ⟨outsS2, hb2, hre⟩ := hsb _ hS
  cases RunS.det (by simpa using hbody) hb2
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ R none hR
  obtain ⟨H', vsM', hrr, hO⟩ := machine_tail hR hol (Γ' := G.adv P (G.Γ.pushTele R none) (.mtch s R brs (some body) false rest))
    (by rw [UCtx.adv_n' hf, Ctx.pushTele_n _ hR]) (fun i hi => by rw [UCtx.adv_er' hf]; exact hpo i hi)
    (fun k hk => by rw [UCtx.adv_er' hf]; exact hpn k hk) (by rw [UCtx.adv_ghost' hf, hpg]) ihr hseqU hC hS hM hG
    hOb hre (by simpa using hrest)
  exact ⟨H', vsM', .mtch hbuild hvM (show selectBr brs (some body) c vsM.toList = some ([], body) by simp [selectBr, hlk])
    (by simpa using hrb) hrr, hO⟩

theorem UCtx.scr_and_true (G : UCtx) : { G with scr := G.scr && !false } = G := by
  cases G; simp

theorem machine_case_fld (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br}
    {els : Option Core} {ρ vs : List Tm} {d c : Nat} {lsF vsF sig0 : Tm} {body : Core}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true) (hslt : ∀ x, s = .fv x → x < G.Γ.n)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hlk : lookupBr brs c = some body)
    (hc : P.ctor d c = some sig0) (hwf : P.wrapField d c = none)
    (hview : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∀ d' c' ls' vs', P.view (P.sub ρS s) = .app (.vc d' c' ls') vs' →
      d' = d ∧ c' = c)
    (hbr : ∀ H idx shp, G.arms P s false = some (H, idx, shp) → ∃ k sig, shp[c]? = some (k, sig, false) ∧
      sig.isTele ∧ vsF.toList.length = sig.len - 1 ∧
      (∀ j, j < sig.len - 1 → sig.ers.getD j true = (sig0.skip (P.lifted d)).ers.getD j true ∧
        sig.uAt j = (sig0.skip (P.lifted d)).uAt j) ∧
      ∃ Gb, G.branchCtx P s k H idx sig false false G.scr true = some Gb ∧
        MRun P b Gb ru rets body (ρ ++ vsF.toList) vs ∧
        (∀ ρS lsS vsS, SimEnv P G.Γ.er ρS ρ → P.view (P.sub ρS s) = .app (.vc d c lsS) vsS →
          SimEnv P Gb.Γ.er (ρS ++ vsS.toList) (ρ ++ vsF.toList))) :
    MRun P b G ru rets (.case s brs els false false) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [ite_false, Bool.false_eq_true] at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU, EK⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqS := UR.seq_fst hU
  simp only [UR.join] at hseqS
  obtain ⟨k, sig, hshp, hsigT, hlenF, hsig, Gb, hGb, ihb, hSb⟩ := hbr Hh idx shp harms
  cases hrun with
  | case hv hsel hbody =>
  rename_i d' c' ls' vs' pre body'
  obtain ⟨hd', hc'⟩ := hview ρS hS _ _ _ _ hv
  subst d' c'
  rw [selectBr_lookup hlk] at hsel
  simp only [Option.some.injEq, Prod.mk.injEq] at hsel
  obtain ⟨rfl, rfl⟩ := hsel
  obtain ⟨H1, w, lsM, vsM, H2, outsM, hbuild, hvM, hrb, hOb⟩ := branch_fld hP hE hrt hslt hsF hlk hc hwf hf hg hG.uqlt
    hshp hsigT hlenF hsig hGb ihb hSb hSu (by simpa using hB) hseqS hS hM hv hbody
  exact ⟨H2, outsM, .case hbuild hvM (selectBr_lookup hlk _) hrb, hOb⟩

theorem machine_case_els (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br}
    {ρ vs : List Tm} {d c : Nat} {lsF vsF : Tm} {body : Core}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hlk : lookupBr brs c = none)
    (hview : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∀ d' c' ls' vs', P.view (P.sub ρS s) = .app (.vc d' c' ls') vs' →
      d' = d ∧ c' = c)
    (ihb : MRun P b { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } ru rets body ρ vs) :
    MRun P b G ru rets (.case s brs (some body) false false) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [ite_false, Bool.false_eq_true] at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU0, EK0⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqS := UR.seq_fst hU
  simp only [UR.join] at hseqS
  rw [UCtx.scr_and_true, usesEls] at hEl
  obtain ⟨⟨EU, EK⟩, hEU, hEl⟩ := Option.bind_eq_some_iff.mp hEl
  simp only [Option.some.injEq, UR.below, Prod.mk.injEq] at hEl
  obtain ⟨rfl, -⟩ := hEl
  cases hrun with
  | case hv hsel hbody =>
  rename_i d' c' ls' vs' pre body'
  obtain ⟨hd', hc'⟩ := hview ρS hS _ _ _ _ hv
  subst d' c'
  simp only [selectBr, hlk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsel
  obtain ⟨rfl, rfl⟩ := hsel
  obtain ⟨H1, w, H2, outsM, hbuild, hvw, hrb, hOb⟩ := branch_els hP hE hrt hf hg hG.uqlt ihb
    hSu hEU hseqS hS hM (by simpa using hbody)
  obtain ⟨lsM, vsM, hvM⟩ := hvw _ _ _ _ hv
  exact ⟨H2, outsM, .case hbuild hvM (show selectBr brs (some body) c vsM.toList = some ([], body) by simp [selectBr, hlk])
    (by simpa using hrb), hOb⟩

theorem machine_caseN_els (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br}
    {ρ vs : List Tm} {body : Core} (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true)
    (hreal : realBr brs (some body) = some ([], body))
    (ihb : MRun P b { G with scr := false, ents := [], rebind := (if G.scr && s.isFv then some s else none), uscr := none, cellOk := false } ru rets body ρ vs) :
    MRun P b G ru rets (.case s brs (some body) false true) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [ite_false, Bool.false_eq_true] at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU0, EK0⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqS := UR.seq_fst hU
  simp only [UR.join] at hseqS
  rw [UCtx.scr_and_true, usesEls] at hEl
  obtain ⟨⟨EU, EK⟩, hEU, hEl⟩ := Option.bind_eq_some_iff.mp hEl
  simp only [Option.some.injEq, UR.below, Prod.mk.injEq] at hEl
  obtain ⟨rfl, -⟩ := hEl
  cases hrun with
  | caseN hreal' hbody =>
  rw [hreal] at hreal'
  simp only [Option.some.injEq, Prod.mk.injEq] at hreal'
  obtain ⟨rfl, rfl⟩ := hreal'
  obtain ⟨H1, w, H2, outsM, hbuild, -, hrb, hOb⟩ := branch_els hP hE hrt hf hg hG.uqlt ihb
    hSu hEU hseqS hS hM (by simpa using hbody)
  exact ⟨H2, outsM, .caseN hreal hbuild (by simpa using hrb), hOb⟩

theorem branchCtx_erf {G Gb : UCtx} {s k H idx sig : Tm} {ph cell : Bool} (hf : G.fill = false) (hT : sig.isTele)
    (h : G.branchCtx P s k H idx sig true ph G.scr cell = some Gb) :
    Gb.Γ.n = G.Γ.n + (sig.len - 1) ∧ (∀ i < G.Γ.n, Gb.Γ.er i = G.Γ.er i) ∧
    (∀ j, Gb.Γ.er (G.Γ.n + j) = true) ∧ Gb.Γ.ghost = (G.Γ.ghost || ph) ∧ Gb.fill = G.fill ∧
    Gb.rebind = none ∧ Gb.uscr = none ∧ Gb.uq = G.uq := by
  unfold UCtx.branchCtx at h
  simp only at h
  rcases hb : Ctx.branch P { G.Γ with ghost := G.Γ.ghost || ph } s k H idx sig with ⟨Γf, r⟩
  obtain ⟨eg, eer, en⟩ := Ctx.branch_fields { G.Γ with ghost := G.Γ.ghost || ph } s k H idx sig
  rw [hb] at eg eer en; dsimp only at eg eer en
  rw [hb] at h
  cases r with
  | ok σ =>
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨g, h1, -⟩ := Ctx.openTele_er (sig.len - 1) { G.Γ with ghost := G.Γ.ghost || ph } sig hT
    have hn := Ctx.openTele_n_eq (sig.len - 1) { G.Γ with ghost := G.Γ.ghost || ph } sig hT (by omega)
    rw [← eg] at g; rw [← eer] at h1; rw [← en] at hn
    simp only [UCtx.next, hf, Bool.false_eq_true, ite_false, Bool.not_true, Bool.and_false, Ctx.advBr_er,
      Ctx.advBr_ghost, Ctx.setErs_n, Ctx.setErs_ghost, Ctx.er_setErs, Ctx.er_upd_cmode, Ctx.er_upd_ghost, ite_true, List.take_nil, List.zipIdx_nil,
      List.filterMap_nil, List.append_nil]
    refine ⟨by simpa [Ctx.n] using hn, fun i hi => ?_, fun j => ?_, by simpa using g, trivial, trivial, by simp, trivial⟩
    · have h := h1 i hi; simp only [Ctx.er, Ctx.n] at hi h ⊢; rw [Ctx.advBr_erA]
      simp only [Ctx.setErs]; rw [arrFrom_getD, if_neg (by simp [Ctx.n]; omega)]; exact h
    · simp only [Ctx.er, Ctx.n]; rw [Ctx.advBr_erA]
      simp only [Ctx.setErs]; rw [arrFrom_getD, if_pos (by simp [Ctx.n])]
      simp [Ctx.n, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | _ => cases h

theorem machine_caseE {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br} {els : Option Core}
    {nt : Bool} {ρ vs : List Tm} {c : Nat} {pre preF : List Tm} {body : Core}
    (hreal : realBr brs els = some (pre, body)) (hpl : preF.length = pre.length)
    (hbr : ∀ H idx shp, G.arms P s true = some (H, idx, shp) →
      (∃ k sig ph, lookupBr brs c = some body ∧ shp[c]? = some (k, sig, ph) ∧ sig.isTele ∧ pre.length = sig.len - 1 ∧
        ∃ Gb, G.branchCtx P s k H idx sig true false G.scr (!nt) = some Gb ∧
          MRun P b Gb ru rets body (ρ ++ preF) vs) ∨
      (lookupBr brs c = none ∧ els = some body ∧ pre = [] ∧
        MRun P b { G with scr := false, ents := [], rebind := none, uscr := none, cellOk := false } ru rets body ρ vs)) :
    MRun P b G ru rets (.case s brs els true nt) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [ite_true] at hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp (by simpa using hU)
  obtain ⟨⟨EU0, EK0⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqS := UR.seq_fst hU
  simp only [UR.join] at hseqS
  have hss := (Uses.seq_sub hseqS).2
  cases hrun with
  | caseE hreal' hbody =>
  rw [hreal] at hreal'
  simp only [Option.some.injEq, Prod.mk.injEq] at hreal'
  obtain ⟨rfl, rfl⟩ := hreal'
  rcases hbr Hh idx shp harms with ⟨k, sig, ph, hlk, hshp, hsigT, hlen, Gb, hGb, ihb⟩ | ⟨hlk, hel, hpre, ihb⟩
  · obtain ⟨BU, BK, hBU, hBsub⟩ := usesArms_sel brs BU0 BK0 hB c body hlk k sig ph hshp Gb (by simpa using hGb)
    obtain ⟨hGn, hGer, hGer', hGg, hGf, hGrb, hGus, hGuq⟩ := branchCtx_erf hf hsigT hGb
    have hsubB : Uses.SubB BU U G.Γ.n := (Uses.below_subB BU G.Γ.n).trans
      (((hBsub.trans (Uses.join_sub_left BU0 EU0)).trans hss).subB _)
    obtain ⟨hMb, lift⟩ := (hM.subB hsubB).pushE (oM := pre) (oS := pre) (oF := preF) (er' := Gb.Γ.er)
      rfl rfl (by rw [hpl]) hGer (fun k' _ => hGer' k')
    have hGOK : GOK P Gb none H (ρM ++ pre) (ρS ++ pre) (ρ ++ preF) Res Shr :=
      ⟨.inl rfl, fun x hx => (by rw [hGus] at hx; cases hx), fun x hx => (by rw [hGrb] at hx; cases hx),
       fun j hj => (by rw [hGuq] at hj; have := hG.uqlt j hj; rw [hGn]; omega), hGf.trans hf, by rw [hGg]; simpa using hg⟩
    have hS' : SimEnv P Gb.Γ.er (ρS ++ pre) (ρ ++ preF) :=
      hS.extend hpl.symm (fun i hi => hGer i (by rw [← hM.lenF]; exact hi)) fun k' a b' _ _ he => by
        rw [hM.lenF, hGer' k'] at he; cases he
    obtain ⟨H', vsM, hrr, hO⟩ := ihb BU BK hBU (ρS ++ pre) vsS hS' hbody H (ρM ++ pre) Res Out Shr none
      (by rw [hGn, ← hlen]; exact hMb) hGOK
    rw [hGn, ← hlen] at hO
    exact ⟨H', vsM, .caseE hreal hrr, (lift hO).supB hsubB⟩
  · subst hel hpre
    rw [usesEls] at hEl
    obtain ⟨⟨EU, EK⟩, hEU, hEl⟩ := Option.bind_eq_some_iff.mp hEl
    simp only [Option.some.injEq, UR.below, Prod.mk.injEq] at hEl
    obtain ⟨rfl, -⟩ := hEl
    have hsubB : Uses.SubB EU U G.Γ.n := (Uses.below_subB EU G.Γ.n).trans
      (((Uses.join_sub_right BU0 (EU.below G.Γ.n))).trans hss |>.subB _)
    have hEU' : usesCore P b { G with scr := false, ents := [], rebind := none, uscr := none, cellOk := false } ru rets body =
        some (EU, EK) := by simpa using hEU
    have hGOK : GOK P { G with scr := false, ents := [], rebind := none, uscr := none, cellOk := false } none H ρM ρS ρ Res Shr :=
      ⟨.inl rfl, fun x hx => (by cases hx), fun x hx => (by cases hx), hG.uqlt, hf, hg⟩
    obtain ⟨H', vsM, hrr, hO⟩ := ihb EU EK hEU' ρS vsS hS (by simpa using hbody) H ρM Res Out Shr none (hM.subB hsubB) hGOK
    exact ⟨H', vsM, .caseE hreal (by simpa using hrr), hO.supB hsubB⟩

theorem MOut.ntFields {S : Uses} {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {T : Tm} {scr : Bool}
    {w uS v : Tm} (hO : MOut P S n er H ρM ρS ρ (fun _ => False) Shr (ret1 T) [scr] H1 [w] [uS] [v])
    {d c k0 : Nat} {lsF vsF sig0 : Tm} {ruF : List Bool} {pre : List Tm}
    (hv : v = .app (.vc d c lsF) vsF) (hc : P.ctor d c = some sig0) (hwf : P.wrapField d c = some k0)
    (hone : ∀ j, j < pre.length → (sig0.skip (P.lifted d)).ers.getD j true = false → j = k0)
    (hpl : pre.length = vsF.toList.length)
    (hruF : ∀ k, ruF.getD k false = true → scr = true ∧ (sig0.skip (P.lifted d)).uAt k = true) :
    MOut P S n er H ρM ρS ρ (fun _ => False) Shr (sig0.skip (P.lifted d)) ruF H1 (pre.map fun _ => w)
      (pre.map fun _ => uS) vsF.toList := by
  have e0 : (ret1 T).ers.getD 0 true = false := by simp [Tm.ers, Ent.er]
  have gw : ∀ (j : Nat) x, (pre.map fun _ => w)[j]? = some x → x = w := fun j x h => by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  have gu : ∀ (j : Nat) x, (pre.map fun _ => uS)[j]? = some x → x = uS := fun j x h => by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  subst hv
  refine ⟨hO.wf, hO.next, hO.blk, hO.keep, by simp, fun j x y hx hy _ => ?_, fun j x y hx hy _ b hf => ?_,
    fun j x y z hx hy hz he hr b hs => ?_, fun j x y z hx hy hz he hr => ?_,
    fun j j' x y z x' y' hjj hx hy hz hx' hy' he he' hr => ?_⟩
  · rw [gw j x hx, gu j y hy]; exact hO.dec 0 w uS rfl rfl e0
  · rw [gw j x hx, gu j y hy] at hf; exact hO.foot 0 w uS rfl rfl e0 b hf
  · rw [gw j x hx, gu j y hy] at hs
    obtain ⟨h1, h2⟩ := hruF j hr
    have := hone j (by simpa using (List.getElem?_eq_some_iff.mp hx).1) he; subst this
    exact hO.uspine 0 w uS _ rfl rfl rfl e0 (by simp [h1]) b (.wrap hwf hc h2 hz hs)
  · rw [gw j x hx, gu j y hy]
    obtain ⟨h1, h2⟩ := hruF j hr
    have := hone j (by simpa using (List.getElem?_eq_some_iff.mp hx).1) he; subst this
    have hwo := hO.uwo 0 w uS _ rfl rfl rfl e0 (by simp [h1])
    cases hwo with
    | wrap hw' hc' _ hz' hwo' =>
      rw [hwf] at hw'; cases hw'; rw [hz] at hz'; cases hz'; exact hwo'
    | free hn => exact .free fun b hs => hn b (.wrap hwf hc h2 hz hs)
    | ptr _ hw' => rw [hwf] at hw'; cases hw'
  · exact absurd ((hone j (by simpa using (List.getElem?_eq_some_iff.mp hx).1) he).trans
      (hone j' (by simpa using (List.getElem?_eq_some_iff.mp hx').1) he').symm) hjj

theorem machine_caseN (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets s : Tm} {brs : List Br}
    {els : Option Core} {ρ vs : List Tm} {d c k0 : Nat} {lsF vsF sig0 : Tm} {body : Core} {pre : List Tm}
    (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ s = true)
    (hsF : s.subst (Tm.env ρ) = .app (.vc d c lsF) vsF) (hreal : realBr brs els = some (pre, body))
    (hlk : lookupBr brs c = some body) (hpl : pre.length = vsF.toList.length)
    (hc : P.ctor d c = some sig0) (hwf : P.wrapField d c = some k0)
    (hone : ∀ j, j < pre.length → (sig0.skip (P.lifted d)).ers.getD j true = false → j = k0)
    (hbr : ∀ H idx shp, G.arms P s false = some (H, idx, shp) → ∃ k sig, shp[c]? = some (k, sig, false) ∧
      sig.isTele ∧ vsF.toList.length = sig.len - 1 ∧
      (∀ j, j < sig.len - 1 → sig.ers.getD j true = (sig0.skip (P.lifted d)).ers.getD j true ∧
        sig.uAt j = (sig0.skip (P.lifted d)).uAt j) ∧
      ∃ Gb, G.branchCtx P s k H idx sig false false G.scr false = some Gb ∧
        MRun P b Gb ru rets body (ρ ++ vsF.toList) vs ∧
        (∀ ρS, SimEnv P G.Γ.er ρS ρ → SimEnv P Gb.Γ.er (ρS ++ pre.map fun _ => P.sub ρS s) (ρ ++ vsF.toList))) :
    MRun P b G ru rets (.case s brs els false true) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨Hh, idx, shp⟩, harms, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [ite_false, Bool.false_eq_true] at hU
  obtain ⟨S, hSu, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨BU0, BK0⟩, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨EU, EK⟩, hEl, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseqS := UR.seq_fst hU
  simp only [UR.join] at hseqS
  obtain ⟨k, sig, hshp, hsigT, hlenF, hsig, Gb, hGb, ihb, hSb⟩ := hbr Hh idx shp harms
  obtain ⟨BU, BK, hBU, hBsub⟩ := usesArms_sel brs BU0 BK0 hB c body hlk k sig false hshp Gb (by simpa using hGb)
  obtain ⟨hGn, hGer, hGer', hGg, hGf, hGrb, hGus, hGuq⟩ := branchCtx_fld hf hsigT hGb
  cases hrun with
  | caseN hreal' hbody =>
  rw [hreal] at hreal'
  simp only [Option.some.injEq, Prod.mk.injEq] at hreal'
  obtain ⟨rfl, rfl⟩ := hreal'
  have hM2 := hM.split hseqS
  obtain ⟨H1, w, hbuild, hOs⟩ := prim_val_tm (T := .nil) hP hE hS hrt hSu hM2
  obtain ⟨ruF, hruF0⟩ : ∃ ruF : List Bool, ruF = if G.scr then (teleUs sig).dropLast else [] := ⟨_, rfl⟩
  have hruF : ∀ j, ruF.getD j false = true → G.scr = true ∧ (sig0.skip (P.lifted d)).uAt j = true := by
    intro j hj
    cases hscr : G.scr
    · simp [hruF0, hscr] at hj
    · simp only [hruF0, hscr, ite_true] at hj
      have hj' : j < sig.len - 1 := by
        have := (List.getElem?_eq_some_iff.mp (Option.isSome_iff_exists.mp (by
          simp only [List.getD_eq_getElem?_getD] at hj
          cases e : (teleUs sig).dropLast[j]? <;> simp_all)).choose_spec).1
        rw [List.length_dropLast, teleUs_length, Tm.len_ers _ hsigT] at this; omega
      refine ⟨rfl, ?_⟩
      rw [← (hsig j hj').2, ← teleUs_getD]; exact getD_dropLast hj
  have hOf := MOut.ntFields hOs hsF hc hwf hone hpl hruF
  have hF := (Uses.seq_spec hseqS).1
  have hjs := Uses.join_sub_left BU0 EU
  have hss := (Uses.seq_sub hseqS).2
  have hm : pre.length = sig.len - 1 := by rw [hpl, hlenF]
  obtain ⟨hMb, liftb⟩ := hM.bindR (A := S) (C := BU) (R0 := fun _ => False) (m := sig.len - 1)
    (er' := Gb.Γ.er) (Uses.seq_sub hseqS).1
    (fun i hi => ⟨fun h => hss.1 i (hjs.1 i (hBsub.1 i (by rwa [Uses.below_lookup hi]))),
      fun h => hss.2 i (hjs.2 i (hBsub.2 i (by rwa [Uses.below_lookup hi])))⟩)
    (fun j hj => ⟨fun h => (by
        have h1 := (hF j).1 h
        cases e : BU.lookup j with
        | none => rfl
        | some x =>
          have := hjs.1 j (hBsub.1 j (by rw [Uses.below_lookup hj, e]; rfl))
          rw [h1] at this; cases this),
      fun h => (hF j).2 (hjs.2 j (hBsub.2 j (by rw [Uses.below_lookup hj]; exact h)))⟩)
    hOf (by simp [hm]) (by rw [hlenF]) hGer
    (fun k' hk _ he => by rw [hGer' k' hk, (hsig k' hk).1] at he; exact he)
    (fun k' hk hc' _ => by
      rcases usesCore_uq b Gb ru rets body (hGf.trans hf) BU BK hBU _ (lookup_mem hc') with h1 | h1
      · rcases hGuq _ h1 with h2 | ⟨i, e, hi, h3⟩
        · have := hG.uqlt _ h2; omega
        · have : i = k' := by omega
          subst this; rw [hruF0]; exact h3
      · rw [hGn] at h1; omega)
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ _ _ _ _ _ _ _ _ _ h => h)
  have hGOK : GOK P Gb none H1 (ρM ++ pre.map fun _ => w) (ρS ++ pre.map fun _ => P.sub ρS s) (ρ ++ vsF.toList)
      (fun a => Res a ∨ False) Shr := by
    refine ⟨.inl rfl, fun x hx => ?_, fun x hx => (by rw [hGrb] at hx; cases hx), fun j hj => ?_, hGf.trans hf,
      hGg.trans hg⟩
    · rw [hGus] at hx; simp at hx
    · rcases hGuq j hj with h2 | ⟨i, e, hi, -⟩
      · have := hG.uqlt _ h2; rw [hGn]; omega
      · omega
  obtain ⟨H2, outsM, hrb, hOb⟩ := ihb BU BK hBU _ vsS (hSb ρS hS) hbody H1 _ _ _ Shr none
    (by rw [hGn]; exact hMb) hGOK
  rw [hGn] at hOb
  exact ⟨H2, outsM, .caseN hreal hbuild hrb, liftb hOb⟩

theorem machine_markMany {b : Nat} {G : UCtx} {ru : List Bool} {rets x : Tm} {m : Mark} {i : Nat} {rest : Core}
    {ρ vs : List Tm} (hm : m = .reuse false ∨ m = .write false)
    (ih : MRun P b { G with cellOk := true } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark m) (.fv i) x rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hg := hG.ghost
  obtain ⟨CU, CK, hC, hsub⟩ : ∃ CU CK, usesCore P b { G with cellOk := true } ru rets rest = some (CU, CK) ∧
      Uses.SubB CU U G.Γ.n := by
    rcases hm with rfl | rfl <;> rw [usesCore] at hU <;>
      obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU <;> simp only [hg, Bool.false_eq_true, ite_false] at hU <;>
      obtain ⟨A, -, hU⟩ := Option.bind_eq_some_iff.mp hU <;>
      exact ⟨CU, CK, hC, ((Uses.seq_sub (UR.seq_fst hU)).2).subB _⟩
  have hG' : GOK P { G with cellOk := true } pd H ρM ρS ρ Res Shr :=
    ⟨hG.pend, hG.uscr, hG.rebind, hG.uqlt, hG.fill, hG.ghost⟩
  cases hrun with
  | chk hr =>
  obtain ⟨H', vsM, hrr, hO⟩ := ih CU CK hC ρS vsS hS hr H ρM Res Out Shr pd (hM.subB hsub) hG'
  exact ⟨H', vsM, .chk (fun m' e => by cases e; rcases hm with rfl | rfl <;> rfl) hrr, hO.supB hsub⟩

theorem MFrame.splitC {U A C : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Out Shr : Nat → Prop}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (h : Uses.seq A C = some U) :
    MFrame P A n er H ρM ρS ρ Res (fun a => Out a ∨ Live P C n er H ρM ρS a) Shr := by
  obtain ⟨sA, sC⟩ := Uses.seq_sub h
  have hfree := (Uses.seq_spec h).1
  refine ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, fun i hi ha he => hM.dec i hi (sA.1 i ha) he,
    fun x hx ha he => hM.wo x hx (sA.2 x ha) he,
    fun x hx z hz hne ha hz' hex hez => hM.sep x hx z hz hne (sA.2 x ha) (sA.1 z hz') hex hez,
    fun x hx ha he a h1 h2 => ?_, ⟨fun a hr hl => hM.res.1 a hr (hl.mono sA), fun a hr ho => ?_,
      fun a hr ho => hM.res.2.2.1 a hr (ho.mono sA), hM.res.2.2.2⟩, fun a h2 => ?_,
    ⟨hM.shr.1, fun x hx ha he => hM.shr.2.1 x hx (sA.2 x ha) he, hM.shr.2.2⟩⟩
  · rcases h2 with h2 | ⟨z, hz, hCz, hez, hf⟩
    · exact hM.out x hx (sA.2 x ha) he a h1 h2
    · have hne : x ≠ z := fun e => by subst e; rw [(hfree x).1 ha] at hCz; cases hCz
      exact hM.sep x hx z hz hne (sA.2 x ha) (sC.1 z hCz) he hez a h1 hf
  · rcases ho with ho | ho
    · exact hM.res.2.1 a hr ho
    · exact hM.res.1 a hr (ho.mono sC)
  · rcases h2 with h2 | ⟨z, hz, hCz, hez, hf⟩
    · exact hM.outb a h2
    · exact Foot.lt hM.wf (hM.dec z hz (sC.1 z hCz) hez) hf

theorem MFrame.bindC {Res2 : Nat → Prop} {U A C : Uses} {n m : Nat} {er er' : Nat → Bool} {H H' : Heap} {ρM ρS ρ oM oS oF : List Tm}
    {Res Out Shr : Nat → Prop} {rets : Tm} {ru : List Bool}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) (sA : A.Sub U) (sC : C.Sub U) (hfree : Uses.Free A C)
    (hO : MOut P A n er H ρM ρS ρ Res Shr rets ru H' oM oS oF) (hlS : oS.length = m) (hlF : oF.length = m)
    (her : ∀ i < n, er' i = er i)
    (hers : ∀ k < m, (C.lookup (n + k)).isSome → er' (n + k) = false → rets.ers.getD k true = false)
    (hu : ∀ k < m, C.lookup (n + k) = some true → er' (n + k) = false → ru.getD k false = true)
    (h2 : ∀ a, Res2 a → Res a)
    (hR2n : ∀ k w u, k < m → oM[k]? = some w → oS[k]? = some u → (C.lookup (n + k)).isSome → er' (n + k) = false →
      ∀ b, Foot P H' w u b → ¬ Res2 b) :
    MFrame P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res2 Out Shr ∧
    ∀ {H'' : Heap} {vsM vsS vs : List Tm} {rets2 : Tm} {ru2 : List Bool},
      MOut P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) Res2 Shr rets2 ru2 H'' vsM vsS vs →
      MOut P U n er H ρM ρS ρ Res Shr rets2 ru2 H'' vsM vsS vs := by
  have hlM : oM.length = m := by rw [hO.len, hlS]
  have cls := fun {i} (hi : i < n + m) => env_cls hM.lenM hM.lenS hM.lenF hlM hlS hlF hi
  have er_old : ∀ {i}, i < n → er' i = false → er i = false := fun hi he => by rw [← her _ hi]; exact he
  have liveRes : ∀ i < n, (C.lookup i).isSome → er i = false → ∀ b, Foot P H (Tm.env ρM i) (Tm.env ρS i) b → ¬ Res b :=
    fun i hi hC he b hf hr => hM.res.1 b hr ⟨i, hi, sC.1 i hC, he, hf⟩
  have hOwn : ∀ i < n, (C.lookup i).isSome → er i = false → ∀ b, Foot P H (Tm.env ρM i) (Tm.env ρS i) b →
      ¬ Own P A n er H ρM ρS ρ b := fun i hi hC hei b hf ⟨x, hx, hA, hex, hs⟩ => by
    have hne : x ≠ i := fun e => by subst e; rw [(hfree x).1 hA] at hC; cases hC
    exact hM.sep x hx i hi hne (sA.2 x hA) (sC.1 i hC) hex hei b hs hf
  have hAg : ∀ i < n, (C.lookup i).isSome → er i = false → Agree H H' (Foot P H (Tm.env ρM i) (Tm.env ρS i)) :=
    fun i hi hC he b hf => hO.keep b (Foot.lt hM.wf (hM.dec i hi (sC.1 i hC) he) hf) (hOwn i hi hC he b hf)
      (liveRes i hi hC he b hf)
  have newSp : ∀ k w u v, k < m → oM[k]? = some w → oS[k]? = some u → oF[k]? = some v →
      C.lookup (n + k) = some true → er' (n + k) = false → ∀ b, Spine P H' w u v b →
      H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Res b :=
    fun k w u v hk hw hu' hv hC he b hs => hO.uspine k w u v hw hu' hv (hers k hk (by simp [hC]) he) (hu k hk hC he) b hs
  have newFt : ∀ k w u, k < m → oM[k]? = some w → oS[k]? = some u → (C.lookup (n + k)).isSome →
      er' (n + k) = false → ∀ b, Foot P H' w u b →
      H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Res b ∨ Live P A n er H ρM ρS b ∨ Shr b :=
    fun k w u hk hw hu' hC he b hf => hO.foot k w u hw hu' (hers k hk hC he) b hf
  have oldSp : ∀ x < n, C.lookup x = some true → er x = false →
      ∀ b, Spine P H' (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b →
      Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b :=
    fun x hx hC he b hs => Spine.bwd (hAg x hx (by simp [hC]) he).spine hs
  have oldFt : ∀ z < n, (C.lookup z).isSome → er z = false → ∀ b, Foot P H' (Tm.env ρM z) (Tm.env ρS z) b →
      Foot P H (Tm.env ρM z) (Tm.env ρS z) b := fun z hz hC he b hf => Foot.bwd (hAg z hz hC he) hf
  have hLive : ∀ a, Live P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) a → H.next ≤ a ∨ Own P A n er H ρM ρS ρ a ∨
      Res a ∨ Live P U n er H ρM ρS a ∨ Shr a := fun a ⟨z, hz, hC, hez, hf⟩ => by
    rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
    · rw [f1, f2] at hf
      have he := er_old hzn hez
      exact .inr (.inr (.inr (.inl ⟨z, hzn, sC.1 z hC, he, oldFt z hzn hC he a hf⟩)))
    · rcases newFt j _ _ hj f1 f2 hC hez a hf with h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl (h.mono sA))))
      · exact .inr (.inr (.inr (.inr h)))
  have hOwnC : ∀ a, Own P C (n + m) er' H' (ρM ++ oM) (ρS ++ oS) (ρ ++ oF) a →
      H.next ≤ a ∨ Own P U n er H ρM ρS ρ a ∨ Res a := fun a ⟨x, hx, hC, hex, hs⟩ => by
    rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · rw [e1, e2, e3] at hs
      have he := er_old hxn hex
      exact .inr (.inl ⟨x, hxn, sC.2 x hC, he, oldSp x hxn hC he a hs⟩)
    · rcases newSp k _ _ _ hk e1 e2 e3 hC hex a hs with h | h | h
      · exact .inl h
      · exact .inr (.inl (h.mono sA))
      · exact .inr (.inr h)
  refine ⟨?_, fun {H'' vsM vsS vs rets2 ru2} hR => ?mo⟩
  case mo =>
    refine ⟨hR.wf, Nat.le_trans hO.next hR.next, fun a ha => hR.blk a (hO.blk a ha), fun a ha ho hr => ?_, hR.len,
      hR.dec, fun k w u hw hu' he b hf => ?_, fun k w u v hw hu' hv he hr b hs => ?_, hR.uwo, hR.usep⟩
    · rw [hR.keep a (Nat.lt_of_lt_of_le ha hO.next) (fun h => by
          rcases hOwnC a h with h | h | h
          · omega
          · exact ho h
          · exact hr h) (fun h => hr (h2 a h)), hO.keep a ha (fun h => ho (h.mono sA)) hr]
    · rcases hR.foot k w u hw hu' he b hf with h | h | h | h | h
      · exact .inl (Nat.le_trans hO.next h)
      · rcases hOwnC b h with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inl (h2 b h)))
      · rcases hLive b h with h | h | h | h | h
        · exact .inl h
        · exact .inr (.inl (h.mono sA))
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))
      · exact .inr (.inr (.inr (.inr h)))
    · rcases hR.uspine k w u v hw hu' hv he hr b hs with h | h | h
      · exact .inl (Nat.le_trans hO.next h)
      · rcases hOwnC b h with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · exact .inr (.inr (h2 b h))
  refine ⟨by simp [hM.lenM, hlM], by simp [hM.lenS, hlS], by simp [hM.lenF, hlF], hO.wf, ?_, ?_, ?_, ?_,
    ⟨fun a hr hl => ?_, fun a hr ho => hM.res.2.1 a (h2 a hr) ho, fun a hr ⟨x, hx, hC, hex, hs⟩ => ?_,
     fun a hr => hO.blk a (hM.res.2.2.2 a (h2 a hr))⟩, ?_, ?_⟩
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
      have hAx : A.lookup x = none := (hfree x).2 hCx
      rcases newFt j _ _ hj f1 f2 hCz hez b h2 with h | ⟨y, hy, hAy, hey, hsy⟩ | h | ⟨w, hw, hAw, hew, hfw⟩ | h
      · omega
      · have hne' : y ≠ x := fun e => by subst e; rw [hAx] at hAy; cases hAy
        exact hM.sep y hy x hxn hne' (sA.2 y hAy) (sC.1 x (by simp [hCx])) hey hex' b hsy hs.foot
      · exact liveRes x hxn (by simp [hCx]) hex' b hs.foot h
      · have hne' : x ≠ w := fun e => by subst e; rw [hAx] at hAw; cases hAw
        exact hM.sep x hxn w hw hne' (sC.2 x hCx) (sA.1 w hAw) hex' hew b hs hfw
      · exact hM.shr.2.1 x hxn (sC.2 x hCx) hex' b hs h
    · rw [f1, f2] at h2
      have hez' := er_old hzn hez
      have hf := oldFt z hzn hCz hez' b h2
      rcases newSp k _ _ _ hk e1 e2 e3 hCx hex b h1 with h | ho | h
      · have := Foot.lt hM.wf (hM.dec z hzn (sC.1 z hCz) hez') hf; omega
      · exact hOwn z hzn hCz hez' b hf ho
      · exact liveRes z hzn hCz hez' b hf h
    · exact hO.usep k j _ _ _ _ _ (fun e => hne (by rw [e])) e1 e2 e3 f1 f2 (hers k hk (by simp [hCx]) hex)
        (hers j hj hCz hez) (hu k hk hCx hex) b h1 h2
  · intro x hx hC he b h1 h2
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3] at h1; exact hM.out x hn (sC.2 x hC) he' b (oldSp x hn hC he' b h1) h2
    · rcases newSp k _ _ _ hk e1 e2 e3 hC he b h1 with h | ⟨y, hy, hAy, hey, hsy⟩ | h
      · have := hM.outb b h2; omega
      · exact hM.out y hy (sA.2 y hAy) hey b hsy h2
      · exact hM.res.2.1 b h h2
  · obtain ⟨z, hz, hC, hez, hf⟩ := hl
    rcases cls hz with ⟨hzn, f1, f2, -⟩ | ⟨j, hj, rfl, f1, f2, -⟩
    · rw [f1, f2] at hf
      have he := er_old hzn hez
      exact liveRes z hzn hC he a (oldFt z hzn hC he a hf) (h2 a hr)
    · exact hR2n j _ _ hj f1 f2 hC hez a hf hr
  · rcases cls hx with ⟨hxn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · rw [e1, e2, e3] at hs
      have he := er_old hxn hex
      exact liveRes x hxn (by simp [hC]) he a (oldSp x hxn hC he a hs).foot (h2 a hr)
    · exact hR2n k _ _ hk e1 e2 (by simp [hC]) hex a hs.foot hr
  · intro a ha; exact Nat.lt_of_lt_of_le (hM.outb a ha) hO.next
  · refine ⟨fun a ha hs => hM.shr.1 a (h2 a ha) hs, fun x hx hC he b h1 h2' => ?_,
      fun a ha => Nat.lt_of_lt_of_le (hM.shr.2.2 a ha) hO.next⟩
    rcases cls hx with ⟨hn, e1, e2, e3⟩ | ⟨k, hk, rfl, e1, e2, e3⟩
    · have he' := er_old hn he
      rw [e1, e2, e3] at h1; exact hM.shr.2.1 x hn (sC.2 x hC) he' b (oldSp x hn hC he' b h1) h2'
    · rcases newSp k _ _ _ hk e1 e2 e3 hC he b h1 with h | ⟨y, hy, hAy, hey, hsy⟩ | h
      · have := hM.shr.2.2 b h2'; omega
      · exact hM.shr.2.1 y hy (sA.2 y hAy) hey b hsy h2'
      · exact hM.shr.1 b h h2'

theorem buildArgs_eq {f : Nat → Tm} : ∀ (args : Tm) (H : Heap), args.isList →
    P.buildArgs H f args = ((P.buildList H f args.toList).1, Tm.ofList (P.buildList H f args.toList).2) := by
  intro args; induction args with
  | nil => intro H _; simp [Prog.buildArgs, Prog.buildList, Tm.toList, Tm.subst, Tm.ofList]
  | cons a as _ ih =>
    intro H h; simp only [Tm.isList] at h
    simp only [Prog.buildArgs, Prog.buildList, Tm.toList, Tm.ofList]; rw [ih _ h]
  | _ => intro H h; simp [Tm.isList] at h

theorem argsUses_ret {G : UCtx} (u : Bool) : ∀ (args s : Tm),
    G.argsUses P (fun k => u && k.u) args s = G.retUses P (s.kinds.map fun k => u && k.u) args s := by
  intro args; induction args with
  | cons a as _ ih =>
    intro s
    cases s with
    | bind k T r =>
      simp only [UCtx.argsUses, UCtx.retUses, Tm.kinds, List.map_cons, ih r]
    | _ => simp [UCtx.argsUses, UCtx.retUses, Tm.kinds]
  | _ => intro s; cases s <;> simp [UCtx.argsUses, UCtx.retUses, Tm.kinds]

theorem MFrame.noRes {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Out Shr : Nat → Prop}
    (hM : MFrame P U n er H ρM ρS ρ Res Out Shr) : MFrame P U n er H ρM ρS ρ (fun _ => False) Out Shr :=
  ⟨hM.lenM, hM.lenS, hM.lenF, hM.wf, hM.dec, hM.wo, hM.sep, hM.out,
   ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩, hM.outb,
   ⟨fun _ h => h.elim, hM.shr.2⟩⟩

theorem MOut.weakRes {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Shr : Nat → Prop}
    {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (hO : MOut P U n er H ρM ρS ρ (fun _ => False) Shr rets ru H' vsM vsS vs) :
    MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho _ => hO.keep a ha ho id, hO.len, hO.dec,
    fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
  · rcases hO.foot k w u hw hu he b hf with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact h.elim
    · exact .inr (.inr (.inr h))
  · rcases hO.uspine k w u v hw hu hv he hr b hs with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact h.elim

theorem Heap.write_blk (H : Heap) (a : Nat) (blk : Blk) (x : Nat) :
    (H.write a blk).blk x = if x = a then some blk else H.blk x := rfl

theorem MOut.compose {A : Uses} {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {Res Shr : Nat → Prop}
    {fs : Tm} {ru : List Bool} {args' argsS argsF : List Tm}
    (hO : MOut P A n er H ρM ρS ρ (fun _ => False) Shr fs ru H1 args' argsS argsF)
    {a d c : Nat} {sig ls T : Tm} {u : Bool} (hc : P.ctor d c = some sig) (hfs : fs = sig.skip (P.lifted d))
    (hwf : P.wrapField d c = none) (hres : Res a) (hlt : a < H.next) (hab : (H.blk a).isSome)
    (hna : ¬ Own P A n er H ρM ρS ρ a ∧ ¬ Live P A n er H ρM ρS a ∧ ¬ Shr a)
    (hlenF : argsS.length = argsF.length) (hle : args'.length ≤ fs.ers.length)
    (hru : ∀ k, k < args'.length → u = true → fs.uAt k = true → ru.getD k false = true) :
    MOut P A n er H ρM ρS ρ Res Shr (ret1 T) [u] (H1.write a (d, c, (maskArgs fs.ers (Tm.ofList args')).toList))
      [.ptr a] [.app (.vc d c .nil) (maskArgs fs.ers (Tm.ofList argsS))]
      [.app (.vc d c ls) (Tm.ofList argsF)] ∧
    ∀ b, Foot P (H1.write a (d, c, (maskArgs fs.ers (Tm.ofList args')).toList)) (.ptr a)
      (.app (.vc d c .nil) (maskArgs fs.ers (Tm.ofList argsS))) b →
      b = a ∨ H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Live P A n er H ρM ρS b ∨ Shr b := by
  subst hfs
  have hlen := hO.len
  have fieldsNotA : ∀ (k : Nat) w v, args'[k]? = some w → argsS[k]? = some v →
      (sig.skip (P.lifted d)).ers.getD k true = false → ∀ b, Foot P H1 w v b → b ≠ a := by
    intro k w v hw hv he b hf e; rw [e] at hf
    rcases hO.foot k w v hw hv he a hf with h | h | h | h | h
    · omega
    · exact hna.1 h
    · exact h
    · exact hna.2.1 h
    · exact hna.2.2 h
  have agF : ∀ (k : Nat) w v, args'[k]? = some w → argsS[k]? = some v →
      (sig.skip (P.lifted d)).ers.getD k true = false →
      Agree H1 (H1.write a (d, c, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList)) (Foot P H1 w v) :=
    fun k w v hw hv he b hf => by rw [Heap.write_blk, if_neg (fieldsNotA k w v hw hv he b hf)]
  have fld : ∀ (k : Nat) w v, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList[k]? = some w →
      (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList argsS)).toList[k]? = some v →
      w = .tok ∨ ((sig.skip (P.lifted d)).ers.getD k true = false ∧ args'[k]? = some w ∧ argsS[k]? = some v) := by
    intro k w v hw hv
    rcases mask_field (by simpa [Tm.toList_ofList] using hle) hw hv with h | ⟨hk, he, e1, e2⟩
    · exact .inl h
    · rw [Tm.toList_ofList] at hk e1 e2
      refine .inr ⟨he, by rw [← e1]; exact get_getD hk, by rw [← e2]; exact get_getD (by omega)⟩
  have hblk : (H1.write a (d, c, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList)).blk a =
      some (d, c, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList) := by simp [Heap.write_blk]
  have isl : ∀ l : List Tm, (Tm.ofList l).isList := fun l => by induction l <;> simp_all [Tm.ofList, Tm.isList]
  have hW1 := hO.wf
  have hn1 := hO.next
  have footA : ∀ b, Foot P (H1.write a (d, c, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList)) (.ptr a)
      (.app (.vc d c .nil) (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList argsS))) b →
      b = a ∨ H.next ≤ b ∨ Own P A n er H ρM ρS ρ b ∨ Live P A n er H ρM ρS b ∨ Shr b := fun b hf => by
    cases hf with
    | here => exact .inl rfl
    | field hb hw' hv' hf' =>
      rw [hblk] at hb; cases hb
      rcases fld _ _ _ hw' hv' with rfl | ⟨he, h1, h2⟩
      · cases hf'
      · rcases hO.foot _ _ _ h1 h2 he b (Foot.bwd (agF _ _ _ h1 h2 he) hf') with h | h | h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact h.elim
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))
  refine ⟨⟨fun x hx => ?_, by simpa [Heap.write] using hn1, fun x hx => ?_, fun x hx ho hr => ?_, rfl,
    fun k w v hw hv _ => ?_, fun k w v hw hv _ b hf => ?_, fun k w v vF hw hv hvF _ hr b hs => ?_,
    fun k w v vF hw hv hvF _ hr => ?_, fun k j _ _ _ _ _ hkj hw _ _ hw' _ _ _ _ => ?_⟩, footA⟩
  · rw [Heap.write_blk, if_neg (by simp [Heap.write] at hx; omega)]; exact hW1 x (by simpa [Heap.write] using hx)
  · rw [Heap.write_blk]; split
    · rfl
    · exact hO.blk x hx
  · have hxa : x ≠ a := fun e => hr (e ▸ hres)
    rw [Heap.write_blk, if_neg hxa]; exact hO.keep x hx ho id
  · cases k with
    | succ k => simp at hw
    | zero =>
      simp at hw hv; subst hw hv
      have hm := mask_mdecs (P := P) (H := H1.write a (d, c, (maskArgs (sig.skip (P.lifted d)).ers (Tm.ofList args')).toList))
        _ (Tm.ofList args') (Tm.ofList argsS) (isl _) (isl _) (by simp [Tm.toList_ofList, hlen])
        (by simpa [Tm.toList_ofList] using hle) fun k hk he => by
          rw [Tm.toList_ofList] at hk ⊢; rw [Tm.toList_ofList]
          have h1 := get_getD hk
          have h2 := get_getD (show k < argsS.length by omega)
          exact (hO.dec k _ _ h1 h2 he).frame (agF k _ _ h1 h2 he)
      have := MDec.ptr hblk hm
      rwa [Tm.ofList_toList _ (mask_isList _ _ (isl _))] at this
  · cases k with
    | succ k => simp at hw
    | zero =>
      simp at hw hv; subst hw hv
      rcases footA b hf with rfl | h | h | h | h
      · exact .inr (.inr (.inl hres))
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr h)))
  · cases k with
    | succ k => simp at hw
    | zero =>
      simp at hw hv hvF hr; subst hw hv hvF hr
      cases hs with
      | top => exact .inr (.inr hres)
      | field hb _ hc' hk hw' hv' hvF' hs' =>
        rw [hblk] at hb; cases hb
        rw [hc] at hc'; cases hc'
        rcases fld _ _ _ hw' hv' with rfl | ⟨he, h1, h2⟩
        · exact (hs'.imm (by simp) (by simp)).elim
        · rcases hO.uspine _ _ _ _ h1 h2 (by simpa [Tm.toList_ofList] using hvF') he (hru _ (List.getElem?_eq_some_iff.mp h1).1 rfl hk) b
            (Spine.bwd (agF _ _ _ h1 h2 he).spine hs') with h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact h.elim
      | wrap hw2 => rw [hwf] at hw2; cases hw2
  · cases k with
    | succ k => simp at hw
    | zero =>
      simp at hw hv hvF hr; subst hw hv hvF hr
      refine .ptr hblk hwf hc (fun j w' u' hw' hu' hf => ?_) (fun j w' u' v' hk hw' hu' hv' => ?_)
        (fun j w' u' v' hk hw' hu' hv' i w2 u2 hij hw2 hu2 b h1 h2 => ?_)
      · rcases fld _ _ _ hw' hu' with rfl | ⟨he, h1, h2⟩
        · cases hf
        · exact fieldsNotA _ _ _ h1 h2 he a (Foot.bwd (agF _ _ _ h1 h2 he) hf) rfl
      · rcases fld _ _ _ hw' hu' with rfl | ⟨he, h1, h2⟩
        · exact .free fun b h => h.imm (by simp) (by simp)
        · exact (hO.uwo _ _ _ _ h1 h2 (by simpa [Tm.toList_ofList] using hv') he (hru _ (List.getElem?_eq_some_iff.mp h1).1 rfl hk)).fwd (agF _ _ _ h1 h2 he)
      · rcases fld _ _ _ hw' hu' with rfl | ⟨he, h1', h2'⟩
        · exact h1.imm (by simp) (by simp)
        · rcases fld _ _ _ hw2 hu2 with rfl | ⟨he2, h3, h4⟩
          · cases h2
          · exact hO.usep _ _ _ _ _ _ _ (Ne.symm hij) h1' h2' (by simpa [Tm.toList_ofList] using hv') h3 h4 he he2
              (hru _ (List.getElem?_eq_some_iff.mp h1').1 rfl hk) b (Spine.bwd (agF _ _ _ h1' h2' he).spine h1) (Foot.bwd (agF _ _ _ h3 h4 he2) h2)
  · cases k <;> cases j <;> simp_all

theorem Tm.kinds_cons_inv {s : Tm} {k : Ent} {ks : List Ent} (h : s.kinds = k :: ks) :
    ∃ T r, s = .bind k T r ∧ r.kinds = ks := by
  cases s <;> simp [Tm.kinds] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, rfl, rfl⟩

theorem argsUses_nobind {G : UCtx} (md : Ent → Bool) {s : Tm} (h : s.kinds = []) (args : Tm) :
    G.argsUses P md args s = some [] := by
  cases args with
  | cons a as => cases s <;> simp_all [Tm.kinds, UCtx.argsUses]
  | _ => simp [UCtx.argsUses]

theorem rtArgs_nobind {Γ : Ctx} {s : Tm} (h : s.kinds = []) (args : Tm) : rtArgs P Γ args s = (args == .nil) := by
  cases args with
  | cons a as => cases s <;> simp_all [Tm.kinds, rtArgs]
  | nil => simp [rtArgs]
  | _ => simp [rtArgs]

theorem argsUses_kinds {G : UCtx} (md : Ent → Bool) : ∀ (args s1 s2 : Tm), s1.kinds = s2.kinds →
    G.argsUses P md args s1 = G.argsUses P md args s2 := by
  intro args; induction args with
  | cons a as _ ih =>
    intro s1 s2 h
    cases hk : s1.kinds with
    | nil => rw [argsUses_nobind md hk, argsUses_nobind md (h ▸ hk)]
    | cons k ks =>
      obtain ⟨T1, r1, rfl, h1⟩ := Tm.kinds_cons_inv hk
      obtain ⟨T2, r2, rfl, h2⟩ := Tm.kinds_cons_inv (h ▸ hk)
      simp only [UCtx.argsUses, ih r1 r2 (h1.trans h2.symm)]
  | _ => intro s1 s2 _; simp [UCtx.argsUses]

theorem rtArgs_kinds {Γ : Ctx} : ∀ (args s1 s2 : Tm), s1.kinds = s2.kinds → rtArgs P Γ args s1 = rtArgs P Γ args s2 := by
  intro args; induction args with
  | cons a as _ ih =>
    intro s1 s2 h
    cases hk : s1.kinds with
    | nil => rw [rtArgs_nobind hk, rtArgs_nobind (h ▸ hk)]
    | cons k ks =>
      obtain ⟨T1, r1, rfl, h1⟩ := Tm.kinds_cons_inv hk
      obtain ⟨T2, r2, rfl, h2⟩ := Tm.kinds_cons_inv (h ▸ hk)
      simp only [rtArgs, ih r1 r2 (h1.trans h2.symm)]
  | _ => intro s1 s2 _; simp [rtArgs]

theorem MOut.ers_congr {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res Shr : Nat → Prop}
    {r1 r2 : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (h : ∀ k, k < vsM.length → r2.ers.getD k true = r1.ers.getD k true)
    (hO : MOut P U n er H ρM ρS ρ Res Shr r1 ru H' vsM vsS vs) : MOut P U n er H ρM ρS ρ Res Shr r2 ru H' vsM vsS vs := by
  have g : ∀ {k : Nat} {w : Tm}, vsM[k]? = some w → r2.ers.getD k true = false → r1.ers.getD k true = false :=
    fun hw he => by rw [← h _ (List.getElem?_eq_some_iff.mp hw).1]; exact he
  exact ⟨hO.wf, hO.next, hO.blk, hO.keep, hO.len, fun k w u hw hu he => hO.dec k w u hw hu (g hw he),
    fun k w u hw hu he => hO.foot k w u hw hu (g hw he), fun k w u v hw hu hv he => hO.uspine k w u v hw hu hv (g hw he),
    fun k w u v hw hu hv he => hO.uwo k w u v hw hu hv (g hw he),
    fun k j w u v w' u' hkj hw hu hv hw' hu' he he' => hO.usep k j w u v w' u' hkj hw hu hv hw' hu' (g hw he) (g hw' he')⟩

theorem prefix_get {α : Type} {l1 l2 : List α} (h : l1 <+: l2) {k : Nat} (hk : k < l1.length) : l2[k]? = l1[k]? := by
  obtain ⟨t, rfl⟩ := h; exact List.getElem?_append_left hk

theorem norm_id {d c : Nat} {x : Tm} (h : P.natD ≠ some d) : P.norm (.app (.vc d c .nil) x) = .app (.vc d c .nil) x := by
  unfold Prog.norm; split <;> simp_all

theorem rtArgs_isList' {Γ : Ctx} : ∀ (args s : Tm), rtArgs P Γ args s = true → args.isList := by
  intro args; induction args with
  | nil => intro _ _; rfl
  | cons a as _ ih =>
    intro s h
    cases s <;> simp [rtArgs] at h
    exact ih _ h.2
  | _ => intro s h; simp [rtArgs] at h

theorem rtArgs_len {Γ : Ctx} : ∀ {args s : Tm}, rtArgs P Γ args s = true → args.toList.length ≤ s.kinds.length := by
  intro args; induction args with
  | nil => intro s _; simp [Tm.toList]
  | cons a as _ ih =>
    intro s h
    cases s <;> simp [rtArgs] at h
    simp [Tm.toList, Tm.kinds]; exact ih h.2
  | _ => intro s h; simp [rtArgs] at h

theorem reuse_core (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {args sig' sig0 ls T : Tm} {u : Bool}
    {A Aargs : Uses} {d c a : Nat}
    (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrta : rtArgs P G.Γ args sig' = true)
    (hAa : G.argsUses P (fun k => u && k.u) args sig' = some Aargs) (hsub : Uses.SubB Aargs A G.Γ.n)
    (hc0 : P.ctor d c = some sig0) (hpre : sig'.kinds <+: (sig0.skip (P.lifted d)).kinds)
    (hwf : P.wrapField d c = none)
    {H : Heap} {Res Out' Shr : Nat → Prop} (hM : MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ Res Out' Shr) (hres : Res a) :
    MOut P A G.Γ.n G.Γ.er H ρM ρS ρ Res Shr (ret1 T) [u]
      ((P.buildArgs H (Tm.env ρM) args).1.write a (d, c, (maskArgs (P.ctorErs d c) (P.buildArgs H (Tm.env ρM) args).2).toList))
      [.ptr a] [.app (.vc d c .nil) (maskArgs (P.ctorErs d c) (P.subUArgs (Tm.env ρS) args))]
      [.app (.vc d c ls) (args.subst (Tm.env ρ))] ∧
    ∀ b, Foot P ((P.buildArgs H (Tm.env ρM) args).1.write a (d, c,
        (maskArgs (P.ctorErs d c) (P.buildArgs H (Tm.env ρM) args).2).toList)) (.ptr a)
      (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) (P.subUArgs (Tm.env ρS) args))) b → Res b → b = a := by
  have hl := rtArgs_isList' _ _ hrta
  have hers : P.ctorErs d c = (sig0.skip (P.lifted d)).ers := by simp [Prog.ctorErs, hc0]
  have hblkRes : ∀ b, Res b → (H.blk b).isSome := hM.res.2.2.2
  have hltRes : ∀ b, Res b → b < H.next := fun b hb => Nat.lt_of_not_le fun hc => by
    have := hblkRes b hb; rw [hM.wf b hc] at this; cases this
  obtain ⟨H1, vsM, hr, hOa⟩ := machine_ret hP (ts := args) (rets := sig') hrta hE hS rfl
    (ru := sig'.kinds.map fun k => u && k.u) (U := Aargs) (by rw [← argsUses_ret]; exact hAa) (hM.noRes.subB hsub) none
  cases hr with
  | ret hb =>
  have hba := buildArgs_eq (P := P) (f := Tm.env ρM) args H hl
  rw [hb] at hba
  simp only at hba
  rw [hba, hers]
  have hlenA : vsM.length = args.toList.length := by
    have := (buildList_ext (P := P) hM.wf (Tm.env ρM) args.toList).2.2; rw [hb] at this; exact this
  have hlen' : args.toList.length ≤ sig'.kinds.length := by
    have := rtArgs_len (P := P) hrta; omega
  have hkl : sig'.kinds.length ≤ (sig0.skip (P.lifted d)).kinds.length := hpre.length_le
  have hO1 := (hOa.supB hsub).ers_congr (r2 := sig0.skip (P.lifted d)) (fun k hk => by
    rw [Tm.ers_kinds, Tm.ers_kinds]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [prefix_get hpre (by omega)])
  obtain ⟨hO2, hft⟩ := MOut.compose (ls := ls) (T := T) (u := u) (a := a) hO1 hc0 rfl hwf hres (hltRes a hres)
    (hblkRes a hres) ⟨fun ho => hM.res.2.2.1 a hres ho, fun hlv => hM.res.1 a hres hlv, fun hs => hM.shr.1 a hres hs⟩
    (by simp) (by rw [Tm.ers_kinds, List.length_map]; omega)
    (fun k hk hu hua => by
      rw [Tm.uAt_kinds] at hua
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [prefix_get hpre (by omega)] at hua
      simp_all)
  have eS : P.subUArgs (Tm.env ρS) args = Tm.ofList (args.toList.map (P.sub ρS)) := Prog.subUArgs_subst _ _ hl
  have eF : args.subst (Tm.env ρ) = Tm.ofList (args.toList.map (·.subst (Tm.env ρ))) := by
    rw [← Tm.toList_subst _ _ hl, Tm.ofList_toList _ (Tm.isList_subst _ _ hl)]
  rw [eS, eF]
  refine ⟨hO2, fun b hf hr => ?_⟩
  rcases hft b hf with h | h | h | h | h
  · exact h
  · exact absurd (hltRes b hr) (by omega)
  · exact (hM.res.2.2.1 b hr h).elim
  · exact (hM.res.1 b hr h).elim
  · exact (hM.shr.1 b hr h).elim

theorem MFrame.footRes {A : Uses} {n : Nat} {er : Nat → Bool} {H H' : Heap} {ρM ρS ρ : List Tm} {Res Out' Shr : Nat → Prop}
    {rets : Tm} {ru : List Bool} {vsM vsS vs : List Tm} (hM : MFrame P A n er H ρM ρS ρ Res Out' Shr)
    (hO : MOut P A n er H ρM ρS ρ (fun _ => False) Shr rets ru H' vsM vsS vs) {k : Nat} {w u : Tm}
    (hw : vsM[k]? = some w) (hu : vsS[k]? = some u) (he : rets.ers.getD k true = false) {b : Nat}
    (hf : Foot P H' w u b) (hr : Res b) : False := by
  have hlt : b < H.next := Nat.lt_of_not_le fun hc => by
    have := hM.res.2.2.2 b hr; rw [hM.wf b hc] at this; cases this
  rcases hO.foot k w u hw hu he b hf with h | h | h | h | h
  · omega
  · exact hM.res.2.2.1 b hr h
  · exact h
  · exact hM.res.1 b hr h
  · exact hM.shr.1 b hr h

theorem prim_val_reuse (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {t T : Tm} {u : Bool} {A : Uses} {x : Nat}
    (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrt : rt P G.Γ t = true) (hA : G.termUses P u t = some A)
    {H : Heap} {Res Out' Shr : Nat → Prop} (hM : MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ Res Out' Shr)
    (hx : ∀ a, Tm.env ρM x = .ptr a → Res a) :
    ∃ H1 w, P.evalP H ρM (some (.reuse true, .fv x)) (.tm t) = (H1, w) ∧
      MOut P A G.Γ.n G.Γ.er H ρM ρS ρ Res Shr (ret1 T) [u] H1 [w] [P.sub ρS t] [t.subst (Tm.env ρ)] ∧
      ∀ b, Foot P H1 w (P.sub ρS t) b → Res b → Tm.env ρM x = .ptr b := by
  simp only [Prog.evalP]
  cases hre : P.reuse H ρM x t with
  | none =>
    obtain ⟨H1, w, hb, hO⟩ := prim_val_tm hP hE hS hrt hA hM.noRes (T := T)
    exact ⟨H1, w, by simp [hb], hO.weakRes, fun b hf hr => (hM.footRes hO (k := 0) rfl rfl rfl hf hr).elim⟩
  | some p =>
    simp only [Option.getD_some]
    cases t with
    | app h args =>
      simp only [Prog.reuse] at hre
      split at hre
      · rename_i a d c _ heq1 heq2
        split at hre
        · rename_i hcond
          simp only [Option.some.injEq] at hre; subst hre
          suffices hd : ∃ sig' sig0 ls Aargs, rtArgs P G.Γ args sig' = true ∧
              G.argsUses P (fun k => u && k.u) args sig' = some Aargs ∧ Uses.SubB Aargs A G.Γ.n ∧
              P.ctor d c = some sig0 ∧ sig'.kinds <+: (sig0.skip (P.lifted d)).kinds ∧
              P.sub ρS (.app h args) = .app (.vc d c .nil) (maskArgs (P.ctorErs d c) (P.subUArgs (Tm.env ρS) args)) ∧
              (Tm.app h args).subst (Tm.env ρ) = .app (.vc d c ls) (args.subst (Tm.env ρ)) by
            obtain ⟨sig', sig0, ls, Aargs, hrta, hAa, hsub, hc0, hpre, eS, eF⟩ := hd
            obtain ⟨hO, hft⟩ := reuse_core hP (T := T) (ls := ls) hE hS hrta hAa hsub hc0 hpre hcond.1 hM (hx a heq1)
            rw [eS, eF]
            exact ⟨_, _, rfl, hO, fun b hf hr => by rw [heq1, hft b hf hr]⟩
          cases h with
          | vc d' c' ls =>
            simp only [Prog.subU, Tm.vc.injEq] at heq2; obtain ⟨rfl, rfl, -⟩ := heq2
            simp only [rt] at hrt
            split at hrt
            · rename_i sig hc
              simp only [Bool.and_eq_true] at hrt
              simp only [UCtx.termUses] at hA
              split at hA
              · rename_i s hsg
                obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hA
                simp only [Option.some.injEq] at h2; subst h2
                have hk := sigOf_vc hsg hc hP
                exact ⟨_, _, _, _, (by rw [rtArgs_kinds args s _ hk]; exact hrt.2), h1, (fun i _ => ⟨id, id⟩), hc, (by rw [hk]; exact List.prefix_refl _),
                  (by simp only [Prog.sub, Prog.subU, hcond.1]; exact norm_id hcond.2), (by simp [Tm.subst]; rfl)⟩
              · cases hA
            · simp at hrt
          | fv j =>
            have hrt0 := hrt
            simp only [rt] at hrt
            split at hrt
            · rename_i sig hsig
              simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hrt
              obtain ⟨d', c', sig0, ls, hfi, hfF, hc, hk⟩ := heads_ok hP hE hS _ hrt0 j sig (List.mem_cons_self ..) hsig
              simp only [UCtx.termUses] at hA
              split at hA
              · rename_i s hsg
                obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hA
                obtain ⟨h2, hjn, hje⟩ := head_seq h2
                have hss : s = sig := by
                  obtain ⟨T, ht, hT⟩ := UCtx.sigOf_spec hsg
                  cases ht with
                  | fv hj =>
                    rw [hj] at hsig; simp only [Option.map_some, Option.some.injEq] at hsig
                    rcases hT with hT | hT <;> rw [hT] at hsig <;> cases hsig; rfl
                  | fvIs hj _ _ => rw [hj] at hsig; simp [Ctx.canon, canonBy, Tm.subst2] at hsig
                subst hss
                have hri := hM.dec j hjn (Uses.seq_isSome h2 (.inl (by simp))) hje
                rw [hfi] at hri
                have hfm := hri.vc_inv'
                simp only [Prog.subU] at heq2; rw [hfm] at heq2
                simp only [Tm.vc.injEq] at heq2; obtain ⟨rfl, rfl, -⟩ := heq2
                exact ⟨_, _, _, _, hrt.2, h1, ((Uses.seq_sub h2).2.subB _), hc, hk,
                  (by simp only [Prog.sub, Prog.subU, hfi, hcond.1]; exact norm_id hcond.2), (by simp [Tm.subst, hfF]; rfl)⟩
              · cases hA
            · simp at hrt
          | _ => simp [rt] at hrt
        · cases hre
      · cases hre
    | _ => simp [Prog.reuse] at hre

theorem machine_prim_pend {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core}
    {ρ vs : List Tm} {pd : Pend}
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P (p.evalS P ρS) (p.eval P ρ))
    (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false p) (.prim p false rest)) [G.ents.headD false]) ru rets rest
        (ρ ++ [p.eval P ρ]) vs)
    (hval : ∀ T A, G.primTy P p = some T → G.primUses P (G.ents.headD false) p = some A →
      ∀ ρS H ρM Res Out' Shr, SimEnv P G.Γ.er ρS ρ → MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ Res Out' Shr →
      GOK P G pd H ρM ρS ρ Res Shr →
      ∃ H1 w, ∃ Q : Nat → Prop, P.evalP H ρM pd p = (H1, w) ∧ MOut P A G.Γ.n G.Γ.er H ρM ρS ρ Res Shr (ret1 T)
        [G.ents.headD false] H1 [w] [p.evalS P ρS] [p.eval P ρ] ∧
        (∀ a, Foot P H1 w (p.evalS P ρS) a → Res a → Q a) ∧
        ∀ y a, G.uscr = some (.fv y) → Tm.env ρM y = .ptr a → ¬ Q a) :
    ∀ U K, usesCore P b G ru rets (.prim p false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim p false rest) vsS →
    ∀ H ρM Res Out Shr, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G pd H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM pd (.prim p false rest) H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr hM hG
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
  obtain ⟨H1, w, Q, hev, hO, hQ, hQu⟩ := hval T A hT hA ρS H ρM Res _ _ hS (hM.splitC hseq) hG
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushPrim P T false p) (.prim p false rest) := ⟨_, rfl⟩
  rw [← hΓ'] at hC
  have her' : ∀ i, Γ'.er i = if i = G.Γ.n then false else G.Γ.er i := fun i => by
    rw [hΓ', UCtx.adv_er' hf, Ctx.pushPrim_er']
  have hn' : Γ'.n = G.Γ.n + 1 := by rw [hΓ', UCtx.adv_n' hf, Ctx.pushPrim_n]
  have huq := usesCore_uq b (G.next Γ' [G.ents.headD false]) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bindC (Res2 := fun a => Res a ∧ ¬ Q a) (Uses.seq_sub hseq).1 (Uses.seq_sub hseq).2 (Uses.seq_spec hseq).1 hO (m := 1) rfl rfl (er' := Γ'.er)
    (fun i hi => by rw [her', if_neg (by omega)])
    (fun k hk _ _ => by obtain rfl : k = 0 := by omega
                        simp [Tm.ers, Ent.er])
    (fun k hk hc _ => by
      obtain rfl : k = 0 := by omega
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
    (fun _ h => h.1)
    (fun k w' u' hk hw hu' _ _ a hft ⟨hr, hq⟩ => by
      obtain rfl : k = 0 := by omega
      simp at hw hu'; subst hw hu'
      exact hq (hQ a hft hr))
  have hS' : SimEnv P Γ'.er (ρS ++ [p.evalS P ρS]) (ρ ++ [p.eval P ρ]) :=
    hS.extend rfl (fun i hi => by rw [her', if_neg (by rw [← hM.lenF]; omega)]) fun k a b ha hb _ => by
      cases k with
      | zero => simp at ha hb; subst ha hb; exact hreal ρS hS
      | succ k => simp at ha
  have ihT := ih T hT
  rw [← hΓ'] at ihT
  obtain ⟨H', vsM, hrr, hOr⟩ := ihT CU CK hC (ρS ++ [p.evalS P ρS]) vsS hS' hr H1 (ρM ++ [w]) _ Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr)
    (hG.nextR (R2 := fun a => Res a ∧ ¬ Q a) (fun x a hx ha => ⟨(hG.uscr x hx).2 a ha, hQu x a hx ha⟩) (by omega) hM.lenM (by
      rw [hΓ', UCtx.adv_ghost' hf, Ctx.pushPrim_ghost]; exact hg))
  refine ⟨H', vsM, .prim (by simp only [Bool.false_eq_true, ite_false]; exact hev) hrr, lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem machine_prim_inert {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {p : Prim} {rest : Core}
    {ρ vs : List Tm}
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P (p.evalS P ρS) (p.eval P ρ))
    (ih : ∀ T, G.primTy P p = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false p) (.prim p false rest)) [G.ents.headD false]) ru rets rest
        (ρ ++ [p.eval P ρ]) vs)
    (hval : PrimVal P G ρ p) :
    ∀ U K, usesCore P b G ru rets (.prim p false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim p false rest) vsS →
    ∀ H ρM Res Out Shr pd, Pend.Inert P pd p → MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G pd H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM pd (.prim p false rest) H' vsM ∧ MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hin hM hG
  refine machine_prim_pend hreal ih (fun T A hT hA ρS H ρM Res Out' Shr hS hM _ => ?_) U K hU ρS vsS hS hrun H ρM Res Out Shr hM hG
  obtain ⟨H1, w, hev, hO⟩ := hval T A hT hA ρS H ρM Out' Shr hS hM.noRes
  exact ⟨H1, w, fun _ => False, by rw [hin]; exact hev, hO.weakRes, fun _ hf hr => hM.footRes hO (k := 0) rfl rfl rfl hf hr,
    fun _ _ _ _ h => h⟩

theorem machine_prim_reuse (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets t : Tm} {rest : Core}
    {ρ vs : List Tm} {x : Nat} (hE : EnvOK P ρ G.Γ) (hrt : rt P G.Γ t = true)
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P ((Prim.tm t).evalS P ρS) ((Prim.tm t).eval P ρ))
    (ih : ∀ T, G.primTy P (.tm t) = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false (.tm t)) (.prim (.tm t) false rest)) [G.ents.headD false]) ru rets
        rest (ρ ++ [(Prim.tm t).eval P ρ]) vs) :
    ∀ U K, usesCore P b G ru rets (.prim (.tm t) false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim (.tm t) false rest) vsS →
    ∀ H ρM Res Out Shr, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G (some (.reuse true, .fv x)) H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM (some (.reuse true, .fv x)) (.prim (.tm t) false rest) H' vsM ∧
      MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs :=
  machine_prim_pend hreal ih fun T A _ hA ρS H ρM Res Out' Shr hS hM hG => by
    rcases hG.pend with h | ⟨_, h⟩ | ⟨m, x', h, -, hx⟩
    · cases h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨H1, w, hev, hO, hft⟩ := prim_val_reuse hP hE hS hrt hA hM fun a h => (hx x a rfl h).1
      exact ⟨H1, w, fun a => Tm.env ρM x = .ptr a, hev, hO, hft, fun y a hy hya hq => (hx x a rfl hq).2 y hy hya⟩

theorem Tm.sdata_app {h fs : Tm} (hs : (Tm.app h fs).sdata = true) : ∃ d c, h = .vc d c .nil ∧ Tm.sdataL fs = true := by
  unfold Tm.sdata at hs
  split at hs
  · rename_i d c fs' e; cases e; exact ⟨d, c, rfl, hs⟩
  all_goals simp_all

theorem Tm.sdata_vc {d c : Nat} {ls : Tm} (hs : (Tm.vc d c ls).sdata = true) : ls = .nil := by
  unfold Tm.sdata at hs
  split at hs <;> simp_all

def PlaceOK (P : Prog) (H H1 : Heap) (w t : Tm) : Prop :=
  H.Ext H1 ∧ H1.WF ∧ MDec P H1 w t ∧ ∀ b, Foot P H1 w t b → H.next ≤ b

theorem Heap.placeDeep_spec (t : Tm) : ∀ {H : Heap}, H.WF →
    (t.sdata = true → PlaceOK P H (H.placeDeep t).1 (H.placeDeep t).2 t) ∧
    (Tm.sdataL t = true → H.Ext (H.placeDeepL t).1 ∧ (H.placeDeepL t).1.WF ∧ MDecs P (H.placeDeepL t).1 (H.placeDeepL t).2 t.toList ∧
      (∀ (k : Nat) w v b, (H.placeDeepL t).2[k]? = some w → t.toList[k]? = some v → Foot P (H.placeDeepL t).1 w v b → H.next ≤ b) ∧
      Tm.ofList t.toList = t) := by
  induction t with
  | app h fs _ ihf =>
    intro H hW
    refine ⟨fun hs => ?_, fun hs => by simp [Tm.sdataL] at hs⟩
    obtain ⟨d, c, rfl, hs⟩ := Tm.sdata_app hs
    obtain ⟨he, hW1, hd, hf, hl⟩ := (ihf hW).2 hs
    obtain ⟨he2, hW2⟩ := Heap.alloc_ext hW1 (d, c, (H.placeDeepL fs).2)
    simp only [Heap.placeDeep]
    refine ⟨he.trans he2, hW2, ?_, fun b hb => ?_⟩
    · have := MDec.ptr (P := P) (Heap.alloc_new _ _) (hd.mono he2); rwa [hl] at this
    · cases hb with
      | here => exact he.1
      | field hb hw hv hf' =>
        rw [Heap.alloc_new] at hb; cases hb
        exact hf _ _ _ _ hw hv (Foot.back he2 (hd.get _ _ _ hw hv) hf')
  | cons a as iha ihas =>
    intro H hW
    refine ⟨fun hs => by simp [Tm.sdata] at hs, fun hs => ?_⟩
    simp only [Tm.sdataL, Bool.and_eq_true] at hs
    obtain ⟨he1, hW1, hd1, hf1⟩ := (iha hW).1 hs.1
    obtain ⟨he2, hW2, hd2, hf2, hl2⟩ := (ihas hW1).2 hs.2
    simp only [Heap.placeDeepL, Tm.toList]
    refine ⟨he1.trans he2, hW2, .cons (hd1.mono he2) hd2, fun k w v b hw hv hb => ?_, by simp [Tm.ofList, hl2]⟩
    cases k with
    | zero => simp at hw hv; subst hw hv; exact hf1 b (Foot.back he2 hd1 hb)
    | succ k => simp at hw hv; exact Nat.le_trans he1.1 (hf2 k w v b hw hv hb)
  | nil => intro H hW; exact ⟨fun _ => ⟨.refl _, hW, .nil, fun b h => by cases h⟩,
      fun _ => ⟨.refl _, hW, .nil, fun _ _ _ _ h => by simp [Heap.placeDeepL] at h, rfl⟩⟩
  | vc d c ls =>
    intro H hW
    refine ⟨fun hs => ?_, fun hs => by simp [Tm.sdataL] at hs⟩
    cases Tm.sdata_vc hs
    exact ⟨.refl _, hW, .vc, fun b h => by cases h⟩
  | nat => intro H hW; exact ⟨fun _ => ⟨.refl _, hW, .nat, fun b h => by cases h⟩, fun hs => by simp [Tm.sdataL] at hs⟩
  | wld => intro H hW; exact ⟨fun _ => ⟨.refl _, hW, .wld, fun b h => by cases h⟩, fun hs => by simp [Tm.sdataL] at hs⟩
  | tok => intro H hW; exact ⟨fun _ => ⟨.refl _, hW, .tok (.inl rfl), fun b h => by cases h⟩, fun hs => by simp [Tm.sdataL] at hs⟩
  | _ => intro H hW; exact ⟨fun hs => by simp [Tm.sdata] at hs, fun hs => by simp [Tm.sdataL] at hs⟩


theorem Spine.wld_inv {H : Heap} {k : Nat} {u v : Tm} {b : Nat} (h : Spine P H (.wld k) u v b) : False := by
  generalize hw : Tm.wld k = w at h
  induction h <;> cases hw <;> rename_i ih <;> exact ih rfl

theorem MDec.wld_inv {H : Heap} {w : Tm} {k : Nat} (h : MDec P H w (.wld k)) : w = .wld k := by
  cases h; rfl

theorem MDec.view_ctor {H : Heap} {w vs : Tm} {d c : Nat} (h : MDec P H w (.app (.vc d c .nil) vs)) :
    ∃ ws, P.viewM H w = .app (.vc d c .nil) ws := by
  cases h with
  | ptr hb _ => exact ⟨_, by simp [Prog.viewM, hb]; rfl⟩
  | imm => exact ⟨.nil, by simp [Prog.viewM, Prog.view]⟩

theorem machine_wdo (hO : P.OracleOK) {b : Nat} {G : UCtx} {ru : List Bool} {rets w req : Tm} {rest : Core}
    {ρ vs : List Tm}
    (hst : ∀ ρS, SimEnv P G.Γ.er ρS ρ → ∃ k rd c vsS, P.sub ρS w = .wld k ∧ P.requestD = some rd ∧
      P.sub ρS req = .app (.vc rd c .nil) vsS)
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P ((Prim.wNext w).evalS P ρS) ((Prim.wNext w).eval P ρ) ∧
      Real P ((Prim.wAsk w req).evalS P ρS) ((Prim.wAsk w req).eval P ρ))
    (ih : ∀ Tw A, G.primTy P (.wNext w) = some Tw → G.primTy P (.wAsk w req) = some A →
      MRun P b (G.next (G.adv P (G.Γ.pushWdo Tw A w) (.wdo w req rest)) [true, false]) ru rets rest
        (ρ ++ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]) vs) :
    MRun P b G ru rets (.wdo w req rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  obtain ⟨Tw, hTw, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨A, hA, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  simp only [hg, Bool.false_eq_true, ite_false] at hU hC
  split at hU
  case isFalse => cases hU
  rename_i hfv
  obtain ⟨x, rfl⟩ : ∃ x, w = .fv x := by cases w <;> simp [Tm.isFv] at hfv; exact ⟨_, rfl⟩
  obtain ⟨y, rfl⟩ : ∃ y, req = .fv y := by cases req <;> simp [Tm.isFv] at hfv; exact ⟨_, rfl⟩
  obtain ⟨X, hX, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨Y, hY, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨S, hSs, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseq := UR.seq_fst hU
  simp only at hseq
  simp only [UCtx.termUses, UCtx.use] at hX hY
  split at hX
  · cases hX
  rename_i hx
  split at hY
  · cases hY
  rename_i hy
  simp only [Option.some.injEq] at hX hY; subst hX hY
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, decide_eq_false_iff_not, Nat.not_le] at hx hy
  obtain ⟨⟨hxn, hxe⟩, -⟩ := hx
  obtain ⟨⟨hyn, hye⟩, -⟩ := hy
  obtain ⟨sS, sC⟩ := Uses.seq_sub hseq
  have hSx : (S.lookup x).isSome := Uses.seq_isSome hSs (.inl (by simp))
  have hSy : (S.lookup y).isSome := Uses.seq_isSome hSs (.inr (by simp))
  cases hrun with
  | wdo hr =>
  obtain ⟨k, rd, c, vsS0, hwS, hrd, hrS⟩ := hst ρS hS
  have hdx := hM.dec x hxn (sS.1 x hSx) hxe
  have hdy := hM.dec y hyn (sS.1 y hSy) hye
  simp only [Prog.sub, Prog.subU] at hwS hrS
  rw [hwS] at hdx; rw [hrS] at hdy
  have hmx := hdx.wld_inv
  obtain ⟨ws, hvw⟩ := hdy.view_ctor
  obtain ⟨H1, v, hpd⟩ : ∃ H1 v, H.placeDeep (P.ask k c).1 = (H1, v) := ⟨_, _, rfl⟩
  have hask : P.askM H (Tm.env ρM x) (Tm.env ρM y) = (H1, v) := by
    rw [Prog.askM, hmx, hvw]; simpa [Prog.answer] using hpd
  have hansS : (Prim.wAsk (.fv x) (.fv y)).evalS P ρS = (P.ask k c).1 := by
    simp [Prim.evalS, Prog.sub, Prog.subU, hwS, hrS, Prog.answer]
  have hnextS : (Prim.wNext (.fv x)).evalS P ρS = .wld (k + 1) := by
    simp [Prim.evalS, Prog.sub, Prog.subU, hwS, Tm.wnext]
  rw [hansS, hnextS] at hr
  obtain ⟨he, hW1, hd1, hf1⟩ := ((Heap.placeDeep_spec (P := P) (P.ask k c).1 hM.wf).1 (hO.sdata k c))
  rw [hpd] at he hW1 hd1 hf1
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushWdo Tw A (.fv x)) (.wdo (.fv x) (.fv y) rest) := ⟨_, rfl⟩
  rw [← hΓ'] at hC
  have hl := hM.lenF
  have her' : ∀ i, Γ'.er i = if i = G.Γ.n + 1 then false else if i = G.Γ.n then false else G.Γ.er i := fun i => by
    rw [hΓ', UCtx.adv_er' hf, Ctx.er_pushWdo]
  have hn' : Γ'.n = G.Γ.n + 2 := by rw [hΓ', UCtx.adv_n' hf]; simp
  have huq := usesCore_uq b (G.next Γ' [true, false]) ru rets rest hf CU CK hC
  have hResLt : ∀ a, Res a → a < H.next := fun a ha => Nat.lt_of_not_le fun hc => by
    have := hM.res.2.2.2 a ha; rw [hM.wf a hc] at this; cases this
  have hO1 : MOut P S G.Γ.n G.Γ.er H ρM ρS ρ Res Shr
      (.bind (.ty false false false) Tw (.bind (.ty false false false) A .nil)) [true, false] H1 [.wld (k + 1), v]
      [.wld (k + 1), (P.ask k c).1] [(Prim.wNext (.fv x)).eval P ρ, (Prim.wAsk (.fv x) (.fv y)).eval P ρ] := by
    refine ⟨hW1, he.1, fun a ha => ?_, fun a ha _ _ => he.2.2 a ha, rfl, fun k' w' u' hw hu _ => ?_,
      fun k' w' u' hw hu _ b hb => ?_, fun k' w' u' v' hw hu hv _ hr b hs => ?_, fun k' w' u' v' hw hu hv _ hr => ?_,
      fun k' j w' u' v' w2 u2 hne hw hu hv _ _ _ _ hr => ?_⟩
    · obtain ⟨bk, hb⟩ := Option.isSome_iff_exists.mp ha; rw [he.2.1 _ _ hb]; rfl
    · match k', hw, hu with
      | 0, hw, hu => simp at hw hu; subst hw hu; exact .wld
      | 1, hw, hu => simp at hw hu; subst hw hu; exact hd1
      | _ + 2, hw, _ => simp at hw
    · match k', hw, hu with
      | 0, hw, hu => simp at hw hu; subst hw hu; cases hb
      | 1, hw, hu => simp at hw hu; subst hw hu; exact .inl (hf1 b hb)
      | _ + 2, hw, _ => simp at hw
    · match k', hw, hr with
      | 0, hw, _ => simp at hw; subst hw; exact hs.wld_inv.elim
      | 1, _, hr => simp at hr
      | _ + 2, hw, _ => simp at hw
    · match k', hw, hr with
      | 0, hw, _ => simp at hw; subst hw; exact .free fun b h => h.wld_inv
      | 1, _, hr => simp at hr
      | _ + 2, hw, _ => simp at hw
    · match k', hw, hr with
      | 0, hw, _ => simp at hw; subst hw; exact fun b h _ => h.wld_inv
      | 1, _, hr => simp at hr
      | _ + 2, hw, _ => simp at hw
  obtain ⟨hMr, lift⟩ := hM.bindC (Res2 := Res) sS sC (Uses.seq_spec hseq).1 hO1 (m := 2) rfl rfl (er' := Γ'.er)
    (fun i hi => by rw [her', if_neg (by omega), if_neg (by omega)])
    (fun k' hk _ _ => by match k', hk with | 0, _ => rfl | 1, _ => rfl)
    (fun k' hk hc _ => by
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
    (fun _ h => h)
    (fun k' w' u' hk hw hu _ _ a hft hr => by
      have := hResLt a hr
      match k', hw, hu with
      | 0, hw, hu => simp at hw hu; subst hw hu; cases hft
      | 1, hw, hu => simp at hw hu; subst hw hu; have := hf1 a hft; omega
      | _ + 2, hw, _ => simp at hw)
  have hS' : SimEnv P Γ'.er (ρS ++ [.wld (k + 1), (P.ask k c).1])
      (ρ ++ [(Prim.wNext (.fv x)).eval P ρ, (Prim.wAsk (.fv x) (.fv y)).eval P ρ]) := by
    have hR := hreal ρS hS; rw [hnextS, hansS] at hR
    refine hS.extend rfl (fun i hi => by rw [her', if_neg (by omega), if_neg (by omega)]) fun k' a b' ha hb _ => ?_
    match k', ha, hb with
    | 0, ha, hb => simp at ha hb; subst ha hb; exact hR.1
    | 1, ha, hb => simp at ha hb; subst ha hb; exact hR.2
    | _ + 2, ha, _ => simp at ha
  have ihT := ih Tw A hTw hA
  rw [← hΓ'] at ihT
  obtain ⟨H', vsM, hrr, hOr⟩ := ihT CU CK hC _ vsS hS' hr H1 (ρM ++ [.wld (k + 1), v]) Res Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr)
    (hG.nextR (R2 := Res) (fun x a hx ha => (hG.uscr x hx).2 a ha) (by omega) hM.lenM (by
      rw [hΓ', UCtx.adv_ghost' hf]; simpa [Ctx.push] using hg))
  refine ⟨H', vsM, .wdo (by simp only [Prog.sub, Prog.subU]; exact hask) ?_, lift ?_⟩
  · simp only [Prog.sub, Prog.subU, hmx, Tm.wnext]; exact hrr
  · simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem VTy.opq_inv (hP : ProgOK P) {v idx ls : Tm} {d : Nat} {D : Adt} (hD : P.adts[d]? = some D) (ho : D.opq = true)
    (hpl : P.placedD ≠ some d) (hwo : P.worldD ≠ some d) (h : VTy P v (.app (.tyc d ls) idx)) : v = .tok := by
  generalize hX : Tm.app (.tyc d ls) idx = X at h
  cases h with
  | opq => rfl
  | world hw =>
    simp only [Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX; exact (hwo hw).elim
  | con hk _ _ _ he =>
    subst he; simp only [Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX
    simp [Prog.ctor, hD, (hP.opq _ _ hD ho).1] at hk
  | coer hD' hc =>
    simp only [Tm.coer, Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX
    rw [hD] at hD'
  | clo => simp [FnDef.type, Tm.subst] at hX
  | mtbl => simp [Adt.mtbl] at hX
  | placed hq =>
    simp only [Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX; exact (hpl hq).elim
  | _ => simp at hX

theorem cellTy_tok (hP : ProgOK P) {G : UCtx} {ρ : List Tm} (hE : EnvOK P ρ G.Γ) {i : Nat} (hc : G.cellTy P i = true) :
    Tm.env ρ i = .tok := by
  unfold UCtx.cellTy at hc
  split at hc
  · rename_i d ls idx he
    obtain ⟨T, hT, hcT⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨v, -, hv, hvt⟩ := hE.get hT
    obtain ⟨D, hD, ho⟩ : ∃ D, P.adts[d]? = some D ∧ D.opq = true := by
      cases hD : P.adts[d]? <;> simp_all
    have hpl : P.placedD ≠ some d := by intro hq; simp [hq] at hc
    have hwo : P.worldD ≠ some d := by intro hq; simp [hq] at hc
    rw [← hE.canon, hcT] at hvt
    rw [hv]; exact VTy.opq_inv hP hD ho hpl hwo hvt
  · cases hc

theorem MOut.resOwn {U : Uses} {n : Nat} {er : Nat → Bool} {H : Heap} {ρM ρS ρ : List Tm} {Res R Shr : Nat → Prop}
    {rets : Tm} {ru : List Bool} {H' : Heap} {vsM vsS vs : List Tm}
    (hO : MOut P U n er H ρM ρS ρ (fun a => Res a ∨ R a) Shr rets ru H' vsM vsS vs)
    (hR : ∀ a, R a → Own P U n er H ρM ρS ρ a) : MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs := by
  refine ⟨hO.wf, hO.next, hO.blk, fun a ha ho hr => hO.keep a ha ho fun h => h.elim hr fun h => ho (hR a h), hO.len,
    hO.dec, fun k w u hw hu he b hf => ?_, fun k w u v hw hu hv he hr b hs => ?_, hO.uwo, hO.usep⟩
  · rcases hO.foot k w u hw hu he b hf with h | h | (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl (hR b h))
    · exact .inr (.inr (.inr h))
  · rcases hO.uspine k w u v hw hu hv he hr b hs with h | h | (h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inr (.inl (hR b h))

theorem machine_markU (hP : ProgOK P) {b : Nat} {G : UCtx} {ru : List Bool} {rets x : Tm} {m : Mark} {i : Nat}
    {rest : Core} {ρ vs : List Tm} (hm : m = .reuse true ∨ m = .write true) (hE : EnvOK P ρ G.Γ)
    (ih : MRun P b { G with Γ := G.Γ.markPd m (.fv i), cellOk := true } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark m) (.fv i) x rest) ρ vs := by
  have hred : ∀ Γ : Ctx, Γ.markPd m (.fv i) = { Γ with pd := some (.sfv i) } := by
    rcases hm with rfl | rfl <;> intro Γ <;> rfl
  simp only [hred] at ih
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hg := hG.ghost
  obtain ⟨CU, CK, hC, hct, hseq, hi, hei⟩ : ∃ CU CK, usesCore P b { G with Γ := { G.Γ with pd := some (.sfv i) }, cellOk := true } ru rets rest = some (CU, CK) ∧
      G.cellTy P i = true ∧ Uses.seq [(i, true)] CU = some U ∧ i < G.Γ.n ∧ G.Γ.er i = false := by
    have key : ∀ C : UR, (if (!G.cellTy P i) = true then none else do
        let C ← C
        UR.seq (← G.use i true, []) C) = some (U, K) → ∃ CU CK, C = some (CU, CK) ∧
      G.cellTy P i = true ∧ Uses.seq [(i, true)] CU = some U ∧ i < G.Γ.n ∧ G.Γ.er i = false := fun C h => by
      split at h
      · cases h
      rename_i hct
      obtain ⟨⟨CU, CK⟩, hC, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [UCtx.use] at hA
      split at hA
      · cases hA
      rename_i hc
      simp only [Option.some.injEq] at hA; subst hA
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hc
      exact ⟨CU, CK, hC, by simpa using hct, UR.seq_fst h, by omega, by simpa using hc.1.2⟩
    rcases hm with rfl | rfl <;> rw [usesCore] at hU <;> simp only [Bool.true_and, hg, Bool.not_false,
      Bool.false_eq_true, ite_false] at hU <;> exact key _ hU
  obtain ⟨sA, sC⟩ := Uses.seq_sub hseq
  have hUi : U.lookup i = some true := sA.2 i (by simp [List.lookup])
  have hCi : CU.lookup i = none := ((Uses.seq_spec hseq).1 i).1 (by simp [List.lookup])
  have hρi := cellTy_tok hP hE hct
  have hsp : ∀ a, Tm.env ρM i = .ptr a → Spine P H (Tm.env ρM i) (Tm.env ρS i) (Tm.env ρ i) a :=
    fun a ha => by rw [ha, hρi]; exact .cell
  have hOwn : ∀ a, Tm.env ρM i = .ptr a → Own P U G.Γ.n G.Γ.er H ρM ρS ρ a := fun a ha => ⟨i, hi, hUi, hei, hsp a ha⟩
  have hne : ∀ z, (CU.lookup z).isSome → z ≠ i := fun z hz e => by subst e; rw [hCi] at hz; cases hz
  have hM1 := hM.subB (sC.subB G.Γ.n)
  have hM' : MFrame P CU G.Γ.n G.Γ.er H ρM ρS ρ (fun a => Res a ∨ Tm.env ρM i = .ptr a) Out Shr := by
    refine ⟨hM1.lenM, hM1.lenS, hM1.lenF, hM1.wf, hM1.dec, hM1.wo, hM1.sep, hM1.out, ⟨?_, ?_, ?_, ?_⟩, hM1.outb,
      ⟨?_, hM1.shr.2⟩⟩
    · rintro a (hr | ha) ⟨z, hz, hCz, hez, hf⟩
      · exact hM1.res.1 a hr ⟨z, hz, hCz, hez, hf⟩
      · exact hM.sep i hi z hz (hne z hCz).symm hUi (sC.1 z hCz) hei hez a (hsp a ha) hf
    · rintro a (hr | ha) ho
      · exact hM1.res.2.1 a hr ho
      · exact hM.out i hi hUi hei a (hsp a ha) ho
    · rintro a (hr | ha) ⟨z, hz, hCz, hez, hs⟩
      · exact hM1.res.2.2.1 a hr ⟨z, hz, hCz, hez, hs⟩
      · exact hM.sep z hz i hi (hne z (by rw [hCz]; rfl)) (sC.2 z hCz) (by rw [hUi]; rfl) hez hei a hs (by rw [ha]; exact .here)
    · rintro a (hr | ha)
      · exact hM1.res.2.2.2 a hr
      · have hd := hM.dec i hi (by rw [hUi]; rfl) hei
        rw [ha] at hd
        generalize Tm.env ρS i = uS at hd
        cases hd with
        | ptr hb => simp [hb]
        | tok h => rcases h with h | ⟨a', h, hb⟩
                   · cases h
                   · cases h; exact hb
    · rintro a (hr | ha) hs
      · exact hM1.shr.1 a hr hs
      · exact hM.shr.2.1 i hi hUi hei a (hsp a ha) hs
  have hG' : GOK P { G with Γ := { G.Γ with pd := some (.sfv i) }, cellOk := true } (some (m, .fv i)) H ρM ρS ρ (fun a => Res a ∨ Tm.env ρM i = .ptr a) Shr :=
    ⟨.inr (.inr ⟨m, .fv i, rfl, by rcases hm with rfl | rfl <;> simp, fun i' a hi' ha => by
        cases hi'; exact ⟨.inr ha, fun y hy hya => hM.res.2.2.1 a ((hG.uscr y hy).2 a hya) (hOwn a ha)⟩⟩),
      fun y hy => ⟨(hG.uscr y hy).1, fun a ha => .inl ((hG.uscr y hy).2 a ha)⟩,
      fun t ht => let ⟨x, h1, h2, h3, h4⟩ := hG.rebind t ht; ⟨x, h1, h2, fun a ha => .inl (h3 a ha), h4⟩,
      hG.uqlt, hG.fill, hG.ghost⟩
  cases hrun with
  | chk hr =>
  obtain ⟨H', vsM, hrr, hO⟩ := ih CU CK hC ρS vsS hS hr H ρM _ Out Shr _ hM' hG'
  exact ⟨H', vsM, .mark (by rcases hm with rfl | rfl <;> rfl) hrr, (hO.supB (sC.subB _)).resOwn hOwn⟩

theorem MOut.cell {A : Uses} {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {Res Out' Shr : Nat → Prop}
    (hM : MFrame P A n er H ρM ρS ρ Res Out' Shr) (hE : H.Ext H1) (hW : H1.WF) {a : Nat} (ha : Res a ∨ H.next ≤ a)
    (hb : (H1.blk a).isSome) {T : Tm} {u : Bool} :
    MOut P A n er H ρM ρS ρ Res Shr (ret1 T) [u] H1 [.ptr a] [.tok] [.tok] ∧ ∀ b, Foot P H1 (.ptr a) .tok b → b = a := by
  have hf : ∀ b, Foot P H1 (.ptr a) .tok b → b = a := fun b h => by cases h; rfl
  have hr : ∀ b, Foot P H1 (.ptr a) .tok b → H.next ≤ b ∨ Res b := fun b h => by
    rw [hf b h]; exact ha.elim .inr .inl
  refine ⟨⟨hW, hE.1, fun a' h => ?_, fun a' h _ _ => hE.2.2 a' h, rfl, fun k w' u' hw hu _ => ?_,
    fun k w' u' hw hu _ b h => ?_, fun k w' u' v' hw hu hv _ _ b h => ?_, fun k w' u' v' hw hu hv _ _ => ?_,
    fun k j _ _ _ _ _ hne hw _ _ hw' _ _ _ _ => ?_⟩, hf⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h; rw [hE.2.1 a' x hx]; rfl
  · cases k with
    | zero => simp at hw hu; subst hw hu; exact .tok (.inr ⟨a, rfl, hb⟩)
    | succ k => simp at hw
  · cases k with
    | zero => simp at hw hu; subst hw hu; exact (hr b h).elim .inl fun h => .inr (.inr (.inl h))
    | succ k => simp at hw
  · cases k with
    | zero => simp at hw hu hv; subst hw hu hv; exact (hr b h.foot).elim .inl fun h => .inr (.inr h)
    | succ k => simp at hw
  · cases k with
    | zero => simp at hw hu hv; subst hw hu hv; exact .cell
    | succ k => simp at hw
  · cases k <;> cases j <;> simp_all

theorem prim_val_cell {m : Mark} (hm : m = .cellOf ∨ m = .write true) {G : UCtx} {ρ ρS ρM : List Tm} {t T A' : Tm}
    {u : Bool} {A : Uses} {H : Heap} {Res Out' Shr : Nat → Prop} (hM : MFrame P A G.Γ.n G.Γ.er H ρM ρS ρ Res Out' Shr)
    (hx : ∀ x a, t = .fv x → Tm.env ρM x = .ptr a → Res a) :
    ∃ H1 w, P.evalP H ρM (some (m, t)) (.axm A') = (H1, w) ∧
      MOut P A G.Γ.n G.Γ.er H ρM ρS ρ Res Shr (ret1 T) [u] H1 [w] [.tok] [.tok] ∧
      ∀ a, Foot P H1 w .tok a → Res a → ∃ x, t = .fv x ∧ Tm.env ρM x = .ptr a := by
  have key : P.evalP H ρM (some (m, t)) (.axm A') = (H, .tok) ∨
      ∃ x a, t = .fv x ∧ Tm.env ρM x = .ptr a ∧ P.evalP H ρM (some (m, t)) (.axm A') = (H, .ptr a) := by
    rcases hm with rfl | rfl <;> cases t <;> simp [Prog.evalP, Prog.evalM, Prim.evalS, Prim.eval] <;> split <;> simp_all
  rcases key with h | ⟨x, a, rfl, hxa, h⟩
  · exact ⟨H, .tok, h, (MOut.imm hM.noRes (.tok (.inl rfl)) fun b hf => by cases hf).weakRes, fun a hf => by cases hf⟩
  · obtain ⟨hO, hf⟩ := MOut.cell hM (Heap.Ext.refl _) hM.wf (.inl (hx x a rfl hxa)) (hM.res.2.2.2 a (hx x a rfl hxa))
      (T := T) (u := u)
    exact ⟨H, .ptr a, h, hO, fun b hb _ => ⟨x, rfl, by rw [hf b hb]; exact hxa⟩⟩

theorem machine_prim_cell {m : Mark} (hm : m = .cellOf ∨ m = .write true) {b : Nat} {G : UCtx} {ru : List Bool}
    {rets t A' : Tm} {rest : Core} {ρ vs : List Tm}
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P ((Prim.axm A').evalS P ρS) ((Prim.axm A').eval P ρ))
    (ih : ∀ T, G.primTy P (.axm A') = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false (.axm A')) (.prim (.axm A') false rest)) [G.ents.headD false]) ru
        rets rest (ρ ++ [(Prim.axm A').eval P ρ]) vs) :
    ∀ U K, usesCore P b G ru rets (.prim (.axm A') false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim (.axm A') false rest) vsS →
    ∀ H ρM Res Out Shr, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G (some (m, t)) H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM (some (m, t)) (.prim (.axm A') false rest) H' vsM ∧
      MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs :=
  machine_prim_pend hreal ih fun T A _ _ ρS H ρM Res Out' Shr _ hM hG => by
    rcases hG.pend with h | ⟨_, h⟩ | ⟨m', t', h, -, hx⟩
    · cases h
    · rcases hm with rfl | rfl <;> cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨H1, w, hev, hO, hft⟩ := prim_val_cell hm (T := T) (u := G.ents.headD false) hM
        fun x a hx' ha => (hx x a hx' ha).1
      exact ⟨H1, w, _, hev, hO, hft, fun y a hy hya ⟨x, hx', hxa⟩ => (hx x a hx' hxa).2 y hy hya⟩

theorem machine_prim_alloc {b : Nat} {G : UCtx} {ru : List Bool} {rets y A' : Tm} {rest : Core} {ρ vs : List Tm}
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P ((Prim.axm A').evalS P ρS) ((Prim.axm A').eval P ρ))
    (ih : ∀ T, G.primTy P (.axm A') = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false (.axm A')) (.prim (.axm A') false rest)) [G.ents.headD false]) ru
        rets rest (ρ ++ [(Prim.axm A').eval P ρ]) vs) :
    ∀ U K, usesCore P b G ru rets (.prim (.axm A') false rest) = some (U, K) → ∀ ρS vsS, SimEnv P G.Γ.er ρS ρ →
    RunS P ρS (.prim (.axm A') false rest) vsS →
    ∀ H ρM Res Out Shr, MFrame P U G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr → GOK P G (some (.alloc, y)) H ρM ρS ρ Res Shr →
    ∃ H' vsM, RunM P H ρM (some (.alloc, y)) (.prim (.axm A') false rest) H' vsM ∧
      MOut P U G.Γ.n G.Γ.er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs :=
  machine_prim_pend hreal ih fun T A _ _ ρS H ρM Res Out' Shr _ hM _ => by
    obtain ⟨hE, hW⟩ := Heap.alloc_ext hM.wf (0, 0, [])
    obtain ⟨hO, hf⟩ := MOut.cell hM hE hW (a := H.next) (.inr (Nat.le_refl _)) (by simp [Heap.alloc])
      (T := T) (u := G.ents.headD false)
    refine ⟨_, _, fun _ => False, rfl, hO, fun a hft hr => ?_, fun _ _ _ _ h => h⟩
    have := hM.res.2.2.2 a hr
    rw [hf a hft, hM.wf _ (Nat.le_refl _)] at this; cases this

theorem machine_cellOf {b : Nat} {G : UCtx} {ru : List Bool} {rets x y : Tm} {rest : Core} {ρ vs : List Tm}
    (ih : MRun P b { G with Γ := G.Γ.markPd .cellOf x, cellOk := true, uscr := none } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark .cellOf) x y rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  rw [usesCore] at hU
  simp only [hG.ghost, Bool.false_or] at hU
  split at hU
  · rename_i hx
    have hx' : G.uscr = some x := by simpa using hx
    cases hrun with
    | chk hr =>
    obtain ⟨H', vsM, hrr, hO⟩ := ih U K hU ρS vsS hS hr H ρM Res Out Shr _ hM
      ⟨.inr (.inr ⟨.cellOf, x, rfl, .inl rfl, fun x' a hx'' ha => ⟨(hG.uscr x' (hx''▸ hx')).2 a ha, fun _ h => (by cases h)⟩⟩),
       fun _ h => (by cases h), fun t ht => let ⟨x, h1, _, h3⟩ := hG.rebind t ht; ⟨x, h1, rfl, h3⟩,
       hG.uqlt, hG.fill, hG.ghost⟩
    exact ⟨H', vsM, .mark rfl hrr, hO⟩
  · cases hU

theorem machine_alloc {b : Nat} {G : UCtx} {ru : List Bool} {rets x y : Tm} {rest : Core} {ρ vs : List Tm}
    (ih : MRun P b { G with cellOk := true } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark .alloc) x y rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  rw [usesCore] at hU
  cases hrun with
  | chk hr =>
  obtain ⟨H', vsM, hrr, hO⟩ := ih U K hU ρS vsS hS hr H ρM Res Out Shr _ hM
    ⟨.inr (.inl ⟨x, rfl⟩), hG.uscr, hG.rebind, hG.uqlt, hG.fill, hG.ghost⟩
  exact ⟨H', vsM, .mark rfl hrr, hO⟩

theorem evalP_fv (H : Heap) (ρ : List Tm) (pd : Pend) (x : Nat) : P.evalP H ρ pd (.tm (.fv x)) = (H, Tm.env ρ x) := by
  rcases pd with _ | ⟨m, t'⟩
  · rfl
  · cases m <;> (try rename_i bb; cases bb) <;> cases t' <;> rfl

theorem machine_rebind {b : Nat} {G : UCtx} {ru : List Bool} {rets t a0 b0 : Tm} {rest : Core} {ρ vs : List Tm}
    (hrb : G.rebind = some t)
    (hreal : ∀ ρS, SimEnv P G.Γ.er ρS ρ → Real P ((Prim.tm t).evalS P ρS) ((Prim.tm t).eval P ρ))
    (ih : ∀ T, G.primTy P (.tm t) = some T →
      MRun P b (G.next (G.adv P (G.Γ.pushPrim P T false (.tm t)) (.prim (.tm t) false rest)) (G.ents.take 1)) ru rets rest
        (ρ ++ [(Prim.tm t).eval P ρ]) vs) :
    MRun P b G ru rets (.chk (.mark .rebind) a0 b0 (.prim (.tm t) false rest)) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  obtain ⟨x, rfl, huscr, hsp, hft, hwo, hdec⟩ := hG.rebind t hrb
  rw [usesCore] at hU
  simp only [hrb, beq_self_eq_true, ite_true] at hU
  obtain ⟨T, hT, hC⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushPrim P T false (.tm (.fv x))) (.prim (.tm (.fv x)) false rest) := ⟨_, rfl⟩
  rw [← hΓ'] at hC
  have her' : ∀ i, Γ'.er i = if i = G.Γ.n then false else G.Γ.er i := fun i => by
    rw [hΓ', UCtx.adv_er' hf, Ctx.pushPrim_er']
  have hn' : Γ'.n = G.Γ.n + 1 := by rw [hΓ', UCtx.adv_n' hf, Ctx.pushPrim_n]
  have hO : MOut P [] G.Γ.n G.Γ.er H ρM ρS ρ Res Shr (ret1 T) [true] H [Tm.env ρM x] [Tm.env ρS x] [Tm.env ρ x] := by
    refine ⟨hM.wf, Nat.le_refl _, fun _ h => h, fun _ _ _ _ => rfl, rfl, fun k w' u' hw hu _ => ?_,
      fun k w' u' hw hu _ b h => ?_, fun k w' u' v' hw hu hv _ _ b h => ?_, fun k w' u' v' hw hu hv _ _ => ?_,
      fun k j _ _ _ _ _ hne hw _ _ hw' _ _ _ _ => ?_⟩
    · cases k with
      | zero => simp at hw hu; subst hw hu; exact hdec
      | succ k => simp at hw
    · cases k with
      | zero =>
        simp at hw hu; subst hw hu
        rcases hft b h with h | h
        · exact .inr (.inr (.inl (hsp b h)))
        · exact .inr (.inr (.inr (.inr h)))
      | succ k => simp at hw
    · cases k with
      | zero => simp at hw hu hv; subst hw hu hv; exact .inr (.inr (hsp b h))
      | succ k => simp at hw
    · cases k with
      | zero => simp at hw hu hv; subst hw hu hv; exact hwo
      | succ k => simp at hw
    · cases k <;> cases j <;> simp_all
  obtain ⟨hMr, lift⟩ := hM.bindC (Res2 := fun a => Res a ∧ ¬ Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) a)
    (C := U) ⟨fun i h => by simp at h, fun i h => by simp at h⟩ ⟨fun _ h => h, fun _ h => h⟩
    (fun j => ⟨fun h => by simp at h, fun _ => rfl⟩) hO (m := 1) rfl rfl (er' := Γ'.er)
    (fun i hi => by rw [her', if_neg (by omega)])
    (fun k hk _ _ => by obtain rfl : k = 0 := by omega
                        simp [Tm.ers, Ent.er])
    (fun k hk _ _ => by obtain rfl : k = 0 := by omega
                        rfl)
    (fun _ h => h.1)
    (fun k w' u' hk hw hu' _ _ a hft' ⟨hr, hns⟩ => by
      obtain rfl : k = 0 := by omega
      simp at hw hu'; subst hw hu'
      rcases hft a hft' with h | h
      · exact hns h
      · exact hM.shr.1 a hr h)
  have hS' : SimEnv P Γ'.er (ρS ++ [(Prim.tm (.fv x)).evalS P ρS]) (ρ ++ [(Prim.tm (.fv x)).eval P ρ]) :=
    hS.extend rfl (fun i hi => by rw [her', if_neg (by rw [← hM.lenF]; omega)]) fun k a b ha hb _ => by
      cases k with
      | zero => simp at ha hb; subst ha hb; exact hreal ρS hS
      | succ k => simp at ha
  have ihT := ih T hT
  rw [← hΓ'] at ihT
  cases hrun with
  | chk hr =>
  cases hr with
  | prim hr =>
  simp only [Bool.false_eq_true, ite_false] at hr
  obtain ⟨H', vsM, hrr, hOr⟩ := ihT U K hC _ vsS hS' hr H (ρM ++ [Tm.env ρM x]) _ Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr)
    (hG.nextR (fun y a hy _ => by rw [huscr] at hy; cases hy) (by omega) hM.lenM (by
      rw [hΓ', UCtx.adv_ghost' hf, Ctx.pushPrim_ghost]; exact hg))
  have hev := evalP_fv (P := P) H ρM pd x
  refine ⟨H', vsM, .chk (fun m e => by cases e; rfl) (.prim (by simp only [Bool.false_eq_true, ite_false]; exact hev) hrr),
    lift ?_⟩
  simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr

theorem usesCore_rebindSkip {b : Nat} {G : UCtx} {ru : List Bool} {rets a0 b0 : Tm} {rest : Core}
    (hne : ∀ t rest', rest = .prim (.tm t) false rest' → G.rebind ≠ some t) :
    ∀ U K, usesCore P b G ru rets (.chk (.mark .rebind) a0 b0 rest) = some (U, K) → usesCore P b G ru rets rest = some (U, K) :=
  fun U K h => by
    cases rest with
    | prim p er rest' =>
      cases er with
      | true => rw [usesCore] at h; exact h
      | false =>
        cases p with
        | tm t =>
          rw [usesCore] at h
          simp only [beq_iff_eq, hne t rest' rfl, ite_false] at h
          exact h
        | _ => rw [usesCore] at h <;> first | cases h | (intro _ _ e; cases e)
    | _ => rw [usesCore] at h <;> first | cases h | (intro _ _ e; cases e) | (intro _ _ _ e; cases e)

theorem machine_rebindSkip {b : Nat} {G : UCtx} {ru : List Bool} {rets a0 b0 : Tm} {rest : Core} {ρ vs : List Tm}
    (hne : ∀ t rest', rest = .prim (.tm t) false rest' → G.rebind ≠ some t) (ih : MRun P b G ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark .rebind) a0 b0 rest) ρ vs :=
  machine_chkSame (fun m e => by cases e; rfl) (usesCore_rebindSkip hne) ih

theorem usesCore_markNF {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {m : Mark} {u : Bool} {rest : Core}
    (hm : m = .reuse u ∨ m = .write u) (ha : ∀ i, a ≠ .fv i) :
    usesCore P b G ru rets (.chk (.mark m) a x rest) = usesCore P b G ru rets rest := by
  rcases hm with rfl | rfl <;> cases a <;>
    first | exact (ha _ rfl).elim | (rw [usesCore] <;> first | rfl | (intros; contradiction))

theorem machine_markNF {b : Nat} {G : UCtx} {ru : List Bool} {rets a x : Tm} {m : Mark} {rest : Core} {ρ vs : List Tm}
    (hm : m = .reuse true ∨ m = .write true) (ha : ∀ i, a ≠ .fv i) (ih : MRun P b G ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.mark m) a x rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hU' : usesCore P b G ru rets rest = some (U, K) := usesCore_markNF hm ha ▸ hU
  cases hrun with
  | chk hr =>
  obtain ⟨H', vsM, hrr, hO⟩ := ih U K hU' ρS vsS hS hr H ρM Res Out Shr _ hM
    ⟨.inr (.inr ⟨m, a, rfl, by rcases hm with rfl | rfl <;> simp, fun x _ hx => (ha x hx).elim⟩),
     hG.uscr, hG.rebind, hG.uqlt, hG.fill, hG.ghost⟩
  exact ⟨H', vsM, .mark (by rcases hm with rfl | rfl <;> rfl) hrr, hO⟩

theorem machine_opn {b : Nat} {G : UCtx} {ru : List Bool} {rets x : Tm} {oe u nt ex : Bool} {ph : List Bool}
    {H cs : Tm} {m : Nat} {σ' : Nat → Option Tm} {rest : Core} {ρ vs : List Tm}
    (hm : (G.Γ.tys[m]?).map G.Γ.canon = some (.mtbl u nt ex ph H cs))
    (hu : unify G.Γ.n (Ctx.atoms P { G.Γ with opened := (m, oe) :: G.Γ.opened }) G.Γ.σ []
      (Ctx.openEqs P { G.Γ with opened := (m, oe) :: G.Γ.opened } (H :: cs.toList)) = .ok σ')
    (ih : MRun P b { G with Γ := { G.Γ with opened := (m, oe) :: G.Γ.opened, σ := σ' } } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk (.opn oe) (.fv m) x rest) ρ vs :=
  machine_same (G' := { G with Γ := { G.Γ with opened := (m, oe) :: G.Γ.opened, σ := σ' } }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h; simp only [hm, hu] at h; exact h, Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h) (fun H ρM pd H' out h => .chk (fun m e => by cases e) h)

theorem machine_slf {b : Nat} {G : UCtx} {ru : List Bool} {rets x : Tm} {s : Nat} {Γ' : Ctx} {rest : Core}
    {ρ vs : List Tm} (hΓ : G.Γ.slotSelf s = some Γ')
    (ih' : MRun P b { G with Γ := Γ' } ru rets rest ρ vs) :
    MRun P b G ru rets (.chk .slf (.fv s) x rest) ρ vs :=
  have ih : MRun P b { G with Γ := { G.Γ with σ := Γ'.σ, ς := Γ'.ς } } ru rets rest ρ vs := by
    rw [← Ctx.slotSelf_eq hΓ]; exact ih'
  machine_same (G' := { G with Γ := { G.Γ with σ := Γ'.σ, ς := Γ'.ς } }) rfl rfl rfl rfl rfl rfl rfl ih
    (fun U K h => ⟨U, K, by rw [usesCore] at h; simp only [hΓ] at h; rw [Ctx.slotSelf_eq hΓ] at h; exact h,
      Uses.Eqb.refl _ _⟩)
    (fun ρS vsS h => by cases h with | chk h => exact h) (fun H ρM pd H' out h => .chk (fun m e => by cases e) h)

theorem Spine.clo_inv {H : Heap} {w u eF : Tm} {gid j b : Nat} (hs : Spine P H w u (.clo eF gid j) b) :
    (∃ eM eS i, w = .clo eM gid j ∧ u = .clo eS gid j ∧ P.rdU gid j i = true ∧
      Spine P H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i) b) ∨
    ∃ G F t, P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧ F.dele = some t ∧ F.u = true ∧
      Spine P H w u (Tm.env (eF.toList ++ closures eF.toList gid G) t) b := by
  generalize hv : Tm.clo eF gid j = v at hs
  cases hs with
  | clo hi hs => simp only [Tm.clo.injEq] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact .inl ⟨_, _, _, rfl, rfl, hi, hs⟩
  | dele hG hF hd hu hs => simp only [Tm.clo.injEq] at hv; obtain ⟨rfl, rfl, rfl⟩ := hv; exact .inr ⟨_, _, _, hG, hF, hd, hu, hs⟩
  | _ => cases hv

theorem clo_vals {gid n : Nat} {Gr : Group} (hGr : P.groups[gid]? = some Gr) {H : Heap} {ρM ρS ρ : List Tm}
    (hlM : ρM.length = n) (hlS : ρS.length = n) (hlF : ρ.length = n)
    (hdec : ∀ i u, Gr.caps.lookup i = some u → MDec P H (Tm.env ρM i) (Tm.env ρS i))
    (hwo : ∀ i, Gr.caps.lookup i = some true → WO P H (Tm.env ρM i) (Tm.env ρS i) (Tm.env ρ i))
    (hsep : ∀ i i', i ≠ i' → Gr.caps.lookup i = some true → (Gr.caps.lookup i').isSome →
      Disj (Spine P H (Tm.env ρM i) (Tm.env ρS i) (Tm.env ρ i)) (Foot P H (Tm.env ρM i') (Tm.env ρS i')))
    (hdl : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.dele = some t → t < n + k ∧
      (t < n → ∃ u, Gr.caps.lookup t = some u ∧ (u = true → F.u = true) ∧
        (u = false → F.u = true → NoSpine P (Tm.env ρ t))) ∧
      (n ≤ t → (Gr.fns[t - n]?.map (·.u)) = some false)) :
    ∀ (k : Nat) (wM wS wF : Tm), (closuresS ρM gid Gr)[k]? = some wM → (closuresS ρS gid Gr)[k]? = some wS →
      (closures ρ gid Gr)[k]? = some wF → ∃ F : FnDef, Gr.fns[k]? = some F ∧ MDec P H wM wS ∧
      (∀ b, Foot P H wM wS b → ∃ (i : Nat) (u : Bool), Gr.caps.lookup i = some u ∧ (u = true → F.u = true) ∧
        Foot P H (Tm.env ρM i) (Tm.env ρS i) b) ∧
      (∀ b, Spine P H wM wS wF b → F.u = true ∧ ∃ i, Gr.caps.lookup i = some true ∧
        Spine P H (Tm.env ρM i) (Tm.env ρS i) (Tm.env ρ i) b) ∧
      (F.u = true → WO P H wM wS wF) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro wM wS wF hM hS hF
  obtain ⟨F, hFk, rfl⟩ := closuresS_get hM
  obtain ⟨F', hF', rfl⟩ := closuresS_get hS
  rw [hFk] at hF'; cases hF'
  obtain ⟨hk, rfl⟩ := closures_get hF
  have htk : ∀ env : List Tm, ((closuresS env gid Gr).take k).length = k := fun env => by
    simp [closuresS_length]; omega
  have hrd : ∀ i, P.rd gid k i = true → ∃ u, Gr.caps.lookup i = some u ∧ (u = true → F.u = true) := fun i h => by
    simp only [Prog.rd, Prog.fnU, hGr, Option.map_some, Option.getD_some, Option.bind_some, hFk] at h
    cases hl : Gr.caps.lookup i with
    | none => simp [hl] at h
    | some u => refine ⟨u, rfl, fun hu => ?_⟩; subst hu; simp_all
  have hrdU : ∀ i, P.rdU gid k i = true → F.u = true ∧ F.dele = none ∧ Gr.caps.lookup i = some true := fun i h => by
    simp only [Prog.rdU, Prog.fnU, hGr, Option.map_some, Option.getD_some, Option.bind_some, hFk, Bool.and_eq_true,
      Option.isNone_iff_eq_none, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  unfold cval
  cases hd : F.dele with
  | none =>
    simp only [htk]
    refine ⟨F, hFk, .clo (by simp [hlM, hlS]) fun i hi => ?_, fun b hf => ?_, fun b hs => ?_, fun hu => ?_⟩
    · obtain ⟨u, hu, -⟩ := hrd i hi; exact hdec i u hu
    · cases hf with
      | clo hi hf =>
        obtain ⟨u, hu, hu'⟩ := hrd _ hi
        exact ⟨_, u, hu, hu', by simpa [Tm.toList_ofList] using hf⟩
    · cases hs with
      | clo hi hs =>
        obtain ⟨h1, -, h3⟩ := hrdU _ hi
        exact ⟨h1, _, h3, by simpa [Tm.toList_ofList] using hs⟩
      | dele hG' hF' hd' =>
        rw [hGr] at hG'; cases hG'; rw [hFk] at hF'; cases hF'; rw [hd] at hd'; cases hd'
    · refine .clo (fun G' F' hG' hF' => by rw [hGr] at hG'; cases hG'; rw [hFk] at hF'; cases hF'; exact hd)
        (fun i hi => by simpa [Tm.toList_ofList] using hwo i (hrdU i hi).2.2)
        (fun i hi i' hne hi' => by
          obtain ⟨u, hu', -⟩ := hrd i' hi'
          simpa [Tm.toList_ofList] using hsep i i' (Ne.symm hne) (hrdU i hi).2.2 (by simp [hu']))
  | some t =>
    simp only
    obtain ⟨htn, hout, hsib⟩ := hdl k F t hFk hd
    have hdele : ∀ b w u, Spine P H w u (.clo (.ofList ρ) gid k) b →
        F.u = true ∧ Spine P H w u (Tm.env (ρ ++ closures ρ gid Gr) t) b :=
      fun b w u hs => by
      rcases hs.clo_inv with ⟨_, _, i, _, _, hi, _⟩ | ⟨G', F', t', hG', hF', hd', hu, hs⟩
      · exact absurd (hrdU i hi).2.1 (by rw [hd]; simp)
      · rw [hGr] at hG'; cases hG'; rw [hFk] at hF'; cases hF'; rw [hd] at hd'; cases hd'
        exact ⟨hu, by simpa [Tm.toList_ofList] using hs⟩
    by_cases htn' : t < n
    · have e : ∀ (env : List Tm), env.length = n → (env ++ (closuresS env gid Gr).take k).getD t .nil = Tm.env env t :=
        fun env hl => by simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left (show t < env.length by omega)]
      have eF : Tm.env (ρ ++ closures ρ gid Gr) t = Tm.env ρ t := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left (show t < ρ.length by omega)]
      rw [e ρM hlM, e ρS hlS]
      obtain ⟨ut, hl, hut, hns⟩ := hout htn'
      refine ⟨F, hFk, hdec t _ hl, fun b hf => ⟨t, ut, hl, hut, hf⟩, fun b hs => ?_, fun hu => ?_⟩
      · obtain ⟨hu, hs⟩ := hdele b _ _ hs; rw [eF] at hs
        cases ut with
        | true => exact ⟨hu, t, hl, hs⟩
        | false => exact (hns rfl hu _ _ _ _ hs).elim
      · cases ut with
        | true => exact .dele hGr hFk hd hu (by rw [Tm.toList_ofList, eF]; exact hwo t hl)
        | false =>
          refine .free fun b hs => ?_
          obtain ⟨hu', hs⟩ := hdele b _ _ hs; rw [eF] at hs; exact hns rfl hu' _ _ _ _ hs
    · have hk' : t - n < k := by omega
      have hcl : ∀ env : List Tm, t - n < (closuresS env gid Gr).length := fun env => by rw [closuresS_length]; omega
      have e : ∀ (env : List Tm), env.length = n →
          (env ++ (closuresS env gid Gr).take k).getD t .nil = (closuresS env gid Gr)[t - n]'(hcl env) :=
        fun env hl => by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show env.length ≤ t by omega), hl,
            hk', List.getElem?_eq_getElem (hcl env)]
      have hcl' : t - n < (closures ρ gid Gr).length := by simp [closures]; omega
      have eF : Tm.env (ρ ++ closures ρ gid Gr) t = (closures ρ gid Gr)[t - n] := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right (show ρ.length ≤ t by omega), hlF,
          List.getElem?_eq_getElem hcl']
      rw [e ρM hlM, e ρS hlS]
      obtain ⟨F', hF', hd1, hfoot, hsp, -⟩ := ih _ hk' _ _ _ (List.getElem?_eq_getElem (hcl ρM))
        (List.getElem?_eq_getElem (hcl ρS)) (List.getElem?_eq_getElem hcl')
      have hu' : F'.u = false := by have := hsib (by omega); rw [hF'] at this; simpa using this
      refine ⟨F, hFk, hd1, fun b hf => ?_, fun b hs => ?_, fun hu => ?_⟩
      · obtain ⟨i, u, hl, hu1, hf'⟩ := hfoot b hf
        exact ⟨i, u, hl, fun h => absurd (hu1 h) (by simp [hu']), hf'⟩
      · obtain ⟨-, hs⟩ := hdele b _ _ hs; rw [eF] at hs; exact absurd (hsp b hs).1 (by simp [hu'])
      · exact .dele hGr hFk hd hu (by
          rw [Tm.toList_ofList, eF]; exact .free fun b hs => by have := (hsp b hs).1; simp_all)

def plainTele : Nat → Tm
  | 0 => .nil
  | m + 1 => .bind (.ty false false false) .nil (plainTele m)

theorem plainTele_ers : ∀ (m k : Nat), k < m → (plainTele m).ers.getD k true = false
  | m + 1, 0, _ => by simp [plainTele, Tm.ers, Ent.er]
  | m + 1, k + 1, h => by simpa [plainTele, Tm.ers] using plainTele_ers m k (by omega)

theorem two_le_filter {α : Type} (p : α → Bool) : ∀ (l : List α) (k j : Nat) (a c : α), k < j → l[k]? = some a →
    l[j]? = some c → p a = true → p c = true → 2 ≤ (l.filter p).length
  | x :: l, 0, j + 1, a, c, _, hk, hj, ha, hc => by
    simp at hk; subst hk
    have hm : c ∈ l.filter p := List.mem_filter.mpr ⟨List.mem_of_getElem? hj, hc⟩
    have : 1 ≤ (l.filter p).length := List.length_pos_of_mem hm
    simp [ha]; omega
  | x :: l, k + 1, j + 1, a, c, h, hk, hj, ha, hc => by
    have := two_le_filter p l k j a c (by omega) hk hj ha hc
    simp only [List.filter_cons]; split <;> simp <;> omega

theorem machine_defFns {b : Nat} {G : UCtx} {ru : List Bool} {rets : Tm} {gid : Nat} {rest : Core} {ρ vs : List Tm}
    {Gr : Group} (hGr : P.groups[gid]? = some Gr)
    (hdl : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.dele = some t → t < G.Γ.n + k ∧
      (t < G.Γ.n → ∃ u, Gr.caps.lookup t = some u ∧ (u = true → F.u = true) ∧
        (u = false → F.u = true → NoSpine P (Tm.env ρ t))) ∧
      (G.Γ.n ≤ t → (Gr.fns[t - G.Γ.n]?.map (·.u)) = some false))
    (hsim : ∀ ρS, SimEnv P G.Γ.er ρS ρ → SimEnv P (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)).er
      (ρS ++ closuresS ρS gid Gr) (ρ ++ closures ρ gid Gr))
    (ih : MRun P b (G.next (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)) (Gr.fns.map (·.u))) ru rets rest
      (ρ ++ closures ρ gid Gr) vs) :
    MRun P b G ru rets (.defFns gid rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hGr, Option.bind_eq_bind, Option.bind_some, hf, hg] at hU
  simp only [Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  split at hU
  case isFalse => cases hU
  obtain ⟨⟨O, K'⟩, -, hU⟩ := Option.bind_eq_some_iff.mp hU
  split at hU
  case isFalse => cases hU
  rename_i _ hc
  simp only [UCtx.defOK, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨-, hall⟩, hone⟩, -⟩ := hc
  have hseq := UR.seq_fst hU
  simp only at hseq
  have hcap : ∀ i u, Gr.caps.lookup i = some u → i < G.Γ.n ∧ G.Γ.er i = false := fun i u h => by
    have := hall _ (lookup_mem h)
    simp only [UCtx.use] at this
    split at this
    · cases this
    · rename_i hc; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hc
      exact ⟨by omega, by simpa using hc.1.2⟩
  have hM' := hM.split hseq
  have hcv := clo_vals hGr hM.lenM hM.lenS hM.lenF
    (fun i u h => hM'.dec i (hcap i u h).1 (by simp [h]) (hcap i u h).2)
    (fun i h => hM'.wo i (hcap i true h).1 h (hcap i true h).2)
    (fun i i' hne h h' => by
      obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp h'
      exact hM'.sep i (hcap i true h).1 i' (hcap i' u' hu').1 hne h h' (hcap i true h).2 (hcap i' u' hu').2) hdl
  have hlF : (closures ρ gid Gr).length = Gr.fns.length := by simp [closures]
  have hgF : ∀ k w, (closuresS ρM gid Gr)[k]? = some w → (closures ρ gid Gr)[k]? = some (Tm.clo (.ofList ρ) gid k) :=
    fun k w hw => by
      have hk := (List.getElem?_eq_some_iff.mp hw).1; rw [closuresS_length] at hk; simp [closures, hk]
  have hru : ∀ k F, Gr.fns[k]? = some F → (Gr.fns.map (·.u)).getD k false = F.u := fun k F h => by
    simp [List.getD_eq_getElem?_getD, h]
  have hO : MOut P Gr.caps G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (plainTele Gr.fns.length) (Gr.fns.map (·.u)) H
      (closuresS ρM gid Gr) (closuresS ρS gid Gr) (closures ρ gid Gr) := by
    refine ⟨hM.wf, Nat.le_refl _, fun _ h => h, fun _ _ _ _ => rfl, by simp [closuresS_length],
      fun k w u hw hu _ => ?_, fun k w u hw hu _ b hf => ?_, fun k w u v hw hu hv _ hr b hs => ?_,
      fun k w u v hw hu hv _ hr => ?_, fun k j w u v w' u' hkj hw hu hv hw' hu' _ _ hr b h1 h2 => ?_⟩
    · obtain ⟨F, -, hd, -⟩ := hcv k w u _ hw hu (hgF k w hw); exact hd
    · obtain ⟨F, -, -, hft, -⟩ := hcv k w u _ hw hu (hgF k w hw)
      obtain ⟨i, u', hl, -, hf'⟩ := hft b hf
      exact .inr (.inr (.inr (.inl ⟨i, (hcap i u' hl).1, by simp [hl], (hcap i u' hl).2, hf'⟩)))
    · obtain ⟨F, -, -, -, hsp, -⟩ := hcv k w u v hw hu hv
      obtain ⟨-, i, hl, hsi⟩ := hsp b hs
      exact .inr (.inl ⟨i, (hcap i true hl).1, hl, (hcap i true hl).2, hsi⟩)
    · obtain ⟨F, hFk, -, -, -, hwo⟩ := hcv k w u v hw hu hv
      exact hwo (by rw [← hru k F hFk]; exact hr)
    · obtain ⟨F, hFk, -, -, hsp, -⟩ := hcv k w u v hw hu hv
      obtain ⟨Fj, hFj, -, hft, -, -⟩ := hcv j w' u' _ hw' hu' (hgF j w' hw')
      obtain ⟨hFu, i, hl, hsi⟩ := hsp b h1
      obtain ⟨i', u'', hl', hu'', hf⟩ := hft b h2
      by_cases e : i = i'
      · subst e; rw [hl] at hl'; cases hl'
        have hFju := hu'' rfl
        have hany : Gr.caps.any (·.2) = true := List.any_eq_true.mpr ⟨_, lookup_mem hl, rfl⟩
        have h1 := hone; simp only [hany, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
        rcases Nat.lt_or_gt_of_ne hkj with hlt | hlt
        · have := two_le_filter (·.u) Gr.fns k j F Fj hlt hFk hFj hFu hFju; omega
        · have := two_le_filter (·.u) Gr.fns j k Fj F hlt hFj hFk hFju hFu; omega
      · exact hM'.sep i (hcap i true hl).1 i' (hcap i' u'' hl').1 e hl (by simp [hl']) (hcap i true hl).2
          (hcap i' u'' hl').2 b hsi hf
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushFns Gr) (.defFns gid rest) := ⟨_, rfl⟩
  rw [← hΓ'] at hC ih hsim
  have hn' : Γ'.n = G.Γ.n + Gr.fns.length := by rw [hΓ', UCtx.adv_n' hf]; simp [Ctx.pushFns, Ctx.n]
  have huq := usesCore_uq b (G.next Γ' (Gr.fns.map (·.u))) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bind hseq hO (m := Gr.fns.length) (by simp [closuresS_length]) hlF (er' := Γ'.er)
    (fun i hi => by rw [hΓ', UCtx.adv_er' hf]; simp; omega)
    (fun k hk _ _ => plainTele_ers _ k hk)
    (fun k hk hc _ => by
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
  cases hrun with
  | defFns hG' hr =>
  rw [hGr] at hG'; cases hG'
  obtain ⟨H', vsM, hrr, hOr⟩ := ih CU CK hC _ vsS (hsim ρS hS) hr H _ Res Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr)
    (hG.next (by omega) hM.lenM (by rw [hΓ', UCtx.adv_ghost' hf]; simpa [Ctx.pushFns] using hg))
  exact ⟨H', vsM, .defFns hGr hrr, lift (by simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr)⟩

theorem machine_call {b : Nat} {G : UCtx} {ru : List Bool} {rets f args : Tm} {dec : Dec} {ms : List Bool}
    {ve : Option (List Bool)} {rest : Core} {ρ vs outsF : List Tm} {t outs : Tm} {uf : Bool}
    (hce : G.callee P f args = some (t, outs, uf)) (hR : outs.isTele) (hol : outsF.length = outs.len)
    (hcall : ∀ A B AB, G.termUses P uf f = some A → G.argsUses P (·.u) args t = some B → Uses.seq A B = some AB →
      ∀ ρS envS gid j Gr F outsSb, SimEnv P G.Γ.er ρS ρ → P.sub ρS f = .clo envS gid j → P.groups[gid]? = some Gr →
      Gr.fns[j]? = some F →
      RunS P (envS.toList ++ closuresS envS.toList gid Gr ++ F.spreadIn ve (args.toList.map (P.sub ρS))) F.body outsSb →
      ∀ H ρM Out' Shr, MFrame P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' Shr →
      ∃ envM H1 as H2 outsMb, P.subU (Tm.env ρM) f = .clo envM gid j ∧
        P.buildList H (Tm.env ρM) (maskArgs (ve.getD []) args).toList = (H1, as) ∧
        RunM P H1 (envM.toList ++ closuresS envM.toList gid Gr ++ F.spreadIn ve as) none F.body H2 outsMb ∧
        MOut P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (plainTele outs.len) (teleUs outs) H2
          (F.spreadOut ve args.toList.length outsMb) (F.spreadOut ve args.toList.length outsSb) outsF)
    (hsim : ∀ ρS envS gid j Gr F outsSb, SimEnv P G.Γ.er ρS ρ → P.sub ρS f = .clo envS gid j →
      P.groups[gid]? = some Gr → Gr.fns[j]? = some F →
      RunS P (envS.toList ++ closuresS envS.toList gid Gr ++ F.spreadIn ve (args.toList.map (P.sub ρS))) F.body outsSb →
      SimEnv P (G.adv P (G.Γ.pushTele outs (some (ms.map (false || ·)))) (.call f dec args false ms ve rest)).er
        (ρS ++ F.spreadOut ve args.toList.length outsSb) (ρ ++ outsF))
    (ih : MRun P b (G.next (G.adv P (G.Γ.pushTele outs (some (ms.map (false || ·)))) (.call f dec args false ms ve rest))
      (teleUs outs)) ru rets rest (ρ ++ outsF) vs) :
    MRun P b G ru rets (.call f dec args false ms ve rest) ρ vs := by
  intro U K hU ρS vsS hS hrun H ρM Res Out Shr pd hM hG
  have hf := hG.fill
  have hg := hG.ghost
  rw [usesCore] at hU
  simp only [hce, Option.bind_eq_bind, Option.bind_some, Bool.or_false, hg, Bool.false_eq_true, ite_false] at hU
  obtain ⟨⟨CU, CK⟩, hC, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨A, hA, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨B, hB, hU⟩ := Option.bind_eq_some_iff.mp hU
  obtain ⟨AB, hAB, hU⟩ := Option.bind_eq_some_iff.mp hU
  have hseq := UR.seq_fst hU
  simp only at hseq
  cases hrun with
  | call hf' hG' hF' hb hr =>
  rename_i envS gid j Gr F outsSb
  obtain ⟨envM, H1, as, H2, outsMb, hfM, hbl, hrb, hO⟩ :=
    hcall A B AB hA hB hAB ρS _ _ _ _ _ _ hS hf' hG' hF' hb H ρM _ Shr (hM.split hseq)
  have hS' := hsim ρS _ _ _ _ _ _ hS hf' hG' hF' hb
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er G.Γ outs (some (ms.map (false || ·))) hR
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = G.adv P (G.Γ.pushTele outs (some (ms.map (false || ·)))) (.call f dec args false ms ve rest) :=
    ⟨_, rfl⟩
  rw [← hΓ'] at ih hC hS'
  have her' : Γ'.er = (G.Γ.pushTele outs (some (ms.map (false || ·)))).er := by rw [hΓ']; exact UCtx.adv_er' hf
  have hn' : Γ'.n = G.Γ.n + outs.len := by rw [hΓ', UCtx.adv_n' hf, Ctx.pushTele_n _ hR]
  have hlS : (F.spreadOut ve args.toList.length outsSb).length = outs.len := by
    have := hS'.1; simp only [List.length_append, hM.lenF, hol, hM.lenS] at this; omega
  have huq := usesCore_uq b (G.next Γ' (teleUs outs)) ru rets rest hf CU CK hC
  obtain ⟨hMr, lift⟩ := hM.bind hseq hO hlS hol (er' := Γ'.er)
    (fun i hi => by rw [her']; exact hpo i hi)
    (fun k hk _ _ => plainTele_ers _ k hk)
    (fun k hk hc _ => by
      rcases huq _ (lookup_mem hc) with h1 | h1
      · exact UCtx.next_uq_new h1 hG.uqlt
      · simp only [UCtx.next] at h1; omega)
  obtain ⟨H', vsM, hrr, hOr⟩ := ih CU CK hC _ vsS hS' hr H2 _ Res Out Shr none
    (by simp only [UCtx.next]; rw [hn']; exact hMr)
    (hG.next (by omega) hM.lenM (by rw [hΓ', UCtx.adv_ghost' hf, hpg]; exact hg))
  exact ⟨H', vsM, .call hfM hG' hF' hbl hrb hrr, lift (by simp only [UCtx.next] at hOr; rw [hn'] at hOr; exact hOr)⟩

theorem rtArgs_mask (Γ : Ctx) : ∀ (args s : Tm), rtArgs P Γ (maskArgs s.ers args) s = rtArgs P Γ args s := by
  intro args; induction args with
  | cons a as _ ih =>
    intro s; cases s with
    | bind k A r => cases hk : k.er <;> simp [maskArgs, Tm.ers, rtArgs, hk, ih]
    | _ => simp [maskArgs, Tm.ers]
  | _ => intro s; cases s <;> simp [maskArgs, Tm.ers]

theorem retUses_mask (G : UCtx) : ∀ (ru : List Bool) (args s : Tm),
    G.retUses P ru (maskArgs s.ers args) s = G.retUses P ru args s := by
  intro ru args; induction args generalizing ru with
  | cons a as _ ih =>
    intro s; cases s with
    | bind k A r => cases ru <;> cases hk : k.er <;> simp [maskArgs, Tm.ers, UCtx.retUses, hk, ih]
    | _ => simp [maskArgs, Tm.ers]
  | _ => intro s; cases s <;> simp [maskArgs, Tm.ers]

theorem mask_length : ∀ (es : List Bool) (args : Tm), (maskArgs es args).toList.length = args.toList.length
  | e :: es, .cons a as => by simp [maskArgs, Tm.toList, mask_length es as]
  | [], _ => by simp [maskArgs]
  | _ :: _, .nil | _ :: _, .fv _ | _ :: _, .bv _ | _ :: _, .univ | _ :: _, .level | _ :: _, .tyc .. | _ :: _, .vc ..
  | _ :: _, .app .. | _ :: _, .bind .. | _ :: _, .tyCtor _ | _ :: _, .valCtor _ | _ :: _, .predates ..
  | _ :: _, .subterm .. | _ :: _, .fn .. | _ :: _, .mtbl .. | _ :: _, .lvl _ | _ :: _, .tok | _ :: _, .clo ..
  | _ :: _, .nat _ | _ :: _, .ptr _ | _ :: _, .wld _ | _ :: _, .sfv _ | _ :: _, .sbv _ => by simp [maskArgs]

theorem MOut.congrE {U : Uses} {n : Nat} {er : Nat → Bool} {H H' : Heap} {ρM ρS ρ : List Tm} {Res Shr : Nat → Prop}
    {rets : Tm} {ru : List Bool} {vsM vsS vs vsS' vs' : List Tm}
    (hO : MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS vs) (hl : vsS'.length = vsS.length)
    (hS : ∀ k, rets.ers.getD k true = false → vsS'[k]? = vsS[k]?)
    (hF : ∀ k, rets.ers.getD k true = false → vs'[k]? = vs[k]?) :
    MOut P U n er H ρM ρS ρ Res Shr rets ru H' vsM vsS' vs' :=
  ⟨hO.wf, hO.next, hO.blk, hO.keep, by rw [hl]; exact hO.len,
    fun k w u hw hu he => hO.dec k w u hw (by rw [← hS k he]; exact hu) he,
    fun k w u hw hu he => hO.foot k w u hw (by rw [← hS k he]; exact hu) he,
    fun k w u v hw hu hv he => hO.uspine k w u v hw (by rw [← hS k he]; exact hu) (by rw [← hF k he]; exact hv) he,
    fun k w u v hw hu hv he => hO.uwo k w u v hw (by rw [← hS k he]; exact hu) (by rw [← hF k he]; exact hv) he,
    fun k j w u v w' u' hkj hw hu hv hw' hu' he he' =>
      hO.usep k j w u v w' u' hkj hw (by rw [← hS k he]; exact hu) (by rw [← hF k he]; exact hv) hw'
        (by rw [← hS j he']; exact hu') he he'⟩

theorem args_val (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {args t : Tm} {B : Uses}
    (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrta : rtArgs P G.Γ args t = true)
    (hB : G.argsUses P (·.u) args t = some B) {H : Heap} {Res Out Shr : Nat → Prop}
    (hM : MFrame P B G.Γ.n G.Γ.er H ρM ρS ρ Res Out Shr) :
    ∃ H1 as, P.buildList H (Tm.env ρM) (maskArgs t.ers args).toList = (H1, as) ∧
      MOut P B G.Γ.n G.Γ.er H ρM ρS ρ Res Shr t (t.kinds.map (·.u)) H1 as (args.toList.map (P.sub ρS))
        (args.toList.map (·.subst (Tm.env ρ))) := by
  obtain ⟨H1, vsM, hr, hO⟩ := machine_ret hP (ts := maskArgs t.ers args) (by rw [rtArgs_mask]; exact hrta) hE hS rfl
    (ru := t.kinds.map fun k => true && k.u) (U := B)
    (by rw [retUses_mask, ← argsUses_ret]; simpa using hB) hM none
  cases hr with
  | ret hb =>
    refine ⟨_, _, hb, MOut.congrE (by simpa using hO) (by simp [mask_length]) (fun k he => ?_) (fun k he => ?_)⟩
    · simp only [List.getElem?_map, mask_get' _ _ k he]
    · simp only [List.getElem?_map, mask_get' _ _ k he]

theorem MDec.clo_inv {H : Heap} {eM eS : List Tm} {gid j : Nat} (h : MDec P H (.clo (.ofList eM) gid j) (.clo (.ofList eS) gid j)) :
    eM.length = eS.length ∧ ∀ i, P.rd gid j i = true → MDec P H (Tm.env eM i) (Tm.env eS i) := by
  generalize hw : Tm.clo (.ofList eM) gid j = w at h
  generalize hu : Tm.clo (.ofList eS) gid j = u at h
  cases h with
  | clo hl hd =>
    simp only [Tm.clo.injEq] at hw hu
    obtain ⟨e1, rfl, rfl⟩ := hw; obtain ⟨e2, -, -⟩ := hu
    have := congrArg Tm.toList e1; have := congrArg Tm.toList e2
    simp only [Tm.toList_ofList] at *; subst_vars; exact ⟨hl, hd⟩
  | tok h => cases hu
  | _ => cases hu

theorem WO.clo_inv {H : Heap} {eM eS eF : Tm} {gid j : Nat} {Gr : Group} {F : FnDef} (hGr : P.groups[gid]? = some Gr)
    (hF : Gr.fns[j]? = some F) (hdn : F.dele = none) (h : WO P H (.clo eM gid j) (.clo eS gid j) (.clo eF gid j)) :
    (∀ i, P.rdU gid j i = true → WO P H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i)) ∧
    (∀ i, P.rdU gid j i = true → ∀ i', i' ≠ i → P.rd gid j i' = true →
      Disj (Spine P H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i))
        (Foot P H (Tm.env eM.toList i') (Tm.env eS.toList i'))) := by
  generalize hw : Tm.clo eM gid j = w at h
  generalize hu : Tm.clo eS gid j = u at h
  generalize hv : Tm.clo eF gid j = v at h
  cases h with
  | clo _ h1 h2 =>
    simp only [Tm.clo.injEq] at hw hu hv
    obtain ⟨rfl, -, -⟩ := hw; obtain ⟨rfl, -, -⟩ := hu; obtain ⟨rfl, rfl, rfl⟩ := hv; exact ⟨h1, h2⟩
  | dele hG' hF' hd' =>
    simp only [Tm.clo.injEq] at hv; obtain ⟨-, rfl, rfl⟩ := hv
    rw [hGr] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [hdn] at hd'; cases hd'
  | free hn =>
    subst hw hu hv
    exact ⟨fun i hi => .free fun b hs => hn b (.clo hi hs), fun i hi i' _ _ b hs _ => hn b (.clo hi hs)⟩
  | _ => first | (cases hv; done) | (cases hw; done) | (cases hu; done)

theorem clo_vals_many {gid n : Nat} {Gr : Group} (hGr : P.groups[gid]? = some Gr) {H : Heap} {ρM ρS ρ : List Tm}
    (hlM : ρM.length = n) (hlS : ρS.length = n) (hlF : ρ.length = n)
    (hdec : ∀ i, Gr.caps.lookup i = some false → MDec P H (Tm.env ρM i) (Tm.env ρS i))
    (hdl : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.u = false → F.dele = some t → t < n + k ∧
      (t < n → Gr.caps.lookup t = some false) ∧ (n ≤ t → (Gr.fns[t - n]?.map (·.u)) = some false)) :
    ∀ (k : Nat) (wM wS wF : Tm), (closuresS ρM gid Gr)[k]? = some wM → (closuresS ρS gid Gr)[k]? = some wS →
      (closures ρ gid Gr)[k]? = some wF → ∀ F : FnDef, Gr.fns[k]? = some F → F.u = false → MDec P H wM wS ∧
      (∀ b, Foot P H wM wS b → ∃ i, Gr.caps.lookup i = some false ∧ Foot P H (Tm.env ρM i) (Tm.env ρS i) b) ∧
      ∀ b, ¬ Spine P H wM wS wF b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro wM wS wF hM hS hF F hFk hu
  obtain ⟨F', hF', rfl⟩ := closuresS_get hM
  obtain ⟨F'', hF'', rfl⟩ := closuresS_get hS
  rw [hFk] at hF' hF''; cases hF'; cases hF''
  obtain ⟨hk, rfl⟩ := closures_get hF
  have htk : ∀ env : List Tm, ((closuresS env gid Gr).take k).length = k := fun env => by
    simp [closuresS_length]; omega
  have hrd : ∀ i, P.rd gid k i = true → Gr.caps.lookup i = some false := fun i h => by
    simp only [Prog.rd, Prog.fnU, hGr, Option.map_some, Option.getD_some, Option.bind_some, hFk, hu,
      Bool.false_and, Bool.or_false] at h
    cases hl : Gr.caps.lookup i with
    | none => simp [hl] at h
    | some u => cases u <;> simp_all
  have nosp : ∀ b w u, ¬ Spine P H w u (.clo (.ofList ρ) gid k) b := fun b w u hs => by
    rcases hs.clo_inv with ⟨_, _, i, _, _, hi, _⟩ | ⟨G', F', t', hG', hF', _, hu', _⟩
    · simp [Prog.rdU, Prog.fnU, hGr, hFk, hu] at hi
    · rw [hGr] at hG'; cases hG'; rw [hFk] at hF'; cases hF'; rw [hu] at hu'; cases hu'
  unfold cval
  cases hd : F.dele with
  | none =>
    simp only [htk]
    refine ⟨.clo (by simp [hlM, hlS]) fun i hi => hdec i (hrd i hi), fun b hf => ?_, fun b => nosp b _ _⟩
    cases hf with
    | clo hi hf => exact ⟨_, hrd _ hi, by simpa [Tm.toList_ofList] using hf⟩
  | some t =>
    simp only
    obtain ⟨htn, hout, hsib⟩ := hdl k F t hFk hu hd
    by_cases htn' : t < n
    · have e : ∀ (env : List Tm), env.length = n → (env ++ (closuresS env gid Gr).take k).getD t .nil = Tm.env env t :=
        fun env hl => by simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left (show t < env.length by omega)]
      rw [e ρM hlM, e ρS hlS]
      exact ⟨hdec t (hout htn'), fun b hf => ⟨t, hout htn', hf⟩, fun b => nosp b _ _⟩
    · have hk' : t - n < k := by omega
      have hcl : ∀ env : List Tm, t - n < (closuresS env gid Gr).length := fun env => by rw [closuresS_length]; omega
      have e : ∀ (env : List Tm), env.length = n →
          (env ++ (closuresS env gid Gr).take k).getD t .nil = (closuresS env gid Gr)[t - n]'(hcl env) :=
        fun env hl => by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show env.length ≤ t by omega), hl,
            hk', List.getElem?_eq_getElem (hcl env)]
      have hcl' : t - n < (closures ρ gid Gr).length := by simp [closures]; omega
      rw [e ρM hlM, e ρS hlS]
      obtain ⟨F', hF', hu'⟩ : ∃ F', Gr.fns[t - n]? = some F' ∧ F'.u = false := by
        have := hsib (by omega)
        cases h : Gr.fns[t - n]? with
        | none => simp [h] at this
        | some F' => exact ⟨F', rfl, by simpa [h] using this⟩
      obtain ⟨hd1, hft, -⟩ := ih _ hk' _ _ _ (List.getElem?_eq_getElem (hcl ρM)) (List.getElem?_eq_getElem (hcl ρS))
        (List.getElem?_eq_getElem hcl') F' hF' hu'
      exact ⟨hd1, hft, fun b => nosp b _ _⟩

theorem body_frame {n m : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {AB B : Uses}
    {Out' Shr : Nat → Prop} (hM : MFrame P AB n er H ρM ρS ρ (fun _ => False) Out' Shr) (sB : B.Sub AB)
    {fi : Nat} (hfi : fi < n) (hfe : er fi = false) (hfU : (AB.lookup fi).isSome)
    (hfB : B.lookup fi ≠ some true) (hfB' : AB.lookup fi = some true → B.lookup fi = none)
    {cM cS cF : List Tm} (hcM : cM.length = m) (hcS : cS.length = m) (hcF : cF.length = m)
    {t : Tm} {as argsS argsF : List Tm}
    (hOa : MOut P B n er H ρM ρS ρ (fun _ => False) Shr t (t.kinds.map (·.u)) H1 as argsS argsF)
    {pM pS : List Tm} {Ub : Uses} {erb : Nat → Bool}
    (hlp : pM.length = argsF.length) (hlpS : pS.length = argsF.length)
    (hpar : ∀ k, k < argsF.length → erb (m + k) = false →
      t.ers.getD k true = false ∧ pM[k]? = as[k]? ∧ pS[k]? = argsS[k]? ∧ (as[k]?).isSome ∧ (argsS[k]?).isSome)
    (hcd : ∀ z < m, (Ub.lookup z).isSome → erb z = false → MDec P H (Tm.env cM z) (Tm.env cS z) ∧
      ∀ b, Foot P H (Tm.env cM z) (Tm.env cS z) b → Foot P H (Tm.env ρM fi) (Tm.env ρS fi) b)
    (hcu : ∀ z < m, Ub.lookup z = some true → erb z = false → AB.lookup fi = some true ∧
      WO P H (Tm.env cM z) (Tm.env cS z) (Tm.env cF z) ∧
      ∀ b, Spine P H (Tm.env cM z) (Tm.env cS z) (Tm.env cF z) b → Spine P H (Tm.env ρM fi) (Tm.env ρS fi) (Tm.env ρ fi) b)
    (hcs : ∀ z < m, ∀ z' < m, z ≠ z' → Ub.lookup z = some true → (Ub.lookup z').isSome → erb z = false → erb z' = false →
      Disj (Spine P H (Tm.env cM z) (Tm.env cS z) (Tm.env cF z)) (Foot P H (Tm.env cM z') (Tm.env cS z')))
    (hpU : ∀ k < argsF.length, Ub.lookup (m + k) = some true → erb (m + k) = false →
      (t.kinds.map (·.u)).getD k false = true) :
    MFrame P Ub (m + argsF.length) erb H1 (cM ++ pM) (cS ++ pS) (cF ++ argsF) (fun _ => False) Out' Shr ∧
    (∀ b, Own P Ub (m + argsF.length) erb H1 (cM ++ pM) (cS ++ pS) (cF ++ argsF) b →
      H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b) ∧
    (∀ b, Live P Ub (m + argsF.length) erb H1 (cM ++ pM) (cS ++ pS) b →
      H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b ∨ Live P AB n er H ρM ρS b ∨ Shr b) := by
  have hnOwn : ∀ b, Foot P H (Tm.env ρM fi) (Tm.env ρS fi) b → ¬ Own P B n er H ρM ρS ρ b :=
    fun b hb ⟨y, hy, hBy, hey, hsy⟩ => by
      have hne : y ≠ fi := fun e => hfB (e ▸ hBy)
      exact hM.sep y hy fi hfi hne (sB.2 y hBy) hfU hey hfe b hsy hb
  have hag : Agree H H1 (Foot P H (Tm.env ρM fi) (Tm.env ρS fi)) := fun b hb =>
    hOa.keep b (Foot.lt hM.wf (hM.dec fi hfi hfU hfe) hb) (hnOwn b hb) id
  have hagC : ∀ z < m, (Ub.lookup z).isSome → erb z = false → Agree H H1 (Foot P H (Tm.env cM z) (Tm.env cS z)) :=
    fun z hz hU he b hb => hag b ((hcd z hz hU he).2 b hb)
  have eC : ∀ (a c : List Tm), a.length = m → ∀ i, i < m → Tm.env (a ++ c) i = Tm.env a i :=
    fun a c hl i hi => env_app_left (by omega)
  have eP : ∀ (a c : List Tm), a.length = m → ∀ k, Tm.env (a ++ c) (m + k) = c.getD k .nil :=
    fun a c hl k => by rw [← hl, env_app_right]
  have gD : ∀ (l : List Tm) k, k < l.length → l[k]? = some (l.getD k .nil) := fun l k hk => get_getD hk
  have cls : ∀ i, i < m + argsF.length → i < m ∨ (∃ k, k < argsF.length ∧ i = m + k) := fun i hi => by
    by_cases h1 : i < m
    · exact .inl h1
    · exact .inr ⟨i - m, by omega, by omega⟩
  have hfd := hM.dec fi hfi hfU hfe
  have toF : ∀ z, z < m → (Ub.lookup z).isSome → erb z = false → ∀ b,
      Foot P H1 (Tm.env (cM ++ pM) z) (Tm.env (cS ++ pS) z) b → Foot P H (Tm.env ρM fi) (Tm.env ρS fi) b :=
    fun z hz hU he b h2 => by
      rw [eC _ _ hcM z hz, eC _ _ hcS z hz] at h2
      exact (hcd z hz hU he).2 b (Foot.bwd (hagC z hz hU he) h2)
  have parV : ∀ k, k < argsF.length → erb (m + k) = false →
      t.ers.getD k true = false ∧ as[k]? = some (Tm.env (cM ++ pM) (m + k)) ∧
      argsS[k]? = some (Tm.env (cS ++ pS) (m + k)) ∧ argsF[k]? = some (Tm.env (cF ++ argsF) (m + k)) := by
    intro k hk he
    obtain ⟨hte, hpm, hps, has, hass⟩ := hpar k hk he
    rw [eP _ _ hcM, eP _ _ hcS, eP _ _ hcF]
    refine ⟨hte, ?_, ?_, gD _ k hk⟩
    · rw [← hpm]; exact gD _ k (by omega)
    · rw [← hps]; exact gD _ k (by omega)
  have envW : ∀ x, x < m → Ub.lookup x = some true → erb x = false →
      AB.lookup fi = some true ∧ ∀ b, Spine P H1 (Tm.env (cM ++ pM) x) (Tm.env (cS ++ pS) x) (Tm.env (cF ++ argsF) x) b →
        Spine P H (Tm.env ρM fi) (Tm.env ρS fi) (Tm.env ρ fi) b := fun x hx hU he => by
    obtain ⟨hABf, -, hsp⟩ := hcu x hx hU he
    refine ⟨hABf, fun b h1 => ?_⟩
    rw [eC _ _ hcM x hx, eC _ _ hcS x hx, eC _ _ hcF x hx] at h1
    exact hsp b (Spine.bwd (hagC x hx (by simp [hU]) he).spine h1)
  have parS : ∀ k, k < argsF.length → Ub.lookup (m + k) = some true → erb (m + k) = false → ∀ b,
      Spine P H1 (Tm.env (cM ++ pM) (m + k)) (Tm.env (cS ++ pS) (m + k)) (Tm.env (cF ++ argsF) (m + k)) b →
      H.next ≤ b ∨ Own P B n er H ρM ρS ρ b := fun k hk hU he b h1 => by
    obtain ⟨hte, h1', h2', h3'⟩ := parV k hk he
    rcases hOa.uspine k _ _ _ h1' h2' h3' hte (hpU k hk hU he) b h1 with h | h | h
    · exact .inl h
    · exact .inr h
    · exact h.elim
  refine ⟨⟨by simp [hcM, hlp], by simp [hcS, hlpS], by simp [hcF], hOa.wf, ?_, ?_, ?_, ?_,
    ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩,
    fun a ha => Nat.lt_of_lt_of_le (hM.outb a ha) hOa.next,
    ⟨fun _ h => h.elim, ?_, fun a ha => Nat.lt_of_lt_of_le (hM.shr.2.2 a ha) hOa.next⟩⟩, ?_, ?_⟩
  · intro i hi hU he
    rcases cls i hi with hi' | ⟨k, hk, rfl⟩
    · rw [eC _ _ hcM i hi', eC _ _ hcS i hi']
      exact (hcd i hi' hU he).1.frame (hagC i hi' hU he)
    · obtain ⟨hte, h1, h2, -⟩ := parV k hk he
      exact hOa.dec k _ _ h1 h2 hte
  · intro x hx hU he
    rcases cls x hx with hx' | ⟨k, hk, rfl⟩
    · rw [eC _ _ hcM x hx', eC _ _ hcS x hx', eC _ _ hcF x hx']
      exact (hcu x hx' hU he).2.1.fwd (hagC x hx' (by simp [hU]) he)
    · obtain ⟨hte, h1, h2, h3⟩ := parV k hk he
      exact hOa.uwo k _ _ _ h1 h2 h3 hte (hpU k hk hU he)
  · intro x hx z hz hne hUx hUz hex hez b h1 h2
    rcases cls x hx with hx' | ⟨k, hk, rfl⟩
    · obtain ⟨hABf, hsf⟩ := envW x hx' hUx hex
      have hsf' := hsf b h1
      rcases cls z hz with hz' | ⟨k', hk', rfl⟩
      · rw [eC _ _ hcM x hx', eC _ _ hcS x hx', eC _ _ hcF x hx'] at h1
        rw [eC _ _ hcM z hz', eC _ _ hcS z hz'] at h2
        exact hcs x hx' z hz' hne hUx hUz hex hez b (Spine.bwd (hagC x hx' (by simp [hUx]) hex).spine h1)
          (Foot.bwd (hagC z hz' hUz hez) h2)
      · obtain ⟨hte, h1', h2', -⟩ := parV k' hk' hez
        rcases hOa.foot k' _ _ h1' h2' hte b h2 with h | ⟨y, hy, hBy, hey, hsy⟩ | h | ⟨z', hz'', hBz', hez', hfz'⟩ | h
        · have := Foot.lt hM.wf hfd hsf'.foot; omega
        · have hne' : fi ≠ y := fun e => hfB (e ▸ hBy)
          exact hM.sep fi hfi y hy hne' hABf (sB.1 y (by simp [hBy])) hfe hey b hsf' hsy.foot
        · exact h
        · have hne' : fi ≠ z' := fun e => by subst e; rw [hfB' hABf] at hBz'; cases hBz'
          exact hM.sep fi hfi z' hz'' hne' hABf (sB.1 z' hBz') hfe hez' b hsf' hfz'
        · exact hM.shr.2.1 fi hfi hABf hfe b hsf' h
    · have hsp := parS k hk hUx hex b h1
      rcases cls z hz with hz' | ⟨k', hk', rfl⟩
      · have hfz := toF z hz' hUz hez b h2
        rcases hsp with h | ⟨y, hy, hBy, hey, hsy⟩
        · have := Foot.lt hM.wf hfd hfz; omega
        · have hne' : y ≠ fi := fun e => hfB (e ▸ hBy)
          exact hM.sep y hy fi hfi hne' (sB.2 y hBy) hfU hey hfe b hsy hfz
      · obtain ⟨hte, h1', h2', h3'⟩ := parV k hk hex
        obtain ⟨hte', h1'', h2'', -⟩ := parV k' hk' hez
        exact hOa.usep k k' _ _ _ _ _ (fun e => hne (by rw [e])) h1' h2' h3' h1'' h2'' hte hte'
          (hpU k hk hUx hex) b h1 h2
  · intro x hx hU he b h1 h2
    rcases cls x hx with hx' | ⟨k, hk, rfl⟩
    · obtain ⟨hABf, hsf⟩ := envW x hx' hU he
      exact hM.out fi hfi hABf hfe b (hsf b h1) h2
    · rcases parS k hk hU he b h1 with h | ⟨y, hy, hBy, hey, hsy⟩
      · have := hM.outb b h2; omega
      · exact hM.out y hy (sB.2 y hBy) hey b hsy h2
  · intro x hx hU he b h1 h2
    rcases cls x hx with hx' | ⟨k, hk, rfl⟩
    · obtain ⟨hABf, hsf⟩ := envW x hx' hU he
      exact hM.shr.2.1 fi hfi hABf hfe b (hsf b h1) h2
    · rcases parS k hk hU he b h1 with h | ⟨y, hy, hBy, hey, hsy⟩
      · have := hM.shr.2.2 b h2; omega
      · exact hM.shr.2.1 y hy (sB.2 y hBy) hey b hsy h2
  · intro b ⟨x, hx, hU, he, hs⟩
    rcases cls x hx with hx' | ⟨k, hk, rfl⟩
    · obtain ⟨hABf, hsf⟩ := envW x hx' hU he
      exact .inr ⟨fi, hfi, hABf, hfe, hsf b hs⟩
    · rcases parS k hk hU he b hs with h | ⟨y, hy, hBy, hey, hsy⟩
      · exact .inl h
      · exact .inr ⟨y, hy, sB.2 y hBy, hey, hsy⟩
  · intro b ⟨z, hz, hU, he, hf⟩
    rcases cls z hz with hz' | ⟨k, hk, rfl⟩
    · exact .inr (.inr (.inl ⟨fi, hfi, hfU, hfe, toF z hz' hU he b hf⟩))
    · obtain ⟨hte, h1', h2', -⟩ := parV k hk he
      rcases hOa.foot k _ _ h1' h2' hte b hf with h | ⟨y, hy, hBy, hey, hsy⟩ | h | ⟨z', hz'', hBz', hez', hfz'⟩ | h
      · exact .inl h
      · exact .inr (.inl ⟨y, hy, sB.2 y hBy, hey, hsy⟩)
      · exact h.elim
      · exact .inr (.inr (.inl ⟨z', hz'', sB.1 z' hBz', hez', hfz'⟩))
      · exact .inr (.inr (.inr h))

theorem callee_frame {n : Nat} {er : Nat → Bool} {H H1 : Heap} {ρM ρS ρ : List Tm} {AB B : Uses}
    {Out' Shr : Nat → Prop} (hM : MFrame P AB n er H ρM ρS ρ (fun _ => False) Out' Shr) (sB : B.Sub AB)
    {fi : Nat} (hfi : fi < n) (hfe : er fi = false) (hfU : (AB.lookup fi).isSome)
    (hfB : B.lookup fi ≠ some true) (hfB' : AB.lookup fi = some true → B.lookup fi = none)
    {envM envS envF : List Tm} {gid j : Nat} {Gr : Group} {F : FnDef}
    (hfM : Tm.env ρM fi = .clo (.ofList envM) gid j) (hfS : Tm.env ρS fi = .clo (.ofList envS) gid j)
    (hfF : Tm.env ρ fi = .clo (.ofList envF) gid j) (hlF : envF.length = envS.length)
    (hGr : P.groups[gid]? = some Gr) (hF : Gr.fns[j]? = some F) (hdn : F.dele = none)
    (hdl : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.u = false → F.dele = some t →
      t < envS.length + k ∧ (t < envS.length → Gr.caps.lookup t = some false) ∧
      (envS.length ≤ t → (Gr.fns[t - envS.length]?.map (·.u)) = some false))
    {t : Tm} {as argsS argsF : List Tm}
    (hOa : MOut P B n er H ρM ρS ρ (fun _ => False) Shr t (t.kinds.map (·.u)) H1 as argsS argsF)
    {pM pS : List Tm} {Ub : Uses} {erb : Nat → Bool}
    (hlp : pM.length = argsF.length) (hlpS : pS.length = argsF.length)
    (hpar : ∀ k, k < argsF.length → erb (envS.length + Gr.fns.length + k) = false →
      t.ers.getD k true = false ∧ pM[k]? = as[k]? ∧ pS[k]? = argsS[k]? ∧ (as[k]?).isSome ∧ (argsS[k]?).isSome)
    (hrd : ∀ i < envS.length, (Ub.lookup i).isSome → erb i = false → P.rd gid j i = true)
    (hrdU : ∀ i < envS.length, Ub.lookup i = some true → erb i = false → P.rdU gid j i = true ∧ AB.lookup fi = some true)
    (hsib : ∀ k < Gr.fns.length, (Ub.lookup (envS.length + k)).isSome → erb (envS.length + k) = false →
      (Gr.fns[k]?.map (·.u)) = some false ∧ Ub.lookup (envS.length + k) ≠ some true)
    (hpU : ∀ k < argsF.length, Ub.lookup (envS.length + Gr.fns.length + k) = some true →
      erb (envS.length + Gr.fns.length + k) = false → (t.kinds.map (·.u)).getD k false = true) :
    MFrame P Ub (envS.length + Gr.fns.length + argsF.length) erb H1
      (envM ++ closuresS envM gid Gr ++ pM) (envS ++ closuresS envS gid Gr ++ pS) (envF ++ closures envF gid Gr ++ argsF)
      (fun _ => False) Out' Shr ∧
    (∀ b, Own P Ub (envS.length + Gr.fns.length + argsF.length) erb H1 (envM ++ closuresS envM gid Gr ++ pM)
      (envS ++ closuresS envS gid Gr ++ pS) (envF ++ closures envF gid Gr ++ argsF) b →
      H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b) ∧
    (∀ b, Live P Ub (envS.length + Gr.fns.length + argsF.length) erb H1 (envM ++ closuresS envM gid Gr ++ pM)
      (envS ++ closuresS envS gid Gr ++ pS) b →
      H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b ∨ Live P AB n er H ρM ρS b ∨ Shr b) := by
  have hfdec := hM.dec fi hfi hfU hfe
  rw [hfM, hfS] at hfdec
  obtain ⟨hlen, hrdM⟩ := MDec.clo_inv hfdec
  have hfoot : ∀ i, P.rd gid j i = true → ∀ b, Foot P H (Tm.env envM i) (Tm.env envS i) b →
      Foot P H (Tm.env ρM fi) (Tm.env ρS fi) b := fun i hi b hb => by
    rw [hfM, hfS]; exact .clo hi (by simpa [Tm.toList_ofList] using hb)
  have hspine : ∀ i, P.rdU gid j i = true → ∀ b, Spine P H (Tm.env envM i) (Tm.env envS i) (Tm.env envF i) b →
      Spine P H (Tm.env ρM fi) (Tm.env ρS fi) (Tm.env ρ fi) b := fun i hi b hb => by
    rw [hfM, hfS, hfF]; exact .clo hi (by simpa [Tm.toList_ofList] using hb)
  have hrdF : ∀ i, Gr.caps.lookup i = some false → P.rd gid j i = true := fun i h => by
    simp [Prog.rd, hGr, h]
  have hcv := clo_vals_many hGr hlen rfl (by rw [hlF]) (fun i h => hrdM i (hrdF i h)) hdl
  have eE : ∀ (a b : List Tm), a.length = envS.length → ∀ i, i < envS.length → Tm.env (a ++ b) i = Tm.env a i :=
    fun a b hl i hi => env_app_left (by omega)
  have eSib : ∀ (a b : List Tm), a.length = envS.length → ∀ k, Tm.env (a ++ b) (envS.length + k) = b.getD k .nil :=
    fun a b hl k => by rw [← hl, env_app_right]
  have gD : ∀ (l : List Tm) k, k < l.length → l[k]? = some (l.getD k .nil) := fun l k hk => get_getD hk
  have sibF : ∀ k, k < Gr.fns.length → (Gr.fns[k]?.map (·.u)) = some false →
      MDec P H ((closuresS envM gid Gr).getD k .nil) ((closuresS envS gid Gr).getD k .nil) ∧
      (∀ b, Foot P H ((closuresS envM gid Gr).getD k .nil) ((closuresS envS gid Gr).getD k .nil) b →
        ∃ i, Gr.caps.lookup i = some false ∧ Foot P H (Tm.env envM i) (Tm.env envS i) b) := fun k hk hu => by
    obtain ⟨F', hF', hu'⟩ : ∃ F', Gr.fns[k]? = some F' ∧ F'.u = false := by
      cases h : Gr.fns[k]? with
      | none => simp [h] at hu
      | some F' => exact ⟨F', rfl, by simpa [h] using hu⟩
    obtain ⟨h1, h2, -⟩ := hcv k _ _ _ (gD _ k (by simp [closuresS_length]; omega))
      (gD _ k (by simp [closuresS_length]; omega)) (gD _ k (by simp [closures]; omega)) F' hF' hu'
    exact ⟨h1, h2⟩
  have hspU : ∀ i, P.rdU gid j i = true → Gr.caps.lookup i = some true := fun i h => by
    simp only [Prog.rdU, hGr, Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h; exact h.2
  have cls : ∀ z, z < envS.length + Gr.fns.length → z < envS.length ∨ ∃ k, k < Gr.fns.length ∧ z = envS.length + k :=
    fun z hz => by
      by_cases h : z < envS.length
      · exact .inl h
      · exact .inr ⟨z - envS.length, by omega, by omega⟩
  refine body_frame hM sB hfi hfe hfU hfB hfB' (by simp [hlen, closuresS_length]) (by simp [closuresS_length])
    (by simp [hlF, closures]) hOa hlp hlpS hpar (fun z hz hU he => ?_) (fun z hz hU he => ?_)
    (fun z hz z' hz' hne hU hU' he he' => ?_) hpU
  · rcases cls z hz with hz' | ⟨k, hk, rfl⟩
    · rw [eE _ _ hlen z hz', eE _ _ rfl z hz']
      exact ⟨hrdM z (hrd z hz' hU he), hfoot z (hrd z hz' hU he)⟩
    · rw [eSib _ _ hlen, eSib _ _ rfl]
      have hu := (hsib k hk hU he).1
      exact ⟨(sibF k hk hu).1, fun b hb => by
        obtain ⟨i, hl, hf⟩ := (sibF k hk hu).2 b hb; exact hfoot i (hrdF i hl) b hf⟩
  · rcases cls z hz with hz' | ⟨k, hk, rfl⟩
    · obtain ⟨hrU, hABf⟩ := hrdU z hz' hU he
      have hwoF := hM.wo fi hfi hABf hfe
      rw [hfM, hfS, hfF] at hwoF
      have hwx := (WO.clo_inv hGr hF hdn hwoF).1 z hrU
      simp only [Tm.toList_ofList] at hwx
      rw [eE _ _ hlen z hz', eE _ _ rfl z hz', eE _ _ hlF z hz']
      exact ⟨hABf, hwx, hspine z hrU⟩
    · exact absurd hU (hsib k hk (by simp [hU]) he).2
  · rcases cls z hz with hzx | ⟨k, hk, rfl⟩
    · obtain ⟨hrU, hABf⟩ := hrdU z hzx hU he
      have hwoF := hM.wo fi hfi hABf hfe
      rw [hfM, hfS, hfF] at hwoF
      rw [eE _ _ hlen z hzx, eE _ _ rfl z hzx, eE _ _ hlF z hzx]
      rcases cls z' hz' with hzy | ⟨k', hk', rfl⟩
      · rw [eE _ _ hlen z' hzy, eE _ _ rfl z' hzy]
        have hd := (WO.clo_inv hGr hF hdn hwoF).2 z hrU z' (Ne.symm hne) (hrd z' hzy hU' he')
        simpa only [Tm.toList_ofList] using hd
      · rw [eSib _ _ hlen, eSib _ _ rfl]
        intro b h1 h2
        have hu := (hsib k' hk' hU' he').1
        obtain ⟨i', hl', hf'⟩ := (sibF k' hk' hu).2 b h2
        have hne' : i' ≠ z := fun e => by subst e; rw [hspU _ hrU] at hl'; cases hl'
        have hd := (WO.clo_inv hGr hF hdn hwoF).2 z hrU i' hne' (hrdF i' hl')
        simp only [Tm.toList_ofList] at hd
        exact hd b h1 hf'
    · exact absurd hU (hsib k hk (by simp [hU]) he).2

theorem callee_out {n nb m : Nat} {er erb : Nat → Bool} {H H1 H2 : Heap} {ρM ρS ρ ρMb ρSb ρFb : List Tm}
    {AB B Ub : Uses} {Shr : Nat → Prop} {t Rb : Tm} {ru rub ruC : List Bool} {as argsS argsF outsMb outsSb outsFb oM oS : List Tm}
    (hOa : MOut P B n er H ρM ρS ρ (fun _ => False) Shr t ru H1 as argsS argsF) (sB : B.Sub AB)
    (hOb : MOut P Ub nb erb H1 ρMb ρSb ρFb (fun _ => False) Shr Rb rub H2 outsMb outsSb outsFb)
    (hown : ∀ b, Own P Ub nb erb H1 ρMb ρSb ρFb b → H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b)
    (hlive : ∀ b, Live P Ub nb erb H1 ρMb ρSb b →
      H.next ≤ b ∨ Own P AB n er H ρM ρS ρ b ∨ Live P AB n er H ρM ρS b ∨ Shr b)
    (hlen : oM.length = oS.length)
    (hsp : ∀ k w u, oM[k]? = some w → oS[k]? = some u →
      (w = .tok ∧ u = .tok) ∨ (Rb.ers.getD k true = false ∧ outsMb[k]? = some w ∧ outsSb[k]? = some u))
    (hru : ∀ k, ruC.getD k false = true → Rb.ers.getD k true = false → rub.getD k false = true) :
    MOut P AB n er H ρM ρS ρ (fun _ => False) Shr (plainTele m) ruC H2 oM oS outsFb := by
  have tokS : ∀ v b, ¬ Spine P H2 .tok .tok v b := fun v b h => h.imm (by simp) (by simp)
  have tokF : ∀ b, ¬ Foot P H2 .tok .tok b := fun b h => by cases h
  refine ⟨hOb.wf, Nat.le_trans hOa.next hOb.next, fun a ha => hOb.blk a (hOa.blk a ha),
    fun a ha ho _ => ?_, hlen, fun k w u hw hu _ => ?_, fun k w u hw hu _ b hf => ?_,
    fun k w u v hw hu hv _ hr b hs => ?_, fun k w u v hw hu hv _ hr => ?_,
    fun k j w u v w' u' hkj hw hu hv hw' hu' _ _ hr b h1 h2 => ?_⟩
  · rw [hOb.keep a (Nat.lt_of_lt_of_le ha hOa.next) (fun h => by
        rcases hown a h with h | h
        · omega
        · exact ho h) id,
      hOa.keep a ha (fun h => ho (h.mono sB)) id]
  · rcases hsp k w u hw hu with ⟨rfl, rfl⟩ | ⟨he, h1, h2⟩
    · exact .tok (.inl rfl)
    · exact hOb.dec k w u h1 h2 he
  · rcases hsp k w u hw hu with ⟨rfl, rfl⟩ | ⟨he, h1, h2⟩
    · exact (tokF b hf).elim
    · rcases hOb.foot k w u h1 h2 he b hf with h | h | h | h | h
      · exact .inl (Nat.le_trans hOa.next h)
      · rcases hown b h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact h.elim
      · rcases hlive b h with h | h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))
      · exact .inr (.inr (.inr (.inr h)))
  · rcases hsp k w u hw hu with ⟨rfl, rfl⟩ | ⟨he, h1, h2⟩
    · exact (tokS v b hs).elim
    · rcases hOb.uspine k w u v h1 h2 hv he (hru k hr he) b hs with h | h | h
      · exact .inl (Nat.le_trans hOa.next h)
      · rcases hown b h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact h.elim
  · rcases hsp k w u hw hu with ⟨rfl, rfl⟩ | ⟨he, h1, h2⟩
    · exact .free fun b h => tokS v b h
    · exact hOb.uwo k w u v h1 h2 hv he (hru k hr he)
  · rcases hsp k w u hw hu with ⟨rfl, rfl⟩ | ⟨he, e1, e2⟩
    · exact tokS v b h1
    · rcases hsp j w' u' hw' hu' with ⟨rfl, rfl⟩ | ⟨he', e1', e2'⟩
      · exact tokF b h2
      · exact hOb.usep k j w u v w' u' hkj e1 e2 hv e1' e2' he he' (hru k hr he) b h1 h2

theorem MDec.clo_inv' {H : Heap} {w e : Tm} {gid j : Nat} (h : MDec P H w (.clo e gid j)) :
    ∃ lM lS, w = .clo (.ofList lM) gid j ∧ e = .ofList lS ∧ lM.length = lS.length ∧
      ∀ i, P.rd gid j i = true → MDec P H (Tm.env lM i) (Tm.env lS i) := by
  generalize hu : Tm.clo e gid j = u at h
  cases h with
  | clo hl hd =>
    simp only [Tm.clo.injEq] at hu; obtain ⟨rfl, rfl, rfl⟩ := hu
    exact ⟨_, _, rfl, rfl, hl, hd⟩
  | _ => cases hu

theorem call_body (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {fi : Nat} {args t : Tm} {uf : Bool}
    {A B AB : Uses} (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrta : rtArgs P G.Γ args t = true)
    (hA : G.termUses P uf (.fv fi) = some A) (hB : G.argsUses P (·.u) args t = some B) (hAB : Uses.seq A B = some AB)
    {envS : Tm} {gid j : Nat} {Gr : Group} {F : FnDef} (hfS : P.sub ρS (.fv fi) = .clo envS gid j)
    (hGr : P.groups[gid]? = some Gr) (hF : Gr.fns[j]? = some F) (hdn : F.dele = none)
    (hdl : ∀ (k : Nat) (F : FnDef) (t : Nat), Gr.fns[k]? = some F → F.u = false → F.dele = some t →
      t < envS.toList.length + k ∧ (t < envS.toList.length → Gr.caps.lookup t = some false) ∧
      (envS.toList.length ≤ t → (Gr.fns[t - envS.toList.length]?.map (·.u)) = some false))
    {envF : List Tm} (hfF : Tm.env ρ fi = .clo (.ofList envF) gid j) (hlF : envF.length = envS.toList.length)
    {ve : Option (List Bool)} (hve : ve = some t.ers) {Gb : UCtx} {rub : List Bool} {Rb : Tm} {Ub : Uses} {Kb : Caps}
    (hUb : usesCore P gid Gb rub Rb F.body = some (Ub, Kb))
    (hGn : Gb.Γ.n = envS.toList.length + Gr.fns.length + args.toList.length)
    (hGok : ∀ H ρM ρS ρ Shr, GOK P Gb none H ρM ρS ρ (fun _ => False) Shr)
    (hrd : ∀ i < envS.toList.length, (Ub.lookup i).isSome → Gb.Γ.er i = false → P.rd gid j i = true)
    (hrdU : ∀ i < envS.toList.length, Ub.lookup i = some true → Gb.Γ.er i = false → P.rdU gid j i = true ∧ uf = true)
    (hsib : ∀ k < Gr.fns.length, (Ub.lookup (envS.toList.length + k)).isSome → Gb.Γ.er (envS.toList.length + k) = false →
      (Gr.fns[k]?.map (·.u)) = some false ∧ Ub.lookup (envS.toList.length + k) ≠ some true)
    (hpU : ∀ k < args.toList.length, Ub.lookup (envS.toList.length + Gr.fns.length + k) = some true →
      Gb.Γ.er (envS.toList.length + Gr.fns.length + k) = false → (t.kinds.map (·.u)).getD k false = true)
    (hsprI : ∀ xs : List Tm, xs.length = args.toList.length → (F.spreadIn ve xs).length = args.toList.length ∧
      ∀ k, k < args.toList.length → Gb.Γ.er (envS.toList.length + Gr.fns.length + k) = false →
        t.ers.getD k true = false ∧ (F.spreadIn ve xs)[k]? = xs[k]?)
    {ruC : List Bool} {m : Nat}
    (hsprO : ∀ xs ys : List Tm, xs.length = ys.length → ys.length = Rb.ers.length →
      (F.spreadOut ve args.toList.length xs).length = (F.spreadOut ve args.toList.length ys).length ∧
      ∀ k w u, (F.spreadOut ve args.toList.length xs)[k]? = some w → (F.spreadOut ve args.toList.length ys)[k]? = some u →
        (w = .tok ∧ u = .tok) ∨ (Rb.ers.getD k true = false ∧ xs[k]? = some w ∧ ys[k]? = some u))
    (hru : ∀ k, ruC.getD k false = true → Rb.ers.getD k true = false → rub.getD k false = true)
    {outsFb outsSb : List Tm}
    (hbody : MRun P gid Gb rub Rb F.body (envF ++ closures envF gid Gr ++ args.toList.map (·.subst (Tm.env ρ))) outsFb)
    (hsimb : SimEnv P Gb.Γ.er (envS.toList ++ closuresS envS.toList gid Gr ++ F.spreadIn ve (args.toList.map (P.sub ρS)))
      (envF ++ closures envF gid Gr ++ args.toList.map (·.subst (Tm.env ρ))))
    (hrunS : RunS P (envS.toList ++ closuresS envS.toList gid Gr ++ F.spreadIn ve (args.toList.map (P.sub ρS))) F.body outsSb)
    (hlS : outsSb.length = Rb.ers.length)
    {H : Heap} {Out' Shr : Nat → Prop} (hM : MFrame P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' Shr) :
    ∃ envM H1 as H2 outsMb, P.subU (Tm.env ρM) (.fv fi) = .clo envM gid j ∧
      P.buildList H (Tm.env ρM) (maskArgs (ve.getD []) args).toList = (H1, as) ∧
      RunM P H1 (envM.toList ++ closuresS envM.toList gid Gr ++ F.spreadIn ve as) none F.body H2 outsMb ∧
      MOut P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (plainTele m) ruC H2
        (F.spreadOut ve args.toList.length outsMb) (F.spreadOut ve args.toList.length outsSb) outsFb := by
  simp only [UCtx.termUses, UCtx.use] at hA
  split at hA
  · cases hA
  rename_i hc
  simp only [Option.some.injEq] at hA; subst hA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hc
  have hfi : fi < G.Γ.n := by omega
  have hfe : G.Γ.er fi = false := by simpa using hc.1.2
  obtain ⟨sA, sB⟩ := Uses.seq_sub hAB
  have hfree := (Uses.seq_spec hAB).1
  have hAfi : [(fi, uf)].lookup fi = some uf := by simp [List.lookup]
  have hfU : (AB.lookup fi).isSome := sA.1 fi (by simp [hAfi])
  have hfB : B.lookup fi ≠ some true := fun h => by have := (hfree fi).2 h; rw [hAfi] at this; cases this
  have hfB' : AB.lookup fi = some true → B.lookup fi = none := fun h => by
    cases uf
    · cases hb : B.lookup fi with
      | none => rfl
      | some v =>
        cases v
        · rw [(Uses.seq_spec hAB).2 fi, hAfi, hb] at h; simp [Uses.merge] at h
        · exact absurd hb hfB
    · exact (hfree fi).1 hAfi
  have hfd := hM.dec fi hfi hfU hfe
  simp only [Prog.sub, Prog.subU] at hfS
  rw [hfS] at hfd
  obtain ⟨lM, lS, hfM, rfl, -, -⟩ := MDec.clo_inv' hfd
  simp only [Tm.toList_ofList] at *
  obtain ⟨H1, as, hbl, hOa⟩ := args_val hP hE hS hrta hB (hM.subB (sB.subB _))
  have hlas : as.length = args.toList.length := by
    have := (buildList_ext (P := P) hM.wf (Tm.env ρM) (maskArgs t.ers args).toList).2.2
    rw [hbl, mask_length] at this; exact this
  obtain ⟨hlI, hkI⟩ := hsprI as hlas
  obtain ⟨hlIS, hkIS⟩ := hsprI (args.toList.map (P.sub ρS)) (by simp)
  obtain ⟨hMb, hown, hlive⟩ := callee_frame hM sB hfi hfe hfU hfB hfB' hfM hfS hfF hlF hGr hF hdn hdl hOa
    (pM := F.spreadIn ve as) (pS := F.spreadIn ve (args.toList.map (P.sub ρS))) (Ub := Ub) (erb := Gb.Γ.er)
    (by simp [hlI]) (by simp [hlIS])
    (fun k hk he => by
      have hk' : k < args.toList.length := by simpa using hk
      have h1 := hkI k hk' he
      have h2 := hkIS k hk' he
      refine ⟨h1.1, h1.2, h2.2, ?_, ?_⟩
      · rw [get_getD (by omega)]; rfl
      · rw [get_getD (by simpa using hk')]; rfl)
    hrd (fun i hi hU he => by
      obtain ⟨h1, rfl⟩ := hrdU i hi hU he
      exact ⟨h1, by rw [(Uses.seq_spec hAB).2 fi, hAfi]; cases B.lookup fi <;> simp [Uses.merge]⟩)
    hsib (fun k hk hU he => hpU k (by simpa using hk) hU he)
  have hn : lS.length + Gr.fns.length + (args.toList.map (·.subst (Tm.env ρ))).length = Gb.Γ.n := by
    simp [hGn]
  rw [hn] at hMb hown hlive
  obtain ⟨H2, outsMb, hrb, hOb⟩ := hbody Ub Kb hUb _ outsSb hsimb hrunS H1 _ _ Out' Shr none hMb (hGok _ _ _ _ _)
  obtain ⟨hlo, hspo⟩ := hsprO outsMb outsSb hOb.len hlS
  exact ⟨.ofList lM, H1, as, H2, outsMb, by simp only [Prog.subU]; exact hfM, by rw [hve]; exact hbl,
    by simpa [Tm.toList_ofList] using hrb,
    callee_out hOa sB hOb hown hlive hlo hspo hru⟩

end Minimal
