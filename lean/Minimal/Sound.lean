import Minimal.Check
import Minimal.UnifySound
import Minimal.Strip
import Minimal.Eval
import Minimal.Deleg
import Minimal.Machine

set_option linter.deprecated false

namespace Minimal

structure Ctx.WF (Γ : Ctx) : Prop where
  tys : ∀ (i : Nat) (T : Tm), Γ.tys[i]? = some T → T.static Γ.n 0
  σ : ∀ e t, Γ.σ e = some t → e < Γ.n ∧ t.static Γ.n 0
  ς : ∀ e s, Γ.ς e = some s → e < Γ.n ∧ (s = Tm.vacant ∨ ∃ j < Γ.n, s = .sfv j)
  mints : ∀ L ∈ Γ.mints, L < Γ.n
  cur : ∀ c, Γ.cur = some c → c < Γ.n
  subs : ∀ s ∈ Γ.subs, s < Γ.n

variable (P : Prog)

def FixOK (F : List (Option Tm)) (ρ : List Tm) : Prop :=
  F.length ≤ ρ.length ∧ ∀ i v, F[i]?.join = some v → Real P v (Tm.env ρ i)

def CoerOwn (sa a sb b : Tm) : Prop :=
  (sa = uniqueTm → sb = uniqueTm → Twin P a b) ∧ (sa = uniqueTm → sb ≠ uniqueTm → NoSpine P a) ∧
    (sb = uniqueTm → sa ≠ uniqueTm → NoSpine P b)

def DeleOK (ds : List (Nat × Nat × Bool × Bool)) (ρ : List Tm) : Prop :=
  ∀ g t sg st, (g, t, sg, st) ∈ ds → g < ρ.length ∧ t < ρ.length ∧
    (∀ vS, Real P vS (Tm.env ρ g) ↔ Real P vS (Tm.env ρ t)) ∧ CoerOwn P (sideTm sg) (Tm.env ρ g) (sideTm st) (Tm.env ρ t)

mutual
inductive VTy : Tm → Tm → Prop
  | univ : VTy v .univ
  | top : VTy v .nil
  | lvl : VTy (.lvl n) .level
  | predates : (∀ n ∈ x.levels, n < m) → VTy .tok (.predates A x (.lvl m))
  | subterm : Tm.PSub a b → VTy .tok (.subterm A a B b)
  | tyCtor {D : Adt} : P.adts[d]? = some D → ls.len = D.lifted → VTys ls D.params out → VTy (.tyc d ls) (.tyCtor out)
  | vc : P.ctor d c = some sig → ls.len = P.lifted d → VTys ls sig out → VTy (.vc d c ls) (.valCtor out)
  | con : P.ctor d c = some sig → ls.len = P.lifted d → VTys ls sig mid → VTys vs mid (.bind (.ty mk me mu) T .nil) →
      T = .app (.tyc d ls) idx → VTy (.app (.vc d c ls) vs) T
  | clo : EnvOK env Γ → P.groups[gid]? = some G → GroupOK P gid Γ G → G.fns[j]? = some F →
      VTy (.clo (.ofList env) gid j) ((F.type G).subst (Tm.env env))
  | mtbl {D : Adt} : P.adts[d]? = some D → ls.len = D.lifted → VTys ls D.params out → D.coercible = false →
      D.opq = false → VTy v (D.mtbl d ls)
  | opq {D : Adt} : P.adts[d]? = some D → D.opq = true → P.placedD ≠ some d → P.worldD ≠ some d →
      VTy .tok (.app (.tyc d ls) idx)
  | world {D : Adt} : P.worldD = some w → P.adts[w]? = some D → D.opq = true → P.placedD ≠ some w →
      VTy (.wld k) (.app (.tyc w .nil) .nil)
  | placed : P.placedD = some q → VTy v T → VTy v (.app (.tyc q .nil) (.cons s (.cons T (.cons v .nil))))
  | coer {D : Adt} : P.adts[d]? = some D → D.coercible = true → (∀ vS, Real P vS a ↔ Real P vS b) →
      CoerOwn P sa a sb b → VTy .tok (Tm.coer d sa A a sb B b)

inductive VTys : Tm → Tm → Tm → Prop
  | nil : VTys .nil t t
  | cons : VTy v A → VTys vs (r.inst v 0) out → VTys (.cons v vs) (.bind (.ty m e u) A r) out
  | isCons : v = e → VTys vs (r.inst v 0) out → VTys (.cons v vs) (.bind (.is ..) e r) out

inductive EnvOK : List Tm → Ctx → Prop
  | mk : ρ.length = Γ.n →
      (∀ (i : Nat) (v T : Tm), ρ[i]? = some v → Γ.tys[i]? = some T → VTy v (T.subst (Tm.env ρ))) →
      (∀ v ∈ ρ, v.lc 0) → Sat (Tm.env ρ) Γ.σ →
      (∀ L ∈ Γ.mints, ∃ m, ρ[L]? = some (.lvl m) ∧ ∀ i < L, ∀ (v : Tm), ρ[i]? = some v → ∀ n ∈ v.levels, n < m) →
      Γ.WF → FixOK P Γ.fixed ρ → DeleOK P Γ.deles ρ → EnvOK ρ Γ
end

variable {P}

theorem sideTm_subst (b : Bool) (f : Nat → Tm) : (sideTm b).subst f = sideTm b := by cases b <;> rfl

theorem sideTm_static {n : Nat} (b : Bool) : (sideTm b).static n 0 = true := by cases b <;> rfl

theorem NoSpine.twin {a b : Tm} (h : NoSpine P b) (t : Twin P a b) : NoSpine P a :=
  fun H w u k hs => h H w u k (((t H w u).1 k).mp hs)

theorem NoSpine.nil : NoSpine P .nil := fun _ _ _ _ h => by cases h

theorem CoerOwn.refl (s a : Tm) : CoerOwn P s a s a := ⟨fun _ _ => .refl a, fun h h' => (h' h).elim, fun h h' => (h' h).elim⟩

theorem CoerOwn.symm {sa a sb b : Tm} (h : CoerOwn P sa a sb b) : CoerOwn P sb b sa a :=
  ⟨fun h1 h2 => (h.1 h2 h1).symm, h.2.2, h.2.1⟩

theorem CoerOwn.shared (a b : Tm) : CoerOwn P sharedTm a sharedTm b :=
  have hn : sharedTm ≠ uniqueTm := by simp [sharedTm, uniqueTm]
  ⟨fun h => (hn h).elim, fun h => (hn h).elim, fun h => (hn h).elim⟩

theorem CoerOwn.trans {sa a sb b sc c : Tm} (h1 : CoerOwn P sa a sb b) (h2 : CoerOwn P sb b sc c) : CoerOwn P sa a sc c := by
  refine ⟨fun ha hc => ?_, fun ha hc => ?_, fun hc ha => ?_⟩ <;> by_cases hb : sb = uniqueTm
  · exact (h1.1 ha hb).trans (h2.1 hb hc)
  · exact .none (h1.2.1 ha hb) (h2.2.2 hc hb)
  · exact (h2.2.1 hb hc).twin (h1.1 ha hb)
  · exact h1.2.1 ha hb
  · exact (h1.2.2 hb ha).twin (h2.1 hb hc).symm
  · exact h2.2.2 hc hb

theorem CoerOwn.wrap {d c k : Nat} {sig ls vs : Tm} (hw : P.wrapField d c = some k) (hs : P.ctor d c = some sig)
    (s : Tm) : CoerOwn P (if (sig.skip (P.lifted d)).uAt k then s else sharedTm) (vs.toList.getD k .nil) s
      (.app (.vc d c ls) vs) := by
  cases hu : (sig.skip (P.lifted d)).uAt k
  · have hn : sharedTm ≠ uniqueTm := by simp [sharedTm, uniqueTm]
    exact ⟨fun h => (hn h).elim, fun h => (hn h).elim, fun _ _ => NoSpine.wrap hw hs (.inl hu)⟩
  · refine ⟨fun _ _ => ?_, fun h h' => (h' h).elim, fun h h' => (h' h).elim⟩
    cases hv : vs.toList[k]? with
    | none => simp only [List.getD_eq_getElem?_getD, hv, Option.getD_none]; exact .none .nil (NoSpine.wrap hw hs (.inr hv))
    | some v => simp only [List.getD_eq_getElem?_getD, hv, Option.getD_some]; exact Twin.wrap hw hs hu hv

theorem Prog.wrapField_spec {d c k : Nat} (h : P.wrapField d c = some k) :
    P.isNt d = true ∧ P.phantom d c = false ∧ ∃ sig, P.ctor d c = some sig ∧ (sig.skip (P.lifted d)).ntField = some k := by
  unfold Prog.wrapField at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    obtain ⟨sig, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨hc.1, hc.2, sig, h1, h2⟩
  · cases h

theorem Tm.ntField_spec {sig : Tm} {k : Nat} (h : sig.ntField = some k) :
    k < sig.len - 1 ∧ sig.ers.getD k true = false ∧ ∀ j < sig.len - 1, sig.ers.getD j true = false → j = k := by
  unfold Tm.ntField at h
  split at h
  · rename_i k' hf
    cases h
    have hk : k ∈ (List.range (sig.len - 1)).filter (fun j => !sig.ers.getD j true) := by rw [hf]; simp
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
    refine ⟨hk.1, hk.2, fun j hj he => ?_⟩
    have : j ∈ (List.range (sig.len - 1)).filter (fun j => !sig.ers.getD j true) := by
      simp only [List.mem_filter, List.mem_range, hj, he]; simp
    rw [hf] at this; simpa using this
  · cases h

theorem Prog.wrapField_none {d c : Nat} (h : P.isNt d = false) : P.wrapField d c = none := by
  simp [Prog.wrapField, h]

namespace Tm

theorem env_lc {ρ : List Tm} (h : ∀ v ∈ ρ, v.lc 0) (i : Nat) : (env ρ i).lc 0 := by
  simp only [env, List.getD_eq_getElem?_getD]
  cases e : ρ[i]? with
  | none => simp [lc]
  | some v => exact h v (List.mem_of_getElem? e)

theorem env_append {ρ more : List Tm} {i : Nat} (h : i < ρ.length) : env (ρ ++ more) i = env ρ i := by
  simp [env, List.getElem?_append_left h]

theorem subst_append {ρ more : List Tm} {t : Tm} {d : Nat} (h : t.static ρ.length d) :
    t.subst (env (ρ ++ more)) = t.subst (env ρ) :=
  subst_ext t fun i hi => env_append (fvs_static t d h i hi)

end Tm

theorem canon_sound {Γ : Ctx} {f : Nat → Tm} (h : Sat f Γ.σ) (hs : SatS f Γ.ς) (t : Tm) :
    (Γ.canon t).subst f = t.subst f :=
  canonBy_sound h hs t

theorem Ctx.WF.ς_mono {Γ : Ctx} (hw : Γ.WF) {n : Nat} (hn : Γ.n ≤ n) :
    ∀ e s, Γ.ς e = some s → e < n ∧ (s = Tm.vacant ∨ ∃ j < n, s = .sfv j) := by
  intro e s h
  obtain ⟨he, hs⟩ := hw.ς e s h
  refine ⟨by omega, ?_⟩
  rcases hs with hs | ⟨j, hj, hs⟩
  · exact .inl hs
  · exact .inr ⟨j, by omega, hs⟩

theorem slotVal_subst {f : Nat → Tm} (hc : ∀ i, (f i).lc 0) {s : Tm} {n : Nat}
    (hs : s = Tm.vacant ∨ ∃ j < n, s = .sfv j) (e : Nat) : s.subst f = Tm.slotOf (f e) := by
  rw [Tm.slotOf_lc0 (hc e)]
  rcases hs with rfl | ⟨j, -, rfl⟩
  · rfl
  · simp only [Tm.subst]; exact Tm.slotOf_lc0 (hc j)

theorem satS_of_closed {Γ : Ctx} (hw : Γ.WF) {f : Nat → Tm} (hc : ∀ i, (f i).lc 0) : SatS f Γ.ς :=
  fun e s h => slotVal_subst hc (hw.ς e s h).2 e

theorem EnvOK.sat {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → Sat (Tm.env ρ) Γ.σ | .mk _ _ _ h _ _ _ _ => h
theorem EnvOK.satS {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → SatS (Tm.env ρ) Γ.ς
  | .mk _ _ hc _ _ hw _ _ => satS_of_closed hw (Tm.env_lc hc)
theorem EnvOK.wf {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → Γ.WF | .mk _ _ _ _ _ h _ _ => h
theorem EnvOK.len {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ρ.length = Γ.n | .mk h _ _ _ _ _ _ _ => h
theorem EnvOK.closed {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ∀ v ∈ ρ, v.lc 0 | .mk _ _ h _ _ _ _ _ => h
theorem EnvOK.fix {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → FixOK P Γ.fixed ρ | .mk _ _ _ _ _ _ h _ => h
theorem EnvOK.dele {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → DeleOK P Γ.deles ρ | .mk _ _ _ _ _ _ _ h => h

theorem DeleOK.append {ds : List (Nat × Nat × Bool × Bool)} {ρ more : List Tm} (h : DeleOK P ds ρ) : DeleOK P ds (ρ ++ more) :=
  fun g t sg st hm => by
    obtain ⟨h1, h2, h3, h4⟩ := h g t sg st hm
    rw [Tm.env_append h1, Tm.env_append h2]; exact ⟨by simp; omega, by simp; omega, h3, h4⟩

theorem EnvOK.vals {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ →
    ∀ (i : Nat) (v T : Tm), ρ[i]? = some v → Γ.tys[i]? = some T → VTy P v (T.subst (Tm.env ρ)) | .mk _ h _ _ _ _ _ _ => h

theorem FixOK.append {F : List (Option Tm)} {ρ more : List Tm} (h : FixOK P F ρ) : FixOK P F (ρ ++ more) := by
  refine ⟨by simp; have := h.1; omega, fun i v hv => ?_⟩
  have hi : i < F.length := by
    rcases Nat.lt_or_ge i F.length with hi | hi
    · exact hi
    · simp [List.getElem?_eq_none hi] at hv
  rw [Tm.env_append (by have := h.1; omega)]; exact h.2 i v hv

theorem EnvOK.canon {ρ : List Tm} {Γ : Ctx} (h : EnvOK P ρ Γ) (t : Tm) :
    (Γ.canon t).subst (Tm.env ρ) = t.subst (Tm.env ρ) := canon_sound h.sat h.satS t

theorem canon_static {Γ : Ctx} (hw : Γ.WF) {t : Tm} {d : Nat} (h : t.static Γ.n d) : (Γ.canon t).static Γ.n d :=
  Tm.static_subst2 t d h fun i hi => ⟨by
    cases e : Γ.σ i with
    | none => simp [Tm.static]; exact Tm.fvs_static t d h i hi
    | some u => simpa using (hw.σ i u e).2, by
    cases e : Γ.ς i with
    | none => simp [Tm.static]; exact Tm.fvs_static t d h i hi
    | some u => rcases (hw.ς i u e).2 with rfl | ⟨j, hj, rfl⟩ <;> simp_all [Tm.static, Tm.vacant]⟩

theorem Tm.isTele_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).isTele := by
  intro t; induction t <;> intro k h <;> simp_all [isTele, inst]

theorem Tm.len_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).len = t.len := by
  intro t; induction t <;> intro k h <;> simp_all [inst, len, isTele]

theorem retOf_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → retOf (t.inst u k) = (retOf t).map (·.inst u (k + t.len - 1)) := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro k ht
    simp only [Tm.isTele] at ht
    cases r with
    | nil => cases m <;> simp [retOf, Tm.inst, Tm.len]
    | bind m' A' r' =>
      have := ihr (k + 1) ht
      simp only [Tm.inst, retOf] at this ⊢
      rw [this]; simp [Tm.len]; congr 1; funext x; congr 1; omega
    | _ => simp [Tm.isTele] at ht
  | nil => intro k _; simp [retOf, Tm.inst]
  | _ => intro k ht; simp [Tm.isTele] at ht

def bvList (n k : Nat) : List Tm := (List.range k).map fun j => .bv (n - 1 - j)

theorem bvList_succ (n k : Nat) : bvList n (k + 1) = .bv (n - 1) :: bvList (n - 1) k := by
  simp only [bvList, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1; apply List.map_congr_left; intro j _; simp; omega

theorem ofList_inst (u : Tm) (k : Nat) : ∀ l : List Tm, (Tm.ofList l).inst u k = Tm.ofList (l.map (·.inst u k))
  | [] => rfl
  | x :: l => by simp [Tm.ofList, Tm.inst, ofList_inst u k l]

theorem bvList_inst (u : Tm) {n k m : Nat} (hk : k ≤ n) (hm : n ≤ m) : (bvList n k).map (·.inst u m) = bvList n k := by
  simp only [bvList, List.map_map]; apply List.map_congr_left; intro j hj
  simp at hj; simp only [Function.comp, Tm.inst]; split <;> (try split) <;> first | omega | rfl

theorem VTys.nil_out' {vs out : Tm} : VTys P vs .nil out → out = .nil := by
  intro h; cases h; rfl

theorem VTys.det : ∀ {vs tele out out' : Tm}, VTys P vs tele out → VTys P vs tele out' → out = out'
  | _, _, _, _, .nil, h => by cases h; rfl
  | _, _, _, _, .cons _ hr, h => by cases h with | cons _ hr' => exact VTys.det hr hr'
  | _, _, _, _, .isCons _ hr, h => by cases h with | isCons _ hr' => exact VTys.det hr hr'

theorem VTys.retHead : ∀ {vs tele out : Tm}, VTys P vs tele out → tele.isTele → (∀ x ∈ vs.toList, x.lc 0) →
    out ≠ .nil → ∀ d (pre : List Tm) k idx, (∀ x ∈ pre, x.lc 0) → k ≤ tele.len - 1 →
    retOf tele = some (.app (.tyc d (.ofList (pre ++ bvList (tele.len - 1) k))) idx) →
    ∃ idx', retOf out = some (.app (.tyc d (.ofList (pre ++ vs.toList.take k ++ bvList (out.len - 1) (k - vs.len)))) idx')
  | _, _, _, .nil, _, _, _, d, pre, k, idx, _, _, hr => ⟨idx, by simpa [Tm.toList, Tm.len] using hr⟩
  | _, _, _, .cons (v := v) (vs := vs') (r := r) _ hr, ht, hv, hn, d, pre, k, idx, hp, hk, hret
  | _, _, _, .isCons (v := v) (vs := vs') (r := r) _ hr, ht, hv, hn, d, pre, k, idx, hp, hk, hret => by
    simp only [Tm.isTele] at ht
    cases r with
    | nil => exact absurd (VTys.nil_out' (by simpa [Tm.inst] using hr)) hn
    | bind m' A' r' =>
      have hvv : v.lc 0 := hv v (by simp [Tm.toList])
      have hv' : ∀ x ∈ vs'.toList, x.lc 0 := fun x hx => hv x (by simp [Tm.toList, hx])
      have hti : ((Tm.bind m' A' r').inst v 0).isTele := Tm.isTele_inst v _ 0 ht
      simp only [retOf] at hret
      have hri := retOf_inst v (.bind m' A' r') 0 ht
      rw [hret] at hri
      have hlen : ((Tm.bind m' A' r').inst v 0).len = (Tm.bind m' A' r').len := Tm.len_inst v _ 0 ht
      simp only [Tm.len, Nat.zero_add, Nat.add_sub_cancel] at hk hlen hri
      have hpre : pre.map (·.inst v r'.len) = pre :=
        List.map_congr_left (fun x hx => Tm.inst_lc x 0 _ (hp x hx) (Nat.zero_le _)) |>.trans (by simp)
      cases k with
      | zero =>
        obtain ⟨idx', h'⟩ := VTys.retHead hr hti hv' hn d pre 0 (idx.inst v r'.len) hp (Nat.zero_le _) (by
          rw [hri, hlen]; simp [Tm.inst, ofList_inst, bvList, hpre])
        exact ⟨idx', by simpa [bvList, Tm.toList] using h'⟩
      | succ k =>
        obtain ⟨idx', h'⟩ := VTys.retHead hr hti hv' hn d (pre ++ [v]) k (idx.inst v r'.len)
          (by intro x hx; simp at hx; rcases hx with hx | rfl; exact hp x hx; exact hvv) (by rw [hlen]; simp [Tm.len]; omega) (by
          rw [hri, hlen]; simp only [Option.map_some, Tm.inst, ofList_inst, List.map_append, bvList_succ, List.map_cons]
          rw [hpre, bvList_inst v (by omega) (by omega)]
          simp [Tm.inst, Tm.len])
        refine ⟨idx', ?_⟩; rw [h']; simp [Tm.toList, Tm.len]
    | _ => simp [Tm.isTele] at ht

theorem EnvOK.get {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {i : Nat} {T : Tm} (h : Γ.tys[i]? = some T) :
    ∃ v, ρ[i]? = some v ∧ Tm.env ρ i = v ∧ VTy P v (T.subst (Tm.env ρ)) := by
  have hi : i < ρ.length := by rw [hE.len]; exact (getElem?_eq_some_iff.mp h).1
  refine ⟨ρ[i], by simp, by simp [Tm.env, hi], hE.vals i _ T (by simp) h⟩

theorem VTy.vc_inv {v s : Tm} (h : VTy P v (.valCtor s)) :
    ∃ d c ls sig, v = .vc d c ls ∧ P.ctor d c = some sig ∧ ls.len = P.lifted d ∧ VTys P ls sig s := by
  cases h with
  | vc hc hl hs => exact ⟨_, _, _, _, rfl, hc, hl, hs⟩
  | con _ _ _ _ he => cases he

theorem VTy.sig_det {v A B : Tm} (hA : VTy P v A) (hB : VTy P v B)
    (ha : ∃ x, A = .tyCtor x ∨ A = .valCtor x) (hb : ∃ x, B = .tyCtor x ∨ B = .valCtor x) : A = B := by
  obtain ⟨x, rfl | rfl⟩ := ha <;> obtain ⟨y, rfl | rfl⟩ := hb <;> cases hA <;> cases hB <;> simp_all <;>
    rename_i h1 _ _ h2 <;> first | rw [VTys.det h1 h2] | (subst_vars; rw [VTys.det h1 h2])

namespace Tm

theorem lc_toList : ∀ (t : Tm) d, t.lc d → ∀ v ∈ t.toList, v.lc d := by
  intro t; induction t <;> intro d h v hv <;> simp_all [toList, lc] <;> grind

theorem ofList_toList : ∀ (t : Tm), t.isList → ofList t.toList = t := by
  intro t; induction t <;> simp_all [ofList, toList, isList]

theorem toList_subst (f : Nat → Tm) : ∀ (t : Tm), t.isList → (t.subst f).toList = t.toList.map (subst f) := by
  intro t; induction t <;> simp_all [toList, subst, isList]

theorem isList_subst (f : Nat → Tm) : ∀ (t : Tm), t.isList → (t.subst f).isList := by
  intro t; induction t <;> simp_all [subst, isList]

theorem len_toList : ∀ (t : Tm), t.isList → t.toList.length = t.len := by
  intro t; induction t <;> simp_all [toList, isList, len]

end Tm

theorem Tm.len_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele ∨ t.isList → (t.subst f).len = t.len := by
  intro t; induction t <;> intro h <;> simp_all [subst, len, isTele, isList]

theorem Tm.isTele_of_inst_fv (i : Nat) : ∀ (t : Tm) k, (t.inst (.fv i) k).isTele → t.isTele := by
  intro t; induction t with
  | bind _ _ r _ ihr => intro k h; simp only [inst, isTele] at h ⊢; exact ihr _ h
  | bv j | sbv j => intro k h; simp only [inst] at h; split at h <;> (try split at h) <;> simp [isTele, slotOf] at h
  | _ => intro k h; simp_all [inst, isTele]

theorem TeleOK.isTele {Γ : Ctx} {t : Tm} : TeleOK P Γ t → t.isTele
  | .nil => rfl
  | .cons _ _ h => by simp only [Tm.isTele]; exact Tm.isTele_of_inst_fv _ _ 0 h.isTele
  | .isCons _ h => by simp only [Tm.isTele]; exact Tm.isTele_of_inst_fv _ _ 0 h.isTele

theorem ArgsTy.isList {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → args.isList
  | .nil => rfl
  | .cons _ _ h | .isCons _ _ h | .anyCons _ h => by simp only [Tm.isList]; exact h.isList

theorem ArgsTy.isTele {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → out.isTele
  | .nil, h => h
  | .cons _ _ hr, h | .isCons _ _ hr, h | .anyCons _ hr, h => hr.isTele (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h))

theorem ArgsTy.len {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → args.len + out.len = tele.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ _ hr, h | .isCons (r := r) _ _ hr, h | .anyCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    have := hr.len (Tm.isTele_inst _ _ 0 h)
    rw [Tm.len_inst _ _ _ h] at this
    simp [Tm.len]; omega

theorem VTys.len {vs tele out : Tm} : VTys P vs tele out → tele.isTele → vs.len + out.len = tele.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ hr, h | .isCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    have := hr.len (Tm.isTele_inst _ _ 0 h)
    rw [Tm.len_inst _ _ _ h] at this
    simp [Tm.len]; omega

theorem VTys.peel : ∀ {vs tele out : Tm}, VTys P vs tele out → out = tele.peel vs
  | _, _, _, .nil => by cases ‹Tm› <;> rfl
  | _, _, _, .cons _ hr | _, _, _, .isCons _ hr => by simp only [Tm.peel]; exact hr.peel

theorem VTys.isTele {vs tele out : Tm} : VTys P vs tele out → tele.isTele → out.isTele
  | .nil, h => h
  | .cons _ hr, h | .isCons _ hr, h => hr.isTele (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h))

theorem VTys.isList {vs tele out : Tm} : VTys P vs tele out → vs.isList
  | .nil => rfl
  | .cons _ hr | .isCons _ hr => by simp only [Tm.isList]; exact hr.isList

theorem lc_of_static {ρ : List Tm} (hc : ∀ v ∈ ρ, v.lc 0) {t : Tm} {n : Nat} (h : t.static n 0) :
    (t.subst (Tm.env ρ)).lc 0 := Tm.lc_subst (Tm.env_lc hc) t 0 n h

theorem static_toList {t : Tm} {n : Nat} (h : t.static n 0) : ∀ v ∈ t.toList, v.static n 0 := by
  induction t <;> simp_all [Tm.toList, Tm.static]

mutual
theorem tm_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) : ∀ {t T : Tm}, TmTy P Γ t T →
    VTy P (t.subst (Tm.env ρ)) (T.subst (Tm.env ρ)) ∧ t.static Γ.n 0 ∧ T.static Γ.n 0
  | _, _, .fv h => by
    obtain ⟨v, _, he, hv⟩ := hE.get h
    refine ⟨by simpa [Tm.subst, he] using hv, ?_, hE.wf.tys _ _ h⟩
    exact decide_eq_true (getElem?_eq_some_iff.mp h).1
  | _, _, .fvIs (i := i) _ hs ht => by
    obtain ⟨hv, _, hT⟩ := tm_sound hP hE ht
    refine ⟨by simp only [Tm.subst]; rw [hE.sat i _ hs]; exact hv, decide_eq_true (hE.wf.σ i _ hs).1, hT⟩
  | _, _, .univ => ⟨.univ, rfl, rfl⟩
  | _, _, .level => ⟨.univ, rfl, rfl⟩
  | _, _, .tyc hD hl ha => by
    obtain ⟨hvs, hls, hout⟩ := args_sound hP hE ha (Tm.static_mono (Nat.zero_le Γ.n) _ (Nat.le_refl 0) (hP.params _ _ hD).2)
    rw [Tm.subst_static0 _ _ 0 (hP.params _ _ hD).2] at hvs
    refine ⟨.tyCtor hD (by rw [Tm.len_subst _ _ (.inr ha.isList), hl]) hvs, by simpa [Tm.static] using hls,
      by simpa [Tm.static] using hout⟩
  | _, _, .vc (d := d) hc hl ha => by
    obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
    obtain ⟨_, hs0, _⟩ := hP.ctors _ _ _ _ hD hsig
    obtain ⟨hvs, hls, hout⟩ := args_sound hP hE ha (Tm.static_mono (Nat.zero_le Γ.n) _ (Nat.le_refl 0) hs0)
    rw [Tm.subst_static0 _ _ 0 hs0] at hvs
    refine ⟨.vc hc (by rw [Tm.len_subst _ _ (.inr ha.isList), hl]) hvs, by simpa [Tm.static] using hls,
      by simpa [Tm.static] using hout⟩
  | _, _, .tyApp hh hH ha => by
    obtain ⟨_, hs, Hs⟩ := tm_sound hP hE hh
    have hps := canon_static hE.wf Hs; rw [hH] at hps
    have := args_sound hP hE ha (by simpa [Tm.static] using hps)
    exact ⟨.univ, by simp [Tm.static, hs, this.2.1], rfl⟩
  | _, _, .vcApp (H := H) (args := args) (sig := sig) hh hH ha => by
    obtain ⟨vh, hs, Hs⟩ := tm_sound hP hE hh
    have hps := canon_static hE.wf Hs; rw [hH] at hps
    rw [← hE.canon H, hH] at vh; simp only [Tm.subst] at vh
    obtain ⟨d, c, ls, sig0, hv, hc, hl, hls⟩ := vh.vc_inv
    obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
    obtain ⟨ht0, _, idx, hr⟩ := hP.ctors _ _ _ _ hD hsig
    obtain ⟨hvs, hargs, hout⟩ := args_sound hP hE ha (by simpa [Tm.static] using hps)
    simp only [Tm.subst] at hvs
    have hlc : ∀ x ∈ ls.toList, x.lc 0 := by
      have := lc_of_static hE.closed hs; rw [hv] at this
      exact Tm.lc_toList ls 0 (by simpa [Tm.lc] using this)
    have hlc' : ∀ x ∈ (args.subst (Tm.env ρ)).toList, x.lc 0 :=
      Tm.lc_toList _ 0 (lc_of_static hE.closed hargs)
    have ht0' := ht0.isTele
    have hmid : (sig.subst (Tm.env ρ)).isTele := hls.isTele ht0'
    have hlen := hls.len ht0'
    have houtlen := hvs.len hmid
    have hLd : P.lifted d = D.lifted := by simp [Prog.lifted, hD]
    have hlsl := Tm.len_toList _ hls.isList
    obtain ⟨i1, h1⟩ := VTys.retHead hls ht0' hlc (by intro h; rw [h] at houtlen; simp [Tm.len, Tm.subst] at houtlen) d [] (P.lifted d) idx
      (by simp) (by simp [Tm.subst, Tm.len] at houtlen; omega) (by rw [hr, hLd]; simp [liftBvs, bvList])
    rw [← hl, ← hlsl, List.take_length, Nat.sub_self] at h1
    simp only [List.nil_append, bvList, List.range_zero, List.map_nil, List.append_nil, Tm.ofList_toList _ hls.isList] at h1
    obtain ⟨i2, h2⟩ := VTys.retHead hvs hmid hlc' (by simp [Tm.subst]) d ls.toList 0 i1 hlc (Nat.zero_le _)
      (by simpa [bvList, Tm.ofList_toList _ hls.isList] using h1)
    simp [Tm.subst, retOf, bvList, Tm.ofList_toList _ hls.isList] at h2
    refine ⟨?_, by simp [Tm.static, hs, hargs], by simpa [Tm.static] using hout⟩
    simp only [Tm.subst]; rw [hv]; exact .con hc hl hls hvs h2
  | _, _, .tyCtor _ hs => ⟨.univ, hs, rfl⟩
  | _, _, .valCtor _ hs _ => ⟨.univ, hs, rfl⟩
  | _, _, .predates hA _ hx _ hL _ => by
    have := tm_sound hP hE hA; have := tm_sound hP hE hx; have := tm_sound hP hE hL
    exact ⟨.univ, by simp_all [Tm.static], rfl⟩
  | _, _, .subterm hA _ ha _ hB _ hb _ => by
    have := tm_sound hP hE hA; have := tm_sound hP hE ha; have := tm_sound hP hE hB; have := tm_sound hP hE hb
    exact ⟨.univ, by simp_all [Tm.static], rfl⟩
  | _, _, .fn _ _ _ _ hs => ⟨.univ, hs, rfl⟩
  | _, _, .mtbl hs => ⟨.univ, hs, rfl⟩
  | _, _, .sfv (i := i) hi hs => by
    obtain ⟨D, m, e, u, hD, hc, hl, -, -, -⟩ := Tm.slotOK_spec hs
    have hct : P.ctor slotD 0 = some (.bind (.ty m e u) (.app (.tyc slotD .nil) .nil) .nil) := by
      simp [Prog.ctor, hD, hc]
    have hv : (Tm.sfv i).subst (Tm.env ρ) = Tm.vacant := by
      simp only [Tm.subst]; exact Tm.slotOf_lc0 (Tm.env_lc hE.closed i)
    refine ⟨hv ▸ .con hct (by simp [Tm.len, Prog.lifted, hD, hl]) .nil .nil rfl, by simpa [Tm.static] using hi,
      by simp [Tm.static]⟩

theorem args_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) : ∀ {args tele out : Tm},
    ArgsTy P Γ args tele out → tele.static Γ.n 0 →
    VTys P (args.subst (Tm.env ρ)) (tele.subst (Tm.env ρ)) (out.subst (Tm.env ρ)) ∧
      args.static Γ.n 0 ∧ out.static Γ.n 0
  | _, _, _, .nil, hs => ⟨.nil, rfl, hs⟩
  | _, _, _, .cons (a := a) (r := r) (T := T) (A := A) ha hc hr, hs => by
    simp only [Tm.static, Bool.and_eq_true] at hs
    obtain ⟨hv, has, _⟩ := tm_sound hP hE ha
    obtain ⟨hvs, hass, hout⟩ := args_sound hP hE hr (Tm.static_inst has r 0 hs.2)
    rw [Tm.subst_inst _ (Tm.env_lc hE.closed) a r 0] at hvs
    have e : T.subst (Tm.env ρ) = A.subst (Tm.env ρ) := by rw [← hE.canon, hc, hE.canon]
    refine ⟨by simp only [Tm.subst]; exact .cons (e ▸ hv) hvs, by simp [Tm.static, has, hass], hout⟩
  | _, _, _, .isCons (a := a) (r := r) (e := e) ha hc hr, hs => by
    simp only [Tm.static, Bool.and_eq_true] at hs
    obtain ⟨_, has, _⟩ := tm_sound hP hE ha
    obtain ⟨hvs, hass, hout⟩ := args_sound hP hE hr (Tm.static_inst has r 0 hs.2)
    rw [Tm.subst_inst _ (Tm.env_lc hE.closed) a r 0] at hvs
    have e' : a.subst (Tm.env ρ) = e.subst (Tm.env ρ) := by rw [← hE.canon, hc, hE.canon]
    refine ⟨by simp only [Tm.subst]; exact .isCons e' hvs, by simp [Tm.static, has, hass], hout⟩
  | _, _, _, .anyCons (a := a) (r := r) ha hr, hs => by
    have hs' : r.static Γ.n 1 := by simpa [Tm.static] using hs
    obtain ⟨hv, has, _⟩ := tm_sound hP hE ha
    obtain ⟨hvs, hass, hout⟩ := args_sound hP hE hr (Tm.static_inst has r 0 hs')
    rw [Tm.subst_inst _ (Tm.env_lc hE.closed) a r 0] at hvs
    refine ⟨by simp only [Tm.subst]; exact .cons .top hvs, by simp [Tm.static, has, hass], hout⟩
end

theorem arr_getElem?_append_cases {α : Type} {l1 : Array α} {l2 : List α} {i : Nat} {x : α}
    (h : (l1 ++ l2.toArray)[i]? = some x) :
    (i < l1.size ∧ l1[i]? = some x) ∨ (l1.size ≤ i ∧ l2[i - l1.size]? = some x) := by
  rw [Array.getElem?_append] at h; split at h
  · exact .inl ⟨by omega, h⟩
  · exact .inr ⟨by omega, by simpa using h⟩

theorem getElem?_append_cases {α : Type} {l1 l2 : List α} {i : Nat} {x : α} (h : (l1 ++ l2)[i]? = some x) :
    (i < l1.length ∧ l1[i]? = some x) ∨ (l1.length ≤ i ∧ l2[i - l1.length]? = some x) := by
  rw [List.getElem?_append] at h; split at h
  · exact .inl ⟨by omega, h⟩
  · exact .inr ⟨by omega, h⟩

theorem Ctx.WF.mono {Γ : Ctx} (h : Γ.WF) (Ts : List Tm) (hT : ∀ T ∈ Ts, T.static Γ.n 0) :
    ({ Γ with tys := Γ.tys ++ Ts.toArray } : Ctx).WF := by
  have hn : Γ.n ≤ ({ Γ with tys := Γ.tys ++ Ts.toArray } : Ctx).n := by simp [Ctx.n]
  refine ⟨fun i T hi => ?_, fun e t he => ?_, h.ς_mono hn, fun L hL => ?_, fun c hc => ?_, fun s hs => ?_⟩
  · rcases arr_getElem?_append_cases hi with ⟨hi, hT'⟩ | ⟨hi, hT'⟩ <;>
      exact Tm.static_mono hn _ (Nat.le_refl 0) (by first | exact h.tys i T hT' | exact hT T (List.mem_of_getElem? hT'))
  · exact ⟨Nat.lt_of_lt_of_le (h.σ e t he).1 hn, Tm.static_mono hn _ (Nat.le_refl 0) (h.σ e t he).2⟩
  · exact Nat.lt_of_lt_of_le (h.mints L hL) hn
  · exact Nat.lt_of_lt_of_le (h.cur c hc) hn
  · exact Nat.lt_of_lt_of_le (h.subs s hs) hn

theorem EnvOK.pushMany {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (vs Ts : List Tm) (hl : vs.length = Ts.length)
    (hv : ∀ (j : Nat) (v T : Tm), vs[j]? = some v → Ts[j]? = some T →
      VTy P v (T.subst (Tm.env ρ)) ∧ T.static Γ.n 0 ∧ v.lc 0) :
    EnvOK P (ρ ++ vs) { Γ with tys := Γ.tys ++ Ts.toArray } := by
  have hlen := hE.len
  have hwf := hE.wf
  have hT : ∀ T ∈ Ts, T.static Γ.n 0 := fun T hT => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT
    exact (hv j vs[j] _ (List.getElem?_eq_getElem (by omega)) (by simp)).2.1
  refine .mk (by simp [Ctx.n] at *; omega) (fun i v T hi hTi => ?_) (fun v hv' => ?_) (fun e t he => ?_)
    (fun L hL => ?_) (hwf.mono Ts hT) hE.fix.append hE.dele.append
  · have hn : ρ.length = Γ.tys.size := hlen
    rcases arr_getElem?_append_cases hTi with ⟨hi', hT'⟩ | ⟨hi', hT'⟩
    · rw [List.getElem?_append_left (by omega)] at hi
      rw [Tm.subst_append (hlen ▸ hwf.tys i T hT')]
      exact hE.vals i v T hi hT'
    · rw [List.getElem?_append_right (by omega)] at hi
      rw [hn] at hi
      obtain ⟨h1, h2, _⟩ := hv _ v T hi hT'
      rw [Tm.subst_append (hlen ▸ h2)]; exact h1
  · rcases List.mem_append.mp hv' with h | h
    · exact hE.closed v h
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
      exact (hv j _ Ts[j] (by simp) (List.getElem?_eq_getElem (by omega))).2.2
  · obtain ⟨he', ht⟩ := hwf.σ e t he
    show Tm.env (ρ ++ vs) e = t.subst (Tm.env (ρ ++ vs))
    rw [Tm.env_append (by omega), Tm.subst_append (hlen ▸ ht)]
    exact hE.sat e t he
  · obtain ⟨m, hm, hlt⟩ := (match hE with | .mk _ _ _ _ h _ _ _ => h) L hL
    have hL' : L < ρ.length := hlen ▸ hwf.mints L hL
    refine ⟨m, by rw [List.getElem?_append_left hL']; exact hm, fun i hi v hv => ?_⟩
    rw [List.getElem?_append_left (by omega)] at hv
    exact hlt i hi v hv

def Chrono (ρ : List Tm) (L : Nat) : Prop :=
  ∃ m, ρ[L]? = some (.lvl m) ∧ ∀ i < L, ∀ (v : Tm), ρ[i]? = some v → ∀ n ∈ v.levels, n < m

theorem EnvOK.chrono {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ∀ L ∈ Γ.mints, Chrono ρ L
  | .mk _ _ _ _ h _ _ _ => h

theorem EnvOK.modify {ρ : List Tm} {Γ Γ' : Ctx} (hE : EnvOK P ρ Γ) (ht : Γ'.tys = Γ.tys)
    (hσ : Sat (Tm.env ρ) Γ'.σ) (hm : ∀ L ∈ Γ'.mints, Chrono ρ L) (hw : Γ'.WF) (hf : Γ'.fixed = Γ.fixed := by rfl)
    (hd : Γ'.deles = Γ.deles := by rfl) : EnvOK P ρ Γ' :=
  .mk (by rw [hE.len]; simp [Ctx.n, ht]) (fun i v T h1 h2 => hE.vals i v T h1 (ht ▸ h2)) hE.closed hσ hm hw
    (hf ▸ hE.fix) (hd ▸ hE.dele)

theorem EnvOK.setDeles {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (ds : List (Nat × Nat × Bool × Bool)) (hd : DeleOK P ds ρ) :
    EnvOK P ρ { Γ with deles := ds } :=
  .mk hE.len hE.vals hE.closed hE.sat hE.chrono ⟨hE.wf.tys, hE.wf.σ, hE.wf.ς, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩ hE.fix hd

theorem EnvOK.refix {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (F : List (Option Tm)) (hF : FixOK P F ρ) :
    EnvOK P ρ { Γ with fixed := F } :=
  .mk hE.len hE.vals hE.closed hE.sat (fun L hL => hE.chrono L hL)
    ⟨hE.wf.tys, hE.wf.σ, hE.wf.ς, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩ hF hE.dele

theorem slotSub_static {n d r : Nat} {s : Tm} (hs : s = Tm.vacant ∨ ∃ j < n, s = .sfv j) {t : Tm}
    (h : t.static n d) : (Ctx.slotSub r s t).static n d :=
  Tm.static_subst2 t d h fun i hi => ⟨by simp [Tm.static]; exact Tm.fvs_static t d h i hi, by
    by_cases e : i = r
    · subst e; rcases hs with rfl | ⟨j, hj, rfl⟩ <;> simp_all [Tm.static, Tm.vacant]
    · simp [e, Tm.static]; exact Tm.fvs_static t d h i hi⟩

theorem Ctx.sfv_canon_lt {Γ : Ctx} (hw : Γ.WF) {e r : Nat} (he : e < Γ.n) (h : Γ.canon (.sfv e) = .sfv r) : r < Γ.n := by
  simp only [Ctx.canon, canonBy, Tm.subst2] at h
  cases hς : Γ.ς e with
  | none => rw [hς] at h; cases h; exact he
  | some u =>
    rw [hς] at h; simp only [Option.getD_some] at h; subst h
    rcases (hw.ς e _ hς).2 with h | ⟨j, hj, h⟩
    · simp [Tm.vacant] at h
    · cases h; exact hj

theorem Ctx.slotBind_spec {Γ : Ctx} (hw : Γ.WF) {e r : Nat} {s t : Tm} (h : Γ.slotBind e s = some (r, t)) :
    r < Γ.n ∧ (t = Tm.vacant ∨ ∃ j < Γ.n, t = .sfv j) := by
  unfold Ctx.slotBind at h
  split at h
  · rename_i hse
    obtain ⟨hs, he⟩ := hse
    split at h
    · rename_i r0 _ hc
      split at h
      · cases h
      · cases h; exact ⟨Ctx.sfv_canon_lt hw he hc, Tm.isSlotVal_spec hs⟩
    · split at h
      · rename_i ha; cases h
        exact ⟨by simpa [Tm.isSlotVal] using hs, Tm.isSlotVal_spec ha⟩
      · cases h
    · cases h
  · cases h

theorem EnvOK.bindSlot {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {r : Nat} {s : Tm} (hr : r < Γ.n)
    (hs : s = Tm.vacant ∨ ∃ j < Γ.n, s = .sfv j) : EnvOK P ρ (Γ.bindSlot r s) := by
  have hc := Tm.env_lc hE.closed
  have hS : SatS (Tm.env ρ) (fun j => if j = r then some s else none) := by
    intro e u h; dsimp only at h; split at h
    · cases h; exact slotVal_subst hc hs e
    · cases h
  have hsub : ∀ t, (Ctx.slotSub r s t).subst (Tm.env ρ) = t.subst (Tm.env ρ) :=
    canonBy_sound (fun _ _ h => by cases h) hS
  refine hE.modify rfl (fun i u hi => ?_) hE.chrono
    ⟨hE.wf.tys, fun i u hi => ?_, fun i u hi => ?_, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩
  · simp only [Ctx.bindSlot, Option.map_eq_some_iff] at hi
    obtain ⟨u0, h0, rfl⟩ := hi
    rw [hsub]; exact hE.sat i u0 h0
  · simp only [Ctx.bindSlot, Option.map_eq_some_iff] at hi
    obtain ⟨u0, h0, rfl⟩ := hi
    obtain ⟨h1, h2⟩ := hE.wf.σ i u0 h0
    exact ⟨h1, slotSub_static hs h2⟩
  · simp only [Ctx.bindSlot] at hi; split at hi
    · cases hi; subst_vars; exact ⟨hr, hs⟩
    · simp only [Option.map_eq_some_iff] at hi
      obtain ⟨u0, h0, rfl⟩ := hi
      obtain ⟨h1, h2⟩ := hE.wf.ς i u0 h0
      refine ⟨h1, ?_⟩
      rcases h2 with rfl | ⟨j, hj, rfl⟩
      · left; rfl
      · by_cases e : j = r
        · subst e; simp only [Ctx.slotSub, canonBy, Tm.subst2, if_true, Option.getD_some]; exact hs
        · right; exact ⟨j, hj, by simp [Ctx.slotSub, canonBy, Tm.subst2, e]⟩

theorem Ctx.slotBind_val {Γ : Ctx} {e r : Nat} {s t : Tm} (h : Γ.slotBind e s = some (r, t)) :
    t.isSlotVal Γ.n = true := by
  unfold Ctx.slotBind at h
  split at h
  · rename_i hse
    split at h
    · split at h
      · cases h
      · cases h; exact hse.1
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · cases h

theorem Ctx.bindSlot_sat {Γ : Ctx} {r : Nat} {s : Tm} {f : Nat → Tm} (hs : s.isSlotVal Γ.n = true)
    (hc : ∀ i, (f i).lc 0) (h : Sat f (Γ.bindSlot r s).σ) : Sat f Γ.σ := by
  intro i t hi
  have hS : SatS f (fun j => if j = r then some s else none) := by
    intro e u h; dsimp only at h; split at h
    · cases h; exact slotVal_subst hc (Tm.isSlotVal_spec hs) e
    · cases h
  rw [h i (Ctx.slotSub r s t) (by simp [Ctx.bindSlot, hi])]; exact canonBy_sound (fun _ _ h => by cases h) hS t

theorem Ctx.withSlot_sat {Γ : Ctx} {e : Nat} {s : Tm} {f : Nat → Tm} (hc : ∀ i, (f i).lc 0)
    (h : Sat f (Γ.withSlot e s).σ) : Sat f Γ.σ := by
  unfold Ctx.withSlot at h; split at h
  · rename_i hb; exact Ctx.bindSlot_sat (Ctx.slotBind_val hb) hc h
  · exact h

theorem Ctx.slotIf_sat {Γ : Ctx} {b : Bool} {e : Nat} {s : Tm} {f : Nat → Tm} (hc : ∀ i, (f i).lc 0)
    (h : Sat f (Γ.slotIf b e s).σ) : Sat f Γ.σ := by
  cases b
  · exact h
  · exact Ctx.withSlot_sat hc h

theorem EnvOK.withSlot {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {e : Nat} (s : Tm) :
    EnvOK P ρ (Γ.withSlot e s) := by
  unfold Ctx.withSlot; split
  · rename_i h
    obtain ⟨hr, ht⟩ := Ctx.slotBind_spec hE.wf h
    exact hE.bindSlot hr ht
  · exact hE

theorem EnvOK.slotIf {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (b : Bool) {e : Nat} (s : Tm) :
    EnvOK P ρ (Γ.slotIf b e s) := by
  cases b
  · exact hE
  · exact hE.withSlot s

theorem EnvOK.withRule {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {e : Nat} {t : Tm} (he : e < Γ.n)
    (ht : t.static Γ.n 0) (hv : Tm.env ρ e = t.subst (Tm.env ρ)) : EnvOK P ρ (Γ.withRule e t) := by
  refine hE.modify rfl (fun i u hi => ?_) hE.chrono ⟨hE.wf.tys, fun i u hi => ?_, hE.wf.ς, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩
  all_goals simp only [Ctx.withRule] at hi; split at hi
  · cases hi; subst_vars; exact hv
  · exact hE.sat i u hi
  · cases hi; subst_vars; exact ⟨he, ht⟩
  · exact hE.wf.σ i u hi

theorem EnvOK.congr {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (Γ' : Ctx) (ht : Γ'.tys = Γ.tys)
    (hσ : Γ'.σ = Γ.σ) (hm : Γ'.mints = Γ.mints) (hc : Γ'.cur = Γ.cur) (hs : Γ'.subs = Γ.subs)
    (hf : Γ'.fixed = Γ.fixed := by rfl) (hd : Γ'.deles = Γ.deles := by rfl) (hς : Γ'.ς = Γ.ς := by rfl) :
    EnvOK P ρ Γ' := by
  have hn : Γ'.n = Γ.n := by simp [Ctx.n, ht]
  have w := hE.wf
  refine hE.modify ht (by rw [hσ]; exact hE.sat) (by rw [hm]; exact hE.chrono) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hf hd
  · intro i T h; rw [hn]; exact w.tys i T (ht ▸ h)
  · intro e t h; rw [hn]; exact w.σ e t (hσ ▸ h)
  · intro e s h; rw [hn]; exact w.ς e s (hς ▸ h)
  · intro L h; rw [hn]; exact w.mints L (hm ▸ h)
  · intro c h; rw [hn]; exact w.cur c (hc ▸ h)
  · intro s h; rw [hn]; exact w.subs s (hs ▸ h)

theorem EnvOK.cm {ρ : List Tm} {Γ : Ctx} (b : Bool) (hE : EnvOK P ρ Γ) : EnvOK P ρ { Γ with cmode := b } :=
  hE.congr _ rfl rfl rfl rfl rfl

theorem EnvOK.push {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {v A : Tm} (hv : VTy P v (A.subst (Tm.env ρ)))
    (hA : A.static Γ.n 0) (hc : v.lc 0) {e : Bool} : EnvOK P (ρ ++ [v]) (Γ.push A e) :=
  (hE.pushMany [v] [A] rfl fun j v' T h1 h2 => by
    cases j with
    | zero => simp at h1 h2; subst h1 h2; exact ⟨hv, hA, hc⟩
    | succ => simp at h1).congr _ rfl rfl rfl rfl rfl

def LvlBound (ρ : List Tm) (cnt : Nat) : Prop := ∀ v ∈ ρ, ∀ n ∈ v.levels, n < cnt

theorem EnvOK.pushMint {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt) :
    EnvOK P (ρ ++ [.lvl cnt]) Γ.pushMint := by
  have h1 := hE.push (v := .lvl cnt) (A := .level) .lvl rfl trivial (e := false)
  have hl := hE.len
  refine h1.modify rfl h1.sat (fun L hL => ?_) ?_
  · simp only [Ctx.pushMint, List.mem_append, List.mem_singleton] at hL
    rcases hL with hL | rfl
    · obtain ⟨m, hm, hlt⟩ := hE.chrono L hL
      have hL' : L < ρ.length := hl ▸ hE.wf.mints L hL
      refine ⟨m, by rw [List.getElem?_append_left hL']; exact hm, fun i hi v hv => ?_⟩
      rw [List.getElem?_append_left (by omega)] at hv; exact hlt i hi v hv
    · refine ⟨cnt, by simp [hl.symm], fun i hi v hv => ?_⟩
      rw [List.getElem?_append_left (by simp only [Ctx.n] at hi hl; omega)] at hv
      exact hb v (List.mem_of_getElem? hv)
  · have w := h1.wf
    exact ⟨w.tys, w.σ, w.ς, fun L hL => by
      simp only [Ctx.pushMint, List.mem_append, List.mem_singleton] at hL
      rcases hL with hL | rfl
      · exact w.mints L hL
      · simp [Ctx.pushMint, Ctx.push, Ctx.n], w.cur, w.subs⟩

theorem Tm.isTele_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele → (t.subst f).isTele := by
  intro t; induction t <;> intro h <;> simp_all [isTele, subst]

structure Ctx.Ext (Γ Γ' : Ctx) : Prop where
  tys : ∃ Ts : List Tm, Γ'.tys = Γ.tys ++ Ts.toArray
  σ : ∀ f : Nat → Tm, (∀ i, (f i).lc 0) → Sat f Γ'.σ → Sat f Γ.σ
  mints : Γ'.mints = Γ.mints
  cur : Γ'.cur = Γ.cur
  subs : Γ'.subs = Γ.subs
  fixed : Γ'.fixed = Γ.fixed

theorem Ctx.Ext.trans {Γ Γ' Γ'' : Ctx} (h1 : Γ.Ext Γ') (h2 : Γ'.Ext Γ'') : Γ.Ext Γ'' := by
  obtain ⟨Ts, e1⟩ := h1.tys; obtain ⟨Us, e2⟩ := h2.tys
  exact ⟨⟨Ts ++ Us, by rw [e2, e1, Array.append_assoc]; simp⟩, fun f hc h => h1.σ f hc (h2.σ f hc h),
    h2.mints.trans h1.mints, h2.cur.trans h1.cur, h2.subs.trans h1.subs, h2.fixed.trans h1.fixed⟩

theorem Ctx.slotEq_eq (Γ : Ctx) (p : Tm × Tm) : ∃ σ ς, Γ.slotEq p = { Γ with σ := σ, ς := ς } := by
  unfold Ctx.slotEq; split
  · exact Γ.withSlot_eq _ _
  · exact Γ.withSlot_eq _ _
  · exact ⟨Γ.σ, Γ.ς, rfl⟩

theorem Ctx.foldl_slotEq_eq : ∀ (L : List (Tm × Tm)) (Γ : Ctx), ∃ σ ς, L.foldl Ctx.slotEq Γ = { Γ with σ := σ, ς := ς }
  | [], Γ => ⟨Γ.σ, Γ.ς, rfl⟩
  | p :: L, Γ => by
    obtain ⟨σ1, ς1, h1⟩ := Γ.slotEq_eq p
    obtain ⟨σ2, ς2, h2⟩ := Ctx.foldl_slotEq_eq L (Γ.slotEq p)
    exact ⟨σ2, ς2, by simp only [List.foldl_cons]; rw [h2, h1]⟩

theorem Ctx.forceSlots_eq (Γ : Ctx) (eqs : List (Tm × Tm)) : ∃ σ ς, Γ.forceSlots eqs = { Γ with σ := σ, ς := ς } :=
  Ctx.foldl_slotEq_eq _ _

@[simp] theorem Ctx.forceSlots_tys (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).tys = Γ.tys := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_erA (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).erA = Γ.erA := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_mints (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).mints = Γ.mints := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_cur (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).cur = Γ.cur := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_subs (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).subs = Γ.subs := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_ghost (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).ghost = Γ.ghost := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_opened (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).opened = Γ.opened := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_fixed (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).fixed = Γ.fixed := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_cmode (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).cmode = Γ.cmode := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_deles (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).deles = Γ.deles := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_pd (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).pd = Γ.pd := by
  obtain ⟨σ, ς, h⟩ := Γ.forceSlots_eq eqs; rw [h]
@[simp] theorem Ctx.forceSlots_n (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).n = Γ.n := by simp [Ctx.n]
@[simp] theorem Ctx.forceSlots_er (Γ : Ctx) (eqs : List (Tm × Tm)) : (Γ.forceSlots eqs).er = Γ.er := by funext i; simp [Ctx.er]

theorem EnvOK.forceSlots {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (eqs : List (Tm × Tm)) : EnvOK P ρ (Γ.forceSlots eqs) := by
  unfold Ctx.forceSlots
  generalize List.filter _ _ = L
  induction L generalizing Γ with
  | nil => exact hE
  | cons p L ih =>
    refine ih ?_
    unfold Ctx.slotEq; split <;> first | exact hE.withSlot _ | exact hE

theorem Ctx.slotEq_ghost (g : Bool) (Γ : Ctx) (p : Tm × Tm) :
    ({ Γ with ghost := g } : Ctx).slotEq p = { Γ.slotEq p with ghost := g } := by
  unfold Ctx.slotEq; split <;> first | rfl | exact Ctx.withSlot_upd_ghost Γ _ _ g

theorem Ctx.forceSlots_upd_ghost (g : Bool) (Γ : Ctx) (eqs : List (Tm × Tm)) :
    ({ Γ with ghost := g } : Ctx).forceSlots eqs = { Γ.forceSlots eqs with ghost := g } := by
  unfold Ctx.forceSlots
  rw [show (fun e : Tm × Tm => (({ Γ with ghost := g } : Ctx).canon e.1, ({ Γ with ghost := g } : Ctx).canon e.2)) =
    fun e => (Γ.canon e.1, Γ.canon e.2) from rfl]
  generalize List.filter _ _ = L
  induction L generalizing Γ with
  | nil => rfl
  | cons p L ih => simp only [List.foldl_cons]; rw [Ctx.slotEq_ghost]; exact ih _

theorem EnvOK.opnCtx {ρ : List Tm} {Γ : Ctx} {m : Nat} {oe : Bool} {σ' : Nat → Option Tm} {H cs : Tm}
    (h : EnvOK P ρ ({ Γ with opened := (m, oe) :: Γ.opened, σ := σ' } : Ctx)) : EnvOK P ρ (Γ.opnCtx P m oe σ' H cs) := by
  have hF := h.forceSlots (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList))
  obtain ⟨σf, ςf, he⟩ := Ctx.forceSlots_eq ({ Γ with opened := (m, oe) :: Γ.opened, σ := σ' } : Ctx)
    (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList))
  unfold Ctx.opnCtx; simp only [he] at hF ⊢; exact hF

theorem EnvOK.ntSlot {ρ : List Tm} {Γf : Ctx} (h : EnvOK P ρ Γf) (Γ : Ctx) (s k : Tm) :
    EnvOK P ρ (Γ.ntSlot P Γf s k) ∧ Γf.Ext (Γ.ntSlot P Γf s k) ∧
      ∃ σ ς, Γ.ntSlot P Γf s k = { Γf with σ := σ, ς := ς } := by
  have hw : ∀ e t, EnvOK P ρ (Γf.withSlot e t) ∧ Γf.Ext (Γf.withSlot e t) ∧
      ∃ σ ς, Γf.withSlot e t = { Γf with σ := σ, ς := ς } := fun e t => by
    obtain ⟨σ, ς, he⟩ := Γf.withSlot_eq e t
    refine ⟨h.withSlot t, ?_, σ, ς, he⟩
    rw [he]; exact ⟨⟨[], by simp⟩, fun f hc hs => Ctx.withSlot_sat hc (he ▸ hs), rfl, rfl, rfl, rfl⟩
  have hid : EnvOK P ρ Γf ∧ Γf.Ext Γf ∧ ∃ σ ς, Γf = { Γf with σ := σ, ς := ς } :=
    ⟨h, ⟨⟨[], by simp⟩, fun _ _ h => h, rfl, rfl, rfl, rfl⟩, Γf.σ, Γf.ς, rfl⟩
  unfold Ctx.ntSlot
  split
  · split
    · exact hw _ _
    · exact hid
  · exact hid

theorem EnvOK.pushEnt {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {k : Ent} {A r v vs out : Tm}
    (hv : VTys P (.cons v vs) (.bind k (A.subst (Tm.env ρ)) (r.subst (Tm.env ρ))) out) (hA : A.static Γ.n 0)
    (hc : v.lc 0) :
    EnvOK P (ρ ++ [v]) (Γ.pushEnt k A) ∧ VTys P vs ((r.subst (Tm.env ρ)).inst v 0) out ∧
      Γ.Ext (Γ.pushEnt k A) ∧ (Γ.pushEnt k A).n = Γ.n + 1 := by
  have ext : ∀ T e, Γ.Ext (Γ.push T e) := fun T _ => ⟨⟨[T], rfl⟩, fun _ _ h => h, rfl, rfl, rfl, rfl⟩
  cases hv with
  | cons hvA hvs => exact ⟨hE.push hvA hA hc, hvs, ext A _, by simp [Ctx.pushEnt, Ctx.push, Ctx.n]⟩
  | isCons he hvs =>
    rename_i mk er uu sl
    have hl := hE.len
    have hs := canon_static hE.wf hA
    have hE1 := (hE.push (A := .nil) (e := er) .top rfl hc).withRule (e := Γ.n) (t := Γ.canon A)
      (by simp [Ctx.push, Ctx.n])
      (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs)
      (by rw [Tm.subst_append (hl ▸ hs), hE.canon, ← he]; simp [Tm.env, hl])
    refine ⟨hE1.slotIf _ (e := Γ.n - 1) (Γ.canon A), hvs,
      ⟨⟨[.nil], by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push]⟩, fun f hc hs e t h => ?_,
        by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push], by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push],
        by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push], by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push]⟩,
      by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push, Ctx.n]⟩
    have := (hE.wf.σ e t h).1
    refine Ctx.slotIf_sat hc hs e t ?_
    simp only [Ctx.withRule, Ctx.push]
    rw [if_neg (by omega)]; exact h

theorem EnvOK.openTele {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) :
    ∀ {tele vs out : Tm}, tele.isTele → tele.static Γ.n 0 → VTys P vs (tele.subst (Tm.env ρ)) out →
    (∀ v ∈ vs.toList, v.lc 0) →
    EnvOK P (ρ ++ vs.toList) (Γ.openTele tele vs.len).1 ∧
    (Γ.openTele tele vs.len).2.subst (Tm.env (ρ ++ vs.toList)) = out ∧
    (Γ.openTele tele vs.len).2.static (Γ.openTele tele vs.len).1.n 0 ∧
    (Γ.openTele tele vs.len).2.isTele ∧
    (Γ.openTele tele vs.len).1.n = Γ.n + vs.len ∧
    Γ.Ext (Γ.openTele tele vs.len).1 := by
  intro tele vs
  induction vs generalizing ρ Γ tele with
  | cons v vs' _ ih =>
    intro out ht hs hv hc
    cases tele with
    | bind k A r =>
      simp only [Tm.isTele, Tm.static, Bool.and_eq_true] at ht hs
      have hl := hE.len
      have hc1 : v.lc 0 := hc v (by simp [Tm.toList])
      obtain ⟨hE', hvs, hext, hn⟩ := hE.pushEnt hv hs.1 hc1
      have hs' : (r.inst (.fv Γ.n) 0).static (Γ.pushEnt k A).n 0 :=
        Tm.static_inst (by simp [Tm.static, hn]) r 0 (Tm.static_mono (by omega) r (Nat.le_refl _) hs.2)
      have hr : (r.inst (.fv Γ.n) 0).subst (Tm.env (ρ ++ [v])) = (r.subst (Tm.env ρ)).inst v 0 := by
        rw [Tm.subst_inst _ (Tm.env_lc hE'.closed), Tm.subst_append (hl ▸ hs.2)]
        congr 1; simp [Tm.subst, Tm.env, hl.symm]
      have := ih hE' (Tm.isTele_inst _ r 0 ht) hs' (hr ▸ hvs) (fun w hw => hc w (by simp [Tm.toList, hw]))
      simp only [Tm.len, Ctx.openTele, Tm.toList, List.append_assoc, List.singleton_append] at this ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := this
      exact ⟨h1, h2, h3, h4, by rw [h5, hn]; omega, hext.trans h6⟩
    | nil => simp [Tm.subst] at hv; cases hv
    | _ => simp [Tm.isTele] at ht
  | nil =>
    intro out ht hs hv hc
    cases hv
    have h0 : Γ.openTele tele 0 = (Γ, tele) := by cases tele <;> simp [Ctx.openTele]
    simp only [Tm.len, h0, Tm.toList, List.append_nil]
    exact ⟨hE, trivial, hs, ht, by simp, ⟨[], by simp⟩, fun _ _ h => h, rfl, rfl, rfl, rfl⟩
  | _ => intro out ht hs hv hc; cases hv

theorem VTy.fn_inv {v l t : Tm} {np : Nat} {u : Bool} {hm : List Bool} (h : VTy P v (.fn l np t u hm)) :
    ∃ env Γ gid G j F, v = .clo (.ofList env) gid j ∧ EnvOK P env Γ ∧ P.groups[gid]? = some G ∧
      GroupOK P gid Γ G ∧ G.fns[j]? = some F ∧ (F.type G).subst (Tm.env env) = .fn l np t u hm := by
  cases h with
  | clo hE hG hok hF => exact ⟨_, _, _, _, _, _, rfl, hE, hG, hok, hF, rfl⟩
  | con _ _ _ _ he => cases he

theorem VTy.ty_inv {v idx ls : Tm} {d : Nat} (h : VTy P v (.app (.tyc d ls) idx))
    (hD : ∀ D, P.adts[d]? = some D → D.coercible = false ∧ D.opq = false) (hpl : P.placedD ≠ some d) :
    ∃ c vs sig mid mk me mu, v = .app (.vc d c ls) vs ∧ P.ctor d c = some sig ∧ ls.len = P.lifted d ∧ VTys P ls sig mid ∧
      VTys P vs mid (.bind (.ty mk me mu) (.app (.tyc d ls) idx) .nil) := by
  cases h with
  | con hc hl hm hv he => cases he; exact ⟨_, _, _, _, _, _, _, rfl, hc, hl, hm, hv⟩
  | coer hD' hc => rw [(hD _ hD').1] at hc; cases hc
  | opq hD' ho => rw [(hD _ hD').2] at ho; cases ho
  | placed hq _ => exact (hpl hq).elim
  | world _ hD' ho => rw [(hD _ hD').2] at ho; cases ho

theorem VTy.placed_inv (hP : ProgOK P) {x s T w : Tm} {q : Nat} (hq : P.placedD = some q)
    (h : VTy P x (.app (.tyc q .nil) (.cons s (.cons T (.cons w .nil))))) : x = w ∧ VTy P x T := by
  obtain ⟨D, hD, ho⟩ := hP.placed _ hq
  cases h with
  | placed _ h => exact ⟨rfl, h⟩
  | opq _ _ hne => exact (hne hq).elim
  | con hc _ _ _ he => cases he; simp [Prog.ctor, hD, (hP.opq _ _ hD ho).1] at hc

theorem ProgOK.placed_ne {P : Prog} (hP : ProgOK P) {d : Nat} {D : Adt} (hD : P.adts[d]? = some D) (ho : D.opq = false) :
    P.placedD ≠ some d := fun hq => by
  obtain ⟨D', hD', ho'⟩ := hP.placed _ hq; rw [hD] at hD'; cases hD'; rw [ho] at ho'; cases ho'

theorem VTy.coer_inv (hP : ProgOK P) {v : Tm} {d : Nat} {D : Adt} {sa A a sb B b : Tm} (hD : P.adts[d]? = some D)
    (hc : D.coercible = true) (h : VTy P v (Tm.coer d sa A a sb B b)) :
    (∀ vS, Real P vS a ↔ Real P vS b) ∧ CoerOwn P sa a sb b := by
  generalize hX : Tm.coer d sa A a sb B b = X at h
  cases h with
  | coer _ _ hr ho => simp only [Tm.coer, Tm.ofList, Tm.app.injEq, Tm.tyc.injEq, Tm.cons.injEq] at hX
                      obtain ⟨-, rfl, -, rfl, rfl, -, rfl, -⟩ := hX; exact ⟨hr, ho⟩
  | con hk _ _ _ he =>
    subst he; simp only [Tm.coer, Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX
    simp [Prog.ctor, hD, hP.coer _ _ hD hc] at hk
  | clo => simp [Tm.coer, FnDef.type, Tm.subst] at hX
  | mtbl => simp [Tm.coer, Adt.mtbl] at hX
  | placed => simp [Tm.coer, Tm.ofList] at hX
  | world => simp [Tm.coer, Tm.ofList] at hX
  | opq hD' ho =>
    simp only [Tm.coer, Tm.app.injEq, Tm.tyc.injEq] at hX; obtain ⟨⟨rfl, -⟩, -⟩ := hX
    rw [hD] at hD'; cases hD'; rw [(hP.opq _ _ hD ho).2] at hc; cases hc
  | _ => simp [Tm.coer] at hX

theorem VTy.level_inv {v : Tm} (h : VTy P v .level) : ∃ n, v = .lvl n := by
  cases h with
  | lvl => exact ⟨_, rfl⟩
  | con _ _ _ _ he => cases he

theorem VTy.predates_inv {v A x L : Tm} (h : VTy P v (.predates A x L)) :
    ∃ m, L = .lvl m ∧ ∀ n ∈ x.levels, n < m := by
  cases h with
  | predates h => exact ⟨_, rfl, h⟩
  | con _ _ _ _ he => cases he

theorem VTy.subterm_inv {v A a B b : Tm} (h : VTy P v (.subterm A a B b)) : Tm.PSub a b := by
  cases h with
  | subterm h => exact h
  | con _ _ _ _ he => cases he

theorem closures_get {env : List Tm} {gid : Nat} {G : Group} {j : Nat} {v : Tm}
    (h : (closures env gid G)[j]? = some v) : j < G.fns.length ∧ v = .clo (.ofList env) gid j := by
  simp only [closures, List.getElem?_map] at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.getElem?_eq_some_iff.mp hk
  simp at this; obtain ⟨h1, rfl⟩ := this; exact ⟨h1, rfl⟩

theorem closuresS_get {env : List Tm} {gid : Nat} {G : Group} {k : Nat} {a : Tm}
    (h : (closuresS env gid G)[k]? = some a) :
    ∃ F, G.fns[k]? = some F ∧ a = cval env gid ((closuresS env gid G).take k) F := by
  have hk : k < G.fns.length := by
    have := (getElem?_eq_some_iff.mp h).1; rwa [closuresS_length] at this
  have := (foldl_snoc (cval env gid) G.fns []).2.2 k hk
  simp only [List.length_nil, Nat.zero_add] at this
  rw [← closuresS, h] at this
  exact ⟨_, List.getElem?_eq_getElem hk, Option.some.inj this⟩

theorem Group.deleOK_spec {G : Group} {n j t : Nat} {F : FnDef} (h : G.deleOK P n = true) (hF : G.fns[j]? = some F)
    (ht : F.dele = some t) : t < n + j ∧ (t < n → G.ers.getD t true = false) ∧
      (n ≤ t → ∃ F', G.fns[t - n]? = some F' ∧ F'.er = false) ∧
      delegWalk P t (n + G.fns.length) ((F.tele.ers.take F.np).count false) (F.tele.ers.drop F.np) false
        (symSpread false (F.tele.ers.take F.np)) F.body = true := by
  unfold Group.deleOK at h
  have hm : (F, j) ∈ G.fns.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simpa using hF)
  have := List.all_eq_true.mp h _ hm
  simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, fun hl => by simpa [hl] using h2, fun hl => ?_, h3⟩
  rw [if_neg (by omega)] at h2
  cases hF' : G.fns[t - n]? with
  | none => simp [hF'] at h2
  | some F' => exact ⟨F', rfl, by simpa [hF'] using h2⟩

theorem closuresS_real {gid : Nat} {G : Group} {envS env : List Tm} (hG : P.groups[gid]? = some G)
    (hgh : G.ghost = false) (hd : G.deleOK P env.length = true) (hl : envS.length = env.length)
    (hS : ∀ i, G.ers.getD i true = false → Real P (Tm.env envS i) (Tm.env env i)) :
    ∀ (k : Nat) (a b : Tm) (F : FnDef), G.fns[k]? = some F → F.er = false → (closuresS envS gid G)[k]? = some a →
      (closures env gid G)[k]? = some b → Real P a b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro a b F hF hfe ha hb
  obtain ⟨F', hF', rfl⟩ := closuresS_get ha
  rw [hF] at hF'; cases hF'
  obtain ⟨-, rfl⟩ := closures_get hb
  have hkl : k < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have htk : ((closuresS envS gid G).take k).length = k := by simp [closuresS_length]; omega
  unfold cval
  cases hdl : F.dele with
  | none => simp only; rw [htk]; exact .clo hG hgh hF hfe hdl hl hS
  | some t =>
    simp only
    obtain ⟨h1, h2, h3, -⟩ := Group.deleOK_spec hd hF hdl
    refine .dele hG hgh hF hfe hdl ?_
    by_cases htn : t < env.length
    · have e1 : (envS ++ (closuresS envS gid G).take k).getD t .nil = Tm.env envS t := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left (show t < envS.length by omega)]
      have e2 : Tm.env (env ++ closures env gid G) t = Tm.env env t := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left htn]
      rw [e1, e2]; exact hS t (h2 htn)
    · obtain ⟨F', hF', hfe'⟩ := h3 (by omega)
      have hlt : t - env.length < k := by omega
      have hcl : t - env.length < (closuresS envS gid G).length := by rw [closuresS_length]; omega
      have e1 : (envS ++ (closuresS envS gid G).take k).getD t .nil = (closuresS envS gid G)[t - env.length] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show envS.length ≤ t by omega), hl,
          List.getElem?_take, hlt, List.getElem?_eq_getElem hcl]
      have hcl' : t - env.length < (closures env gid G).length := by simp [closures]; omega
      have e2 : Tm.env (env ++ closures env gid G) t = (closures env gid G)[t - env.length] := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right (show env.length ≤ t by omega),
          List.getElem?_eq_getElem hcl']
      rw [e1, e2]
      exact ih _ hlt _ _ F' hF' hfe' (List.getElem?_eq_getElem hcl) (List.getElem?_eq_getElem hcl')

theorem Group.sidesOK_spec {G : Group} {Γ : Ctx} {j t : Nat} {F : FnDef} (h : G.sidesOK Γ = true)
    (hg : G.ghost = false) (hF : G.fns[j]? = some F) (ht : F.dele = some t) :
    (F.er = false → Γ.deleSide G t = true → F.u = true) ∧ (t < Γ.n → (Γ.fnSide t).isSome) ∧
    (Γ.n ≤ t → ∃ F', G.fns[t - Γ.n]? = some F' ∧ F'.u = false) := by
  unfold Group.sidesOK at h
  simp only [hg, Bool.false_or, List.all_eq_true] at h
  have := h F (List.mem_of_getElem? hF)
  simp only [ht, Option.all_some, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun he hs => by simp_all, fun hl => by simpa [hl] using h2, fun hl => ?_⟩
  rw [if_neg (by omega)] at h2
  cases hF' : G.fns[t - Γ.n]? with
  | none => simp [hF'] at h2
  | some F' => exact ⟨F', rfl, by simpa [hF'] using h2⟩

theorem NoSpine.clo_many {gid j : Nat} {G : Group} {F : FnDef} {e : Tm} (hG : P.groups[gid]? = some G)
    (hF : G.fns[j]? = some F) (hu : F.u = false) : NoSpine P (.clo e gid j) := by
  intro H w u b h
  cases h with
  | clo h _ => simp [Prog.rdU, Prog.fnU, hG, hF, hu] at h
  | dele hG' hF' _ hu' =>
    rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [hu] at hu'; cases hu'

theorem EnvOK.fnSide {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {i : Nat} {u : Bool} (h : Γ.fnSide i = some u) :
    ∃ e gid j G F, Tm.env ρ i = .clo e gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧ F.u = u := by
  unfold Ctx.fnSide at h
  cases hT : Γ.tys[i]? with
  | none => simp [hT] at h
  | some T =>
    rw [hT] at h; simp only [Option.map_some] at h
    obtain ⟨v, -, hv, hvt⟩ := hE.get hT
    rw [← hE.canon] at hvt
    cases hc : Γ.canon T
    case fn l np t' u' hm =>
      rw [hc] at h hvt; simp only [Option.some.injEq] at h; subst h; simp only [Tm.subst] at hvt
      obtain ⟨env, -, gid, G, j, F, rfl, -, hG, -, hF, hty⟩ := hvt.fn_inv
      simp only [FnDef.type, Tm.subst, Tm.fn.injEq] at hty
      exact ⟨_, _, _, _, _, hv, hG, hF, hty.2.2.2.1⟩
    all_goals (rw [hc] at h; simp at h)

theorem NoSpine.side {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {i : Nat} (h : Γ.fnSide i = some false) :
    NoSpine P (Tm.env ρ i) := by
  obtain ⟨e, gid, j, G, F, he, hG, hF, hu⟩ := hE.fnSide h
  rw [he]; exact .clo_many hG hF hu

theorem sideTm_eq {b : Bool} : sideTm b = uniqueTm ↔ b = true := by
  cases b <;> simp [sideTm, sharedTm, uniqueTm]

theorem dele_own {gid j t : Nat} {G : Group} {F : FnDef} {env : List Tm} {st : Bool}
    (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (ht : F.dele = some t)
    (hno : st = false → NoSpine P (Tm.env (env ++ closures env gid G) t)) (hsu : st = true → F.u = true) :
    CoerOwn P (sideTm F.u) (.clo (.ofList env) gid j) (sideTm st) (Tm.env (env ++ closures env gid G) t) := by
  have tl : (Tm.ofList env).toList = env := Tm.toList_ofList env
  have hsp : ∀ {H w u b}, Spine P H w u (.clo (.ofList env) gid j) b →
      F.u = true ∧ Spine P H w u (Tm.env (env ++ closures env gid G) t) b := by
    intro H w u b h
    cases h with
    | clo h _ => simp [Prog.rdU, Prog.fnU, hG, hF, ht] at h
    | dele hG' hF' hd hu h =>
      rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [ht] at hd; cases hd
      rw [tl] at h; exact ⟨hu, h⟩
  refine ⟨fun hg hs => ?_, fun hg hs => ?_, fun hs hg => ?_⟩
  · simp only [sideTm_eq] at hg hs
    have hb : ∀ {H w u b}, Spine P H w u (Tm.env (env ++ closures env gid G) t) b → Spine P H w u (.clo (.ofList env) gid j) b :=
      fun h => .dele hG hF ht hg (by rw [tl]; exact h)
    intro H w u
    refine ⟨fun b => ⟨fun h => (hsp h).2, hb⟩, ⟨fun h => ?_, fun h => .dele hG hF ht hg (by rw [tl]; exact h)⟩⟩
    cases h with
    | clo hn => rw [hn G F hG hF] at ht; cases ht
    | dele hG' hF' hd _ h =>
      rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [ht] at hd; cases hd; rw [tl] at h; exact h
    | free hn => exact .free fun b h => hn b (hb h)
  · simp only [ne_eq, sideTm_eq, Bool.not_eq_true] at hg hs
    exact fun H w u b h => hno hs H w u b (hsp h).2
  · simp only [ne_eq, sideTm_eq, Bool.not_eq_true] at hg hs; exact absurd (hsu hs) (by simpa using hg)

theorem EnvOK.deleSlots {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (k : Nat) (fns : List FnDef) :
    EnvOK P ρ (Ctx.deleSlots k fns Γ) := by
  unfold Ctx.deleSlots
  generalize fns.zipIdx = L
  induction L generalizing Γ with
  | nil => exact hE
  | cons p L ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact hE.withSlot _
    · exact hE

theorem EnvOK.pushFns (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {gid : Nat} {G : Group}
    (hG : P.groups[gid]? = some G) (hok : GroupOK P gid Γ G) :
    EnvOK P (ρ ++ closures ρ gid G) (Γ.pushFns G) := by
  refine EnvOK.deleSlots ?_ _ _
  cases hok with
  | mk hK hl hty hm hb he hg hd hds =>
  have h1 := hE.pushMany (closures ρ gid G) (G.fns.map (FnDef.type G)) (by simp [closures]) fun j v T h1 h2 => by
    obtain ⟨hj, rfl⟩ := closures_get h1
    simp only [List.getElem?_map] at h2
    obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact ⟨.clo hE hG (.mk hK hl hty hm hb he hg hd hds) hF, (tm_sound hP hE (hty j F hF)).2.1, trivial⟩
  refine EnvOK.congr (h1.setDeles _ fun g t sg st hm => ?_) _ rfl rfl rfl rfl rfl
  rcases List.mem_append.mp hm with hm | hm
  · exact hE.dele.append g t sg st hm
  obtain ⟨⟨F, j⟩, hFj, hm⟩ := List.mem_filterMap.mp hm
  simp only at hm
  split at hm
  · cases hm
  rename_i hne
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hne
  obtain ⟨t', ht', hm⟩ := Option.map_eq_some_iff.mp hm
  simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  have hF : G.fns[j]? = some F := by simpa using List.mem_zipIdx_iff_getElem?.mp hFj
  have hjl : j < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have hlen := hE.len
  obtain ⟨hlt, -⟩ := Group.deleOK_spec hd hF ht'
  have hcl : Tm.env (ρ ++ closures ρ gid G) (Γ.n + j) = .clo (.ofList ρ) gid j := by
    simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right, hlen, closures, hjl]
  obtain ⟨hs1, hs2, hs3⟩ := Group.sidesOK_spec hds hne.2 hF ht'
  have hno : Γ.deleSide G t' = false → NoSpine P (Tm.env (ρ ++ closures ρ gid G) t') := fun hst => by
    by_cases hl : t' < Γ.n
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hs2 hl)
      have hd : Γ.deleSide G t' = u := by
        simp only [Ctx.deleSide, Ctx.fnU, Ctx.fnSide] at hu ⊢
        rw [Array.getElem?_append_left (show t' < Γ.tys.size from hl)]; exact congrArg (Option.getD · false) hu
      rw [hd] at hst; subst hst
      rw [env_app_left (by omega)]; exact .side hE hu
    · obtain ⟨F', hF', hu'⟩ := hs3 (by omega)
      have hk : t' - ρ.length < G.fns.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hF').1
      have : Tm.env (ρ ++ closures ρ gid G) t' = .clo (.ofList ρ) gid (t' - ρ.length) := by
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right (show ρ.length ≤ t' by omega), closures, hk]
      rw [this]; exact .clo_many hG (by rw [hlen]; exact hF') hu'
  have hown := dele_own (env := ρ) (st := Γ.deleSide G t') hG hF ht' hno (hs1 hne.1)
  refine ⟨by simp [closures]; omega, by simp [closures]; omega, fun vS => ?_, by rw [hcl]; exact hown⟩
  rw [hcl]
  constructor
  · intro h
    generalize hx : Tm.ofList ρ = x at h
    cases h with
    | clo hG' _ hF' _ hdn => rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [ht'] at hdn; cases hdn
    | dele hG' _ hF' _ hdt hR =>
      rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [ht'] at hdt; cases hdt
      have tl : ∀ l : List Tm, (Tm.ofList l).toList = l := fun l => by induction l <;> simp [Tm.ofList, Tm.toList, *]
      have := congrArg Tm.toList hx
      rw [tl, tl] at this
      subst this; exact hR
    | other _ _ h3 _ => exact absurd rfl (h3 _ _ _)
    | nat he h' =>
      obtain ⟨c, args, hv⟩ := Prog.view_nat (n := by assumption) he
      rw [hv] at h'
      refine .nat he ?_; rw [hv]
      cases h' with
      | dele hG' _ hF' _ hdt hR =>
        rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [ht'] at hdt; cases hdt
        have tl : ∀ l : List Tm, (Tm.ofList l).toList = l := fun l => by induction l <;> simp [Tm.ofList, Tm.toList, *]
        have := congrArg Tm.toList hx
        rw [tl, tl] at this
        subst this; exact hR
      | other _ _ h3 _ => exact absurd rfl (h3 _ _ _)
  · exact fun h => .dele hG hne.2 hF hne.1 ht' h

namespace Tm

theorem levels_static {n : Nat} : ∀ (t : Tm) d, t.static n d → t.levels = [] := by
  intro t; induction t <;> intro d h <;> simp_all [static, levels] <;> grind

theorem levels_subst (f : Nat → Tm) : ∀ (t : Tm), ∀ x ∈ (t.subst f).levels, x ∈ t.levels ∨ ∃ i ∈ t.fvs, x ∈ (f i).levels := by
  intro t; induction t <;> simp_all [subst, levels, fvs] <;> (try (rename_i i; cases f i <;> simp [slotOf, vacant, levels])) <;> grind

theorem levels_toList : ∀ (t : Tm), ∀ v ∈ t.toList, ∀ x ∈ v.levels, x ∈ t.levels := by
  intro t; induction t <;> simp_all [toList, levels] <;> grind

theorem levels_ofList : ∀ (l : List Tm), ∀ x ∈ (ofList l).levels, ∃ v ∈ l, x ∈ v.levels := by
  intro l; induction l <;> simp_all [ofList, levels] <;> grind

theorem tele_one {f : Nat → Tm} {m : Ent} {A : Tm} : ∀ {t : Tm}, t.isTele → t.subst f = .bind m A .nil →
    ∃ A', t = .bind m A' .nil ∧ A'.subst f = A := by
  intro t ht h
  cases t with
  | bind m' A' r =>
    simp only [subst, bind.injEq] at h
    obtain ⟨rfl, rfl, hr⟩ := h
    cases r <;> simp_all [subst, isTele]
  | _ => simp_all [subst, isTele]

theorem levels_ofList_mem : ∀ (l : List Tm), ∀ v ∈ l, ∀ x ∈ v.levels, x ∈ (ofList l).levels := by
  intro l; induction l <;> simp_all [ofList, levels] <;> grind

end Tm

theorem LvlBound.append {ρ vs : List Tm} {cnt : Nat} : LvlBound (ρ ++ vs) cnt ↔ LvlBound ρ cnt ∧ LvlBound vs cnt := by
  simp [LvlBound, or_imp, forall_and]

theorem LvlBound.mono {ρ : List Tm} {cnt cnt' : Nat} (h : LvlBound ρ cnt) (hc : cnt ≤ cnt') : LvlBound ρ cnt' :=
  fun v hv x hx => Nat.lt_of_lt_of_le (h v hv x hx) hc

theorem LvlBound.subst {ρ : List Tm} {cnt n d : Nat} (h : LvlBound ρ cnt) {t : Tm} (ht : t.static n d) :
    ∀ x ∈ (t.subst (Tm.env ρ)).levels, x < cnt := by
  intro x hx
  rcases Tm.levels_subst _ t x hx with hx | ⟨i, _, hx⟩
  · simp [Tm.levels_static t d ht] at hx
  · simp only [Tm.env, List.getD_eq_getElem?_getD] at hx
    cases e : ρ[i]? with
    | none => simp [e, Tm.levels] at hx
    | some v => simp [e] at hx; exact h v (List.mem_of_getElem? e) x hx

theorem headD_getD (xs : List Nat) : xs.headD 0 = xs.getD 0 0 := by cases xs <;> rfl
theorem tail_getD (xs : List Nat) (j : Nat) : xs.tail.getD j 0 = xs.getD (j + 1) 0 := by cases xs <;> simp

theorem lexLt_of : ∀ (i k : Nat) (xs ys : List Nat), i < k → (∀ j < i, xs.getD j 0 = ys.getD j 0) →
    xs.getD i 0 < ys.getD i 0 → lexLt k xs ys = true
  | _, 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | 0, k + 1, xs, ys, _, _, h => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, headD_getD]; exact .inl h
  | i + 1, k + 1, xs, ys, hk, hp, h => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, headD_getD]
    refine .inr ⟨hp 0 (by omega), lexLt_of i k _ _ (by omega) (fun j hj => ?_) ?_⟩
    · rw [tail_getD, tail_getD]; exact hp (j + 1) (by omega)
    · rw [tail_getD, tail_getD]; exact h

def MuOK (μ : Option (List Nat)) (Γ : Ctx) (ρ : List Tm) : Prop :=
  match Γ.cur with
  | none => μ = none
  | some c => ∃ n, ρ[c]? = some (.lvl n) ∧ μ = some (n :: Γ.subs.map fun s => (Tm.env ρ s).size)

theorem MuOK.append {μ : Option (List Nat)} {Γ Γ' : Ctx} {ρ vs : List Tm} (h : MuOK μ Γ ρ) (hw : Γ.WF)
    (hl : ρ.length = Γ.n) (hc : Γ'.cur = Γ.cur) (hs : Γ'.subs = Γ.subs) : MuOK μ Γ' (ρ ++ vs) := by
  unfold MuOK at *; rw [hc, hs]
  split at h
  · exact h
  · rename_i c e
    obtain ⟨n, h1, h2⟩ := h
    refine ⟨n, by rw [List.getElem?_append_left (hl ▸ hw.cur c e)]; exact h1, ?_⟩
    rw [h2]; congr 2
    apply List.map_congr_left; intro s hs'; rw [Tm.env_append (hl ▸ hw.subs s hs')]

theorem markedArgs_subst_tele (f : Nat → Tm) : ∀ (t args : Tm), t.isTele → markedArgs (t.subst f) args = markedArgs t args := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro args h
    cases args with
    | cons a as => simp only [Tm.subst, markedArgs]; rw [ihr as h]
    | _ => simp [Tm.subst, markedArgs]
  | nil => intro _ _; rfl
  | _ => intro _ h; simp [Tm.isTele] at h

theorem markedArgs_subst_args (f : Nat → Tm) : ∀ (t args : Tm), args.isList →
    markedArgs t (args.subst f) = (markedArgs t args).map (Tm.subst f) := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro args h
    cases args with
    | cons a as =>
      simp only [Tm.subst, markedArgs, Tm.isList] at h ⊢
      split <;> simp [ihr as h]
    | nil => rfl
    | _ => simp [Tm.isList] at h
  | _ => intro args _; cases args <;> rfl

theorem marks_subst (f : Nat → Tm) : ∀ (t : Tm) n, t.isTele → marks (t.subst f) n = marks t n := by
  intro t; induction t with
  | bind m A r _ ihr => intro n h; cases n <;> simp_all [marks, Tm.subst, Tm.isTele]
  | nil => intro _ _; rfl
  | _ => intro _ h; simp [Tm.isTele] at h

theorem markedArgs_length : ∀ (t args : Tm), args.isList → (markedArgs t args).length ≤ (marks t args.len).count true := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro args h
    cases args with
    | cons a as =>
      simp only [markedArgs, marks, Tm.len, Tm.isList] at h ⊢
      have := ihr as h
      rcases m with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [Ent.marked] <;> omega
    | _ => simp [markedArgs]
  | _ => intro args _; cases args <;> simp [markedArgs]

theorem markedArgs_mem : ∀ (t args : Tm), ∀ x ∈ markedArgs t args, x ∈ args.toList := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro args x hx
    cases args with
    | cons a as =>
      simp only [markedArgs] at hx; simp only [Tm.toList, List.mem_cons]
      split at hx
      · rcases List.mem_cons.mp hx with h | h
        · exact .inl h
        · exact .inr (ihr as x h)
      · exact .inr (ihr as x hx)
    | _ => simp [markedArgs] at hx
  | _ => intro args x hx; cases args <;> simp [markedArgs] at hx

theorem fields_toList (Γ : Ctx) (m : Nat) : (Γ.fields m).toList = (List.range m).map fun j => .fv (Γ.n + j) := by
  simp [Ctx.fields, Tm.toList_ofList]

theorem fields_isList (Γ : Ctx) (m : Nat) : (Γ.fields m).isList := by
  simp only [Ctx.fields]; generalize (List.range m).map _ = l
  induction l <;> simp_all [Tm.ofList, Tm.isList]

theorem fields_subst {Γ : Ctx} {ρ : List Tm} (vs : List Tm) (hl : ρ.length = Γ.n) :
    (Γ.fields vs.length).subst (Tm.env (ρ ++ vs)) = .ofList vs := by
  rw [← Tm.ofList_toList _ (Tm.isList_subst _ _ (fields_isList Γ _)), Tm.toList_subst _ _ (fields_isList Γ _),
    fields_toList]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [Tm.subst, Tm.env, hl.symm, List.getElem?_append_right, List.getElem?_eq_getElem h2]

def Result (P : Prog) (ρ : List Tm) (cnt : Nat) (rets : Tm) (r : Except String (List Tm × Nat)) : Prop :=
  ∃ vs cnt', r = .ok (vs, cnt') ∧ VTys P (.ofList vs) (rets.subst (Tm.env ρ)) .nil ∧
    LvlBound vs cnt' ∧ cnt ≤ cnt' ∧ ∀ v ∈ vs, v.lc 0

theorem Result.weaken {ρ more : List Tm} {cnt cnt1 : Nat} {rets : Tm} {r : Except String (List Tm × Nat)}
    (h : Result P (ρ ++ more) cnt1 rets r) (hs : rets.static ρ.length 0) (hc : cnt ≤ cnt1) : Result P ρ cnt rets r := by
  obtain ⟨vs, c', e, hv, hb, hle, hlc⟩ := h
  exact ⟨vs, c', e, by rwa [Tm.subst_append hs] at hv, hb, Nat.le_trans hc hle, hlc⟩

theorem EnvOK.pushTele {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {tele : Tm} {outs : List Tm}
    (ov : Option (List Bool))
    (ht : tele.isTele) (hs : tele.static Γ.n 0) (hv : VTys P (.ofList outs) (tele.subst (Tm.env ρ)) .nil)
    (hc : ∀ v ∈ outs, v.lc 0) :
    EnvOK P (ρ ++ outs) (Γ.pushTele tele ov) ∧ (Γ.pushTele tele ov).cur = Γ.cur ∧
      (Γ.pushTele tele ov).subs = Γ.subs ∧ Γ.n ≤ (Γ.pushTele tele ov).n := by
  have hl := hv.len (Tm.isTele_subst _ _ ht)
  rw [Tm.len_subst _ _ (.inl ht)] at hl; simp [Tm.len] at hl
  have := hE.openTele ht hs hv (by simpa [Tm.toList_ofList] using hc)
  rw [Tm.toList_ofList, hl] at this
  obtain ⟨h1, _, _, _, h5, h6⟩ := this
  have hf : ∀ Γ' : Ctx, (Γ.setErs Γ' ov).tys = Γ'.tys ∧ (Γ.setErs Γ' ov).σ = Γ'.σ ∧
      (Γ.setErs Γ' ov).mints = Γ'.mints ∧ (Γ.setErs Γ' ov).cur = Γ'.cur ∧ (Γ.setErs Γ' ov).subs = Γ'.subs ∧
      (Γ.setErs Γ' ov).fixed = Γ'.fixed ∧ (Γ.setErs Γ' ov).deles = Γ'.deles := by
    intro Γ'; cases ov <;> simp [Ctx.setErs]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf (Γ.openTele tele tele.len).1
  refine ⟨h1.congr _ f1 f2 f3 f4 f5 f6 f7 (by cases ov <;> rfl), f4.trans h6.cur, f5.trans h6.subs, ?_⟩
  show Γ.tys.size ≤ (Γ.setErs (Γ.openTele tele tele.len).1 ov).tys.size
  rw [f1]; simp only [Ctx.n] at h5; omega

theorem Tm.ofList_vc_subst (f : Nat → Tm) (d : Nat) (ls : Tm) : ∀ l : List Nat,
    (Tm.ofList (l.map (Tm.vc d · ls))).subst f = Tm.ofList (l.map (Tm.vc d · (ls.subst f)))
  | [] => rfl
  | _ :: l => by simp [Tm.ofList, Tm.subst, Tm.ofList_vc_subst f d ls l]

theorem Tm.ofList_vc_static (n k d : Nat) (ls : Tm) (h : ls.static n k) :
    ∀ l : List Nat, (Tm.ofList (l.map (Tm.vc d · ls))).static n k = true
  | [] => rfl
  | _ :: l => by simp [Tm.ofList, Tm.static, h, Tm.ofList_vc_static n k d ls h l]

theorem fieldsSimple_inst {S : List Nat} (u : Tm) : ∀ (t : Tm) k, fieldsSimple S t = true → fieldsSimple S (t.inst u k) = true := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro k h
    unfold fieldsSimple at h
    split at h
    · rename_i d r' hr
      cases hr
      simp only [Bool.and_eq_true] at h
      have := ihr (k + 1) h.2
      cases r' <;> simp_all [Tm.inst, fieldsSimple]
    · rename_i hr
      cases hr; simp [Tm.inst, fieldsSimple]
    · cases h
  | _ => intro k h; simp [fieldsSimple] at h

theorem Tm.size_mem_toList : ∀ (t w : Tm), w ∈ t.toList → w.size < t.size := by
  intro t; induction t with
  | cons h r _ ihr =>
    intro w hw
    simp only [Tm.toList, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [Tm.size]; omega
    · have := ihr w hw; simp [Tm.size]; omega
  | _ => intro w hw; simp [Tm.toList] at hw

theorem fieldsSimple_bind {S : List Nat} {k : Ent} {A r : Tm} (h : fieldsSimple S (.bind k A r) = true) :
    ∃ m u, k = .ty m false u ∧ (r = .nil ∨ ∃ d, A = .app (.tyc d .nil) .nil ∧ d ∈ S ∧ fieldsSimple S r = true) := by
  unfold fieldsSimple at h
  split at h
  · rename_i hr
    simp only [Tm.bind.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨_, _, rfl, .inr ⟨_, rfl, h.1, h.2⟩⟩
  · rename_i hr; simp only [Tm.bind.injEq] at hr; obtain ⟨rfl, _, rfl⟩ := hr; exact ⟨_, _, rfl, .inl rfl⟩
  · cases h

theorem fields_simple {n : Nat}
    (ih : ∀ (v : Tm), v.size < n → ∀ d vS, d ∈ P.simple → VTy P v (.app (.tyc d .nil) .nil) → Real P vS v → P.unnat vS = v)
    {mk me mu : Bool} {T : Tm} :
    ∀ (vs sig sigR vsS : Tm), fieldsSimple P.simple sig = true → fieldsSimple P.simple sigR = true →
      VTys P vs sig (.bind (.ty mk me mu) T .nil) →
      Reals P vsS vs sigR → (∀ w ∈ vs.toList, w.size < n) → P.unnat vsS = vs := by
  intro vs; induction vs with
  | cons a vs' _ ihv =>
    intro sig sigR vsS hfs hfr hvs hrs hsz
    cases hvs with
    | cons hva hvs' =>
      cases hrs with
      | cons hra hrs' =>
      obtain ⟨m, _, hk, hr⟩ := fieldsSimple_bind hfs
      rcases hr with rfl | ⟨d', rfl, hd', hfs'⟩
      · simp only [Tm.inst] at hvs'; cases hvs'
      obtain ⟨m', _, hk', hr'⟩ := fieldsSimple_bind hfr
      subst hk'
      have e1 := ih a (hsz a (by simp [Tm.toList])) d' _ hd' hva (hra rfl)
      subst e1
      rcases hr' with rfl | ⟨_, _, _, hfr'⟩
      · cases hrs'; rfl
      simp only [Prog.unnat]
      rw [ihv _ _ _ (fieldsSimple_inst _ _ _ hfs') hfr' hvs' hrs' (fun w hw => hsz w (by simp [Tm.toList, hw]))]
    | isCons _ _ => simp [fieldsSimple] at hfs
  | nil => intro sig sigR vsS _ _ _ hrs _; cases hrs; rfl
  | _ => intro sig sigR vsS _ _ hvs; cases hvs

theorem real_simple (hS : P.simpleStep P.simple = P.simple) :
    ∀ n (v : Tm), v.size < n → ∀ d vS, d ∈ P.simple → VTy P v (.app (.tyc d .nil) .nil) → Real P vS v → P.unnat vS = v := by
  intro n; induction n with
  | zero => intro v h; omega
  | succ n ih =>
    intro v hn d vS hd hv hR
    have hd' : d ∈ P.simpleStep P.simple := by rw [hS]; exact hd
    simp only [Prog.simpleStep, List.mem_filter] at hd'
    obtain ⟨_, hD⟩ := hd'
    split at hD
    · rename_i D hDd
      have hco : D.coercible = false := by revert hD; cases D.coercible <;> simp
      have hop : D.opq = false := by revert hD; cases D.opq <;> simp
      obtain ⟨c, vs, sig, mid, mk, me, mu, rfl, hc, hl0, hm, hvs⟩ := hv.ty_inv (fun D' h => by
        rw [hDd] at h; cases h; exact ⟨hco, hop⟩) (fun hq => by simp [hq] at hD)
      cases hm
      simp only [Bool.and_eq_true, List.all_eq_true] at hD
      have hsig : D.ctors[c]? = some sig := by simpa [Prog.ctor, hDd] using hc
      have hfs := hD.2 sig (List.mem_of_getElem? hsig)
      have hnw : P.wrapField d c = none := by
        cases hw : P.wrapField d c with
        | none => rfl
        | some k =>
          have := (Prog.wrapField_spec hw).1
          simp [Prog.isNt, hDd] at this; simp [this] at hD
      obtain ⟨w, hwe, hR, hwn⟩ : ∃ w, P.unnat w = P.unnat vS ∧ Real P w (.app (.vc d c .nil) vs) ∧ ∀ k, w ≠ .nat k := by
        cases vS with
        | nat k =>
          cases hR with
          | nat he h' =>
            obtain ⟨c', a', hv'⟩ := Prog.view_nat (n := k) he
            exact ⟨_, by rw [← hv', Prog.unnat_view he], hv' ▸ h', by simp⟩
          | wrap hw _ => rw [hnw] at hw; cases hw
          | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)
        | _ => exact ⟨_, rfl, hR, by simp⟩
      rw [← hwe]
      cases hR with
      | nat => exact absurd rfl (hwn _)
      | con hc' _ _ hrs =>
        rw [hc] at hc'; cases hc'
        rw [← hl0] at hrs; simp only [Tm.len, Tm.skip] at hrs
        simp only [Prog.unnat]
        congr 1
        exact fields_simple ih _ _ _ _ hfs hfs hvs hrs fun w hw => by
          have := Tm.size_mem_toList vs w hw; simp [Tm.size] at hn; omega
      | wrap hw _ =>
        have := (Prog.wrapField_spec hw).1
        simp [Prog.isNt, hDd] at this; simp [this] at hD
      | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)
    · cases hD

namespace Tm

theorem ers_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).ers = t.ers := by
  intro t; induction t <;> intro k h <;> simp_all [inst, ers, isTele]

theorem ers_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele → (t.subst f).ers = t.ers := by
  intro t; induction t <;> intro h <;> simp_all [subst, ers, isTele]

theorem uAt_inst (u : Tm) : ∀ (t : Tm) k n, t.isTele → (t.inst u k).uAt n = t.uAt n := by
  intro t; induction t <;> intro k n h <;> cases n <;> simp_all [inst, uAt, isTele]

theorem uAt_subst (f : Nat → Tm) : ∀ (t : Tm) n, t.isTele → (t.subst f).uAt n = t.uAt n := by
  intro t; induction t <;> intro n h <;> cases n <;> simp_all [subst, uAt, isTele]

end Tm

theorem ArgsTy.ers {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele →
    out.ers = tele.ers.drop args.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ _ hr, h | .isCons (r := r) _ _ hr, h | .anyCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    rw [hr.ers (Tm.isTele_inst _ _ 0 h), Tm.ers_inst _ _ _ h]; simp [Tm.ers, Tm.len]


theorem Tm.coer_subst (f : Nat → Tm) (d : Nat) (sa A a sb B b : Tm) :
    (Tm.coer d sa A a sb B b).subst f = Tm.coer d (sa.subst f) (A.subst f) (a.subst f) (sb.subst f) (B.subst f) (b.subst f) := rfl

theorem Tm.coer_static {n k d : Nat} {sa A a sb B b : Tm} :
    (Tm.coer d sa A a sb B b).static n k = true ↔ sa.static n k = true ∧ A.static n k = true ∧ a.static n k = true ∧
      sb.static n k = true ∧ B.static n k = true ∧ b.static n k = true := by
  simp [Tm.coer, Tm.ofList, Tm.static, and_assoc]

theorem TmTy.app_isList {Γ : Ctx} {h args T : Tm} (ht : TmTy P Γ (.app h args) T) : args.isList := by
  cases ht with
  | tyApp _ _ ha => exact ha.isList
  | vcApp _ _ ha => exact ha.isList

theorem Tm.toList_getD_subst (f : Nat → Tm) {t : Tm} (h : t.isList) (k : Nat) :
    (t.subst f).toList.getD k .nil = (t.toList.getD k .nil).subst f := by
  rw [Tm.toList_subst _ _ h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases t.toList[k]? <;> rfl

theorem Real.wrap_iff {vS vs ls : Tm} {d c k : Nat} (hw : P.wrapField d c = some k) :
    Real P vS (.app (.vc d c ls) vs) ↔ Real P vS (vs.toList.getD k .nil) := by
  constructor
  · intro h
    refine Real.natInd (fun vS hn h => ?_) _ h
    cases h with
    | nat he _ => exact .nat he (hn _ _ rfl he)
    | con _ _ hw' _ => rw [hw] at hw'; cases hw'
    | wrap hw' hr => rw [hw] at hw'; cases hw'; exact hr
    | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)
  · exact .wrap hw

theorem Reals.congr (ws : Tm) : ∀ {a vs t : Tm}, Reals P a vs t → ws.isList → vs.toList.length = ws.toList.length →
    (∀ j < vs.toList.length, t.ers.getD j true = false → ∀ x, Real P x (vs.toList.getD j .nil) → Real P x (ws.toList.getD j .nil)) →
    Reals P a ws t := by
  induction ws with
  | cons w ws' _ ih =>
    intro a vs t h hw hl hf
    cases h with
    | nil => simp [Tm.toList] at hl
    | cons hr hs =>
      refine .cons (fun hk => by simpa [Tm.toList] using hf 0 (by simp [Tm.toList]) (by simp [Tm.ers, hk]) _ (by simpa [Tm.toList] using hr hk))
        (ih hs (by simpa [Tm.isList] using hw) (by simpa [Tm.toList] using hl) fun j hjl hj x hx => ?_)
      simpa [Tm.toList] using hf (j + 1) (by simpa [Tm.toList] using hjl) (by simpa [Tm.ers] using hj) x (by simpa [Tm.toList] using hx)
  | nil =>
    intro a vs t h _ hl _
    cases h with
    | nil => exact .nil
    | cons => simp [Tm.toList] at hl
  | _ => intro _ _ _ _ hw; simp [Tm.isList] at hw

theorem Real.ctor_congr {d c : Nat} {sig vs ws vS ls : Tm} (hc : P.ctor d c = some sig) (hw : ws.isList)
    (hl : vs.toList.length = ws.toList.length)
    (hf : ∀ j < vs.toList.length, (sig.skip (P.lifted d)).ers.getD j true = false → ∀ x, Real P x (vs.toList.getD j .nil) →
      Real P x (ws.toList.getD j .nil))
    (h : Real P vS (.app (.vc d c ls) vs)) : Real P vS (.app (.vc d c ls) ws) := by
  refine Real.natInd (fun vS hn h => ?_) _ h
  cases h with
  | nat he _ => exact .nat he (hn _ _ rfl he)
  | con hc' hp hw' hr => rw [hc] at hc'; cases hc'; exact .con hc hp hw' (Reals.congr _ hr hw hl hf)
  | wrap hw' hr =>
    obtain ⟨-, -, sig', hc', hk⟩ := Prog.wrapField_spec hw'
    rw [hc] at hc'; cases hc'
    rename_i k
    by_cases hkl : k < vs.toList.length
    · exact .wrap hw' (hf _ hkl (Tm.ntField_spec hk).2.1 _ hr)
    · refine .wrap hw' ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact .other (by simp) (by simp) (by simp) (by simp)
  | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)

theorem Tm.toList_subst_get (f : Nat → Tm) : ∀ (t : Tm) (i : Nat) (x : Tm), t.toList[i]? = some x →
    (t.subst f).toList[i]? = some (x.subst f) := by
  intro t; induction t with
  | cons h r _ ihr => intro i x hx; cases i <;> simp_all [Tm.toList, Tm.subst]
  | _ => intro i x hx; simp [Tm.toList] at hx

theorem VTy.mtbl_inv {v T cs : Tm} {u nt ex : Bool} {ph : List Bool} (h : VTy P v (.mtbl u nt ex ph T cs)) :
    ∃ (d : Nat) (D : Adt) (ls out : Tm), P.adts[d]? = some D ∧ D.coercible = false ∧ D.opq = false ∧ ls.len = D.lifted ∧
      VTys P ls D.params out ∧ D.mtbl d ls = .mtbl u nt ex ph T cs := by
  generalize hX : Tm.mtbl u nt ex ph T cs = X at h
  cases h with
  | mtbl hD hl hv hco hop => exact ⟨_, _, _, _, hD, hco, hop, hl, hv, rfl⟩
  | con _ _ _ _ he => subst he; simp at hX
  | clo => simp [FnDef.type, Tm.subst] at hX
  | coer => simp [Tm.coer] at hX
  | _ => simp at hX

theorem Tm.isTele_peel : ∀ (ls t : Tm), t.isTele → (t.peel ls).isTele := by
  intro ls; induction ls with
  | cons a as _ ih =>
    intro t h; cases t with
    | bind m A r => simp only [Tm.peel]; exact ih _ (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h))
    | _ => simpa [Tm.peel] using h
  | _ => intro t h; cases t <;> simpa [Tm.peel] using h

theorem Tm.static_peel {n : Nat} : ∀ {ls : Tm}, ls.static n 0 → ∀ (t : Tm), t.static n 0 → (t.peel ls).static n 0 := by
  intro ls; induction ls with
  | cons a as _ ih =>
    intro hls t h; simp only [Tm.static, Bool.and_eq_true] at hls
    cases t with
    | bind m A r =>
      simp only [Tm.peel]; simp only [Tm.static, Bool.and_eq_true] at h
      exact ih hls.2 _ (Tm.static_inst hls.1 r 0 h.2)
    | _ => simpa [Tm.peel] using h
  | _ => intro _ t h; cases t <;> simpa [Tm.peel] using h

theorem Tm.peel_subst (f : Nat → Tm) (hf : ∀ i, (f i).lc 0) : ∀ (ls : Tm), ls.isList → ∀ (t : Tm), t.isTele →
    (t.peel ls).subst f = (t.subst f).peel (ls.subst f) := by
  intro ls; induction ls with
  | cons a as _ ih =>
    intro hl t h; simp only [Tm.isList] at hl
    cases t with
    | bind m A r =>
      simp only [Tm.peel, Tm.subst]
      rw [ih hl _ (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h)), Tm.subst_inst f hf a r 0]
    | nil => simp [Tm.peel, Tm.subst]
    | _ => simp [Tm.isTele] at h
  | nil => intro _ t h; cases t <;> simp [Tm.peel, Tm.subst]
  | _ => intro hl; simp [Tm.isList] at hl

theorem Tm.skip_inst (u : Tm) : ∀ (t : Tm) k n, t.isTele →
    ((t.inst u k).skip n).ers = (t.skip n).ers ∧ ((t.inst u k).skip n).len = (t.skip n).len ∧
    ∀ j, ((t.inst u k).skip n).uAt j = (t.skip n).uAt j := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro k n h; simp only [Tm.isTele] at h
    cases n with
    | zero =>
      refine ⟨by simp [Tm.skip, Tm.inst, Tm.ers, ers_inst _ _ _ h], by simp [Tm.skip, Tm.inst, Tm.len, Tm.len_inst _ _ _ h],
        fun j => ?_⟩
      cases j <;> simp [Tm.skip, Tm.inst, Tm.uAt, Tm.uAt_inst _ _ _ _ h]
    | succ n => simpa [Tm.skip, Tm.inst] using ihr (k + 1) n h
  | nil => intro k n _; cases n <;> simp [Tm.inst, Tm.skip]
  | _ => intro k n h; simp [Tm.isTele] at h

theorem VTys.skip : ∀ {vs tele out : Tm}, VTys P vs tele out → tele.isTele →
    (tele.skip vs.len).ers = out.ers ∧ (tele.skip vs.len).len = out.len ∧ ∀ j, (tele.skip vs.len).uAt j = out.uAt j
  | _, _, _, .nil, _ => by simp [Tm.skip, Tm.len]
  | _, _, _, .cons (r := r) _ hr, h | _, _, _, .isCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    obtain ⟨h1, h2, h5⟩ := hr.skip (Tm.isTele_inst _ _ 0 h)
    obtain ⟨h3, h4, h6⟩ := Tm.skip_inst _ r 0 _ h
    simp only [Tm.len, Tm.skip]; exact ⟨h3 ▸ h1, h4 ▸ h2, fun j => (h6 j).symm.trans (h5 j)⟩

theorem Tm.uer_skip : ∀ (t : Tm) (n : Nat), (∀ i, t.uAt i = true → t.ers.getD i true = false) →
    ∀ j, (t.skip n).uAt j = true → (t.skip n).ers.getD j true = false := by
  intro t; induction t <;> intro n h j hu <;> cases n <;> try exact h j hu
  all_goals first
    | (rename_i ih _; exact ih _ (fun i hi => by simpa [Tm.ers] using h (i + 1) (by simpa [Tm.uAt] using hi)) j hu)
    | exact h j hu

theorem uAt_skip (hP : ProgOK P) {d c : Nat} {ls sig0 sig : Tm} {f : Nat → Tm} (hct : P.ctor d c = some sig0)
    (hlf : ls.len = P.lifted d) (hvs0 : VTys P ls sig0 (sig.subst f)) (hst : sig.isTele) :
    ∀ j, (sig0.skip (P.lifted d)).uAt j = sig.uAt j := fun j => by
  obtain ⟨D', hD', hs'⟩ := Option.bind_eq_some_iff.mp hct
  rw [← hlf, (hvs0.skip (hP.ctors _ _ _ _ hD' hs').1.isTele).2.2 j, Tm.uAt_subst _ _ _ hst]

theorem WrapOK.sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {C : Tm} {k : Nat}
    (h : WrapOK P Γ C k) : ∃ d c ls, C.subst (Tm.env ρ) = .vc d c ls ∧ P.wrapField d c = some k := by
  have eqc : ∀ {a b : Tm}, Γ.canon a = Γ.canon b → a.subst (Tm.env ρ) = b.subst (Tm.env ρ) :=
    fun h => by rw [← hE.canon, h, hE.canon]
  cases h with
  | decl hC hw => exact ⟨_, _, _, by rw [← hE.canon, hC]; rfl, hw⟩
  | opened hm hM hc hl hC' he hp hK hk ht hn =>
    rename_i m oe M i C' K sig u ex ph H cs
    obtain ⟨v, _, hv, hvT⟩ := hE.get hM
    rw [← hE.canon M, hc] at hvT; simp only [Tm.subst] at hvT
    obtain ⟨d, D, ls, _, hD, _, _, _, _, he'⟩ := hvT.mtbl_inv
    simp only [Adt.mtbl, Tm.mtbl.injEq] at he'
    obtain ⟨-, hnt, -, hph, -, hcs⟩ := he'
    have hcl := Tm.toList_subst_get (Tm.env ρ) cs i C' hC'
    rw [← hcs, Tm.toList_ofList] at hcl
    have hi : i < D.ctors.length := by simpa using (List.getElem?_eq_some_iff.mp hcl).1
    rw [List.getElem?_map, List.getElem?_range hi] at hcl
    simp only [Option.map_some, Option.some.injEq] at hcl
    have eC : C.subst (Tm.env ρ) = .vc d i ls := (eqc he).trans hcl.symm
    have vk := (tm_sound hP hE hK).1
    rw [← hE.canon K, hk, eC] at vk; simp only [Tm.subst] at vk
    obtain ⟨d', c', ls', sig0, e1, hct, hl, hvs⟩ := vk.vc_inv; cases e1
    refine ⟨d, i, ls, eC, ?_⟩
    have hph' : P.phantom d i = false := by
      rw [← hp, ← hph]; simp [Prog.phantom, hD, hi, List.getD_eq_getElem?_getD]
    have hnt' : P.isNt d = true := by simp [Prog.isNt, hD, hnt]
    have hsig0 : sig0.isTele := by
      obtain ⟨D', hD', hs'⟩ := Option.bind_eq_some_iff.mp hct
      exact (hP.ctors _ _ _ _ hD' hs').1.isTele
    obtain ⟨hk1, hk2⟩ := hvs.skip hsig0
    have hnf : (sig0.skip (P.lifted d)).ntField = sig.ntField := by
      simp only [Tm.ntField, ← hl, hk1, hk2, Tm.ers_subst _ _ ht, Tm.len_subst _ _ (.inl ht)]
    simp [Prog.wrapField, hnt', hph', hct, hnf, hn]

theorem Prog.natOK_spec {d : Nat} (h : P.natOK d = true) :
    P.natD = some d ∧ P.lifted d = 0 ∧ P.isNt d = false ∧ P.phantom d 0 = false ∧ P.phantom d 1 = false ∧
    (∃ m e u, P.ctor d 0 = some (.bind (.ty m e u) (natTy d) .nil)) ∧
    ∃ m1 u1 m2 e2 u2, P.ctor d 1 = some (.bind (.ty m1 false u1) (natTy d) (.bind (.ty m2 e2 u2) (natTy d) .nil)) := by
  unfold Prog.natOK at h
  split at h
  · rename_i D hD
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hn, hl⟩, hnt⟩, h0⟩, h1⟩, hc⟩ := h
    split at hc
    · rename_i m e u z m1 u1 a m2 e2 u2 s hcs
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      refine ⟨hn, by simp [Prog.lifted, hD, hl], by simp [Prog.isNt, hD, hnt], ?_, ?_, ⟨m, e, u, ?_⟩, ⟨m1, u1, m2, e2, u2, ?_⟩⟩
      · simpa [Prog.phantom, hD, List.getD_eq_getElem?_getD] using h0
      · simpa [Prog.phantom, hD, List.getD_eq_getElem?_getD] using h1
      · simp [Prog.ctor, hD, hcs]
      · simp [Prog.ctor, hD, hcs]
    · cases hc
  · cases h

theorem natTm_vty {d : Nat} (h : P.natOK d = true) : ∀ n, VTy P (natTm' d n) (natTy d) := by
  obtain ⟨-, hl, -, -, -, ⟨m, e, u, h0⟩, ⟨m1, u1, m2, e2, u2, h1⟩⟩ := Prog.natOK_spec h
  intro n
  induction n with
  | zero => exact .con h0 (by simp [Tm.len, hl]) .nil .nil rfl
  | succ k ih =>
    refine .con (mk := m2) (me := e2) (mu := u2) h1 (by simp [Tm.len, hl]) .nil (.cons ih ?_) rfl
    simpa [natTy, Tm.inst] using (VTys.nil : VTys P .nil (.bind (.ty m2 e2 u2) (natTy d) .nil) _)

theorem natTm_real {d : Nat} (h : P.natOK d = true) : ∀ n, Real P (.nat n) (natTm' d n) := by
  obtain ⟨hn, hl, hnt, hp0, hp1, ⟨m, e, u, h0⟩, ⟨m1, u1, m2, e2, u2, h1⟩⟩ := Prog.natOK_spec h
  intro n
  induction n with
  | zero => exact .nat hn (by simpa [Prog.view, hn, natTm'] using .con h0 hp0 (Prog.wrapField_none hnt) .nil)
  | succ k ih =>
    refine .nat hn ?_
    simp only [Prog.view, hn, natTm']
    exact .con h1 hp1 (Prog.wrapField_none hnt) (by rw [hl]; exact .cons (fun _ => ih) .nil)

theorem natTm_lc (d : Nat) : ∀ n, (natTm' d n).lc 0 ∧ (natTm' d n).levels = []
  | 0 => by simp [natTm', Tm.lc, Tm.levels]
  | k + 1 => by have := natTm_lc d k; simp [natTm', Tm.lc, Tm.levels, this]

theorem VTy.atom_inv {d : Nat} {D : Adt} {m e u : Bool} (hD : P.adts[d]? = some D)
    (hc : D.ctors = [.bind (.ty m e u) (.app (.tyc d .nil) .nil) .nil]) (hl : D.lifted = 0) (ho : D.opq = false)
    {v : Tm} (h : VTy P v (.app (.tyc d .nil) .nil)) : v = .app (.vc d 0 .nil) .nil := by
  cases h with
  | @con d' c sig ls mid vs mk me mu T idx hct hls hv1 hv2 hT =>
    cases hT
    simp only [Prog.ctor, hD, hc, Option.bind_some] at hct
    cases c with
    | succ c => simp at hct
    | zero =>
      simp at hct; subst hct
      cases hv1
      cases hv2 with
      | nil => rfl
      | cons _ h2 => cases h2
  | opq hD' ho' => rw [hD] at hD'; cases hD'; rw [ho] at ho'; cases ho'
  | world _ hD' ho' => rw [hD] at hD'; cases hD'; rw [ho] at ho'; cases ho'

theorem Ctx.markPd_eq (Γ : Ctx) (m : Mark) (a : Tm) : Γ.markPd m a = { Γ with pd := (Γ.markPd m a).pd } := by
  unfold Ctx.markPd; split <;> rfl

theorem EnvOK.markPd {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (m : Mark) (a : Tm) : EnvOK P ρ (Γ.markPd m a) :=
  hE.congr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (hς := by simp)

theorem Ctx.slotSelf_eq {Γ Γ' : Ctx} {s : Nat} (h : Γ.slotSelf s = some Γ') :
    Γ' = { Γ with σ := Γ'.σ, ς := Γ'.ς } := by
  unfold Ctx.slotSelf at h; simp only [] at h
  split at h
  · cases h; unfold Ctx.withSlot; split <;> rfl
  · split at h
    · cases h; rfl
    · cases h

theorem EnvOK.slotSelf (hP : ProgOK P) {ρ : List Tm} {Γ Γ' : Ctx} (hE : EnvOK P ρ Γ) {s : Nat} {S : Tm}
    (hok : P.slotOK = true) (hs : TmTy P Γ (.fv s) S) (hS : Γ.canon S = .app (.tyc slotD .nil) .nil)
    (h : Γ.slotSelf s = some Γ') : EnvOK P ρ Γ' := by
  obtain ⟨hv, hst, -⟩ := tm_sound hP hE hs
  have hsn : s < Γ.n := by simpa [Tm.static] using hst
  unfold Ctx.slotSelf at h; simp only [] at h
  split at h
  · cases h; exact hE.withSlot _
  · split at h
    · cases h
      obtain ⟨D, m, e, u, hD, hc, hl, -, ho, -⟩ := Tm.slotOK_spec hok
      rw [← hE.canon S, hS] at hv; simp only [Tm.subst] at hv
      have hvac := VTy.atom_inv hD hc hl ho hv
      have hss : (Tm.sfv s).static Γ.n 0 := by simpa [Tm.static] using hsn
      refine hE.withRule hsn (canon_static hE.wf hss) ?_
      rw [hE.canon]; simp only [Tm.subst] at hvac ⊢
      rw [hvac]; rfl
    · cases h

structure Prog.OracleOK (P : Prog) : Prop where
  typed : ∀ k c rd ls vs ls' A, P.requestD = some rd → VTy P (.app (.vc rd c ls) vs) (.app (.tyc rd ls') (.cons A .nil)) →
    VTy P (P.ask k c).2 A ∧ Real P (P.ask k c).1 (P.ask k c).2
  lc : ∀ k c, (P.ask k c).2.lc 0
  levels : ∀ k c, (P.ask k c).2.levels = []
  noClo : ∀ k c, (P.ask k c).2.noClo = true
  sdata : ∀ k c, (P.ask k c).1.sdata = true

theorem VTy.world_inv (hP : ProgOK P) {v : Tm} {w : Nat} (hw : P.worldD = some w)
    (h : VTy P v (.app (.tyc w .nil) .nil)) : ∃ k, v = .wld k := by
  obtain ⟨⟨D, hD, ho⟩, hpl⟩ := hP.world _ hw
  cases h with
  | world => exact ⟨_, rfl⟩
  | con hc _ _ _ he => cases he; simp [Prog.ctor, hD, (hP.opq _ _ hD ho).1] at hc
  | opq _ _ _ hne => exact (hne hw).elim
  | _ => simp_all [FnDef.type, Tm.subst, Adt.mtbl, Tm.coer]

theorem VTy.world_mk (hP : ProgOK P) {w : Nat} (hw : P.worldD = some w) (k : Nat) :
    VTy P (.wld k) (.app (.tyc w .nil) .nil) := by
  obtain ⟨⟨D, hD, ho⟩, hpl⟩ := hP.world _ hw
  exact .world hw hD ho hpl

theorem prim_sound (hP : ProgOK P) (hO : P.OracleOK) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat}
    (hb : LvlBound ρ cnt) {p : Prim} {T : Tm} (h : PrimTy P Γ p T) :
    VTy P (p.eval P ρ) (T.subst (Tm.env ρ)) ∧ T.static Γ.n 0 ∧ (p.eval P ρ).lc 0 ∧ ∀ x ∈ (p.eval P ρ).levels, x < cnt := by
  have hw := hE.wf
  have stat : ∀ {t T : Tm}, TmTy P Γ t T → (Γ.canon T).static Γ.n 0 := fun ht =>
    canon_static hw (tm_sound hP hE ht).2.2
  have sem : ∀ {t T : Tm}, TmTy P Γ t T → VTy P (t.subst (Tm.env ρ)) ((Γ.canon T).subst (Tm.env ρ)) := fun ht => by
    rw [hE.canon]; exact (tm_sound hP hE ht).1
  have eqc : ∀ {a b : Tm}, Γ.canon a = Γ.canon b → a.subst (Tm.env ρ) = b.subst (Tm.env ρ) :=
    fun h => by rw [← hE.canon, h, hE.canon]
  cases h with
  | tm ht | lit ht =>
    obtain ⟨hv, hs, hT⟩ := tm_sound hP hE ht
    exact ⟨hv, hT, lc_of_static hE.closed hs, hb.subst hs⟩
  | @assert _ t T' _ ht hts hS hk he hA =>
    obtain ⟨hv, hs, _⟩ := tm_sound hP hE ht
    have hl := hE.len
    have hAe : T.subst (Tm.env ρ) = T.subst (Γ.fixedEnv P) := Tm.subst_ext T fun i hi => by
      obtain ⟨d, vS, hti, hd, hfx⟩ := hk i hi
      have hi' : i < ρ.length := hl ▸ (getElem?_eq_some_iff.mp hti).1
      have hR := hE.fix.2 i vS hfx
      have hvi := hE.vals i _ _ (List.getElem?_eq_getElem hi') hti
      simp only [Tm.subst] at hvi
      have e1 := real_simple hS _ _ (Nat.lt_succ_self _) d vS hd hvi
        (by simpa [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using hR)
      simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Ctx.fixedEnv, hfx, e1]
    have hlcA : (T.subst (Tm.env ρ)).lc 0 := Tm.lc_subst (Tm.env_lc hE.closed) T 0 Γ.n hA
    rw [Tm.subst_static0 _ t 0 hts, ← he, ← hAe, Tm.subst_lc _ _ 0 hlcA] at hv
    refine ⟨by simpa [Prim.eval] using hv, hA, ?_, ?_⟩
    · have := lc_of_static (ρ := []) (by simp) (n := 0) hts
      rw [Tm.subst_static0 _ t 0 hts] at this; simpa [Prim.eval] using this
    · simp only [Prim.eval]; rw [Tm.levels_static t 0 hts]; simp
  | proveSubterm ha hb' hst =>
    obtain ⟨_, has, hA⟩ := tm_sound hP hE ha
    obtain ⟨_, hbs, hB⟩ := tm_sound hP hE hb'
    have := Tm.psub_subst (Tm.env ρ) (Tm.strictSub_psub _ _ hst)
    rw [hE.canon, hE.canon] at this
    exact ⟨.subterm this, by simp [Tm.static, hA, has, hB, hbs], trivial, by simp [Prim.eval, Tm.levels]⟩
  | provePredates hx hL hX =>
    rename_i x L sl X
    obtain ⟨m, hm, hlt⟩ := hE.chrono L hL
    have hLn := hw.mints L hL
    have hl := hE.len
    have hxn : x < Γ.n := by
      have := hw.tys x X hX
      simpa [Ctx.n] using (Array.getElem?_eq_some_iff.mp hX).1
    have hxl : x < ρ.length := by omega
    have hxv : ρ[x]? = some ρ[x] := List.getElem?_eq_getElem hxl
    refine ⟨?_, ?_, trivial, by simp [Prim.eval, Tm.levels]⟩
    · have e : Tm.env ρ L = .lvl m := by simp [Tm.env, hm]
      rcases hx with hx | ⟨rfl, y, hy, hc⟩
      rotate_left
      · have hv := hE.canon (.fv x)
        rw [hc] at hv; simp only [Tm.subst, Tm.slotOf_lc0 (Tm.env_lc hE.closed y)] at hv
        simp only [Tm.subst, e, Bool.false_eq_true, ite_false, ← hv]
        exact .predates fun n hn => by simp [Tm.vacant, Tm.levels] at hn
      cases sl
      · simp only [Tm.subst, e, Bool.false_eq_true, ite_false]
        exact .predates fun n hn => hlt x hx _ hxv n (by simpa [Tm.env, hxv] using hn)
      · simp only [Tm.subst, e, ite_true, Tm.slotOf_lc0 (Tm.env_lc hE.closed x)]
        exact .predates fun n hn => by simp [Tm.vacant, Tm.levels] at hn
    · cases sl <;> simp [Tm.static, hw.tys _ _ hX] <;> omega
  | predatesTrans hp hq h1 h2 =>
    have v1 := sem hp; have v2 := sem hq
    rw [h1] at v1; rw [h2] at v2
    simp only [Tm.subst] at v1 v2
    obtain ⟨m1, e1, hl1⟩ := v1.predates_inv
    obtain ⟨m2, e2, hl2⟩ := v2.predates_inv
    rw [e1] at hl2
    have s1 := stat hp; have s2 := stat hq; rw [h1] at s1; rw [h2] at s2
    simp only [Tm.static, Bool.and_eq_true] at s1 s2
    refine ⟨?_, by simp [Tm.static, s1.1.1, s1.1.2, s2.2], trivial, by simp [Prim.eval, Tm.levels]⟩
    simp only [Tm.subst, e2]
    exact .predates fun n hn => Nat.lt_trans (hl1 n hn) (hl2 m1 (by simp [Tm.levels]))
  | subtermTrans hp hq h1 h2 =>
    have v1 := sem hp; have v2 := sem hq
    rw [h1] at v1; rw [h2] at v2
    simp only [Tm.subst] at v1 v2
    have s1 := stat hp; have s2 := stat hq; rw [h1] at s1; rw [h2] at s2
    simp only [Tm.static, Bool.and_eq_true] at s1 s2
    exact ⟨.subterm (.trans v1.subterm_inv v2.subterm_inv), by simp [Tm.static, s1, s2], trivial,
      by simp [Prim.eval, Tm.levels]⟩
  | mtblOf hD hl ha hco hop =>
    rename_i d D ls _
    obtain ⟨hvs, hls, -⟩ := args_sound hP hE ha (Tm.static_mono (Nat.zero_le Γ.n) _ (Nat.le_refl 0) (hP.params _ _ hD).2)
    rw [Tm.subst_static0 _ _ 0 (hP.params _ _ hD).2] at hvs
    have hc : (D.mtbl d ls).subst (Tm.env ρ) = D.mtbl d (ls.subst (Tm.env ρ)) := by
      simp only [Adt.mtbl, Tm.subst, Tm.ofList_vc_subst]
    refine ⟨by rw [hc]; exact .mtbl hD (by rw [Tm.len_subst _ _ (.inr ha.isList), hl]) hvs hco hop, ?_, trivial,
      by simp [Prim.eval, Tm.levels]⟩
    simp [Adt.mtbl, Tm.static, Tm.ofList_vc_static _ _ _ _ hls, hls]
  | coerce hp e hD hc ha hbb hb' hT =>
    obtain ⟨hv, hbs, _⟩ := tm_sound hP hE hbb
    have s1 := stat hp; rw [e] at s1
    obtain ⟨_, _, _, _, hBs, _⟩ := Tm.coer_static.mp s1
    refine ⟨?_, hBs, lc_of_static hE.closed hbs, hb.subst hbs⟩
    simp only [Prim.eval]; rw [eqc hT] at hv; exact hv
  | coerRefl hs he hD hc =>
    obtain ⟨_, hss, hSs⟩ := tm_sound hP hE hs
    obtain ⟨_, hes, hEs⟩ := tm_sound hP hE he
    exact ⟨by rw [Tm.coer_subst]; exact .coer hD hc (fun _ => Iff.rfl) (.refl _ _),
      Tm.coer_static.mpr ⟨hss, hEs, hes, hss, hEs, hes⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
  | deleOf hm hg ht hD hc =>
    obtain ⟨h1, h2, h3, h4⟩ := hE.dele _ _ _ _ hm
    have hl := hE.len
    have hw := hE.wf
    exact ⟨by rw [Tm.coer_subst, sideTm_subst, sideTm_subst]; exact .coer hD hc h3 h4,
      Tm.coer_static.mpr ⟨sideTm_static _, hw.tys _ _ hg, by simp [Tm.static]; omega, sideTm_static _, hw.tys _ _ ht,
        by simp [Tm.static]; omega⟩, trivial,
      by simp [Prim.eval, Tm.levels]⟩
  | coerOf hp e hD hc hC hcc =>
    have v := sem hp; rw [e, Tm.coer_subst] at v
    have s1 := stat hp; rw [e] at s1
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tm.coer_static.mp s1
    exact ⟨by rw [Tm.coer_subst]; exact .coer hC hcc (v.coer_inv hP hD hc).1 (v.coer_inv hP hD hc).2,
      Tm.coer_static.mpr ⟨h1, h2, h3, h4, h5, h6⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
  | coerSym hp e hD hc =>
    have v := sem hp; rw [e, Tm.coer_subst] at v
    have s1 := stat hp; rw [e] at s1
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Tm.coer_static.mp s1
    exact ⟨by rw [Tm.coer_subst]; exact .coer hD hc (fun vS => ((v.coer_inv hP hD hc).1 vS).symm) (v.coer_inv hP hD hc).2.symm,
      Tm.coer_static.mpr ⟨h4, h5, h6, h1, h2, h3⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
  | coerShare hp e hD hc =>
    have v := sem hp; rw [e, Tm.coer_subst] at v
    have s1 := stat hp; rw [e] at s1
    obtain ⟨_, h2, h3, _, h5, h6⟩ := Tm.coer_static.mp s1
    exact ⟨by rw [Tm.coer_subst]; exact .coer hD hc (v.coer_inv hP hD hc).1 (.shared _ _),
      Tm.coer_static.mpr ⟨rfl, h2, h3, rfl, h5, h6⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
  | coerTrans hp hq e1 e2 hD hc =>
    have v1 := sem hp; rw [e1, Tm.coer_subst] at v1
    have v2 := sem hq; rw [e2, Tm.coer_subst] at v2
    have s1 := stat hp; rw [e1] at s1
    have s2 := stat hq; rw [e2] at s2
    obtain ⟨h1, h2, h3, _, _, _⟩ := Tm.coer_static.mp s1
    obtain ⟨_, _, _, h4, h5, h6⟩ := Tm.coer_static.mp s2
    have c1 := v1.coer_inv hP hD hc; have c2 := v2.coer_inv hP hD hc
    exact ⟨by rw [Tm.coer_subst]; exact .coer hD hc (fun vS => (c1.1 vS).trans (c2.1 vS)) (c1.2.trans c2.2),
      Tm.coer_static.mpr ⟨h1, h2, h3, h4, h5, h6⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
  | @coerWrap _ s S C args T0 k F dC D K sig src hs ha hwk hf hD hc hCK hCk hst hsrc =>
    obtain ⟨d, c, ls, eC, hw⟩ := hwk.sound hP hE
    obtain ⟨_, hss, _⟩ := tm_sound hP hE hs
    obtain ⟨_, has, hTs⟩ := tm_sound hP hE ha
    obtain ⟨_, hfs, hFs⟩ := tm_sound hP hE hf
    have hl := ha.app_isList
    refine ⟨?_, Tm.coer_static.mpr ⟨by subst hsrc; split; exact hss; rfl, hFs, hfs, hss, hTs, has⟩, trivial,
      by simp [Prim.eval, Tm.levels]⟩
    have vC := sem hCK; rw [hCk] at vC; simp only [Tm.subst] at vC
    obtain ⟨_, _, _, sig0, eC', hct, hlf, hvs0⟩ := vC.vc_inv
    rw [eC] at eC'; cases eC'
    have huAt := uAt_skip hP hct hlf hvs0 hst
    rw [Tm.coer_subst]
    refine .coer hD hc (fun vS => ?_) ?_
    · simp only [Tm.subst]; rw [eC, Real.wrap_iff hw, Tm.toList_getD_subst _ hl]
    · have := CoerOwn.wrap (vs := args.subst (Tm.env ρ)) (ls := ls) hw hct (s.subst (Tm.env ρ))
      rw [huAt] at this
      subst hsrc; simp only [Tm.subst]; rw [eC, ← Tm.toList_getD_subst _ hl]
      split <;> rename_i h <;> simp only [h] at this <;> first | exact this | simpa [sharedTm, Tm.subst] using this
  | coerCtor hs hK hk ht h1 h2 hl hf hD hc =>
    rename_i s S C K sig srcs Ts tgts Tt dC D ps
    obtain ⟨_, hss, _⟩ := tm_sound hP hE hs
    have vC := sem hK
    obtain ⟨_, h1s, hT1⟩ := tm_sound hP hE h1
    obtain ⟨_, h2s, hT2⟩ := tm_sound hP hE h2
    rw [hk] at vC; simp only [Tm.subst] at vC
    obtain ⟨d, c, ls, sig0, eC, hct, hlf, hvs0⟩ := vC.vc_inv
    have l1 := h1.app_isList; have l2 := h2.app_isList
    have hsig0 : sig0.isTele := by
      obtain ⟨D', hD', hs'⟩ := Option.bind_eq_some_iff.mp hct
      exact (hP.ctors _ _ _ _ hD' hs').1.isTele
    have hers : (sig0.skip (P.lifted d)).ers = sig.ers := by
      rw [← hlf, (hvs0.skip hsig0).1]; exact Tm.ers_subst (Tm.env ρ) _ ht
    have hlen : ((srcs.subst (Tm.env ρ)).toList).length = ((tgts.subst (Tm.env ρ)).toList).length := by
      rw [Tm.toList_subst _ _ l1, Tm.toList_subst _ _ l2, List.length_map, List.length_map,
        Tm.len_toList _ l1, Tm.len_toList _ l2, hl]
    have hiff : ∀ j < (srcs.subst (Tm.env ρ)).toList.length, (sig0.skip (P.lifted d)).ers.getD j true = false → ∀ x,
        Real P x ((srcs.subst (Tm.env ρ)).toList.getD j .nil) ↔ Real P x ((tgts.subst (Tm.env ρ)).toList.getD j .nil) := by
      intro j hjl hj x
      rw [hers] at hj
      rw [Tm.toList_subst _ _ l1, List.length_map, Tm.len_toList _ l1] at hjl
      obtain ⟨p, Pt, sa, A, x', sb, B, y', -, hpt, ept, hx, hy, -⟩ := hf j hjl hj
      have v := sem hpt; rw [ept, Tm.coer_subst] at v
      rw [Tm.toList_getD_subst _ l1, Tm.toList_getD_subst _ l2, ← eqc hx, ← eqc hy]
      exact (v.coer_inv hP hD hc).1 x
    refine ⟨?_, Tm.coer_static.mpr ⟨hss, hT1, h1s, hss, hT2, h2s⟩, trivial, by simp [Prim.eval, Tm.levels]⟩
    have huAt := uAt_skip hP hct hlf hvs0 ht
    rw [Tm.coer_subst]
    refine .coer hD hc (fun vS => ?_) ⟨fun hsU _ => ?_, fun h h' => (h' h).elim, fun h h' => (h' h).elim⟩
    · simp only [Tm.subst]; rw [eC]
      exact ⟨Real.ctor_congr hct (Tm.isList_subst _ _ l2) hlen fun j hjl hj x => (hiff j hjl hj x).mp,
        Real.ctor_congr hct (Tm.isList_subst _ _ l1) hlen.symm fun j hjl hj x => (hiff j (hlen ▸ hjl) hj x).mpr⟩
    · simp only [Tm.subst]; rw [eC]
      refine Twin.ctor hct hlen fun j v1 v2 hu e1 e2 => ?_
      have hj := Tm.uer_skip _ _ (hP.uer _ _ _ hct) j hu
      rw [hers] at hj; rw [huAt] at hu
      have hjl : j < srcs.len := by
        have := (List.getElem?_eq_some_iff.mp e1).1
        rwa [Tm.toList_subst _ _ l1, List.length_map, Tm.len_toList _ l1] at this
      obtain ⟨p, Pt, sa, A, x', sb, B, y', -, hpt, ept, hx, hy, hsd⟩ := hf j hjl hj
      rw [if_pos hu] at hsd
      have v := sem hpt; rw [ept, Tm.coer_subst] at v
      have := (v.coer_inv hP hD hc).2
      rw [eqc hsd.1, eqc hsd.2, eqc hx, eqc hy, ← Tm.toList_getD_subst _ l1, ← Tm.toList_getD_subst _ l2,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, e1, e2] at this
      exact this.1 hsU hsU
  | @placedSlot d D q E m1 e1 u1 m2 e2 u2 m3 e3 u3 _ a A' b B' m e u hD hc hl ho hE' hc' hl' ha hA hb hB _ =>
    have va := sem ha; rw [hA] at va; simp only [Tm.subst] at va
    have vb := sem hb; rw [hB] at vb; simp only [Tm.subst] at vb
    have ea := VTy.atom_inv hD hc hl ho va
    have eb := VTy.atom_inv hD hc hl ho vb
    obtain ⟨-, has, -⟩ := tm_sound hP hE ha
    obtain ⟨-, hbs, -⟩ := tm_sound hP hE hb
    have hct : P.ctor q 0 = some (eqSig q (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)) := by simp [Prog.ctor, hE', hc']
    refine ⟨?_, by simp [Tm.static, has, hbs], by simp [Prim.eval, Tm.lc, ea], by simp [Prim.eval, Tm.levels, ea]⟩
    rw [ea] at va
    simp only [Prim.eval, Tm.subst, ea, eb]
    refine .con (mk := m3) (me := e3) (mu := u3) hct (by simp [Tm.len, Prog.lifted, hE', hl']) .nil ?_ rfl
    exact .cons .univ (.cons (by simpa [Tm.inst] using va) (by simp [Tm.inst]; exact .nil))
  | num h =>
    rename_i d n
    exact ⟨by simpa [Prim.eval, natTy, Tm.subst] using natTm_vty h n, by simp [natTy, Tm.static], (natTm_lc d n).1,
      by simp [Prim.eval, (natTm_lc d n).2]⟩
  | wNext hwd hw hW =>
    have vw := sem hw; rw [hW] at vw; simp only [Tm.subst] at vw
    obtain ⟨k, hk⟩ := vw.world_inv hP hwd
    refine ⟨?_, by simp [Tm.static], by simp [Prim.eval, hk, Tm.lc, Tm.wnext], by simp [Prim.eval, hk, Tm.levels, Tm.wnext]⟩
    simp only [Prim.eval, hk, Tm.subst, Tm.wnext]; exact VTy.world_mk hP hwd _
  | wAsk hwd hrd hw hW hr hR =>
    have vw := sem hw; rw [hW] at vw; simp only [Tm.subst] at vw
    obtain ⟨k, hk⟩ := vw.world_inv hP hwd
    have vr := sem hr; rw [hR] at vr; simp only [Tm.subst] at vr
    obtain ⟨⟨D, hD, hop, hco, -⟩, hpl, -⟩ := hP.request _ hrd
    have vr' := vr
    obtain ⟨c, vs, -, -, -, -, -, he, -⟩ := vr.ty_inv (fun D' h => by rw [hD] at h; cases h; exact ⟨hco, hop⟩) hpl
    rw [he] at vr'
    obtain ⟨h1, -⟩ := hO.typed k c _ _ _ _ _ hrd vr'
    have h3 := hO.lc k c
    have h4 := hO.levels k c
    have hs := stat hr; rw [hR] at hs; simp only [Tm.static, Bool.and_eq_true] at hs
    refine ⟨?_, hs.2.1, ?_, ?_⟩ <;> simp only [Prim.eval, hk, he, Prog.answer]
    · exact h1
    · exact h3
    · simp [h4]
  | axm hA _ hc hD ho hpl hwo =>
    obtain ⟨_, hAs, _⟩ := tm_sound hP hE hA
    refine ⟨?_, hAs, trivial, by simp [Prim.eval, Tm.levels]⟩
    rw [← hE.canon, hc]; exact .opq hD ho hpl hwo
  | place hq ha hAB hB hs =>
    obtain ⟨-, has, -⟩ := tm_sound hP hE ha
    have v := sem ha; rw [hAB, hE.canon] at v
    refine ⟨?_, by simp [Tm.static, hs, hB, has], lc_of_static hE.closed has, hb.subst has⟩
    simp only [Prim.eval, Tm.subst]; exact .placed hq v
  | unplace hq ha hA hv =>
    obtain ⟨-, has, -⟩ := tm_sound hP hE ha
    have v := sem ha; rw [hA] at v; simp only [Tm.subst] at v
    have st := stat ha; rw [hA] at st; simp [Tm.static] at st
    exact ⟨by simpa [Prim.eval] using (VTy.placed_inv hP hq v).2, st.2.1, lc_of_static hE.closed has, hb.subst has⟩
  | @placedEq q e E m1 e1 u1 m2 e2 u2 m3 e3 u3 _ C U s B w a A b B' hq hE' hc' hl' hC hCc ha hA hbT hB =>
    obtain ⟨-, has, -⟩ := tm_sound hP hE ha
    obtain ⟨-, hbs, -⟩ := tm_sound hP hE hbT
    obtain ⟨-, hCs, -⟩ := tm_sound hP hE hC
    have va := sem ha; rw [hA] at va
    have vb := sem hbT; rw [hB, hCc] at vb; simp only [Tm.subst] at vb
    have va' := va; rw [hCc] at va'; simp only [Tm.subst] at va'
    have ea := (VTy.placed_inv hP hq va').1
    have eb := (VTy.placed_inv hP hq vb).1
    rw [hE.canon] at va
    refine ⟨?_, by simp [Tm.static, has, hbs, hCs], by simp [Prim.eval, Tm.lc, lc_of_static hE.closed has,
      lc_of_static hE.closed hCs], by
      intro x hx; simp [Prim.eval, Tm.levels] at hx
      rcases hx with h | h
      · exact hb.subst hCs x h
      · exact hb.subst has x h⟩
    have hct : P.ctor e 0 = some (eqSig e (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)) := by simp [Prog.ctor, hE', hc']
    simp only [Prim.eval, Tm.subst]; rw [eb, ← ea]
    refine .con (mk := m3) (me := e3) (mu := u3) hct (by simp [Tm.len, Prog.lifted, hE', hl']) .nil ?_ rfl
    have hCl : ∀ (u : Tm) k, (C.subst (Tm.env ρ)).inst u k = C.subst (Tm.env ρ) := fun u k =>
      Tm.inst_lc _ 0 k (lc_of_static hE.closed hCs) (Nat.zero_le k)
    have hal : ∀ (u : Tm) k, (a.subst (Tm.env ρ)).inst u k = a.subst (Tm.env ρ) := fun u k =>
      Tm.inst_lc _ 0 k (lc_of_static hE.closed has) (Nat.zero_le k)
    exact .cons .univ (.cons (by simpa [Tm.inst] using va) (by simp [Tm.inst, hCl, hal]; exact .nil))
  | predatesSubterm hp hq h1 h2 =>
    have v1 := sem hp; have v2 := sem hq
    rw [h1] at v1; rw [h2] at v2
    simp only [Tm.subst] at v1 v2
    obtain ⟨m, e, hl⟩ := v1.predates_inv
    have hs := v2.subterm_inv
    have s1 := stat hp; have s2 := stat hq; rw [h1] at s1; rw [h2] at s2
    simp only [Tm.static, Bool.and_eq_true] at s1 s2
    refine ⟨?_, by simp [Tm.static, s1, s2], trivial, by simp [Prim.eval, Tm.levels]⟩
    simp only [Tm.subst, e]
    exact .predates fun n hn => hl n (Tm.psub_levels hs n hn)

theorem EnvOK.pushPrim (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {p : Prim} {T v : Tm}
    {er : Bool} (hp : PrimTy P Γ p T) (hv : VTy P v (T.subst (Tm.env ρ))) (hT : T.static Γ.n 0) (hc : v.lc 0)
    (he : v = p.eval P ρ) :
    EnvOK P (ρ ++ [v]) (Γ.pushPrim P T er p) ∧ (Γ.pushPrim P T er p).cur = Γ.cur ∧
      (Γ.pushPrim P T er p).subs = Γ.subs ∧ (Γ.pushPrim P T er p).n = Γ.n + 1 := by
  have hn0 : (Γ.pushPrim0 T er p).n = Γ.n + 1 := by cases p <;> simp [Ctx.pushPrim0, Ctx.withRule, Ctx.push, Ctx.n]
  suffices h0 : EnvOK P (ρ ++ [v]) (Γ.pushPrim0 T er p) by
    have h0' : EnvOK P (ρ ++ [v]) ({ Γ.pushPrim0 T er p with pd := none } : Ctx) := h0.congr _ rfl rfl rfl rfl rfl
    refine ⟨h0'.slotIf _ _, ?_, ?_,
      by rw [Ctx.pushPrim, Ctx.slotIf_n]; exact hn0⟩ <;>
      cases p <;> simp [Ctx.pushPrim, Ctx.pushPrim0, Ctx.pushPrim0, Ctx.withRule, Ctx.push]
  have h1 := hE.push hv hT hc (e := er)
  cases hp with
  | tm ht =>
    have hl := hE.len
    have hs := canon_static hE.wf (tm_sound hP hE ht).2.1
    refine h1.withRule (by simp [Ctx.push, Ctx.n]) (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_
    rw [Tm.subst_append (hl ▸ hs), hE.canon, he]
    simp [Tm.env, hl, Prim.eval]
  | coerce _ _ _ _ _ ht =>
    have hl := hE.len
    have hs := canon_static hE.wf (tm_sound hP hE ht).2.1
    refine h1.withRule (by simp [Ctx.push, Ctx.n]) (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_
    rw [Tm.subst_append (hl ▸ hs), hE.canon, he]
    simp [Tm.env, hl, Prim.eval]
  | @unplace q _ a A s B w v hq ha hA hv =>
    have hl := hE.len
    have st := canon_static hE.wf (tm_sound hP hE ha).2.2; rw [hA] at st
    simp [Tm.static] at st
    have hs : (Γ.canon _).static Γ.n 0 := hv ▸ st.2.2
    refine h1.withRule (by simp [Ctx.push, Ctx.n]) (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_
    have v0 := (tm_sound hP hE ha).1; rw [← hE.canon A, hA] at v0; simp only [Tm.subst] at v0
    rw [Tm.subst_append (hl ▸ hs), he, hv]
    simp [Tm.env, hl, Prim.eval, (VTy.placed_inv hP hq v0).1]
  | _ => exact h1

theorem dec_same {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {μ : Option (List Nat)} (hm : MuOK μ Γ ρ)
    {l t args a : Tm} {c i s n1 : Nat} (hal : args.isList) (hl : l.subst (Tm.env ρ) = .lvl n1)
    (hk : (marks t args.len).count true ≤ P.k) (hc : Γ.cur = some c) (hl' : Γ.canon l = Γ.canon (.fv c))
    (hai : (markedArgs t args)[i]? = some a) (hsi : Γ.subs[i]? = some s)
    (hpre : ∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
      Γ.canon a' = Γ.canon (.fv s'))
    (hps : Tm.PSub (a.subst (Tm.env ρ)) ((Tm.fv s).subst (Tm.env ρ))) :
    muLt P.k (some (n1 :: (markedArgs t (args.subst (Tm.env ρ))).map Tm.size)) μ = true := by
  have eqc : ∀ {a b : Tm}, Γ.canon a = Γ.canon b → a.subst (Tm.env ρ) = b.subst (Tm.env ρ) :=
    fun h => by rw [← hE.canon, h, hE.canon]
  unfold MuOK at hm
  rw [hc] at hm; obtain ⟨lam, hlam, rfl⟩ := hm
  rw [eqc hl'] at hl; simp [Tm.subst, Tm.env, hlam] at hl; subst hl
  have hi : i < (markedArgs t args).length := (List.getElem?_eq_some_iff.mp hai).1
  have hik : i < P.k := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi (markedArgs_length t args hal)) hk
  simp only [muLt, markedArgs_subst_args _ t args hal, List.map_map]
  refine lexLt_of (i + 1) _ _ _ (by omega) (fun j hj => ?_) ?_
  · cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getD_eq_getElem?_getD]
      have hj' : j < i := by omega
      cases ea : (markedArgs t args)[j]? with
      | none => have := List.getElem?_eq_none_iff.mp ea; omega
      | some a' =>
        cases es : Γ.subs[j]? with
        | none =>
          have := List.getElem?_eq_none_iff.mp es
          have := (List.getElem?_eq_some_iff.mp hsi).1; omega
        | some s' =>
          have := hpre j hj' a' s' ea es
          simp [List.getElem?_cons_succ, List.getElem?_map, ea, es, eqc this, Tm.subst]
  · simp only [List.getD_eq_getElem?_getD]
    simpa [List.getElem?_cons_succ, List.getElem?_map, hai, hsi, Tm.subst] using Tm.psub_size hps

theorem dec_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {μ : Option (List Nat)}
    (hm : MuOK μ Γ ρ) {dec : Dec} {l t args : Tm} (hd : DecOK P Γ dec l t args) (hal : args.isList)
    {n1 : Nat} (hl : l.subst (Tm.env ρ) = .lvl n1) (hk : (marks t args.len).count true ≤ P.k) :
    muLt P.k (some (n1 :: (markedArgs t (args.subst (Tm.env ρ))).map Tm.size)) μ = true := by
  have sem : ∀ {p Pt : Tm}, TmTy P Γ p Pt → VTy P (p.subst (Tm.env ρ)) ((Γ.canon Pt).subst (Tm.env ρ)) :=
    fun hp => by rw [hE.canon]; exact (tm_sound hP hE hp).1
  have eqc : ∀ {a b : Tm}, Γ.canon a = Γ.canon b → a.subst (Tm.env ρ) = b.subst (Tm.env ρ) :=
    fun h => by rw [← hE.canon, h, hE.canon]
  unfold MuOK at hm
  cases hd with
  | top hc => rw [hc] at hm; rw [hm]; rfl
  | lower hc hp hP' hx hL =>
    rw [hc] at hm; obtain ⟨lam, hlam, rfl⟩ := hm
    have v := sem hp; rw [hP'] at v; simp only [Tm.subst] at v
    obtain ⟨m, e, hlt⟩ := v.predates_inv
    rw [eqc hL] at e; simp [Tm.subst, Tm.env, hlam] at e
    rw [eqc hx, hl] at hlt
    have := hlt n1 (by simp [Tm.levels])
    simp only [muLt]
    exact lexLt_of 0 _ _ _ (by omega) (fun _ h => absurd h (Nat.not_lt_zero _)) (by simp; omega)
  | same hc hl' _ hai hsi hpre hp hP' h0 h1 =>
    have v := sem hp; rw [hP'] at v; simp only [Tm.subst] at v
    have hps := v.subterm_inv
    rw [eqc h0, eqc h1] at hps
    exact dec_same hE (by unfold MuOK; exact hm) hal hl hk hc hl' hai hsi hpre hps
  | autoSub hc hl' hai hsi hpre hst _ =>
    have hps := Tm.psub_subst (Tm.env ρ) (Tm.strictSub_psub _ _ hst)
    rw [hE.canon, hE.canon] at hps
    exact dec_same hE (by unfold MuOK; exact hm) hal hl hk hc hl' hai hsi hpre hps
  | autoPred hc hx hxc hcm _ =>
    rename_i c x _
    rw [hc] at hm; obtain ⟨lam, hlam, rfl⟩ := hm
    obtain ⟨m, hmc, hlt⟩ := hE.chrono c hcm
    rw [hlam] at hmc; cases hmc
    have hxl : x < ρ.length := by rw [hE.len]; have := hE.wf.cur c hc; omega
    have e := hE.canon l; rw [hx, hl] at e; simp only [Tm.subst, Tm.env] at e
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxl, Option.getD_some] at e
    have := hlt x hxc _ (List.getElem?_eq_getElem hxl) n1 (by rw [e]; simp [Tm.levels])
    simp only [muLt]
    exact lexLt_of 0 _ _ _ (by omega) (fun _ h => absurd h (Nat.not_lt_zero _)) (by simp; omega)

theorem fv_filterMap_env (ρ : List Tm) (g : Tm → Nat) : ∀ (L : List Tm), (∀ x ∈ L, ∃ i, x = .fv i) →
    (L.filterMap Tm.fvIdx).map (fun s => g (Tm.env ρ s)) = (L.map (Tm.subst (Tm.env ρ))).map g
  | [], _ => rfl
  | x :: L, h => by
    obtain ⟨i, rfl⟩ := h x (by simp)
    simp [Tm.subst, Tm.fvIdx, fv_filterMap_env ρ g L fun y hy => h y (by simp [hy])]


theorem Real.nil' (vS : Tm) : Real P vS .nil := .other (by simp) (by simp) (by simp) (by simp)

theorem SimEnv.extend {er er' : Nat → Bool} {ρS ρ vsS vs : List Tm} (h : SimEnv P er ρS ρ)
    (hl : vsS.length = vs.length) (hlo : ∀ i < ρ.length, er' i = er i)
    (hnew : ∀ k a b, vsS[k]? = some a → vs[k]? = some b → er' (ρ.length + k) = false → Real P a b) :
    SimEnv P er' (ρS ++ vsS) (ρ ++ vs) := by
  refine ⟨by simp [h.1, hl], fun i hi => ?_⟩
  by_cases h1 : i < ρ.length
  · rw [Tm.env_append h1, Tm.env_append (by rw [h.1]; exact h1)]
    exact h.2 i (by rw [← hlo i h1]; exact hi)
  · by_cases h2 : i < ρ.length + vs.length
    · obtain ⟨k, rfl⟩ : ∃ k, i = ρ.length + k := ⟨i - ρ.length, by omega⟩
      have hk : k < vs.length := by omega
      refine hnew k _ _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hk) hi |> fun r => ?_
      simpa [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right, h.1, hk, hl] using r
    · have e1 : Tm.env (ρ ++ vs) i = .nil := by
        have : (ρ ++ vs).length ≤ i := by simp; omega
        simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
      rw [e1]; exact Real.nil' _

theorem rtArgs_subst {Γ : Ctx} (f : Nat → Tm) : ∀ (args sig : Tm), rtArgs P Γ args sig = true →
    rtArgs P Γ args (sig.subst f) = true
  | .nil, _, _ => by simp [rtArgs]
  | .cons a as, .bind k _ r, h => by
    simp only [rtArgs, Tm.subst, Bool.and_eq_true] at h ⊢; exact ⟨h.1, rtArgs_subst f as r h.2⟩
  | .cons .., .nil, h | .cons .., .fv _, h | .cons .., .bv _, h | .cons .., .cons .., h | .cons .., .app .., h
  | .cons .., .tyc .., h | .cons .., .vc .., h | .cons .., .tyCtor _, h | .cons .., .valCtor _, h
  | .cons .., .univ, h | .cons .., .level, h | .cons .., .predates .., h | .cons .., .subterm .., h
  | .cons .., .fn .., h | .cons .., .lvl _, h | .cons .., .tok, h | .cons .., .clo .., h | .cons .., .nat _, h => by
    simp [rtArgs] at h
  | .fv _, _, h | .bv _, _, h | .bind .., _, h | .app .., _, h | .tyc .., _, h | .vc .., _, h | .tyCtor _, _, h
  | .valCtor _, _, h | .univ, _, h | .level, _, h | .predates .., _, h | .subterm .., _, h | .fn .., _, h
  | .lvl _, _, h | .tok, _, h | .clo .., _, h | .nat _, _, h => by simp [rtArgs] at h

theorem Real.vc_inv {vS ls : Tm} {d c : Nat} (h : Real P vS (.vc d c ls)) : vS = .vc d c .nil ∧ P.phantom d c = false := by
  cases h with
  | vc h => exact ⟨rfl, h⟩
  | other _ h2 _ _ => exact absurd rfl (h2 _ _ _)
  | nat he h' =>
    obtain ⟨_, _, hv⟩ := Prog.view_nat (n := _) he; rw [hv] at h'
    cases h' with | other _ h2 _ _ => exact absurd rfl (h2 _ _ _)

theorem Reals.retele : ∀ {a b t t' : Tm}, Reals P a b t → t.ers = t'.ers → Reals P a b t'
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, t', .cons hr hs, he => by
    cases t' with
    | bind k' A' r' =>
      simp only [Tm.ers, List.cons.injEq] at he
      exact .cons (fun hk => hr (he.1 ▸ hk)) (hs.retele he.2)
    | _ => simp [Tm.ers] at he

theorem Reals.getD {a b t : Tm} : Reals P a b t → ∀ k, t.ers.getD k true = false →
    Real P (a.toList.getD k .nil) (b.toList.getD k .nil)
  | .nil, _, _ => Real.nil' _
  | .cons hr _, 0, he => by simpa [Tm.toList] using hr (by simpa [Tm.ers] using he)
  | .cons _ hs, k + 1, he => by simpa [Tm.toList] using hs.getD k (by simpa [Tm.ers] using he)

theorem Prog.subUArgs_subst (f : Nat → Tm) : ∀ (ts : Tm), ts.isList →
    P.subUArgs f ts = .ofList (ts.toList.map (P.subU f)) := by
  intro ts; induction ts <;> intro h <;> simp_all [Tm.isList, Tm.subst, Prog.subUArgs, Tm.toList, Tm.ofList]

theorem Real.ofArgs {d c : Nat} {sig argsS args ls : Tm} (hc : P.ctor d c = some sig) (hp : P.phantom d c = false)
    (hr : Reals P argsS args (sig.skip (P.lifted d))) :
    Real P (match P.wrapField d c with
      | some k => argsS.toList.getD k .nil
      | none => P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) argsS))) (.app (.vc d c ls) args) := by
  cases hw : P.wrapField d c with
  | none =>
    have : P.ctorErs d c = (sig.skip (P.lifted d)).ers := by simp [Prog.ctorErs, hc]
    rw [this]; exact Real.norm (.con hc hp hw hr.mask)
  | some k =>
    obtain ⟨_, _, sig', hc', hk⟩ := Prog.wrapField_spec hw
    rw [hc] at hc'; cases hc'
    exact .wrap hw (hr.getD k (Tm.ntField_spec hk).2.1)

mutual
theorem rt_real (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ (t : Tm), rt P Γ t = true → Real P (P.sub ρS t) (t.subst (Tm.env ρ))
  | .fv i, h => by simp only [rt, Bool.not_eq_eq_eq_not, Bool.not_true] at h; exact hS.2 i h
  | .sfv i, h => by
    simp only [rt, Bool.and_eq_true] at h
    obtain ⟨D, m, e, u, hD, hc, -, hn, -, hp⟩ := Tm.slotOK_spec h.2
    have hct : P.ctor slotD 0 = some (.bind (.ty m e u) (.app (.tyc slotD .nil) .nil) .nil) := by
      simp [Prog.ctor, hD, hc]
    have hw : P.wrapField slotD 0 = none := by simp [Prog.wrapField, Prog.isNt, hD, hn]
    simp only [Prog.sub, Prog.subU, Tm.subst]; rw [Tm.slotOf_lc0 (Tm.env_lc hE.closed i)]
    exact .con hct hp hw .nil
  | .app hd args, h => by
    cases hd with
    | vc d c ls =>
      simp only [rt] at h
      split at h
      · rename_i sig hc
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        simp only [Prog.sub, Prog.subU, Tm.subst]
        exact Real.ofArgs hc h.1.1 (rtArgs_reals hP hE hS args _ h.2)
      · simp at h
    | fv i =>
      simp only [rt] at h
      split at h
      · rename_i sig heq
        simp only [Option.map_eq_some_iff] at heq
        obtain ⟨T, hT, hcT⟩ := heq
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        obtain ⟨v, -, hev, hv⟩ := hE.get hT
        rw [← hE.canon, hcT] at hv; simp only [Tm.subst] at hv
        obtain ⟨d, c, ls, sig0, rfl, hc, hl, hvs⟩ := hv.vc_inv
        have hR := hS.2 i h.1; rw [hev] at hR
        simp only [Prog.sub, Prog.subU, Tm.subst]; rw [hev, hR.vc_inv.1]
        have hsig0 : sig0.isTele := by
          obtain ⟨D', hD', hs'⟩ := Option.bind_eq_some_iff.mp hc
          exact (hP.ctors _ _ _ _ hD' hs').1.isTele
        exact Real.ofArgs hc hR.vc_inv.2 ((rtArgs_reals hP hE hS args _ (rtArgs_subst _ args sig h.2)).retele
          (by rw [← hl, (hvs.skip hsig0).1]))
      · simp at h
    | _ => simp [rt] at h
  | .vc _ _ _, h => by simp only [Prog.sub, Prog.subU, Tm.subst]; exact .vc (by simpa [rt] using h)
  | .tyc .., h | .tyCtor _, h | .valCtor _, h | .univ, h | .level, h | .predates .., h | .subterm .., h
  | .fn .., h | .nil, h | .bv _, h | .cons .., h | .bind .., h | .lvl _, h | .tok, h | .clo .., h | .nat _, h => by
    simp [rt] at h

theorem rtArgs_reals (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ (args tele : Tm), rtArgs P Γ args tele = true →
      Reals P (P.subUArgs (Tm.env ρS) args) (args.subst (Tm.env ρ)) tele
  | .nil, _, _ => by simp only [Tm.subst, Prog.subUArgs]; exact .nil
  | .cons a as, .bind k _ r, h => by
    simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
    simp only [Tm.subst, Prog.subUArgs]
    exact .cons (fun hk => rt_real hP hE hS a (by simpa [hk] using h.1)) (rtArgs_reals hP hE hS as r h.2)
  | .cons .., .nil, h | .cons .., .fv _, h | .cons .., .bv _, h | .cons .., .cons .., h | .cons .., .app .., h
  | .cons .., .tyc .., h | .cons .., .vc .., h | .cons .., .tyCtor _, h | .cons .., .valCtor _, h
  | .cons .., .univ, h | .cons .., .level, h | .cons .., .predates .., h | .cons .., .subterm .., h
  | .cons .., .fn .., h | .cons .., .lvl _, h | .cons .., .tok, h | .cons .., .clo .., h => by simp [rtArgs] at h
  | .fv _, _, h | .bv _, _, h | .bind .., _, h | .app .., _, h | .tyc .., _, h | .vc .., _, h | .tyCtor _, _, h
  | .valCtor _, _, h | .univ, _, h | .level, _, h | .predates .., _, h | .subterm .., _, h | .fn .., _, h
  | .lvl _, _, h | .tok, _, h | .clo .., _, h => by simp [rtArgs] at h
end

theorem Reals.len {a b t : Tm} : Reals P a b t → a.toList.length = b.toList.length
  | .nil => rfl
  | .cons _ h => by simp [Tm.toList, h.len]

theorem Reals.get {a b t : Tm} : Reals P a b t → ∀ k x y, a.toList[k]? = some x → b.toList[k]? = some y →
    t.ers.getD k true = false → Real P x y
  | .nil, _, _, _, h, _, _ => by simp [Tm.toList] at h
  | .cons hr hs, 0, x, y, h1, h2, he => by
    simp [Tm.toList] at h1 h2; subst h1 h2; exact hr (by simpa [Tm.ers] using he)
  | .cons _ hs, k + 1, x, y, h1, h2, he => hs.get k x y (by simpa [Tm.toList] using h1)
      (by simpa [Tm.toList] using h2) (by simpa [Tm.ers] using he)

theorem Ctx.pushEnt_n (Γ : Ctx) (k : Ent) (A : Tm) : (Γ.pushEnt k A).n = Γ.n + 1 := by
  cases k <;> simp [Ctx.pushEnt, Ctx.withRule, Ctx.push, Ctx.n]

theorem Ctx.openTele_er : ∀ m (Γ : Ctx) (t : Tm), t.isTele →
    (Γ.openTele t m).1.ghost = Γ.ghost ∧ (∀ i < Γ.n, (Γ.openTele t m).1.er i = Γ.er i) ∧
    ∀ k < m, k < t.ers.length → (Γ.openTele t m).1.er (Γ.n + k) = t.ers.getD k true := by
  intro m; induction m with
  | zero => intro Γ t _; refine ⟨?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩ <;> cases t <;> simp [Ctx.openTele]
  | succ m ih =>
    intro Γ t ht
    cases t with
    | bind k A r =>
      simp only [Tm.isTele] at ht
      have hn := Γ.pushEnt_n k A
      have her : ∀ i, (Γ.pushEnt k A).er i = if i = Γ.n then k.er else Γ.er i := by
        intro i; cases k <;> simp [Ctx.pushEnt, Ent.er]
      obtain ⟨g, h1, h2⟩ := ih (Γ.pushEnt k A) (r.inst (.fv Γ.n) 0) (Tm.isTele_inst _ r 0 ht)
      simp only [Ctx.openTele]
      refine ⟨by rw [g]; cases k <;> simp [Ctx.pushEnt, Ctx.withRule, Ctx.push], fun i hi => by rw [h1 i (by omega), her, if_neg (by omega)], ?_⟩
      intro j hj hjl
      cases j with
      | zero => rw [h1 _ (by omega), her, if_pos (by omega)]; simp [Tm.ers]
      | succ j =>
        rw [Tm.ers_inst _ _ _ ht] at h2
        have := h2 j (by omega) (by simp [Tm.ers] at hjl; omega)
        rw [show Γ.n + (j + 1) = (Γ.pushEnt k A).n + j by omega, this]; simp [Tm.ers]
    | _ => refine ⟨rfl, fun _ _ => rfl, fun j _ hj => ?_⟩; simp [Tm.ers] at hj

theorem Tm.len_ers : ∀ (t : Tm), t.isTele → t.ers.length = t.len := by
  intro t; induction t <;> intro h <;> simp_all [ers, len, isTele]

theorem Ctx.pushTele_er (Γ : Ctx) (R : Tm) (ov : Option (List Bool)) (hR : R.isTele) :
    (Γ.pushTele R ov).ghost = Γ.ghost ∧ (∀ i < Γ.n, (Γ.pushTele R ov).er i = Γ.er i) ∧
    ∀ k < R.len, (Γ.pushTele R ov).er (Γ.n + k) = (ov.getD R.ers).getD k true := by
  obtain ⟨g, h1, h2⟩ := Ctx.openTele_er R.len Γ R hR
  cases ov with
  | none => exact ⟨g, h1, fun k hk => h2 k hk (by rw [Tm.len_ers _ hR]; exact hk)⟩
  | some ms =>
    refine ⟨g, fun i hi => ?_, fun k _ => ?_⟩
    · rw [Ctx.pushTele, Ctx.er_setErs, if_neg (by omega)]; exact h1 i hi
    · simp [Ctx.pushTele]

@[simp] theorem Ctx.pushTele_fixed (Γ : Ctx) (R : Tm) (ov : Option (List Bool)) :
    (Γ.pushTele R ov).fixed = Γ.fixed := by
  have : ∀ m (Γ : Ctx) t, (Γ.openTele t m).1.fixed = Γ.fixed := by
    intro m; induction m with
    | zero => intro Γ t; cases t <;> rfl
    | succ m ih => intro Γ t; cases t <;> try rfl
                   rename_i k A r; simp only [Ctx.openTele]; rw [ih]; cases k <;> simp [Ctx.pushEnt, Ctx.withRule, Ctx.push]
  cases ov <;> simp [Ctx.pushTele, Ctx.setErs, this]

theorem callee_some {v : Tm} {env : List Tm} {n gid : Nat} {G : Group} {F : FnDef}
    (h : callee P v = some (env, n, gid, G, F)) :
    ∃ e j, v = .clo e gid j ∧ env = e.toList ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F := by
  unfold callee at h
  split at h
  · rename_i e g j
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨G', hG, F', hF, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl, rfl, rfl⟩ := h
      exact ⟨e, j, rfl, rfl, hG, hF⟩
    · simp at h
  · simp at h

theorem Real.clo_inv {vS e : Tm} {gid j : Nat} (h : Real P vS (.clo e gid j)) :
    (∃ envS env G F, vS = .clo (.ofList envS) gid j ∧ e = .ofList env ∧ P.groups[gid]? = some G ∧
      G.ghost = false ∧ G.fns[j]? = some F ∧ F.er = false ∧ F.dele = none ∧
      SimEnv P (fun i => G.ers.getD i true) envS env) ∨
    (∃ env G F t, e = .ofList env ∧ P.groups[gid]? = some G ∧ G.ghost = false ∧ G.fns[j]? = some F ∧
      F.er = false ∧ F.dele = some t ∧ Real P vS (Tm.env (env ++ closures env gid G) t)) := by
  cases h with
  | clo hG hg hF hf hd hl hr => exact .inl ⟨_, _, _, _, rfl, rfl, hG, hg, hF, hf, hd, hl, hr⟩
  | dele hG hg hF hf hd hr => exact .inr ⟨_, _, _, _, rfl, hG, hg, hF, hf, hd, hr⟩
  | other _ _ h3 _ => exact absurd rfl (h3 _ _ _)
  | nat he h' =>
    obtain ⟨_, _, hv⟩ := Prog.view_nat (n := _) he; rw [hv] at h'
    cases h' with
    | dele hG hg hF hf hd hr => exact .inr ⟨_, _, _, _, rfl, hG, hg, hF, hf, hd, .nat he (by rw [hv]; exact hr)⟩
    | other _ _ h3 _ => exact absurd rfl (h3 _ _ _)

theorem Real.con_inv {vS ls : Tm} {d c : Nat} {vs : Tm} (h : Real P vS (.app (.vc d c ls) vs)) (hn : P.isNt d = false) :
    ∃ vsS sig, P.view vS = .app (.vc d c .nil) vsS ∧ P.ctor d c = some sig ∧ P.phantom d c = false ∧
      Reals P vsS vs (sig.skip (P.lifted d)) := by
  have h2 := Real.view h
  generalize hw : P.view vS = w at h2
  cases h2 with
  | con hc hp _ hr => exact ⟨_, _, rfl, hc, hp, hr⟩
  | wrap hw _ => rw [(Prog.wrapField_spec hw).1] at hn; cases hn
  | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)
  | nat he _ => cases vS <;> simp [Prog.view, he] at hw <;> (split at hw <;> simp_all)

theorem Real.wrap_inv (hP : ProgOK P) {vS ls : Tm} {d c : Nat} {vs : Tm} (h : Real P vS (.app (.vc d c ls) vs))
    (hn : P.isNt d = true) : ∃ k, P.wrapField d c = some k ∧ Real P vS (vs.toList.getD k .nil) := by
  cases h with
  | con hc hp hw _ =>
    have := hP.newtype _ _ _ hn hp hc
    simp [Prog.wrapField, hn, hp, hc] at hw; rw [hw] at this; cases this
  | wrap hw hr => exact ⟨_, hw, hr⟩
  | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)
  | nat he h' =>
    obtain ⟨_, _, hv⟩ := Prog.view_nat (n := _) he; rw [hv] at h'
    cases h' with
    | con hc hp hw _ =>
      have := hP.newtype _ _ _ hn hp hc
      simp [Prog.wrapField, hn, hp, hc] at hw; rw [hw] at this; cases this
    | wrap hw hr => exact ⟨_, hw, .nat he (by rw [hv]; exact hr)⟩
    | other h1 _ _ _ => exact absurd rfl (h1 _ _ _ _)

section
variable {Γ Γ' : Ctx}
theorem Ctx.advBr_cases {s k : Tm} {fe : Bool} {n : Nat} :
    Γ.advBr P Γ' s k fe n = Γ' ∨ ∃ vs, Γ.advBr P Γ' s k fe n = Γ.record Γ' vs := by
  unfold Ctx.advBr
  repeat' split
  all_goals first | exact .inl rfl | exact .inr ⟨_, rfl⟩

theorem Ctx.adv_cases {c : Core} : Ctx.adv P Γ Γ' c = Γ' ∨ ∃ vs, Ctx.adv P Γ Γ' c = Γ.record Γ' vs := by
  unfold Ctx.adv; split
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem Ctx.advBr_same {s k : Tm} {fe : Bool} {n : Nat} : ∃ F, Γ.advBr P Γ' s k fe n = { Γ' with fixed := F } := by
  rcases Ctx.advBr_cases (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n) with h | ⟨vs, h⟩ <;> rw [h]
  · exact ⟨Γ'.fixed, rfl⟩
  · exact ⟨_, rfl⟩

theorem Ctx.adv_same {c : Core} : ∃ F, Ctx.adv P Γ Γ' c = { Γ' with fixed := F } := by
  rcases Ctx.adv_cases (P := P) (Γ := Γ) (Γ' := Γ') (c := c) with h | ⟨vs, h⟩ <;> rw [h]
  · exact ⟨Γ'.fixed, rfl⟩
  · exact ⟨_, rfl⟩
@[simp] theorem Ctx.advBr_tys {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).tys = Γ'.tys := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_tys {c : Core} : (Ctx.adv P Γ Γ' c).tys = Γ'.tys := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_σ {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).σ = Γ'.σ := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_σ {c : Core} : (Ctx.adv P Γ Γ' c).σ = Γ'.σ := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_mints {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).mints = Γ'.mints := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_mints {c : Core} : (Ctx.adv P Γ Γ' c).mints = Γ'.mints := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_cur {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).cur = Γ'.cur := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_cur {c : Core} : (Ctx.adv P Γ Γ' c).cur = Γ'.cur := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_subs {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).subs = Γ'.subs := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_subs {c : Core} : (Ctx.adv P Γ Γ' c).subs = Γ'.subs := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_er {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).er = Γ'.er := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]; rfl
theorem Ctx.advBr_erA {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).erA = Γ'.erA := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_er {c : Core} : (Ctx.adv P Γ Γ' c).er = Γ'.er := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]; rfl
@[simp] theorem Ctx.advBr_ghost {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).ghost = Γ'.ghost := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_ghost {c : Core} : (Ctx.adv P Γ Γ' c).ghost = Γ'.ghost := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_opened {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).opened = Γ'.opened := by
  obtain ⟨F, h⟩ := Ctx.advBr_same (P := P) (Γ := Γ) (Γ' := Γ') (s := s) (k := k) (fe := fe) (n := n); rw [h]
@[simp] theorem Ctx.adv_opened {c : Core} : (Ctx.adv P Γ Γ' c).opened = Γ'.opened := by
  obtain ⟨F, h⟩ := Ctx.adv_same (P := P) (Γ := Γ) (Γ' := Γ') (c := c); rw [h]
@[simp] theorem Ctx.advBr_n {s k : Tm} {fe : Bool} {n : Nat} : (Γ.advBr P Γ' s k fe n).n = Γ'.n := by simp [Ctx.n]
@[simp] theorem Ctx.adv_n {c : Core} : (Ctx.adv P Γ Γ' c).n = Γ'.n := by simp [Ctx.n]
end

theorem EnvOK.record {ρ outs vs : List Tm} {Γ Γ' : Ctx} (hE : EnvOK P ρ Γ) (hE' : EnvOK P (ρ ++ outs) Γ')
    (hf : Γ'.fixed = Γ.fixed) (hr : Γ.ready = true) (hl : vs.length = outs.length)
    (hv : ∀ k a b, vs[k]? = some a → outs[k]? = some b → Γ'.er (Γ.n + k) = false → Real P a b) :
    EnvOK P (ρ ++ outs) (Γ.record Γ' vs) := by
  have hn : Γ.fixed.length = Γ.n := by simp only [Ctx.ready, Bool.and_eq_true, beq_iff_eq] at hr; exact hr.1.1.1
  have hρ := hE.len
  refine (hE'.refix _ ⟨by simp; omega, fun i v h => ?_⟩)
  rw [List.getElem?_append] at h
  split at h
  · rename_i hi
    rw [Tm.env_append (by omega)]
    rw [hf] at *
    exact hE.fix.2 i v h
  · rename_i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = Γ.fixed.length + m := ⟨i - Γ.fixed.length, by omega⟩
    simp only [Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_zipIdx] at h
    cases ha : vs[m]? with
    | none => simp [ha] at h
    | some a =>
      simp only [ha, Option.map_some, Option.join_some] at h
      split at h
      · simp at h
      · rename_i her
        cases h
        have hk : m < outs.length := by have := (List.getElem?_eq_some_iff.mp ha).1; omega
        have hb : outs[m]? = some outs[m] := List.getElem?_eq_getElem hk
        have := hv _ _ _ ha hb (by rw [← hn]; simpa [hn] using her)
        simp only [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right (show ρ.length ≤ Γ.fixed.length + m by omega)]
        rw [show Γ.fixed.length + m - ρ.length = m by omega, hb]; exact this

theorem EnvOK.ready_sim {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (hr : Γ.ready = true) :
    SimEnv P Γ.er Γ.strip ρ ∧ Γ.ghost = false ∧ Γ.cur = none := by
  simp only [Ctx.ready, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Bool.not_eq_true',
    List.all_eq_true, Bool.or_eq_true] at hr
  obtain ⟨⟨⟨hn, hc⟩, hg⟩, ha⟩ := hr
  replace ha : ∀ i < Γ.n, (Γ.fixed[i]?.join).isSome = true ∨ Γ.er i = true := fun i hi => by
    obtain ⟨o, ho⟩ : ∃ o, Γ.fixed[i]? = some o := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simpa [ho] using ha (o, i) (List.mk_mem_zipIdx_iff_getElem?.mpr ho)
  simp only [Option.isSome_iff_exists] at ha
  have hl := hE.len
  refine ⟨⟨by simp [Ctx.strip]; omega, fun i he => ?_⟩, hg, hc⟩
  rcases Nat.lt_or_ge i Γ.n with hi | hi
  · rcases ha i hi with ⟨v, hv⟩ | h
    · have := hE.fix.2 i v hv
      have hs : Tm.env Γ.strip i = v := by
        simp only [Tm.env, Ctx.strip, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases h : Γ.fixed[i]? with
        | none => simp [h] at hv
        | some o => simp [h] at hv; simp [hv]
      rw [hs]; exact this
    · rw [h] at he; cases he
  · have : Tm.env ρ i = .nil := by simp [Tm.env, List.getElem?_eq_none (show ρ.length ≤ i by omega)]
    rw [this]; exact Real.nil' _

theorem EnvOK.known {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {k ls : Tm} {d c d' c' : Nat}
    (hk : Γ.known k = some (d, c)) (hv : k.subst (Tm.env ρ) = .vc d' c' ls) : d' = d ∧ c' = c := by
  cases k with
  | vc => simp [Ctx.known, Tm.subst] at hk hv; obtain ⟨rfl, rfl⟩ := hk; obtain ⟨rfl, rfl, -⟩ := hv; exact ⟨rfl, rfl⟩
  | fv y =>
    simp only [Ctx.known] at hk
    split at hk
    · rename_i d0 c0 hy
      cases hk
      have := (hE.fix.2 y _ hy); simp only [Tm.subst] at hv; rw [hv] at this
      have := this.vc_inv.1; cases this; exact ⟨rfl, rfl⟩
    · cases hk
  | _ => simp [Ctx.known] at hk

theorem EnvOK.advBr (hP : ProgOK P) {ρ pre : List Tm} {Γ Γ' : Ctx} {s k : Tm} {fe : Bool} {n d c : Nat} {vs sig sig0 ls ls' : Tm}
    (hlen : n = (sig0.skip (P.lifted d)).len - 1) (hE : EnvOK P ρ Γ) (hE' : EnvOK P (ρ ++ pre) Γ') (hf : Γ'.fixed = Γ.fixed)
    (hs : s.subst (Tm.env ρ) = .app (.vc d c ls) vs) (hpre : pre = vs.toList) (hn : n = pre.length)
    (hsig : P.ctor d c = some sig0) (hers : (sig0.skip (P.lifted d)).ers = sig.ers)
    (her : ∀ j < pre.length, Γ'.er (Γ.n + j) = (fe || sig.ers.getD j true))
    (hk : k.subst (Tm.env ρ) = .vc d c ls') :
    EnvOK P (ρ ++ pre) (Γ.advBr P Γ' s k fe n) := by
  unfold Ctx.advBr
  split
  · rename_i hr
    split
    · rename_i hfe
      exact hE.record hE' hf hr (by simp [hn]) fun j a b ha hb he => by
        rw [her j (List.getElem?_eq_some_iff.mp hb).1, hfe] at he; cases he
    · rename_i hfe
      split
      · rename_i x d0 c0 hkn
        split
        · rename_i hnt
          obtain ⟨rfl, rfl⟩ := hE.known hkn hk
          split
          · rename_i w hx
            have hR := hE.fix.2 x _ hx
            simp only [Tm.subst] at hs; rw [hs] at hR
            obtain ⟨k0, hw, hrk⟩ := Real.wrap_inv hP hR hnt
            obtain ⟨-, -, sig1, hc1, hnf⟩ := Prog.wrapField_spec hw
            rw [hsig] at hc1; cases hc1
            obtain ⟨-, -, honly⟩ := Tm.ntField_spec hnf
            subst hpre
            exact hE.record hE' hf hr (by simp [hn]) fun j a b ha hb he => by
              have hj := (List.getElem?_eq_some_iff.mp hb).1
              rw [her j hj] at he
              simp only [hfe, Bool.false_or] at he
              rw [← hers] at he
              have := honly j (by omega) he
              subst this
              rw [List.getElem?_replicate] at ha
              split at ha
              · cases ha
                rw [List.getD_eq_getElem?_getD, hb] at hrk; exact hrk
              · cases ha
          · exact hE'
        rename_i hnt
        obtain ⟨rfl, rfl⟩ := hE.known hkn hk
        split
        · rename_i d' c' vsS hx
          split
          · rename_i hdc
            obtain ⟨rfl, rfl⟩ := hdc
            obtain ⟨w, hx, hwv⟩ := Option.map_eq_some_iff.mp hx
            have hR := hE.fix.2 x _ hx
            simp only [Tm.subst] at hs; rw [hs] at hR
            obtain ⟨vsS', sig', e1, hsig', _, hrv⟩ := hR.con_inv (by simpa using hnt)
            rw [hwv] at e1
            cases e1; rw [hsig] at hsig'; cases hsig'
            subst hpre
            exact hE.record hE' hf hr hrv.len fun j a b ha hb he => by
              rw [her j (List.getElem?_eq_some_iff.mp hb).1] at he
              simp only [hfe, Bool.false_or] at he
              exact (hrv.retele hers).get j a b ha hb he
          · exact hE'
        · exact hE'
      · exact hE'
  · exact hE'

theorem selectBr_same {brs : List Br} {els : Option Core} {c : Nat} {vs vs' pre : List Tm}
    {body : Core} (h : selectBr brs els c vs = some (pre, body)) :
    (pre = vs ∧ selectBr brs els c vs' = some (vs', body)) ∨ (pre = [] ∧ selectBr brs els c vs' = some ([], body)) := by
  unfold selectBr at h ⊢
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  · cases els <;> simp at h; obtain ⟨rfl, rfl⟩ := h; simp

theorem compat_get : ∀ (ms : List Bool) (t : Tm) (k : Nat), compat ms t = true → k < t.ers.length →
    ms.getD k true = false → t.ers.getD k true = false
  | m :: ms, .bind e _ r, 0, h, _, hm => by
    simp only [compat, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp at hm; subst hm; simpa [Tm.ers] using h.1
  | m :: ms, .bind e _ r, k + 1, h, hk, hm => by
    simp only [compat, Bool.and_eq_true] at h
    simpa [Tm.ers] using compat_get ms r k h.2 (by simpa [Tm.ers] using hk) (by simpa using hm)
  | [], _, _, _, _, hm => by simp at hm
  | _ :: _, .nil, _, _, hk, _ | _ :: _, .fv _, _, _, hk, _ | _ :: _, .bv _, _, _, hk, _
  | _ :: _, .cons .., _, _, hk, _ | _ :: _, .app .., _, _, hk, _ | _ :: _, .tyc .., _, _, hk, _
  | _ :: _, .vc .., _, _, hk, _ | _ :: _, .tyCtor _, _, _, hk, _ | _ :: _, .valCtor _, _, _, hk, _
  | _ :: _, .univ, _, _, hk, _ | _ :: _, .level, _, _, hk, _ | _ :: _, .predates .., _, _, hk, _
  | _ :: _, .subterm .., _, _, hk, _ | _ :: _, .fn .., _, _, hk, _ | _ :: _, .lvl _, _, _, hk, _
  | _ :: _, .tok, _, _, hk, _ | _ :: _, .clo .., _, _, hk, _ => by simp [Tm.ers] at hk

theorem call_setup_ctx (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {f Ft l t args outsT : Tm} {np : Nat} {dec : Dec}
    (hf : TmTy P Γ f Ft) {uf : Bool} {hmk : List Bool} (hF : Γ.canon Ft = .fn l np t uf hmk) (ht : t.isTele) (ha : ArgsTy P Γ args t outsT)
    (hn : args.len = np) (hd : DecOK P Γ dec l t args) {env : List Tm} {Γc : Ctx} {gid j : Nat} {G : Group}
    {F : FnDef} (hfv : f.subst (Tm.env ρ) = .clo (.ofList env) gid j) (hEc : EnvOK P env Γc) (hG : P.groups[gid]? = some G)
    (hok : GroupOK P gid Γc G) (hFj : G.fns[j]? = some F)
    (hty : (F.type G).subst (Tm.env env) = .fn (l.subst (Tm.env ρ)) np (t.subst (Tm.env ρ)) uf hmk)
    (hfs : f.static Γ.n 0 = true) (hFs' : l.static Γ.n 0 = true ∧ t.static Γ.n 0 = true) :
    ∃ env n1 gid G F, callee P (f.subst (Tm.env ρ)) = some (env, n1, gid, G, F) ∧
      muLt P.k (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) μ ∧
      (∃ Γb rb, Γb = (Γc.body G F).1 ∧ rb = (Γc.body G F).2 ∧ CoreTy P gid Γb F.body rb ∧
        EnvOK P (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) Γb ∧
        LvlBound (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt ∧
        MuOK (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) Γb
          (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) ∧
        rb.static Γb.n 0 ∧
        rb.subst (Tm.env (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ)))) = outsT.subst (Tm.env ρ) ∧
        Γb.ghost = (G.ghost || F.er) ∧ (∀ i < env.length, F.dele = none → Γb.er i = G.ers.getD i true) ∧
        (∀ j' F', G.fns[j']? = some F' → F.dele = none → Γb.er (env.length + j') = F'.er) ∧
        (∀ i t, F.dele = some t → i < env.length + G.fns.length → i ≠ t → Γb.er i = true) ∧
        (∀ k < np, Γb.er (env.length + G.fns.length + k) = t.ers.getD k true) ∧ rb.isTele) ∧
      outsT.isTele ∧ outsT.static Γ.n 0 ∧ F.tele.ers = t.ers ∧ F.np = np ∧ G.deleOK P env.length = true := by
  have hw := hE.wf
  simp only [FnDef.type, Tm.subst, Tm.fn.injEq] at hty
  obtain ⟨hlv, hnp, htele, -⟩ := hty
  have hok' := hok
  cases hok with
  | mk hK hKl htyF hmk hbody hGe hg hdo _ =>
  obtain ⟨lv, hlv', hlve, hvK⟩ := hEc.get hK
  rw [← hEc.canon, hKl] at hvK; simp only [Tm.subst] at hvK
  obtain ⟨n1, rfl⟩ := hvK.level_inv
  have hal := ha.isList
  obtain ⟨hva, has, hos⟩ := args_sound hP hE ha hFs'.2
  have hargv : args.toList.map (·.subst (Tm.env ρ)) = (args.subst (Tm.env ρ)).toList :=
    (Tm.toList_subst _ _ hal).symm
  have hofl : Tm.ofList (args.subst (Tm.env ρ)).toList = args.subst (Tm.env ρ) :=
    Tm.ofList_toList _ (Tm.isList_subst _ _ hal)
  obtain ⟨_, hFstat, hFty⟩ := tm_sound hP hEc (htyF j F hFj)
  have hFtele : F.tele.isTele := by cases htyF j F hFj with | fn _ _ h _ _ => exact h.isTele
  have hFnp : F.np ≤ F.tele.len := by cases htyF j F hFj with | fn _ _ _ h _ => exact h
  simp only [FnDef.type, Tm.static, Bool.and_eq_true] at hFstat
  have hle := hEc.len
  have hlvl : l.subst (Tm.env ρ) = .lvl n1 := by rw [← hlv]; simpa [Tm.subst] using hlve
  have hmarks : ∀ X, markedArgs F.tele X = markedArgs t X := fun X => by
    rw [← markedArgs_subst_tele (Tm.env env) _ X hFtele, htele, markedArgs_subst_tele _ _ X ht]
  refine ⟨env, n1, gid, G, F, ?_, ?_, ?_, ha.isTele ht, hos,
    by rw [← Tm.ers_subst (Tm.env env) _ hFtele, htele, Tm.ers_subst _ _ ht], hnp, by rw [hEc.len]; exact hdo⟩
  · rw [hfv]; simp [callee, hG, hFj, Tm.toList_ofList, hlv']
  · rw [hargv, hofl, hmarks]
    refine dec_sound hP hE hm hd hal hlvl ?_
    have := hmk j F hFj
    rwa [← marks_subst (Tm.env env) _ _ hFtele, htele, marks_subst _ _ _ ht, hnp, ← hn] at this
  · have hE1 := hEc.pushFns hP hG hok'
    have hl1 := hE1.len
    have hn1 : Γc.n ≤ (Γc.pushFns G).n := by simp [Ctx.pushFns, Ctx.n]
    have hFt1 : F.tele.static (Γc.pushFns G).n 0 := Tm.static_mono hn1 _ (Nat.le_refl 0) hFstat.2
    have hvF : VTys P (args.subst (Tm.env ρ)) (F.tele.subst (Tm.env (env ++ closures env gid G)))
        (outsT.subst (Tm.env ρ)) := by
      rw [Tm.subst_append (hle ▸ hFstat.2), htele]; exact hva
    have hlc : ∀ v ∈ (args.subst (Tm.env ρ)).toList, v.lc 0 := by
      rw [Tm.toList_subst _ _ hal]; intro v hv'
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hv'
      exact lc_of_static hE.closed (static_toList has a ha')
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hE1.openTele hFtele hFt1 hvF hlc
    have hlen : (args.subst (Tm.env ρ)).len = F.np := by rw [Tm.len_subst _ _ (.inr hal), hn, hnp]
    rw [hlen] at h1 h2 h3 h4 h5 h6
    rw [hargv]
    have hlenl : (args.subst (Tm.env ρ)).toList.length = F.np := by
      rw [Tm.len_toList _ (Tm.isList_subst _ _ hal), hlen]
    have hfields : ∀ x ∈ markedArgs F.tele ((Γc.pushFns G).fields F.np), ∃ i, x = .fv i ∧
        (Γc.pushFns G).n ≤ i ∧ i < (Γc.pushFns G).n + F.np := by
      intro x hx
      have := markedArgs_mem _ _ x hx
      rw [fields_toList] at this
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp this
      exact ⟨_, rfl, by omega, by simp at hk; omega⟩
    obtain ⟨-, o1, o2⟩ := Ctx.openTele_er F.np (Γc.pushFns G) F.tele hFtele
    have hpn : (Γc.pushFns G).n = env.length + G.fns.length := by simp [Ctx.pushFns, Ctx.n, hle]
    refine ⟨(Γc.body G F).1, (Γc.body G F).2, rfl, rfl, hbody j F hFj, ?_, ?_, ?_, ?_, ?_,
      by simp [Ctx.body, hg], fun i hi hdn => ?_, fun j' F' hF' hdn => ?_, fun i t hdt hi hne => ?_, fun k hk => ?_, ?_⟩
    rotate_left 5
    · rw [Ctx.er_body]
      simp only [hdn, Option.isSome_none, Bool.false_and, Bool.false_or]
      rw [o1 i (by omega)]; rw [Ctx.er_pushFns, if_neg (by omega)]; exact hGe i (by omega)
    · rw [Ctx.er_body]
      simp only [hdn, Option.isSome_none, Bool.false_and, Bool.false_or]
      have hj' := (List.getElem?_eq_some_iff.mp hF').1
      rw [o1 _ (by omega)]; rw [Ctx.er_pushFns, if_pos (by omega)]; simp [← hle, hF']
    · rw [Ctx.er_body]
      have : i < (Γc.pushFns G).n := by rw [hpn]; exact hi
      simp [hdt, this, Ne.symm hne]
    · rw [Ctx.er_body]
      have hlt : ¬ (env.length + G.fns.length + k < (Γc.pushFns G).n) := by rw [hpn]; omega
      simp only [hlt, decide_false, Bool.and_false, Bool.false_and, Bool.false_or]
      rw [← hpn, o2 k (by omega) (by rw [Tm.len_ers _ hFtele]; omega), ← Tm.ers_subst (Tm.env env) _ hFtele, htele,
        Tm.ers_subst _ _ ht]
    · simp only [Ctx.body]; exact h4
    · simp only [Ctx.body]
      refine h1.modify rfl h1.sat h1.chrono ⟨h1.wf.tys, h1.wf.σ, h1.wf.ς, h1.wf.mints, fun c hc => ?_, fun s hs => ?_⟩
      · simp at hc; subst hc
        have := (getElem?_eq_some_iff.mp hK).1
        simp only [Ctx.n] at this hn1 h5 ⊢; omega
      · simp only [List.mem_filterMap] at hs
        obtain ⟨x, hx, hxs⟩ := hs
        obtain ⟨i, rfl, _, hi⟩ := hfields x hx
        simp [Tm.fvIdx] at hxs; subst hxs; simp only [Ctx.n] at h5 hi ⊢; omega
    · refine LvlBound.append.mpr ⟨LvlBound.append.mpr ⟨fun w hw x hx => ?_, fun w hw x hx => ?_⟩, fun w hw x hx => ?_⟩
      · have := hb.subst hfs x; rw [hfv] at this
        exact this (by simp only [Tm.levels]; exact Tm.levels_ofList_mem env w hw x hx)
      · simp only [closures, List.mem_map] at hw
        obtain ⟨_, _, rfl⟩ := hw
        have := hb.subst hfs x; rw [hfv] at this; exact this hx
      · rw [Tm.toList_subst _ _ hal] at hw
        obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hw
        exact hb.subst (static_toList has a ha') x hx
    · simp only [MuOK, Ctx.body]
      refine ⟨n1, ?_, ?_⟩
      · have : G.lvl < env.length := by rw [hle]; exact (getElem?_eq_some_iff.mp hK).1
        rw [List.append_assoc, List.getElem?_append_left this]; exact hlv'
      · congr 2
        rw [fv_filterMap_env _ Tm.size _ (fun x hx => by obtain ⟨i, h, _⟩ := hfields x hx; exact ⟨i, h⟩),
          ← markedArgs_subst_args _ _ _ (fields_isList _ _), ← hlenl, fields_subst _ hl1]
    · simp only [Ctx.body]; simpa [Ctx.n] using h3
    · simp only [Ctx.body]; simpa using h2

theorem call_setup (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {f Ft l t args outsT : Tm} {np : Nat} {dec : Dec}
    (hf : TmTy P Γ f Ft) {uf : Bool} {hmk : List Bool} (hF : Γ.canon Ft = .fn l np t uf hmk) (ht : t.isTele) (ha : ArgsTy P Γ args t outsT)
    (hn : args.len = np) (hd : DecOK P Γ dec l t args) :
    ∃ env n1 gid G F, callee P (f.subst (Tm.env ρ)) = some (env, n1, gid, G, F) ∧
      muLt P.k (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) μ ∧
      (∃ Γb rb, CoreTy P gid Γb F.body rb ∧
        EnvOK P (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) Γb ∧
        LvlBound (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt ∧
        MuOK (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) Γb
          (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) ∧
        rb.static Γb.n 0 ∧
        rb.subst (Tm.env (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ)))) = outsT.subst (Tm.env ρ) ∧
        Γb.ghost = (G.ghost || F.er) ∧ (∀ i < env.length, F.dele = none → Γb.er i = G.ers.getD i true) ∧
        (∀ j' F', G.fns[j']? = some F' → F.dele = none → Γb.er (env.length + j') = F'.er) ∧
        (∀ i t, F.dele = some t → i < env.length + G.fns.length → i ≠ t → Γb.er i = true) ∧
        (∀ k < np, Γb.er (env.length + G.fns.length + k) = t.ers.getD k true) ∧ rb.isTele) ∧
      outsT.isTele ∧ outsT.static Γ.n 0 ∧ F.tele.ers = t.ers ∧ F.np = np ∧ G.deleOK P env.length = true := by
  have hw := hE.wf
  obtain ⟨hv, hfs, hFs⟩ := tm_sound hP hE hf
  have hFs' := canon_static hw hFs
  rw [hF] at hFs'; simp only [Tm.static, Bool.and_eq_true] at hFs'
  rw [← hE.canon Ft, hF] at hv; simp only [Tm.subst] at hv
  obtain ⟨env, Γc, gid, G, j, F, hfv, hEc, hG, hok, hFj, hty⟩ := hv.fn_inv
  obtain ⟨e', n1, g', G', F', h1, h2, ⟨Γb, rb, -, -, hX⟩, h4⟩ :=
    call_setup_ctx hP hE hb hm hf hF ht ha hn hd hfv hEc hG hok hFj hty hfs hFs'
  exact ⟨e', n1, g', G', F', h1, h2, ⟨Γb, rb, hX⟩, h4⟩

theorem Ctx.openTele_ghost (g : Bool) : ∀ m (Γ : Ctx) t,
    ({ Γ with ghost := g } : Ctx).openTele t m = ({ (Γ.openTele t m).1 with ghost := g }, (Γ.openTele t m).2) := by
  intro m; induction m with
  | zero => intro Γ t; cases t <;> rfl
  | succ m ih =>
    intro Γ t
    cases t with
    | bind k A r =>
      simp only [Ctx.openTele]
      have : ({ Γ with ghost := g } : Ctx).pushEnt k A = { Γ.pushEnt k A with ghost := g } := by
        cases k with
        | ty => rfl
        | is => exact Ctx.slotIf_upd_ghost ((Γ.push .nil _).withRule Γ.n (Γ.canon A)) _ _ _ g
      rw [this]; exact ih _ _
    | _ => rfl

theorem Ctx.ntSlot_ghost (g : Bool) (Γ Γf : Ctx) (s k : Tm) :
    ({ Γ with ghost := g } : Ctx).ntSlot P { Γf with ghost := g } s k = { Γ.ntSlot P Γf s k with ghost := g } := by
  unfold Ctx.ntSlot
  rw [show ({ Γ with ghost := g } : Ctx).known k = Γ.known k from rfl]
  generalize Γ.known k = kn; generalize s.varSlot = vs
  rcases kn with _ | ⟨d, c⟩ <;> rcases vs with _ | σ <;> dsimp only <;> try rfl
  generalize P.wrapField d c = wf
  rcases wf with _ | j
  · rfl
  · exact Ctx.withSlot_upd_ghost Γf _ _ g

theorem Ctx.branch_ghost (g : Bool) (Γ : Ctx) (s k H idx sig : Tm) :
    ({ Γ with ghost := g } : Ctx).branch P s k H idx sig =
      ({ (Γ.branch P s k H idx sig).1 with ghost := g }, (Γ.branch P s k H idx sig).2) := by
  simp only [Ctx.branch, Ctx.openTele_ghost, Ctx.ntSlot_ghost]
  generalize Γ.ntSlot P (Γ.openTele sig (sig.len - 1)).1 s k = Γn
  have e1 : ∀ Γ' : Ctx, ({ Γ' with ghost := g } : Ctx).n = Γ'.n := fun _ => rfl
  have e3 : ∀ Γ' : Ctx, Ctx.atoms P ({ Γ' with ghost := g } : Ctx) = Ctx.atoms P Γ' := fun _ => rfl
  have e4 : ∀ Γ' : Ctx, ({ Γ' with ghost := g } : Ctx).canon = Γ'.canon := fun _ => rfl
  have e5 : ∀ Γ' : Ctx, ({ Γ' with ghost := g } : Ctx).fields = Γ'.fields := fun _ => rfl
  simp only [e1, e3, e4, e5]
  split
  · split
    · rename_i σ0 _
      have h1 := Ctx.forceSlots_upd_ghost g ({ Γn with σ := σ0 } : Ctx)
      dsimp only
      simp only [Prod.mk.injEq, UResult.ok.injEq]
      refine ⟨h1 _, ?_⟩
      rw [h1]
    · rfl
  · rfl

section
variable (Γ Γ' : Ctx) (ov : Option (List Bool))
@[simp] theorem Ctx.setErs_tys : (Γ.setErs Γ' ov).tys = Γ'.tys := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_σ : (Γ.setErs Γ' ov).σ = Γ'.σ := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_mints : (Γ.setErs Γ' ov).mints = Γ'.mints := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_cur : (Γ.setErs Γ' ov).cur = Γ'.cur := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_subs : (Γ.setErs Γ' ov).subs = Γ'.subs := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_ghost : (Γ.setErs Γ' ov).ghost = Γ'.ghost := by cases ov <;> rfl
@[simp] theorem Ctx.setErs_n : (Γ.setErs Γ' ov).n = Γ'.n := by simp [Ctx.n]
theorem Ctx.setErs_er_lt {i : Nat} (h : i < Γ.n) : (Γ.setErs Γ' ov).er i = Γ'.er i := by
  cases ov with
  | none => rfl
  | some ms => rw [Ctx.er_setErs, if_neg (by omega)]
theorem Ctx.setErs_er_ge (ms : List Bool) (k : Nat) : (Γ.setErs Γ' (some ms)).er (Γ.n + k) = ms.getD k true := by
  rw [Ctx.er_setErs, if_pos (by omega)]; simp
end

theorem Shape.sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {er : Bool} {H : Tm} {shp : List Arm}
    {nt : Bool} (h : Shape P Γ er H shp nt) :
    ∃ d D ls, H.subst (Tm.env ρ) = .tyc d ls ∧ P.adts[d]? = some D ∧ ls.len = D.lifted ∧ shp.length = D.ctors.length ∧
      (∀ c k sig p, shp[c]? = some (k, sig, p) → k.subst (Tm.env ρ) = .vc d c ls ∧ k.static Γ.n 0 ∧
        (∃ sig0, D.ctors[c]? = some sig0 ∧ sig.subst (Tm.env ρ) = sig0.peel ls) ∧ sig.isTele ∧ sig.static Γ.n 0 ∧
        p = P.phantom d c) ∧
      P.isNt d = nt ∧ D.coercible = false ∧ D.opq = false := by
  cases h with
  | decl hD hco hop hl0 hli hls =>
    refine ⟨_, _, _, rfl, hD, by rw [Tm.len_subst _ _ (.inr hli), hl0], by simp, fun c k sig p hc => ?_,
      by simp [Prog.isNt, hD], hco, hop⟩
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Option.map_eq_some_iff] at hc
    obtain ⟨sig', hs', he⟩ := hc; simp only [Function.comp, Nat.zero_add, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨ht, h0, _⟩ := hP.ctors _ _ _ _ hD hs'
    refine ⟨by simp [Tm.subst], by simpa [Tm.static] using hls, ⟨_, hs', ?_⟩, Tm.isTele_peel _ _ ht.isTele,
      Tm.static_peel hls _ (Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) h0), rfl⟩
    rw [Tm.peel_subst _ (Tm.env_lc hE.closed) _ hli _ ht.isTele, Tm.subst_static0 _ _ 0 h0]
  | opened hm hM hc hl h1 h2 hr =>
    rename_i m M u ex ph cs
    obtain ⟨v, _, hv, hvT⟩ := hE.get hM
    rw [← hE.canon M, hc] at hvT; simp only [Tm.subst] at hvT
    obtain ⟨d, D, ls, _, hD, hco, hop, hll, _, he⟩ := hvT.mtbl_inv
    simp only [Adt.mtbl, Tm.mtbl.injEq] at he
    obtain ⟨-, hnt, -, hph, hT, hcs⟩ := he
    have hks : (cs.subst (Tm.env ρ)).toList = (List.range D.ctors.length).map (Tm.vc d · ls) := by
      rw [← hcs, Tm.toList_ofList]
    rw [Tm.toList_subst _ _ hl, ← h1, List.map_map] at hks
    have hlen : shp.length = D.ctors.length := by simpa using congrArg List.length hks
    refine ⟨d, D, ls, hT.symm, hD, hll, hlen, fun c k sig p hc => ?_, by simp [Prog.isNt, hD, hnt], hco, hop⟩
    have hcl : c < D.ctors.length := hlen ▸ (List.getElem?_eq_some_iff.mp hc).1
    have hk : k.subst (Tm.env ρ) = .vc d c ls := by
      have := congrArg (·[c]?) hks; simp only [List.getElem?_map, hc, List.getElem?_range hcl] at this
      simpa using this
    obtain ⟨hp, hst, hss, K, hK, hKc⟩ := h2 c k sig p hc
    obtain ⟨vk, hks', _⟩ := tm_sound hP hE hK
    rw [← hE.canon K, hKc, hk] at vk; simp only [Tm.subst] at vk
    obtain ⟨d', c', ls', sig0, he', hctor, _, hvs⟩ := vk.vc_inv
    simp only [Tm.vc.injEq] at he'; obtain ⟨rfl, rfl, rfl⟩ := he'
    refine ⟨hk, hks', ⟨sig0, by simpa [Prog.ctor, hD] using hctor, hvs.peel⟩, hst, hss, ?_⟩
    rw [hp, ← hph]; simp [Prog.phantom, hD, hcl, List.getD_eq_getElem?_getD]

theorem Tm.mtbl_subst (f : Nat → Tm) (D : Adt) (d : Nat) (ls : Tm) : (D.mtbl d ls).subst f = D.mtbl d (ls.subst f) := by
  simp [Adt.mtbl, Tm.subst, Tm.ofList_vc_subst]


theorem headD_mem {α : Type} {l : List α} {x d : α} (h : x ∈ l) : l.headD d ∈ l := by cases l <;> simp_all

def Names (P : Prog) (v : Tm) (M : Tm) : Prop :=
  ∃ d D ls, P.adts[d]? = some D ∧ M = D.mtbl d ls ∧ (v = .tyc d ls ∨ ∃ c, v = .vc d c ls)

theorem Names.uniq {v M M' : Tm} (h : Names P v M) (h' : Names P v M') : M = M' := by
  obtain ⟨d, D, ls, hD, rfl, hv⟩ := h
  obtain ⟨d', D', ls', hD', rfl, hv'⟩ := h'
  have : d = d' ∧ ls = ls' := by
    rcases hv with rfl | ⟨_, rfl⟩ <;> rcases hv' with h | ⟨_, h⟩ <;> cases h <;> exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := this; rw [hD] at hD'; cases hD'; rfl

theorem EnvOK.lists {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {σ : Nat → Option Tm} (hs : Sat (Tm.env ρ) σ)
    {M T : Tm} {ks : List Tm} (h : (M, T, ks) ∈ Γ.lists σ) : ∃ d ls, Names P (T.subst (Tm.env ρ)) (M.subst (Tm.env ρ)) ∧
      T.subst (Tm.env ρ) = .tyc d ls ∧ ∀ i (x : Tm), ks[i]? = some x → x.subst (Tm.env ρ) = .vc d i ls ∧
        Names P (x.subst (Tm.env ρ)) (M.subst (Tm.env ρ)) := by
  obtain ⟨⟨m, _⟩, -, hm⟩ := List.mem_filterMap.mp h
  cases hM : Γ.tys[m]? with
  | none => simp [hM] at hm
  | some M0 =>
    simp only [hM, Option.map_some] at hm
    split at hm
    · rename_i u nt ex ph T' cs hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl⟩ := hm
      obtain ⟨v, _, _, hv⟩ := hE.get hM
      rw [← canonBy_sound hs hE.satS M0, Option.some.inj hc] at hv
      obtain ⟨d, D, ls, _, hD, -, -, -, -, he⟩ := hv.mtbl_inv
      have he' := he; simp only [Adt.mtbl, Tm.mtbl.injEq] at he'
      obtain ⟨-, -, -, -, hT, hcs⟩ := he'
      have hM' : (Tm.mtbl u nt ex ph T' cs).subst (Tm.env ρ) = D.mtbl d ls := by rw [he]; rfl
      refine ⟨d, ls, ⟨d, D, ls, hD, hM', .inl hT.symm⟩, hT.symm, fun i x hx => ?_⟩
      have := Tm.toList_subst_get (Tm.env ρ) cs i x hx
      rw [← hcs, Tm.toList_ofList] at this
      have hi : i < D.ctors.length := by simpa using (List.getElem?_eq_some_iff.mp this).1
      rw [List.getElem?_map, List.getElem?_range hi] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨this.symm, d, D, ls, hD, hM', .inr ⟨i, this.symm⟩⟩
    · cases hm

theorem sigOf_vty (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {x s : Tm} (h : sigOf P Γ x = some s) :
    (∃ y, s.subst (Tm.env ρ) = .tyCtor y ∨ s.subst (Tm.env ρ) = .valCtor y) ∧
      VTy P (x.subst (Tm.env ρ)) (s.subst (Tm.env ρ)) := by
  cases x with
  | fv e =>
    simp only [sigOf, Ctx.sig] at h
    cases hT : Γ.tys[e]? with
    | none => simp [hT] at h
    | some T =>
      obtain ⟨v, _, hv, hvT⟩ := hE.get hT
      rw [← hE.canon T] at hvT
      simp only [hT, Option.map_some] at h
      split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rename_i h' <;>
        rw [Option.some.inj h'] at hvT <;> simp only [Tm.subst] at hvT ⊢ <;> rw [hv] <;>
        first | exact ⟨⟨_, .inl rfl⟩, hvT⟩ | exact ⟨⟨_, .inr rfl⟩, hvT⟩
  | tyc d ls =>
    cases ls with
    | nil =>
      simp only [sigOf] at h; split at h
      · rename_i hl; simp only [Option.map_eq_some_iff] at h; obtain ⟨D, hD, rfl⟩ := h
        simp only [Tm.subst]; rw [Tm.subst_static0 _ _ 0 (hP.params _ _ hD).2]
        exact ⟨⟨_, .inl rfl⟩, .tyCtor hD (by simpa [Tm.len, Prog.lifted, hD] using hl.symm) .nil⟩
      · cases h
    | _ => simp [sigOf] at h
  | vc d c ls =>
    cases ls with
    | nil =>
      simp only [sigOf] at h; split at h
      · rename_i hl; simp only [Option.map_eq_some_iff] at h; obtain ⟨sig, hc, rfl⟩ := h
        obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
        simp only [Tm.subst]; rw [Tm.subst_static0 _ _ 0 (hP.ctors _ _ _ _ hD hsig).2.1]
        exact ⟨⟨_, .inr rfl⟩, .vc hc (by simpa [Tm.len] using hl.symm) .nil⟩
      · cases h
    | _ => simp [sigOf] at h
  | _ => simp [sigOf] at h

theorem EnvOK.atomSound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) : AtomSound (Tm.env ρ) (Γ.atoms P) := by
  intro σ hs a b hab
  have hnames : ∀ x M, x.subst (Tm.env ρ) = a.subst (Tm.env ρ) →
      M ∈ (Γ.lists σ).filterMap (fun (M, T, ks) => if T == x || ks.contains x then some M else none) ++ declMtbl P x →
      Names P (a.subst (Tm.env ρ)) (M.subst (Tm.env ρ)) := by
    intro x M hx hM
    rcases List.mem_append.mp hM with hM | hM
    · obtain ⟨⟨M', T, ks⟩, hmem, hsel⟩ := List.mem_filterMap.mp hM
      obtain ⟨d, ls, hN, hT, hks⟩ := hE.lists hs hmem
      simp only [Option.ite_none_right_eq_some, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hsel
      obtain ⟨hor, h⟩ := hsel; cases h
      rcases hor with rfl | hk
      · rw [← hx]; exact hN
      · obtain ⟨i, hi⟩ := List.getElem?_of_mem hk
        rw [← hx]; exact (hks i x hi).2
    · cases x with
      | tyc d ls | vc d _ ls =>
        cases ls with
        | nil =>
          simp only [declMtbl, Option.mem_toList, Option.map_eq_some_iff] at hM
          obtain ⟨D, hD, rfl⟩ := hM
          rw [Tm.mtbl_subst, ← hx]; exact ⟨d, D, .nil, hD, rfl, by simp [Tm.subst]⟩
        | _ => simp [declMtbl] at hM
      | _ => simp [declMtbl] at hM
  simp only [Ctx.atoms]
  split
  · rename_i hany; exfalso
    obtain ⟨⟨M, T, ks⟩, hmem, hij⟩ := List.any_eq_true.mp hany
    split at hij
    · rename_i i j hi hj
      obtain ⟨hi', hia, -⟩ := List.idxOf?_eq_some_iff.mp hi
      obtain ⟨hj', hjb, -⟩ := List.idxOf?_eq_some_iff.mp hj
      obtain ⟨d, ls, -, -, hks⟩ := hE.lists hs hmem
      have e1 := (hks i a (by simp [← hia])).1
      have e2 := (hks j b (by simp [← hjb])).1
      rw [hab, e2] at e1; cases e1; simp at hij
    · cases hij
  split
  · rename_i hat
    simp only [Bool.and_eq_true] at hat
    simp only [Tm.sameHead_of_subst hat.1 hat.2 hab, ite_true]; exact ⟨[], rfl, by simp⟩
  refine ⟨_, rfl, fun p hp => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · split at hp
      · rename_i s s' h1 h2
        simp only [List.mem_singleton] at hp; subst hp
        simp only [canonBy_sound hs hE.satS]
        obtain ⟨hs1, v1⟩ := sigOf_vty hP hE h1
        obtain ⟨hs2, v2⟩ := sigOf_vty hP hE h2
        rw [hab] at v1
        exact VTy.sig_det v1 v2 (by obtain ⟨y, h | h⟩ := hs1 <;> exact ⟨y, by simp [h]⟩)
          (by obtain ⟨y, h | h⟩ := hs2 <;> exact ⟨y, by simp [h]⟩)
      · simp at hp
    · obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hp
      have all : ∀ M ∈ (Γ.lists σ).filterMap (fun (M, T, ks) => if T == a || ks.contains a then some M else none) ++ declMtbl P a ++
          ((Γ.lists σ).filterMap (fun (M, T, ks) => if T == b || ks.contains b then some M else none) ++ declMtbl P b),
          Names P (a.subst (Tm.env ρ)) (M.subst (Tm.env ρ)) := by
        intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · exact hnames a M rfl hM
        · exact hnames b M hab.symm hM
      have hh := all _ (headD_mem (d := .nil) hM)
      exact (all M hM).uniq hh |>.symm

theorem EnvOK.openEqs (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (o : List (Nat × Bool)) (xs : List Tm) :
    ∀ p ∈ Ctx.openEqs P { Γ with opened := o } xs, p.1.subst (Tm.env ρ) = p.2.subst (Tm.env ρ) := by
  intro p hp
  simp only [Ctx.openEqs, List.mem_flatMap] at hp
  obtain ⟨x, -, hx⟩ := hp
  obtain ⟨more, hmo, hmore⟩ := (hE.congr { Γ with opened := o } rfl rfl rfl rfl rfl).atomSound hP Γ.σ hE.sat x x rfl
  rw [hmo] at hx; exact hmore p hx

theorem EnvOK.opened (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {o : List (Nat × Bool)}
    {xs : List Tm} {σ' : Nat → Option Tm}
    (hu : unify Γ.n (Ctx.atoms P { Γ with opened := o }) Γ.σ [] (Ctx.openEqs P { Γ with opened := o } xs) = .ok σ') :
    EnvOK P ρ { Γ with opened := o, σ := σ' } := by
  have hun := unify_sound (Tm.env ρ) (fun i => Tm.bound_of_lc _ 0 (Tm.env_lc hE.closed i)) Γ.n
    (Ctx.atoms P { Γ with opened := o }) ((hE.congr { Γ with opened := o } rfl rfl rfl rfl rfl).atomSound hP)
    Γ.σ [] (Ctx.openEqs P { Γ with opened := o } xs) hE.sat (hE.openEqs hP o xs)
  have hwσ := unify_wf _ _ _ [] _ _ (fun e t he => hE.wf.σ e t he) hu
  exact hE.modify rfl (hun.1 _ hu) hE.chrono ⟨hE.wf.tys, hwσ, hE.wf.ς, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩

theorem EnvOK.openFail (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {m : Nat} {oe u nt ex : Bool}
    {ph : List Bool} {M H cs : Tm} (hM : Γ.tys[m]? = some M) (hc : Γ.canon M = .mtbl u nt ex ph H cs)
    (h : ¬ cs.toList.Nodup ∨ unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
      (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .contra) : False := by
  rcases h with hn | hu
  · have hmem : (Tm.mtbl u nt ex ph H cs, H, cs.toList) ∈ Ctx.lists { Γ with opened := (m, oe) :: Γ.opened } Γ.σ := by
      simp only [Ctx.lists, List.filterMap_cons, hM, Option.map_some]
      have : canonBy Γ.σ Γ.ς M = Tm.mtbl u nt ex ph H cs := hc
      simp [this]
    obtain ⟨d, ls, -, -, hks⟩ := (hE.congr { Γ with opened := (m, oe) :: Γ.opened } rfl rfl rfl rfl rfl).lists hE.sat hmem
    apply hn
    have hmap : cs.toList.map (·.subst (Tm.env ρ)) = (List.range cs.toList.length).map (Tm.vc d · ls) := by
      apply List.ext_getElem?; intro i
      simp only [List.getElem?_map]
      cases hi : cs.toList[i]? with
      | none =>
        have : cs.toList.length ≤ i := List.getElem?_eq_none_iff.mp hi
        simp [this]
      | some x =>
        have hl : i < cs.toList.length := (List.getElem?_eq_some_iff.mp hi).1
        simp [List.getElem?_range hl, (hks i x hi).1]
    have : (cs.toList.map (·.subst (Tm.env ρ))).Nodup := by
      rw [hmap]; exact List.Pairwise.map (Tm.vc d · ls) (fun a b hab h => hab (by cases h; rfl)) List.nodup_range
    exact List.Pairwise.of_map (fun x => x.subst (Tm.env ρ)) (fun a b hab h => hab (by rw [h])) this
  · exact (unify_sound (Tm.env ρ) (fun i => Tm.bound_of_lc _ 0 (Tm.env_lc hE.closed i)) Γ.n _
      ((hE.congr { Γ with opened := (m, oe) :: Γ.opened } rfl rfl rfl rfl rfl).atomSound hP)
      Γ.σ [] _ hE.sat (hE.openEqs hP _ _)).2 hu

theorem match_setup (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {s St H idx R : Tm} {er : Bool} {shp : List Arm} {bnd : Nat}
    {brs : List Br} {els : Option Core} {g : Bool → Bool} {ge fe ntf : Bool}
    (hs : TmTy P Γ s St) (hS : Γ.canon St = .app H idx) (hsh : Shape P Γ er H shp ntf)
    (hbr : ∀ c k sig p, shp[c]? = some (k, sig, p) →
      BranchOK P bnd fe { Γ with ghost := g p } s k H idx sig R (lookupBr brs c) els.isSome)
    (hel : ∀ e, els = some e → CoreTy P bnd { Γ with ghost := ge } e R) (hRs : R.static Γ.n 0) :
    ∃ d c ls vs, s.subst (Tm.env ρ) = .app (.vc d c ls) vs ∧ P.isNt d = ntf ∧
      (∃ k sig sig0, shp[c]? = some (k, sig, P.phantom d c) ∧ P.ctor d c = some sig0 ∧ ls.len = P.lifted d ∧
        VTys P ls sig0 (sig.subst (Tm.env ρ)) ∧ sig.isTele) ∧
      ∃ pre body, selectBr brs els c vs.toList = some (pre, body) ∧
      ∃ Γ', CoreTy P bnd Γ' body R ∧ EnvOK P (ρ ++ pre) Γ' ∧ LvlBound (ρ ++ pre) cnt ∧
        MuOK μ Γ' (ρ ++ pre) ∧ R.static Γ'.n 0 ∧ (Γ'.ghost = g (P.phantom d c) ∨ Γ'.ghost = ge) ∧
        (∀ i < Γ.n, Γ'.er i = Γ.er i) ∧
        (∀ sig, P.ctor d c = some sig → ∀ k < pre.length, Γ'.er (Γ.n + k) = (fe || (sig.skip (P.lifted d)).ers.getD k true)) ∧
        ((lookupBr brs c).isSome → ∃ sig, P.ctor d c = some sig ∧ pre.length = (sig.skip (P.lifted d)).len - 1) ∧
        ((∃ e, els = some e ∧ lookupBr brs c = none ∧ body = e ∧ Γ' = { Γ with ghost := ge }) ∨
          ∃ k sig Γf σ, shp[c]? = some (k, sig, P.phantom d c) ∧ lookupBr brs c = some body ∧
            ({ Γ with ghost := g (P.phantom d c) } : Ctx).branch P s k H idx sig = (Γf, .ok σ) ∧
            Γ' = { ({ Γ with ghost := g (P.phantom d c) } : Ctx).advBr P (({ Γ with ghost := g (P.phantom d c) } : Ctx).setErs
              { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)) s k fe (sig.len - 1)
              with cmode := false }) := by
  have hw := hE.wf
  have hl := hE.len
  obtain ⟨hv, hss, hSs⟩ := tm_sound hP hE hs
  have hSs' := canon_static hw hSs
  rw [hS] at hSs'; simp only [Tm.static, Bool.and_eq_true] at hSs'
  rw [← hE.canon St, hS] at hv; simp only [Tm.subst] at hv
  obtain ⟨d, D, ls, hH, hD, hll, hlen, harm, hntd, hco, hop⟩ := hsh.sound hP hE
  rw [hH] at hv
  obtain ⟨c, vs, sig', mid, mk, me, mu, hsv, hctor, hl', hmid, hvs⟩ := hv.ty_inv (fun D' h => by
    rw [hD] at h; cases h; exact ⟨hco, hop⟩) (hP.placed_ne hD hop)
  have hsig' : D.ctors[c]? = some sig' := by simpa [Prog.ctor, hD] using hctor
  obtain ⟨⟨k, sig, p⟩, hshc⟩ : ∃ a, shp[c]? = some a :=
    ⟨_, List.getElem?_eq_getElem (hlen ▸ (List.getElem?_eq_some_iff.mp hsig').1)⟩
  obtain ⟨hk, hks, ⟨sig0, hsigc, hpe⟩, hst, hsigs, rfl⟩ := harm c k sig p hshc
  rw [hsig'] at hsigc; cases hsigc
  have e := hmid.peel; rw [← hpe] at e; subst e
  have hvs0 := hmid
  have hsigT : sig'.isTele := (hP.ctors _ _ _ _ hD hsig').1.isTele
  obtain ⟨hsk1, hsk2, -⟩ := hvs0.skip hsigT
  rw [hl'] at hsk1 hsk2
  have hlen := hvs.len (Tm.isTele_subst _ _ hst)
  rw [Tm.len_subst _ _ (.inl hst)] at hlen
  simp only [Tm.len] at hlen
  have hlc : ∀ v ∈ vs.toList, v.lc 0 := fun v hv' => by
    have : (s.subst (Tm.env ρ)).lc 0 := lc_of_static hE.closed hss
    rw [hsv] at this; simp only [Tm.lc] at this
    exact Tm.lc_toList vs 0 this.2 v hv'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hE.openTele hst hsigs hvs hlc
  have hm' : vs.len = sig.len - 1 := by omega
  rw [hm'] at h1 h2 h3 h4 h5 h6
  generalize hpr : Γ.openTele sig (sig.len - 1) = pr at h1 h2 h3 h4 h5 h6
  obtain ⟨Γf0, rem⟩ := pr
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨Rc, rfl, hRc⟩ := Tm.tele_one h4 h2
  obtain ⟨h1, hx, σn, ςn, hnt⟩ := h1.ntSlot Γ s k
  generalize hΓf : Γ.ntSlot P Γf0 s k = Γf at h1 hx hnt
  have h5 : Γf.n = Γ.n + (sig.len - 1) := by rw [hnt]; exact h5
  have h6 := h6.trans hx
  have hbranch : Γ.branch P s k H idx sig =
      (match unify Γf.n (Γf.atoms P) Γf.σ [] [(Γ.canon s, Γf.canon (.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)] with
        | .ok σ => (({ Γf with σ := σ } : Ctx).forceSlots [(Γ.canon s, Γf.canon (.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)],
            UResult.ok (({ Γf with σ := σ } : Ctx).forceSlots [(Γ.canon s, Γf.canon (.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)]).σ)
        | r => (Γf, r)) := by
    simp only [Ctx.branch, hpr, hΓf] <;> rfl
  have hEf := h1
  have hvl : vs.toList.length = sig.len - 1 := by rw [Tm.len_toList _ hvs.isList, hm']
  have hsat : Sat (Tm.env (ρ ++ vs.toList)) Γ.σ := h6.σ _ (Tm.env_lc hEf.closed) hEf.sat
  have heqs : ∀ p ∈ [(Γ.canon s, Γf.canon (Tm.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)],
      p.1.subst (Tm.env (ρ ++ vs.toList)) = p.2.subst (Tm.env (ρ ++ vs.toList)) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp only
      rw [canon_sound (Γ := Γ) hsat (satS_of_closed hE.wf (Tm.env_lc hEf.closed)), canon_sound hEf.sat hEf.satS,
        Tm.subst_append (hl ▸ hss), hsv, ← hvl]
      simp only [Tm.subst]; rw [Tm.subst_append (hl ▸ hks), hk, fields_subst _ hl, Tm.ofList_toList _ hvs.isList]
    · simp only
      rw [canon_sound (Γ := Γ) hsat (satS_of_closed hE.wf (Tm.env_lc hEf.closed)), canon_sound hEf.sat hEf.satS, hRc,
        Tm.subst_append (t := Tm.app H idx) (by simpa [Tm.static, hl] using hSs')]
      simp [Tm.subst, hH]
  have hun := unify_sound (Tm.env (ρ ++ vs.toList)) (fun i => Tm.bound_of_lc _ 0 (Tm.env_lc hEf.closed i)) Γf.n (Γf.atoms P) (hEf.atomSound hP) Γf.σ [] _ hEf.sat heqs
  refine ⟨d, c, ls, vs, hsv, hntd, ⟨k, sig, sig', hshc, hctor, hl', hvs0, hst⟩, ?_⟩
  have hbr' := hbr c k sig _ hshc
  generalize hbody : lookupBr brs c = br at hbr'
  generalize hei : els.isSome = eb at hbr'
  cases hbr' with
  | dead hd | refuted hd =>
    rw [Ctx.branch_ghost, hbranch] at hd
    split at hd
    · simp at hd
    · exact absurd hd hun.2
  | covered =>
    obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hei
    refine ⟨[], e, by simp [selectBr, hbody], _, hel e rfl, ?_, by simpa using hb, ?_, hRs, .inr rfl,
      fun _ _ => rfl, fun _ _ k hk => absurd hk (Nat.not_lt_zero _), fun h => by simp at h, .inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [List.append_nil]; exact hE.congr _ rfl rfl rfl rfl rfl
    · rw [List.append_nil]; exact hm
  | live hlive hcb =>
    rename_i Γf' body σ'
    have hlive0 := hlive
    rw [Ctx.branch_ghost, hbranch] at hlive
    split at hlive
    rotate_left
    · rename_i hne; simp only [Prod.mk.injEq] at hlive; exact (hne σ' hlive.2).elim
    rename_i σ0 hu
    simp only [Prod.mk.injEq, UResult.ok.injEq] at hlive
    obtain ⟨hΓf', hσ'⟩ := hlive
    have hsσ := hun.1 σ0 hu
    have hwσ := unify_wf Γf.n (Γf.atoms P) Γf.σ [] _ σ0 (fun e t he => hEf.wf.σ e t he) hu
    have hEu := (hEf.modify (Γ' := { Γf with σ := σ0 }) rfl hsσ hEf.chrono
      ⟨hEf.wf.tys, hwσ, hEf.wf.ς, hEf.wf.mints, hEf.wf.cur, hEf.wf.subs⟩).forceSlots [(Γ.canon s, Γf.canon (.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)]
    obtain ⟨σu, ςu, hΓu⟩ := Ctx.forceSlots_eq ({ Γf with σ := σ0 } : Ctx) [(Γ.canon s, Γf.canon (.app k (Γ.fields (sig.len - 1)))), (Γ.canon (.app H idx), Γf.canon Rc)]
    rw [hΓu] at hΓf' hσ' hEu
    subst hΓf' hσ'
    obtain ⟨-, o1, o2⟩ := Ctx.openTele_er (sig.len - 1) Γ sig hst
    rw [hpr] at o1 o2
    replace o1 : ∀ i < Γ.n, Γf.er i = Γ.er i := by rw [hnt]; exact o1
    replace o2 : ∀ k < sig.len - 1, k < sig.ers.length → Γf.er (Γ.n + k) = sig.ers.getD k true := by rw [hnt]; exact o2
    refine ⟨vs.toList, body, by simp [selectBr, hbody], _, hcb, ?_, ?_, ?_, ?_, .inl (by simp),
      fun i hi => by show (Ctx.advBr _ _ _ _ _ _ _).er _ = _; rw [Ctx.advBr_er, Ctx.setErs_er_lt _ _ _ (by simpa [Ctx.n] using hi)]; exact o1 i hi,
      fun sig'' hsig'' k hk => ?_, fun _ => ⟨_, hctor, by rw [hvl, hsk2, Tm.len_subst _ _ (.inl hst)]⟩,
      .inr ⟨k, sig, _, _, hshc, rfl, hlive0, rfl⟩⟩
    rotate_left 4
    · rw [hctor] at hsig''; cases hsig''
      show (Ctx.advBr _ _ _ _ _ _ _).er _ = _; rw [Ctx.advBr_er, hsk1, Tm.ers_subst _ _ hst]
      cases fe
      · exact o2 k (by omega) (by rw [Tm.len_ers _ hst]; omega)
      · simp only [Bool.true_or, Ctx.er_setErs, Ctx.n, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
          List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
    · refine EnvOK.cm false ?_
      refine ((hE.congr { Γ with ghost := g (P.phantom d c) } rfl rfl rfl rfl rfl).advBr hP (by rw [hsk2, Tm.len_subst _ _ (.inl hst)])
        (hEu.congr _
            (by simp) (by simp) (by simp) (by simp) (by simp) (by cases fe <;> simp [Ctx.setErs])
            (by cases fe <;> simp [Ctx.setErs]) (hς := by cases fe <;> simp [Ctx.setErs]))
        (by cases fe <;> simp [Ctx.setErs, h6.fixed]) hsv rfl (by rw [hvl]) hctor hsk1 (fun j hj => ?_) hk)
      rw [Tm.ers_subst _ _ hst]
      cases fe
      · exact o2 j (by omega) (by rw [Tm.len_ers _ hst]; omega)
      · simp only [Bool.true_or, Ctx.er_setErs, Ctx.n, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
          List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
    · refine LvlBound.append.mpr ⟨hb, fun v hv' x hx => ?_⟩
      have := hb.subst hss x; rw [hsv] at this
      exact this (by simp only [Tm.levels]; exact List.mem_append_right _ (Tm.levels_toList vs v hv' x hx))
    · exact hm.append hw hl (by simp [h6.cur]) (by simp [h6.subs])
    · exact Tm.static_mono (by simp only [Ctx.n] at h5 ⊢; simp only [Ctx.advBr_tys, Ctx.setErs]; split <;> simp <;> omega) _ (Nat.le_refl 0) hRs
  | fixedOut _ hx hkk hne hnt =>
    have := (hE.congr { Γ with ghost := g (P.phantom d c) } rfl rfl rfl rfl rfl).known hkk hk
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨w, hx, hwv⟩ := Option.map_eq_some_iff.mp hx
    have hR := hE.fix.2 _ _ hx
    simp only [Tm.subst] at hsv; rw [hsv] at hR
    obtain ⟨_, _, e1, _⟩ := hR.con_inv hnt
    rw [hwv] at e1
    simp only [Tm.app.injEq, Tm.vc.injEq] at e1
    obtain ⟨⟨-, hc0, -⟩, -⟩ := e1
    have := (hE.congr { Γ with ghost := g (P.phantom d c) } rfl rfl rfl rfl rfl).known hkk hk
    exact absurd (this.2.symm.trans hc0.symm) hne

theorem noRet_select {brs : List Br} {els : Option Core} {c : Nat} {vs pre : List Tm}
    {body : Core} (h : selectBr brs els c vs = some (pre, body)) (hb : Core.armsNoRet brs = true)
    (he : Core.optNoRet els = true) : body.noRet = true := by
  unfold selectBr at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    unfold lookupBr at hl; simp only [Option.map_eq_some_iff] at hl
    obtain ⟨⟨x, y, w, z⟩, hf, rfl⟩ := hl
    have hmem := List.mem_of_find?_eq_some hf
    clear hf
    induction brs with
    | nil => simp at hmem
    | cons a t ih =>
      simp only [Core.armsNoRet, Bool.and_eq_true] at hb
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact hb.1
      · exact ih hb.2 hm
  · cases els <;> simp at h
    obtain ⟨-, rfl⟩ := h
    simpa [Core.optNoRet] using he

theorem noRet_eval : ∀ μ ρ cnt c, c.noRet = true → ∀ r, eval P μ ρ cnt c ≠ .ok r := by
  intro μ ρ cnt c
  induction μ, ρ, cnt, c using eval.induct P with
  | case1 => intro h; simp [Core.noRet] at h
  | case2 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu outs cnt1 hev ihb ihr =>
    intro h r e
    rw [eval] at e; simp only [hcal] at e; rw [dif_pos hmu] at e; simp only [argv, μ'] at hev; simp only [hev] at e
    exact ihr (by simpa [Core.noRet] using h) r e
  | case3 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu e' hev ihb =>
    intro h r e
    rw [eval] at e; simp only [hcal] at e; rw [dif_pos hmu] at e; simp only [argv, μ'] at hev; simp only [hev] at e
    cases e
  | case4 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu =>
    intro h r e
    rw [eval] at e; simp only [hcal] at e; rw [dif_neg hmu] at e; cases e
  | case5 μ ρ cnt f dec args er ms ve rest hcal =>
    intro h r e
    rw [eval] at e; simp only [hcal] at e; cases e
  | case7 μ ρ cnt s R brs els er rest d c ls vs hs pre body hb e' hev ihb =>
    intro h r e
    rw [eval] at e; simp only [hs] at e
    split at e
    · rename_i pre' body' hb'
      rw [hb] at hb'; cases hb'
      simp only [hev] at e; cases e
    · simp at e
  | case6 μ ρ cnt s R brs els er rest d c ls vs hs pre body hb outs cnt1 hev ihb ihr =>
    intro h r e
    rw [eval] at e; simp only [hs] at e
    split at e
    · rename_i pre' body' hb'
      rw [hb] at hb'; cases hb'
      simp only [hev] at e
      exact ihr (by simpa [Core.noRet] using h) r e
    · simp at e
  | case8 μ ρ cnt s R brs els er rest d c ls vs hs hb =>
    intro h r e
    rw [eval] at e; simp only [hs] at e
    split at e
    · rename_i hb'; rw [hb] at hb'; cases hb'
    · cases e
  | case20 μ ρ cnt s brs els er nt d c ls vs hs hb =>
    intro h r e
    rw [eval] at e; simp only [hs] at e
    split at e
    · rename_i hb'; rw [hb] at hb'; cases hb'
    · cases e
  | case22 μ ρ cnt R body rest outs cnt1 hev ihb ihr =>
    intro h r e
    simp only [Core.noRet, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ihb h _ hev
    · rw [eval] at e; simp only [hev] at e; exact ihr h r e
  | case23 μ ρ cnt R body rest e0 hev ihb =>
    intro h r e
    rw [eval] at e; simp only [hev] at e; cases e
  | case10 μ ρ cnt p er rest ih =>
    intro h r e; rw [eval] at e; exact ih (by simpa [Core.noRet] using h) r e
  | case11 μ ρ cnt w req rest ih =>
    intro h r e; rw [eval] at e; exact ih (by simpa [Core.noRet] using h) r e
  | case12 μ ρ cnt rest ih =>
    intro h r e; rw [eval] at e; exact ih (by simpa [Core.noRet] using h) r e
  | case13 μ ρ cnt gid rest G hG ih =>
    intro h r e; rw [eval, hG] at e; exact ih (by simpa [Core.noRet] using h) r e
  | case15 μ ρ cnt k a b rest ih =>
    intro h r e; rw [eval] at e; exact ih (by simpa [Core.noRet] using h) r e
  | case19 μ ρ cnt s brs els er nt d c ls vs hs pre body hb ih =>
    intro h r e
    simp only [Core.noRet, Bool.and_eq_true] at h
    rw [eval] at e; simp only [hs] at e
    split at e
    · rename_i pre' body' hb'
      rw [hb] at hb'; cases hb'
      exact ih (noRet_select hb h.1 h.2) r e
    · simp at e
  | _ =>
    intro _ r e
    rw [eval] at e
    first
      | simp_all
      | (split at e <;> simp_all)
      | (simp only [*] at e; simp at e)

theorem eval_real {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {c : Core} {r : List Tm × Nat}
    (h : eval P μ ρ cnt c = .ok r) : c.real = true := by
  simp only [Core.real, Bool.not_eq_eq_eq_not, Bool.not_true]
  cases hn : c.noRet
  · rfl
  · exact absurd h (noRet_eval _ _ _ _ hn r)

theorem armsOK_mem {Γ : Ctx} {shp : List Arm} {brs : List Br} (h : armsOK Γ shp brs = true) {e : Br}
    (he : e ∈ brs) : ∃ k sig p, shp[e.2.1]? = some (k, sig, p) ∧ e.1 = sig.len - 1 := by
  have := List.all_eq_true.mp h e he
  obtain ⟨n, c, k, b⟩ := e
  simp only at this ⊢
  split at this
  · rename_i k sig p hs; simp only [Bool.and_eq_true, beq_iff_eq] at this; exact ⟨k, sig, p, hs, this.1⟩
  · cases this

theorem realBr_of_select {brs : List Br} {els : Option Core} {c : Nat} {vs pre : List Tm}
    {body : Core} (h : selectBr brs els c vs = some (pre, body)) (hr : body.real = true)
    (hc : realCount brs els ≤ 1) :
    (∃ n k, (n, c, k, body) ∈ brs ∧ lookupBr brs c = some body ∧ realBr brs els = some (List.replicate n .tok, body)) ∨
    (pre = [] ∧ realBr brs els = some ([], body)) := by
  unfold selectBr at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hb' := hb
    unfold lookupBr at hb; simp only [Option.map_eq_some_iff] at hb
    obtain ⟨⟨x, y, w, z⟩, hf, hz⟩ := hb
    simp only at hz; subst hz
    have hmem := List.mem_of_find?_eq_some hf
    have hy : y = c := by simpa using List.find?_some hf
    subst hy
    refine .inl ⟨x, w, hmem, hb', ?_⟩
    have hin : (x, y, w, z) ∈ brs.filter (·.2.2.2.real) := List.mem_filter.mpr ⟨hmem, by simpa using hr⟩
    have hlen : (brs.filter (·.2.2.2.real)).length ≤ 1 := by unfold realCount at hc; omega
    have hfl : brs.filter (·.2.2.2.real) = [(x, y, w, z)] := by
      generalize brs.filter (·.2.2.2.real) = l at hin hlen
      match l, hin, hlen with
      | [a], hin, _ => simp at hin; simp [hin]
      | [], hin, _ => simp at hin
      | _ :: _ :: _, _, hlen => simp at hlen
    unfold realBr; rw [hfl]
  · cases els <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    refine .inr ⟨rfl, ?_⟩
    have : brs.filter (·.2.2.2.real) = [] := by
      rename_i e
      have h1 : ((some e).filter Core.real).isSome.toNat = 1 := by simp [Option.filter, hr]
      unfold realCount at hc; exact List.length_eq_zero_iff.mp (by omega)
    unfold realBr; rw [this]

theorem ctor_tele (hP : ProgOK P) {d c : Nat} {sig : Tm} (h : P.ctor d c = some sig) : sig.isTele := by
  obtain ⟨D, hD, hs⟩ := Option.bind_eq_some_iff.mp h
  exact (hP.ctors _ _ _ _ hD hs).1.isTele

theorem no_value_of_empty {v : Tm} {d : Nat} {D : Adt} {args ls : Tm} (hD : P.adts[d]? = some D)
    (hempty : D.ctors = []) (hco : D.coercible = false) (hop : D.opq = false) (hpl : P.placedD ≠ some d) :
    ¬ VTy P v (.app (.tyc d ls) args) := by
  intro h
  obtain ⟨c, vs, sig, _, mk, me, _, _, hc, _⟩ := h.ty_inv (fun D' h => by rw [hD] at h; cases h; exact ⟨hco, hop⟩) hpl
  simp [Prog.ctor, hD, hempty] at hc

def Sim (P : Prog) (Γ : Ctx) (ρ : List Tm) (c : Core) (rets : Tm) (r : Except String (List Tm × Nat)) : Prop :=
  Γ.ghost = false → ∀ ρS, SimEnv P Γ.er ρS ρ → ∀ vs cnt', r = .ok (vs, cnt') →
    ∃ vsS, RunS P ρS c vsS ∧ Reals P (.ofList vsS) (.ofList vs) rets

theorem SimEnv.pushTele {Γ : Ctx} {ρS ρ outsS outs : List Tm} (hS : SimEnv P Γ.er ρS ρ) (hl : ρ.length = Γ.n)
    {R : Tm} (hR : R.isTele) (ov : Option (List Bool)) (hlen : outs.length = R.len)
    (hlS : outsS.length = outs.length)
    (hr : ∀ k a b, outsS[k]? = some a → outs[k]? = some b → (ov.getD R.ers).getD k true = false → Real P a b) :
    SimEnv P (Γ.pushTele R ov).er (ρS ++ outsS) (ρ ++ outs) := by
  obtain ⟨-, h1, h2⟩ := Ctx.pushTele_er Γ R ov hR
  refine hS.extend hlS (fun i hi => h1 i (hl ▸ hi)) fun k a b ha hb he => hr k a b ha hb ?_
  have hk : k < R.len := hlen ▸ (List.getElem?_eq_some_iff.mp hb).1
  rw [← h2 k hk, ← hl]; exact he

theorem Reals.ofList_subst (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) {ts tele : Tm} (hl : ts.isList)
    (h : rtArgs P Γ ts tele = true) :
    Reals P (.ofList (ts.toList.map (P.sub ρS))) (.ofList (ts.toList.map (·.subst (Tm.env ρ)))) tele := by
  rw [← Tm.toList_subst _ _ hl, Tm.ofList_toList _ (Tm.isList_subst _ _ hl)]
  have := rtArgs_reals hP hE hS ts tele h
  rwa [Prog.subUArgs_subst _ _ hl] at this

theorem Reals.list {a b t : Tm} (h : Reals P a b t) : ∀ k x y, a.toList[k]? = some x → b.toList[k]? = some y →
    t.ers.getD k true = false → Real P x y := h.get

def HeadSim (P : Prog) (Γ Γ' : Ctx) (ρ outs : List Tm) (c rest : Core) : Prop :=
  ∀ ρS, Γ.ghost = false → SimEnv P Γ.er ρS ρ → ∃ outsS, (∀ vs', stepS P ρS c = some vs' → vs' = outsS) ∧
    (∀ out, RunS P (ρS ++ outsS) rest out → RunS P ρS c out) ∧ outsS.length = outs.length ∧
    ∀ k a b, outsS[k]? = some a → outs[k]? = some b → Γ'.er (Γ.n + k) = false → Real P a b

theorem EnvOK.adv {ρ outs : List Tm} {Γ Γ' : Ctx} {c rest : Core} (hE : EnvOK P ρ Γ) (hE' : EnvOK P (ρ ++ outs) Γ')
    (hf : Γ'.fixed = Γ.fixed) (hh : HeadSim P Γ Γ' ρ outs c rest) : EnvOK P (ρ ++ outs) (Ctx.adv P Γ Γ' c) := by
  unfold Ctx.adv
  split
  · rename_i hr
    obtain ⟨hS, hg, _⟩ := hE.ready_sim hr
    obtain ⟨outsS, hst, _, hlen, hre⟩ := hh _ hg hS
    split
    · rename_i vs hvs
      cases hst vs hvs
      exact hE.record hE' hf hr hlen hre
    · exact hE'
  · exact hE'

theorem HeadSim.finish {ρ outs : List Tm} {Γ Γ' : Ctx} {c rest : Core} {rets : Tm} {r : Except String (List Tm × Nat)}
    (hE : EnvOK P ρ Γ) (hlo : ∀ i < Γ.n, Γ'.er i = Γ.er i) (hg' : Γ.ghost = false → Γ'.ghost = false)
    (hh : HeadSim P Γ Γ' ρ outs c rest) (hsim : Sim P (Ctx.adv P Γ Γ' c) (ρ ++ outs) rest rets r) :
    Sim P Γ ρ c rets r := by
  intro hg ρS hS vs cnt' hr
  obtain ⟨outsS, _, comp, hlen, hre⟩ := hh ρS hg hS
  have hl := hE.len
  obtain ⟨vsS, hrun, hres⟩ := hsim (by simpa using hg' hg) _
    (by simpa using hS.extend hlen (fun i hi => hlo i (hl ▸ hi)) fun k a b ha hb he => hre k a b ha hb (hl ▸ he))
    vs cnt' hr
  exact ⟨vsS, comp _ hrun, hres⟩

theorem runS_det {ρ : List Tm} {c : Core} {n : Nat} {out out' : List Tm} (h : runS P n ρ c = some out)
    (h' : RunS P ρ c out') : out = out' := (runS_sound _ _ _ _ h).det h'

theorem seq_setup {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {Γ : Ctx} {R rets : Tm} {body rest : Core} {outs : List Tm}
    {cnt1 : Nat} (hE : EnvOK P ρ Γ) (hlb : LvlBound ρ cnt) (hm : MuOK μ Γ ρ) (hrs : rets.static Γ.n 0)
    (hRs : R.static Γ.n 0) (hRt : R.isTele)
    (hres : Result P ρ cnt R (eval P μ ρ cnt body) ∧ Sim P Γ ρ body R (eval P μ ρ cnt body))
    (hev : eval P μ ρ cnt body = .ok (outs, cnt1)) :
    EnvOK P (ρ ++ outs) (Ctx.adv P Γ (Γ.pushTele R) (.seq R body rest)) ∧ LvlBound (ρ ++ outs) cnt1 ∧
    MuOK μ (Ctx.adv P Γ (Γ.pushTele R) (.seq R body rest)) (ρ ++ outs) ∧
    rets.static (Ctx.adv P Γ (Γ.pushTele R) (.seq R body rest)).n 0 ∧
    HeadSim P Γ (Γ.pushTele R none) ρ outs (.seq R body rest) rest ∧ cnt ≤ cnt1 ∧ outs.length = R.len := by
  obtain ⟨⟨outs', c', e, hvs, hbv, hle, hlc⟩, hsb⟩ := hres
  rw [hev] at e; cases e
  have hl := hE.len
  have hol : outs.length = R.len := by
    have := hvs.len (Tm.isTele_subst _ _ hRt)
    rw [Tm.len_subst _ _ (.inl hRt), ← Tm.len_toList _ hvs.isList, Tm.toList_ofList] at this; simpa [Tm.len] using this
  obtain ⟨hE'', hcur, hsubs, hnle⟩ := hE.pushTele none hRt hRs hvs hlc
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er Γ R none hRt
  have hh : HeadSim P Γ (Γ.pushTele R none) ρ outs (.seq R body rest) rest := by
    intro ρS hg hS
    obtain ⟨outsS, hrunb, hreb⟩ := hsb hg ρS hS outs cnt1 hev
    refine ⟨outsS, fun vs' h => runS_det (by simpa [stepS] using h) hrunb, fun out h => .seq hrunb h,
      by simpa [Tm.toList_ofList] using hreb.len, fun k a b ha hb he => ?_⟩
    rw [hpn k (hol ▸ (List.getElem?_eq_some_iff.mp hb).1)] at he
    exact hreb.get k a b (by simpa [Tm.toList_ofList] using ha) (by simpa [Tm.toList_ofList] using hb) (by simpa using he)
  exact ⟨hE.adv hE'' (by simp) hh, LvlBound.append.mpr ⟨hlb.mono hle, hbv⟩,
    hm.append hE.wf hl (by simpa using hcur) (by simpa using hsubs), Tm.static_mono (by simpa using hnle) _ (Nat.le_refl 0) hrs,
    hh, hle, hol⟩

theorem Real.wld_inv {x : Tm} {k : Nat} (h : Real P x (.wld k)) : x = .wld k := by
  cases h with
  | world => rfl
  | other _ _ _ h4 => exact absurd rfl (h4 k)
  | nat he h =>
    rename_i n
    cases n <;> simp only [Prog.view, he] at h <;> cases h <;> simp_all

theorem Real.ctor_inv {x ls vs : Tm} {d c : Nat} (h : Real P x (.app (.vc d c ls) vs)) (hnt : P.isNt d = false)
    (hn : P.natD ≠ some d) : ∃ vsS, x = .app (.vc d c .nil) vsS := by
  cases h with
  | con => exact ⟨_, rfl⟩
  | wrap hw => rw [Prog.wrapField_none hnt] at hw; cases hw
  | other h1 => exact absurd rfl (h1 _ _ _ _)
  | nat he h =>
    rename_i n
    cases n <;> simp only [Prog.view, he] at h <;> cases h <;> (try simp_all) <;>
      first | (rename_i h; exact h _ _ _ _ rfl rfl rfl rfl) | (rename_i hw _; rw [Prog.wrapField_none hnt] at hw; cases hw)

theorem EnvOK.sem (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {t T : Tm} (ht : TmTy P Γ t T) :
    VTy P (t.subst (Tm.env ρ)) ((Γ.canon T).subst (Tm.env ρ)) := by
  rw [hE.canon]; exact (tm_sound hP hE ht).1

theorem world_args (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {w req T : Tm}
    (hp : PrimTy P Γ (.wAsk w req) T) :
    ∃ k rd c ls vs ls', w.subst (Tm.env ρ) = .wld k ∧ P.requestD = some rd ∧ req.subst (Tm.env ρ) = .app (.vc rd c ls) vs ∧
      VTy P (.app (.vc rd c ls) vs) (.app (.tyc rd ls') (.cons (T.subst (Tm.env ρ)) .nil)) := by
  cases hp with
  | wAsk hwd hrd hw hW hr hR =>
    have vw := hE.sem hP hw; rw [hW] at vw; simp only [Tm.subst] at vw
    obtain ⟨k, hk⟩ := vw.world_inv hP hwd
    have vr := hE.sem hP hr; rw [hR] at vr; simp only [Tm.subst] at vr
    obtain ⟨⟨D, hD, hop, hco, -⟩, hpl, -⟩ := hP.request _ hrd
    obtain ⟨c, vs, -, -, -, -, -, he, -⟩ := vr.ty_inv (fun D' h => by rw [hD] at h; cases h; exact ⟨hco, hop⟩) hpl
    exact ⟨k, _, c, _, vs, _, hk, hrd, he, he ▸ vr⟩

theorem world_strip (hP : ProgOK P) {ρ ρS : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ)
    (hS : SimEnv P Γ.er ρS ρ) {w req A : Tm} (hpa : PrimTy P Γ (.wAsk w req) A)
    (hrt : (rt P Γ w && rt P Γ req) = true) :
    ∃ k rd c ls vs vsS, w.subst (Tm.env ρ) = .wld k ∧ P.sub ρS w = .wld k ∧ P.requestD = some rd ∧
      req.subst (Tm.env ρ) = .app (.vc rd c ls) vs ∧ P.sub ρS req = .app (.vc rd c .nil) vsS ∧
      ∃ ls', VTy P (.app (.vc rd c ls) vs) (.app (.tyc rd ls') (.cons (A.subst (Tm.env ρ)) .nil)) := by
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨k, rd, c, ls, vs, ls', hk, hrd, he, hv⟩ := world_args hP hE hpa
  have hRw := rt_real hP hE hS w hrt.1; rw [hk] at hRw
  have hRr := rt_real hP hE hS req hrt.2; rw [he] at hRr
  obtain ⟨⟨D, hD, -, -, hnt⟩, -, hn⟩ := hP.request _ hrd
  obtain ⟨vsS, hx⟩ := hRr.ctor_inv (by simp [Prog.isNt, hD, hnt]) hn
  exact ⟨k, rd, c, ls, vs, vsS, hk, hRw.wld_inv, hrd, he, hx, ls', hv⟩

theorem world_real (hP : ProgOK P) (hO : P.OracleOK) {ρ ρS : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ)
    (hS : SimEnv P Γ.er ρS ρ) {w req A : Tm} (hpa : PrimTy P Γ (.wAsk w req) A)
    (hrt : (rt P Γ w && rt P Γ req) = true) :
    Real P ((Prim.wNext w).evalS P ρS) ((Prim.wNext w).eval P ρ) ∧
      Real P ((Prim.wAsk w req).evalS P ρS) ((Prim.wAsk w req).eval P ρ) := by
  obtain ⟨k, rd, c, ls, vs, vsS, hk, hkS, hrd, he, hx, ls', hv⟩ := world_strip hP hE hS hpa hrt
  refine ⟨?_, ?_⟩
  · simp only [Prim.evalS, Prim.eval, hk, hkS, Tm.wnext]; exact .world
  · simp only [Prim.evalS, Prim.eval, hk, he, hkS, hx, Prog.answer]
    exact (hO.typed k c _ _ _ _ _ hrd hv).2

theorem prim_real (hP : ProgOK P) {ρ ρS : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ)
    (hS : SimEnv P Γ.er ρS ρ) {p : Prim} {T : Tm}
    (hp : PrimTy P Γ p T) (hrt : p.rt P Γ = true) : Real P (p.evalS P ρS) (p.eval P ρ) := by
  cases p with
  | tm t | lit t | place t _ | unplace t _ => exact rt_real hP hE hS t hrt
  | coerce a b p =>
    cases hp with
    | coerce hpp e hD hc ha _ hb' _ =>
      rename_i Pt _ _ _ _ _ _ _ _ _ _
      have hR := rt_real hP hE hS a hrt
      have v := (tm_sound hP hE hpp).1
      rw [← hE.canon Pt, e, Tm.coer_subst] at v
      have eqc : ∀ {x y : Tm}, Γ.canon x = Γ.canon y → x.subst (Tm.env ρ) = y.subst (Tm.env ρ) :=
        fun h => by rw [← hE.canon, h, hE.canon]
      simp only [Prim.evalS, Prim.eval]
      rw [eqc ha] at hR; rw [eqc hb']
      exact ((v.coer_inv hP hD hc).1 _).mp hR
  | assert => simp [Prim.rt] at hrt
  | num d n => cases hp with | num h => exact natTm_real h n
  | placedSlot | placedEq | wAsk | wNext => simp [Prim.rt] at hrt
  | _ => exact .other (by simp [Prim.eval]) (by simp [Prim.eval]) (by simp [Prim.eval]) (by simp [Prim.eval])

theorem prim_setup (hP : ProgOK P) (hO : P.OracleOK) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {Γ : Ctx} {p : Prim} {er : Bool}
    {T rets : Tm} {rest : Core} (hE : EnvOK P ρ Γ) (hb : LvlBound ρ cnt) (hm : MuOK μ Γ ρ) (hrs : rets.static Γ.n 0)
    (hp : PrimTy P Γ p T) (hok : (er || Γ.ok (p.rt P Γ)) = true) :
    EnvOK P (ρ ++ [p.eval P ρ]) (Ctx.adv P Γ (Γ.pushPrim P T er p) (.prim p er rest)) ∧ LvlBound (ρ ++ [p.eval P ρ]) cnt ∧
    MuOK μ (Ctx.adv P Γ (Γ.pushPrim P T er p) (.prim p er rest)) (ρ ++ [p.eval P ρ]) ∧
    rets.static (Ctx.adv P Γ (Γ.pushPrim P T er p) (.prim p er rest)).n 0 ∧
    HeadSim P Γ (Γ.pushPrim P T er p) ρ [p.eval P ρ] (.prim p er rest) rest ∧
    ∀ i, (Γ.pushPrim P T er p).er i = if i = Γ.n then er else Γ.er i := by
  obtain ⟨hv, hT, hlc, hlv⟩ := prim_sound hP hO hE hb hp
  obtain ⟨hE', hcur, hsubs, hn⟩ := hE.pushPrim hP hp hv hT hlc rfl
  have hl := hE.len
  have her : ∀ i, (Γ.pushPrim P T er p).er i = if i = Γ.n then er else Γ.er i := by
    intro i; simp only [Ctx.pushPrim, Ctx.slotIf_er]; show (Γ.pushPrim0 T er p).er i = _; cases p <;> simp [Ctx.pushPrim0]
  have hh : HeadSim P Γ (Γ.pushPrim P T er p) ρ [p.eval P ρ] (.prim p er rest) rest := by
    intro ρS hg hS
    refine ⟨[if er then .tok else p.evalS P ρS], fun vs' h => by simp [stepS] at h; exact h.symm,
      fun out h => .prim h, rfl, fun k a b ha hb he => ?_⟩
    cases k with
    | succ => simp at ha
    | zero =>
      simp at ha hb; subst ha hb
      rw [her, if_pos (by omega)] at he; subst he
      simp only [Ctx.ok, hg, Bool.false_or] at hok
      exact prim_real hP hE hS hp hok
  have hpf : (Γ.pushPrim P T er p).fixed = Γ.fixed := by
    simp only [Ctx.pushPrim, Ctx.slotIf_fixed]; cases p <;> simp [Ctx.pushPrim0, Ctx.withRule, Ctx.push]
  exact ⟨hE.adv hE' hpf hh, LvlBound.append.mpr ⟨hb, by simpa [LvlBound] using hlv⟩,
    hm.append hE.wf hl (by simpa using hcur) (by simpa using hsubs), Tm.static_mono (by simp; omega) _ (Nat.le_refl 0) hrs,
    hh, her⟩

theorem wdo_setup (hP : ProgOK P) (hO : P.OracleOK) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {Γ : Ctx}
    {w req Tw A rets : Tm} {rest : Core} (hE : EnvOK P ρ Γ) (hb : LvlBound ρ cnt) (hm : MuOK μ Γ ρ)
    (hrs : rets.static Γ.n 0) (hw : PrimTy P Γ (.wNext w) Tw) (ha : PrimTy P Γ (.wAsk w req) A)
    (hok : Γ.ok (rt P Γ w && rt P Γ req) = true) :
    EnvOK P (ρ ++ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ])
        (Ctx.adv P Γ (Γ.pushWdo Tw A w) (.wdo w req rest)) ∧
      LvlBound (ρ ++ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]) cnt ∧
      MuOK μ (Ctx.adv P Γ (Γ.pushWdo Tw A w) (.wdo w req rest))
        (ρ ++ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]) ∧
      rets.static (Ctx.adv P Γ (Γ.pushWdo Tw A w) (.wdo w req rest)).n 0 ∧
      HeadSim P Γ (Γ.pushWdo Tw A w) ρ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]
        (.wdo w req rest) rest ∧
      ∀ i, (Γ.pushWdo Tw A w).er i = if i = Γ.n + 1 then false else if i = Γ.n then false else Γ.er i := by
  obtain ⟨v1, s1, c1, l1⟩ := prim_sound hP hO hE hb hw
  obtain ⟨v2, s2, c2, l2⟩ := prim_sound hP hO hE hb ha
  have hl := hE.len
  have hE1 := (hE.push v1 s1 c1 (e := false)).slotIf w.varSlot.isSome (e := Γ.n) (Γ.canon (w.varSlot.getD .nil))
  have hE2 := hE1.push (v := (Prim.wAsk w req).eval P ρ) (A := A)
    (by rw [Tm.subst_append (hl ▸ s2)]; exact v2)
    (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) s2) c2 (e := false)
  have her : ∀ i, (Γ.pushWdo Tw A w).er i = if i = Γ.n + 1 then false else if i = Γ.n then false else Γ.er i := by
    exact Ctx.er_pushWdo Γ Tw A w
  have hh : HeadSim P Γ (Γ.pushWdo Tw A w) ρ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]
      (.wdo w req rest) rest := by
    intro ρS hg hS
    simp only [Ctx.ok, hg, Bool.false_or] at hok
    refine ⟨[(Prim.wNext w).evalS P ρS, (Prim.wAsk w req).evalS P ρS], fun vs' h => by simp [stepS] at h,
      fun out h => .wdo (by simpa using h), rfl, fun k a b ha' hb' _ => ?_⟩
    have hR := world_real hP hO hE hS ha hok
    match k, ha', hb' with
    | 0, ha', hb' => simp at ha' hb'; subst ha' hb'; exact hR.1
    | 1, ha', hb' => simp at ha' hb'; subst ha' hb'; exact hR.2
    | _ + 2, ha', _ => simp at ha'
  have hn : (Γ.pushWdo Tw A w).n = Γ.n + 2 := by simp [Ctx.pushWdo, Ctx.push, Ctx.n]
  have hE2' : EnvOK P (ρ ++ [(Prim.wNext w).eval P ρ, (Prim.wAsk w req).eval P ρ]) (Γ.pushWdo Tw A w) := by
    simpa [Ctx.pushWdo] using hE2
  refine ⟨hE.adv hE2' (by simp [Ctx.pushWdo, Ctx.push]) hh, LvlBound.append.mpr ⟨hb, ?_⟩, hm.append hE.wf hl (by simp [Ctx.pushWdo, Ctx.push]) (by simp [Ctx.pushWdo, Ctx.push]),
    Tm.static_mono (by simp [hn]) _ (Nat.le_refl 0) hrs, hh, her⟩
  intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact l1
  · exact l2

theorem mtch_setup (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {Γ Γ' : Ctx} {s R rets : Tm}
    {brs : List Br} {els : Option Core} {er ntf : Bool} {rest body : Core} {d c : Nat} {ls vs : Tm} {pre outs : List Tm}
    {cnt1 : Nat} (hE : EnvOK P ρ Γ) (hlb : LvlBound ρ cnt) (hm : MuOK μ Γ ρ) (hrs : rets.static Γ.n 0)
    (hRs : R.static Γ.n 0) (hRt : R.isTele) (hok : (er || Γ.ok (rt P Γ s)) = true) (hnt : (er || !ntf) = true)
    (hs : s.subst (Tm.env ρ) = .app (.vc d c ls) vs) (hb : selectBr brs els c vs.toList = some (pre, body))
    (hev : eval P μ (ρ ++ pre) cnt body = .ok (outs, cnt1)) (hntd : P.isNt d = ntf)
    (hg' : Γ'.ghost = (Γ.ghost || er || P.phantom d c) ∨ Γ'.ghost = (Γ.ghost || er))
    (he1 : ∀ i < Γ.n, Γ'.er i = Γ.er i)
    (he2 : ∀ sig, P.ctor d c = some sig → ∀ k < pre.length,
      Γ'.er (Γ.n + k) = (false || (sig.skip (P.lifted d)).ers.getD k true))
    (hres : Result P (ρ ++ pre) cnt R (eval P μ (ρ ++ pre) cnt body) ∧ Sim P Γ' (ρ ++ pre) body R (eval P μ (ρ ++ pre) cnt body)) :
    EnvOK P (ρ ++ outs) (Ctx.adv P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none))
      (.mtch s R brs els er rest)) ∧ LvlBound (ρ ++ outs) cnt1 ∧
    MuOK μ (Ctx.adv P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) (.mtch s R brs els er rest))
      (ρ ++ outs) ∧
    rets.static (Ctx.adv P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none))
      (.mtch s R brs els er rest)).n 0 ∧
    HeadSim P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) ρ outs (.mtch s R brs els er rest) rest ∧
    cnt ≤ cnt1 ∧ outs.length = R.len := by
  obtain ⟨⟨outs', c', e, hvs, hbv, hle, hlc⟩, hsb⟩ := hres
  rw [hev] at e; cases e
  have hl := hE.len
  rw [Tm.subst_append (hl ▸ hRs)] at hvs
  have hol : outs.length = R.len := by
    have := hvs.len (Tm.isTele_subst _ _ hRt)
    rw [Tm.len_subst _ _ (.inl hRt), ← Tm.len_toList _ hvs.isList, Tm.toList_ofList] at this; simpa [Tm.len] using this
  obtain ⟨hE'', hcur, hsubs, hnle⟩ := hE.pushTele (if er then some (List.replicate R.len true) else none) hRt hRs hvs hlc
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er Γ R (if er then some (List.replicate R.len true) else none) hRt
  have hh : HeadSim P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) ρ outs
      (.mtch s R brs els er rest) rest := by
    intro ρS hg hS
    cases er with
    | true =>
      refine ⟨List.replicate R.len .tok, fun vs' h => by simp [stepS] at h; exact h.symm,
        fun out h => .mtchE h, by simp [hol], fun k a b _ hb he => ?_⟩
      rw [hpn k (hol ▸ (List.getElem?_eq_some_iff.mp hb).1)] at he
      simp only [if_true, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_replicate] at he
      split at he <;> simp at he
    | false =>
      simp only [Ctx.ok, hg, Bool.false_or] at hok
      have hR := rt_real hP hE hS s hok; rw [hs] at hR
      obtain ⟨vsS, sig, hsS, hsig, hph, hrv⟩ := hR.con_inv (by rw [hntd]; simpa using hnt)
      have hgb : Γ'.ghost = false := by rcases hg' with h | h <;> rw [h, hg] <;> simp [hph]
      have hSb : ∃ preS, selectBr brs els c vsS.toList = some (preS, body) ∧
          SimEnv P Γ'.er (ρS ++ preS) (ρ ++ pre) := by
        rcases selectBr_same (vs' := vsS.toList) hb with ⟨rfl, hsel⟩ | ⟨rfl, hsel⟩
        · refine ⟨_, hsel, hS.extend hrv.len (fun i hi => he1 i (hl ▸ hi)) fun k a b ha hb he => ?_⟩
          rw [hl, he2 sig hsig k (List.getElem?_eq_some_iff.mp hb).1, Bool.false_or] at he
          exact hrv.get k a b ha hb he
        · exact ⟨_, hsel, hS.extend rfl (fun i hi => he1 i (hl ▸ hi)) fun k _ _ h => by simp at h⟩
      obtain ⟨preS, hsel, hSb⟩ := hSb
      obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _ hSb outs cnt1 hev
      refine ⟨outsS, fun vs' h => ?_, fun out h => .mtch hsS hsel hrunb h,
        by simpa [Tm.toList_ofList] using hreb.len, fun k a b ha hb he => ?_⟩
      · simp only [stepS, hsS, hsel, Option.bind_eq_bind, Option.bind_some] at h
        exact runS_det (by rwa [runA_toArray] at h) hrunb
      · rw [hpn k (hol ▸ (List.getElem?_eq_some_iff.mp hb).1)] at he
        exact hreb.get k a b (by simpa [Tm.toList_ofList] using ha)
          (by simpa [Tm.toList_ofList] using hb) (by simpa using he)
  exact ⟨hE.adv hE'' (by simp) hh, LvlBound.append.mpr ⟨hlb.mono hle, hbv⟩,
    hm.append hE.wf hl (by simpa using hcur) (by simpa using hsubs), Tm.static_mono (by simpa using hnle) _ (Nat.le_refl 0) hrs,
    hh, hle, hol⟩

theorem call_simb (hP : ProgOK P) {ρ ρS : List Tm} {Γ Γb : Ctx} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ)
    {args t outsT : Tm} {np : Nat} (ha : ArgsTy P Γ args t outsT) (ht : t.isTele) (hn : args.len = np)
    (hra : rtArgs P Γ args t = true) {gid : Nat} {G : Group} {F : FnDef} {envS env : List Tm}
    {ve : Option (List Bool)} (hG : P.groups[gid]? = some G) (hgG : G.ghost = false) (hdn : F.dele = none)
    (hdo : G.deleOK P env.length = true) (hSc : SimEnv P (fun i => G.ers.getD i true) envS env)
    (hve : ve = some t.ers) (hFe : F.tele.ers = t.ers) (hFnp : F.np = np)
    (he1 : ∀ i < env.length, F.dele = none → Γb.er i = G.ers.getD i true)
    (he2 : ∀ j' F', G.fns[j']? = some F' → F.dele = none → Γb.er (env.length + j') = F'.er)
    (he3 : ∀ k < np, Γb.er (env.length + G.fns.length + k) = t.ers.getD k true) :
    SimEnv P Γb.er (envS ++ closuresS envS gid G ++ F.spreadIn ve (args.toList.map (P.sub ρS)))
      (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) := by
  have hlc := hSc.1
  have hclo : ∀ k a b, (closuresS envS gid G)[k]? = some a → (closures env gid G)[k]? = some b →
      Γb.er (env.length + k) = false → Real P a b := by
    intro k a b ha hb he
    obtain ⟨hk, -⟩ := closures_get hb
    obtain ⟨Fk, hFk⟩ : ∃ Fk, G.fns[k]? = some Fk := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [he2 k Fk hFk hdn] at he
    exact closuresS_real hG hgG hdo hlc hSc.2 k a b Fk hFk he ha hb
  have hS1 := hSc.extend (er' := Γb.er) (by simp [closures, closuresS_length]) (fun i hi => he1 i hi hdn) hclo
  have hal := ha.isList
  have htl : np ≤ t.ers.length := by have := ha.len ht; rw [Tm.len_ers _ ht]; omega
  have hlenS : (args.toList.map (P.sub ρS)).length = np := by simp [Tm.len_toList _ hal, hn]
  have hin : F.spreadIn ve (args.toList.map (P.sub ρS)) =
      spread (t.ers.take np) (filt (t.ers.take np) (args.toList.map (P.sub ρS))) := by
    simp only [FnDef.spreadIn, hFe, hFnp, hve, hlenS, Option.getD_some]
  have hS2 := hS1.extend (er' := Γb.er) (vsS := F.spreadIn ve (args.toList.map (P.sub ρS)))
    (vs := args.toList.map (·.subst (Tm.env ρ)))
    (by rw [hin, length_spread]; simp [Tm.len_toList _ hal, hn]; omega) (fun _ _ => rfl) fun k a b ha' hb he => by
      have hk : k < np := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        rw [List.length_map, Tm.len_toList _ ha.isList] at this; omega
      simp only [List.length_append, closures, List.length_map, List.length_range] at he
      rw [he3 k hk] at he
      rw [hin, spread_filt _ _ (by simp [hlenS]; omega) k (by rw [getD_take hk]; exact he)] at ha'
      rw [← Tm.toList_subst _ _ ha.isList] at hb
      have hra' := rtArgs_reals hP hE hS args t hra
      rw [Prog.subUArgs_subst _ _ ha.isList] at hra'
      exact hra'.get k a b (by simpa [Tm.toList_ofList, Prog.sub] using ha') hb he
  exact hS2

theorem dele_sim {Γb : Ctx} {env0 argsS argsF : List Tm} {gid tg np : Nat} {G : Group} {pe : List Bool} {vS : Tm}
    (hRt : Real P vS (Tm.env (env0 ++ closures env0 gid G) tg)) (htg : tg < env0.length + G.fns.length)
    (hdl : ∀ i, i < env0.length + G.fns.length → i ≠ tg → Γb.er i = true)
    (he3 : ∀ k < np, Γb.er (env0.length + G.fns.length + k) = pe.getD k true)
    (hpl : pe.length = np) (hlS : argsS.length = np) (hlF : argsF.length = np)
    (hra : ∀ k x y, argsS[k]? = some x → argsF[k]? = some y → pe.getD k true = false → Real P x y) :
    SimEnv P Γb.er ((List.replicate (env0.length + G.fns.length) .tok).set tg vS ++ spread pe (filt pe argsS))
      (env0 ++ closures env0 gid G ++ argsF) := by
  have hEl : ((List.replicate (env0.length + G.fns.length) Tm.tok).set tg vS).length = env0.length + G.fns.length := by
    simp
  have hEt : Tm.env ((List.replicate (env0.length + G.fns.length) Tm.tok).set tg vS) tg = vS := by
    simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_set, htg]
  have hcl : (env0 ++ closures env0 gid G).length = env0.length + G.fns.length := by simp [closures]
  refine ⟨by simp [length_spread, closures, hpl, hlF]; omega, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i (env0.length + G.fns.length) with hin | hin
  · by_cases hit : i = tg
    · subst hit
      rw [env_app_left (by rw [hEl]; exact hin), hEt, env_app_left (by rw [hcl]; exact hin)]; exact hRt
    · rw [hdl i hin hit] at hi; cases hi
  · obtain ⟨k, rfl⟩ : ∃ k, i = env0.length + G.fns.length + k := ⟨i - (env0.length + G.fns.length), by omega⟩
    have e1 := env_app_right (ρ := (List.replicate (env0.length + G.fns.length) Tm.tok).set tg vS)
      (vs := spread pe (filt pe argsS)) k
    have e2 := env_app_right (ρ := env0 ++ closures env0 gid G) (vs := argsF) k
    rw [hEl] at e1; rw [hcl] at e2
    rw [e1, e2]
    rcases Nat.lt_or_ge k np with hk | hk
    · rw [he3 k hk] at hi
      obtain ⟨x, hx⟩ : ∃ x, argsS[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨y, hy⟩ : ∃ y, argsF[k]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [List.getD_eq_getElem?_getD, spread_filt pe argsS (by omega) k hi, hx, List.getD_eq_getElem?_getD, hy]
      exact hra k x y hx hy hi
    · rw [List.getD_eq_getElem?_getD (l := argsF), List.getElem?_eq_none (show argsF.length ≤ k by omega)]; exact Real.nil' _

theorem call_step (hP : ProgOK P) {μ : Option (List Nat)} {ρ : List Tm} {cnt : Nat} {Γ : Ctx} {f Ft l t args outsT rets : Tm}
    {np : Nat} {uf : Bool} {hmk : List Bool} {dec : Dec} {er : Bool} {ms : List Bool} {ve : Option (List Bool)}
    {rest : Core} {env : List Tm} {n1 gid : Nat} {G : Group} {F : FnDef} {outs : List Tm} {cnt1 : Nat}
    (hE : EnvOK P ρ Γ) (hb : LvlBound ρ cnt) (hm : MuOK μ Γ ρ) (hrs : rets.static Γ.n 0)
    (hf : TmTy P Γ f Ft) (hF : Γ.canon Ft = .fn l np t uf hmk) (ht : t.isTele) (ha : ArgsTy P Γ args t outsT)
    (hn : args.len = np) (hd : DecOK P Γ dec l t args) (ho : outsT.len = ms.length)
    (hok : (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outsT)) = true) (hve : ve = some t.ers)
    (hcal : callee P (f.subst (Tm.env ρ)) = some (env, n1, gid, G, F))
    (hev : eval P (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt F.body = .ok (outs, cnt1))
    (ihb : ∀ Γb rb, CoreTy P gid Γb F.body rb → EnvOK P (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) Γb → LvlBound (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt →
      MuOK (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) Γb (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) → rb.static Γb.n 0 →
      Result P (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt rb (eval P (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt F.body) ∧ Sim P Γb (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) F.body rb (eval P (some (n1 :: (markedArgs F.tele (.ofList (args.toList.map (·.subst (Tm.env ρ))))).map Tm.size)) (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ))) cnt F.body)) :
    EnvOK P (ρ ++ outs) (Ctx.adv P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)) ∧ LvlBound (ρ ++ outs) cnt1 ∧ MuOK μ (Ctx.adv P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)) (ρ ++ outs) ∧ rets.static (Ctx.adv P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)).n 0 ∧
    HeadSim P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) ρ outs (.call f dec args er ms ve rest) rest ∧
    cnt ≤ cnt1 ∧ outs.length = outsT.len ∧
    ∀ ρS, Γ.ghost = false → SimEnv P Γ.er ρS ρ → er = false → ∀ envS gid' j' Gr' F' outsSb,
      P.sub ρS f = .clo envS gid' j' → P.groups[gid']? = some Gr' → Gr'.fns[j']? = some F' →
      RunS P (envS.toList ++ closuresS envS.toList gid' Gr' ++ F'.spreadIn ve (args.toList.map (P.sub ρS))) F'.body outsSb →
      SimEnv P (Ctx.adv P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)).er
        (ρS ++ F'.spreadOut ve args.toList.length outsSb) (ρ ++ outs) := by
  obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb, hgb, he1, he2, hdl, he3, hrbt⟩,
    hot, hos, hFe, hFnp, hdo⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
  rw [hcal] at hcal'; cases hcal'
  obtain ⟨⟨vs, c', e, hvs, hbv, hle, hlc⟩, hsb⟩ := ihb Γb rb hcb hEb hbb hmb hrbs
  rw [hev] at e; cases e
  rw [hrb] at hvs
  have hol : outs.length = outsT.len := by
    have := hvs.len (Tm.isTele_subst _ _ hot)
    rw [Tm.len_subst _ _ (.inl hot), ← Tm.len_toList _ hvs.isList, Tm.toList_ofList] at this; simpa [Tm.len] using this
  obtain ⟨hE', hcur, hsubs, hnle⟩ := hE.pushTele (some (ms.map (er || ·))) hot hos hvs hlc
  have hl := hE.len
  obtain ⟨hpg, hpo, hpn⟩ := Ctx.pushTele_er Γ outsT (some (ms.map (er || ·))) hot
  have hh0 : ∀ ρS, Γ.ghost = false → SimEnv P Γ.er ρS ρ → ∃ o, (er = false → ∀ envS gid' j' Gr' F' outsSb,
      P.sub ρS f = .clo envS gid' j' → P.groups[gid']? = some Gr' → Gr'.fns[j']? = some F' →
      RunS P (envS.toList ++ closuresS envS.toList gid' Gr' ++ F'.spreadIn ve (args.toList.map (P.sub ρS))) F'.body outsSb →
      o = F'.spreadOut ve args.toList.length outsSb) ∧
      (∀ vs', stepS P ρS (.call f dec args er ms ve rest) = some vs' → vs' = o) ∧
      (∀ out, RunS P (ρS ++ o) rest out → RunS P ρS (.call f dec args er ms ve rest) out) ∧ o.length = outs.length ∧
      ∀ k a b, o[k]? = some a → outs[k]? = some b → (Γ.pushTele outsT (some (ms.map (er || ·)))).er (Γ.n + k) = false →
        Real P a b := by
    intro ρS hg hS
    have her : ∀ k, k < outs.length →
        (Γ.pushTele outsT (some (ms.map (er || ·)))).er (Γ.n + k) = (ms.map (er || ·)).getD k true :=
      fun k hk => hpn k (hol ▸ hk)
    cases er with
    | true =>
      refine ⟨List.replicate ms.length .tok, (fun h => by cases h), fun vs' h => by simp [stepS] at h; exact h.symm,
        fun out h => .callE h, by simp [← ho, hol], fun k a b _ hb he => ?_⟩
      rw [her k (List.getElem?_eq_some_iff.mp hb).1] at he
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at he
      cases h : ms[k]? <;> simp [h] at he
    | false =>
      simp only [Ctx.ok, hg, Bool.false_or, Bool.and_eq_true] at hok
      obtain ⟨⟨hrf, hra⟩, hcm⟩ := hok
      obtain ⟨e₀, j, hfv, rfl, hG, hFj⟩ := callee_some hcal
      have hR := rt_real hP hE hS f hrf; rw [hfv] at hR
      rcases hR.clo_inv with ⟨envS, env₀, G', F', hfS, rfl, hG', hgG, hF', hfe, hdn, hSc⟩ | ⟨env₀, G', F', tg, he₀, hG', hgG, hF', hfe, hdt, hRt⟩
      rotate_left
      · rw [hG] at hG'; cases hG'; rw [hFj] at hF'; cases hF'; subst he₀; subst hve
        rw [Tm.toList_ofList] at *
        have hal := ha.isList
        have htl : np ≤ t.ers.length := by have := ha.len ht; rw [Tm.len_ers _ ht]; omega
        have hlenS : (args.toList.map (P.sub ρS)).length = np := by simp [Tm.len_toList _ hal, hn]
        obtain ⟨hlt, -, -, hwalk⟩ := Group.deleOK_spec hdo hFj hdt
        have hjl : j < G.fns.length := (List.getElem?_eq_some_iff.mp hFj).1
        have hpe : F.tele.ers.take F.np = t.ers.take np := by rw [hFe, hFnp]
        have hpl : (t.ers.take np).length = np := by simp; omega
        have hSdef : filt (t.ers.take (args.toList.map (P.sub ρS)).length) (args.toList.map (P.sub ρS)) =
            filt (t.ers.take np) (args.toList.map (P.sub ρS)) := by rw [hlenS]
        have hSlen : (filt (t.ers.take (args.toList.map (P.sub ρS)).length) (args.toList.map (P.sub ρS))).length =
            (F.tele.ers.take F.np).count false := by
          rw [hSdef, hpe, length_filt _ _ (by rw [hpl, hlenS])]
        have hEl : ((List.replicate (env₀.length + G.fns.length) Tm.tok).set tg (P.sub ρS f)).length =
            env₀.length + G.fns.length := by simp
        have hEt : Tm.env ((List.replicate (env₀.length + G.fns.length) Tm.tok).set tg (P.sub ρS f)) tg =
            P.sub ρS f := by
          simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_set, show tg < env₀.length + G.fns.length by omega]
        have hra' := rtArgs_reals hP hE hS args t hra
        rw [Prog.subUArgs_subst _ _ hal] at hra'
        have hS2 : SimEnv P Γb.er
            ((List.replicate (env₀.length + G.fns.length) Tm.tok).set tg (P.sub ρS f) ++
              spread (F.tele.ers.take F.np)
                (filt (t.ers.take (args.toList.map (P.sub ρS)).length) (args.toList.map (P.sub ρS))))
            (env₀ ++ closures env₀ gid G ++ args.toList.map (·.subst (Tm.env ρ))) := by
          rw [hpe, hSdef]
          refine dele_sim hRt (by omega) (fun i hin hit => hdl i tg hdt hin hit)
            (fun k hk => by rw [he3 k hk, getD_take hk]) hpl hlenS (by simp [Tm.len_toList _ hal, hn])
            (fun k x y hx hy hi => ?_)
          have hk : k < np := by have := (List.getElem?_eq_some_iff.mp hx).1; simpa [hlenS] using this
          simp only [List.getElem?_map, Option.map_eq_some_iff] at hx hy
          obtain ⟨a, ha1, rfl⟩ := hx; obtain ⟨a', ha2, rfl⟩ := hy
          rw [ha1] at ha2; cases ha2
          exact hra'.get k _ _ (by simp [ha1, Prog.sub, Tm.toList_ofList]) (by rw [Tm.toList_subst _ _ hal]; simp [ha1])
            (by rwa [getD_take hk] at hi)
        have hgb' : Γb.ghost = false := by rw [hgb, hgG, hfe]; rfl
        obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb' _ hS2 outs cnt1 hev
        try rw [Tm.toList_ofList] at hrunb
        obtain ⟨env', gid', j', G', F', outs', hcl, hG2, hF2, hb2, hres⟩ :=
          walk1 (re := F.tele.ers.drop F.np) hSlen (show tg < env₀.length + G.fns.length by omega) hrunb _ hwalk
            (fun so => WInv.init hEl _ _ so)
        rw [env_app_left (by rw [hEl]; omega), hEt] at hcl
        have hrbe : rb.ers = outsT.ers := by rw [← Tm.ers_subst _ _ hrbt, hrb, Tm.ers_subst _ _ hot]
        have hoe : outsT.ers = t.ers.drop np := by rw [ha.ers ht, hn]
        have hre : F.tele.ers.drop F.np = outsT.ers := by rw [hFe, hFnp, hoe]
        have hvd : t.ers.drop args.toList.length = outsT.ers := by rw [Tm.len_toList _ hal, hn, hoe]
        have hlo : outsT.ers.length = outs.length := by rw [Tm.len_ers _ hot, hol]
        have hlS : outsS.length = outs.length := by have := hreb.len; simpa [Tm.toList_ofList] using this
        have hb3 : RunS P (env'.toList ++ closuresS env'.toList gid' G' ++ F'.spreadIn (some t.ers) (args.toList.map (P.sub ρS)))
            F'.body outs' := by simpa [FnDef.spreadIn] using hb2
        refine ⟨F'.spreadOut (some t.ers) args.toList.length outs', fun _ envS' g'' j'' G'' F'' oS hcl' hG' hF' hrun' => ?_,
          fun vs' h => ?_, fun out h => .call hcl hG2 hF2 hb3 h,
          by simp [FnDef.spreadOut, length_spread, hvd, hlo, Option.getD_some], fun k a b ha hb he => ?_⟩
        · rw [hcl] at hcl'; simp only [Tm.clo.injEq] at hcl'; obtain ⟨rfl, rfl, rfl⟩ := hcl'
          rw [hG2] at hG'; cases hG'; rw [hF2] at hF'; cases hF'
          rw [RunS.det hb3 hrun']
        · simp only [stepS, hcl, hG2, hF2, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
            Option.some.injEq] at h
          obtain ⟨o, h1, rfl⟩ := h
          rw [runA_toArray] at h1; rw [runS_det h1 hb3]
        · rw [her k (List.getElem?_eq_some_iff.mp hb).1] at he
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at he
          have hk : k < outsT.len := hol ▸ (List.getElem?_eq_some_iff.mp hb).1
          have hmk : ms.getD k true = false := by
            simp only [List.getD_eq_getElem?_getD]; cases h : ms[k]? <;> simp_all
          have hek := compat_get ms outsT k hcm (by rw [Tm.len_ers _ hot]; exact hk) hmk
          simp only [FnDef.spreadOut, Option.getD_some, hvd] at ha
          rw [spread_get _ _ _ hek, Option.some.injEq] at ha
          rw [hre] at hres
          have h1 := hres k hek
          rw [ha] at h1
          have hkS : k < outsS.length := by rw [hlS]; exact (List.getElem?_eq_some_iff.mp hb).1
          have hk' : outsS[k]? = some a := by
            rw [← h1]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkS]
          rw [← hrbe] at hek
          exact hreb.get k a b (by simpa [Tm.toList_ofList] using hk') (by simpa [Tm.toList_ofList] using hb) hek
      rw [hG] at hG'; cases hG'; rw [hFj] at hF'; cases hF'
      rw [Tm.toList_ofList] at *
      have hlc := hSc.1
      have hS2 := call_simb hP hE hS ha ht hn hra hG hgG hdn hdo hSc hve hFe hFnp he1 he2 he3
      have hal := ha.isList
      have hgb' : Γb.ghost = false := by rw [hgb, hgG, hfe]; rfl
      obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb' _ hS2 outs cnt1 hev
      have hrbe : rb.ers = outsT.ers := by
        rw [← Tm.ers_subst _ _ hrbt, hrb, Tm.ers_subst _ _ hot]
      have hoe : outsT.ers = t.ers.drop np := by rw [ha.ers ht, hn]
      have hout : F.spreadOut ve args.toList.length outsS = spread outsT.ers (filt outsT.ers outsS) := by
        simp only [FnDef.spreadOut, hFe, hFnp, hve, Tm.len_toList _ hal, hn, hoe, Option.getD_some]
      have hlo : outsT.ers.length = outsS.length := by
        have := hreb.len; simp only [Tm.toList_ofList] at this
        rw [Tm.len_ers _ hot, ← hol, this]
      try rw [Tm.toList_ofList] at hrunb
      refine ⟨F.spreadOut ve args.toList.length outsS, fun _ envS' g'' j'' G'' F'' oS hcl' hG' hF' hrun' => ?_, fun vs' h => ?_,
        fun out h => .call hfS hG hFj (by simpa [Tm.toList_ofList] using hrunb) h,
        by rw [hout, length_spread, hlo]; simpa [Tm.toList_ofList] using hreb.len, fun k a b ha hb he => ?_⟩
      · rw [hfS] at hcl'; simp only [Tm.clo.injEq] at hcl'; obtain ⟨rfl, rfl, rfl⟩ := hcl'
        rw [hG] at hG'; cases hG'; rw [hFj] at hF'; cases hF'
        simp only [Tm.toList_ofList] at hrun'
        rw [RunS.det hrunb hrun']
      · simp only [stepS, hfS, hG, hFj, Tm.toList_ofList, Option.bind_eq_bind, Option.bind_some,
          Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨o, h1, rfl⟩ := h
        rw [runA_toArray] at h1; rw [runS_det h1 hrunb]
      · rw [her k (List.getElem?_eq_some_iff.mp hb).1] at he
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at he
        have hk : k < outsT.len := hol ▸ (List.getElem?_eq_some_iff.mp hb).1
        have hmk : ms.getD k true = false := by
          simp only [List.getD_eq_getElem?_getD]; cases h : ms[k]? <;> simp_all
        have := compat_get ms outsT k hcm (by rw [Tm.len_ers _ hot]; exact hk) hmk
        rw [hout, spread_filt _ _ hlo k this] at ha
        rw [← hrbe] at this
        exact hreb.get k a b (by simpa [Tm.toList_ofList] using ha) (by simpa [Tm.toList_ofList] using hb) this
  have hh : HeadSim P Γ (Γ.pushTele outsT (some (ms.map (er || ·)))) ρ outs (.call f dec args er ms ve rest) rest :=
    fun ρS hg hS => let ⟨o, _, h⟩ := hh0 ρS hg hS; ⟨o, h⟩
  refine ⟨hE.adv hE' (by simp [Ctx.pushTele_fixed]) hh, LvlBound.append.mpr ⟨hb.mono hle, hbv⟩,
    hm.append hE.wf hl (by simpa using hcur) (by simpa using hsubs), Tm.static_mono (by simpa using hnle) _ (Nat.le_refl 0) hrs,
    hh, hle, hol, fun ρS hg hS her envS gid' j' Gr' F' outsSb hfS hGr hFj hrun => ?_⟩
  obtain ⟨o, hO, -, -, hlo, hre⟩ := hh0 ρS hg hS
  rw [hO her envS gid' j' Gr' F' outsSb hfS hGr hFj hrun] at hlo hre
  rw [Ctx.adv_er]
  exact hS.extend hlo (fun i hi => hpo i (hl ▸ hi)) fun k a b ha hb he => hre k a b ha hb (by rw [← hl]; exact he)

theorem eval_sound (hP : ProgOK P) (hO : P.OracleOK) : ∀ μ ρ cnt c, ∀ b Γ rets, CoreTy P b Γ c rets → EnvOK P ρ Γ →
    LvlBound ρ cnt → MuOK μ Γ ρ → rets.static Γ.n 0 →
    Result P ρ cnt rets (eval P μ ρ cnt c) ∧ Sim P Γ ρ c rets (eval P μ ρ cnt c) := by
  intro μ ρ cnt c
  induction μ, ρ, cnt, c using eval.induct P with
  | case1 μ ρ cnt ts =>
    intro b Γ rets hc hE hb _ hrs
    cases hc with
    | ret ha hok =>
    obtain ⟨hv, hs, _⟩ := args_sound hP hE ha hrs
    have hl := ha.isList
    refine ⟨⟨_, cnt, by rw [eval], ?_, ?_, Nat.le_refl _, ?_⟩, ?_⟩
    · rw [← Tm.toList_subst _ _ hl, Tm.ofList_toList _ (Tm.isList_subst _ _ hl)]; simpa [Tm.subst] using hv
    · intro v hv' x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv'
      exact hb.subst (static_toList hs t ht) x hx
    · intro v hv'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv'
      exact lc_of_static hE.closed (static_toList hs t ht)
    · intro hg ρS hS vs cnt' hr
      rw [eval] at hr; cases hr
      simp only [Ctx.ok, hg, Bool.false_or] at hok
      exact ⟨_, .ret, Reals.ofList_subst hP hE hS hl hok⟩
  | case2 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu outs cnt1 hev ihb ihr =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | @call _ _ _ _ np t _ _ _ outsT _ _ _ _ _ _ _ hf hF ht ha hn hd ho hok hve hr =>
    obtain ⟨hE', hb', hm', hrs', hh, hle, -, -⟩ := call_step hP hE hb hm hrs hf hF ht ha hn hd ho hok hve hcal hev (ihb gid)
    have hl := hE.len
    rw [eval]; simp only [hcal]; rw [dif_pos hmu]; simp only [argv, μ'] at hev; simp only [hev]
    obtain ⟨hpg, hpo, -⟩ := Ctx.pushTele_er Γ outsT (some (ms.map (er || ·))) (ha.isTele ht)
    have ihr' := ihr b _ rets hr hE' hb' hm' hrs'
    exact ⟨Result.weaken ihr'.1 (hl ▸ hrs) hle, hh.finish hE hpo (fun hg => hpg.trans hg) ihr'.2⟩
  | case3 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu e hev ihb =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb⟩, hot, hos⟩ :=
      call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    obtain ⟨⟨vs, c', e', _⟩, _⟩ := ihb gid Γb rb hcb hEb hbb hmb hrbs
    rw [hev] at e'; cases e'
  | case4 μ ρ cnt f dec args er ms ve rest env n1 gid G F hcal argv μ' hmu =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', hmu', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    exact absurd hmu' hmu
  | case5 μ ρ cnt f dec args er ms ve rest hcal =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
  | case6 μ ρ cnt s R brs els er rest d c ls vs hs pre body hb outs cnt1 hev ihb ihr =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD hnt _ _ hRs hRt hok hbr hel hr =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', hg', he1, he2⟩ :=
      match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    have hres := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    obtain ⟨hE'', hlb'', hm'', hrs'', hh, hle, -⟩ :=
      mtch_setup (rest := rest) hP hE hlb hm hrs hRs hRt hok hnt hs hb hev hntd hg' he1 he2.1 hres
    obtain ⟨hpg, hpo, -⟩ := Ctx.pushTele_er Γ R (if er then some (List.replicate R.len true) else none) hRt
    rw [eval]; simp only [hs]
    split
    · rename_i pre'' body'' hb''
      rw [hb] at hb''; cases hb''
      simp only [hev]
      have ihr' := ihr bnd _ rets hr hE'' hlb'' hm'' hrs''
      exact ⟨Result.weaken ihr'.1 (hE.len ▸ hrs) hle, hh.finish hE hpo (fun hg => hpg.trans hg) ihr'.2⟩
    · rename_i hno; rw [hb] at hno; cases hno
  | case7 μ ρ cnt s R brs els er rest d c ls vs hs pre body hb e hev ihb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD hnt _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', _⟩ :=
      match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    obtain ⟨⟨_, _, e', _⟩, _⟩ := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    rw [hev] at e'; cases e'
  | case8 μ ρ cnt s R brs els er rest d c ls vs hs hb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD hnt _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, pre', body', hb', _⟩ := match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
  | case9 μ ρ cnt s R brs els er rest hs =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD hnt _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨d', c', ls', vs', hsv, hntd, _⟩ := match_setup hP hE hlb hm hst hS hD hbr hel hRs
    exact (hs _ _ _ _ hsv).elim
  | case22 μ ρ cnt R body rest outs cnt1 hev ihb ihr =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | seq _ hRs hRt hb hr =>
    obtain ⟨hE', hlb', hm', hrs', hh, hle, -⟩ := seq_setup hE hlb hm hrs hRs hRt (rest := rest) (ihb bnd Γ R hb hE hlb hm hRs) hev
    have ihr' := ihr bnd _ rets hr hE' hlb' hm' hrs'
    obtain ⟨hpg, hpo, -⟩ := Ctx.pushTele_er Γ R none hRt
    rw [eval]; simp only [hev]
    exact ⟨Result.weaken ihr'.1 (hE.len ▸ hrs) hle, hh.finish hE hpo (fun hg => hpg.trans hg) ihr'.2⟩
  | case23 μ ρ cnt R body rest e0 hev ihb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | seq _ hRs hRt hb hr =>
    obtain ⟨⟨_, _, e1, _⟩, _⟩ := ihb bnd Γ R hb hE hlb hm hRs
    rw [hev] at e1; cases e1
  | case10 μ ρ cnt p er rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | @prim _ _ T _ _ _ _ hp hok hr =>
    obtain ⟨hE'', hlb', hm', hrs', hh, her⟩ := prim_setup (rest := rest) hP hO hE hb hm hrs hp hok
    rw [eval]
    have hl := hE.len
    have ih' := ih b _ rets hr hE'' hlb' hm' hrs'
    exact ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_refl _), hh.finish hE (fun i hi => by rw [her, if_neg (by omega)])
      (fun hg => by rw [← hg]; cases p <;> simp [Ctx.pushPrim, Ctx.pushPrim0, Ctx.pushPrim0, Ctx.withRule, Ctx.push]) ih'.2⟩
  | case11 μ ρ cnt w req rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | wdo hw ha hok hr =>
    obtain ⟨hE'', hlb', hm', hrs', hh, her⟩ := wdo_setup (rest := rest) hP hO hE hb hm hrs hw ha hok
    rw [eval]
    have hl := hE.len
    have ih' := ih b _ rets hr hE'' hlb' hm' hrs'
    exact ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_refl _),
      hh.finish hE (fun i hi => by rw [her, if_neg (by omega), if_neg (by omega)])
        (fun hg => by rw [← hg]; simp [Ctx.pushWdo, Ctx.push]) ih'.2⟩
  | case12 μ ρ cnt rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defLvl hr =>
    rw [eval]
    have hl := hE.len
    have hh : HeadSim P Γ Γ.pushMint ρ [.lvl cnt] (.defLvl rest) rest := by
      intro ρS hg hS
      refine ⟨[.tok], fun vs' h => by simp [stepS] at h; exact h.symm, fun out h => .defLvl h, rfl,
        fun k a b ha hb _ => ?_⟩
      cases k with
      | succ => simp at ha
      | zero => simp at ha hb; subst ha hb; exact .other (by simp) (by simp) (by simp) (by simp)
    have ih' := ih b _ rets hr (hE.adv (hE.pushMint hb) rfl hh) (LvlBound.append.mpr ⟨hb.mono (Nat.le_succ _), by simp [LvlBound, Tm.levels]⟩)
      (hm.append hE.wf hl (by simp [Ctx.pushMint, Ctx.push]) (by simp [Ctx.pushMint, Ctx.push]))
      (Tm.static_mono (by simp [Ctx.pushMint, Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hrs)
    exact ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_succ _), hh.finish (Γ' := Γ.pushMint) hE
      (fun i hi => by simp [show i ≠ Γ.n by omega]) (fun hg => hg) ih'.2⟩
  | case13 μ ρ cnt gid rest G hG ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defFns _ hG' hok hr =>
    rw [hG] at hG'; cases hG'
    rw [eval, hG]
    have hl := hE.len
    have hh : HeadSim P Γ (Γ.pushFns G) ρ (closures ρ gid G) (.defFns gid rest) rest := by
      intro ρS hg hS
      cases hok with
      | mk _ _ _ _ _ hGe hGg hd _ =>
      refine ⟨closuresS ρS gid G, fun vs' h => by simp [stepS, hG] at h; exact h.symm, fun out h => .defFns hG h,
        by simp [closures, closuresS_length], fun k a b ha hb he => ?_⟩
      obtain ⟨hk, -⟩ := closures_get hb
      obtain ⟨Fk, hFk⟩ : ∃ Fk, G.fns[k]? = some Fk := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [Ctx.er_pushFns, if_pos (by omega), show Γ.n + k - Γ.n = k by omega, hFk] at he
      refine closuresS_real hG (by rw [← hGg, hg]) (by rw [hl]; exact hd) (by rw [hS.1]) (fun i hi => ?_) k a b Fk hFk
        (by simpa using he) ha hb
      by_cases hin : i < Γ.n
      · rw [← hGe i hin] at hi; exact hS.2 i hi
      · have : Tm.env ρ i = .nil := by
          simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ρ.length ≤ i by omega)]
        rw [this]; exact Real.nil' _
    have ih' := ih b _ rets hr (hE.adv (hE.pushFns hP hG hok) (by simp [Ctx.pushFns]) hh) (LvlBound.append.mpr ⟨hb, fun v hv x hx => by
        simp only [closures, List.mem_map] at hv
        obtain ⟨j, _, rfl⟩ := hv
        obtain ⟨w, hw, hx'⟩ := Tm.levels_ofList ρ x (by simpa [Tm.levels] using hx)
        exact hb w hw x hx'⟩)
      (hm.append hE.wf hl (by simp [Ctx.pushFns]) (by simp [Ctx.pushFns]))
      (Tm.static_mono (by simp [Ctx.pushFns, Ctx.n]) _ (Nat.le_refl 0) hrs)
    exact ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_refl _), hh.finish (Γ' := Γ.pushFns G) hE
      (fun i hi => by rw [Ctx.er_pushFns, if_neg (by omega)]) (fun hg => by simpa [Ctx.pushFns] using hg) ih'.2⟩
  | case14 μ ρ cnt gid rest hG =>
    intro b Γ rets hc
    cases hc with
    | defFns _ hG' => rw [hG] at hG'; cases hG'
  | case15 μ ρ cnt k a e rest ih =>
    intro b Γ rets hc hE hb hm hrs
    rw [eval]
    have : ∃ o σ' ς' cm pd, CoreTy P b { Γ with opened := o, σ := σ', ς := ς', cmode := cm, pd := pd } rest rets ∧
        EnvOK P ρ { Γ with opened := o, σ := σ', ς := ς', cmode := cm, pd := pd } := by
      cases hc with
      | chkOpn _ _ _ hu h => exact ⟨_, _, _, _, Γ.pd, h, EnvOK.opnCtx (hE.opened hP hu)⟩
      | chkOpnFail hM hc h => exact (hE.openFail hP hM hc h).elim
      | chkCm h => exact ⟨Γ.opened, Γ.σ, Γ.ς, true, Γ.pd, h, hE.congr _ rfl rfl rfl rfl rfl⟩
      | chkSlotAt h => exact ⟨Γ.opened, Γ.σ, Γ.ς, Γ.cmode, _, h, hE.congr _ rfl rfl rfl rfl rfl⟩
      | chkMark h =>
        rw [Ctx.markPd_eq] at h
        exact ⟨Γ.opened, Γ.σ, Γ.ς, Γ.cmode, _, h, hE.congr _ rfl rfl rfl rfl rfl⟩
      | chkSlf hok hs hS hΓ h =>
        rename_i Γ'
        have e := Ctx.slotSelf_eq hΓ
        refine ⟨Γ.opened, Γ'.σ, Γ'.ς, Γ.cmode, Γ.pd, ?_, ?_⟩
        · rw [e] at h; exact h
        · have := hE.slotSelf hP hok hs hS hΓ; rw [e] at this; exact this
      | _ => exact ⟨Γ.opened, Γ.σ, Γ.ς, Γ.cmode, Γ.pd, by assumption, hE.congr _ rfl rfl rfl rfl rfl⟩
    obtain ⟨o, σ', ς', cm, pd', h', hE'⟩ := this
    have ih' := ih b _ rets h' hE' hb hm hrs
    refine ⟨ih'.1, fun hg ρS hS vs cnt' hr' => ?_⟩
    obtain ⟨vsS, hrun, hre⟩ := ih'.2 hg ρS hS vs cnt' hr'
    exact ⟨vsS, .chk hrun, hre⟩
  | case16 μ ρ cnt body a hev ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | absurd hcb hn => exact absurd hev (noRet_eval _ _ _ _ hn a)
  | case17 μ ρ cnt body e hev ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | absurd hcb hn =>
    obtain ⟨⟨vs, c', e', -⟩, -⟩ := ih b _ _ hcb (hE.congr _ rfl rfl rfl rfl rfl) hb hm rfl
    rw [hev] at e'; cases e'
  | case18 μ ρ cnt =>
    intro b Γ rets hc
    cases hc
  | case19 μ ρ cnt s brs els er nt d c ls vs hs pre body hb ih =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | case hst hS hD hntc hd hok hreal hbr hel =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', hg', he1, he2, hpl, -⟩ :=
      match_setup (ge := Γ.ghost) hP hE hlb hm hst hS hD hbr (fun e h => by simpa using hel e h) hrs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    have hl := hE.len
    obtain ⟨hres, hsb⟩ := ih bnd Γ' rets hcb hE' hlb' hm' hRs'
    rw [eval]; simp only [hs]
    split
    · rename_i pre'' body'' hb''
      rw [hb] at hb''; cases hb''
      refine ⟨Result.weaken hres (hl ▸ hrs) (Nat.le_refl _), fun hg ρS hS vs'' cnt' hr' => ?_⟩
      cases er with
      | false =>
        simp only [Ctx.ok, hg, Bool.false_or] at hok
        have hR := rt_real hP hE hS s hok; rw [hs] at hR
        simp only [Bool.not_false, Bool.and_true] at hntc
        subst hntc
        cases hn : nt with
        | true =>
          rw [hn] at hntd
          obtain ⟨k, hw, hRk⟩ := hR.wrap_inv hP hntd
          obtain ⟨-, hph, sigw, hsigw, hkw⟩ := Prog.wrapField_spec hw
          obtain ⟨_, hkd, hku⟩ := Tm.ntField_spec hkw
          have hgb : Γ'.ghost = false := by rcases hg' with h | h <;> rw [h] <;> simp [hg, hph]
          rcases realBr_of_select hb (eval_real hr') (hreal hg (by simp [hn])) with ⟨n, _, hmem, hlk, hrb⟩ | ⟨rfl, hrb⟩
          · obtain ⟨sig, hsig, hpl⟩ := hpl (by simp [hlk])
            rw [hsigw] at hsig; cases hsig
            have hpv : pre = vs.toList := by
              simp only [selectBr, hlk, Option.some.injEq, Prod.mk.injEq] at hb; exact hb.1.symm
            have hnl : n = pre.length := by
              obtain ⟨_, sig0, _, hsh0, hn0⟩ := armsOK_mem hd hmem
              obtain ⟨_, sig1, sigc, hsh1, hct, hlf, hvs1, hst1⟩ := harm
              rw [hsh1] at hsh0; cases hsh0
              rw [hsigw] at hct; cases hct
              have hsk := (hvs1.skip (ctor_tele hP hsigw)).2.1
              rw [hlf] at hsk
              simp only at hn0; rw [hn0, hpl, hsk, Tm.len_subst _ _ (.inl hst1)]
            have hSb : SimEnv P Γ'.er (ρS ++ (List.replicate n Tm.tok).map fun _ => P.sub ρS s) (ρ ++ pre) :=
              hS.extend (by simp [hnl]) (fun i hi => he1 i (hl ▸ hi)) fun j a b ha hb he => by
                have hj := (List.getElem?_eq_some_iff.mp hb).1
                rw [hl, he2 _ hsigw j hj, Bool.false_or] at he
                have := hku j (by omega) he; subst this
                simp only [List.map_replicate, List.getElem?_replicate] at ha
                split at ha
                · cases ha; rw [hpv] at hb
                  simpa [List.getD_eq_getElem?_getD, hb] using hRk
                · cases ha
            obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _ hSb vs'' cnt' hr'
            exact ⟨outsS, .caseN hrb hrunb, hreb⟩
          · obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _
              (hS.extend rfl (fun i hi => he1 i (hl ▸ hi)) fun k _ _ h => by simp at h) vs'' cnt' hr'
            exact ⟨outsS, .caseN hrb (by simpa using hrunb), hreb⟩
        | false =>
          obtain ⟨vsS, sig, hsS, hsig, hph, hrv⟩ := hR.con_inv (by rw [hntd, hn])
          have hgb : Γ'.ghost = false := by rcases hg' with h | h <;> rw [h] <;> simp [hg, hph]
          have hSb : ∃ preS, selectBr brs els c vsS.toList = some (preS, body) ∧
              SimEnv P Γ'.er (ρS ++ preS) (ρ ++ pre) := by
            rcases selectBr_same (vs' := vsS.toList) hb with ⟨rfl, hsel⟩ | ⟨rfl, hsel⟩
            · refine ⟨_, hsel, hS.extend hrv.len (fun i hi => he1 i (hl ▸ hi)) fun k a b ha hb he => ?_⟩
              rw [hl, he2 sig hsig k (List.getElem?_eq_some_iff.mp hb).1, Bool.false_or] at he
              exact hrv.get k a b ha hb he
            · exact ⟨_, hsel, hS.extend rfl (fun i hi => he1 i (hl ▸ hi)) fun k _ _ h => by simp at h⟩
          obtain ⟨preS, hsel, hSb⟩ := hSb
          obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _ hSb vs'' cnt' hr'
          exact ⟨outsS, .case hsS hsel hrunb, hreb⟩
      | true =>
        have hgb : Γ'.ghost = false := by rcases hg' with h | h <;> rw [h] <;> simp [hg]
        rcases realBr_of_select hb (eval_real hr') (hreal hg rfl) with ⟨n, _, hmem, hlk, hrb⟩ | ⟨rfl, hrb⟩
        · obtain ⟨sig, hsig, hpl⟩ := hpl (by simp [hlk])
          obtain ⟨_, sig0, _, hsh0, hn⟩ := armsOK_mem hd hmem
          obtain ⟨_, sig1, sigc, hsh1, hct, hlf, hvs1, hst1⟩ := harm
          rw [hsh1] at hsh0; cases hsh0
          rw [hsig] at hct; cases hct
          have hsk := (hvs1.skip (ctor_tele hP hsig)).2.1
          rw [hlf] at hsk
          have hSb : SimEnv P Γ'.er (ρS ++ List.replicate n .tok) (ρ ++ pre) :=
            hS.extend (by simp only at hn; simp [hn, hpl, hsk, Tm.len_subst _ _ (.inl hst1)]) (fun i hi => he1 i (hl ▸ hi)) fun k a b ha hb he => by
              rw [hl, he2 _ hsig k (List.getElem?_eq_some_iff.mp hb).1, Bool.true_or] at he; cases he
          obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _ hSb vs'' cnt' hr'
          exact ⟨outsS, .caseE hrb hrunb, hreb⟩
        · obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _
            (hS.extend rfl (fun i hi => he1 i (hl ▸ hi)) fun k _ _ h => by simp at h) vs'' cnt' hr'
          exact ⟨outsS, .caseE hrb hrunb, hreb⟩
    · rename_i hno; rw [hb] at hno; cases hno
  | case20 μ ρ cnt s brs els er nt d c ls vs hs hb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | case hst hS hD hntc hd hok hreal hbr hel =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, pre', body', hb', _⟩ :=
      match_setup (ge := Γ.ghost) hP hE hlb hm hst hS hD hbr (fun e h => by simpa using hel e h) hrs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
  | case21 μ ρ cnt s brs els er nt hs =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | case hst hS hD hntc hd hok hreal hbr hel =>
    obtain ⟨d', c', ls', vs', hsv, hntd, harm, _⟩ :=
      match_setup (ge := Γ.ghost) hP hE hlb hm hst hS hD hbr (fun e h => by simpa using hel e h) hrs
    exact (hs _ _ _ _ hsv).elim

theorem checked_runs (hO : P.OracleOK) {rets : Tm} (h : Checked P rets) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) rets .nil ∧
      ∃ vsS, RunS P [] P.main vsS ∧ Reals P (.ofList vsS) (.ofList vs) rets := by
  obtain ⟨hP, hc, hs⟩ := h
  have hE : EnvOK P [] {tys := #[]} :=
    .mk rfl (fun _ _ _ h _ => by simp at h) (by simp) (fun _ _ h => by simp at h) (by simp)
      ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h, by simp, by simp, by simp⟩
      ⟨by simp, fun _ _ h => by simp at h⟩ (fun _ _ _ _ h => by simp at h)
  obtain ⟨⟨vs, cnt, e, hv, _⟩, hsim⟩ :=
    eval_sound hP hO none [] 0 P.main _ _ rets hc hE (by simp [LvlBound]) (by simp [MuOK]) (by simpa [Ctx.n] using hs)
  exact ⟨vs, cnt, e, by rwa [Tm.subst_static0 _ _ 0 hs] at hv,
    hsim rfl [] ⟨rfl, fun _ _ => by simpa [Tm.env] using Real.nil' (P := P) .nil⟩ vs cnt e⟩

theorem no_false (hO : P.OracleOK) {d : Nat} {D : Adt} {args ls : Tm} {m e : Bool} (hD : P.adts[d]? = some D) (hempty : D.ctors = [])
    (hco : D.coercible = false) (hop : D.opq = false) :
    ¬ Checked P (.bind (.ty m e u) (.app (.tyc d ls) args) .nil) := by
  intro h
  obtain ⟨vs, _, _, hv, _⟩ := checked_runs hO h
  generalize Tm.ofList vs = w at hv
  cases hv with
  | cons hv _ => exact no_value_of_empty hD hempty hco hop (h.1.placed_ne hD hop) hv

theorem check_sound (hO : P.OracleOK) {R : Tm} {h : Checked P R} (_ : checkProg P = .ok ⟨R, h⟩) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) R .nil ∧
      ∃ vsS, RunS P [] P.main vsS ∧ Reals P (.ofList vsS) (.ofList vs) R :=
  checked_runs hO h

end Minimal
