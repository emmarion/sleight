import Minimal.UnifySound
import Minimal.Strip
import Minimal.Eval

set_option linter.deprecated false

namespace Minimal

structure Ctx.WF (Γ : Ctx) : Prop where
  tys : ∀ (i : Nat) (T : Tm), Γ.tys[i]? = some T → T.static Γ.n 0
  σ : ∀ e t, Γ.σ e = some t → e < Γ.n ∧ t.static Γ.n 0
  mints : ∀ L ∈ Γ.mints, L < Γ.n
  cur : ∀ c, Γ.cur = some c → c < Γ.n
  subs : ∀ s ∈ Γ.subs, s < Γ.n

variable (P : Prog)

mutual
inductive VTy : Tm → Tm → Prop
  | univ : VTy v .univ
  | top : VTy v .nil
  | lvl : VTy (.lvl n) .level
  | predates : (∀ n ∈ x.levels, n < m) → VTy .tok (.predates A x (.lvl m))
  | subterm : Tm.PSub a b → VTy .tok (.subterm A a B b)
  | tyCtor : VTy (.tyc d) (.tyCtor ps)
  | vc : P.ctor d c = some sig → VTy (.vc d c) (.valCtor sig)
  | con : P.ctor d c = some sig → VTys vs sig (.bind (.ty mk me) T .nil) → T = .app (.tyc d) idx →
      VTy (.app (.vc d c) vs) T
  | clo : EnvOK env Γ → P.groups[gid]? = some G → GroupOK P gid Γ G → G.fns[j]? = some F →
      VTy (.clo (.ofList env) gid j) ((F.type G).subst (Tm.env env))

inductive VTys : Tm → Tm → Tm → Prop
  | nil : VTys .nil t t
  | cons : VTy v A → VTys vs (r.inst v 0) out → VTys (.cons v vs) (.bind (.ty m e) A r) out
  | isCons : v = e → VTys vs (r.inst v 0) out → VTys (.cons v vs) (.bind (.is _) e r) out

inductive EnvOK : List Tm → Ctx → Prop
  | mk : ρ.length = Γ.n →
      (∀ (i : Nat) (v T : Tm), ρ[i]? = some v → Γ.tys[i]? = some T → VTy v (T.subst (Tm.env ρ))) →
      (∀ v ∈ ρ, v.lc 0) → Sat (Tm.env ρ) Γ.σ →
      (∀ L ∈ Γ.mints, ∃ m, ρ[L]? = some (.lvl m) ∧ ∀ i < L, ∀ (v : Tm), ρ[i]? = some v → ∀ n ∈ v.levels, n < m) →
      Γ.WF → EnvOK ρ Γ
end

variable {P}

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

theorem canon_sound {Γ : Ctx} {f : Nat → Tm} (h : Sat f Γ.σ) (t : Tm) : (Γ.canon t).subst f = t.subst f := by
  simp only [Ctx.canon, Tm.subst_subst]
  congr 1; funext i
  cases e : Γ.σ i with
  | none => simp [Tm.subst]
  | some u => simp [h i u e]

theorem EnvOK.sat {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → Sat (Tm.env ρ) Γ.σ | .mk _ _ _ h _ _ => h
theorem EnvOK.wf {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → Γ.WF | .mk _ _ _ _ _ h => h
theorem EnvOK.len {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ρ.length = Γ.n | .mk h _ _ _ _ _ => h
theorem EnvOK.closed {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ∀ v ∈ ρ, v.lc 0 | .mk _ _ h _ _ _ => h
theorem EnvOK.vals {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ →
    ∀ (i : Nat) (v T : Tm), ρ[i]? = some v → Γ.tys[i]? = some T → VTy P v (T.subst (Tm.env ρ)) | .mk _ h _ _ _ _ => h

theorem EnvOK.canon {ρ : List Tm} {Γ : Ctx} (h : EnvOK P ρ Γ) (t : Tm) :
    (Γ.canon t).subst (Tm.env ρ) = t.subst (Tm.env ρ) := canon_sound h.sat t

theorem canon_static {Γ : Ctx} (hw : Γ.WF) {t : Tm} {d : Nat} (h : t.static Γ.n d) : (Γ.canon t).static Γ.n d :=
  Tm.static_subst t d h fun i hi => by
    cases e : Γ.σ i with
    | none => simp [Tm.static]; exact Tm.fvs_static t d h i hi
    | some u => simpa using (hw.σ i u e).2

theorem retOf_inst (u : Tm) : ∀ (t : Tm) k d idx, retOf t = some (.app (.tyc d) idx) →
    ∃ idx', retOf (t.inst u k) = some (.app (.tyc d) idx') := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro k d idx h
    cases r with
    | nil => cases m <;> simp [retOf] at h; subst h; simp [Tm.inst, retOf]
    | bind m' A' r' =>
      simp only [retOf] at h
      obtain ⟨idx', h'⟩ := ihr (k + 1) d idx h
      exact ⟨idx', by simpa [Tm.inst, retOf] using h'⟩
    | _ => simp [retOf] at h
  | _ => intro k d idx h; simp [retOf] at h

theorem VTys.nil_out' {vs out : Tm} : VTys P vs .nil out → out = .nil := by
  intro h; cases h; rfl

theorem VTys.retOf {vs tele out : Tm} :
    VTys P vs tele out → ∀ d idx, retOf tele = some (.app (.tyc d) idx) → out ≠ .nil → ∃ idx', retOf out = some (.app (.tyc d) idx')
  | .nil, d, idx, h, _ => ⟨idx, h⟩
  | .cons (r := r) _ hr, d, idx, h, hn | .isCons (r := r) _ hr, d, idx, h, hn => by
    cases r with
    | nil => exact absurd (VTys.nil_out' hr) hn
    | bind m' A' r' =>
      simp only [Minimal.retOf] at h
      obtain ⟨idx', h'⟩ := retOf_inst _ _ 0 d idx h
      exact VTys.retOf hr d idx' h' hn
    | _ => simp [Minimal.retOf] at h

theorem EnvOK.get {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {i : Nat} {T : Tm} (h : Γ.tys[i]? = some T) :
    ∃ v, ρ[i]? = some v ∧ Tm.env ρ i = v ∧ VTy P v (T.subst (Tm.env ρ)) := by
  have hi : i < ρ.length := by rw [hE.len]; exact (List.getElem?_eq_some_iff.mp h).1
  refine ⟨ρ[i], by simp, by simp [Tm.env, hi], hE.vals i _ T (by simp) h⟩

theorem VTy.vc_inv {v s : Tm} (h : VTy P v (.valCtor s)) : ∃ d c, v = .vc d c ∧ P.ctor d c = some s := by
  cases h with
  | vc hc => exact ⟨_, _, rfl, hc⟩
  | con _ _ he => cases he

mutual
theorem tm_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) : ∀ {t T : Tm}, TmTy P Γ t T →
    VTy P (t.subst (Tm.env ρ)) (T.subst (Tm.env ρ)) ∧ t.static Γ.n 0 ∧ T.static Γ.n 0
  | _, _, .fv h => by
    obtain ⟨v, _, he, hv⟩ := hE.get h
    refine ⟨by simpa [Tm.subst, he] using hv, ?_, hE.wf.tys _ _ h⟩
    exact decide_eq_true (List.getElem?_eq_some_iff.mp h).1
  | _, _, .fvIs (i := i) _ hs ht => by
    obtain ⟨hv, _, hT⟩ := tm_sound hP hE ht
    refine ⟨by simp only [Tm.subst]; rw [hE.sat i _ hs]; exact hv, decide_eq_true (hE.wf.σ i _ hs).1, hT⟩
  | _, _, .univ => ⟨.univ, rfl, rfl⟩
  | _, _, .level => ⟨.univ, rfl, rfl⟩
  | _, _, .tyc hD => ⟨.tyCtor, rfl, by
      simpa [Tm.static] using Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) (hP.params _ _ hD).2⟩
  | _, _, .vc (d := d) hc => by
    obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
    obtain ⟨_, hs0, _⟩ := hP.ctors _ _ _ _ hD hsig
    refine ⟨?_, rfl, by simpa [Tm.static] using Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) hs0⟩
    simp only [Tm.subst]; rw [Tm.subst_static0 _ _ 0 hs0]; exact .vc hc
  | _, _, .tyApp hh hH ha => by
    obtain ⟨_, hs, Hs⟩ := tm_sound hP hE hh
    have hps := canon_static hE.wf Hs; rw [hH] at hps
    have := args_sound hP hE ha (by simpa [Tm.static] using hps)
    exact ⟨.univ, by simp [Tm.static, hs, this.2.1], rfl⟩
  | _, _, .vcApp (H := H) hh hH ha => by
    obtain ⟨vh, hs, Hs⟩ := tm_sound hP hE hh
    have hps := canon_static hE.wf Hs; rw [hH] at hps
    rw [← hE.canon H, hH] at vh; simp only [Tm.subst] at vh
    obtain ⟨d, c, hv, hc⟩ := vh.vc_inv
    obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
    obtain ⟨_, _, idx, hr⟩ := hP.ctors _ _ _ _ hD hsig
    obtain ⟨hvs, hargs, hout⟩ := args_sound hP hE ha (by simpa [Tm.static] using hps)
    simp only [Tm.subst] at hvs
    obtain ⟨idx', hidx⟩ := VTys.retOf hvs d idx hr (by simp)
    simp [retOf] at hidx
    refine ⟨?_, by simp [Tm.static, hs, hargs], by simpa [Tm.static] using hout⟩
    simp only [Tm.subst]; rw [hv]; exact .con hc hvs hidx
  | _, _, .tyCtor _ hs => ⟨.univ, hs, rfl⟩
  | _, _, .valCtor _ hs _ => ⟨.univ, hs, rfl⟩
  | _, _, .predates hA _ hx _ hL _ => by
    have := tm_sound hP hE hA; have := tm_sound hP hE hx; have := tm_sound hP hE hL
    exact ⟨.univ, by simp_all [Tm.static], rfl⟩
  | _, _, .subterm hA _ ha _ hB _ hb _ => by
    have := tm_sound hP hE hA; have := tm_sound hP hE ha; have := tm_sound hP hE hB; have := tm_sound hP hE hb
    exact ⟨.univ, by simp_all [Tm.static], rfl⟩
  | _, _, .fn _ _ _ _ hs => ⟨.univ, hs, rfl⟩

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
end

theorem getElem?_append_cases {α : Type} {l1 l2 : List α} {i : Nat} {x : α} (h : (l1 ++ l2)[i]? = some x) :
    (i < l1.length ∧ l1[i]? = some x) ∨ (l1.length ≤ i ∧ l2[i - l1.length]? = some x) := by
  rw [List.getElem?_append] at h; split at h
  · exact .inl ⟨by omega, h⟩
  · exact .inr ⟨by omega, h⟩

theorem Ctx.WF.mono {Γ : Ctx} (h : Γ.WF) (Ts : List Tm) (hT : ∀ T ∈ Ts, T.static Γ.n 0) :
    ({ Γ with tys := Γ.tys ++ Ts } : Ctx).WF := by
  have hn : Γ.n ≤ ({ Γ with tys := Γ.tys ++ Ts } : Ctx).n := by simp [Ctx.n]
  refine ⟨fun i T hi => ?_, fun e t he => ?_, fun L hL => ?_, fun c hc => ?_, fun s hs => ?_⟩
  · rcases getElem?_append_cases hi with ⟨hi, hT'⟩ | ⟨hi, hT'⟩ <;>
      exact Tm.static_mono hn _ (Nat.le_refl 0) (by first | exact h.tys i T hT' | exact hT T (List.mem_of_getElem? hT'))
  · exact ⟨Nat.lt_of_lt_of_le (h.σ e t he).1 hn, Tm.static_mono hn _ (Nat.le_refl 0) (h.σ e t he).2⟩
  · exact Nat.lt_of_lt_of_le (h.mints L hL) hn
  · exact Nat.lt_of_lt_of_le (h.cur c hc) hn
  · exact Nat.lt_of_lt_of_le (h.subs s hs) hn

theorem EnvOK.pushMany {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (vs Ts : List Tm) (hl : vs.length = Ts.length)
    (hv : ∀ (j : Nat) (v T : Tm), vs[j]? = some v → Ts[j]? = some T →
      VTy P v (T.subst (Tm.env ρ)) ∧ T.static Γ.n 0 ∧ v.lc 0) :
    EnvOK P (ρ ++ vs) { Γ with tys := Γ.tys ++ Ts } := by
  have hlen := hE.len
  have hwf := hE.wf
  have hT : ∀ T ∈ Ts, T.static Γ.n 0 := fun T hT => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT
    exact (hv j vs[j] _ (List.getElem?_eq_getElem (by omega)) (by simp)).2.1
  refine .mk (by simp [Ctx.n] at *; omega) (fun i v T hi hTi => ?_) (fun v hv' => ?_) (fun e t he => ?_)
    (fun L hL => ?_) (hwf.mono Ts hT)
  · have hn : ρ.length = Γ.tys.length := hlen
    rcases getElem?_append_cases hTi with ⟨hi', hT'⟩ | ⟨hi', hT'⟩
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
  · obtain ⟨m, hm, hlt⟩ := (match hE with | .mk _ _ _ _ h _ => h) L hL
    have hL' : L < ρ.length := hlen ▸ hwf.mints L hL
    refine ⟨m, by rw [List.getElem?_append_left hL']; exact hm, fun i hi v hv => ?_⟩
    rw [List.getElem?_append_left (by omega)] at hv
    exact hlt i hi v hv

def Chrono (ρ : List Tm) (L : Nat) : Prop :=
  ∃ m, ρ[L]? = some (.lvl m) ∧ ∀ i < L, ∀ (v : Tm), ρ[i]? = some v → ∀ n ∈ v.levels, n < m

theorem EnvOK.chrono {ρ : List Tm} {Γ : Ctx} : EnvOK P ρ Γ → ∀ L ∈ Γ.mints, Chrono ρ L
  | .mk _ _ _ _ h _ => h

theorem EnvOK.modify {ρ : List Tm} {Γ Γ' : Ctx} (hE : EnvOK P ρ Γ) (ht : Γ'.tys = Γ.tys)
    (hσ : Sat (Tm.env ρ) Γ'.σ) (hm : ∀ L ∈ Γ'.mints, Chrono ρ L) (hw : Γ'.WF) : EnvOK P ρ Γ' :=
  .mk (by rw [hE.len]; simp [Ctx.n, ht]) (fun i v T h1 h2 => hE.vals i v T h1 (ht ▸ h2)) hE.closed hσ hm hw

theorem EnvOK.withRule {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {e : Nat} {t : Tm} (he : e < Γ.n)
    (ht : t.static Γ.n 0) (hv : Tm.env ρ e = t.subst (Tm.env ρ)) : EnvOK P ρ (Γ.withRule e t) := by
  refine hE.modify rfl (fun i u hi => ?_) hE.chrono ⟨hE.wf.tys, fun i u hi => ?_, hE.wf.mints, hE.wf.cur, hE.wf.subs⟩
  all_goals simp only [Ctx.withRule] at hi; split at hi
  · cases hi; subst_vars; exact hv
  · exact hE.sat i u hi
  · cases hi; subst_vars; exact ⟨he, ht⟩
  · exact hE.wf.σ i u hi

theorem EnvOK.congr {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) (Γ' : Ctx) (ht : Γ'.tys = Γ.tys)
    (hσ : Γ'.σ = Γ.σ) (hm : Γ'.mints = Γ.mints) (hc : Γ'.cur = Γ.cur) (hs : Γ'.subs = Γ.subs) : EnvOK P ρ Γ' := by
  have hn : Γ'.n = Γ.n := by simp [Ctx.n, ht]
  have w := hE.wf
  refine hE.modify ht (by rw [hσ]; exact hE.sat) (by rw [hm]; exact hE.chrono) ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i T h; rw [hn]; exact w.tys i T (ht ▸ h)
  · intro e t h; rw [hn]; exact w.σ e t (hσ ▸ h)
  · intro L h; rw [hn]; exact w.mints L (hm ▸ h)
  · intro c h; rw [hn]; exact w.cur c (hc ▸ h)
  · intro s h; rw [hn]; exact w.subs s (hs ▸ h)

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
    exact ⟨w.tys, w.σ, fun L hL => by
      simp only [Ctx.pushMint, List.mem_append, List.mem_singleton] at hL
      rcases hL with hL | rfl
      · exact w.mints L hL
      · simp [Ctx.pushMint, Ctx.push, Ctx.n], w.cur, w.subs⟩

theorem Tm.isTele_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).isTele := by
  intro t; induction t <;> intro k h <;> simp_all [isTele, inst]

theorem Tm.isTele_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele → (t.subst f).isTele := by
  intro t; induction t <;> intro h <;> simp_all [isTele, subst]

structure Ctx.Ext (Γ Γ' : Ctx) : Prop where
  tys : ∃ Ts, Γ'.tys = Γ.tys ++ Ts
  σ : ∀ e t, Γ.σ e = some t → Γ'.σ e = some t
  mints : Γ'.mints = Γ.mints
  cur : Γ'.cur = Γ.cur
  subs : Γ'.subs = Γ.subs

theorem Ctx.Ext.trans {Γ Γ' Γ'' : Ctx} (h1 : Γ.Ext Γ') (h2 : Γ'.Ext Γ'') : Γ.Ext Γ'' := by
  obtain ⟨Ts, e1⟩ := h1.tys; obtain ⟨Us, e2⟩ := h2.tys
  exact ⟨⟨Ts ++ Us, by rw [e2, e1, List.append_assoc]⟩, fun e t h => h2.σ e t (h1.σ e t h),
    h2.mints.trans h1.mints, h2.cur.trans h1.cur, h2.subs.trans h1.subs⟩

theorem EnvOK.pushEnt {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {k : Ent} {A r v vs out : Tm}
    (hv : VTys P (.cons v vs) (.bind k (A.subst (Tm.env ρ)) (r.subst (Tm.env ρ))) out) (hA : A.static Γ.n 0)
    (hc : v.lc 0) :
    EnvOK P (ρ ++ [v]) (Γ.pushEnt k A) ∧ VTys P vs ((r.subst (Tm.env ρ)).inst v 0) out ∧
      Γ.Ext (Γ.pushEnt k A) ∧ (Γ.pushEnt k A).n = Γ.n + 1 := by
  have ext : ∀ T e, Γ.Ext (Γ.push T e) := fun T _ => ⟨⟨[T], rfl⟩, fun _ _ h => h, rfl, rfl, rfl⟩
  cases hv with
  | cons hvA hvs => exact ⟨hE.push hvA hA hc, hvs, ext A _, by simp [Ctx.pushEnt, Ctx.push, Ctx.n]⟩
  | isCons he hvs =>
    have hl := hE.len
    have hs := canon_static hE.wf hA
    refine ⟨(hE.push .top rfl hc).withRule (by simp [Ctx.push, Ctx.n])
      (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_, hvs,
      ⟨⟨[.nil], rfl⟩, fun e t h => ?_, rfl, rfl, rfl⟩, by simp [Ctx.pushEnt, Ctx.withRule, Ctx.push, Ctx.n]⟩
    · rw [Tm.subst_append (hl ▸ hs), hE.canon, ← he]
      simp [Tm.env, hl]
    · have := (hE.wf.σ e t h).1
      simp only [Ctx.pushEnt, Ctx.withRule, Ctx.push]
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
    exact ⟨hE, trivial, hs, ht, by simp, ⟨[], by simp⟩, fun _ _ h => h, rfl, rfl, rfl⟩
  | _ => intro out ht hs hv hc; cases hv

theorem VTy.fn_inv {v l t : Tm} {np : Nat} (h : VTy P v (.fn l np t)) :
    ∃ env Γ gid G j F, v = .clo (.ofList env) gid j ∧ EnvOK P env Γ ∧ P.groups[gid]? = some G ∧
      GroupOK P gid Γ G ∧ G.fns[j]? = some F ∧ (F.type G).subst (Tm.env env) = .fn l np t := by
  cases h with
  | clo hE hG hok hF => exact ⟨_, _, _, _, _, _, rfl, hE, hG, hok, hF, rfl⟩
  | con _ _ he => cases he

theorem VTy.ty_inv {v idx : Tm} {d : Nat} (h : VTy P v (.app (.tyc d) idx)) :
    ∃ c vs sig mk me, v = .app (.vc d c) vs ∧ P.ctor d c = some sig ∧ VTys P vs sig (.bind (.ty mk me) (.app (.tyc d) idx) .nil) := by
  cases h with
  | con hc hv he => cases he; exact ⟨_, _, _, _, _, rfl, hc, hv⟩

theorem VTy.level_inv {v : Tm} (h : VTy P v .level) : ∃ n, v = .lvl n := by
  cases h with
  | lvl => exact ⟨_, rfl⟩
  | con _ _ he => cases he

theorem VTy.predates_inv {v A x L : Tm} (h : VTy P v (.predates A x L)) :
    ∃ m, L = .lvl m ∧ ∀ n ∈ x.levels, n < m := by
  cases h with
  | predates h => exact ⟨_, rfl, h⟩
  | con _ _ he => cases he

theorem VTy.subterm_inv {v A a B b : Tm} (h : VTy P v (.subterm A a B b)) : Tm.PSub a b := by
  cases h with
  | subterm h => exact h
  | con _ _ he => cases he

theorem closures_get {env : List Tm} {gid : Nat} {G : Group} {j : Nat} {v : Tm}
    (h : (closures env gid G)[j]? = some v) : j < G.fns.length ∧ v = .clo (.ofList env) gid j := by
  simp only [closures, List.getElem?_map] at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.getElem?_eq_some_iff.mp hk
  simp at this; obtain ⟨h1, rfl⟩ := this; exact ⟨h1, rfl⟩

theorem EnvOK.pushFns (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {gid : Nat} {G : Group}
    (hG : P.groups[gid]? = some G) (hok : GroupOK P gid Γ G) :
    EnvOK P (ρ ++ closures ρ gid G) (Γ.pushFns G) := by
  cases hok with
  | mk hK hl hty hm hb he hg =>
  refine EnvOK.congr (hE.pushMany _ _ (by simp [closures]) fun j v T h1 h2 => ?_) _ rfl rfl rfl rfl rfl
  obtain ⟨hj, rfl⟩ := closures_get h1
  simp only [List.getElem?_map] at h2
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp h2
  exact ⟨.clo hE hG (.mk hK hl hty hm hb he hg) hF, (tm_sound hP hE (hty j F hF)).2.1, trivial⟩

namespace Tm

theorem levels_static {n : Nat} : ∀ (t : Tm) d, t.static n d → t.levels = [] := by
  intro t; induction t <;> intro d h <;> simp_all [static, levels] <;> grind

theorem levels_subst (f : Nat → Tm) : ∀ (t : Tm), ∀ x ∈ (t.subst f).levels, x ∈ t.levels ∨ ∃ i ∈ t.fvs, x ∈ (f i).levels := by
  intro t; induction t <;> simp_all [subst, levels, fvs] <;> grind

theorem levels_toList : ∀ (t : Tm), ∀ v ∈ t.toList, ∀ x ∈ v.levels, x ∈ t.levels := by
  intro t; induction t <;> simp_all [toList, levels] <;> grind

theorem levels_ofList : ∀ (l : List Tm), ∀ x ∈ (ofList l).levels, ∃ v ∈ l, x ∈ v.levels := by
  intro l; induction l <;> simp_all [ofList, levels] <;> grind

theorem lc_toList : ∀ (t : Tm) d, t.lc d → ∀ v ∈ t.toList, v.lc d := by
  intro t; induction t <;> intro d h v hv <;> simp_all [toList, lc] <;> grind

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

theorem toList_ofList : ∀ (l : List Tm), (ofList l).toList = l := by
  intro l; induction l <;> simp_all [ofList, toList]

theorem ofList_toList : ∀ (t : Tm), t.isList → ofList t.toList = t := by
  intro t; induction t <;> simp_all [ofList, toList, isList]

theorem toList_subst (f : Nat → Tm) : ∀ (t : Tm), t.isList → (t.subst f).toList = t.toList.map (subst f) := by
  intro t; induction t <;> simp_all [toList, subst, isList]

theorem isList_subst (f : Nat → Tm) : ∀ (t : Tm), t.isList → (t.subst f).isList := by
  intro t; induction t <;> simp_all [subst, isList]

theorem len_toList : ∀ (t : Tm), t.isList → t.toList.length = t.len := by
  intro t; induction t <;> simp_all [toList, isList, len]

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
      rcases m with ⟨⟨⟩⟩ | _ <;> simp [Ent.marked] <;> omega
    | _ => simp [markedArgs]
  | _ => intro args _; cases args <;> simp [markedArgs]

theorem Tm.len_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele ∨ t.isList → (t.subst f).len = t.len := by
  intro t; induction t <;> intro h <;> simp_all [subst, len, isTele, isList]

theorem Tm.len_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).len = t.len := by
  intro t; induction t <;> intro k h <;> simp_all [inst, len, isTele]

theorem Tm.isTele_of_inst_fv (i : Nat) : ∀ (t : Tm) k, (t.inst (.fv i) k).isTele → t.isTele := by
  intro t; induction t with
  | bind _ _ r _ ihr => intro k h; simp only [inst, isTele] at h ⊢; exact ihr _ h
  | bv j => intro k h; simp only [inst] at h; split at h <;> (try split at h) <;> simp [isTele] at h
  | _ => intro k h; simp_all [inst, isTele]

theorem TeleOK.isTele {Γ : Ctx} {t : Tm} : TeleOK P Γ t → t.isTele
  | .nil => rfl
  | .cons _ _ h => by simp only [Tm.isTele]; exact Tm.isTele_of_inst_fv _ _ 0 h.isTele
  | .isCons _ h => by simp only [Tm.isTele]; exact Tm.isTele_of_inst_fv _ _ 0 h.isTele

theorem ArgsTy.isList {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → args.isList
  | .nil => rfl
  | .cons _ _ h | .isCons _ _ h => by simp only [Tm.isList]; exact h.isList

theorem ArgsTy.isTele {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → out.isTele
  | .nil, h => h
  | .cons _ _ hr, h | .isCons _ _ hr, h => hr.isTele (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h))

theorem ArgsTy.len {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → args.len + out.len = tele.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ _ hr, h | .isCons (r := r) _ _ hr, h => by
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

theorem VTys.isList {vs tele out : Tm} : VTys P vs tele out → vs.isList
  | .nil => rfl
  | .cons _ hr | .isCons _ hr => by simp only [Tm.isList]; exact hr.isList

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
      (Γ.setErs Γ' ov).mints = Γ'.mints ∧ (Γ.setErs Γ' ov).cur = Γ'.cur ∧ (Γ.setErs Γ' ov).subs = Γ'.subs := by
    intro Γ'; cases ov <;> simp [Ctx.setErs]
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf (Γ.openTele tele tele.len).1
  refine ⟨h1.congr _ f1 f2 f3 f4 f5, f4.trans h6.cur, f5.trans h6.subs, ?_⟩
  show Γ.tys.length ≤ (Γ.setErs (Γ.openTele tele tele.len).1 ov).tys.length
  rw [f1]; simp only [Ctx.n] at h5; omega

theorem lc_of_static {ρ : List Tm} (hc : ∀ v ∈ ρ, v.lc 0) {t : Tm} {n : Nat} (h : t.static n 0) :
    (t.subst (Tm.env ρ)).lc 0 := Tm.lc_subst (Tm.env_lc hc) t 0 n h

theorem static_toList {t : Tm} {n : Nat} (h : t.static n 0) : ∀ v ∈ t.toList, v.static n 0 := by
  induction t <;> simp_all [Tm.toList, Tm.static]

theorem prim_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {p : Prim} {T : Tm} (h : PrimTy P Γ p T) :
    VTy P (p.eval ρ) (T.subst (Tm.env ρ)) ∧ T.static Γ.n 0 ∧ (p.eval ρ).lc 0 ∧ ∀ x ∈ (p.eval ρ).levels, x < cnt := by
  have hw := hE.wf
  have stat : ∀ {t T : Tm}, TmTy P Γ t T → (Γ.canon T).static Γ.n 0 := fun ht =>
    canon_static hw (tm_sound hP hE ht).2.2
  have sem : ∀ {t T : Tm}, TmTy P Γ t T → VTy P (t.subst (Tm.env ρ)) ((Γ.canon T).subst (Tm.env ρ)) := fun ht => by
    rw [hE.canon]; exact (tm_sound hP hE ht).1
  cases h with
  | tm ht =>
    obtain ⟨hv, hs, hT⟩ := tm_sound hP hE ht
    exact ⟨hv, hT, lc_of_static hE.closed hs, hb.subst hs⟩
  | proveSubterm ha hb' hst =>
    obtain ⟨_, has, hA⟩ := tm_sound hP hE ha
    obtain ⟨_, hbs, hB⟩ := tm_sound hP hE hb'
    have := Tm.psub_subst (Tm.env ρ) (Tm.strictSub_psub _ _ hst)
    rw [hE.canon, hE.canon] at this
    exact ⟨.subterm this, by simp [Tm.static, hA, has, hB, hbs], trivial, by simp [Prim.eval, Tm.levels]⟩
  | provePredates hx hL hX =>
    rename_i x L X
    obtain ⟨m, hm, hlt⟩ := hE.chrono L hL
    have hLn := hw.mints L hL
    have hl := hE.len
    have hxl : x < ρ.length := by omega
    have hxv : ρ[x]? = some ρ[x] := List.getElem?_eq_getElem hxl
    refine ⟨?_, ?_, trivial, by simp [Prim.eval, Tm.levels]⟩
    · have e : Tm.env ρ L = .lvl m := by simp [Tm.env, hm]
      simp only [Tm.subst, e]
      exact .predates fun n hn => hlt x hx _ hxv n (by simpa [Tm.env, hxv] using hn)
    · simp [Tm.static, hw.tys _ _ hX]; omega
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
    (he : v = p.eval ρ) :
    EnvOK P (ρ ++ [v]) (Γ.pushPrim T er p) ∧ (Γ.pushPrim T er p).cur = Γ.cur ∧
      (Γ.pushPrim T er p).subs = Γ.subs ∧ (Γ.pushPrim T er p).n = Γ.n + 1 := by
  have h1 := hE.push hv hT hc (e := er)
  refine ⟨?_, by cases p <;> rfl, by cases p <;> rfl, by cases p <;> simp [Ctx.pushPrim, Ctx.withRule, Ctx.push, Ctx.n]⟩
  cases hp with
  | tm ht =>
    have hl := hE.len
    have hs := canon_static hE.wf (tm_sound hP hE ht).2.1
    refine h1.withRule (by simp [Ctx.push, Ctx.n]) (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_
    rw [Tm.subst_append (hl ▸ hs), hE.canon, he]
    simp [Tm.env, hl, Prim.eval]
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
  | autoSub hc hl' hai hsi hpre hst =>
    have hps := Tm.psub_subst (Tm.env ρ) (Tm.strictSub_psub _ _ hst)
    rw [hE.canon, hE.canon] at hps
    exact dec_same hE (by unfold MuOK; exact hm) hal hl hk hc hl' hai hsi hpre hps
  | autoPred hc hx hxc hcm =>
    rename_i c x
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

namespace Tm

def ers : Tm → List Bool
  | bind k _ r => k.er :: r.ers
  | _ => []

theorem ers_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).ers = t.ers := by
  intro t; induction t <;> intro k h <;> simp_all [inst, ers, isTele]

theorem ers_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele → (t.subst f).ers = t.ers := by
  intro t; induction t <;> intro h <;> simp_all [subst, ers, isTele]

end Tm

theorem Real.nil' (vS : Tm) : Real P vS .nil := .other (by simp) (by simp) (by simp)

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
  | .cons .., .tyc _, h | .cons .., .vc .., h | .cons .., .tyCtor _, h | .cons .., .valCtor _, h
  | .cons .., .univ, h | .cons .., .level, h | .cons .., .predates .., h | .cons .., .subterm .., h
  | .cons .., .fn .., h | .cons .., .lvl _, h | .cons .., .tok, h | .cons .., .clo .., h => by simp [rtArgs] at h
  | .fv _, _, h | .bv _, _, h | .bind .., _, h | .app .., _, h | .tyc _, _, h | .vc .., _, h | .tyCtor _, _, h
  | .valCtor _, _, h | .univ, _, h | .level, _, h | .predates .., _, h | .subterm .., _, h | .fn .., _, h
  | .lvl _, _, h | .tok, _, h | .clo .., _, h => by simp [rtArgs] at h

theorem Real.vc_inv {vS : Tm} {d c : Nat} (h : Real P vS (.vc d c)) : vS = .vc d c ∧ P.phantom d c = false := by
  cases h with
  | vc h => exact ⟨rfl, h⟩
  | other _ h2 _ => exact absurd rfl (h2 _ _)

mutual
theorem rt_real {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ (t : Tm), rt P Γ t = true → Real P (t.subst (Tm.env ρS)) (t.subst (Tm.env ρ))
  | .fv i, h => by simp only [rt, Bool.not_eq_eq_eq_not, Bool.not_true] at h; exact hS.2 i h
  | .app hd args, h => by
    cases hd with
    | vc d c =>
      simp only [rt] at h
      split at h
      · rename_i sig hc
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        exact .con hc h.1 (rtArgs_reals hE hS args sig h.2)
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
        obtain ⟨d, c, rfl, hc⟩ := hv.vc_inv
        have hR := hS.2 i h.1; rw [hev] at hR
        simp only [Tm.subst]; rw [hev, hR.vc_inv.1]
        exact .con hc hR.vc_inv.2 (rtArgs_reals hE hS args _ (rtArgs_subst _ args sig h.2))
      · rename_i ps heq
        simp only [Option.map_eq_some_iff] at heq
        obtain ⟨T, hT, hcT⟩ := heq
        obtain ⟨v, -, hev, hv⟩ := hE.get hT
        rw [← hE.canon, hcT] at hv; simp only [Tm.subst] at hv
        cases hv with
        | tyCtor => simp only [Tm.subst]; rw [hev]; exact .other (by simp) (by simp) (by simp)
        | con _ _ he => cases he
      · simp at h
    | tyc _ => exact .other (by simp [Tm.subst]) (by simp [Tm.subst]) (by simp [Tm.subst])
    | _ => simp [rt] at h
  | .vc _ _, h => by simp only [Tm.subst]; exact .vc (by simpa [rt] using h)
  | .tyc _, _ | .tyCtor _, _ | .valCtor _, _ | .univ, _ | .level, _ | .predates .., _ | .subterm .., _
  | .fn .., _ => .other (by simp [Tm.subst]) (by simp [Tm.subst]) (by simp [Tm.subst])
  | .nil, h | .bv _, h | .cons .., h | .bind .., h | .lvl _, h | .tok, h | .clo .., h => by simp [rt] at h

theorem rtArgs_reals {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ (args tele : Tm), rtArgs P Γ args tele = true →
      Reals P (args.subst (Tm.env ρS)) (args.subst (Tm.env ρ)) tele
  | .nil, _, _ => .nil
  | .cons a as, .bind k _ r, h => by
    simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
    exact .cons (fun hk => rt_real hE hS a (by simpa [hk] using h.1)) (rtArgs_reals hE hS as r h.2)
  | .cons .., .nil, h | .cons .., .fv _, h | .cons .., .bv _, h | .cons .., .cons .., h | .cons .., .app .., h
  | .cons .., .tyc _, h | .cons .., .vc .., h | .cons .., .tyCtor _, h | .cons .., .valCtor _, h
  | .cons .., .univ, h | .cons .., .level, h | .cons .., .predates .., h | .cons .., .subterm .., h
  | .cons .., .fn .., h | .cons .., .lvl _, h | .cons .., .tok, h | .cons .., .clo .., h => by simp [rtArgs] at h
  | .fv _, _, h | .bv _, _, h | .bind .., _, h | .app .., _, h | .tyc _, _, h | .vc .., _, h | .tyCtor _, _, h
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
      have her : ∀ i, (Γ.pushEnt k A).er i = if i = Γ.n then k.er else Γ.er i := by intro i; cases k <;> rfl
      obtain ⟨g, h1, h2⟩ := ih (Γ.pushEnt k A) (r.inst (.fv Γ.n) 0) (Tm.isTele_inst _ r 0 ht)
      simp only [Ctx.openTele]
      refine ⟨by rw [g]; cases k <;> rfl, fun i hi => by rw [h1 i (by omega), her, if_neg (by omega)], ?_⟩
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
    · simp only [Ctx.pushTele, Ctx.setErs]; rw [if_neg (by omega)]; exact h1 i hi
    · simp [Ctx.pushTele, Ctx.setErs]

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
    ∃ envS env G F, vS = .clo (.ofList envS) gid j ∧ e = .ofList env ∧ P.groups[gid]? = some G ∧
      G.ghost = false ∧ G.fns[j]? = some F ∧ F.er = false ∧ SimEnv P (fun i => G.ers.getD i true) envS env := by
  cases h with
  | clo hG hg hF hf hl hr => exact ⟨_, _, _, _, rfl, rfl, hG, hg, hF, hf, hl, hr⟩
  | other _ _ h3 => exact absurd rfl (h3 _ _ _)

theorem Real.con_inv {vS : Tm} {d c : Nat} {vs : Tm} (h : Real P vS (.app (.vc d c) vs)) :
    ∃ vsS sig, vS = .app (.vc d c) vsS ∧ P.ctor d c = some sig ∧ P.phantom d c = false ∧ Reals P vsS vs sig := by
  cases h with
  | con hc hp hr => exact ⟨_, _, rfl, hc, hp, hr⟩
  | other h1 _ => exact absurd rfl (h1 _ _ _)

theorem selectBr_same {brs : List (Nat × Nat × Core)} {els : Option Core} {c : Nat} {vs vs' pre : List Tm}
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
  | _ :: _, .cons .., _, _, hk, _ | _ :: _, .app .., _, _, hk, _ | _ :: _, .tyc _, _, _, hk, _
  | _ :: _, .vc .., _, _, hk, _ | _ :: _, .tyCtor _, _, _, hk, _ | _ :: _, .valCtor _, _, _, hk, _
  | _ :: _, .univ, _, _, hk, _ | _ :: _, .level, _, _, hk, _ | _ :: _, .predates .., _, _, hk, _
  | _ :: _, .subterm .., _, _, hk, _ | _ :: _, .fn .., _, _, hk, _ | _ :: _, .lvl _, _, _, hk, _
  | _ :: _, .tok, _, _, hk, _ | _ :: _, .clo .., _, _, hk, _ => by simp [Tm.ers] at hk

theorem call_setup (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {f Ft l t args outsT : Tm} {np : Nat} {dec : Dec}
    (hf : TmTy P Γ f Ft) (hF : Γ.canon Ft = .fn l np t) (ht : t.isTele) (ha : ArgsTy P Γ args t outsT)
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
        Γb.ghost = (G.ghost || F.er) ∧ (∀ i < env.length, Γb.er i = G.ers.getD i true) ∧
        (∀ j' F', G.fns[j']? = some F' → Γb.er (env.length + j') = F'.er) ∧
        (∀ k < np, Γb.er (env.length + G.fns.length + k) = t.ers.getD k true) ∧ rb.isTele) ∧
      outsT.isTele ∧ outsT.static Γ.n 0 := by
  have hw := hE.wf
  obtain ⟨hv, hfs, hFs⟩ := tm_sound hP hE hf
  have hFs' := canon_static hw hFs
  rw [hF] at hFs'; simp only [Tm.static, Bool.and_eq_true] at hFs'
  rw [← hE.canon Ft, hF] at hv; simp only [Tm.subst] at hv
  obtain ⟨env, Γc, gid, G, j, F, hfv, hEc, hG, hok, hFj, hty⟩ := hv.fn_inv
  simp only [FnDef.type, Tm.subst, Tm.fn.injEq] at hty
  obtain ⟨hlv, hnp, htele⟩ := hty
  have hok' := hok
  cases hok with
  | mk hK hKl htyF hmk hbody hGe hg =>
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
  refine ⟨env, n1, gid, G, F, ?_, ?_, ?_, ha.isTele ht, hos⟩
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
    refine ⟨(Γc.body G F).1, (Γc.body G F).2, hbody j F hFj, ?_, ?_, ?_, ?_, ?_,
      by simp [Ctx.body, hg], fun i hi => ?_, fun j' F' hF' => ?_, fun k hk => ?_, ?_⟩
    rotate_left 5
    · show ((Γc.pushFns G).openTele F.tele F.np).1.er i = _
      rw [o1 i (by omega)]; simp only [Ctx.pushFns]; rw [if_neg (by omega)]; exact hGe i (by omega)
    · show ((Γc.pushFns G).openTele F.tele F.np).1.er _ = _
      have hj' := (List.getElem?_eq_some_iff.mp hF').1
      rw [o1 _ (by omega)]; simp only [Ctx.pushFns]; rw [if_pos (by omega)]; simp [← hle, hF']
    · show ((Γc.pushFns G).openTele F.tele F.np).1.er _ = _
      rw [← hpn, o2 k (by omega) (by rw [Tm.len_ers _ hFtele]; omega), ← Tm.ers_subst (Tm.env env) _ hFtele, htele,
        Tm.ers_subst _ _ ht]
    · simp only [Ctx.body]; exact h4
    · simp only [Ctx.body]
      refine h1.modify rfl h1.sat h1.chrono ⟨h1.wf.tys, h1.wf.σ, h1.wf.mints, fun c hc => ?_, fun s hs => ?_⟩
      · simp at hc; subst hc
        have := (List.getElem?_eq_some_iff.mp hK).1
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
      · have : G.lvl < env.length := by rw [hle]; exact (List.getElem?_eq_some_iff.mp hK).1
        rw [List.append_assoc, List.getElem?_append_left this]; exact hlv'
      · congr 2
        rw [fv_filterMap_env _ Tm.size _ (fun x hx => by obtain ⟨i, h, _⟩ := hfields x hx; exact ⟨i, h⟩),
          ← markedArgs_subst_args _ _ _ (fields_isList _ _), ← hlenl, fields_subst _ hl1]
    · simp only [Ctx.body]; simpa [Ctx.n] using h3
    · simp only [Ctx.body]; simpa using h2

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
        cases k <;> rfl
      rw [this]; exact ih _ _
    | _ => rfl

theorem Ctx.branch_ghost (g : Bool) (Γ : Ctx) (s : Tm) (d c : Nat) (idx sig : Tm) :
    ({ Γ with ghost := g } : Ctx).branch s d c idx sig =
      ({ (Γ.branch s d c idx sig).1 with ghost := g }, (Γ.branch s d c idx sig).2) := by
  simp only [Ctx.branch, Ctx.openTele_ghost]
  split <;> rfl

theorem match_setup (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {s St idx R : Tm} {d bnd : Nat} {D : Adt}
    {brs : List (Nat × Nat × Core)} {els : Option Core} {g : Nat → Bool} {ge : Bool}
    (hs : TmTy P Γ s St) (hS : Γ.canon St = .app (.tyc d) idx) (hD : P.adts[d]? = some D)
    (hbr : ∀ (c : Nat) sig, D.ctors[c]? = some sig →
      BranchOK P bnd { Γ with ghost := g c } s d idx c sig R (lookupBr brs c) els.isSome)
    (hel : ∀ e, els = some e → CoreTy P bnd { Γ with ghost := ge } e R) (hRs : R.static Γ.n 0) :
    ∃ c vs, s.subst (Tm.env ρ) = .app (.vc d c) vs ∧ ∃ pre body, selectBr brs els c vs.toList = some (pre, body) ∧
      ∃ Γ', CoreTy P bnd Γ' body R ∧ EnvOK P (ρ ++ pre) Γ' ∧ LvlBound (ρ ++ pre) cnt ∧
        MuOK μ Γ' (ρ ++ pre) ∧ R.static Γ'.n 0 ∧ (Γ'.ghost = g c ∨ Γ'.ghost = ge) ∧ (∀ i < Γ.n, Γ'.er i = Γ.er i) ∧
        ∀ sig, P.ctor d c = some sig → ∀ k < pre.length, Γ'.er (Γ.n + k) = sig.ers.getD k true := by
  have hw := hE.wf
  have hl := hE.len
  obtain ⟨hv, hss, hSs⟩ := tm_sound hP hE hs
  have hSs' := canon_static hw hSs
  rw [hS] at hSs'; simp only [Tm.static] at hSs'
  rw [← hE.canon St, hS] at hv; simp only [Tm.subst] at hv
  obtain ⟨c, vs, sig, mk, me, hsv, hctor, hvs⟩ := hv.ty_inv
  have hsig : D.ctors[c]? = some sig := by simpa [Prog.ctor, hD] using hctor
  obtain ⟨hsigT, hsig0, _⟩ := hP.ctors d D c sig hD hsig
  have hst : sig.isTele := hsigT.isTele
  have hsigs : sig.static Γ.n 0 := Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) hsig0
  have hsub : sig.subst (Tm.env ρ) = sig := Tm.subst_static0 _ _ 0 hsig0
  have hlen := hvs.len hst
  simp only [Tm.len] at hlen
  have hlc : ∀ v ∈ vs.toList, v.lc 0 := fun v hv' => by
    have : (s.subst (Tm.env ρ)).lc 0 := lc_of_static hE.closed hss
    rw [hsv] at this; simp only [Tm.lc] at this
    exact Tm.lc_toList vs 0 this.2 v hv'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hE.openTele hst hsigs (hsub ▸ hvs) hlc
  have hm' : vs.len = sig.len - 1 := by omega
  rw [hm'] at h1 h2 h3 h4 h5 h6
  generalize hpr : Γ.openTele sig (sig.len - 1) = pr at h1 h2 h3 h4 h5 h6
  obtain ⟨Γf, rem⟩ := pr
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨Rc, rfl, hRc⟩ := Tm.tele_one h4 h2
  have hbranch : Γ.branch s d c idx sig =
      (Γf, unify Γf.n Γf.σ [] [(Γ.canon s, Γf.canon (.app (.vc d c) (Γ.fields (sig.len - 1)))), (Γ.canon (.app (.tyc d) idx), Γf.canon Rc)]) := by
    simp [Ctx.branch, hpr]
  have hEf := h1
  have hvl : vs.toList.length = sig.len - 1 := by rw [Tm.len_toList _ hvs.isList, hm']
  have hsat : Sat (Tm.env (ρ ++ vs.toList)) Γ.σ := fun e t he => hEf.sat e t (h6.σ e t he)
  have heqs : ∀ p ∈ [(Γ.canon s, Γf.canon (Tm.app (.vc d c) (Γ.fields (sig.len - 1)))), (Γ.canon (.app (.tyc d) idx), Γf.canon Rc)],
      p.1.subst (Tm.env (ρ ++ vs.toList)) = p.2.subst (Tm.env (ρ ++ vs.toList)) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp only
      rw [canon_sound (Γ := Γ) hsat, canon_sound hEf.sat, Tm.subst_append (hl ▸ hss), hsv, ← hvl]
      simp only [Tm.subst]; rw [fields_subst _ hl, Tm.ofList_toList _ hvs.isList]
    · simp only
      rw [canon_sound (Γ := Γ) hsat, canon_sound hEf.sat, hRc,
        Tm.subst_append (t := Tm.app (.tyc d) idx) (by simpa [Tm.static, hl] using hSs')]
      simp [Tm.subst]
  have hun := unify_sound (Tm.env (ρ ++ vs.toList)) (fun i => Tm.bound_of_lc _ 0 (Tm.env_lc hEf.closed i)) Γf.n Γf.σ [] _ hEf.sat heqs
  refine ⟨c, vs, hsv, ?_⟩
  have hbr' := hbr c sig hsig
  generalize hbody : lookupBr brs c = br at hbr'
  generalize hei : els.isSome = eb at hbr'
  cases hbr' with
  | dead hd | refuted hd => rw [Ctx.branch_ghost, hbranch] at hd; exact absurd hd hun.2
  | covered =>
    obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hei
    refine ⟨[], e, by simp [selectBr, hbody], _, hel e rfl, ?_, by simpa using hb, ?_, hRs, .inr rfl,
      fun _ _ => rfl, fun _ _ k hk => absurd hk (Nat.not_lt_zero _)⟩
    · rw [List.append_nil]; exact hE.congr _ rfl rfl rfl rfl rfl
    · rw [List.append_nil]; exact hm
  | live hlive hcb =>
    rename_i Γf' body σ'
    rw [Ctx.branch_ghost, hbranch] at hlive; simp only [Prod.mk.injEq] at hlive
    obtain ⟨rfl, hu⟩ := hlive
    have hsσ := hun.1 σ' hu
    have hwσ := unify_wf Γf.n Γf.σ [] _ σ' (fun e t he => hEf.wf.σ e t he) hu
    obtain ⟨-, o1, o2⟩ := Ctx.openTele_er (sig.len - 1) Γ sig hst
    rw [hpr] at o1 o2
    refine ⟨vs.toList, body, by simp [selectBr, hbody], _, hcb, ?_, ?_, ?_, ?_, .inl rfl, o1,
      fun sig' hsig' k hk => ?_⟩
    rotate_left 4
    · rw [hctor] at hsig'; cases hsig'
      exact o2 k (by omega) (by rw [Tm.len_ers _ hst]; omega)
    · exact (hEf.modify (Γ' := { Γf with σ := σ' }) rfl hsσ hEf.chrono
        ⟨hEf.wf.tys, hwσ, hEf.wf.mints, hEf.wf.cur, hEf.wf.subs⟩).congr _ rfl rfl rfl rfl rfl
    · refine LvlBound.append.mpr ⟨hb, fun v hv' x hx => ?_⟩
      have := hb.subst hss x; rw [hsv] at this
      exact this (by simp only [Tm.levels]; exact Tm.levels_toList vs v hv' x hx)
    · exact hm.append hw hl h6.cur h6.subs
    · exact Tm.static_mono (by simp only [Ctx.n] at h5 ⊢; omega) _ (Nat.le_refl 0) hRs

theorem no_value_of_empty {v : Tm} {d : Nat} {D : Adt} {args : Tm} (hD : P.adts[d]? = some D)
    (hempty : D.ctors = []) : ¬ VTy P v (.app (.tyc d) args) := by
  intro h
  obtain ⟨c, vs, sig, mk, me, _, hc, _⟩ := h.ty_inv
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

theorem Reals.ofList_subst {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) {ts tele : Tm} (hl : ts.isList)
    (h : rtArgs P Γ ts tele = true) :
    Reals P (.ofList (ts.toList.map (·.subst (Tm.env ρS)))) (.ofList (ts.toList.map (·.subst (Tm.env ρ)))) tele := by
  rw [← Tm.toList_subst _ _ hl, ← Tm.toList_subst _ _ hl, Tm.ofList_toList _ (Tm.isList_subst _ _ hl),
    Tm.ofList_toList _ (Tm.isList_subst _ _ hl)]
  exact rtArgs_reals hE hS ts tele h

theorem Reals.list {a b t : Tm} (h : Reals P a b t) : ∀ k x y, a.toList[k]? = some x → b.toList[k]? = some y →
    t.ers.getD k true = false → Real P x y := h.get

theorem eval_sound (hP : ProgOK P) : ∀ μ ρ cnt c, ∀ b Γ rets, CoreTy P b Γ c rets → EnvOK P ρ Γ →
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
      exact ⟨_, .ret, Reals.ofList_subst hE hS hl hok⟩
  | case2 μ ρ cnt f dec args er ms rest env n1 gid G F hcal argv μ' hmu outs cnt1 hev ihb ihr =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | @call _ _ _ _ np t _ outsT _ _ _ _ _ _ hf hF ht ha hn hd ho hok hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb, hgb, he1, he2, he3, hrbt⟩,
      hot, hos⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    obtain ⟨⟨vs, c', e, hvs, hbv, hle, hlc⟩, hsb⟩ := ihb gid Γb rb hcb hEb hbb hmb hrbs
    rw [hev] at e; cases e
    rw [hrb] at hvs
    have hol : outs.length = outsT.len := by
      have := hvs.len (Tm.isTele_subst _ _ hot)
      rw [Tm.len_subst _ _ (.inl hot), ← Tm.len_toList _ hvs.isList, Tm.toList_ofList] at this; simpa [Tm.len] using this
    obtain ⟨hE', hcur, hsubs, hnle⟩ := hE.pushTele (some (ms.map (er || ·))) hot hos hvs hlc
    have hl := hE.len
    rw [eval]; simp only [hcal]; rw [dif_pos hmu]; simp only [argv, μ'] at hev; simp only [hev]
    have ihr' := ihr b _ rets hr hE' (LvlBound.append.mpr ⟨hb.mono hle, hbv⟩)
      (hm.append hE.wf hl hcur hsubs) (Tm.static_mono hnle _ (Nat.le_refl 0) hrs)
    refine ⟨Result.weaken ihr'.1 (hl ▸ hrs) hle, fun hg ρS hS vs' cnt' hr' => ?_⟩
    have hg' : (Γ.pushTele outsT (some (ms.map (er || ·)))).ghost = false := by
      rw [(Ctx.pushTele_er Γ outsT _ hot).1, hg]
    cases er with
    | true =>
      obtain ⟨vsS, hrun, hre⟩ := ihr'.2 hg' _ (hS.pushTele (outsS := List.replicate ms.length .tok) hl hot _ hol
        (by simp [← ho, hol]) (fun k a b _ hb he => by
          simp only [Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map] at he
          cases h : ms[k]? <;> simp [h] at he)) vs' cnt' hr'
      exact ⟨vsS, .callE hrun, hre⟩
    | false =>
      simp only [Ctx.ok, hg, Bool.false_or, Bool.and_eq_true] at hok
      obtain ⟨⟨hrf, hra⟩, hcm⟩ := hok
      obtain ⟨e₀, j, hfv, rfl, hG, hFj⟩ := callee_some hcal
      have hR := rt_real hE hS f hrf; rw [hfv] at hR
      obtain ⟨envS, env₀, G', F', hfS, rfl, hG', hgG, hF', hfe, hSc⟩ := hR.clo_inv
      rw [hG] at hG'; cases hG'; rw [hFj] at hF'; cases hF'
      rw [Tm.toList_ofList] at *
      have hlc := hSc.1
      have hclo : ∀ k a b, (closures envS gid G)[k]? = some a → (closures env₀ gid G)[k]? = some b →
          Γb.er (env₀.length + k) = false → Real P a b := by
        intro k a b ha hb he
        obtain ⟨hk, rfl⟩ := closures_get ha
        obtain ⟨-, rfl⟩ := closures_get hb
        obtain ⟨Fk, hFk⟩ : ∃ Fk, G.fns[k]? = some Fk := ⟨_, List.getElem?_eq_getElem hk⟩
        rw [he2 k Fk hFk] at he
        exact .clo hG hgG hFk he hlc hSc.2
      have hS1 := hSc.extend (er' := Γb.er) (by simp [closures]) (fun i hi => he1 i hi) hclo
      have hS2 := hS1.extend (er' := Γb.er) (vsS := args.toList.map (·.subst (Tm.env ρS)))
        (vs := args.toList.map (·.subst (Tm.env ρ))) (by simp) (fun _ _ => rfl) fun k a b ha' hb he => by
          have hk : k < np := by
            have := (List.getElem?_eq_some_iff.mp hb).1
            rw [List.length_map, Tm.len_toList _ ha.isList] at this; omega
          simp only [List.length_append, closures, List.length_map, List.length_range] at he
          rw [he3 k hk] at he
          rw [← Tm.toList_subst _ _ ha.isList] at ha' hb
          exact (rtArgs_reals hE hS args t hra).get k a b ha' hb he
      have hgb' : Γb.ghost = false := by rw [hgb, hgG, hfe]; rfl
      obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb' _ hS2 outs cnt1 hev
      have hrbe : rb.ers = outsT.ers := by
        rw [← Tm.ers_subst _ _ hrbt, hrb, Tm.ers_subst _ _ hot]
      obtain ⟨vsS, hrun, hre⟩ := ihr'.2 hg' _ (hS.pushTele (outsS := outsS) hl hot _ hol (by
          simpa [Tm.toList_ofList] using hreb.len)
        (fun k a b ha hb he => by
          simp only [Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map] at he
          have hk : k < outsT.len := hol ▸ (List.getElem?_eq_some_iff.mp hb).1
          have hmk : ms.getD k true = false := by
            simp only [List.getD_eq_getElem?_getD]; cases h : ms[k]? <;> simp_all
          have := compat_get ms outsT k hcm (by rw [Tm.len_ers _ hot]; exact hk) hmk
          rw [← hrbe] at this
          exact hreb.get k a b (by simpa [Tm.toList_ofList] using ha) (by simpa [Tm.toList_ofList] using hb) this))
        vs' cnt' hr'
      exact ⟨vsS, .call hfS hG hFj (by simpa [Tm.toList_ofList] using hrunb) hrun, hre⟩
  | case3 μ ρ cnt f dec args er ms rest env n1 gid G F hcal argv μ' hmu e hev ihb =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb⟩, hot, hos⟩ :=
      call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    obtain ⟨⟨vs, c', e', _⟩, _⟩ := ihb gid Γb rb hcb hEb hbb hmb hrbs
    rw [hev] at e'; cases e'
  | case4 μ ρ cnt f dec args er ms rest env n1 gid G F hcal argv μ' hmu =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', hmu', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    exact absurd hmu' hmu
  | case5 μ ρ cnt f dec args er ms rest hcal =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho _ hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
  | case6 μ ρ cnt s R brs els er rest d c vs hs pre body hb outs cnt1 hev ihb ihr =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt hok hbr hel hr =>
    obtain ⟨c', vs', hsv, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', hg', he1, he2⟩ :=
      match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    obtain ⟨⟨outs', c', e, hvs, hbv, hle, hlc⟩, hsb⟩ := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    rw [hev] at e; cases e
    have hl := hE.len
    rw [Tm.subst_append (hl ▸ hRs)] at hvs
    have hol : outs.length = R.len := by
      have := hvs.len (Tm.isTele_subst _ _ hRt)
      rw [Tm.len_subst _ _ (.inl hRt), ← Tm.len_toList _ hvs.isList, Tm.toList_ofList] at this; simpa [Tm.len] using this
    have hov := (if er then some (List.replicate R.len true) else none : Option (List Bool))
    obtain ⟨hE'', hcur, hsubs, hnle⟩ := hE.pushTele (if er then some (List.replicate R.len true) else none) hRt hRs hvs hlc
    rw [eval]; simp only [hs]
    split
    · rename_i pre'' body'' hb''
      rw [hb] at hb''; cases hb''
      simp only [hev]
      have ihr' := ihr bnd _ rets hr hE'' (LvlBound.append.mpr ⟨hlb.mono hle, hbv⟩)
        (hm.append hE.wf hl hcur hsubs) (Tm.static_mono hnle _ (Nat.le_refl 0) hrs)
      refine ⟨Result.weaken ihr'.1 (hl ▸ hrs) hle, fun hg ρS hS vs'' cnt' hr' => ?_⟩
      have hg'' : (Γ.pushTele R (if er then some (List.replicate R.len true) else none)).ghost = false := by
        rw [(Ctx.pushTele_er Γ R _ hRt).1, hg]
      cases er with
      | true =>
        obtain ⟨vsS, hrun, hre⟩ := ihr'.2 hg'' _ (hS.pushTele (outsS := List.replicate R.len .tok) hl hRt _ hol
          (by simp [hol])
          (fun k a b ha _ he => by
            simp only [if_true, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_replicate] at he
            split at he <;> simp at he)) vs'' cnt' hr'
        exact ⟨vsS, .mtchE hrun, hre⟩
      | false =>
        simp only [Ctx.ok, hg, Bool.false_or] at hok
        have hR := rt_real hE hS s hok; rw [hs] at hR
        obtain ⟨vsS, sig, hsS, hsig, hph, hrv⟩ := hR.con_inv
        have hgb : Γ'.ghost = false := by rcases hg' with h | h <;> rw [h, hg] <;> simp [hph]
        have hSb : ∃ preS, selectBr brs els c vsS.toList = some (preS, body) ∧
            SimEnv P Γ'.er (ρS ++ preS) (ρ ++ pre) := by
          rcases selectBr_same (vs' := vsS.toList) hb with ⟨rfl, hsel⟩ | ⟨rfl, hsel⟩
          · refine ⟨_, hsel, hS.extend hrv.len (fun i hi => he1 i (hl ▸ hi)) fun k a b ha hb he => ?_⟩
            rw [hl, he2 sig hsig k (List.getElem?_eq_some_iff.mp hb).1] at he
            exact hrv.get k a b ha hb he
          · exact ⟨_, hsel, hS.extend rfl (fun i hi => he1 i (hl ▸ hi)) fun k _ _ h => by simp at h⟩
        obtain ⟨preS, hsel, hSb⟩ := hSb
        obtain ⟨outsS, hrunb, hreb⟩ := hsb hgb _ hSb outs cnt1 hev
        obtain ⟨vsS', hrun, hre⟩ := ihr'.2 hg'' _ (hS.pushTele (outsS := outsS) hl hRt _ hol (by
            simpa [Tm.toList_ofList] using hreb.len)
          (fun k a b ha hb he => hreb.get k a b (by simpa [Tm.toList_ofList] using ha)
            (by simpa [Tm.toList_ofList] using hb) (by simpa using he))) vs'' cnt' hr'
        exact ⟨vsS', .mtch hsS hsel hrunb hrun, hre⟩
    · rename_i hno; rw [hb] at hno; cases hno
  | case7 μ ρ cnt s R brs els er rest d c vs hs pre body hb e hev ihb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨c', vs', hsv, pre', body', hb', Γ', hcb, hE', hlb', hm', hRs', _⟩ :=
      match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    obtain ⟨⟨_, _, e', _⟩, _⟩ := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    rw [hev] at e'; cases e'
  | case8 μ ρ cnt s R brs els er rest d c vs hs hb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨c', vs', hsv, pre', body', hb', _⟩ := match_setup hP hE hlb hm hst hS hD hbr hel hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
  | case9 μ ρ cnt s R brs els er rest hs =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt _ hbr hel hr =>
    obtain ⟨c', vs', hsv, _⟩ := match_setup hP hE hlb hm hst hS hD hbr hel hRs
    exact (hs _ _ _ hsv).elim
  | case10 μ ρ cnt p er rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | @prim _ _ T _ _ _ _ hp hok hr =>
    obtain ⟨hv, hT, hlc, hlv⟩ := prim_sound hP hE hb hp
    obtain ⟨hE', hcur, hsubs, hn⟩ := hE.pushPrim hP hp hv hT hlc rfl
    rw [eval]
    have hl := hE.len
    have ih' := ih b _ rets hr hE' (LvlBound.append.mpr ⟨hb, by simpa [LvlBound] using hlv⟩)
      (hm.append hE.wf hl hcur hsubs) (Tm.static_mono (by omega) _ (Nat.le_refl 0) hrs)
    refine ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_refl _), fun hg ρS hS vs cnt' hr' => ?_⟩
    have her : ∀ i, (Γ.pushPrim T er p).er i = if i = Γ.n then er else Γ.er i := by intro i; cases p <;> rfl
    have hg' : (Γ.pushPrim T er p).ghost = false := by rw [← hg]; cases p <;> rfl
    obtain ⟨vsS, hrun, hre⟩ := ih'.2 hg' _ (hS.extend (vsS := [if er then .tok else p.eval ρS]) rfl
      (fun i hi => by rw [her, if_neg (by omega)]) fun k a b ha hb he => by
        cases k with
        | succ => simp at ha
        | zero =>
          simp at ha hb; subst ha hb
          rw [her, if_pos (by omega)] at he; subst he
          simp only [Ctx.ok, hg, Bool.false_or] at hok
          cases p with
          | tm t => exact rt_real hE hS t hok
          | _ => exact .other (by simp [Prim.eval]) (by simp [Prim.eval]) (by simp [Prim.eval])) vs cnt' hr'
    exact ⟨vsS, .prim hrun, hre⟩
  | case11 μ ρ cnt rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defLvl hr =>
    rw [eval]
    have hl := hE.len
    have ih' := ih b _ rets hr (hE.pushMint hb) (LvlBound.append.mpr ⟨hb.mono (Nat.le_succ _), by simp [LvlBound, Tm.levels]⟩)
      (hm.append hE.wf hl rfl rfl) (Tm.static_mono (by simp [Ctx.pushMint, Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hrs)
    refine ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_succ _), fun hg ρS hS vs cnt' hr' => ?_⟩
    obtain ⟨vsS, hrun, hre⟩ := ih'.2 hg _ (hS.extend (vsS := [.tok]) rfl
      (fun i hi => by simp [Ctx.pushMint, Ctx.push]; omega)
      fun k a b ha hb _ => by
        cases k with
        | succ => simp at ha
        | zero => simp at ha hb; subst ha hb; exact .other (by simp) (by simp) (by simp)) vs cnt' hr'
    exact ⟨vsS, .defLvl hrun, hre⟩
  | case12 μ ρ cnt gid rest G hG ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defFns _ hG' hok hr =>
    rw [hG] at hG'; cases hG'
    rw [eval, hG]
    have hl := hE.len
    have ih' := ih b _ rets hr (hE.pushFns hP hG hok) (LvlBound.append.mpr ⟨hb, fun v hv x hx => by
        simp only [closures, List.mem_map] at hv
        obtain ⟨j, _, rfl⟩ := hv
        obtain ⟨w, hw, hx'⟩ := Tm.levels_ofList ρ x (by simpa [Tm.levels] using hx)
        exact hb w hw x hx'⟩)
      (hm.append hE.wf hl rfl rfl) (Tm.static_mono (by simp [Ctx.pushFns, Ctx.n]) _ (Nat.le_refl 0) hrs)
    refine ⟨Result.weaken ih'.1 (hl ▸ hrs) (Nat.le_refl _), fun hg ρS hS vs cnt' hr' => ?_⟩
    cases hok with
    | mk _ _ _ _ _ hGe hGg =>
    obtain ⟨vsS, hrun, hre⟩ := ih'.2 hg _ (hS.extend (vsS := closures ρS gid G) (by simp [closures])
      (fun i hi => by simp only [Ctx.pushFns]; rw [if_neg (by omega)])
      fun k a b ha hb he => by
        obtain ⟨hk, rfl⟩ := closures_get ha
        obtain ⟨-, rfl⟩ := closures_get hb
        obtain ⟨Fk, hFk⟩ : ∃ Fk, G.fns[k]? = some Fk := ⟨_, List.getElem?_eq_getElem hk⟩
        simp only [Ctx.pushFns] at he
        rw [if_pos (by omega), show ρ.length + k - Γ.n = k by omega, hFk] at he
        refine .clo hG (by rw [← hGg, hg]) hFk (by simpa using he) hS.1 fun i hi => ?_
        by_cases hin : i < Γ.n
        · rw [← hGe i hin] at hi; exact hS.2 i hi
        · have : Tm.env ρ i = .nil := by
            simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ρ.length ≤ i by omega)]
          rw [this]; exact Real.nil' _) vs cnt' hr'
    exact ⟨vsS, .defFns hG hrun, hre⟩
  | case13 μ ρ cnt gid rest hG =>
    intro b Γ rets hc
    cases hc with
    | defFns _ hG' => rw [hG] at hG'; cases hG'
  | case14 μ ρ cnt k a e rest ih =>
    intro b Γ rets hc hE hb hm hrs
    rw [eval]
    have : CoreTy P b Γ rest rets := by cases hc <;> assumption
    have ih' := ih b Γ rets this hE hb hm hrs
    refine ⟨ih'.1, fun hg ρS hS vs cnt' hr' => ?_⟩
    obtain ⟨vsS, hrun, hre⟩ := ih'.2 hg ρS hS vs cnt' hr'
    exact ⟨vsS, .chk hrun, hre⟩
  | case15 μ ρ cnt body a hev ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | absurd hcb hst hD hemp =>
    obtain ⟨⟨vs, c', e, hv, -⟩, -⟩ := ih b _ _ hcb (hE.congr _ rfl rfl rfl rfl rfl) hb hm
      (by simpa [Tm.static, Ctx.n] using hst)
    exfalso
    generalize Tm.ofList vs = w at hv
    simp only [Tm.subst] at hv
    cases hv with
    | cons hv _ => exact no_value_of_empty hD hemp hv
  | case16 μ ρ cnt body e hev ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | absurd hcb hst hD hemp =>
    obtain ⟨⟨vs, c', e', -⟩, -⟩ := ih b _ _ hcb (hE.congr _ rfl rfl rfl rfl rfl) hb hm
      (by simpa [Tm.static, Ctx.n] using hst)
    rw [hev] at e'; cases e'
  | case17 μ ρ cnt =>
    intro b Γ rets hc
    cases hc

theorem checked_runs {rets : Tm} (h : Checked P rets) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) rets .nil ∧
      ∃ vsS, RunS P [] P.main vsS ∧ Reals P (.ofList vsS) (.ofList vs) rets := by
  obtain ⟨hP, hc, hs⟩ := h
  have hE : EnvOK P [] {tys := []} :=
    .mk rfl (fun _ _ _ h _ => by simp at h) (by simp) (fun _ _ h => by simp at h) (by simp)
      ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, by simp, by simp, by simp⟩
  obtain ⟨⟨vs, cnt, e, hv, _⟩, hsim⟩ :=
    eval_sound hP none [] 0 P.main _ _ rets hc hE (by simp [LvlBound]) (by simp [MuOK]) (by simpa [Ctx.n] using hs)
  exact ⟨vs, cnt, e, by rwa [Tm.subst_static0 _ _ 0 hs] at hv,
    hsim rfl [] ⟨rfl, fun _ _ => by simpa [Tm.env] using Real.nil' (P := P) .nil⟩ vs cnt e⟩

theorem no_false {d : Nat} {D : Adt} {args : Tm} {m e : Bool} (hD : P.adts[d]? = some D) (hempty : D.ctors = []) :
    ¬ Checked P (.bind (.ty m e) (.app (.tyc d) args) .nil) := by
  intro h
  obtain ⟨vs, _, _, hv, _⟩ := checked_runs h
  generalize Tm.ofList vs = w at hv
  cases hv with
  | cons hv _ => exact no_value_of_empty hD hempty hv

theorem check_sound {R : Tm} {h : Checked P R} (_ : checkProg P = .ok ⟨R, h⟩) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) R .nil ∧
      ∃ vsS, RunS P [] P.main vsS ∧ Reals P (.ofList vsS) (.ofList vs) R :=
  checked_runs h

end Minimal
