import Minimal.UnifySound
import Minimal.Check
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
  | lvl : VTy (.lvl n) .level
  | predates : (∀ n ∈ x.levels, n < m) → VTy .tok (.predates A x (.lvl m))
  | subterm : Tm.PSub a b → VTy .tok (.subterm A a B b)
  | con : P.ctor d c = some sig → VTys vs sig (.bind mk T .nil) → T = .ty d idx → VTy (.con d c vs) T
  | clo : EnvOK env Γ → P.groups[gid]? = some G → GroupOK P gid Γ G → G.fns[j]? = some F →
      VTy (.clo (.ofList env) gid j) ((F.type G).subst (Tm.env env))

inductive VTys : Tm → Tm → Tm → Prop
  | nil : VTys .nil t t
  | cons : VTy v A → VTys vs (r.inst v 0) out → VTys (.cons v vs) (.bind m A r) out

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

theorem retOf_inst (u : Tm) : ∀ (t : Tm) k d idx, retOf t = some (.ty d idx) →
    ∃ idx', retOf (t.inst u k) = some (.ty d idx') := by
  intro t; induction t with
  | bind m A r _ ihr =>
    intro k d idx h
    cases r with
    | nil => simp [retOf] at h; subst h; simp [Tm.inst, retOf]
    | bind m' A' r' =>
      simp only [retOf] at h
      obtain ⟨idx', h'⟩ := ihr (k + 1) d idx h
      exact ⟨idx', by simpa [Tm.inst, retOf] using h'⟩
    | _ => simp [retOf] at h
  | _ => intro k d idx h; simp [retOf] at h

theorem VTys.nil_out' {vs out : Tm} : VTys P vs .nil out → out = .nil := by
  intro h; cases h; rfl

theorem VTys.retOf {vs tele out : Tm} :
    VTys P vs tele out → ∀ d idx, retOf tele = some (.ty d idx) → out ≠ .nil → ∃ idx', retOf out = some (.ty d idx')
  | .nil, d, idx, h, _ => ⟨idx, h⟩
  | .cons (r := r) _ hr, d, idx, h, hn => by
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

mutual
theorem tm_sound (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) : ∀ {t T : Tm}, TmTy P Γ t T →
    VTy P (t.subst (Tm.env ρ)) (T.subst (Tm.env ρ)) ∧ t.static Γ.n 0 ∧ T.static Γ.n 0
  | _, _, .fv h => by
    obtain ⟨v, _, he, hv⟩ := hE.get h
    refine ⟨by simpa [Tm.subst, he] using hv, ?_, hE.wf.tys _ _ h⟩
    exact decide_eq_true (List.getElem?_eq_some_iff.mp h).1
  | _, _, .univ => ⟨.univ, rfl, rfl⟩
  | _, _, .level => ⟨.univ, rfl, rfl⟩
  | _, _, .ty hD ha => by
    have := args_sound hP hE ha (Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) (hP.params _ _ hD).2)
    exact ⟨.univ, by simpa [Tm.static] using this.2.1, rfl⟩
  | _, _, .con (d := d) hc ha => by
    obtain ⟨D, hD, hsig⟩ : ∃ D, P.adts[d]? = some D ∧ _ := Option.bind_eq_some_iff.mp hc
    obtain ⟨_, hs0, idx, hr⟩ := hP.ctors _ _ _ _ hD hsig
    have := args_sound hP hE ha (Tm.static_mono (Nat.zero_le _) _ (Nat.le_refl 0) hs0)
    rw [Tm.subst_static0 _ _ 0 hs0] at this
    obtain ⟨hv, hargs, hout⟩ := this
    simp only [Tm.subst] at hv
    obtain ⟨idx', hidx⟩ := VTys.retOf hv d idx hr (by simp)
    simp [retOf] at hidx
    refine ⟨.con hc hv hidx, by simpa [Tm.static] using hargs, ?_⟩
    simpa [Tm.static] using hout
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

theorem EnvOK.push {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {v A : Tm} (hv : VTy P v (A.subst (Tm.env ρ)))
    (hA : A.static Γ.n 0) (hc : v.lc 0) : EnvOK P (ρ ++ [v]) (Γ.push A) :=
  hE.pushMany [v] [A] rfl fun j v' T h1 h2 => by
    cases j with
    | zero => simp at h1 h2; subst h1 h2; exact ⟨hv, hA, hc⟩
    | succ => simp at h1

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

def LvlBound (ρ : List Tm) (cnt : Nat) : Prop := ∀ v ∈ ρ, ∀ n ∈ v.levels, n < cnt

theorem EnvOK.pushMint {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt) :
    EnvOK P (ρ ++ [.lvl cnt]) Γ.pushMint := by
  have h1 := hE.push (v := .lvl cnt) (A := .level) .lvl rfl trivial
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

theorem EnvOK.openTele {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) :
    ∀ {tele vs out : Tm}, tele.isTele → tele.static Γ.n 0 → VTys P vs (tele.subst (Tm.env ρ)) out →
    (∀ v ∈ vs.toList, v.lc 0) →
    EnvOK P (ρ ++ vs.toList) (Γ.openTele tele vs.len).1 ∧
    (Γ.openTele tele vs.len).2.subst (Tm.env (ρ ++ vs.toList)) = out ∧
    (Γ.openTele tele vs.len).2.static (Γ.openTele tele vs.len).1.n 0 ∧
    (Γ.openTele tele vs.len).2.isTele ∧
    (Γ.openTele tele vs.len).1.n = Γ.n + vs.len ∧
    ∃ Ts, (Γ.openTele tele vs.len).1 = { Γ with tys := Γ.tys ++ Ts } := by
  intro tele vs
  induction vs generalizing ρ Γ tele with
  | cons v vs' _ ih =>
    intro out ht hs hv hc
    cases tele with
    | bind m A r =>
      simp only [Tm.subst] at hv
      cases hv with
      | cons hvA hvs =>
      simp only [Tm.isTele, Tm.static, Bool.and_eq_true] at ht hs
      have hl := hE.len
      have hc1 : v.lc 0 := hc v (by simp [Tm.toList])
      have hE' := hE.push hvA hs.1 hc1
      have hs' : (r.inst (.fv Γ.n) 0).static (Γ.push A).n 0 :=
        Tm.static_inst (by simp [Tm.static, Ctx.push, Ctx.n]) r 0
          (Tm.static_mono (by simp [Ctx.push, Ctx.n]) r (Nat.le_refl _) hs.2)
      have hr : (r.inst (.fv Γ.n) 0).subst (Tm.env (ρ ++ [v])) = (r.subst (Tm.env ρ)).inst v 0 := by
        rw [Tm.subst_inst _ (Tm.env_lc hE'.closed), Tm.subst_append (hl ▸ hs.2)]
        congr 1; simp [Tm.subst, Tm.env, hl.symm]
      have := ih hE' (Tm.isTele_inst _ r 0 ht) hs' (hr ▸ hvs) (fun w hw => hc w (by simp [Tm.toList, hw]))
      simp only [Tm.len, Ctx.openTele, Tm.toList, List.append_assoc, List.singleton_append] at this ⊢
      obtain ⟨h1, h2, h3, h4, h5, Ts, h6⟩ := this
      refine ⟨h1, h2, h3, h4, by rw [h5]; simp [Ctx.push, Ctx.n]; omega, A :: Ts, ?_⟩
      rw [h6]; simp [Ctx.push]
    | nil => simp [Tm.subst] at hv; cases hv
    | _ => simp [Tm.isTele] at ht
  | nil =>
    intro out ht hs hv hc
    cases hv
    have h0 : Γ.openTele tele 0 = (Γ, tele) := by cases tele <;> simp [Ctx.openTele]
    simp only [Tm.len, h0, Tm.toList, List.append_nil]
    exact ⟨hE, trivial, hs, ht, by simp, [], by simp⟩
  | _ => intro out ht hs hv hc; cases hv

theorem VTy.fn_inv {v l t : Tm} {np : Nat} (h : VTy P v (.fn l np t)) :
    ∃ env Γ gid G j F, v = .clo (.ofList env) gid j ∧ EnvOK P env Γ ∧ P.groups[gid]? = some G ∧
      GroupOK P gid Γ G ∧ G.fns[j]? = some F ∧ (F.type G).subst (Tm.env env) = .fn l np t := by
  cases h with
  | clo hE hG hok hF => exact ⟨_, _, _, _, _, _, rfl, hE, hG, hok, hF, rfl⟩
  | con _ _ he => cases he

theorem VTy.ty_inv {v idx : Tm} {d : Nat} (h : VTy P v (.ty d idx)) :
    ∃ c vs sig mk, v = .con d c vs ∧ P.ctor d c = some sig ∧ VTys P vs sig (.bind mk (.ty d idx) .nil) := by
  cases h with
  | con hc hv he => cases he; exact ⟨_, _, _, _, rfl, hc, hv⟩

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
  | mk hK hl hty _ _ =>
  refine hE.pushMany _ _ (by simp [closures]) fun j v T h1 h2 => ?_
  obtain ⟨hj, rfl⟩ := closures_get h1
  simp only [List.getElem?_map] at h2
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp h2
  exact ⟨.clo hE hG (.mk hK hl hty ‹_› ‹_›) hF, (tm_sound hP hE (hty j F hF)).2.1, trivial⟩

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

theorem tele_one {f : Nat → Tm} {m : Bool} {A : Tm} : ∀ {t : Tm}, t.isTele → t.subst f = .bind m A .nil →
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
      cases m <;> simp <;> omega
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

theorem ArgsTy.isList {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → args.isList
  | .nil => rfl
  | .cons _ _ h => by simp only [Tm.isList]; exact h.isList

theorem ArgsTy.isTele {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → out.isTele
  | .nil, h => h
  | .cons _ _ hr, h => hr.isTele (Tm.isTele_inst _ _ 0 (by simpa [Tm.isTele] using h))

theorem ArgsTy.len {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele → args.len + out.len = tele.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ _ hr, h => by
    simp only [Tm.isTele] at h
    have := hr.len (Tm.isTele_inst _ _ 0 h)
    rw [Tm.len_inst _ _ _ h] at this
    simp [Tm.len]; omega

theorem VTys.len {vs tele out : Tm} : VTys P vs tele out → tele.isTele → vs.len + out.len = tele.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    have := hr.len (Tm.isTele_inst _ _ 0 h)
    rw [Tm.len_inst _ _ _ h] at this
    simp [Tm.len]; omega

theorem VTys.isList {vs tele out : Tm} : VTys P vs tele out → vs.isList
  | .nil => rfl
  | .cons _ hr => by simp only [Tm.isList]; exact hr.isList

theorem canon_static {Γ : Ctx} (hw : Γ.WF) {t : Tm} {d : Nat} (h : t.static Γ.n d) : (Γ.canon t).static Γ.n d :=
  Tm.static_subst t d h fun i hi => by
    cases e : Γ.σ i with
    | none => simp [Tm.static]; exact Tm.fvs_static t d h i hi
    | some u => simpa using (hw.σ i u e).2

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
    (ht : tele.isTele) (hs : tele.static Γ.n 0) (hv : VTys P (.ofList outs) (tele.subst (Tm.env ρ)) .nil)
    (hc : ∀ v ∈ outs, v.lc 0) :
    EnvOK P (ρ ++ outs) (Γ.pushTele tele) ∧ (Γ.pushTele tele).cur = Γ.cur ∧ (Γ.pushTele tele).subs = Γ.subs ∧
      Γ.n ≤ (Γ.pushTele tele).n := by
  have hl := hv.len (Tm.isTele_subst _ _ ht)
  rw [Tm.len_subst _ _ (.inl ht)] at hl; simp [Tm.len] at hl
  have := hE.openTele ht hs hv (by simpa [Tm.toList_ofList] using hc)
  rw [Tm.toList_ofList, hl] at this
  obtain ⟨h1, _, _, _, h5, Ts, h6⟩ := this
  refine ⟨h1, ?_, ?_, ?_⟩ <;> simp only [Ctx.pushTele, h6] <;> simp [Ctx.n]

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
    (hp : PrimTy P Γ p T) (hv : VTy P v (T.subst (Tm.env ρ))) (hT : T.static Γ.n 0) (hc : v.lc 0)
    (he : v = p.eval ρ) :
    EnvOK P (ρ ++ [v]) (Γ.pushPrim T p) ∧ (Γ.pushPrim T p).cur = Γ.cur ∧ (Γ.pushPrim T p).subs = Γ.subs ∧
      (Γ.pushPrim T p).n = Γ.n + 1 := by
  have h1 := hE.push hv hT hc
  refine ⟨?_, by cases p <;> rfl, by cases p <;> rfl, by cases p <;> simp [Ctx.pushPrim, Ctx.withRule, Ctx.push, Ctx.n]⟩
  cases hp with
  | tm ht =>
    have hl := hE.len
    have hs := canon_static hE.wf (tm_sound hP hE ht).2.1
    refine h1.withRule (by simp [Ctx.push, Ctx.n]) (Tm.static_mono (by simp [Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hs) ?_
    rw [Tm.subst_append (hl ▸ hs), hE.canon, he]
    simp [Tm.env, hl, Prim.eval]
  | _ => exact h1

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
  | same hc hl' hmi hai hsi hpre hp hP' h0 h1 =>
    rename_i c pos i a s p Pt A a0 B b0
    rw [hc] at hm; obtain ⟨lam, hlam, rfl⟩ := hm
    rw [eqc hl'] at hl; simp [Tm.subst, Tm.env, hlam] at hl; subst hl
    have v := sem hp; rw [hP'] at v; simp only [Tm.subst] at v
    have hps := v.subterm_inv
    rw [eqc h0, eqc h1] at hps
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

theorem fv_filterMap_env (ρ : List Tm) (g : Tm → Nat) : ∀ (L : List Tm), (∀ x ∈ L, ∃ i, x = .fv i) →
    (L.filterMap Tm.fvIdx).map (fun s => g (Tm.env ρ s)) = (L.map (Tm.subst (Tm.env ρ))).map g
  | [], _ => rfl
  | x :: L, h => by
    obtain ⟨i, rfl⟩ := h x (by simp)
    simp [Tm.subst, Tm.fvIdx, fv_filterMap_env ρ g L fun y hy => h y (by simp [hy])]

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
        rb.subst (Tm.env (env ++ closures env gid G ++ args.toList.map (·.subst (Tm.env ρ)))) = outsT.subst (Tm.env ρ)) ∧
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
  | mk hK hKl htyF hmk hbody =>
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
    obtain ⟨h1, h2, h3, h4, h5, Ts, h6⟩ := hE1.openTele hFtele hFt1 hvF hlc
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
    refine ⟨(Γc.body G F).1, (Γc.body G F).2, hbody j F hFj, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Ctx.body]
      refine h1.modify rfl h1.sat h1.chrono ⟨h1.wf.tys, h1.wf.σ, h1.wf.mints, fun c hc => ?_, fun s hs => ?_⟩
      · simp at hc; subst hc
        have := (List.getElem?_eq_some_iff.mp hK).1
        simp only [Ctx.n] at this hn1 h5 ⊢; rw [h6] at h5 ⊢; simp at h5 ⊢; omega
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

theorem match_setup (hP : ProgOK P) {ρ : List Tm} {Γ : Ctx} (hE : EnvOK P ρ Γ) {cnt : Nat} (hb : LvlBound ρ cnt)
    {μ : Option (List Nat)} (hm : MuOK μ Γ ρ) {s St idx R : Tm} {d bnd : Nat} {D : Adt}
    {brs : List (Nat × Nat × Core)}
    (hs : TmTy P Γ s St) (hS : Γ.canon St = .ty d idx) (hD : P.adts[d]? = some D)
    (hbr : ∀ (c : Nat) sig, D.ctors[c]? = some sig → BranchOK P bnd Γ s d idx c sig R (lookupBr brs c))
    (hRs : R.static Γ.n 0) :
    ∃ c vs, s.subst (Tm.env ρ) = .con d c vs ∧ ∃ body, lookupBr brs c = some body ∧
      ∃ Γ', CoreTy P bnd Γ' body R ∧ EnvOK P (ρ ++ vs.toList) Γ' ∧ LvlBound (ρ ++ vs.toList) cnt ∧
        MuOK μ Γ' (ρ ++ vs.toList) ∧ R.static Γ'.n 0 := by
  have hw := hE.wf
  have hl := hE.len
  obtain ⟨hv, hss, hSs⟩ := tm_sound hP hE hs
  have hSs' := canon_static hw hSs
  rw [hS] at hSs'; simp only [Tm.static] at hSs'
  rw [← hE.canon St, hS] at hv; simp only [Tm.subst] at hv
  obtain ⟨c, vs, sig, mk, hsv, hctor, hvs⟩ := hv.ty_inv
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
    exact Tm.lc_toList vs 0 this v hv'
  obtain ⟨h1, h2, h3, h4, h5, Ts, h6⟩ := hE.openTele hst hsigs (hsub ▸ hvs) hlc
  have hm' : vs.len = sig.len - 1 := by omega
  rw [hm'] at h1 h2 h3 h4 h5 h6
  generalize hpr : Γ.openTele sig (sig.len - 1) = pr at h1 h2 h3 h4 h5 h6
  obtain ⟨Γf, rem⟩ := pr
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨Rc, rfl, hRc⟩ := Tm.tele_one h4 h2
  have hbranch : Γ.branch s d c idx sig =
      (Γf, unify Γf.n Γf.σ [] [(Γ.canon s, .con d c (Γ.fields (sig.len - 1))), (Γ.canon (.ty d idx), Γf.canon Rc)]) := by
    simp [Ctx.branch, hpr]
  have hEf := h1
  have hvl : vs.toList.length = sig.len - 1 := by rw [Tm.len_toList _ hvs.isList, hm']
  have hsat : Sat (Tm.env (ρ ++ vs.toList)) Γ.σ := by have := hEf.sat; rw [h6] at this; exact this
  have heqs : ∀ p ∈ [(Γ.canon s, Tm.con d c (Γ.fields (sig.len - 1))), (Γ.canon (.ty d idx), Γf.canon Rc)],
      p.1.subst (Tm.env (ρ ++ vs.toList)) = p.2.subst (Tm.env (ρ ++ vs.toList)) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp only
      rw [canon_sound (Γ := Γ) hsat, Tm.subst_append (hl ▸ hss), hsv, ← hvl]
      simp only [Tm.subst]; rw [fields_subst _ hl, Tm.ofList_toList _ hvs.isList]
    · simp only
      rw [canon_sound (Γ := Γ) hsat, canon_sound hEf.sat, hRc,
        Tm.subst_append (t := Tm.ty d idx) (by simpa [Tm.static, hl] using hSs')]
      simp [Tm.subst]
  have hun := unify_sound (Tm.env (ρ ++ vs.toList)) Γf.n Γf.σ [] _ hEf.sat heqs
  refine ⟨c, vs, hsv, ?_⟩
  have hbr' := hbr c sig hsig
  generalize hbody : lookupBr brs c = br at hbr'
  cases hbr' with
  | dead hd => rw [hbranch] at hd; exact absurd hd hun.2
  | live hlive hcb =>
    rename_i Γf' body σ'
    rw [hbranch] at hlive; simp only [Prod.mk.injEq] at hlive
    obtain ⟨rfl, hu⟩ := hlive
    have hsσ := hun.1 σ' hu
    have hwσ := unify_wf Γf.n Γf.σ [] _ σ' (fun e t he => hEf.wf.σ e t he) hu
    refine ⟨body, rfl, { Γf with σ := σ' }, hcb, ?_, ?_, ?_, ?_⟩
    · exact hEf.modify rfl hsσ hEf.chrono ⟨hEf.wf.tys, hwσ, hEf.wf.mints, hEf.wf.cur, hEf.wf.subs⟩
    · refine LvlBound.append.mpr ⟨hb, fun v hv' x hx => ?_⟩
      have := hb.subst hss x; rw [hsv] at this
      exact this (by simp only [Tm.levels]; exact Tm.levels_toList vs v hv' x hx)
    · exact hm.append hw hl (by rw [h6]) (by rw [h6])
    · exact Tm.static_mono (by simp only [Ctx.n] at h5 ⊢; omega) _ (Nat.le_refl 0) hRs

theorem eval_sound (hP : ProgOK P) : ∀ μ ρ cnt c, ∀ b Γ rets, CoreTy P b Γ c rets → EnvOK P ρ Γ →
    LvlBound ρ cnt → MuOK μ Γ ρ → rets.static Γ.n 0 → Result P ρ cnt rets (eval P μ ρ cnt c) := by
  intro μ ρ cnt c
  induction μ, ρ, cnt, c using eval.induct P with
  | case1 μ ρ cnt ts =>
    intro b Γ rets hc hE hb _ hrs
    cases hc with
    | ret ha =>
    obtain ⟨hv, hs, _⟩ := args_sound hP hE ha hrs
    have hl := ha.isList
    refine ⟨_, cnt, by rw [eval], ?_, ?_, Nat.le_refl _, ?_⟩
    · rw [← Tm.toList_subst _ _ hl, Tm.ofList_toList _ (Tm.isList_subst _ _ hl)]; simpa [Tm.subst] using hv
    · intro v hv' x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv'
      exact hb.subst (static_toList hs t ht) x hx
    · intro v hv'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv'
      exact lc_of_static hE.closed (static_toList hs t ht)
  | case2 μ ρ cnt f dec args n rest env n1 gid G F hcal argv μ' hmu outs cnt1 hev ihb ihr =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb⟩, hot, hos⟩ :=
      call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    obtain ⟨vs, c', e, hvs, hbv, hle, hlc⟩ := ihb gid Γb rb hcb hEb hbb hmb hrbs
    rw [hev] at e; cases e
    rw [hrb] at hvs
    obtain ⟨hE', hcur, hsubs, hnle⟩ := hE.pushTele hot hos hvs hlc
    have hl := hE.len
    rw [eval]; simp only [hcal]; rw [dif_pos hmu]; simp only [argv, μ'] at hev; simp only [hev]
    exact Result.weaken (ihr b _ rets hr hE' (LvlBound.append.mpr ⟨hb.mono hle, hbv⟩)
      (hm.append hE.wf hl hcur hsubs) (Tm.static_mono hnle _ (Nat.le_refl 0) hrs)) (hl ▸ hrs) hle
  | case3 μ ρ cnt f dec args n rest env n1 gid G F hcal argv μ' hmu e hev ihb =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _, ⟨Γb, rb, hcb, hEb, hbb, hmb, hrbs, hrb⟩, hot, hos⟩ :=
      call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    obtain ⟨vs, c', e', _⟩ := ihb gid Γb rb hcb hEb hbb hmb hrbs
    rw [hev] at e'; cases e'
  | case4 μ ρ cnt f dec args n rest env n1 gid G F hcal argv μ' hmu =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho hr =>
    obtain ⟨env', n1', gid', G', F', hcal', hmu', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
    exact absurd hmu' hmu
  | case5 μ ρ cnt f dec args n rest hcal =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | call hf hF ht ha hn hd ho hr =>
    obtain ⟨env', n1', gid', G', F', hcal', _⟩ := call_setup hP hE hb hm hf hF ht ha hn hd
    rw [hcal] at hcal'; cases hcal'
  | case6 μ ρ cnt s R brs rest d c vs hs body hb outs cnt1 hev ihb ihr =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt hbr hr =>
    obtain ⟨c', vs', hsv, body', hb', Γ', hcb, hE', hlb', hm', hRs'⟩ := match_setup hP hE hlb hm hst hS hD hbr hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    obtain ⟨outs', c', e, hvs, hbv, hle, hlc⟩ := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    rw [hev] at e; cases e
    have hl := hE.len
    rw [Tm.subst_append (hl ▸ hRs)] at hvs
    obtain ⟨hE'', hcur, hsubs, hnle⟩ := hE.pushTele hRt hRs hvs hlc
    rw [eval]; simp only [hs]
    split
    · rename_i body'' hb''
      rw [hb] at hb''; cases hb''
      simp only [hev]
      exact Result.weaken (ihr bnd _ rets hr hE'' (LvlBound.append.mpr ⟨hlb.mono hle, hbv⟩)
        (hm.append hE.wf hl hcur hsubs) (Tm.static_mono hnle _ (Nat.le_refl 0) hrs)) (hl ▸ hrs) hle
    · rename_i hno; exact absurd hb (hno _)
  | case7 μ ρ cnt s R brs rest d c vs hs body hb e hev ihb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt hbr hr =>
    obtain ⟨c', vs', hsv, body', hb', Γ', hcb, hE', hlb', hm', hRs'⟩ := match_setup hP hE hlb hm hst hS hD hbr hRs
    rw [hs] at hsv; cases hsv
    rw [hb] at hb'; cases hb'
    obtain ⟨_, _, e', _⟩ := ihb bnd Γ' R hcb hE' hlb' hm' hRs'
    rw [hev] at e'; cases e'
  | case8 μ ρ cnt s R brs rest d c vs hs hb =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt hbr hr =>
    obtain ⟨c', vs', hsv, body', hb', _⟩ := match_setup hP hE hlb hm hst hS hD hbr hRs
    rw [hs] at hsv; cases hsv
    exact (hb _ hb').elim
  | case9 μ ρ cnt s R brs rest hs =>
    intro bnd Γ rets hc hE hlb hm hrs
    cases hc with
    | mtch hst hS hD _ _ hRs hRt hbr hr =>
    obtain ⟨c', vs', hsv, _⟩ := match_setup hP hE hlb hm hst hS hD hbr hRs
    exact (hs _ _ _ hsv).elim
  | case10 μ ρ cnt p rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | prim hp hr =>
    obtain ⟨hv, hT, hlc, hlv⟩ := prim_sound hP hE hb hp
    obtain ⟨hE', hcur, hsubs, hn⟩ := hE.pushPrim hP hp hv hT hlc rfl
    rw [eval]
    have hl := hE.len
    refine Result.weaken (ih b _ rets hr hE' ?_ (hm.append hE.wf hl hcur hsubs)
      (Tm.static_mono (by omega) _ (Nat.le_refl 0) hrs)) (hl ▸ hrs) (Nat.le_refl _)
    exact LvlBound.append.mpr ⟨hb, by simpa [LvlBound] using hlv⟩
  | case11 μ ρ cnt rest ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defLvl hr =>
    rw [eval]
    have hl := hE.len
    refine Result.weaken (ih b _ rets hr (hE.pushMint hb) ?_ (hm.append hE.wf hl rfl rfl)
      (Tm.static_mono (by simp [Ctx.pushMint, Ctx.push, Ctx.n]) _ (Nat.le_refl 0) hrs)) (hl ▸ hrs) (Nat.le_succ _)
    exact LvlBound.append.mpr ⟨hb.mono (Nat.le_succ _), by simp [LvlBound, Tm.levels]⟩
  | case12 μ ρ cnt gid rest G hG ih =>
    intro b Γ rets hc hE hb hm hrs
    cases hc with
    | defFns _ hG' hok hr =>
    rw [hG] at hG'; cases hG'
    rw [eval, hG]
    have hl := hE.len
    refine Result.weaken (ih b _ rets hr (hE.pushFns hP hG hok) ?_ (hm.append hE.wf hl rfl rfl)
      (Tm.static_mono (by simp [Ctx.pushFns, Ctx.n]) _ (Nat.le_refl 0) hrs)) (hl ▸ hrs) (Nat.le_refl _)
    refine LvlBound.append.mpr ⟨hb, fun v hv x hx => ?_⟩
    simp only [closures, List.mem_map] at hv
    obtain ⟨j, _, rfl⟩ := hv
    obtain ⟨w, hw, hx'⟩ := Tm.levels_ofList ρ x (by simpa [Tm.levels] using hx)
    exact hb w hw x hx'
  | case13 μ ρ cnt gid rest hG =>
    intro b Γ rets hc
    cases hc with
    | defFns _ hG' => rw [hG] at hG'; cases hG'

theorem checked_runs {rets : Tm} (h : Checked P rets) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) rets .nil := by
  obtain ⟨hP, hc, hs⟩ := h
  have hE : EnvOK P [] {tys := []} :=
    .mk rfl (fun _ _ _ h _ => by simp at h) (by simp) (fun _ _ h => by simp at h) (by simp)
      ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, by simp, by simp, by simp⟩
  obtain ⟨vs, cnt, e, hv, _⟩ :=
    eval_sound hP none [] 0 P.main _ _ rets hc hE (by simp [LvlBound]) (by simp [MuOK]) (by simpa [Ctx.n] using hs)
  exact ⟨vs, cnt, e, by rwa [Tm.subst_static0 _ _ 0 hs] at hv⟩

theorem no_value_of_empty {v : Tm} {d : Nat} {D : Adt} {args : Tm} (hD : P.adts[d]? = some D)
    (hempty : D.ctors = []) : ¬ VTy P v (.ty d args) := by
  intro h
  obtain ⟨c, vs, sig, mk, _, hc, _⟩ := h.ty_inv
  simp [Prog.ctor, hD, hempty] at hc

theorem no_false {d : Nat} {D : Adt} {args : Tm} {m : Bool} (hD : P.adts[d]? = some D) (hempty : D.ctors = []) :
    ¬ Checked P (.bind m (.ty d args) .nil) := by
  intro h
  obtain ⟨vs, _, _, hv⟩ := checked_runs h
  generalize Tm.ofList vs = w at hv
  cases hv with
  | cons hv _ => exact no_value_of_empty hD hempty hv

theorem check_sound {R : Tm} {h : Checked P R} (_ : checkProg P = .ok ⟨R, h⟩) :
    ∃ vs cnt, eval P none [] 0 P.main = .ok (vs, cnt) ∧ VTys P (.ofList vs) R .nil :=
  checked_runs h

end Minimal
