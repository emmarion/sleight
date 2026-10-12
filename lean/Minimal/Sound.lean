import Minimal.UnifySound
import Minimal.Check
import Minimal.Eval

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

end Minimal
