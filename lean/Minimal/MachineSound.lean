import Minimal.Machine
import Minimal.Sound

namespace Minimal

variable (P : Prog)

mutual
def rtReads (Γ : Ctx) : Tm → List Nat
  | .fv i => [i]
  | .app (.vc d c _) args => match P.ctor d c with
    | some sig => rtReadsArgs Γ args (sig.skip (P.lifted d))
    | none => []
  | .app (.fv i) args => i :: match (Γ.tys[i]?).map Γ.canon with
    | some (.valCtor sig) => rtReadsArgs Γ args sig
    | _ => []
  | _ => []

def rtReadsArgs (Γ : Ctx) : Tm → Tm → List Nat
  | .cons a as, .bind k _ r => (if k.er then [] else rtReads Γ a) ++ rtReadsArgs Γ as r
  | _, _ => []
end

mutual
def rtHeads (Γ : Ctx) : Tm → List Nat
  | .app (.vc d c _) args => match P.ctor d c with
    | some sig => rtHeadsArgs Γ args (sig.skip (P.lifted d))
    | none => []
  | .app (.fv i) args => i :: match (Γ.tys[i]?).map Γ.canon with
    | some (.valCtor sig) => rtHeadsArgs Γ args sig
    | _ => []
  | _ => []

def rtHeadsArgs (Γ : Ctx) : Tm → Tm → List Nat
  | .cons a as, .bind k _ r => (if k.er then [] else rtHeads Γ a) ++ rtHeadsArgs Γ as r
  | _, _ => []
end

variable {P}

theorem MDec.nat_inv {H : Heap} {n : Nat} {v : Tm} (h : MDec P H (.nat n) v) : v = .nat n := by
  cases h with
  | nat => rfl
  | tok h => rcases h with h | ⟨_, h⟩ <;> cases h

theorem MDec.nat_inv' {H : Heap} {n : Nat} {w : Tm} (h : MDec P H w (.nat n)) : w = .nat n := by
  cases h with
  | nat => rfl

theorem MDec.vc_inv' {H : Heap} {d c : Nat} {w : Tm} (h : MDec P H w (.vc d c .nil)) : w = .vc d c .nil := by
  cases h with
  | vc => rfl

theorem norm_cases (d c : Nat) (args : Tm) :
    P.norm (.app (.vc d c .nil) args) = .app (.vc d c .nil) args ∨
    (P.natD = some d ∧ ((c = 0 ∧ args = .nil ∧ P.norm (.app (.vc d c .nil) args) = .nat 0) ∨
      ∃ k, c = 1 ∧ args = .cons (.nat k) .nil ∧ P.norm (.app (.vc d c .nil) args) = .nat (k + 1))) := by
  unfold Prog.norm
  split
  · rename_i heq; simp only [Tm.app.injEq, Tm.vc.injEq] at heq; obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := heq
    split
    · exact .inr ⟨‹_›, .inl ⟨rfl, rfl, rfl⟩⟩
    · exact .inl rfl
  · rename_i k heq; simp only [Tm.app.injEq, Tm.vc.injEq] at heq; obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := heq
    split
    · exact .inr ⟨‹_›, .inr ⟨k, rfl, rfl, rfl⟩⟩
    · exact .inl rfl
  · exact .inl rfl

theorem MDecs.nil_inv {H : Heap} {ws : List Tm} (h : MDecs P H ws []) : ws = [] := by cases h; rfl
theorem MDecs.nil_inv' {H : Heap} {vs : List Tm} (h : MDecs P H [] vs) : vs = [] := by cases h; rfl

theorem place_ext {H : Heap} (hW : H.WF) (v : Tm) : H.Ext (P.place H v).1 ∧ (P.place H v).1.WF := by
  unfold Prog.place; split
  · exact Heap.alloc_ext hW _
  · exact ⟨Heap.Ext.refl _, hW⟩

theorem place_norm {H : Heap} (hW : H.WF) {d c : Nat} {margs sargs : Tm} (hl : margs.isList) (hs : sargs.isList)
    (hm : MDecs P H margs.toList sargs.toList) :
    H.Ext (P.place H (P.norm (.app (.vc d c .nil) margs))).1 ∧ (P.place H (P.norm (.app (.vc d c .nil) margs))).1.WF ∧
    MDec P (P.place H (P.norm (.app (.vc d c .nil) margs))).1 (P.place H (P.norm (.app (.vc d c .nil) margs))).2
      (P.norm (.app (.vc d c .nil) sargs)) := by
  have hplace : H.Ext (P.place H (.app (.vc d c .nil) margs)).1 ∧ (P.place H (.app (.vc d c .nil) margs)).1.WF ∧
      MDec P (P.place H (.app (.vc d c .nil) margs)).1 (P.place H (.app (.vc d c .nil) margs)).2
        (.app (.vc d c .nil) sargs) := by
    obtain ⟨he, hw⟩ := Heap.alloc_ext hW (d, c, margs.toList)
    refine ⟨he, hw, ?_⟩
    have := MDec.ptr (P := P) (Heap.alloc_new H (d, c, margs.toList)) (hm.mono he)
    rwa [Tm.ofList_toList _ hs] at this
  rcases norm_cases (P := P) d c margs with h | ⟨hd, ⟨rfl, rfl, h⟩ | ⟨k, rfl, rfl, h⟩⟩
  · rw [h]
    rcases norm_cases (P := P) d c sargs with h' | ⟨hd', ⟨rfl, rfl, h'⟩ | ⟨k, rfl, rfl, h'⟩⟩
    · rw [h']; exact hplace
    · have := hm.nil_inv
      cases margs <;> simp_all [Tm.toList, Tm.isList] <;> simp [Prog.norm, hd'] at h
    · cases margs with
      | cons a as =>
        simp only [Tm.toList] at hm
        cases hm with
        | cons hx hr =>
          have := hx.nat_inv'; subst this
          have := hr.nil_inv
          cases as <;> simp_all [Tm.toList, Tm.isList] <;> simp [Prog.norm, hd'] at h
      | _ => simp [Tm.toList] at hm; cases hm
  · rw [h]
    have := hm.nil_inv'
    cases sargs <;> simp_all [Tm.toList, Tm.isList]
    exact ⟨Heap.Ext.refl _, hW, by simp [Prog.norm, hd, Prog.place]; exact .nat⟩
  · rw [h]
    cases sargs with
    | cons a as =>
      simp only [Tm.toList] at hm
      cases hm with
      | cons hx hr =>
        have := hx.nat_inv; subst this
        have := hr.nil_inv'
        cases as <;> simp_all [Tm.toList, Tm.isList]
        exact ⟨Heap.Ext.refl _, hW, by simp [Prog.norm, hd, Prog.place]; exact .nat⟩
    | _ => simp [Tm.toList] at hm; cases hm

mutual
theorem build_ext {H : Heap} (hW : H.WF) (f : Nat → Tm) : ∀ t, H.Ext (P.build H f t).1 ∧ (P.build H f t).1.WF
  | .app h args => by
    obtain ⟨e1, w1⟩ := buildArgs_ext hW f args
    simp only [Prog.build]
    split
    · split
      · exact ⟨e1, w1⟩
      · exact ⟨e1.trans (place_ext w1 _).1, (place_ext w1 _).2⟩
    · exact ⟨e1, w1⟩
  | .fv _ | .vc .. | .bv _ | .nil | .cons .. | .bind .. | .tyc .. | .tyCtor _ | .valCtor _ | .univ | .level
  | .predates .. | .subterm .. | .fn .. | .mtbl .. | .lvl _ | .tok | .clo .. | .nat _ | .ptr _ => by
    simp only [Prog.build]; exact ⟨Heap.Ext.refl _, hW⟩

theorem buildArgs_ext {H : Heap} (hW : H.WF) (f : Nat → Tm) : ∀ t, H.Ext (P.buildArgs H f t).1 ∧ (P.buildArgs H f t).1.WF
  | .cons a as => by
    obtain ⟨e1, w1⟩ := build_ext hW f a
    obtain ⟨e2, w2⟩ := buildArgs_ext w1 f as
    simp only [Prog.buildArgs]; exact ⟨e1.trans e2, w2⟩
  | .fv _ | .vc .. | .bv _ | .nil | .app .. | .bind .. | .tyc .. | .tyCtor _ | .valCtor _ | .univ | .level
  | .predates .. | .subterm .. | .fn .. | .mtbl .. | .lvl _ | .tok | .clo .. | .nat _ | .ptr _ => by
    simp only [Prog.buildArgs]; exact ⟨Heap.Ext.refl _, hW⟩
end

theorem mask_isList : ∀ (ers : List Bool) (a : Tm), a.isList → (maskArgs ers a).isList
  | [], _, h => by simpa [maskArgs] using h
  | e :: es, .cons x xs, h => by simp only [maskArgs, Tm.isList] at h ⊢; exact mask_isList es xs h
  | _ :: _, .nil, _ => rfl
  | _ :: _, .fv _, h | _ :: _, .bv _, h | _ :: _, .app .., h | _ :: _, .bind .., h | _ :: _, .tyc .., h
  | _ :: _, .vc .., h | _ :: _, .tyCtor _, h | _ :: _, .valCtor _, h | _ :: _, .univ, h | _ :: _, .level, h
  | _ :: _, .predates .., h | _ :: _, .subterm .., h | _ :: _, .fn .., h | _ :: _, .mtbl .., h
  | _ :: _, .lvl _, h | _ :: _, .tok, h | _ :: _, .clo .., h | _ :: _, .nat _, h | _ :: _, .ptr _, h => by
    simp [Tm.isList] at h

theorem mask_mdecs {H : Heap} : ∀ (ers : List Bool) (a b : Tm), a.isList → b.isList → a.toList.length = b.toList.length →
    a.toList.length ≤ ers.length →
    (∀ k, k < a.toList.length → ers.getD k true = false → MDec P H (a.toList.getD k .nil) (b.toList.getD k .nil)) →
    MDecs P H (maskArgs ers a).toList (maskArgs ers b).toList
  | [], .nil, .nil, _, _, _, _, _ => by simp [maskArgs, Tm.toList]; exact .nil
  | e :: es, .nil, .nil, _, _, _, _, _ => by simp [maskArgs, Tm.toList]; exact .nil
  | e :: es, .cons x xs, .cons y ys, hl, hs, hlen, hle, hm => by
    simp only [maskArgs, Tm.toList]
    refine .cons ?_ (mask_mdecs es xs ys (by simpa [Tm.isList] using hl) (by simpa [Tm.isList] using hs)
      (by simpa [Tm.toList] using hlen) (by simp [Tm.toList] at hle; omega) fun k hk hk' => by
        simpa [Tm.toList] using hm (k + 1) (by simp [Tm.toList]; omega) (by simpa using hk'))
    cases e with
    | true => exact .tok (.inl rfl)
    | false => simpa [Tm.toList] using hm 0 (by simp [Tm.toList]) rfl
  | [], .cons .., _, _, _, _, hle, _ => by simp [Tm.toList] at hle
  | _, .nil, .cons .., _, _, hlen, _, _ => by simp [Tm.toList] at hlen
  | _, .cons .., .nil, _, _, hlen, _, _ => by simp [Tm.toList] at hlen
  | _, .nil, .fv _, _, h, _, _, _ | _, .nil, .bv _, _, h, _, _, _ | _, .nil, .app .., _, h, _, _, _
  | _, .nil, .bind .., _, h, _, _, _ | _, .nil, .tyc .., _, h, _, _, _ | _, .nil, .vc .., _, h, _, _, _
  | _, .nil, .tyCtor _, _, h, _, _, _ | _, .nil, .valCtor _, _, h, _, _, _ | _, .nil, .univ, _, h, _, _, _
  | _, .nil, .level, _, h, _, _, _ | _, .nil, .predates .., _, h, _, _, _ | _, .nil, .subterm .., _, h, _, _, _
  | _, .nil, .fn .., _, h, _, _, _ | _, .nil, .mtbl .., _, h, _, _, _ | _, .nil, .lvl _, _, h, _, _, _
  | _, .nil, .tok, _, h, _, _, _ | _, .nil, .clo .., _, h, _, _, _ | _, .nil, .nat _, _, h, _, _, _
  | _, .nil, .ptr _, _, h, _, _, _ => by simp [Tm.isList] at h
  | _, .cons .., .fv _, _, h, _, _, _ | _, .cons .., .bv _, _, h, _, _, _ | _, .cons .., .app .., _, h, _, _, _
  | _, .cons .., .bind .., _, h, _, _, _ | _, .cons .., .tyc .., _, h, _, _, _ | _, .cons .., .vc .., _, h, _, _, _
  | _, .cons .., .tyCtor _, _, h, _, _, _ | _, .cons .., .valCtor _, _, h, _, _, _ | _, .cons .., .univ, _, h, _, _, _
  | _, .cons .., .level, _, h, _, _, _ | _, .cons .., .predates .., _, h, _, _, _ | _, .cons .., .subterm .., _, h, _, _, _
  | _, .cons .., .fn .., _, h, _, _, _ | _, .cons .., .mtbl .., _, h, _, _, _ | _, .cons .., .lvl _, _, h, _, _, _
  | _, .cons .., .tok, _, h, _, _, _ | _, .cons .., .clo .., _, h, _, _, _ | _, .cons .., .nat _, _, h, _, _, _
  | _, .cons .., .ptr _, _, h, _, _, _ => by simp [Tm.isList] at h
  | _, .fv _, _, h, _, _, _, _ | _, .bv _, _, h, _, _, _, _ | _, .app .., _, h, _, _, _, _
  | _, .bind .., _, h, _, _, _, _ | _, .tyc .., _, h, _, _, _, _ | _, .vc .., _, h, _, _, _, _
  | _, .tyCtor _, _, h, _, _, _, _ | _, .valCtor _, _, h, _, _, _, _ | _, .univ, _, h, _, _, _, _
  | _, .level, _, h, _, _, _, _ | _, .predates .., _, h, _, _, _, _ | _, .subterm .., _, h, _, _, _, _
  | _, .fn .., _, h, _, _, _, _ | _, .mtbl .., _, h, _, _, _, _ | _, .lvl _, _, h, _, _, _, _
  | _, .tok, _, h, _, _, _, _ | _, .clo .., _, h, _, _, _, _ | _, .nat _, _, h, _, _, _, _
  | _, .ptr _, _, h, _, _, _, _ => by simp [Tm.isList] at h

def HeadsOK (P : Prog) (Γ : Ctx) (fS : Nat → Tm) (L : List Nat) : Prop :=
  ∀ i sig, i ∈ L → (Γ.tys[i]?).map Γ.canon = some (.valCtor sig) →
    ∃ d c sig0, fS i = .vc d c .nil ∧ P.ctor d c = some sig0 ∧ (sig0.skip (P.lifted d)).ers = sig.ers

theorem build_ctor {H : Heap} (hW : H.WF) {d c : Nat} {sig : Tm} (hc : P.ctor d c = some sig) {args' argsS : Tm}
    (hl : args'.isList) (hs : argsS.isList) (hlen : args'.toList.length = argsS.toList.length)
    (hle : args'.toList.length ≤ (sig.skip (P.lifted d)).ers.length)
    (hm : ∀ k, k < args'.toList.length → (sig.skip (P.lifted d)).ers.getD k true = false →
      MDec P H (args'.toList.getD k .nil) (argsS.toList.getD k .nil)) :
    let r : Heap × Tm := match P.wrapField d c with
      | some k => (H, args'.toList.getD k .nil)
      | none => P.place H (P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) args')))
    H.Ext r.1 ∧ r.1.WF ∧ MDec P r.1 r.2 (match P.wrapField d c with
      | some k => argsS.toList.getD k .nil
      | none => P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) argsS))) := by
  intro r
  have he : P.ctorErs d c = (sig.skip (P.lifted d)).ers := by simp [Prog.ctorErs, hc]
  cases hw : P.wrapField d c with
  | some k =>
    simp only [r, hw]
    obtain ⟨_, _, sig', hc', hk⟩ := Prog.wrapField_spec hw
    rw [hc] at hc'; cases hc'
    refine ⟨Heap.Ext.refl _, hW, ?_⟩
    by_cases hkl : k < args'.toList.length
    · exact hm k hkl (Tm.ntField_spec hk).2.1
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show args'.toList.length ≤ k by omega),
        List.getElem?_eq_none (show argsS.toList.length ≤ k by omega)]; exact .nil
  | none =>
    simp only [r, hw]
    rw [he]
    exact place_norm hW (mask_isList _ _ hl) (mask_isList _ _ hs) (mask_mdecs _ _ _ hl hs hlen hle hm)

mutual
theorem rt_build {Γ : Ctx} {f fS : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ t, rt P Γ t = true →
    (∀ i ∈ rtReads P Γ t, MDec P H (f i) (fS i)) → HeadsOK P Γ fS (rtHeads P Γ t) →
    H.Ext (P.build H f t).1 ∧ (P.build H f t).1.WF ∧ MDec P (P.build H f t).1 (P.build H f t).2 (P.subU fS t)
  | H, hW, .fv i, _, hr, _ => by
    simp only [Prog.build, Prog.subU]; exact ⟨Heap.Ext.refl _, hW, hr i (by simp [rtReads])⟩
  | H, hW, .vc d c ls, _, _, _ => by
    simp only [Prog.build, Prog.subU]; exact ⟨Heap.Ext.refl _, hW, .vc⟩
  | H, hW, .app (.vc d c ls) args, h, hr, hh => by
    simp only [rt] at h
    split at h
    · rename_i sig hc
      simp only [Bool.and_eq_true] at h
      have hr' : ∀ i ∈ rtReadsArgs P Γ args (sig.skip (P.lifted d)), MDec P H (f i) (fS i) :=
        fun i hi => hr i (by simp [rtReads, hc, hi])
      have hh' : HeadsOK P Γ fS (rtHeadsArgs P Γ args (sig.skip (P.lifted d))) :=
        fun i sg hi => hh i sg (by simp [rtHeads, hc, hi])
      obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
      obtain ⟨e2, w2, hd⟩ := build_ctor (P := P) w1 hc l1 l2 len hle hm
      simp only [Prog.build, Prog.subU]
      exact ⟨e1.trans e2, w2, hd⟩
    · simp at h
  | H, hW, .app (.fv i) args, h, hr, hh => by
    simp only [rt] at h
    split at h
    · rename_i sig hsig
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨d, c, sig0, hfi, hc, hers⟩ := hh i sig (by simp [rtHeads]) hsig
      have hri : MDec P H (f i) (fS i) := hr i (by simp [rtReads])
      rw [hfi] at hri
      have hfm := hri.vc_inv'
      have hr' : ∀ j ∈ rtReadsArgs P Γ args sig, MDec P H (f j) (fS j) :=
        fun j hj => hr j (by simp [rtReads, hsig, hj])
      have hh' : HeadsOK P Γ fS (rtHeadsArgs P Γ args sig) :=
        fun j sg hj => hh j sg (by simp [rtHeads, hsig, hj])
      obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
      rw [← hers] at hle hm
      obtain ⟨e2, w2, hd⟩ := build_ctor (P := P) w1 hc l1 l2 len hle hm
      simp only [Prog.build, Prog.subU, hfi, hfm]
      exact ⟨e1.trans e2, w2, hd⟩
    · simp at h
  | _, _, .app (.bv _) _, h, _, _ | _, _, .app .nil _, h, _, _ | _, _, .app (.cons ..) _, h, _, _
  | _, _, .app (.bind ..) _, h, _, _ | _, _, .app (.app ..) _, h, _, _ | _, _, .app (.tyc ..) _, h, _, _
  | _, _, .app (.tyCtor _) _, h, _, _ | _, _, .app (.valCtor _) _, h, _, _ | _, _, .app .univ _, h, _, _
  | _, _, .app .level _, h, _, _ | _, _, .app (.predates ..) _, h, _, _ | _, _, .app (.subterm ..) _, h, _, _
  | _, _, .app (.fn ..) _, h, _, _ | _, _, .app (.mtbl ..) _, h, _, _ | _, _, .app (.lvl _) _, h, _, _
  | _, _, .app .tok _, h, _, _ | _, _, .app (.clo ..) _, h, _, _ | _, _, .app (.nat _) _, h, _, _
  | _, _, .app (.ptr _) _, h, _, _
  | _, _, .bv _, h, _, _ | _, _, .nil, h, _, _ | _, _, .cons .., h, _, _ | _, _, .bind .., h, _, _
  | _, _, .tyc .., h, _, _ | _, _, .tyCtor _, h, _, _ | _, _, .valCtor _, h, _, _ | _, _, .univ, h, _, _
  | _, _, .level, h, _, _ | _, _, .predates .., h, _, _ | _, _, .subterm .., h, _, _ | _, _, .fn .., h, _, _
  | _, _, .mtbl .., h, _, _ | _, _, .lvl _, h, _, _ | _, _, .tok, h, _, _ | _, _, .clo .., h, _, _
  | _, _, .nat _, h, _, _ | _, _, .ptr _, h, _, _ => by simp [rt] at h

theorem rt_buildArgs {Γ : Ctx} {f fS : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ args sig, rtArgs P Γ args sig = true →
    (∀ i ∈ rtReadsArgs P Γ args sig, MDec P H (f i) (fS i)) → HeadsOK P Γ fS (rtHeadsArgs P Γ args sig) →
    H.Ext (P.buildArgs H f args).1 ∧ (P.buildArgs H f args).1.WF ∧ (P.buildArgs H f args).2.isList ∧
    (P.subUArgs fS args).isList ∧ (P.buildArgs H f args).2.toList.length = (P.subUArgs fS args).toList.length ∧
    (P.buildArgs H f args).2.toList.length ≤ sig.ers.length ∧
    ∀ k, k < (P.buildArgs H f args).2.toList.length → sig.ers.getD k true = false →
      MDec P (P.buildArgs H f args).1 ((P.buildArgs H f args).2.toList.getD k .nil) ((P.subUArgs fS args).toList.getD k .nil)
  | H, hW, .nil, _, _, _, _ => by
    simp only [Prog.buildArgs, Prog.subUArgs, Tm.subst, Tm.isList, Tm.toList]
    exact ⟨Heap.Ext.refl _, hW, trivial, trivial, by simp, by simp, fun k hk _ => by simp at hk⟩
  | H, hW, .cons a as, .bind k A r, h, hr, hh => by
    simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨e1, w1⟩ := build_ext (P := P) hW f a
    have hr2 : ∀ i ∈ rtReadsArgs P Γ as r, MDec P (P.build H f a).1 (f i) (fS i) :=
      fun i hi => (hr i (by simp [rtReadsArgs, hi])).mono e1
    have hh2 : HeadsOK P Γ fS (rtHeadsArgs P Γ as r) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hi])
    obtain ⟨e2, w2, l1, l2, len, hle, hm⟩ := rt_buildArgs w1 as r h.2 hr2 hh2
    simp only [Prog.buildArgs, Prog.subUArgs, Tm.isList, Tm.toList, List.length_cons, Tm.ers]
    refine ⟨e1.trans e2, w2, l1, l2, by omega, by omega, fun j hjl hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      simp only [List.getD_cons_zero] at hj
      have hk : k.er = false := hj
      have hrt : rt P Γ a = true := by simpa [hk] using h.1
      have := rt_build hW a hrt (fun i hi => hr i (by simp [rtReadsArgs, hk, hi]))
        (fun i sg hi => hh i sg (by simp [rtHeadsArgs, hk, hi]))
      exact this.2.2.mono e2
    | succ j => simpa using hm j (by simp at hjl; omega) (by simpa using hj)
  | _, _, .cons .., .nil, h, _, _ | _, _, .cons .., .fv _, h, _, _ | _, _, .cons .., .bv _, h, _, _
  | _, _, .cons .., .cons .., h, _, _ | _, _, .cons .., .app .., h, _, _ | _, _, .cons .., .tyc .., h, _, _
  | _, _, .cons .., .vc .., h, _, _ | _, _, .cons .., .tyCtor _, h, _, _ | _, _, .cons .., .valCtor _, h, _, _
  | _, _, .cons .., .univ, h, _, _ | _, _, .cons .., .level, h, _, _ | _, _, .cons .., .predates .., h, _, _
  | _, _, .cons .., .subterm .., h, _, _ | _, _, .cons .., .fn .., h, _, _ | _, _, .cons .., .mtbl .., h, _, _
  | _, _, .cons .., .lvl _, h, _, _ | _, _, .cons .., .tok, h, _, _ | _, _, .cons .., .clo .., h, _, _
  | _, _, .cons .., .nat _, h, _, _ | _, _, .cons .., .ptr _, h, _, _
  | _, _, .fv _, _, h, _, _ | _, _, .bv _, _, h, _, _ | _, _, .bind .., _, h, _, _ | _, _, .app .., _, h, _, _
  | _, _, .tyc .., _, h, _, _ | _, _, .vc .., _, h, _, _ | _, _, .tyCtor _, _, h, _, _ | _, _, .valCtor _, _, h, _, _
  | _, _, .univ, _, h, _, _ | _, _, .level, _, h, _, _ | _, _, .predates .., _, h, _, _ | _, _, .subterm .., _, h, _, _
  | _, _, .fn .., _, h, _, _ | _, _, .mtbl .., _, h, _, _ | _, _, .lvl _, _, h, _, _ | _, _, .tok, _, h, _, _
  | _, _, .clo .., _, h, _, _ | _, _, .nat _, _, h, _, _ | _, _, .ptr _, _, h, _, _ => by simp [rtArgs] at h
end

end Minimal
