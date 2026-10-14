import Minimal.Machine
import Minimal.Sound
import Minimal.Uses

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
  | tok h => rcases h with h | ⟨_, h, _⟩ <;> cases h

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

def Tm.kinds : Tm → List Ent
  | .bind k _ r => k :: r.kinds
  | _ => []

theorem Tm.kinds_inst (u : Tm) : ∀ (t : Tm) k, t.isTele → (t.inst u k).kinds = t.kinds := by
  intro t; induction t <;> intro k h <;> simp_all [Tm.inst, Tm.kinds, Tm.isTele]

theorem Tm.kinds_subst (f : Nat → Tm) : ∀ (t : Tm), t.isTele → (t.subst f).kinds = t.kinds := by
  intro t; induction t <;> intro h <;> simp_all [Tm.subst, Tm.kinds, Tm.isTele]

theorem Tm.kinds_skip : ∀ (t : Tm) (n : Nat), (t.skip n).kinds = t.kinds.drop n
  | .bind _ _ r, n + 1 => by simp [Tm.skip, Tm.kinds, Tm.kinds_skip r n]
  | .bind _ _ _, 0 => by simp [Tm.skip]
  | .fv _, n | .bv _, n | .nil, n | .cons .., n | .app .., n | .tyc .., n | .vc .., n | .tyCtor _, n
  | .valCtor _, n | .univ, n | .level, n | .predates .., n | .subterm .., n | .fn .., n | .mtbl .., n
  | .lvl _, n | .tok, n | .clo .., n | .nat _, n | .ptr _, n => by cases n <;> simp [Tm.skip, Tm.kinds]

theorem Tm.ers_kinds : ∀ (t : Tm), t.ers = t.kinds.map Ent.er
  | .bind _ _ r => by simp [Tm.ers, Tm.kinds, Tm.ers_kinds r]
  | .fv _ | .bv _ | .nil | .cons .. | .app .. | .tyc .. | .vc .. | .tyCtor _ | .valCtor _ | .univ | .level
  | .predates .. | .subterm .. | .fn .. | .mtbl .. | .lvl _ | .tok | .clo .. | .nat _ | .ptr _ => rfl

theorem Tm.uAt_kinds : ∀ (t : Tm) (k : Nat), t.uAt k = ((t.kinds[k]?).map Ent.u).getD false
  | .bind _ _ r, 0 => rfl
  | .bind _ _ r, k + 1 => by simp [Tm.uAt, Tm.kinds, Tm.uAt_kinds r k]
  | .fv _, _ | .bv _, _ | .nil, _ | .cons .., _ | .app .., _ | .tyc .., _ | .vc .., _ | .tyCtor _, _ | .valCtor _, _
  | .univ, _ | .level, _ | .predates .., _ | .subterm .., _ | .fn .., _ | .mtbl .., _ | .lvl _, _ | .tok, _
  | .clo .., _ | .nat _, _ | .ptr _, _ => by cases ‹Nat› <;> rfl

def HeadsOK (P : Prog) (Γ : Ctx) (fS fF : Nat → Tm) (L : List Nat) : Prop :=
  ∀ i sig, i ∈ L → (Γ.tys[i]?).map Γ.canon = some (.valCtor sig) →
    ∃ d c sig0 ls, fS i = .vc d c .nil ∧ fF i = .vc d c ls ∧ P.ctor d c = some sig0 ∧ sig.kinds <+: (sig0.skip (P.lifted d)).kinds

theorem prefix_getD {s s' : List Bool} (hp : s <+: s') {k : Nat} (hk : k < s.length) : s'.getD k true = s.getD k true := by
  obtain ⟨t, rfl⟩ := hp
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

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
theorem rt_build {Γ : Ctx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ t, rt P Γ t = true →
    (∀ i ∈ rtReads P Γ t, MDec P H (f i) (fS i)) → HeadsOK P Γ fS fF (rtHeads P Γ t) →
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
      have hh' : HeadsOK P Γ fS fF (rtHeadsArgs P Γ args (sig.skip (P.lifted d))) :=
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
      obtain ⟨d, c, sig0, -, hfi, -, hc, hk⟩ := hh i sig (by simp [rtHeads]) hsig
      have hers : sig.ers <+: (sig0.skip (P.lifted d)).ers := by rw [Tm.ers_kinds, Tm.ers_kinds]; exact hk.map _
      have hri : MDec P H (f i) (fS i) := hr i (by simp [rtReads])
      rw [hfi] at hri
      have hfm := hri.vc_inv'
      have hr' : ∀ j ∈ rtReadsArgs P Γ args sig, MDec P H (f j) (fS j) :=
        fun j hj => hr j (by simp [rtReads, hsig, hj])
      have hh' : HeadsOK P Γ fS fF (rtHeadsArgs P Γ args sig) :=
        fun j sg hj => hh j sg (by simp [rtHeads, hsig, hj])
      obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
      obtain ⟨e2, w2, hd⟩ := build_ctor (P := P) w1 hc l1 l2 len (Nat.le_trans hle hers.length_le)
        (fun k hk hke => hm k hk (by rw [← prefix_getD hers (by omega)]; exact hke))
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

theorem rt_buildArgs {Γ : Ctx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ args sig, rtArgs P Γ args sig = true →
    (∀ i ∈ rtReadsArgs P Γ args sig, MDec P H (f i) (fS i)) → HeadsOK P Γ fS fF (rtHeadsArgs P Γ args sig) →
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
    have hh2 : HeadsOK P Γ fS fF (rtHeadsArgs P Γ as r) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hi])
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

theorem MDecs.get' {H : Heap} : ∀ {ws vs : List Tm}, MDecs P H ws vs → ∀ (k : Nat) w v, ws[k]? = some w → vs[k]? = some v →
    MDec P H w v := fun h => h.get

theorem Foot.back {H H' : Heap} (he : H.Ext H') : ∀ {w v : Tm}, MDec P H w v → ∀ {b}, Foot P H' w v b → Foot P H w v b := by
  intro w v hm b hf
  induction hf generalizing H with
  | here => exact .here
  | field hb hw hv _ ih =>
    cases hm with
    | ptr hb0 hs =>
      have := he.2 _ _ hb0; rw [hb] at this; cases this
      rw [Tm.toList_ofList] at hv
      exact .field hb0 hw (by rw [Tm.toList_ofList]; exact hv) (ih he (hs.get _ _ _ hw hv))
  | clo hi _ ih =>
    cases hm with
    | clo hl hs =>
      rename_i envM envS _
      refine .clo hi (ih he ?_)
      rw [Tm.toList_ofList, Tm.toList_ofList]; exact hs _ hi

theorem Foot.tok_inv {H : Heap} {v : Tm} {b : Nat} (h : Foot P H .tok v b) : False := by cases h
theorem Foot.nat_inv {H : Heap} {n : Nat} {v : Tm} {b : Nat} (h : Foot P H (.nat n) v b) : False := by cases h
theorem Foot.nil_inv {H : Heap} {v : Tm} {b : Nat} (h : Foot P H .nil v b) : False := by cases h

theorem mask_get : ∀ (ers : List Bool) (a : Tm) (k : Nat) (w : Tm), (maskArgs ers a).toList[k]? = some w →
    w = .tok ∨ (k < ers.length → ers.getD k true = false) ∧ a.toList[k]? = some w
  | [], a, k, w, h => .inr ⟨fun h' => by simp at h', by simpa [maskArgs] using h⟩
  | e :: es, .cons x xs, 0, w, h => by
    simp only [maskArgs, Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at h
    cases e
    · exact .inr ⟨fun _ => rfl, by simp [Tm.toList, ← h]⟩
    · exact .inl h.symm
  | e :: es, .cons x xs, k + 1, w, h => by
    simp only [maskArgs, Tm.toList, List.getElem?_cons_succ] at h
    rcases mask_get es xs k w h with h1 | ⟨h1, h2⟩
    · exact .inl h1
    · exact .inr ⟨fun hk => by simpa using h1 (by simpa using hk), by simpa [Tm.toList] using h2⟩
  | _ :: _, .nil, _, _, h | _ :: _, .fv _, _, _, h | _ :: _, .bv _, _, _, h | _ :: _, .app .., _, _, h
  | _ :: _, .bind .., _, _, h | _ :: _, .tyc .., _, _, h | _ :: _, .vc .., _, _, h | _ :: _, .tyCtor _, _, _, h
  | _ :: _, .valCtor _, _, _, h | _ :: _, .univ, _, _, h | _ :: _, .level, _, _, h | _ :: _, .predates .., _, _, h
  | _ :: _, .subterm .., _, _, h | _ :: _, .fn .., _, _, h | _ :: _, .mtbl .., _, _, h | _ :: _, .lvl _, _, _, h
  | _ :: _, .tok, _, _, h | _ :: _, .clo .., _, _, h | _ :: _, .nat _, _, _, h | _ :: _, .ptr _, _, _, h => by
    simp [maskArgs, Tm.toList] at h

theorem mask_get' : ∀ (ers : List Bool) (a : Tm) (k : Nat), ers.getD k true = false →
    (maskArgs ers a).toList[k]? = a.toList[k]?
  | [], a, k, _ => by simp [maskArgs]
  | e :: es, .cons x xs, 0, h => by simp at h; simp [maskArgs, Tm.toList, h]
  | e :: es, .cons x xs, k + 1, h => by
    simp only [maskArgs, Tm.toList, List.getElem?_cons_succ]; exact mask_get' es xs k (by simpa using h)
  | _ :: _, .nil, _, _ | _ :: _, .fv _, _, _ | _ :: _, .bv _, _, _ | _ :: _, .app .., _, _
  | _ :: _, .bind .., _, _ | _ :: _, .tyc .., _, _ | _ :: _, .vc .., _, _ | _ :: _, .tyCtor _, _, _
  | _ :: _, .valCtor _, _, _ | _ :: _, .univ, _, _ | _ :: _, .level, _, _ | _ :: _, .predates .., _, _
  | _ :: _, .subterm .., _, _ | _ :: _, .fn .., _, _ | _ :: _, .mtbl .., _, _ | _ :: _, .lvl _, _, _
  | _ :: _, .tok, _, _ | _ :: _, .clo .., _, _ | _ :: _, .nat _, _, _ | _ :: _, .ptr _, _, _ => by
    simp [maskArgs]

theorem build_ctor_foot {H : Heap} (hW : H.WF) {d c : Nat} {sig : Tm} (hc : P.ctor d c = some sig) {args' argsS : Tm}
    (hl : args'.isList) (hs : argsS.isList) (hlen : args'.toList.length = argsS.toList.length)
    (hle : args'.toList.length ≤ (sig.skip (P.lifted d)).ers.length)
    (hm : ∀ k, k < args'.toList.length → (sig.skip (P.lifted d)).ers.getD k true = false →
      MDec P H (args'.toList.getD k .nil) (argsS.toList.getD k .nil)) {b : Nat} :
    let r : Heap × Tm := match P.wrapField d c with
      | some k => (H, args'.toList.getD k .nil)
      | none => P.place H (P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) args')))
    Foot P r.1 r.2 (match P.wrapField d c with
      | some k => argsS.toList.getD k .nil
      | none => P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) argsS))) b →
    H.next ≤ b ∨ ∃ k, k < args'.toList.length ∧ (sig.skip (P.lifted d)).ers.getD k true = false ∧
      Foot P H (args'.toList.getD k .nil) (argsS.toList.getD k .nil) b := by
  intro r hf
  have he : P.ctorErs d c = (sig.skip (P.lifted d)).ers := by simp [Prog.ctorErs, hc]
  cases hw : P.wrapField d c with
  | some k =>
    simp only [r, hw] at hf
    obtain ⟨_, _, sig', hc', hk⟩ := Prog.wrapField_spec hw
    rw [hc] at hc'; cases hc'
    by_cases hkl : k < args'.toList.length
    · exact .inr ⟨k, hkl, (Tm.ntField_spec hk).2.1, hf⟩
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show args'.toList.length ≤ k by omega)] at hf
      exact hf.nil_inv.elim
  | none =>
    simp only [r, hw] at hf
    rw [he] at hf
    rcases norm_cases (P := P) d c (maskArgs (sig.skip (P.lifted d)).ers args') with h | ⟨_, ⟨_, _, h⟩ | ⟨_, _, _, h⟩⟩
    · rw [h] at hf
      simp only [Prog.place, Heap.alloc] at hf
      rcases norm_cases (P := P) d c (maskArgs (sig.skip (P.lifted d)).ers argsS) with h' | ⟨_, ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩⟩
      · rw [h'] at hf
        cases hf with
        | here => exact .inl (Nat.le_refl _)
        | @field _ _ _ _ w v _ k _ hb hw' hv hf' =>
          simp only [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨-, -, rfl⟩ := hb
          rcases mask_get _ _ _ _ hw' with rfl | ⟨hk, hw2⟩
          · exact hf'.tok_inv.elim
          · have hkl : k < args'.toList.length := (List.getElem?_eq_some_iff.mp hw2).1
            have hke := hk (by omega)
            rw [mask_get' _ _ _ hke] at hv
            have e1 : args'.toList.getD k .nil = w := by simp [List.getD_eq_getElem?_getD, hw2]
            have e2 : argsS.toList.getD k .nil = v := by simp [List.getD_eq_getElem?_getD, hv]
            have hmk := hm k hkl hke
            rw [e1, e2] at hmk
            obtain ⟨hex, _⟩ := Heap.alloc_ext hW (d, c, (maskArgs (sig.skip (P.lifted d)).ers args').toList)
            exact .inr ⟨k, hkl, hke, by rw [e1, e2]; exact Foot.back hex hmk hf'⟩
      all_goals (rw [h'] at hf; cases hf; exact .inl (Nat.le_refl _))
    · rw [h] at hf; simp [Prog.place] at hf; exact hf.nat_inv.elim
    · rw [h] at hf; simp [Prog.place] at hf; exact hf.nat_inv.elim

mutual
theorem rt_build_foot {Γ : Ctx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ t, rt P Γ t = true →
    (∀ i ∈ rtReads P Γ t, MDec P H (f i) (fS i)) → HeadsOK P Γ fS fF (rtHeads P Γ t) → ∀ b,
    Foot P (P.build H f t).1 (P.build H f t).2 (P.subU fS t) b →
    H.next ≤ b ∨ ∃ i ∈ rtReads P Γ t, Foot P H (f i) (fS i) b
  | H, hW, .fv i, _, hr, _, b, hf => by
    simp only [Prog.build, Prog.subU] at hf; exact .inr ⟨i, by simp [rtReads], hf⟩
  | H, hW, .vc d c ls, _, _, _, b, hf => by simp only [Prog.build, Prog.subU] at hf; cases hf
  | H, hW, .app (.vc d c ls) args, h, hr, hh, b, hf => by
    simp only [rt] at h
    split at h
    · rename_i sig hc
      simp only [Bool.and_eq_true] at h
      have hr' : ∀ i ∈ rtReadsArgs P Γ args (sig.skip (P.lifted d)), MDec P H (f i) (fS i) :=
        fun i hi => hr i (by simp [rtReads, hc, hi])
      have hh' : HeadsOK P Γ fS fF (rtHeadsArgs P Γ args (sig.skip (P.lifted d))) :=
        fun i sg hi => hh i sg (by simp [rtHeads, hc, hi])
      obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
      simp only [Prog.build, Prog.subU] at hf
      rcases build_ctor_foot (P := P) w1 hc l1 l2 len hle hm hf with hb | ⟨k, hk, hke, hfk⟩
      · exact .inl (Nat.le_trans e1.1 hb)
      · rcases rt_buildArgs_foot hW args _ h.2 hr' hh' k hk hke b hfk with hb | ⟨i, hi, hfi⟩
        · exact .inl hb
        · exact .inr ⟨i, by simp [rtReads, hc, hi], hfi⟩
    · simp at h
  | H, hW, .app (.fv i) args, h, hr, hh, b, hf => by
    simp only [rt] at h
    split at h
    · rename_i sig hsig
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨d, c, sig0, -, hfi, -, hc, hk⟩ := hh i sig (by simp [rtHeads]) hsig
      have hers : sig.ers <+: (sig0.skip (P.lifted d)).ers := by rw [Tm.ers_kinds, Tm.ers_kinds]; exact hk.map _
      have hri : MDec P H (f i) (fS i) := hr i (by simp [rtReads])
      rw [hfi] at hri
      have hfm := hri.vc_inv'
      have hr' : ∀ j ∈ rtReadsArgs P Γ args sig, MDec P H (f j) (fS j) :=
        fun j hj => hr j (by simp [rtReads, hsig, hj])
      have hh' : HeadsOK P Γ fS fF (rtHeadsArgs P Γ args sig) :=
        fun j sg hj => hh j sg (by simp [rtHeads, hsig, hj])
      obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
      simp only [Prog.build, Prog.subU, hfi, hfm] at hf
      rcases build_ctor_foot (P := P) w1 hc l1 l2 len (Nat.le_trans hle hers.length_le)
        (fun k hk hke => hm k hk (by rw [← prefix_getD hers (by omega)]; exact hke)) hf with hb | ⟨k, hk, hke, hfk⟩
      · exact .inl (Nat.le_trans e1.1 hb)
      · rw [prefix_getD hers (by omega)] at hke
        rcases rt_buildArgs_foot hW args _ h.2 hr' hh' k hk hke b hfk with hb | ⟨j, hj, hfj⟩
        · exact .inl hb
        · exact .inr ⟨j, by simp [rtReads, hsig, hj], hfj⟩
    · simp at h
  | _, _, .app (.bv _) _, h, _, _, _, _ | _, _, .app .nil _, h, _, _, _, _ | _, _, .app (.cons ..) _, h, _, _, _, _
  | _, _, .app (.bind ..) _, h, _, _, _, _ | _, _, .app (.app ..) _, h, _, _, _, _ | _, _, .app (.tyc ..) _, h, _, _, _, _
  | _, _, .app (.tyCtor _) _, h, _, _, _, _ | _, _, .app (.valCtor _) _, h, _, _, _, _ | _, _, .app .univ _, h, _, _, _, _
  | _, _, .app .level _, h, _, _, _, _ | _, _, .app (.predates ..) _, h, _, _, _, _ | _, _, .app (.subterm ..) _, h, _, _, _, _
  | _, _, .app (.fn ..) _, h, _, _, _, _ | _, _, .app (.mtbl ..) _, h, _, _, _, _ | _, _, .app (.lvl _) _, h, _, _, _, _
  | _, _, .app .tok _, h, _, _, _, _ | _, _, .app (.clo ..) _, h, _, _, _, _ | _, _, .app (.nat _) _, h, _, _, _, _
  | _, _, .app (.ptr _) _, h, _, _, _, _
  | _, _, .bv _, h, _, _, _, _ | _, _, .nil, h, _, _, _, _ | _, _, .cons .., h, _, _, _, _ | _, _, .bind .., h, _, _, _, _
  | _, _, .tyc .., h, _, _, _, _ | _, _, .tyCtor _, h, _, _, _, _ | _, _, .valCtor _, h, _, _, _, _ | _, _, .univ, h, _, _, _, _
  | _, _, .level, h, _, _, _, _ | _, _, .predates .., h, _, _, _, _ | _, _, .subterm .., h, _, _, _, _ | _, _, .fn .., h, _, _, _, _
  | _, _, .mtbl .., h, _, _, _, _ | _, _, .lvl _, h, _, _, _, _ | _, _, .tok, h, _, _, _, _ | _, _, .clo .., h, _, _, _, _
  | _, _, .nat _, h, _, _, _, _ | _, _, .ptr _, h, _, _, _, _ => by simp [rt] at h

theorem rt_buildArgs_foot {Γ : Ctx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ args sig, rtArgs P Γ args sig = true →
    (∀ i ∈ rtReadsArgs P Γ args sig, MDec P H (f i) (fS i)) → HeadsOK P Γ fS fF (rtHeadsArgs P Γ args sig) →
    ∀ k, k < (P.buildArgs H f args).2.toList.length → sig.ers.getD k true = false → ∀ b,
    Foot P (P.buildArgs H f args).1 ((P.buildArgs H f args).2.toList.getD k .nil) ((P.subUArgs fS args).toList.getD k .nil) b →
    H.next ≤ b ∨ ∃ i ∈ rtReadsArgs P Γ args sig, Foot P H (f i) (fS i) b
  | H, hW, .nil, _, _, _, _, k, hk, _, _, _ => by simp [Prog.buildArgs, Tm.subst, Tm.toList] at hk
  | H, hW, .cons a as, .bind e A r, h, hr, hh, k, hk, hke, b, hf => by
    simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨e1, w1⟩ := build_ext (P := P) hW f a
    have hr2 : ∀ i ∈ rtReadsArgs P Γ as r, MDec P (P.build H f a).1 (f i) (fS i) :=
      fun i hi => (hr i (by simp [rtReadsArgs, hi])).mono e1
    have hh2 : HeadsOK P Γ fS fF (rtHeadsArgs P Γ as r) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hi])
    obtain ⟨e2, w2, -⟩ := rt_buildArgs w1 as r h.2 hr2 hh2
    simp only [Prog.buildArgs, Prog.subUArgs, Tm.toList, Tm.ers] at hf hk hke
    cases k with
    | zero =>
      simp only [List.getD_cons_zero] at hf hke
      have hrt : rt P Γ a = true := by simpa [hke] using h.1
      have hra : ∀ i ∈ rtReads P Γ a, MDec P H (f i) (fS i) := fun i hi => hr i (by simp [rtReadsArgs, hke, hi])
      have hha : HeadsOK P Γ fS fF (rtHeads P Γ a) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hke, hi])
      have hma := (rt_build hW a hrt hra hha).2.2
      rcases rt_build_foot hW a hrt hra hha b (Foot.back e2 hma hf) with hb | ⟨i, hi, hfi⟩
      · exact .inl hb
      · exact .inr ⟨i, by simp [rtReadsArgs, hke, hi], hfi⟩
    | succ k =>
      simp only [List.getD_cons_succ, List.length_cons] at hf hke hk
      rcases rt_buildArgs_foot w1 as r h.2 hr2 hh2 k (by omega) hke b hf with hb | ⟨i, hi, hfi⟩
      · exact .inl (Nat.le_trans e1.1 hb)
      · exact .inr ⟨i, by simp [rtReadsArgs, hi], Foot.back e1 (hr i (by simp [rtReadsArgs, hi])) hfi⟩
  | _, _, .cons .., .nil, h, _, _, _, _, _, _, _ | _, _, .cons .., .fv _, h, _, _, _, _, _, _, _ | _, _, .cons .., .bv _, h, _, _, _, _, _, _, _
  | _, _, .cons .., .cons .., h, _, _, _, _, _, _, _ | _, _, .cons .., .app .., h, _, _, _, _, _, _, _ | _, _, .cons .., .tyc .., h, _, _, _, _, _, _, _
  | _, _, .cons .., .vc .., h, _, _, _, _, _, _, _ | _, _, .cons .., .tyCtor _, h, _, _, _, _, _, _, _ | _, _, .cons .., .valCtor _, h, _, _, _, _, _, _, _
  | _, _, .cons .., .univ, h, _, _, _, _, _, _, _ | _, _, .cons .., .level, h, _, _, _, _, _, _, _ | _, _, .cons .., .predates .., h, _, _, _, _, _, _, _
  | _, _, .cons .., .subterm .., h, _, _, _, _, _, _, _ | _, _, .cons .., .fn .., h, _, _, _, _, _, _, _ | _, _, .cons .., .mtbl .., h, _, _, _, _, _, _, _
  | _, _, .cons .., .lvl _, h, _, _, _, _, _, _, _ | _, _, .cons .., .tok, h, _, _, _, _, _, _, _ | _, _, .cons .., .clo .., h, _, _, _, _, _, _, _
  | _, _, .cons .., .nat _, h, _, _, _, _, _, _, _ | _, _, .cons .., .ptr _, h, _, _, _, _, _, _, _
  | _, _, .fv _, _, h, _, _, _, _, _, _, _ | _, _, .bv _, _, h, _, _, _, _, _, _, _ | _, _, .bind .., _, h, _, _, _, _, _, _, _ | _, _, .app .., _, h, _, _, _, _, _, _, _
  | _, _, .tyc .., _, h, _, _, _, _, _, _, _ | _, _, .vc .., _, h, _, _, _, _, _, _, _ | _, _, .tyCtor _, _, h, _, _, _, _, _, _, _ | _, _, .valCtor _, _, h, _, _, _, _, _, _, _
  | _, _, .univ, _, h, _, _, _, _, _, _, _ | _, _, .level, _, h, _, _, _, _, _, _, _ | _, _, .predates .., _, h, _, _, _, _, _, _, _ | _, _, .subterm .., _, h, _, _, _, _, _, _, _
  | _, _, .fn .., _, h, _, _, _, _, _, _, _ | _, _, .mtbl .., _, h, _, _, _, _, _, _, _ | _, _, .lvl _, _, h, _, _, _, _, _, _, _ | _, _, .tok, _, h, _, _, _, _, _, _, _
  | _, _, .clo .., _, h, _, _, _, _, _, _, _ | _, _, .nat _, _, h, _, _, _, _, _, _, _ | _, _, .ptr _, _, h, _, _, _, _, _, _, _ => by simp [rtArgs] at h
end

theorem Uses.add_spec {U U' : Uses} {i : Nat} {u : Bool} (h : Uses.add U i u = some U') :
    U.lookup i ≠ some true ∧ (u = true → U.lookup i = none) ∧
    ∀ j, U'.lookup j = if j = i then some (u || (U.lookup i).getD false) else U.lookup j := by
  unfold Uses.add at h
  split at h
  · cases h
  · rename_i hl
    cases u
    · simp at h; subst h
      refine ⟨by simp [hl], by simp, fun j => ?_⟩
      split <;> simp_all
    · simp at h
  · rename_i hl
    simp at h; subst h
    refine ⟨by simp [hl], fun _ => hl, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simp [List.lookup, hl]
    · have : (j == i) = false := by simpa [beq_iff_eq] using hj
      simp [List.lookup, hj, this]

def Uses.merge : Option Bool → Option Bool → Option Bool
  | none, x => x
  | x, none => x
  | some a, some b => some (a || b)

def Uses.Free (A B : Uses) : Prop :=
  ∀ j, (A.lookup j = some true → B.lookup j = none) ∧ (B.lookup j = some true → A.lookup j = none)

theorem Uses.seq_spec : ∀ {B A U : Uses}, Uses.seq A B = some U →
    Uses.Free A B ∧ ∀ j, U.lookup j = Uses.merge (A.lookup j) (B.lookup j)
  | [], A, U, h => by
    simp [Uses.seq] at h; subst h
    exact ⟨fun j => by simp, fun j => by cases A.lookup j <;> rfl⟩
  | (i, u) :: B, A, U, h => by
    simp only [Uses.seq, List.foldlM_cons] at h
    obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hn, hu, hl⟩ := Uses.add_spec h1
    obtain ⟨hf, hm⟩ := Uses.seq_spec (A := A1) (B := B) h2
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [List.lookup, beq_self_eq_true]
        refine ⟨fun h' => absurd h' hn, fun h' => ?_⟩
        cases u <;> simp at h'; exact hu rfl
      · have hb : (j == i) = false := by simpa [beq_iff_eq] using hj
        simp only [List.lookup, hb]
        have := hl j; rw [if_neg hj] at this
        rw [← this]; exact hf j
    · by_cases hj : j = i
      · subst hj
        have e := hl j; rw [if_pos rfl] at e
        have hf' := hf j
        rw [hm j, e]
        simp only [List.lookup, beq_self_eq_true]
        cases hb : B.lookup j with
        | none => cases ha : A.lookup j <;> simp [Uses.merge, Bool.or_comm]
        | some q =>
          rw [e, hb] at hf'
          have hq : q = false := by cases q; rfl; exact absurd (hf'.2 rfl) (by simp)
          have hux : (u || (A.lookup j).getD false) = false := by
            cases hx : (u || (A.lookup j).getD false); rfl; rw [hx] at hf'; simp [hb] at hf'
          subst hq
          simp only [Bool.or_eq_false_iff] at hux
          obtain ⟨rfl, ha⟩ := hux
          cases ha' : A.lookup j with
          | none => simp [Uses.merge]
          | some x => rw [ha'] at ha; simp at ha; subst ha; simp [Uses.merge]
      · have hb : (j == i) = false := by simpa [beq_iff_eq] using hj
        have e := hl j; rw [if_neg hj] at e
        rw [hm j, e]; simp only [List.lookup, hb]

theorem Prog.rdU_rd {gid i : Nat} (h : P.rdU gid i = true) : P.rd gid i = true := by
  unfold Prog.rdU at h; unfold Prog.rd
  cases hg : P.groups[gid]? with
  | none => simp [hg] at h
  | some G =>
    simp only [hg, Option.map_some, Option.getD_some, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨⟨j, u⟩, hm, rfl, -⟩ := h
    exact ⟨_, hm, by simp⟩

theorem Foot.blk {H : Heap} : ∀ {w v : Tm}, MDec P H w v → ∀ {b}, Foot P H w v b → (H.blk b).isSome := by
  intro w v hm b hf
  induction hf with
  | here =>
    cases hm with
    | ptr hb _ => simp [hb]
    | tok h => rcases h with h | ⟨_, h, hb⟩ <;> cases h; exact hb
  | field hb hw hv _ ih =>
    cases hm with
    | ptr hb0 hs => rw [hb] at hb0; cases hb0; rw [Tm.toList_ofList] at hv; exact ih (hs.get _ _ _ hw hv)
  | clo hi _ ih =>
    cases hm with
    | clo hl hs => exact ih (by rw [Tm.toList_ofList, Tm.toList_ofList]; exact hs _ hi)

theorem Heap.Ext.agree {H H' : Heap} (he : H.Ext H') {w v : Tm} (hm : MDec P H w v) : Agree H H' (Foot P H w v) := by
  intro a ha
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Foot.blk hm ha)
  rw [hb, he.2 _ _ hb]

theorem Foot.fwd {H H' : Heap} : ∀ {w v : Tm}, Agree H H' (Foot P H w v) → ∀ {b}, Foot P H w v b → Foot P H' w v b := by
  intro w v hA b hf
  induction hf with
  | here => exact .here
  | field hb hw hv hf ih =>
    exact .field (by rw [hA _ .here]; exact hb) hw hv (ih fun a ha => hA a (.field hb hw hv ha))
  | clo hi hf ih => exact .clo hi (ih fun a ha => hA a (.clo hi ha))

theorem Foot.bwd {H H' : Heap} : ∀ {w v : Tm}, Agree H H' (Foot P H w v) → ∀ {b}, Foot P H' w v b → Foot P H w v b := by
  intro w v hA b hf
  induction hf with
  | here => exact .here
  | field hb hw hv hf ih =>
    have hb' : _ := hA _ .here; rw [hb] at hb'
    exact .field hb'.symm hw hv (ih fun a ha => hA a (.field hb'.symm hw hv ha))
  | clo hi hf ih => exact .clo hi (ih fun a ha => hA a (.clo hi ha))

theorem Spine.foot {H : Heap} {w u v : Tm} {b : Nat} (hs : Spine P H w u v b) : Foot P H w u b := by
  induction hs with
  | top => exact .here
  | field hb _ _ _ hw hu _ _ ih => exact .field hb hw hu ih
  | wrap _ _ _ _ _ ih => exact ih
  | clo hi _ ih => exact .clo (Prog.rdU_rd hi) ih

theorem Spine.fwd {H H' : Heap} {w u v : Tm} (hA : Agree H H' (Spine P H w u v)) {b : Nat} (hs : Spine P H w u v b) :
    Spine P H' w u v b := by
  induction hs with
  | top hn => exact .top hn
  | field hb hn hc hk hw hu hv _ ih =>
    exact .field (by rw [hA _ (.top hn)]; exact hb) hn hc hk hw hu hv (ih fun a ha => hA a (.field hb hn hc hk hw hu hv ha))
  | wrap hn hc hk hv _ ih => exact .wrap hn hc hk hv (ih fun a ha => hA a (.wrap hn hc hk hv ha))
  | clo hi _ ih => exact .clo hi (ih fun a ha => hA a (.clo hi ha))

theorem Spine.bwd {H H' : Heap} {w u v : Tm} (hA : Agree H H' (Spine P H w u v)) {b : Nat} (hs : Spine P H' w u v b) :
    Spine P H w u v b := by
  induction hs with
  | top hn => exact .top hn
  | field hb hn hc hk hw hu hv _ ih =>
    have hb' : _ := hA _ (.top hn); rw [hb] at hb'
    exact .field hb'.symm hn hc hk hw hu hv (ih fun a ha => hA a (.field hb'.symm hn hc hk hw hu hv ha))
  | wrap hn hc hk hv _ ih => exact .wrap hn hc hk hv (ih fun a ha => hA a (.wrap hn hc hk hv ha))
  | clo hi _ ih => exact .clo hi (ih fun a ha => hA a (.clo hi ha))

theorem Agree.spine {H H' : Heap} {w u v : Tm} (hA : Agree H H' (Foot P H w u)) : Agree H H' (Spine P H w u v) :=
  fun a ha => hA a ha.foot

theorem WO.fwd {H H' : Heap} {w u v : Tm} (hw : WO P H w u v) (hA : Agree H H' (Foot P H w u)) : WO P H' w u v := by
  induction hw with
  | ptr hb hn hc hcy hu hd ihu =>
    rename_i a d c ws sig ls vsS vs
    have sub : ∀ (k : Nat) w u, ws[k]? = some w → vsS.toList[k]? = some u → Agree H H' (Foot P H w u) :=
      fun k w u hw hu a ha => hA a (.field hb hw hu ha)
    refine .ptr (by rw [hA _ .here]; exact hb) hn hc
      (fun k w u hw hu hf => hcy k w u hw hu (Foot.bwd (sub k w u hw hu) hf))
      (fun k w u v hk hw hu hv => ihu k w u v hk hw hu hv (sub k w u hw hu))
      (fun k w u v hk hw hu hv j w' u' hj hw' hu' a h1 h2 =>
        hd k w u v hk hw hu hv j w' u' hj hw' hu' a (Spine.bwd (sub k w u hw hu).spine h1) (Foot.bwd (sub j w' u' hw' hu') h2))
  | wrap hn hc hk hv _ ih => exact .wrap hn hc hk hv (ih hA)
  | clo hu hd ihu =>
    rename_i gid j eM eS eF
    have sub : ∀ i, P.rd gid i = true → Agree H H' (Foot P H (Tm.env eM.toList i) (Tm.env eS.toList i)) :=
      fun i hi a ha => hA a (.clo hi ha)
    exact .clo (fun i hi => ihu i hi (sub i (Prog.rdU_rd hi)))
      (fun i hi i' hne hi' a h1 h2 =>
        hd i hi i' hne hi' a (Spine.bwd (sub i (Prog.rdU_rd hi)).spine h1) (Foot.bwd (sub i' hi') h2))
  | free hn => exact .free fun b h => hn b (Spine.bwd hA.spine h)

theorem Spine.word {H : Heap} {w u v : Tm} {b : Nat} (hs : Spine P H w u v b) :
    (∃ a, w = .ptr a) ∨ ∃ e g j, w = .clo e g j := by
  induction hs with
  | top => exact .inl ⟨_, rfl⟩
  | field => exact .inl ⟨_, rfl⟩
  | wrap _ _ _ _ _ ih => exact ih
  | clo => exact .inr ⟨_, _, _, rfl⟩

theorem Spine.imm {H : Heap} {w u v : Tm} {b : Nat} (hs : Spine P H w u v b) (h1 : ∀ a, w ≠ .ptr a)
    (h2 : ∀ e g j, w ≠ .clo e g j) : False := by
  rcases hs.word with ⟨a, rfl⟩ | ⟨e, g, j, rfl⟩
  · exact h1 a rfl
  · exact h2 e g j rfl

theorem build_ctor_spine {H : Heap} (hW : H.WF) {d c : Nat} {sig : Tm} (hc : P.ctor d c = some sig) {args' argsS : Tm}
    (hl : args'.isList) (hs : argsS.isList) (hlen : args'.toList.length = argsS.toList.length)
    (hle : args'.toList.length ≤ (sig.skip (P.lifted d)).ers.length)
    (hm : ∀ k, k < args'.toList.length → (sig.skip (P.lifted d)).ers.getD k true = false →
      MDec P H (args'.toList.getD k .nil) (argsS.toList.getD k .nil)) {ls argsF : Tm} {b : Nat} :
    let r : Heap × Tm := match P.wrapField d c with
      | some k => (H, args'.toList.getD k .nil)
      | none => P.place H (P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) args')))
    Spine P r.1 r.2 (match P.wrapField d c with
      | some k => argsS.toList.getD k .nil
      | none => P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) argsS))) (.app (.vc d c ls) argsF) b →
    H.next ≤ b ∨ ∃ k v, k < args'.toList.length ∧ (sig.skip (P.lifted d)).ers.getD k true = false ∧
      (sig.skip (P.lifted d)).uAt k = true ∧ argsF.toList[k]? = some v ∧
      Spine P H (args'.toList.getD k .nil) (argsS.toList.getD k .nil) v b := by
  intro r hf
  have he : P.ctorErs d c = (sig.skip (P.lifted d)).ers := by simp [Prog.ctorErs, hc]
  cases hw : P.wrapField d c with
  | some k =>
    simp only [r, hw] at hf
    obtain ⟨_, _, sig', hc', hk⟩ := Prog.wrapField_spec hw
    rw [hc] at hc'; cases hc'
    generalize hw' : args'.toList.getD k .nil = w at hf
    generalize hu' : argsS.toList.getD k .nil = u at hf
    cases hf with
    | top hn | field _ hn => rw [hw] at hn; cases hn
    | wrap hn hc2 hk2 hv hs2 =>
      rw [hw] at hn; cases hn; rw [hc] at hc2; cases hc2
      by_cases hkl : k < args'.toList.length
      · exact .inr ⟨k, _, hkl, (Tm.ntField_spec hk).2.1, hk2, hv, by rw [hw', hu']; exact hs2⟩
      · rw [← hw', List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hs2
        exact (hs2.imm (by simp) (by simp)).elim
  | none =>
    simp only [r, hw] at hf
    rw [he] at hf
    rcases norm_cases (P := P) d c (maskArgs (sig.skip (P.lifted d)).ers args') with h | ⟨_, ⟨_, _, h⟩ | ⟨_, _, _, h⟩⟩
    · rw [h] at hf
      simp only [Prog.place, Heap.alloc] at hf
      generalize hu' : P.norm (.app (.vc d c .nil) (maskArgs (sig.skip (P.lifted d)).ers argsS)) = u at hf
      cases hf with
      | top => exact .inl (Nat.le_refl _)
      | wrap hn => rw [hw] at hn; cases hn
      | field hb _ hc2 hk2 hw2 hu2 hv hs2 =>
        simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, -, rfl⟩ := hb
        rw [hc] at hc2; cases hc2
        rcases norm_cases (P := P) d c (maskArgs (sig.skip (P.lifted d)).ers argsS) with h' | ⟨_, ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩⟩
        · rw [h'] at hu'; simp only [Tm.app.injEq] at hu'; obtain ⟨-, rfl⟩ := hu'
          rcases mask_get _ _ _ _ hw2 with rfl | ⟨hk, hw3⟩
          · exact (hs2.imm (by simp) (by simp)).elim
          · have hkl := (List.getElem?_eq_some_iff.mp hw3).1
            have hke := hk (by omega)
            rw [mask_get' _ _ _ hke] at hu2
            have hmk := hm _ hkl hke
            have e : ∀ (l : List Tm) j x, l[j]? = some x → l.getD j .nil = x := fun l j x h => by
              simp [List.getD_eq_getElem?_getD, h]
            rw [e _ _ _ hw3, e _ _ _ hu2] at hmk
            obtain ⟨hex, _⟩ := Heap.alloc_ext hW (d, c, (maskArgs (sig.skip (P.lifted d)).ers args').toList)
            exact .inr ⟨_, _, hkl, hke, hk2, hv, by rw [e _ _ _ hw3, e _ _ _ hu2]; exact Spine.bwd (hex.agree hmk).spine hs2⟩
        all_goals (rw [h'] at hu'; cases hu')
    · rw [h] at hf; simp [Prog.place] at hf; exact (hf.imm (by simp) (by simp)).elim
    · rw [h] at hf; simp [Prog.place] at hf; exact (hf.imm (by simp) (by simp)).elim

def Live (P : Prog) (U : Uses) (n : Nat) (H : Heap) (ρM ρS : List Tm) (a : Nat) : Prop :=
  ∃ z < n, (U.lookup z).isSome ∧ Foot P H (Tm.env ρM z) (Tm.env ρS z) a

def Own (P : Prog) (U : Uses) (n : Nat) (H : Heap) (ρM ρS ρ : List Tm) (a : Nat) : Prop :=
  ∃ x < n, U.lookup x = some true ∧ Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) a

structure MFrame (P : Prog) (U : Uses) (n : Nat) (H : Heap) (ρM ρS ρ : List Tm) (Res Out : Nat → Prop) : Prop where
  lenM : ρM.length = n
  lenS : ρS.length = n
  wf : H.WF
  dec : ∀ i < n, (U.lookup i).isSome → MDec P H (Tm.env ρM i) (Tm.env ρS i)
  wo : ∀ x < n, U.lookup x = some true → WO P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x)
  sep : ∀ x < n, ∀ z < n, x ≠ z → U.lookup x = some true → (U.lookup z).isSome →
    Disj (Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x)) (Foot P H (Tm.env ρM z) (Tm.env ρS z))
  out : ∀ x < n, U.lookup x = some true → Disj (Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x)) Out
  res : Disj Res (Live P U n H ρM ρS) ∧ Disj Res Out ∧ Disj Res (Own P U n H ρM ρS ρ) ∧ ∀ a, Res a → (H.blk a).isSome

structure MOut (P : Prog) (U : Uses) (n : Nat) (H : Heap) (ρM ρS ρ : List Tm) (Res : Nat → Prop) (rets : Tm)
    (ru : List Bool) (H' : Heap) (vsM vsS vs : List Tm) : Prop where
  wf : H'.WF
  next : H.next ≤ H'.next
  keep : ∀ a, a < H.next → ¬ Own P U n H ρM ρS ρ a → ¬ Res a → H'.blk a = H.blk a
  len : vsM.length = vsS.length
  dec : ∀ k w u, vsM[k]? = some w → vsS[k]? = some u → rets.ers.getD k true = false → MDec P H' w u
  foot : ∀ k w u, vsM[k]? = some w → vsS[k]? = some u → rets.ers.getD k true = false → ∀ b, Foot P H' w u b →
    H.next ≤ b ∨ Own P U n H ρM ρS ρ b ∨ Res b ∨ Live P U n H ρM ρS b
  uspine : ∀ k w u v, vsM[k]? = some w → vsS[k]? = some u → vs[k]? = some v → rets.ers.getD k true = false →
    ru.getD k false = true → ∀ b, Spine P H' w u v b → H.next ≤ b ∨ Own P U n H ρM ρS ρ b ∨ Res b
  uwo : ∀ k w u v, vsM[k]? = some w → vsS[k]? = some u → vs[k]? = some v → rets.ers.getD k true = false →
    ru.getD k false = true → WO P H' w u v
  usep : ∀ k j w u v w' u', k ≠ j → vsM[k]? = some w → vsS[k]? = some u → vs[k]? = some v → vsM[j]? = some w' →
    vsS[j]? = some u' → rets.ers.getD k true = false → rets.ers.getD j true = false → ru.getD k false = true →
    Disj (Spine P H' w u v) (Foot P H' w' u')

theorem UCtx.sigOf_spec {G : UCtx} {h s : Tm} (e : G.sigOf P h = some s) :
    ∃ T, TmTy P G.Γ h T ∧ (G.Γ.canon T = .valCtor s ∨ G.Γ.canon T = .tyCtor s) := by
  unfold UCtx.sigOf at e
  split at e
  · rename_i T ht _
    split at e <;> simp at e
    · subst e; exact ⟨T, ht, .inl ‹_›⟩
    · subst e; exact ⟨T, ht, .inr ‹_›⟩
  · simp at e

theorem ArgsTy.kinds {Γ : Ctx} {args tele out : Tm} : ArgsTy P Γ args tele out → tele.isTele →
    out.kinds = tele.kinds.drop args.len
  | .nil, _ => by simp [Tm.len]
  | .cons (r := r) _ _ hr, h | .isCons (r := r) _ _ hr, h | .anyCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    rw [hr.kinds (Tm.isTele_inst _ _ 0 h), Tm.kinds_inst _ _ _ h]; simp [Tm.kinds, Tm.len]

theorem sigOf_vc {G : UCtx} {d c : Nat} {ls s sig : Tm} (e : G.sigOf P (.vc d c ls) = some s) (hc : P.ctor d c = some sig)
    (hP : ProgOK P) : s.kinds = (sig.skip (P.lifted d)).kinds := by
  obtain ⟨T, ht, hT⟩ := UCtx.sigOf_spec e
  cases ht with
  | vc hc' hl ha =>
    rw [hc] at hc'; cases hc'
    have hst : sig.isTele := by
      obtain ⟨D, hD, hs'⟩ := Option.bind_eq_some_iff.mp hc
      exact (hP.ctors _ _ _ _ hD hs').1.isTele
    rcases hT with hT | hT <;> simp only [Ctx.canon, canonBy, Tm.subst] at hT <;> cases hT
    rw [Tm.kinds_subst _ _ (ha.isTele hst), ha.kinds hst, Tm.kinds_skip, hl]

theorem Uses.merge_isSome {a b : Option Bool} (h : a.isSome ∨ b.isSome) : (Uses.merge a b).isSome := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp_all [Uses.merge]

theorem Uses.seq_isSome {A B U : Uses} (h : Uses.seq A B = some U) {i : Nat}
    (hi : (A.lookup i).isSome ∨ (B.lookup i).isSome) : (U.lookup i).isSome := by
  rw [(Uses.seq_spec h).2 i]; exact Uses.merge_isSome hi

mutual
theorem termUses_reads (hP : ProgOK P) {G : UCtx} : ∀ {u : Bool} {t : Tm} {A : Uses}, G.termUses P u t = some A →
    ∀ i ∈ rtReads P G.Γ t, (A.lookup i).isSome
  | u, .fv j, A, h, i, hi => by
    simp only [rtReads, List.mem_singleton] at hi; subst hi
    simp only [UCtx.termUses, UCtx.use] at h
    split at h <;> simp at h; subst h; simp
  | u, .app (.vc d c ls) args, A, h, i, hi => by
    simp only [rtReads] at hi
    split at hi
    · rename_i sig hc
      simp only [UCtx.termUses] at h
      split at h
      · rename_i s hs
        obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
        cases h2
        exact argsUses_reads hP h1 (by rw [Tm.ers_kinds, Tm.ers_kinds, sigOf_vc hs hc hP]) i hi
      · cases h
    · simp at hi
  | u, .app (.fv j) args, A, h, i, hi => by
    simp only [UCtx.termUses] at h
    split at h
    · rename_i s hs
      obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      simp only [rtReads, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact Uses.seq_isSome h2 (.inl (by simp))
      · split at hi
        · rename_i sig hsig
          obtain ⟨T, ht, hT⟩ := UCtx.sigOf_spec hs
          cases ht with
          | fv hj =>
            rw [hj] at hsig; simp only [Option.map_some, Option.some.injEq] at hsig
            rcases hT with hT | hT <;> rw [hT] at hsig <;> cases hsig
            exact Uses.seq_isSome h2 (.inr (argsUses_reads hP h1 rfl i hi))
          | fvIs hj _ _ =>
            rw [hj] at hsig; simp [Ctx.canon, canonBy, Tm.subst] at hsig
        · simp at hi
    · cases h
  | _, .app (.bv _) _, _, _, _, hi | _, .app .nil _, _, _, _, hi | _, .app (.cons ..) _, _, _, _, hi
  | _, .app (.bind ..) _, _, _, _, hi | _, .app (.app ..) _, _, _, _, hi | _, .app (.tyc ..) _, _, _, _, hi
  | _, .app (.tyCtor _) _, _, _, _, hi | _, .app (.valCtor _) _, _, _, _, hi | _, .app .univ _, _, _, _, hi
  | _, .app .level _, _, _, _, hi | _, .app (.predates ..) _, _, _, _, hi | _, .app (.subterm ..) _, _, _, _, hi
  | _, .app (.fn ..) _, _, _, _, hi | _, .app (.mtbl ..) _, _, _, _, hi | _, .app (.lvl _) _, _, _, _, hi
  | _, .app .tok _, _, _, _, hi | _, .app (.clo ..) _, _, _, _, hi | _, .app (.nat _) _, _, _, _, hi
  | _, .app (.ptr _) _, _, _, _, hi
  | _, .bv _, _, _, _, hi | _, .nil, _, _, _, hi | _, .cons .., _, _, _, hi | _, .bind .., _, _, _, hi
  | _, .tyc .., _, _, _, hi | _, .tyCtor _, _, _, _, hi | _, .valCtor _, _, _, _, hi | _, .univ, _, _, _, hi
  | _, .level, _, _, _, hi | _, .predates .., _, _, _, hi | _, .subterm .., _, _, _, hi | _, .fn .., _, _, _, hi
  | _, .mtbl .., _, _, _, hi | _, .lvl _, _, _, _, hi | _, .tok, _, _, _, hi | _, .clo .., _, _, _, hi
  | _, .nat _, _, _, _, hi | _, .ptr _, _, _, _, hi | _, .vc .., _, _, _, hi => by simp [rtReads] at hi

theorem argsUses_reads (hP : ProgOK P) {G : UCtx} : ∀ {md : Ent → Bool} {args s sig : Tm} {A : Uses},
    G.argsUses P md args s = some A → s.ers = sig.ers → ∀ i ∈ rtReadsArgs P G.Γ args sig, (A.lookup i).isSome
  | md, .cons a as, s, sig, A, h, he, i, hi => by
    cases sig with
    | bind k' _ r' =>
      cases s with
      | bind k _ r =>
        simp only [Tm.ers, List.cons.injEq] at he
        simp only [rtReadsArgs, List.mem_append, ← he.1] at hi
        simp only [UCtx.argsUses] at h
        cases hk : k.er
        · simp only [hk, ↓reduceIte] at h hi
          obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
          rcases hi with hi | hi
          · exact Uses.seq_isSome h3 (.inl (termUses_reads hP h1 i (by simpa using hi)))
          · exact Uses.seq_isSome h3 (.inr (argsUses_reads hP hB he.2 i hi))
        · simp only [hk, ↓reduceIte] at h hi
          obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
          rcases hi with hi | hi
          · simp at hi
          · exact Uses.seq_isSome h3 (.inr (argsUses_reads hP hB he.2 i hi))
      | _ => simp [Tm.ers] at he
    | _ => simp [rtReadsArgs] at hi
  | _, .nil, _, _, _, _, _, _, hi | _, .fv _, _, _, _, _, _, _, hi | _, .bv _, _, _, _, _, _, _, hi
  | _, .bind .., _, _, _, _, _, _, hi | _, .app .., _, _, _, _, _, _, hi | _, .tyc .., _, _, _, _, _, _, hi
  | _, .vc .., _, _, _, _, _, _, hi | _, .tyCtor _, _, _, _, _, _, _, hi | _, .valCtor _, _, _, _, _, _, _, hi
  | _, .univ, _, _, _, _, _, _, hi | _, .level, _, _, _, _, _, _, hi | _, .predates .., _, _, _, _, _, _, hi
  | _, .subterm .., _, _, _, _, _, _, hi | _, .fn .., _, _, _, _, _, _, hi | _, .mtbl .., _, _, _, _, _, _, hi
  | _, .lvl _, _, _, _, _, _, _, hi | _, .tok, _, _, _, _, _, _, hi | _, .clo .., _, _, _, _, _, _, hi
  | _, .nat _, _, _, _, _, _, _, hi | _, .ptr _, _, _, _, _, _, _, hi => by simp [rtReadsArgs] at hi
end

theorem Tm.kinds_subst_prefix (f : Nat → Tm) : ∀ (t : Tm), t.kinds <+: (t.subst f).kinds
  | .bind _ _ r => by simpa [Tm.subst, Tm.kinds] using Tm.kinds_subst_prefix f r
  | .fv _ | .bv _ | .nil | .cons .. | .app .. | .tyc .. | .vc .. | .tyCtor _ | .valCtor _ | .univ | .level
  | .predates .. | .subterm .. | .fn .. | .mtbl .. | .lvl _ | .tok | .clo .. | .nat _ | .ptr _ => List.nil_prefix

theorem VTys.kinds : ∀ {vs tele out : Tm}, VTys P vs tele out → tele.isTele → out.kinds = tele.kinds.drop vs.len
  | _, _, _, .nil, _ => by simp [Tm.len]
  | _, _, _, .cons (r := r) _ hr, h | _, _, _, .isCons (r := r) _ hr, h => by
    simp only [Tm.isTele] at h
    rw [hr.kinds (Tm.isTele_inst _ _ 0 h), Tm.kinds_inst _ _ _ h]; simp [Tm.kinds, Tm.len]

theorem head_ok (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) {i : Nat} {sig : Tm}
    (hsig : (Γ.tys[i]?).map Γ.canon = some (.valCtor sig)) (her : Γ.er i = false) :
    ∃ d c sig0 ls, Tm.env ρS i = .vc d c .nil ∧ Tm.env ρ i = .vc d c ls ∧ P.ctor d c = some sig0 ∧
      sig.kinds <+: (sig0.skip (P.lifted d)).kinds := by
  simp only [Option.map_eq_some_iff] at hsig
  obtain ⟨T, hT, hcT⟩ := hsig
  obtain ⟨v, -, hev, hv⟩ := hE.get hT
  rw [← hE.canon, hcT] at hv; simp only [Tm.subst] at hv
  obtain ⟨d, c, ls, sig0, rfl, hc, hl, hvs⟩ := hv.vc_inv
  have hR := hS.2 i her; rw [hev] at hR
  have hsig0 : sig0.isTele := by
    obtain ⟨D', hD', hs'⟩ := Option.bind_eq_some_iff.mp hc
    exact (hP.ctors _ _ _ _ hD' hs').1.isTele
  refine ⟨d, c, sig0, ls, hR.vc_inv.1, hev, hc, ?_⟩
  rw [Tm.kinds_skip, ← hl, ← hvs.kinds hsig0]; exact Tm.kinds_subst_prefix _ _

mutual
theorem heads_ok (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ t, rt P Γ t = true → HeadsOK P Γ (Tm.env ρS) (Tm.env ρ) (rtHeads P Γ t)
  | .app (.vc d c ls) args, h => by
    intro i sg hi hsg
    simp only [rt] at h; simp only [rtHeads] at hi
    split at h
    · rename_i sig hc
      simp only [hc, Bool.and_eq_true] at hi h
      exact heads_okArgs hP hE hS args _ h.2 i sg hi hsg
    · simp at h
  | .app (.fv j) args, h => by
    intro i sg hi hsg
    simp only [rt] at h; simp only [rtHeads, List.mem_cons] at hi
    split at h
    · rename_i sig hsig
      simp only [hsig, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi h
      rcases hi with rfl | hi
      · exact head_ok hP hE hS hsg h.1
      · exact heads_okArgs hP hE hS args _ h.2 i sg hi hsg
    · simp at h
  | .fv _, _ | .vc .., _ => fun i _ hi => by simp [rtHeads] at hi
  | .app (.bv _) _, h | .app .nil _, h | .app (.cons ..) _, h
  | .app (.bind ..) _, h | .app (.app ..) _, h | .app (.tyc ..) _, h
  | .app (.tyCtor _) _, h | .app (.valCtor _) _, h | .app .univ _, h
  | .app .level _, h | .app (.predates ..) _, h | .app (.subterm ..) _, h
  | .app (.fn ..) _, h | .app (.mtbl ..) _, h | .app (.lvl _) _, h
  | .app .tok _, h | .app (.clo ..) _, h | .app (.nat _) _, h | .app (.ptr _) _, h
  | .bv _, h | .nil, h | .cons .., h | .bind .., h | .tyc .., h | .tyCtor _, h | .valCtor _, h | .univ, h
  | .level, h | .predates .., h | .subterm .., h | .fn .., h | .mtbl .., h | .lvl _, h | .tok, h | .clo .., h
  | .nat _, h | .ptr _, h => by simp [rt] at h

theorem heads_okArgs (hP : ProgOK P) {Γ : Ctx} {ρS ρ : List Tm} (hE : EnvOK P ρ Γ) (hS : SimEnv P Γ.er ρS ρ) :
    ∀ args sig, rtArgs P Γ args sig = true → HeadsOK P Γ (Tm.env ρS) (Tm.env ρ) (rtHeadsArgs P Γ args sig)
  | .cons a as, .bind k _ r, h => by
    intro i sg hi hsg
    simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
    simp only [rtHeadsArgs, List.mem_append] at hi
    rcases hi with hi | hi
    · cases hk : k.er
      · simp only [hk, ↓reduceIte] at hi
        exact heads_ok hP hE hS a (by simpa [hk] using h.1) i sg hi hsg
      · simp [hk] at hi
    · exact heads_okArgs hP hE hS as r h.2 i sg hi hsg
  | .nil, _, _ | .cons .., .nil, _ | .cons .., .fv _, _ | .cons .., .bv _, _ | .cons .., .cons .., _
  | .cons .., .app .., _ | .cons .., .tyc .., _ | .cons .., .vc .., _ | .cons .., .tyCtor _, _
  | .cons .., .valCtor _, _ | .cons .., .univ, _ | .cons .., .level, _ | .cons .., .predates .., _
  | .cons .., .subterm .., _ | .cons .., .fn .., _ | .cons .., .mtbl .., _ | .cons .., .lvl _, _
  | .cons .., .tok, _ | .cons .., .clo .., _ | .cons .., .nat _, _ | .cons .., .ptr _, _
  | .fv _, _, _ | .bv _, _, _ | .bind .., _, _ | .app .., _, _ | .tyc .., _, _ | .vc .., _, _ | .tyCtor _, _, _
  | .valCtor _, _, _ | .univ, _, _ | .level, _, _ | .predates .., _, _ | .subterm .., _, _ | .fn .., _, _
  | .mtbl .., _, _ | .lvl _, _, _ | .tok, _, _ | .clo .., _, _ | .nat _, _, _ | .ptr _, _, _ =>
    fun i _ hi => by simp [rtHeadsArgs] at hi
end

theorem Uses.seq_true {A B U : Uses} (h : Uses.seq A B = some U) {i : Nat}
    (hi : A.lookup i = some true ∨ B.lookup i = some true) : U.lookup i = some true := by
  rw [(Uses.seq_spec h).2 i]
  rcases hi with hi | hi <;> rw [hi]
  · cases B.lookup i <;> simp [Uses.merge]
  · cases A.lookup i <;> simp [Uses.merge]

theorem prefix_uAt {s s' : Tm} (hp : s.kinds <+: s'.kinds) {k : Nat} (hk : k < s.kinds.length) : s'.uAt k = s.uAt k := by
  obtain ⟨t, ht⟩ := hp
  rw [Tm.uAt_kinds, Tm.uAt_kinds, ← ht, List.getElem?_append_left hk]

mutual
theorem rt_build_spine (hP : ProgOK P) {G : UCtx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF → ∀ t A,
    rt P G.Γ t = true → G.termUses P true t = some A →
    (∀ i ∈ rtReads P G.Γ t, MDec P H (f i) (fS i)) → HeadsOK P G.Γ fS fF (rtHeads P G.Γ t) → ∀ b,
    Spine P (P.build H f t).1 (P.build H f t).2 (P.subU fS t) (t.subst fF) b →
    H.next ≤ b ∨ ∃ i ∈ rtReads P G.Γ t, A.lookup i = some true ∧ Spine P H (f i) (fS i) (fF i) b
  | H, hW, .fv i, A, _, hu, _, _, b, hs => by
    simp only [UCtx.termUses, UCtx.use] at hu
    split at hu <;> simp at hu; subst hu
    simp only [Prog.build, Prog.subU, Tm.subst] at hs
    exact .inr ⟨i, by simp [rtReads], by simp, hs⟩
  | H, hW, .vc d c ls, _, _, _, _, _, b, hs => by
    simp only [Prog.build, Prog.subU, Tm.subst] at hs; exact (hs.imm (by simp) (by simp)).elim
  | H, hW, .app (.vc d c ls) args, A, h, hu, hr, hh, b, hs => by
    simp only [rt] at h
    split at h
    · rename_i sig hc
      simp only [Bool.and_eq_true] at h
      simp only [UCtx.termUses] at hu
      split at hu
      · rename_i s hsg
        obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hu
        cases h2
        have hr' : ∀ i ∈ rtReadsArgs P G.Γ args (sig.skip (P.lifted d)), MDec P H (f i) (fS i) :=
          fun i hi => hr i (by simp [rtReads, hc, hi])
        have hh' : HeadsOK P G.Γ fS fF (rtHeadsArgs P G.Γ args (sig.skip (P.lifted d))) :=
          fun i sg hi => hh i sg (by simp [rtHeads, hc, hi])
        obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
        simp only [Prog.build, Prog.subU, Tm.subst] at hs
        rcases build_ctor_spine (P := P) w1 hc l1 l2 len hle hm hs with hb | ⟨k, v, hk, hke, hku, hv, hsk⟩
        · exact .inl (Nat.le_trans e1.1 hb)
        · rcases rt_buildArgs_spine hP hW args _ s _ _ h.2 h1 (sigOf_vc hsg hc hP) (fun e he => by simp [he])
            hr' hh' k v hk hke hku hv b hsk with hb | ⟨i, hi, hl, hsi⟩
          · exact .inl hb
          · exact .inr ⟨i, by simp [rtReads, hc, hi], hl, hsi⟩
      · cases hu
    · simp at h
  | H, hW, .app (.fv j) args, A, h, hu, hr, hh, b, hs => by
    simp only [rt] at h
    split at h
    · rename_i sig hsig
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨d, c, sig0, ls, hfi, hfF, hc, hk⟩ := hh j sig (by simp [rtHeads]) hsig
      have hers : sig.ers <+: (sig0.skip (P.lifted d)).ers := by rw [Tm.ers_kinds, Tm.ers_kinds]; exact hk.map _
      have hri : MDec P H (f j) (fS j) := hr j (by simp [rtReads])
      rw [hfi] at hri
      have hfm := hri.vc_inv'
      simp only [UCtx.termUses] at hu
      split at hu
      · rename_i s hsg
        obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hu
        have hss : s = sig := by
          obtain ⟨T, ht, hT⟩ := UCtx.sigOf_spec hsg
          cases ht with
          | fv hj =>
            rw [hj] at hsig; simp only [Option.map_some, Option.some.injEq] at hsig
            rcases hT with hT | hT <;> rw [hT] at hsig <;> cases hsig; rfl
          | fvIs hj _ _ => rw [hj] at hsig; simp [Ctx.canon, canonBy, Tm.subst] at hsig
        subst hss
        have hr' : ∀ i ∈ rtReadsArgs P G.Γ args s, MDec P H (f i) (fS i) :=
          fun i hi => hr i (by simp [rtReads, hsig, hi])
        have hh' : HeadsOK P G.Γ fS fF (rtHeadsArgs P G.Γ args s) :=
          fun i sg hi => hh i sg (by simp [rtHeads, hsig, hi])
        obtain ⟨e1, w1, l1, l2, len, hle, hm⟩ := rt_buildArgs hW args _ h.2 hr' hh'
        simp only [Prog.build, Prog.subU, Tm.subst, hfi, hfm, hfF] at hs
        rcases build_ctor_spine (P := P) w1 hc l1 l2 len (Nat.le_trans hle hers.length_le)
          (fun k hk hke => hm k hk (by rw [← prefix_getD hers (by omega)]; exact hke)) hs with
          hb | ⟨k, v, hk', hke, hku, hv, hsk⟩
        · exact .inl (Nat.le_trans e1.1 hb)
        · have hkl : k < s.kinds.length := by
            have := Nat.lt_of_lt_of_le hk' hle; rwa [Tm.ers_kinds, List.length_map] at this
          rw [prefix_getD hers (by rw [Tm.ers_kinds, List.length_map]; exact hkl)] at hke
          rw [prefix_uAt hk hkl] at hku
          rcases rt_buildArgs_spine hP hW args _ s _ A1 h.2 h1 rfl (fun e he => by simp [he])
            hr' hh' k v hk' hke hku hv b hsk with hb | ⟨i, hi, hl, hsi⟩
          · exact .inl hb
          · exact .inr ⟨i, by simp [rtReads, hsig, hi], Uses.seq_true h2 (.inr hl), hsi⟩
      · cases hu
    · simp at h
  | _, _, .app (.bv _) _, _, h, _, _, _, _, _ | _, _, .app .nil _, _, h, _, _, _, _, _
  | _, _, .app (.cons ..) _, _, h, _, _, _, _, _ | _, _, .app (.bind ..) _, _, h, _, _, _, _, _
  | _, _, .app (.app ..) _, _, h, _, _, _, _, _ | _, _, .app (.tyc ..) _, _, h, _, _, _, _, _
  | _, _, .app (.tyCtor _) _, _, h, _, _, _, _, _ | _, _, .app (.valCtor _) _, _, h, _, _, _, _, _
  | _, _, .app .univ _, _, h, _, _, _, _, _ | _, _, .app .level _, _, h, _, _, _, _, _
  | _, _, .app (.predates ..) _, _, h, _, _, _, _, _ | _, _, .app (.subterm ..) _, _, h, _, _, _, _, _
  | _, _, .app (.fn ..) _, _, h, _, _, _, _, _ | _, _, .app (.mtbl ..) _, _, h, _, _, _, _, _
  | _, _, .app (.lvl _) _, _, h, _, _, _, _, _ | _, _, .app .tok _, _, h, _, _, _, _, _
  | _, _, .app (.clo ..) _, _, h, _, _, _, _, _ | _, _, .app (.nat _) _, _, h, _, _, _, _, _
  | _, _, .app (.ptr _) _, _, h, _, _, _, _, _
  | _, _, .bv _, _, h, _, _, _, _, _ | _, _, .nil, _, h, _, _, _, _, _ | _, _, .cons .., _, h, _, _, _, _, _
  | _, _, .bind .., _, h, _, _, _, _, _ | _, _, .tyc .., _, h, _, _, _, _, _ | _, _, .tyCtor _, _, h, _, _, _, _, _
  | _, _, .valCtor _, _, h, _, _, _, _, _ | _, _, .univ, _, h, _, _, _, _, _ | _, _, .level, _, h, _, _, _, _, _
  | _, _, .predates .., _, h, _, _, _, _, _ | _, _, .subterm .., _, h, _, _, _, _, _ | _, _, .fn .., _, h, _, _, _, _, _
  | _, _, .mtbl .., _, h, _, _, _, _, _ | _, _, .lvl _, _, h, _, _, _, _, _ | _, _, .tok, _, h, _, _, _, _, _
  | _, _, .clo .., _, h, _, _, _, _, _ | _, _, .nat _, _, h, _, _, _, _, _ | _, _, .ptr _, _, h, _, _, _, _, _ => by
    simp [rt] at h

theorem rt_buildArgs_spine (hP : ProgOK P) {G : UCtx} {f fS fF : Nat → Tm} : ∀ {H : Heap}, H.WF →
    ∀ args sig s (md : Ent → Bool) A, rtArgs P G.Γ args sig = true → G.argsUses P md args s = some A →
    s.kinds = sig.kinds → (∀ e : Ent, e.u = true → md e = true) →
    (∀ i ∈ rtReadsArgs P G.Γ args sig, MDec P H (f i) (fS i)) → HeadsOK P G.Γ fS fF (rtHeadsArgs P G.Γ args sig) →
    ∀ k v, k < (P.buildArgs H f args).2.toList.length → sig.ers.getD k true = false → sig.uAt k = true →
    (args.subst fF).toList[k]? = some v → ∀ b,
    Spine P (P.buildArgs H f args).1 ((P.buildArgs H f args).2.toList.getD k .nil)
      ((P.subUArgs fS args).toList.getD k .nil) v b →
    H.next ≤ b ∨ ∃ i ∈ rtReadsArgs P G.Γ args sig, A.lookup i = some true ∧ Spine P H (f i) (fS i) (fF i) b
  | H, hW, .cons a as, .bind e T r, s, md, A, h, hu, hks, hmd, hr, hh, k, v, hk, hke, hku, hv, b, hs => by
    cases s with
    | bind e' T' r' =>
      simp only [Tm.kinds, List.cons.injEq] at hks
      obtain ⟨rfl, hks⟩ := hks
      simp only [rtArgs, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨e1, w1⟩ := build_ext (P := P) hW f a
      have hr2 : ∀ i ∈ rtReadsArgs P G.Γ as r, MDec P (P.build H f a).1 (f i) (fS i) :=
        fun i hi => (hr i (by simp [rtReadsArgs, hi])).mono e1
      have hh2 : HeadsOK P G.Γ fS fF (rtHeadsArgs P G.Γ as r) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hi])
      obtain ⟨e2, w2, -⟩ := rt_buildArgs w1 as r h.2 hr2 hh2
      have hsplit : ∃ A1 B, (e'.er = false → G.termUses P (md e') a = some A1) ∧ G.argsUses P md as r' = some B ∧
          Uses.seq A1 B = some A := by
        simp only [UCtx.argsUses] at hu
        split at hu
        · obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hu
          obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
          exact ⟨A1, B, fun h => by simp_all, hB, h3⟩
        · obtain ⟨A1, h1, h2⟩ := Option.bind_eq_some_iff.mp hu
          obtain ⟨B, hB, h3⟩ := Option.bind_eq_some_iff.mp h2
          exact ⟨A1, B, fun _ => h1, hB, h3⟩
      obtain ⟨A1, B, h1, hB, h3⟩ := hsplit
      simp only [Prog.buildArgs, Prog.subUArgs, Tm.toList, Tm.ers, Tm.subst] at hs hk hke hv
      cases k with
      | zero =>
        simp only [List.getD_cons_zero] at hs hke
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv
        have hku' : e'.u = true := hku
        have hrt : rt P G.Γ a = true := by simpa [hke] using h.1
        have hra : ∀ i ∈ rtReads P G.Γ a, MDec P H (f i) (fS i) := fun i hi => hr i (by simp [rtReadsArgs, hke, hi])
        have hha : HeadsOK P G.Γ fS fF (rtHeads P G.Γ a) := fun i sg hi => hh i sg (by simp [rtHeadsArgs, hke, hi])
        have hma := (rt_build hW a hrt hra hha).2.2
        have h1 := h1 hke; rw [hmd e' hku'] at h1
        rcases rt_build_spine hP hW a A1 hrt h1 hra hha b (Spine.bwd (e2.agree hma).spine hs) with hb | ⟨i, hi, hl, hsi⟩
        · exact .inl hb
        · exact .inr ⟨i, by simp [rtReadsArgs, hke, hi], Uses.seq_true h3 (.inl hl), hsi⟩
      | succ k =>
        simp only [List.getD_cons_succ, List.length_cons, List.getElem?_cons_succ] at hs hke hk hv
        rcases rt_buildArgs_spine hP w1 as r r' md B h.2 hB hks hmd hr2 hh2 k v (by omega) hke hku hv b hs with
          hb | ⟨i, hi, hl, hsi⟩
        · exact .inl (Nat.le_trans e1.1 hb)
        · have hmi := hr i (by simp [rtReadsArgs, hi])
          exact .inr ⟨i, by simp [rtReadsArgs, hi], Uses.seq_true h3 (.inr hl), Spine.bwd (e1.agree hmi).spine hsi⟩
    | _ => simp [Tm.kinds] at hks
  | H, hW, .nil, _, _, _, _, _, _, _, _, _, _, k, _, hk, _, _, _, _, _ => by
    simp [Prog.buildArgs, Tm.subst, Tm.toList] at hk
  | _, _, .cons .., .nil, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .fv _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .bv _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .cons .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .app .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .tyc .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .vc .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .tyCtor _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .valCtor _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .univ, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .level, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .predates .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .subterm .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .fn .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .mtbl .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .lvl _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .tok, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .clo .., _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .nat _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .cons .., .ptr _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .fv _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .bv _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .bind .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .app .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .tyc .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .vc .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .tyCtor _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .valCtor _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .univ, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .level, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .predates .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .subterm .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .fn .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .mtbl .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .lvl _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .tok, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .clo .., _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .nat _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, _, .ptr _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [rtArgs] at h
end

structure GOK (P : Prog) (G : UCtx) (pd : Pend) (H : Heap) (ρM ρS ρ : List Tm) (Res : Nat → Prop) : Prop where
  cell : G.cellOk = true → (∃ y, pd = some (.alloc, y)) ∨
    ∃ m x, pd = some (m, .fv x) ∧ (m = .cellOf ∨ m = .write true ∨ m = .reuse true) ∧ ∀ a, Tm.env ρM x = .ptr a → Res a
  uscr : ∀ x, G.uscr = some (.fv x) → ∀ a, Tm.env ρM x = .ptr a → Res a
  rebind : ∀ x, G.rebind = some (.fv x) → (∀ b, Spine P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) b → Res b) ∧
    WO P H (Tm.env ρM x) (Tm.env ρS x) (Tm.env ρ x) ∧ MDec P H (Tm.env ρM x) (Tm.env ρS x)

end Minimal
