import Minimal.Lemmas

set_option linter.unusedVariables false

namespace Minimal

abbrev Res (α : Type) := Except String α

def need (b : Prop) [Decidable b] (msg : String) : Res (PLift b) :=
  if h : b then .ok ⟨h⟩ else .error msg

def retOf : Tm → Option Tm
  | .bind (.ty _ _) R .nil => some R
  | .bind _ _ r => retOf r
  | _ => none

structure ProgOK (P : Prog) : Prop where
  params : ∀ (d : Nat) (D : Adt), P.adts[d]? = some D → TeleOK P {tys := []} D.params ∧ D.params.static 0 0
  ctors : ∀ (d : Nat) (D : Adt) (c : Nat) sig, P.adts[d]? = some D → D.ctors[c]? = some sig →
    TeleOK P {tys := []} sig ∧ sig.static 0 0 ∧ ∃ idx, retOf sig = some (.app (.tyc d) idx)

def Checked (P : Prog) (rets : Tm) : Prop :=
  ProgOK P ∧ CoreTy P P.groups.length {tys := []} P.main rets ∧ rets.static 0 0

variable (P : Prog)

mutual
def checkTm' (Γ : Ctx) (rules : Bool) : (t : Tm) → Res {T // TmTy P Γ t T}
  | .fv i => match h : Γ.tys[i]?, rules with
    | some .nil, true => match hs : Γ.σ i with
      | some t => do let ⟨T, ht⟩ ← checkTm' Γ false t; .ok ⟨T, .fvIs h hs ht⟩
      | none => .error s!"entry {i} has no type"
    | some T, _ => .ok ⟨T, .fv h⟩
    | none, _ => .error s!"unbound entry {i}"
  | .univ => .ok ⟨.univ, .univ⟩
  | .level => .ok ⟨.univ, .level⟩
  | .tyc d => match h : P.adts[d]? with
    | some D => .ok ⟨_, .tyc h⟩
    | none => .error "unknown type constructor"
  | .vc d c => match h : P.ctor d c with
    | some sig => .ok ⟨_, .vc h⟩
    | none => .error "unknown constructor"
  | .app hd args => do
    let ⟨H, hh⟩ ← checkTm' Γ rules hd
    match hH : Γ.canon H with
    | .tyCtor ps => do
      let ⟨out, ha⟩ ← checkArgs' Γ rules args ps
      let ⟨ho⟩ ← need (out = .nil) "type constructor applied to the wrong number of arguments"
      .ok ⟨.univ, .tyApp hh hH (ho ▸ ha)⟩
    | .valCtor sig => do
      let ⟨out, ha⟩ ← checkArgs' Γ rules args sig
      match out, ha with
      | .bind (.ty _ _) T .nil, ha => .ok ⟨T, .vcApp hh hH ha⟩
      | _, _ => .error "constructor applied to the wrong number of arguments"
    | _ => .error "applied a head that is not a constructor"
  | .tyCtor ps => do
    let ⟨ht⟩ ← checkTele' Γ rules ps
    let ⟨hs⟩ ← need ((Tm.tyCtor ps).static Γ.n 0) "TyCtor: not well scoped"
    .ok ⟨.univ, .tyCtor ht hs⟩
  | .valCtor sig => do
    let ⟨ht⟩ ← checkTele' Γ rules sig
    let ⟨hs⟩ ← need ((Tm.valCtor sig).static Γ.n 0) "ValCtor: not well scoped"
    let ⟨hr⟩ ← need (sig.valRet 0) "ValCtor: the return is not an application of a type constructor from outside"
    .ok ⟨.univ, .valCtor ht hs hr⟩
  | .predates A x L => do
    let ⟨U, hA⟩ ← checkTm' Γ rules A
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "Predates: not a type"
    let ⟨X, hx⟩ ← checkTm' Γ rules x
    let ⟨hX⟩ ← need (Γ.canon X = Γ.canon A) "Predates: term not of the type"
    let ⟨K, hL⟩ ← checkTm' Γ rules L
    let ⟨hK⟩ ← need (Γ.canon K = .level) "Predates: not a level"
    .ok ⟨.univ, .predates hA hU hx hX hL hK⟩
  | .subterm A a B b => do
    let ⟨U, hA⟩ ← checkTm' Γ rules A
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "Subterm: not a type"
    let ⟨A', ha⟩ ← checkTm' Γ rules a
    let ⟨hA'⟩ ← need (Γ.canon A' = Γ.canon A) "Subterm: term not of the type"
    let ⟨V, hB⟩ ← checkTm' Γ rules B
    let ⟨hV⟩ ← need (Γ.canon V = .univ) "Subterm: not a type"
    let ⟨B', hb⟩ ← checkTm' Γ rules b
    let ⟨hB'⟩ ← need (Γ.canon B' = Γ.canon B) "Subterm: term not of the type"
    .ok ⟨.univ, .subterm hA hU ha hA' hB hV hb hB'⟩
  | .fn l np t => do
    let ⟨K, hl⟩ ← checkTm' Γ rules l
    let ⟨hK⟩ ← need (Γ.canon K = .level) "Fn: not a level"
    let ⟨ht⟩ ← checkTele' Γ rules t
    let ⟨hn⟩ ← need (np ≤ t.len) "Fn: more parameters than entries"
    let ⟨hs⟩ ← need ((Tm.fn l np t).static Γ.n 0) "Fn: not well scoped"
    .ok ⟨.univ, .fn hl hK ht hn hs⟩
  | _ => .error "not a term of the type grammar"
termination_by t => (rules.toNat, t.size)
decreasing_by all_goals (try simp only [Prod.lex_def]); all_goals (simp [Tm.size]; try omega)

def checkArgs' (Γ : Ctx) (rules : Bool) : (args tele : Tm) → Res {out // ArgsTy P Γ args tele out}
  | .nil, t => .ok ⟨t, .nil⟩
  | .cons a as, .bind (.ty _ _) A r => do
    let ⟨T, ha⟩ ← checkTm' Γ rules a
    let ⟨h⟩ ← need (Γ.canon T = Γ.canon A) "argument of the wrong type"
    let ⟨out, hr⟩ ← checkArgs' Γ rules as (r.inst a 0)
    .ok ⟨out, .cons ha h hr⟩
  | .cons a as, .bind (.is _) e r => do
    let ⟨_, ha⟩ ← checkTm' Γ rules a
    let ⟨h⟩ ← need (Γ.canon a = Γ.canon e) "argument not the term its is entry names"
    let ⟨out, hr⟩ ← checkArgs' Γ rules as (r.inst a 0)
    .ok ⟨out, .isCons ha h hr⟩
  | _, _ => .error "too many arguments"
termination_by args => (rules.toNat, args.size)
decreasing_by all_goals (try simp only [Prod.lex_def]); all_goals (simp [Tm.size]; try omega)

def checkTele' (Γ : Ctx) (rules : Bool) : (t : Tm) → Res (PLift (TeleOK P Γ t))
  | .nil => .ok ⟨.nil⟩
  | .bind (.ty _ _) A r => do
    let ⟨U, hA⟩ ← checkTm' Γ rules A
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "telescope entry not a type"
    let ⟨hr⟩ ← checkTele' (Γ.push A) rules (r.inst (.fv Γ.n) 0)
    .ok ⟨.cons hA hU hr⟩
  | .bind (.is _) e r => do
    let ⟨_, he⟩ ← checkTm' Γ rules e
    let ⟨hr⟩ ← checkTele' (Γ.pushEnt (.is false) e) rules (r.inst (.fv Γ.n) 0)
    .ok ⟨.isCons he hr⟩
  | _ => .error "not a telescope"
termination_by t => (rules.toNat, t.size)
decreasing_by all_goals (try simp only [Prod.lex_def]); all_goals (simp [Tm.size, Tm.size_inst_fv]; try omega)
end

def checkTm (Γ : Ctx) := checkTm' P Γ true
def checkArgs (Γ : Ctx) := checkArgs' P Γ true
def checkTele (Γ : Ctx) := checkTele' P Γ true

instance (l : List Tm) (s : List Nat) (Γ : Ctx) (i : Nat) :
    Decidable (∀ j < i, ∀ a' s', l[j]? = some a' → s[j]? = some s' → Γ.canon a' = Γ.canon (.fv s')) :=
  decidable_of_iff (∀ j ∈ List.range i, ∀ a' ∈ l[j]?, ∀ s' ∈ s[j]?, Γ.canon a' = Γ.canon (.fv s'))
    (by simp only [List.mem_range, Option.mem_def]
        exact ⟨fun h j hj a' s' ha hs => h j hj a' ha s' hs, fun h j hj a' ha s' hs => h j hj a' s' ha hs⟩)

def checkDec (Γ : Ctx) (l t args : Tm) : (dec : Dec) → Res (PLift (DecOK P Γ dec l t args))
  | .none => match h : Γ.cur with
    | none => .ok ⟨.top h⟩
    | some c =>
      if hl : Γ.canon l = Γ.canon (.fv c) then
        let ms := markedArgs t args
        match ((List.range ms.length).find? fun j =>
            Γ.canon ms[j]! != Γ.canon (.fv (Γ.subs.getD j 0))) with
        | none => .error "a same-level call whose subterm arguments are all unchanged"
        | some i =>
          match ha : ms[i]?, hs : Γ.subs[i]? with
          | some a, some s => do
            let ⟨hpre⟩ ← need (∀ j < i, ∀ a' s', ms[j]? = some a' → Γ.subs[j]? = some s' →
                Γ.canon a' = Γ.canon (.fv s')) "unreachable"
            let ⟨hst⟩ ← need ((Γ.canon a).strictSub (Γ.canon (.fv s))) "subterm: not a strict subterm"
            .ok ⟨.autoSub h hl ha hs hpre hst⟩
          | _, _ => .error "subterm: no such subterm argument"
      else match hx : Γ.canon l with
        | .fv x => do
          let ⟨h1⟩ ← need (x < c) "predates: the callee's level was not made before the current one"
          let ⟨h2⟩ ← need (c ∈ Γ.mints) "predates: the current level is not made by def-lvl"
          .ok ⟨.autoPred h hx h1 h2⟩
        | _ => .error "predates: the callee's level is not an entry"
  | .predates p => match h : Γ.cur with
    | some c => do
      let ⟨Pt, hp⟩ ← checkTm P Γ p
      match hP : Γ.canon Pt with
      | .predates _ x L => do
        let ⟨hx⟩ ← need (Γ.canon x = Γ.canon l) "predates: not about the callee's level"
        let ⟨hL⟩ ← need (Γ.canon L = Γ.canon (.fv c)) "predates: not to the current level"
        .ok ⟨.lower h hp hP hx hL⟩
      | _ => .error "predates: not a Predates proof"
    | none => .error "a decrease annotation at the top level"
  | .subterm pos p => match h : Γ.cur with
    | some c => do
      let ⟨hl⟩ ← need (Γ.canon l = Γ.canon (.fv c)) "subterm: callee not at the current level"
      match hi : markedIndex t pos 0 with
      | none => .error "subterm: the argument is not for a subterm parameter"
      | some i =>
      match ha : (markedArgs t args)[i]?, hs : Γ.subs[i]? with
      | some a, some s => do
        let ⟨hpre⟩ ← need (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
            Γ.canon a' = Γ.canon (.fv s')) "subterm: an earlier subterm argument differs"
        let ⟨Pt, hp⟩ ← checkTm P Γ p
        match hP : Γ.canon Pt with
        | .subterm _ a0 _ b0 => do
          let ⟨h0⟩ ← need (Γ.canon a0 = Γ.canon a) "subterm: proof not about the argument"
          let ⟨h1⟩ ← need (Γ.canon b0 = Γ.canon (.fv s)) "subterm: proof not about the parameter"
          .ok ⟨.same h hl hi ha hs hpre hp hP h0 h1⟩
        | _ => .error "subterm: not a Subterm proof"
      | _, _ => .error "subterm: no such subterm argument"
    | none => .error "a decrease annotation at the top level"

def checkPrim (Γ : Ctx) : (p : Prim) → Res {T // PrimTy P Γ p T}
  | .tm t => do let ⟨T, h⟩ ← checkTm P Γ t; .ok ⟨T, .tm h⟩
  | .proveSubterm a b => do
    let ⟨A, ha⟩ ← checkTm P Γ a
    let ⟨B, hb⟩ ← checkTm P Γ b
    let ⟨h⟩ ← need ((Γ.canon a).strictSub (Γ.canon b)) "prove-subterm: not a strict subterm"
    .ok ⟨_, .proveSubterm ha hb h⟩
  | .provePredates x L => do
    let ⟨h1⟩ ← need (x < L) "prove-predates: not introduced before the level"
    let ⟨h2⟩ ← need (L ∈ Γ.mints) "prove-predates: not a level made by def-lvl"
    match h : Γ.tys[x]? with
    | some X => .ok ⟨_, .provePredates h1 h2 h⟩
    | none => .error "prove-predates: unbound"
  | .predatesTrans p q => do
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    let ⟨Qt, hq⟩ ← checkTm P Γ q
    match h1 : Γ.canon Pt, h2 : Γ.canon Qt with
    | .predates A a l1, .predates C l1' l2 => do
      let ⟨e⟩ ← need (l1' = l1) "predates-trans: levels differ"
      .ok ⟨_, .predatesTrans hp hq h1 (e ▸ h2)⟩
    | _, _ => .error "predates-trans: not Predates proofs"
  | .subtermTrans p q => do
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    let ⟨Qt, hq⟩ ← checkTm P Γ q
    match h1 : Γ.canon Pt, h2 : Γ.canon Qt with
    | .subterm A a B b, .subterm B' b' C c => do
      let ⟨e⟩ ← need (B' = B ∧ b' = b) "subterm-trans: middle terms differ"
      .ok ⟨_, .subtermTrans hp hq h1 (e.1 ▸ e.2 ▸ h2)⟩
    | _, _ => .error "subterm-trans: not Subterm proofs"
  | .predatesSubterm p q => do
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    let ⟨Qt, hq⟩ ← checkTm P Γ q
    match h1 : Γ.canon Pt, h2 : Γ.canon Qt with
    | .predates A a l, .subterm B b A' a' => do
      let ⟨e⟩ ← need (A' = A ∧ a' = a) "predates-subterm: terms differ"
      .ok ⟨_, .predatesSubterm hp hq h1 (e.1 ▸ e.2 ▸ h2)⟩
    | _, _ => .error "predates-subterm: not the right proofs"

def synthRets (Γ : Ctx) (n : Nat) : (ts : Tm) → Res {R // ArgsTy P Γ ts R .nil ∧ R.static n 0}
  | .nil => .ok ⟨.nil, .nil, rfl⟩
  | .cons a as => do
    let ⟨T, ha⟩ ← checkTm P Γ a
    let ⟨R, hr, hR⟩ ← synthRets Γ n as
    have hi : R.inst a 0 = R := Tm.inst_static n R 0 0 hR (Nat.le_refl 0)
    have hR1 := Tm.static_mono (Nat.le_refl n) R (Nat.zero_le 1) hR
    if hs : (Γ.canon T).static 0 0 then
      have hc : Γ.canon (Γ.canon T) = Γ.canon T := Tm.subst_static0 _ _ _ hs
      .ok ⟨.bind (.ty false false) (Γ.canon T) R, .cons ha hc.symm (by rw [hi]; exact hr),
        by simp [Tm.static, Tm.static_mono (Nat.zero_le n) _ (Nat.le_refl 0) hs, hR1]⟩
    else if hs : T.static n 0 then
      .ok ⟨.bind (.ty false false) T R, .cons ha rfl (by rw [hi]; exact hr), by simp [Tm.static, hs, hR1]⟩
    else .error "a result's type mentions entries it may not"
  | _ => .error "not a list of results"

mutual
def checkCore (b : Nat) (Γ : Ctx) : (c : Core) → (rets : Tm ⊕ Nat) →
    Res {R // CoreTy P b Γ c R ∧ (∀ r, rets = .inl r → R = r) ∧ ∀ n, rets = .inr n → R.static n 0}
  | .ret ts, .inl r => do
    let ⟨out, h⟩ ← checkArgs P Γ ts r
    let ⟨ho⟩ ← need (out = .nil) "wrong number of results"
    let ⟨hr⟩ ← need (Γ.ok (rtArgs P Γ ts r)) "a non-erased result mentions an erased entry or a phantom constructor"
    .ok ⟨r, .ret (ho ▸ h) hr, fun _ e => Sum.inl.inj e, fun _ e => (by cases e)⟩
  | .ret ts, .inr n => do
    let ⟨R, h, hs⟩ ← synthRets P Γ n ts
    let ⟨hr⟩ ← need (Γ.ok (rtArgs P Γ ts R)) "a non-erased result mentions an erased entry or a phantom constructor"
    .ok ⟨R, .ret h hr, fun _ e => (by cases e), fun _ e => by cases e; exact hs⟩
  | .absurd body, rets => do
    let ⟨R, hb, _, hs⟩ ← checkCore b { Γ with ghost := true } body (.inr Γ.n)
    match hR : R with
    | .bind (.ty _ _) (.app (.tyc d) idx) .nil => match hD : P.adts[d]? with
      | some D => do
        let ⟨he⟩ ← need (D.ctors = []) "absurd: the body's value is of a type with constructors"
        have hst : (Tm.app (.tyc d) idx).static Γ.n 0 := by
          have := hs Γ.n rfl; rw [hR] at this; simp only [Tm.static, Bool.and_eq_true] at this ⊢; exact this.1
        let R' := match rets with | .inl r => r | .inr _ => .nil
        .ok ⟨R', .absurd (hR ▸ hb) hst hD he, fun r e => by simp [R', e], fun n e => by simp [R', e, Tm.static]⟩
      | none => .error "unknown type"
    | _ => .error "absurd: the body does not end in one value of a data type"
  | .dead, _ => .error "a refuted branch outside a match"
  | .call f dec args er ms rest, rets => do
    let ⟨Ft, hf⟩ ← checkTm P Γ f
    match hF : Γ.canon Ft with
    | .fn l np t => do
      let ⟨ht⟩ ← need (t.isTele) "not a telescope"
      let ⟨outs, ha⟩ ← checkArgs P Γ args t
      let ⟨hn⟩ ← need (args.len = np) "wrong number of arguments"
      let ⟨hd⟩ ← checkDec P Γ l t args dec
      let ⟨ho⟩ ← need (outs.len = ms.length) "wrong number of results bound"
      let ⟨hm⟩ ← need (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outs))
        "a non-erased call mentions an erased entry or a phantom constructor, or binds an erased result at many"
      let ⟨R, hr, e⟩ ← checkCore b (Γ.pushTele outs (some (ms.map (er || ·)))) rest rets
      .ok ⟨R, .call hf hF ht ha hn hd ho hm hr, e⟩
    | _ => .error "not a function"
  | .mtch s R0 brs els er rest, rets => do
    let ⟨St, hs⟩ ← checkTm P Γ s
    match hS : Γ.canon St with
    | .app (.tyc d) idx => match hD : P.adts[d]? with
      | some D => do
        let ⟨hl⟩ ← need (∀ e ∈ brs, e.1 = d ∧ e.2.1 < D.ctors.length) "a branch names a constructor of another type"
        let ⟨hR⟩ ← checkTele P Γ R0
        let ⟨hRs⟩ ← need (R0.static Γ.n 0) "match: return telescope not well scoped"
        let ⟨hRt⟩ ← need (R0.isTele) "match: not a telescope"
        let ⟨hm⟩ ← need (er || Γ.ok (rt P Γ s)) "a non-erased match on an erased scrutinee"
        let Γg := { Γ with ghost := Γ.ghost || er }
        let ⟨hb⟩ ← checkBranches b Γ er s d idx R0 brs els.isSome D.ctors 0
        let ⟨he⟩ ← (match els with
          | some eb => do
            let ⟨_⟩ ← need (D.ctors.zipIdx.any fun (sig, c) =>
                (lookupBr brs c).isNone && (Γ.branch s d c idx sig).2 matches .ok _ | .unknown)
              "else: it stands for no constructor"
            let ⟨_, h, e⟩ ← checkCore b Γg eb (.inl R0)
            .ok ⟨fun _ h' => by cases h'; exact e.1 R0 rfl ▸ h⟩
          | none => .ok ⟨fun _ h' => nomatch h'⟩ : Res (PLift (∀ e, els = some e → CoreTy P b Γg e R0)))
        let ⟨R, hr, e⟩ ← checkCore b (Γ.pushTele R0 (if er then some (List.replicate R0.len true) else none)) rest rets
        .ok ⟨R, .mtch hs hS hD hl hR hRs hRt hm (fun c sig h1 => by simpa using hb c sig h1) he hr, e⟩
      | none => .error "unknown type"
    | _ => .error "scrutinee not of a data type"
  | .prim p er rest, rets => do
    let ⟨T, hp⟩ ← checkPrim P Γ p
    let ⟨hm⟩ ← need (er || Γ.ok (p.rt P Γ)) "a non-erased let binder of a term mentioning an erased entry or a phantom constructor"
    let ⟨R, hr, e⟩ ← checkCore b (Γ.pushPrim T er p) rest rets
    .ok ⟨R, .prim hp hm hr, e⟩
  | .defLvl rest, rets => do
    let ⟨R, hr, e⟩ ← checkCore b Γ.pushMint rest rets
    .ok ⟨R, .defLvl hr, e⟩
  | .defFns gid rest, rets => do
    let ⟨hg⟩ ← need (gid < b) "group out of order"
    match hG : P.groups[gid]? with
    | some G => do
      let ⟨hok⟩ ← checkGroup gid Γ G
      let ⟨R, hr, e⟩ ← checkCore b (Γ.pushFns G) rest rets
      .ok ⟨R, .defFns hg hG hok hr, e⟩
    | none => .error "unknown group"
  | .chk .rt a _ rest, rets => do
    let ⟨h⟩ ← need (Γ.ok (rt P Γ a)) "a non-erased let binder of an erased entry"
    let ⟨R, hr, eq⟩ ← checkCore b Γ rest rets
    .ok ⟨R, .chkRt h hr, eq⟩
  | .chk .is a e rest, rets => do
    let ⟨_, he⟩ ← checkTm P Γ e
    let ⟨h⟩ ← need (Γ.canon a = Γ.canon e) "let: the binder is not the term its is clause names"
    let ⟨R, hr, eq⟩ ← checkCore b Γ rest rets
    .ok ⟨R, .chkIs he h hr, eq⟩
  | .chk .ty a T rest, rets => do
    let ⟨A, ha⟩ ← checkTm P Γ a
    let ⟨U, hT⟩ ← checkTm P Γ T
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "let: the binder's annotation is not a type"
    let ⟨h⟩ ← need (Γ.canon A = Γ.canon T) "let: the binder is not of the type written"
    let ⟨R, hr, eq⟩ ← checkCore b Γ rest rets
    .ok ⟨R, .chkTy ha hT hU h hr, eq⟩
termination_by c => (b, 1, sizeOf c, 0)
decreasing_by all_goals (simp only [Prod.lex_def]; simp; try omega)

def checkBranches (b : Nat) (Γ : Ctx) (er : Bool) (s : Tm) (d : Nat) (idx R0 : Tm) (brs : List (Nat × Nat × Core))
    (els : Bool) : (ctors : List Tm) → (base : Nat) →
    Res (PLift (∀ (c : Nat) sig, ctors[c]? = some sig →
      BranchOK P b { Γ with ghost := Γ.ghost || er || P.phantom d (base + c) } s d idx (base + c) sig R0
        (lookupBr brs (base + c)) els))
  | [], _ => .ok ⟨fun _ _ h => by simp at h⟩
  | sig :: cs, base => do
    let Γc : Ctx := { Γ with ghost := Γ.ghost || er || P.phantom d base }
    let ⟨hh⟩ ← (match hb : Γc.branch s d base idx sig, hl : lookupBr brs base with
      | (_, .contra), some .dead => .ok ⟨BranchOK.refuted (by rw [hb])⟩
      | (_, _), some .dead => .error "an absurd branch names a constructor that is not refuted"
      | (Γf, .ok σ), some body => do
        let ⟨_, hr, e⟩ ← checkCore b { Γf with σ := σ } body (.inl R0)
        .ok ⟨BranchOK.live hb (e.1 R0 rfl ▸ hr)⟩
      | (_, .contra), none => .ok ⟨BranchOK.dead (by rw [hb])⟩
      | (_, .contra), some _ => .error "a listed branch is refuted"
      | (_, .unknown), some _ => .error "cannot decide whether the branch is refuted"
      | (_, _), none => if h : els then .ok ⟨h ▸ BranchOK.covered⟩
          else .error "a branch that is not refuted is missing" :
      Res (PLift (BranchOK P b Γc s d idx base sig R0 (lookupBr brs base) els)))
    let ⟨ht⟩ ← checkBranches b Γ er s d idx R0 brs els cs (base + 1)
    .ok ⟨fun
      | 0, _, h1 => by simp at h1; subst h1; simpa using hh
      | c + 1, sig, h1 => by
        have := ht c sig (by simpa using h1)
        rwa [show base + 1 + c = base + (c + 1) by omega] at this⟩
termination_by ctors => (b, 1, sizeOf brs, ctors.length)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · have := sizeOf_lookupBr hl; simp; omega
  · simp

def checkGroup (gid : Nat) (Γ : Ctx) (G : Group) : Res (PLift (GroupOK P gid Γ G)) := do
  match hK : Γ.tys[G.lvl]? with
  | some K => do
    let ⟨hl⟩ ← need (Γ.canon K = .level) "def-fns: not a level"
    let ⟨hf⟩ ← checkFns gid Γ G G.fns 0
    let ⟨he⟩ ← need (∀ i < Γ.n, Γ.er i = G.ers.getD i true) "def-fns: the elaborator's erasure disagrees"
    let ⟨hg⟩ ← need (Γ.ghost = G.ghost) "def-fns: the elaborator's erasure disagrees"
    .ok ⟨.mk hK hl (fun j F h => (hf j F (by simpa using h)).1)
      (fun j F h => (hf j F (by simpa using h)).2.1) (fun j F h => (hf j F (by simpa using h)).2.2) he hg⟩
  | none => .error "def-fns: unbound level"
termination_by (gid + 1, 0, sizeOf G.fns + 1, 0)
decreasing_by all_goals (simp only [Prod.lex_def]; simp; try omega)

def checkFns (gid : Nat) (Γ : Ctx) (G : Group) : (fns : List FnDef) → (base : Nat) →
    Res (PLift (∀ (j : Nat) (F : FnDef), fns[j]? = some F →
      TmTy P Γ (F.type G) .univ ∧ (marks F.tele F.np).count true ≤ P.k ∧
      CoreTy P gid (Γ.body G F).1 F.body (Γ.body G F).2))
  | [], _ => .ok ⟨fun _ _ h => nomatch h⟩
  | F :: fs, base => do
    let ⟨T, ht⟩ ← checkTm P Γ (F.type G)
    let ⟨hT⟩ ← need (T = .univ) "def-fns: not a function type"
    let ⟨hk⟩ ← need ((marks F.tele F.np).count true ≤ P.k) "def-fns: too many subterm parameters"
    let ⟨_, hb, e⟩ ← checkCore gid (Γ.body G F).1 F.body (.inl (Γ.body G F).2)
    let ⟨hr⟩ ← checkFns gid Γ G fs (base + 1)
    .ok ⟨fun
      | 0, F', h => by simp at h; subst h; exact ⟨hT ▸ ht, hk, e.1 _ rfl ▸ hb⟩
      | j + 1, F', h => hr j F' (by simpa using h)⟩
termination_by fns => (gid + 1, 0, sizeOf fns, 0)
decreasing_by all_goals (simp only [Prod.lex_def]; simp; try omega)
end

def allIdx {α : Type} {Q : Nat → α → Prop} (f : (i : Nat) → (x : α) → Res (PLift (Q i x))) :
    (l : List α) → (base : Nat) → Res (PLift (∀ i x, l[i]? = some x → Q (base + i) x))
  | [], _ => .ok ⟨fun _ _ h => by simp at h⟩
  | x :: xs, base => do
    let ⟨h⟩ ← f base x
    let ⟨hs⟩ ← allIdx f xs (base + 1)
    .ok ⟨fun
      | 0, _, e => by simp at e; subst e; simpa using h
      | i + 1, y, e => by
        have := hs i y (by simpa using e)
        rwa [show base + 1 + i = base + (i + 1) by omega] at this⟩

def checkCtor (d : Nat) (_ : Nat) (sig : Tm) :
    Res (PLift (TeleOK P {tys := []} sig ∧ sig.static 0 0 ∧ ∃ idx, retOf sig = some (.app (.tyc d) idx))) := do
  let ⟨ht⟩ ← checkTele P {tys := []} sig
  let ⟨hs⟩ ← need (sig.static 0 0) "def-adts: a constructor's signature is not closed"
  match h : retOf sig with
  | some (.app (.tyc d') idx) => do
    let ⟨e⟩ ← need (d' = d) "def-adts: a constructor returns another type"
    .ok ⟨ht, hs, idx, e ▸ h⟩
  | _ => .error "def-adts: a constructor does not return its type"

def checkProg : Res {R // Checked P R} := do
  let ⟨ha⟩ ← allIdx (Q := fun d (D : Adt) => (TeleOK P {tys := []} D.params ∧ D.params.static 0 0) ∧ ∀ (c : Nat) sig,
      D.ctors[c]? = some sig → TeleOK P {tys := []} sig ∧ sig.static 0 0 ∧ ∃ idx, retOf sig = some (.app (.tyc d) idx))
    (fun d D => do
      let ⟨hp⟩ ← checkTele P {tys := []} D.params
      let ⟨hps⟩ ← need (D.params.static 0 0) "def-adts: parameters not closed"
      let ⟨hc⟩ ← allIdx (checkCtor P d) D.ctors 0
      .ok ⟨⟨hp, hps⟩, fun c sig h => by simpa using hc c sig h⟩) P.adts 0
  let ⟨R, h, _, hs⟩ ← checkCore P P.groups.length {tys := []} P.main (.inr 0)
  have hs := hs 0 rfl
  .ok ⟨R, ⟨fun d D e => by have := ha d D e; simp only [Nat.zero_add] at this; exact this.1,
    fun d D c sig e1 e2 => by have := ha d D e1; simp only [Nat.zero_add] at this; exact this.2 c sig e2⟩, h, hs⟩

end Minimal
