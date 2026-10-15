import Minimal.Lemmas

set_option linter.unusedVariables false

namespace Minimal

abbrev Res (α : Type) := Except String α

def need (b : Prop) [Decidable b] (msg : String) : Res (PLift b) :=
  if h : b then .ok ⟨h⟩ else .error msg

def retOf : Tm → Option Tm
  | .bind (.ty ..) R .nil => some R
  | .bind _ _ r => retOf r
  | _ => none

def liftBvs (m k : Nat) : Tm := .ofList ((List.range k).map fun j => .bv (m - 1 - j))

structure ProgOK (P : Prog) : Prop where
  params : ∀ (d : Nat) (D : Adt), P.adts[d]? = some D → TeleOK P {tys := #[]} D.params ∧ D.params.static 0 0
  ctors : ∀ (d : Nat) (D : Adt) (c : Nat) sig, P.adts[d]? = some D → D.ctors[c]? = some sig →
    TeleOK P {tys := #[]} sig ∧ sig.static 0 0 ∧ ∃ idx, retOf sig = some (.app (.tyc d (liftBvs (sig.len - 1) D.lifted)) idx)
  newtype : ∀ d c sig, P.isNt d = true → P.phantom d c = false → P.ctor d c = some sig → (sig.skip (P.lifted d)).ntField.isSome
  coer : ∀ (d : Nat) (D : Adt), P.adts[d]? = some D → D.coercible = true → D.ctors = []
  opq : ∀ (d : Nat) (D : Adt), P.adts[d]? = some D → D.opq = true → D.ctors = [] ∧ D.coercible = false
  placed : ∀ q, P.placedD = some q → ∃ D, P.adts[q]? = some D ∧ D.opq = true
  uer : ∀ (d c : Nat) sig, P.ctor d c = some sig → ∀ j, sig.uAt j = true → sig.ers.getD j true = false

def Checked (P : Prog) (rets : Tm) : Prop :=
  ProgOK P ∧ CoreTy P P.groups.length {tys := #[]} P.main rets ∧ rets.static 0 0

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
  | .tyc d ls => match h : P.adts[d]? with
    | some D => do
      let ⟨hl⟩ ← need (ls.len = D.lifted) "a type constructor with the wrong number of lifted arguments"
      let ⟨out, ha⟩ ← checkArgs' Γ rules ls D.params
      .ok ⟨_, .tyc h hl ha⟩
    | none => .error "unknown type constructor"
  | .vc d c ls => match h : P.ctor d c with
    | some sig => do
      let ⟨hl⟩ ← need (ls.len = P.lifted d) "a constructor with the wrong number of lifted arguments"
      let ⟨out, ha⟩ ← checkArgs' Γ rules ls sig
      .ok ⟨_, .vc h hl ha⟩
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
      | .bind (.ty ..) T .nil, ha => .ok ⟨T, .vcApp hh hH ha⟩
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
  | .fn l np t uf hm => do
    let ⟨K, hl⟩ ← checkTm' Γ rules l
    let ⟨hK⟩ ← need (Γ.canon K = .level) "Fn: not a level"
    let ⟨ht⟩ ← checkTele' Γ rules t
    let ⟨hn⟩ ← need (np ≤ t.len) "Fn: more parameters than entries"
    let ⟨hs⟩ ← need ((Tm.fn l np t uf hm).static Γ.n 0) "Fn: not well scoped"
    .ok ⟨.univ, .fn hl hK ht hn hs⟩
  | .mtbl u nt ex ph T cs => do
    let ⟨hs⟩ ← need ((Tm.mtbl u nt ex ph T cs).static Γ.n 0) "Matchable: not well scoped"
    .ok ⟨.univ, .mtbl hs⟩
  | _ => .error "not a term of the type grammar"
termination_by t => (rules.toNat, t.size)
decreasing_by all_goals (try simp only [Prod.lex_def]); all_goals (simp [Tm.size]; try omega)

def checkArgs' (Γ : Ctx) (rules : Bool) : (args tele : Tm) → Res {out // ArgsTy P Γ args tele out}
  | .nil, t => .ok ⟨t, .nil⟩
  | .cons a as, .bind (.ty ..) .nil r => do
    let ⟨_, ha⟩ ← checkTm' Γ rules a
    let ⟨out, hr⟩ ← checkArgs' Γ rules as (r.inst a 0)
    .ok ⟨out, .anyCons ha hr⟩
  | .cons a as, .bind (.ty ..) A r => do
    let ⟨T, ha⟩ ← checkTm' Γ rules a
    let ⟨h⟩ ← need (Γ.canon T = Γ.canon A) "argument of the wrong type"
    let ⟨out, hr⟩ ← checkArgs' Γ rules as (r.inst a 0)
    .ok ⟨out, .cons ha h hr⟩
  | .cons a as, .bind (.is ..) e r => do
    let ⟨_, ha⟩ ← checkTm' Γ rules a
    let ⟨h⟩ ← need (Γ.canon a = Γ.canon e) "argument not the term its is entry names"
    let ⟨out, hr⟩ ← checkArgs' Γ rules as (r.inst a 0)
    .ok ⟨out, .isCons ha h hr⟩
  | _, _ => .error "too many arguments"
termination_by args => (rules.toNat, args.size)
decreasing_by all_goals (try simp only [Prod.lex_def]); all_goals (simp [Tm.size]; try omega)

def checkTele' (Γ : Ctx) (rules : Bool) : (t : Tm) → Res (PLift (TeleOK P Γ t))
  | .nil => .ok ⟨.nil⟩
  | .bind (.ty ..) A r => do
    let ⟨U, hA⟩ ← checkTm' Γ rules A
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "telescope entry not a type"
    let ⟨hr⟩ ← checkTele' (Γ.push A) rules (r.inst (.fv Γ.n) 0)
    .ok ⟨.cons hA hU hr⟩
  | .bind (.is ..) e r => do
    let ⟨_, he⟩ ← checkTm' Γ rules e
    let ⟨hr⟩ ← checkTele' (Γ.pushEnt (.is false false false) e) rules (r.inst (.fv Γ.n) 0)
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
            .ok ⟨.autoSub h hl ha hs hpre hst (.inl rfl)⟩
          | _, _ => .error "subterm: no such subterm argument"
      else match hx : Γ.canon l with
        | .fv x => do
          let ⟨h1⟩ ← need (x < c) "predates: the callee's level was not made before the current one"
          let ⟨h2⟩ ← need (c ∈ Γ.mints) "predates: the current level is not made by def-lvl"
          .ok ⟨.autoPred h hx h1 h2 (.inl rfl)⟩
        | _ => .error "predates: the callee's level is not an entry"
  | .predates p => if hh : p = Tm.hole then
      match h : Γ.cur with
      | some c => match hx : Γ.canon l with
        | .fv x => do
          let ⟨h1⟩ ← need (x < c) "predates: the callee's level was not made before the current one"
          let ⟨h2⟩ ← need (c ∈ Γ.mints) "predates: the current level is not made by def-lvl"
          .ok ⟨.autoPred h hx h1 h2 (.inr (by rw [hh]))⟩
        | _ => .error "predates: the callee's level is not an entry"
      | none => .error "a decrease annotation at the top level"
    else match h : Γ.cur with
    | some c => do
      let ⟨Pt, hp⟩ ← checkTm P Γ p
      match hP : Γ.canon Pt with
      | .predates _ x L => do
        let ⟨hx⟩ ← need (Γ.canon x = Γ.canon l) "predates: not about the callee's level"
        let ⟨hL⟩ ← need (Γ.canon L = Γ.canon (.fv c)) "predates: not to the current level"
        let ⟨hs⟩ ← need (Γ.canon l ≠ Γ.canon (.fv c)) "a same-level call takes a (subterm p) annotation, not (predates p)"
        .ok ⟨.lower h hp hP hx hL hs⟩
      | _ => .error "predates: not a Predates proof"
    | none => .error "a decrease annotation at the top level"
  | .subterm pos p => if hh : p = Tm.hole then
      match h : Γ.cur with
      | some c => do
        let ⟨hl⟩ ← need (Γ.canon l = Γ.canon (.fv c)) "subterm: callee not at the current level"
        match hi : markedIndex t pos 0 with
        | none => .error "subterm: the argument is not for a subterm parameter"
        | some i =>
        match ha : (markedArgs t args)[i]?, hs : Γ.subs[i]? with
        | some a, some s => do
          let ⟨hpre⟩ ← need (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
              Γ.canon a' = Γ.canon (.fv s')) "subterm: an earlier subterm argument differs"
          let ⟨hst⟩ ← need ((Γ.canon a).strictSub (Γ.canon (.fv s))) "subterm: not a strict subterm"
          .ok ⟨.autoSub h hl ha hs hpre hst (.inr ⟨pos, by rw [hh], hi⟩)⟩
        | _, _ => .error "subterm: no such subterm argument"
      | none => .error "a decrease annotation at the top level"
    else match h : Γ.cur with
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

def coerAdt : Res {x : Nat × Adt // P.adts[x.1]? = some x.2 ∧ x.2.coercible = true} :=
  match h : P.adts.findIdx? (·.coercible) with
  | some d => match h2 : P.adts[d]? with
    | some D => if hc : D.coercible = true then .ok ⟨(d, D), h2, hc⟩ else .error "unreachable"
    | none => .error "unreachable"
  | none => .error "Coercible is not declared"

def deleAdt : Res {x : Nat × Adt // P.adts[x.1]? = some x.2 ∧ x.2.coercible = true} :=
  match h : P.adts.findIdx? (·.name == "Delegate") with
  | some d => match h2 : P.adts[d]? with
    | some D => if hc : D.coercible = true then .ok ⟨(d, D), h2, hc⟩ else .error "Delegate is not a proof type"
    | none => .error "unreachable"
  | none => .error "Delegate is not declared"

def coerParts (dC : Nat) : (t : Tm) →
    Option {x : Tm × Tm × Tm × Tm × Tm × Tm // t = Tm.coer dC x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2}
  | .app (.tyc d .nil) (.cons sa (.cons A (.cons a (.cons sb (.cons B (.cons b .nil)))))) =>
    if h : d = dC then some ⟨(sa, A, a, sb, B, b), by subst h; rfl⟩ else none
  | _ => none

def wrapAt (Γ : Ctx) (C : Tm) (m : Nat) (oe : Bool) (hm : (m, oe) ∈ Γ.opened) : Res {k // WrapOK P Γ C k} :=
  match hM : Γ.tys[m]? with
  | some M => match hc : Γ.canon M with
    | .mtbl _ true _ ph _ cs => do
      let ⟨hl⟩ ← need cs.isList "unreachable"
      match hi : cs.toList.findIdx? (fun C' => Γ.canon C' == Γ.canon C) with
      | some i => match hC' : cs.toList[i]? with
        | some C' => do
          let ⟨he⟩ ← need (Γ.canon C = Γ.canon C') "unreachable"
          let ⟨hp⟩ ← need (ph.getD i false = false) "coercible-wrap: a phantom constructor wraps nothing"
          let ⟨K, hK⟩ ← checkTm P Γ C
          match hk : Γ.canon K with
          | .valCtor sig => do
            let ⟨ht⟩ ← need sig.isTele "unreachable"
            match hn : sig.ntField with
            | some k => .ok ⟨k, .opened hm hM hc hl hC' he hp hK hk ht hn⟩
            | none => .error "coercible-wrap: not a wrapping constructor"
          | _ => .error "coercible-wrap: not a value constructor"
        | none => .error "unreachable"
      | none => .error "not listed"
    | _ => .error "not a newtype Matchable"
  | none => .error "unbound"

def wrapOf (Γ : Ctx) (C : Tm) : Res {k // WrapOK P Γ C k} :=
  match hC : Γ.canon C with
  | .vc d c _ => match hw : P.wrapField d c with
    | some k => .ok ⟨k, .decl hC hw⟩
    | none => .error "coercible-wrap: the constructor has no opened newtype `Matchable`"
  | _ =>
    let rec go : (l : List (Nat × Bool)) → (∀ e ∈ l, e ∈ Γ.opened) → Res {k // WrapOK P Γ C k}
      | [], _ => .error "coercible-wrap: the constructor has no opened newtype `Matchable`"
      | (m, oe) :: l, h => match wrapAt P Γ C m oe (h _ (by simp)) with
        | .ok r => .ok r
        | .error _ => go l fun e he => h e (by simp [he])
    go Γ.opened fun _ h => h

def checkPrim (Γ : Ctx) : (p : Prim) → Res {T // PrimTy P Γ p T}
  | .tm t => do let ⟨T, h⟩ ← checkTm P Γ t; .ok ⟨T, .tm h⟩
  | .lit t => do let ⟨T, h⟩ ← checkTm P Γ t; .ok ⟨T, .lit h⟩
  | .num d n => do let ⟨h⟩ ← need (P.natOK d = true) "a numeral needs the prelude's Nat"; .ok ⟨natTy d, .num h⟩
  | .assert t A => do
    let ⟨T, h⟩ ← checkTm P Γ t
    let ⟨hs⟩ ← need (t.static 0 0) "a literal's proof is not closed"
    let ⟨hS⟩ ← need (P.simpleStep P.simple = P.simple) "unreachable"
    let ⟨hk⟩ ← need ((A.fvs.all fun i => match Γ.tys[i]? with
        | some (.app (.tyc d .nil) .nil) => P.simple.contains d && (Γ.fixed[i]?.join).isSome
        | _ => false) = true)
      "a literal's fact mentions an entry whose value is not known"
    let ⟨he⟩ ← need (A.subst (Γ.fixedEnv P) = T) "a literal's proof is not of the fact it states"
    let ⟨hA⟩ ← need (A.static Γ.n 0) "a literal's fact is not well scoped"
    .ok ⟨A, .assert h hs hS (fun i hi => by
      have := List.all_eq_true.mp hk i hi
      split at this
      · rename_i d e
        simp only [Bool.and_eq_true, List.contains_iff_mem] at this
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this.2
        exact ⟨d, v, e, this.1, hv⟩
      · cases this) he hA⟩
  | .coerce a b p => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    match coerParts dC (Γ.canon Pt) with
    | some ⟨(_, _, a', _, B, b'), e⟩ => do
      let ⟨ha⟩ ← need (Γ.canon a = Γ.canon a') "coerce: value mismatch: the value is not the source of the proof"
      let ⟨Tb, hb⟩ ← checkTm P Γ b
      let ⟨hb'⟩ ← need (Γ.canon b = Γ.canon b') "unreachable: coerce's target"
      let ⟨hT⟩ ← need (Γ.canon Tb = Γ.canon B) "coerce: the target is not of the type the proof names"
      .ok ⟨B, .coerce hp e hD hc ha hb hb' hT⟩
    | none => .error "coerce: the proof is not a `Coercible` proof"
  | .coerRefl s e => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨_, hs⟩ ← checkTm P Γ s
    let ⟨_, he⟩ ← checkTm P Γ e
    .ok ⟨_, .coerRefl (dC := dC) hs he hD hc⟩
  | .deleOf g t => do
    let ⟨(dD, D), hD, hc⟩ ← deleAdt P
    match hm : Γ.deles.find? (fun e => e.1 == g && e.2.1 == t) with
    | some (g', t', sg, st) =>
      have hm' : (g, t, sg, st) ∈ Γ.deles := by
        have := List.find?_some hm; simp only [Bool.and_eq_true, beq_iff_eq] at this
        obtain ⟨rfl, rfl⟩ := this; exact List.mem_of_find?_eq_some hm
      match hg : Γ.tys[g]?, ht : Γ.tys[t]? with
      | some _, some _ => .ok ⟨_, .deleOf hm' hg ht hD hc⟩
      | _, _ => .error "delegate-of: unbound entry"
    | none => .error "delegate-of: not a function with a `delegate` body"
  | .coerOf p => do
    let ⟨(dD, D), hD, hc⟩ ← deleAdt P
    let ⟨(dC, C), hC, hcc⟩ ← coerAdt P
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    match coerParts dD (Γ.canon Pt) with
    | some ⟨_, e⟩ => .ok ⟨_, .coerOf hp e hD hc hC hcc⟩
    | none => .error "coercible-of: not a `Delegate` proof"
  | .coerSym p => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    match coerParts dC (Γ.canon Pt) with
    | some ⟨_, e⟩ => .ok ⟨_, .coerSym hp e hD hc⟩
    | none => .error "coercible-sym: not a `Coercible` proof"
  | .coerShare p => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    match coerParts dC (Γ.canon Pt) with
    | some ⟨_, e⟩ => .ok ⟨_, .coerShare hp e hD hc⟩
    | none => .error "coercible-share: not a `Coercible` proof"
  | .coerTrans p q => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨Pt, hp⟩ ← checkTm P Γ p
    let ⟨Qt, hq⟩ ← checkTm P Γ q
    match coerParts dC (Γ.canon Pt), coerParts dC (Γ.canon Qt) with
    | some ⟨(sa, A, a, sb, B, b), e1⟩, some ⟨(sb', B', b', sc, C, c), e2⟩ => do
      if h : sb' = sb ∧ B' = B ∧ b' = b then
        .ok ⟨_, .coerTrans (sc := sc) (C := C) (c := c) hp hq e1 (by obtain ⟨rfl, rfl, rfl⟩ := h; exact e2) hD hc⟩
      else .error "coercible-trans: the middle sides differ"
    | _, _ => .error "coercible-trans: not `Coercible` proofs"
  | .coerWrap s C args => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨_, hs⟩ ← checkTm P Γ s
    let ⟨T0, ha⟩ ← checkTm P Γ (.app C args)
    let ⟨k, hwk⟩ ← wrapOf P Γ C
    let ⟨_, hf⟩ ← checkTm P Γ (args.toList.getD k .nil)
    let ⟨K, hK⟩ ← checkTm P Γ C
    match hk : Γ.canon K with
    | .valCtor sig => do
      let ⟨ht⟩ ← need sig.isTele "coercible-wrap: the constructor's signature is not written out"
      .ok ⟨_, .coerWrap hs ha hwk hf hD hc hK hk ht rfl⟩
    | _ => .error "coercible-wrap: not a value constructor"
  | .coerCtor s C srcs tgts ps => do
    let ⟨(dC, D), hD, hc⟩ ← coerAdt P
    let ⟨_, hs⟩ ← checkTm P Γ s
    let ⟨K, hK⟩ ← checkTm P Γ C
    match hk : Γ.canon K with
    | .valCtor sig => do
      let ⟨ht⟩ ← need sig.isTele "coercible-ctor: the constructor's signature is not written out"
      let ⟨_, h1⟩ ← checkTm P Γ (.app C srcs)
      let ⟨_, h2⟩ ← checkTm P Γ (.app C tgts)
      let ⟨hl⟩ ← need (srcs.len = tgts.len) "coercible-ctor: the sources and targets differ in number"
      let ⟨hf⟩ ← allIdx (Q := fun j (e : Bool) => j < srcs.len → e = false → ∃ p Pt sa A x sb B y, ps.toList[j]? = some p ∧
          TmTy P Γ p Pt ∧ Γ.canon Pt = Tm.coer dC sa A x sb B y ∧ Γ.canon x = Γ.canon (srcs.toList.getD j .nil) ∧
          Γ.canon y = Γ.canon (tgts.toList.getD j .nil) ∧
          (if sig.uAt j then Γ.canon sa = Γ.canon s ∧ Γ.canon sb = Γ.canon s
            else Γ.canon sa = sharedTm ∧ Γ.canon sb = sharedTm))
        (fun j e => if he : j < srcs.len ∧ e = false then
          match hp : ps.toList[j]? with
          | some p => do
            let ⟨Pt, hpt⟩ ← checkTm P Γ p
            match coerParts dC (Γ.canon Pt) with
            | some ⟨(sa, A, x, sb, B, y), e⟩ => do
              let ⟨hx⟩ ← need (Γ.canon x = Γ.canon (srcs.toList.getD j .nil)) "coercible-ctor: a field's proof is not about its source"
              let ⟨hy⟩ ← need (Γ.canon y = Γ.canon (tgts.toList.getD j .nil)) "coercible-ctor: a field's proof is not about its target"
              let ⟨hsd⟩ ← need (if sig.uAt j then Γ.canon sa = Γ.canon s ∧ Γ.canon sb = Γ.canon s
                  else Γ.canon sa = sharedTm ∧ Γ.canon sb = sharedTm)
                "coercible-ctor: the proof for a field has its sides: `(Shared)` for a many field, the form's own for a unique one"
              .ok ⟨fun _ _ => ⟨p, Pt, sa, A, x, sb, B, y, rfl, hpt, e, hx, hy, hsd⟩⟩
            | none => .error "coercible-ctor: expected a `Coercible` proof for a non-erased field"
          | none => .error "coercible-ctor: a non-erased field has no proof"
        else .ok ⟨fun h1 h2 => absurd ⟨h1, h2⟩ he⟩) sig.ers 0
      .ok ⟨_, .coerCtor hs hK hk ht h1 h2 hl (fun j hjl hj => by
        cases h : sig.ers[j]? with
        | none => simp [List.getD_eq_getElem?_getD, h] at hj
        | some e =>
          have : e = false := by simpa [List.getD_eq_getElem?_getD, h] using hj
          simpa using hf j e h (by simpa using hjl) this) hD hc⟩
    | _ => .error "coercible-ctor: not a value constructor"
  | .mtblOf d ls => match h : P.adts[d]? with
    | some D => do
      let ⟨hl⟩ ← need (ls.len = D.lifted) "matchable-of: the wrong number of lifted arguments"
      let ⟨_, ha⟩ ← checkArgs P Γ ls D.params
      let ⟨hc⟩ ← need (D.coercible = false) "matchable-of: Coercible has no Matchable"
      let ⟨ho⟩ ← need (D.opq = false) "matchable-of: an opaque type has no Matchable"
      .ok ⟨_, .mtblOf h hl ha hc ho⟩
    | none => .error "matchable-of: unknown type"
  | .atom d => match h : P.adts[d]? with
    | some D => match hc : D.ctors with
      | [.bind (.ty m e u) (.app (.tyc d' .nil) .nil) .nil] => do
        let ⟨hd⟩ ← need (d' = d) "an atom's type has another constructor"
        let ⟨hl⟩ ← need (D.lifted = 0) "an atom's type has lifted arguments"
        let ⟨hn⟩ ← need (D.newtype = false) "an atom's type is a newtype"
        let ⟨hp⟩ ← need (P.phantom d 0 = false) "an atom's constructor is phantom"
        .ok ⟨_, .atom h (hd ▸ hc) hl hn hp⟩
      | _ => .error "an atom's type has one constructor with no fields"
    | none => .error "an atom of an unknown type"
  | .atomEq d q a b => match h : P.adts[d]?, h' : P.adts[q]? with
    | some D, some E => match hc : D.ctors, hc' : E.ctors with
      | [.bind (.ty m e u) (.app (.tyc d' .nil) .nil) .nil],
        [.bind (.ty m1 e1 u1) .univ (.bind (.ty m2 e2 u2) (.bv 0) (.bind (.ty m3 e3 u3)
          (.app (.tyc q' .nil) (.cons (.bv 1) (.cons (.bv 0) (.cons (.bv 0) .nil)))) .nil))] => do
        let ⟨hd⟩ ← need (d' = d) "an atom's type has another constructor"
        let ⟨hq⟩ ← need (q' = q) "Eq's constructor builds another type"
        let ⟨hl⟩ ← need (D.lifted = 0) "an atom's type has lifted arguments"
        let ⟨ho⟩ ← need (D.opq = false) "an atom's type is opaque"
        let ⟨hl'⟩ ← need (E.lifted = 0) "Eq has lifted arguments"
        let ⟨A, ha⟩ ← checkTm P Γ a
        let ⟨B, hb⟩ ← checkTm P Γ b
        let ⟨hA⟩ ← need (Γ.canon A = .app (.tyc d .nil) .nil) "slot-self: not a slot"
        let ⟨hB⟩ ← need (Γ.canon B = .app (.tyc d .nil) .nil) "slot-self: not a slot"
        have hc2 : E.ctors = [eqSig q (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)] := by rw [hc', hq]; rfl
        .ok ⟨_, .atomEq h (hd ▸ hc) hl ho h' hc2 hl' ha hA hb hB⟩
      | _, _ => .error "slot-self: Slot or Eq has an unexpected shape"
    | _, _ => .error "slot-self: Slot or Eq is unknown"
  | .axm A => do
    let ⟨U, hA⟩ ← checkTm P Γ A
    let ⟨hU⟩ ← need (Γ.canon U = .univ) "an axiom's return is not a type"
    match hc : Γ.canon A with
    | .app (.tyc d ls) idx => match hD : P.adts[d]? with
      | some D => do
        let ⟨ho⟩ ← need (D.opq = true) "an axiom returns only a value of an opaque type"
        let ⟨hpl⟩ ← need (P.placedD ≠ some d) "an axiom returns no `Placed` value"
        .ok ⟨_, .axm hA hU hc hD ho hpl⟩
      | none => .error "an axiom returns only a value of an opaque type"
    | _ => .error "an axiom returns only a value of an opaque type"
  | .place a T => match T with
    | .app (.tyc q .nil) (.cons s (.cons B (.cons a' .nil))) => do
      let ⟨hq⟩ ← need (P.placedD = some q) "place-at: not a `Placed` type"
      let ⟨A, ha⟩ ← checkTm P Γ a
      let ⟨hAB⟩ ← need (Γ.canon A = Γ.canon B) "place-at: the value is not of the type its box names"
      let ⟨hB⟩ ← need (B.static Γ.n 0) "place-at: the type is not well scoped"
      let ⟨hs⟩ ← need (s.static Γ.n 0) "place-at: the slot is not well scoped"
      if h : a' = a then by subst h; exact .ok ⟨_, PrimTy.place hq ha hAB hB hs⟩
      else .error "place-at: the box names another value"
    | _ => .error "place-at: not a `Placed` type"
  | .unplace a v => do
    let ⟨A, ha⟩ ← checkTm P Γ a
    match hA : Γ.canon A with
    | .app (.tyc q .nil) (.cons s (.cons B (.cons w .nil))) => do
      let ⟨hq⟩ ← need (P.placedD = some q) "unplace-at: not a `Placed` value"
      let ⟨hv⟩ ← need (Γ.canon v = w) "unplace-at: the result is not the box's index"
      .ok ⟨_, .unplace hq ha hA hv⟩
    | _ => .error "unplace-at: not a `Placed` value"
  | .placedEq e C a b => match hE : P.adts[e]? with
    | some E => match hc : E.ctors with
      | [.bind (.ty m1 e1 u1) .univ (.bind (.ty m2 e2 u2) (.bv 0) (.bind (.ty m3 e3 u3)
          (.app (.tyc e' .nil) (.cons (.bv 1) (.cons (.bv 0) (.cons (.bv 0) .nil)))) .nil))] => do
        let ⟨he⟩ ← need (e' = e) "Eq's constructor builds another type"
        let ⟨hl⟩ ← need (E.lifted = 0) "Eq has lifted arguments"
        have hc2 : E.ctors = [eqSig e (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)] := by rw [hc, he]; rfl
        let ⟨U, hC⟩ ← checkTm P Γ C
        match hCc : Γ.canon C with
        | .app (.tyc q .nil) (.cons s (.cons B (.cons w .nil))) => do
          let ⟨hq⟩ ← need (P.placedD = some q) "placed-eq: not a `Placed` type"
          let ⟨A, ha⟩ ← checkTm P Γ a
          let ⟨B', hb⟩ ← checkTm P Γ b
          let ⟨hA⟩ ← need (Γ.canon A = Γ.canon C) "placed-eq: the first box is of another type"
          let ⟨hB⟩ ← need (Γ.canon B' = Γ.canon C) "placed-eq: the second box is of another type"
          .ok ⟨_, .placedEq hq hE hc2 hl hC hCc ha hA hb hB⟩
        | _ => .error "placed-eq: not a `Placed` type"
      | _ => .error "placed-eq: Eq has an unexpected shape"
    | none => .error "placed-eq: Eq is unknown"
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

def armsOf (Γ : Ctx) (ph : List Bool) : (ks : List Tm) → (base : Nat) →
    Res {shp : List Arm // shp.map (·.1) = ks ∧ ∀ i k sig p, shp[i]? = some (k, sig, p) →
      p = ph.getD (base + i) false ∧ sig.isTele ∧ sig.static Γ.n 0 ∧ ∃ K, TmTy P Γ k K ∧ Γ.canon K = .valCtor sig}
  | [], _ => .ok ⟨[], rfl, fun _ _ _ _ h => by simp at h⟩
  | k :: ks, base => do
    let ⟨K, hk⟩ ← checkTm P Γ k
    match hK : Γ.canon K with
    | .valCtor sig => do
      let ⟨ht⟩ ← need sig.isTele "Matchable: a constructor's signature is not a telescope"
      let ⟨hs⟩ ← need (sig.static Γ.n 0) "Matchable: a constructor's signature is not well scoped"
      let ⟨shp, h1, h2⟩ ← armsOf Γ ph ks (base + 1)
      .ok ⟨(k, sig, ph.getD base false) :: shp, by simp [h1], fun
        | 0, _, _, _, h => by simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨by simp, ht, hs, K, hk, hK⟩
        | i + 1, k', sig', p', h => by
          have := h2 i k' sig' p' (by simpa using h)
          rwa [show base + 1 + i = base + (i + 1) by omega] at this⟩
    | _ => .error "Matchable: an entry is not a value constructor"

def shapeOf (Γ : Ctx) (er : Bool) : (H : Tm) → Res ((shp : List Arm) × {nt // Shape P Γ er H shp nt})
  | .tyc d ls => match h : P.adts[d]? with
    | some D => do
      let ⟨hc⟩ ← need (D.coercible = false) "a match on Coercible, which has no constructors to match"
      let ⟨ho⟩ ← need (D.opq = false) s!"`{D.name}` has no `Matchable` open"
      let ⟨hl⟩ ← need (ls.len = D.lifted) "a type constructor with the wrong number of lifted arguments"
      let ⟨hi⟩ ← need ls.isList "a type constructor's lifted arguments are not a list"
      let ⟨hs⟩ ← need (ls.static Γ.n 0) "a type constructor's lifted arguments are not well scoped"
      .ok ⟨_, _, .decl h hc ho hl hi hs⟩
    | none => .error "unknown type"
  | H =>
    let names (e : Nat × Bool) : Bool := match (Γ.tys[e.1]?).map Γ.canon with
      | some (.mtbl _ _ _ _ H' _) => H' == H
      | _ => false
    let pick : Option {e // e ∈ Γ.opened} := match hf : Γ.opened.find? (fun e => names e && !e.2 && !Γ.er e.1) with
      | some e => some ⟨e, List.mem_of_find?_eq_some hf⟩
      | none => match hf : Γ.opened.find? names with
        | some e => some ⟨e, List.mem_of_find?_eq_some hf⟩
        | none => none
    match pick with
    | some ⟨(m, oe), hmem⟩ => match hM : Γ.tys[m]? with
      | some M => match hc : Γ.canon M with
        | .mtbl _ nt _ ph H' cs => do
          let ⟨hH⟩ ← need (H' = H) "unreachable"
          let ⟨hl⟩ ← need cs.isList "Matchable: the constructors are not a list"
          let ⟨hr⟩ ← need (er || Γ.ok (!oe && !Γ.er m)) "a match that dispatches at runtime through an erased Matchable"
          let ⟨shp, h1, h2⟩ ← armsOf P Γ ph cs.toList 0
          .ok ⟨shp, nt, .opened hmem hM (hH ▸ hc) hl h1 (fun i k sig p h => by simpa using h2 i k sig p h) hr⟩
        | _ => .error "unreachable"
      | none => .error "unreachable"
    | none => .error "scrutinee: no Matchable is open for its type"

def synthRets (Γ : Ctx) (n : Nat) : (ts : Tm) → Res {R // ArgsTy P Γ ts R .nil ∧ R.static n 0}
  | .nil => .ok ⟨.nil, .nil, rfl⟩
  | .cons a as => do
    let ⟨T, ha⟩ ← checkTm P Γ a
    let ⟨R, hr, hR⟩ ← synthRets Γ n as
    have hi : R.inst a 0 = R := Tm.inst_static n R 0 0 hR (Nat.le_refl 0)
    have hR1 := Tm.static_mono (Nat.le_refl n) R (Nat.zero_le 1) hR
    if hs : (Γ.canon T).static 0 0 then
      have hc : Γ.canon (Γ.canon T) = Γ.canon T := Tm.subst_static0 _ _ _ hs
      .ok ⟨.bind (.ty false false false) (Γ.canon T) R, .cons ha hc.symm (by rw [hi]; exact hr),
        by simp [Tm.static, Tm.static_mono (Nat.zero_le n) _ (Nat.le_refl 0) hs, hR1]⟩
    else if hs : T.static n 0 then
      .ok ⟨.bind (.ty false false false) T R, .cons ha rfl (by rw [hi]; exact hr), by simp [Tm.static, hs, hR1]⟩
    else .ok ⟨.bind (.ty false false false) .nil R, .anyCons ha (by rw [hi]; exact hr), by simp [Tm.static, hR1]⟩
  | _ => .error "not a list of results"

def retTele (Γ : Ctx) (ts : List Tm) (hid : Nat) : Option Tm := do
  let Ts ← ts.mapM fun t => match checkTm P Γ t with
    | .ok ⟨T, _⟩ => some (Γ.canon T)
    | .error _ => none
  let ents := Ts.zipIdx.map fun (T, j) =>
    ((List.range j).foldl (fun (T : Tm) i => match ts[i]? with
      | some (Tm.fv x) => T.close x (j - 1 - i)
      | _ => T) T, decide (j < hid))
  some (ents.foldr (fun (T, e) r => .bind (.ty false e false) T r) .nil)

mutual
def checkCore (b : Nat) (Γ : Ctx) : (c : Core) → (rets : Tm ⊕ Nat) →
    Res {R // CoreTy P b Γ c R ∧ (∀ r, rets = .inl r → R = r) ∧ ∀ n, rets = .inr n → R.static n 0}
  | .ret ts, .inl r => do
    let ⟨out, h⟩ ← checkArgs P Γ ts r
    let ⟨ho⟩ ← need (out = .nil) "wrong number of results"
    let ⟨hr⟩ ← need (Γ.ok (rtArgs P Γ ts r)) "a non-erased result mentions something erased"
    .ok ⟨r, .ret (ho ▸ h) hr, fun _ e => Sum.inl.inj e, fun _ e => (by cases e)⟩
  | .ret ts, .inr n =>
    let fallback : Res {R // CoreTy P b Γ (.ret ts) R ∧ (∀ r, Sum.inr n = Sum.inl r → R = r) ∧
        ∀ m, Sum.inr n = Sum.inr m → R.static m 0} := do
      let ⟨R, h, hs⟩ ← synthRets P Γ n ts
      let ⟨hr⟩ ← need (Γ.ok (rtArgs P Γ ts R)) "a non-erased result mentions something erased"
      .ok ⟨R, .ret h hr, fun _ e => (by cases e), fun _ e => by cases e; exact hs⟩
    match retTele P Γ ts.toList P.hidden with
    | some R => match checkArgs P Γ ts R with
      | .ok ⟨out, h⟩ =>
        if ho : out = .nil ∧ R.static n 0 ∧ Γ.ok (rtArgs P Γ ts R) = true then
          .ok ⟨R, .ret (ho.1 ▸ h) ho.2.2, fun _ e => (by cases e), fun _ e => by cases e; exact ho.2.1⟩
        else fallback
      | .error _ => fallback
    | none => fallback
  | .absurd body, rets => do
    let ⟨_, hb, e⟩ ← checkCore b { Γ with ghost := true } body (.inl .nil)
    let ⟨hn⟩ ← need (body.noRet = true) "absurd: the body does not refute the facts in force"
    let R' := match rets with | .inl r => r | .inr _ => .nil
    .ok ⟨R', .absurd (e.1 _ rfl ▸ hb) hn, fun r e => by simp [R', e], fun n e => by simp [R', e, Tm.static]⟩
  | .dead, _ => .error "a refuted branch outside a match"
  | .seq R0 body rest, rets => do
    let ⟨hR⟩ ← checkTele P Γ R0
    let ⟨hRs⟩ ← need (R0.static Γ.n 0) "results not well scoped"
    let ⟨hRt⟩ ← need (R0.isTele) "results: not a telescope"
    let ⟨_, hb, e⟩ ← checkCore b Γ body (.inl R0)
    let ⟨R, hr, e2⟩ ← checkCore b (Ctx.adv P Γ (Γ.pushTele R0) (.seq R0 body rest)) rest rets
    .ok ⟨R, .seq hR hRs hRt (e.1 R0 rfl ▸ hb) hr, e2⟩
  | .call f dec args er ms ve rest, rets => do
    let ⟨Ft, hf⟩ ← checkTm P Γ f
    match hF : Γ.canon Ft with
    | .fn l np t _ _ => do
      let ⟨ht⟩ ← need (t.isTele) "not a telescope"
      let ⟨outs, ha⟩ ← checkArgs P Γ args t
      let ⟨hn⟩ ← need (args.len = np) "wrong number of arguments"
      let ⟨hd⟩ ← checkDec P Γ l t args dec
      let ⟨ho⟩ ← need (outs.len = ms.length) "wrong number of results bound"
      let ⟨hm⟩ ← need (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outs))
        "a non-erased call mentions something erased, or binds an erased result at many"
      let ⟨hv⟩ ← need (ve = some t.ers) "the call's view of its callee's erasures is not its type's"
      let ⟨R, hr, e⟩ ← checkCore b (Ctx.adv P Γ (Γ.pushTele outs (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)) rest rets
      .ok ⟨R, .call hf hF ht ha hn hd ho hm hv hr, e⟩
    | _ => .error "not a function"
  | .mtch s R0 brs els er rest, rets => do
    let ⟨St, hs⟩ ← checkTm P Γ s
    match hS : Γ.canon St with
    | .app H idx => do
      let ⟨shp, ntf, hsh⟩ ← shapeOf P Γ er H
      let ⟨hnt⟩ ← need (er || !ntf) "unreachable: a non-erased match on a newtype elaborates to a case"
      let ⟨hl⟩ ← need (armsOK Γ shp brs) "a branch names a constructor of another type"
      let ⟨hR⟩ ← checkTele P Γ R0
      let ⟨hRs⟩ ← need (R0.static Γ.n 0) "match: return telescope not well scoped"
      let ⟨hRt⟩ ← need (R0.isTele) "match: not a telescope"
      let ⟨hm⟩ ← need (er || Γ.ok (rt P Γ s)) "a non-erased match on an erased scrutinee"
      let Γg := { Γ with ghost := Γ.ghost || er }
      let ⟨hb⟩ ← checkBranches b Γ false (fun p => Γ.ghost || er || p) s H idx R0 brs els.isSome shp 0
      let ⟨he⟩ ← (match els with
        | some eb => do
          let ⟨_⟩ ← need (shp.zipIdx.any fun ((k, sig, _), c) =>
              (lookupBr brs c).isNone && (Γ.branch P s k H idx sig).2 matches .ok _ | .unknown)
            "else: it stands for no constructor"
          let ⟨_, h, e⟩ ← checkCore b Γg eb (.inl R0)
          .ok ⟨fun _ h' => by cases h'; exact e.1 R0 rfl ▸ h⟩
        | none => .ok ⟨fun _ h' => nomatch h'⟩ : Res (PLift (∀ e, els = some e → CoreTy P b Γg e R0)))
      let ⟨R, hr, e⟩ ← checkCore b (Ctx.adv P Γ (Γ.pushTele R0 (if er then some (List.replicate R0.len true) else none)) (.mtch s R0 brs els er rest)) rest rets
      .ok ⟨R, .mtch hs hS hsh hnt hl hR hRs hRt hm (fun c k sig p h1 => by simpa using hb c k sig p h1) he hr, e⟩
    | _ => .error "scrutinee not of a data type"
  | .case s brs els er nt, rets => do
    let ⟨St, hs⟩ ← checkTm P Γ s
    match hS : Γ.canon St with
    | .app H idx => do
      let ⟨shp, ntf, hsh⟩ ← shapeOf P Γ er H
      let ⟨hnt⟩ ← need (nt = (ntf && !er)) "unreachable: a case on a newtype is marked as one"
      let ⟨hl⟩ ← need (armsOK Γ shp brs) "a branch names a constructor of another type"
      let ⟨hm⟩ ← need (er || Γ.ok (rt P Γ s)) "a non-erased match on an erased scrutinee"
      let ⟨h1⟩ ← need (Γ.ghost = false → (er || nt) → realCount brs els ≤ 1)
        "a match with an erased discriminant has more than one real branch"
      let g := fun p => Γ.ghost || (!er && p)
      let fes (sig : Tm) := if er then some (List.replicate (sig.len - 1) true) else none
      let ⟨R, hR1, hR2⟩ ← (match hr : rets with
        | .inl r => .ok ⟨r, fun _ e => Sum.inl.inj e, fun _ e => by cases e⟩
        | .inr n => do
          let pick : Option {x : Ctx × Core // sizeOf x.2 < sizeOf brs + sizeOf els} :=
            match hf : brs.find? (·.2.2.2.real) with
            | some (_, c, _, body) => match shp[c]? with
              | some (k, sig, p) => match ({ Γ with ghost := g p } : Ctx).branch P s k H idx sig with
                | (Γf, .ok σ) => some ⟨({ ({ Γ with ghost := g p } : Ctx).advBr P (({ Γ with ghost := g p } : Ctx).setErs
                    { Γf with σ := σ } (fes sig)) s k er (sig.len - 1) with cmode := false }, body), by
                    have := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some hf); simp at this ⊢; omega⟩
                | _ => none
              | none => none
            | none => match he : els with
              | some e => some ⟨(Γ, e), by simp; omega⟩
              | none => none
          match pick with
          | some ⟨(Γb, body), hlt⟩ => do
            have : sizeOf body < sizeOf brs + sizeOf els := hlt
            let ⟨R, _, _, h⟩ ← checkCore b Γb body (.inr n)
            .ok ⟨R, (fun _ e => nomatch e), h⟩
          | none => .ok ⟨.nil, (fun _ e => nomatch e), fun _ _ => rfl⟩ :
        Res {R : Tm // (∀ r, rets = .inl r → R = r) ∧ ∀ m, rets = .inr m → R.static m 0})
      let ⟨hb⟩ ← checkBranches b Γ er g s H idx R brs els.isSome shp 0
      let ⟨he⟩ ← (match els with
        | some eb => do
          let ⟨_⟩ ← need (shp.zipIdx.any fun ((k, sig, _), c) =>
              (lookupBr brs c).isNone && (Γ.branch P s k H idx sig).2 matches .ok _ | .unknown)
            "else: it stands for no constructor"
          let ⟨_, h, e⟩ ← checkCore b Γ eb (.inl R)
          .ok ⟨fun _ h' => by cases h'; exact e.1 R rfl ▸ h⟩
        | none => .ok ⟨fun _ h' => nomatch h'⟩ : Res (PLift (∀ e, els = some e → CoreTy P b Γ e R)))
      .ok ⟨R, .case hs hS hsh hnt hl hm h1 (fun c k sig p h => by simpa [g] using hb c k sig p h) he,
        hR1, hR2⟩
    | _ => .error "scrutinee not of a data type"
  | .prim p er rest, rets => do
    let ⟨T, hp⟩ ← checkPrim P Γ p
    let ⟨hm⟩ ← need (er || Γ.ok (p.rt P Γ)) "a non-erased let binder of a term mentioning something erased"
    let ⟨R, hr, e⟩ ← checkCore b (Ctx.adv P Γ (Γ.pushPrim T er p) (.prim p er rest)) rest rets
    .ok ⟨R, .prim hp hm hr, e⟩
  | .defLvl rest, rets => do
    let ⟨R, hr, e⟩ ← checkCore b (Ctx.adv P Γ Γ.pushMint (.defLvl rest)) rest rets
    .ok ⟨R, .defLvl hr, e⟩
  | .defFns gid rest, rets => do
    let ⟨hg⟩ ← need (gid < b) "group out of order"
    match hG : P.groups[gid]? with
    | some G => do
      let ⟨hok⟩ ← checkGroup gid Γ G
      let ⟨R, hr, e⟩ ← checkCore b (Ctx.adv P Γ (Γ.pushFns G) (.defFns gid rest)) rest rets
      .ok ⟨R, .defFns hg hG hok hr, e⟩
    | none => .error "unknown group"
  | .chk (.opn oe) (.fv m) _ rest, rets => match hM : Γ.tys[m]? with
    | some M => match hc : Γ.canon M with
      | .mtbl _ _ _ _ H cs => do
        let Γo : Ctx := { Γ with opened := (m, oe) :: Γ.opened }
        let R' := match rets with | .inl r => r | .inr _ => .nil
        have e1 : ∀ r, rets = .inl r → R' = r := fun r e => by simp [R', e]
        have e2 : ∀ n, rets = .inr n → R'.static n 0 := fun n e => by simp [R', e, Tm.static]
        match hd : rest with
        | .dead =>
          if hn : cs.toList.Nodup then
            match hu : unify Γ.n (Γo.atoms P) Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
            | .contra => .ok ⟨R', by rw [hd]; exact .chkOpnFail hM hc (.inr hu), e1, e2⟩
            | _ => .error "open-absurd: the open does not contradict what is open"
          else .ok ⟨R', by rw [hd]; exact .chkOpnFail hM hc (.inl hn), e1, e2⟩
        | r => do
          let ⟨hn⟩ ← need cs.toList.Nodup "open-adt: a constructor is listed twice, which contradicts what is open"
          match hu : unify Γ.n (Γo.atoms P) Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
          | .ok σ' => do
            let ⟨R, hr, eq⟩ ← checkCore b { Γo with σ := σ' } r rets
            .ok ⟨R, by rw [hd]; exact .chkOpn hM hc hn hu hr, eq⟩
          | .contra => .error "open-adt: the Matchable contradicts what is open"
          | .unknown => .error "open-adt: cannot decide whether the Matchable agrees with what is open"
      | _ => .error "open-adt: not a Matchable"
    | none => .error "open-adt: unbound"
  | .chk (.opn _) .., _ => .error "open-adt: not an entry"
  | .chk .cm _ _ rest, rets => do
    let ⟨R, hr, eq⟩ ← checkCore b { Γ with cmode := true } rest rets
    .ok ⟨R, .chkCm hr, eq⟩
  | .chk (.mark _) _ _ rest, rets => do
    let ⟨R, hr, eq⟩ ← checkCore b Γ rest rets
    .ok ⟨R, .chkMark hr, eq⟩
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

def checkBranches (b : Nat) (Γ : Ctx) (fe : Bool) (g : Bool → Bool) (s H idx R0 : Tm)
    (brs : List Br) (els : Bool) : (arms : List Arm) → (base : Nat) →
    Res (PLift (∀ c k sig p, arms[c]? = some (k, sig, p) →
      BranchOK P b fe { Γ with ghost := g p } s k H idx sig R0 (lookupBr brs (base + c)) els))
  | [], _ => .ok ⟨fun _ _ _ _ h => by simp at h⟩
  | (k, sig, p) :: cs, base => do
    let Γc : Ctx := { Γ with ghost := g p }
    let ⟨hh⟩ ← (match hl : lookupBr brs base with
      | some .dead => match hb : Γc.branch P s k H idx sig with
        | (_, .contra) => .ok ⟨BranchOK.refuted (by rw [hb])⟩
        | _ => .error "an absurd branch names a constructor that is not refuted"
      | some body => match hb : Γc.branch P s k H idx sig with
        | (Γf, .ok σ) => do
          let ⟨_, hr, e⟩ ← checkCore b { Γc.advBr P (Γc.setErs { Γf with σ := σ }
            (if fe then some (List.replicate (sig.len - 1) true) else none)) s k fe (sig.len - 1) with cmode := false }
            body (.inl R0)
          .ok ⟨BranchOK.live hb (e.1 R0 rfl ▸ hr)⟩
        | (_, .contra) => .error "a listed branch is refuted"
        | (_, .unknown) => .error "cannot decide whether the branch is refuted"
      | none => match hb : Γc.branch P s k H idx sig with
        | (_, .contra) => .ok ⟨BranchOK.dead (by rw [hb])⟩
        | _ => if h : els then .ok ⟨h ▸ BranchOK.covered⟩
          else match s, hk : Γc.known k with
            | .fv x, some (d', c) => match hs : (Γc.fixed[x]?.join).map P.view with
              | some (.app (.vc d c0 _) vs) =>
                if hd : Γc.cmode = true ∧ d' = d ∧ c ≠ c0 ∧ P.isNt d = false then
                  .ok ⟨by obtain ⟨hm, rfl, hc, hn⟩ := hd; exact BranchOK.fixedOut hm hs hk hc hn⟩
                else .error "a branch that is not refuted is missing"
              | _ => .error "a branch that is not refuted is missing"
            | _, _ => .error "a branch that is not refuted is missing" :
      Res (PLift (BranchOK P b fe Γc s k H idx sig R0 (lookupBr brs base) els)))
    let ⟨ht⟩ ← checkBranches b Γ fe g s H idx R0 brs els cs (base + 1)
    .ok ⟨fun
      | 0, _, _, _, h1 => by simp at h1; obtain ⟨rfl, rfl, rfl⟩ := h1; simpa using hh
      | c + 1, k', sig', p', h1 => by
        have := ht c k' sig' p' (by simpa using h1)
        rwa [show base + 1 + c = base + (c + 1) by omega] at this⟩
termination_by arms => (b, 1, sizeOf brs, arms.length)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · have := sizeOf_lookupBr hl; simp; omega
  · simp

def checkGroup (gid : Nat) (Γ : Ctx) (G : Group) : Res (PLift (GroupOK P gid Γ G)) := do
  match hK : Γ.tys[G.lvl]? with
  | some K => do
    let ⟨hl⟩ ← need (Γ.canon K = .level) "def-fns: not a level"
    let ⟨hf⟩ ← checkFns gid Γ G G.fns 0
    let ers := G.ers.toArray
    let ⟨he⟩ ← need (∀ i < Γ.n, Γ.er i = ers.getD i true) "def-fns: the elaborator's erasure disagrees"
    let ⟨hg⟩ ← need (Γ.ghost = G.ghost) "def-fns: the elaborator's erasure disagrees"
    let ⟨hd⟩ ← need (G.deleOK P Γ.n = true)
      "def-fns: a delegate body does more than pass its arguments to its target and its target's results back"
    let ⟨hds⟩ ← need (G.sidesOK Γ = true)
      "def-fns: a delegate's sides disagree with the functions' types"
    .ok ⟨.mk hK hl (fun j F h => (hf j F (by simpa using h)).1)
      (fun j F h => (hf j F (by simpa using h)).2.1) (fun j F h => (hf j F (by simpa using h)).2.2) (by simpa [ers] using he) hg hd hds⟩
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

def checkCtor (d k : Nat) (_ : Nat) (sig : Tm) :
    Res (PLift (TeleOK P {tys := #[]} sig ∧ sig.static 0 0 ∧ ∃ idx, retOf sig = some (.app (.tyc d (liftBvs (sig.len - 1) k)) idx))) := do
  let ⟨ht⟩ ← checkTele P {tys := #[]} sig
  let ⟨hs⟩ ← need (sig.static 0 0) "def-adts: a constructor's signature is not closed"
  match h : retOf sig with
  | some (.app (.tyc d' ls) idx) => do
    let ⟨e⟩ ← need (d' = d) "def-adts: a constructor returns another type"
    let ⟨el⟩ ← need (ls = liftBvs (sig.len - 1) k) "def-adts: a constructor's return does not pass on the lifted parameters"
    .ok ⟨ht, hs, idx, e ▸ el ▸ h⟩
  | _ => .error "def-adts: a constructor does not return its type"

def checkProg : Res {R // Checked P R} := do
  let ⟨ha⟩ ← allIdx (Q := fun d (D : Adt) => (TeleOK P {tys := #[]} D.params ∧ D.params.static 0 0) ∧ ∀ (c : Nat) sig,
      D.ctors[c]? = some sig → TeleOK P {tys := #[]} sig ∧ sig.static 0 0 ∧
        ∃ idx, retOf sig = some (.app (.tyc d (liftBvs (sig.len - 1) D.lifted)) idx))
    (fun d D => do
      let ⟨hp⟩ ← checkTele P {tys := #[]} D.params
      let ⟨hps⟩ ← need (D.params.static 0 0) "def-adts: parameters not closed"
      let ⟨hc⟩ ← allIdx (checkCtor P d D.lifted) D.ctors 0
      .ok ⟨⟨hp, hps⟩, fun c sig h => by simpa using hc c sig h⟩) P.adts 0
  let ⟨hn⟩ ← need (∀ d ∈ List.range P.adts.length, ∀ c ∈ List.range (((P.adts[d]?).map fun (D : Adt) => D.ctors.length).getD 0),
      P.isNt d = true → P.phantom d c = false → ((P.ctor d c).bind fun sig => (sig.skip (P.lifted d)).ntField).isSome)
    "a newtype does not have newtype shape"
  let ⟨hco⟩ ← need (∀ d ∈ List.range P.adts.length, ∀ D, P.adts[d]? = some D → D.coercible = true → D.ctors = [])
    "unreachable: Coercible has constructors"
  let ⟨hop⟩ ← need (∀ d ∈ List.range P.adts.length, ∀ D, P.adts[d]? = some D → D.opq = true →
      D.ctors = [] ∧ D.coercible = false)
    "unreachable: an opaque type has constructors"
  let ⟨hpl⟩ ← need ((P.placedD.all fun q => (P.adts[q]?.map (·.opq)) == some true) = true)
    "unreachable: Placed is not opaque"
  let ⟨hue⟩ ← need (∀ d ∈ List.range P.adts.length, ∀ D, P.adts[d]? = some D → ∀ sig ∈ D.ctors,
      ∀ j < sig.ers.length, sig.uAt j = true → sig.ers.getD j true = false)
    "unreachable: a constructor field is both erased and unique"
  let ⟨R, h, _, hs⟩ ← checkCore P P.groups.length {tys := #[]} P.main (.inr 0)
  have hs := hs 0 rfl
  .ok ⟨R, ⟨fun d D e => by have := ha d D e; simp only [Nat.zero_add] at this; exact this.1,
    fun d D c sig e1 e2 => by have := ha d D e1; simp only [Nat.zero_add] at this; exact this.2 c sig e2,
    fun d c sig h1 h2 h3 => by
      obtain ⟨D, hD, hc⟩ := Option.bind_eq_some_iff.mp h3
      have hd : d < P.adts.length := (List.getElem?_eq_some_iff.mp hD).1
      have hcl : c < D.ctors.length := (List.getElem?_eq_some_iff.mp hc).1
      have := hn d (List.mem_range.mpr hd) c (List.mem_range.mpr (by simpa [hD] using hcl)) h1 h2
      simpa [h3] using this,
    fun d D h1 h2 => hco d (List.mem_range.mpr (List.getElem?_eq_some_iff.mp h1).1) D h1 h2,
    fun d D h1 h2 => hop d (List.mem_range.mpr (List.getElem?_eq_some_iff.mp h1).1) D h1 h2,
    fun q hq => by
      rw [hq] at hpl; simp only [Option.all_some, beq_iff_eq, Option.map_eq_some_iff] at hpl
      obtain ⟨D, hD, ho⟩ := hpl; exact ⟨D, hD, ho⟩,
    fun d c sig h j hu => by
      obtain ⟨D, hD, hc⟩ := Option.bind_eq_some_iff.mp h
      exact hue d (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hD).1) D hD sig (List.mem_of_getElem? hc) j
        (Tm.uAt_lt _ _ hu) hu⟩, h, hs⟩

end Minimal
