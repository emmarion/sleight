namespace Minimal

inductive Ent where
  | ty (mark er u : Bool)
  | is (mark er u sl : Bool)
  deriving DecidableEq, Repr, Inhabited

def Ent.marked : Ent → Bool
  | ty m _ _ => m
  | is m _ _ _ => m

def Ent.er : Ent → Bool
  | ty _ e _ | is _ e _ _ => e

def Ent.u : Ent → Bool
  | ty _ _ u | is _ _ u _ => u

inductive Tm where
  | fv (i : Nat)
  | bv (i : Nat)
  | nil
  | cons (h t : Tm)
  | bind (k : Ent) (ty rest : Tm)
  | app (h args : Tm)
  | tyc (d : Nat) (ls : Tm)
  | vc (d c : Nat) (ls : Tm)
  | tyCtor (ps : Tm)
  | valCtor (sig : Tm)
  | univ
  | level
  | predates (A x L : Tm)
  | subterm (A a B b : Tm)
  | fn (l : Tm) (np : Nat) (tele : Tm) (u : Bool) (hm : List Bool)
  | mtbl (u nt ex : Bool) (ph : List Bool) (T cs : Tm)
  | lvl (n : Nat)
  | tok
  | clo (env : Tm) (gid j : Nat)
  | nat (n : Nat)
  | ptr (a : Nat)
  | wld (k : Nat)
  | sfv (i : Nat)
  | sbv (i : Nat)
  deriving DecidableEq, Repr, Inhabited

def slotD : Nat := 4

namespace Tm

def vacant : Tm := app (vc slotD 0 nil) nil

def isSlotVal (n : Nat) : Tm → Bool
  | sfv j => j < n
  | t => t == vacant

def slotOf : Tm → Tm
  | fv j | sfv j => sfv j
  | _ => vacant

def subst (f : Nat → Tm) : Tm → Tm
  | fv i => f i
  | sfv i => slotOf (f i)
  | tyc d ls => tyc d (ls.subst f)
  | vc d c ls => vc d c (ls.subst f)
  | cons h t => cons (h.subst f) (t.subst f)
  | bind m a r => bind m (a.subst f) (r.subst f)
  | app h a => app (h.subst f) (a.subst f)
  | tyCtor p => tyCtor (p.subst f)
  | valCtor p => valCtor (p.subst f)
  | predates A x L => predates (A.subst f) (x.subst f) (L.subst f)
  | subterm A a B b => subterm (A.subst f) (a.subst f) (B.subst f) (b.subst f)
  | fn l np t uf hm => fn (l.subst f) np (t.subst f) uf hm
  | mtbl u nt ex ph T cs => mtbl u nt ex ph (T.subst f) (cs.subst f)
  | t => t

def subst2 (f g : Nat → Tm) : Tm → Tm
  | fv i => f i
  | sfv i => g i
  | tyc d ls => tyc d (ls.subst2 f g)
  | vc d c ls => vc d c (ls.subst2 f g)
  | cons h t => cons (h.subst2 f g) (t.subst2 f g)
  | bind m a r => bind m (a.subst2 f g) (r.subst2 f g)
  | app h a => app (h.subst2 f g) (a.subst2 f g)
  | tyCtor p => tyCtor (p.subst2 f g)
  | valCtor p => valCtor (p.subst2 f g)
  | predates A x L => predates (A.subst2 f g) (x.subst2 f g) (L.subst2 f g)
  | subterm A a B b => subterm (A.subst2 f g) (a.subst2 f g) (B.subst2 f g) (b.subst2 f g)
  | fn l np t uf hm => fn (l.subst2 f g) np (t.subst2 f g) uf hm
  | mtbl u nt ex ph T cs => mtbl u nt ex ph (T.subst2 f g) (cs.subst2 f g)
  | t => t

def inst : Tm → Tm → Nat → Tm
  | bv i, u, k => if i = k then u else if k < i then bv (i - 1) else bv i
  | sbv i, u, k => if i = k then slotOf u else if k < i then sbv (i - 1) else sbv i
  | tyc d ls, u, k => tyc d (ls.inst u k)
  | vc d c ls, u, k => vc d c (ls.inst u k)
  | cons h t, u, k => cons (h.inst u k) (t.inst u k)
  | bind m a r, u, k => bind m (a.inst u k) (r.inst u (k + 1))
  | app h a, u, k => app (h.inst u k) (a.inst u k)
  | tyCtor p, u, k => tyCtor (p.inst u k)
  | valCtor p, u, k => valCtor (p.inst u k)
  | predates A x L, u, k => predates (A.inst u k) (x.inst u k) (L.inst u k)
  | subterm A a B b, u, k => subterm (A.inst u k) (a.inst u k) (B.inst u k) (b.inst u k)
  | fn l np t uf hm, u, k => fn (l.inst u k) np (t.inst u k) uf hm
  | mtbl a nt ex ph T cs, u, k => mtbl a nt ex ph (T.inst u k) (cs.inst u k)
  | t, _, _ => t

def size : Tm → Nat
  | tyc _ ls | vc _ _ ls => ls.size + 1
  | cons h t => h.size + t.size + 1
  | bind _ a r => a.size + r.size + 1
  | app h a => h.size + a.size + 1
  | tyCtor p | valCtor p => p.size + 1
  | predates A x L => A.size + x.size + L.size + 1
  | subterm A a B b => A.size + a.size + B.size + b.size + 1
  | fn l _ t _ _ => l.size + t.size + 1
  | mtbl _ _ _ _ T cs => T.size + cs.size + 1
  | _ => 1

def levels : Tm → List Nat
  | lvl n => [n]
  | tyc _ ls | vc _ _ ls => ls.levels
  | cons h t => h.levels ++ t.levels
  | bind _ a r => a.levels ++ r.levels
  | app h a => h.levels ++ a.levels
  | tyCtor p | valCtor p => p.levels
  | predates A x L => A.levels ++ x.levels ++ L.levels
  | subterm A a B b => A.levels ++ a.levels ++ B.levels ++ b.levels
  | fn l _ t _ _ => l.levels ++ t.levels
  | mtbl _ _ _ _ T cs => T.levels ++ cs.levels
  | clo e _ _ => e.levels
  | _ => []

def static (n : Nat) : Nat → Tm → Bool
  | _, fv i | _, sfv i => i < n
  | d, bv i | d, sbv i => i < d
  | d, tyc _ ls | d, vc _ _ ls => ls.static n d
  | d, cons h t => h.static n d && t.static n d
  | d, bind _ a r => a.static n d && r.static n (d + 1)
  | d, app h a => h.static n d && a.static n d
  | d, tyCtor p | d, valCtor p => p.static n d
  | d, predates A x L => A.static n d && x.static n d && L.static n d
  | d, subterm A a B b => A.static n d && a.static n d && B.static n d && b.static n d
  | d, fn l _ t _ _ => l.static n d && t.static n d
  | d, mtbl _ _ _ _ T cs => T.static n d && cs.static n d
  | _, nil | _, univ | _, level => true
  | _, lvl _ | _, tok | _, clo .. | _, nat _ | _, ptr _ | _, wld _ => false

def bound : Nat → Tm → Bool
  | d, bv i | d, sbv i => i < d
  | d, tyc _ ls | d, vc _ _ ls => ls.bound d
  | d, cons h t => h.bound d && t.bound d
  | d, bind _ a r => a.bound d && r.bound (d + 1)
  | d, app h a => h.bound d && a.bound d
  | d, tyCtor p | d, valCtor p => p.bound d
  | d, predates A x L => A.bound d && x.bound d && L.bound d
  | d, subterm A a B b => A.bound d && a.bound d && B.bound d && b.bound d
  | d, fn l _ t _ _ => l.bound d && t.bound d
  | d, mtbl _ _ _ _ T cs => T.bound d && cs.bound d
  | _, _ => true

def lc : Nat → Tm → Prop
  | _, fv _ | _, sfv _ => False
  | d, bv i | d, sbv i => i < d
  | d, tyc _ ls | d, vc _ _ ls => ls.lc d
  | d, cons h t => h.lc d ∧ t.lc d
  | d, bind _ a r => a.lc d ∧ r.lc (d + 1)
  | d, app h a => h.lc d ∧ a.lc d
  | d, tyCtor p | d, valCtor p => p.lc d
  | d, predates A x L => A.lc d ∧ x.lc d ∧ L.lc d
  | d, subterm A a B b => A.lc d ∧ a.lc d ∧ B.lc d ∧ b.lc d
  | d, fn l _ t _ _ => l.lc d ∧ t.lc d
  | d, mtbl _ _ _ _ T cs => T.lc d ∧ cs.lc d
  | _, _ => True

def fvs : Tm → List Nat
  | fv i | sfv i => [i]
  | tyc _ ls | vc _ _ ls => ls.fvs
  | cons h t => h.fvs ++ t.fvs
  | bind _ a r => a.fvs ++ r.fvs
  | app h a => h.fvs ++ a.fvs
  | tyCtor p | valCtor p => p.fvs
  | predates A x L => A.fvs ++ x.fvs ++ L.fvs
  | subterm A a B b => A.fvs ++ a.fvs ++ B.fvs ++ b.fvs
  | fn l _ t _ _ => l.fvs ++ t.fvs
  | mtbl _ _ _ _ T cs => T.fvs ++ cs.fvs
  | _ => []

def occ : Tm → List Nat
  | fv i => [i]
  | tyc _ ls | vc _ _ ls => ls.occ
  | cons h t => h.occ ++ t.occ
  | bind _ a r => a.occ ++ r.occ
  | app h a => h.occ ++ a.occ
  | tyCtor p | valCtor p => p.occ
  | predates A x L => A.occ ++ x.occ ++ L.occ
  | subterm A a B b => A.occ ++ a.occ ++ B.occ ++ b.occ
  | fn l _ t _ _ => l.occ ++ t.occ
  | mtbl _ _ _ _ T cs => T.occ ++ cs.occ
  | _ => []

def ofList : List Tm → Tm
  | [] => nil
  | t :: ts => cons t (ofList ts)

def toList : Tm → List Tm
  | cons h t => h :: t.toList
  | _ => []

def fvIdx : Tm → Option Nat
  | fv i => some i
  | _ => none

def isList : Tm → Bool
  | nil => true
  | cons _ t => t.isList
  | _ => false

def isTele : Tm → Bool
  | nil => true
  | bind _ _ r => r.isTele
  | _ => false

def len : Tm → Nat
  | cons _ t | bind _ _ t => t.len + 1
  | _ => 0

def uAt : Tm → Nat → Bool
  | bind k _ _, 0 => k.u
  | bind _ _ r, n + 1 => r.uAt n
  | _, _ => false

def peel : Tm → Tm → Tm
  | bind _ _ r, cons a as => (r.inst a 0).peel as
  | t, _ => t

def skip : Nat → Tm → Tm
  | n + 1, bind _ _ r => r.skip n
  | _, t => t

def ers : Tm → List Bool
  | bind k _ r => k.er :: r.ers
  | _ => []

def ntField (sig : Tm) : Option Nat :=
  match (List.range (sig.len - 1)).filter (fun j => !sig.ers.getD j true) with
  | [k] => some k
  | _ => none

inductive PSub : Tm → Tm → Prop
  | head : PSub h (cons h t)
  | tail : PSub t (cons h t)
  | app : PSub a (app h a)
  | trans : PSub a b → PSub b c → PSub a c

def strictSub (a : Tm) : Tm → Bool
  | cons h t => a == h || a == t || a.strictSub h || a.strictSub t
  | app _ x => a == x || a.strictSub x
  | _ => false

def env (ρ : List Tm) (i : Nat) : Tm := ρ.getD i nil

def valRet : Tm → Nat → Bool
  | bind _ _ r@(bind ..), n => r.valRet (n + 1)
  | bind (.ty ..) (app (tyc ..) _) nil, _ | bind (.ty ..) (app (fv _) _) nil, _ => true
  | bind (.ty ..) (app (bv k) _) nil, n => n ≤ k
  | _, _ => false

end Tm

def natTy (d : Nat) : Tm := .app (.tyc d .nil) .nil

def natTm' (d : Nat) : Nat → Tm
  | 0 => .app (.vc d 0 .nil) .nil
  | k + 1 => .app (.vc d 1 .nil) (.cons (natTm' d k) .nil)

theorem Tm.toList_ofList : ∀ l : List Tm, (Tm.ofList l).toList = l
  | [] => rfl
  | _ :: l => by simp [Tm.ofList, Tm.toList, Tm.toList_ofList l]

def holeBase : Nat := 2 ^ 40

def Tm.hole : Tm := .fv holeBase

def Tm.close (i : Nat) : Nat → Tm → Tm
  | k, .fv j => if j = i then .bv k else .fv j
  | k, .sfv j => if j = i then .sbv k else .sfv j
  | k, .tyc d ls => .tyc d (ls.close i k)
  | k, .vc d c ls => .vc d c (ls.close i k)
  | k, .cons h t => .cons (h.close i k) (t.close i k)
  | k, .bind m a r => .bind m (a.close i k) (r.close i (k + 1))
  | k, .app h a => .app (h.close i k) (a.close i k)
  | k, .tyCtor p => .tyCtor (p.close i k)
  | k, .valCtor p => .valCtor (p.close i k)
  | k, .predates A x L => .predates (A.close i k) (x.close i k) (L.close i k)
  | k, .subterm A a B b => .subterm (A.close i k) (a.close i k) (B.close i k) (b.close i k)
  | k, .fn l np t u hm => .fn (l.close i k) np (t.close i k) u hm
  | k, .mtbl u nt ex ph T cs => .mtbl u nt ex ph (T.close i k) (cs.close i k)
  | _, t => t

inductive Dec where
  | none
  | predates (p : Tm)
  | subterm (pos : Nat) (p : Tm)
  deriving Repr, Inhabited, DecidableEq

inductive Prim where
  | tm (t : Tm)
  | lit (t : Tm)
  | proveSubterm (a b : Tm)
  | provePredates (x L : Nat)
  | predatesTrans (p q : Tm)
  | subtermTrans (p q : Tm)
  | predatesSubterm (p q : Tm)
  | mtblOf (d : Nat) (ls : Tm)
  | assert (t A : Tm)
  | coerce (a b p : Tm)
  | coerRefl (s e : Tm)
  | deleOf (g t : Nat)
  | coerOf (p : Tm)
  | coerSym (p : Tm)
  | coerTrans (p q : Tm)
  | coerShare (p : Tm)
  | coerWrap (s C args : Tm)
  | coerCtor (s C srcs tgts ps : Tm)
  | axm (A : Tm)
  | atom (d : Nat)
  | wAsk (w req : Tm)
  | wNext (w : Tm)
  | atomEq (d q : Nat) (a b : Tm)
  | place (a T : Tm)
  | unplace (a v : Tm)
  | placedEq (q : Nat) (A a b : Tm)
  | num (d n : Nat)
  deriving Repr, Inhabited, DecidableEq

inductive Mark where
  | reuse (uniq : Bool)
  | cellOf
  | alloc
  | write (uniq : Bool)
  | skip
  | uq (ms : List Bool)
  | uqScr
  | rebind
  deriving Repr, Inhabited, DecidableEq

inductive Chk where
  | mark (m : Mark)
  | is
  | ty
  | rt
  | opn (er : Bool)
  | cm
  | slf
  deriving Repr, Inhabited, DecidableEq

inductive Core where
  | ret (ts : Tm)
  | call (f : Tm) (dec : Dec) (args : Tm) (er : Bool) (ms : List Bool) (ve : Option (List Bool)) (rest : Core)
  | mtch (s : Tm) (rets : Tm) (brs : List (Nat × Nat × Tm × Core)) (els : Option Core) (er : Bool) (rest : Core)
  | prim (p : Prim) (er : Bool) (rest : Core)
  | wdo (w req : Tm) (rest : Core)
  | defLvl (rest : Core)
  | defFns (gid : Nat) (rest : Core)
  | chk (k : Chk) (a b : Tm) (rest : Core)
  | case (s : Tm) (brs : List (Nat × Nat × Tm × Core)) (els : Option Core) (er nt : Bool)
  | seq (R : Tm) (body rest : Core)
  | absurd (body : Core)
  | dead
  deriving Repr, Inhabited

mutual
def Core.noRet : Core → Bool
  | .ret _ => false
  | .call _ _ _ _ _ _ r | .mtch _ _ _ _ _ r | .prim _ _ r | .wdo _ _ r | .defLvl r | .defFns _ r | .chk _ _ _ r => r.noRet
  | .case _ brs els _ _ => Core.armsNoRet brs && Core.optNoRet els
  | .seq _ body rest => body.noRet || rest.noRet
  | .absurd _ | .dead => true

def Core.armsNoRet : List (Nat × Nat × Tm × Core) → Bool
  | [] => true
  | (_, _, _, b) :: t => b.noRet && Core.armsNoRet t

def Core.optNoRet : Option Core → Bool
  | none => true
  | some e => e.noRet
end

def Core.real (c : Core) : Bool := !c.noRet

abbrev Br := Nat × Nat × Tm × Core

def lookupBr (brs : List Br) (c : Nat) : Option Core := (brs.find? (·.2.1 == c)).map (·.2.2.2)

theorem sizeOf_lookupBr {brs : List Br} {c : Nat} {body : Core}
    (h : lookupBr brs c = some body) : sizeOf body < sizeOf brs := by
  simp only [lookupBr, Option.map_eq_some_iff] at h
  obtain ⟨⟨x, y, w, z⟩, he, rfl⟩ := h
  have := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some he)
  simp at this ⊢; omega

def selectBr (brs : List Br) (els : Option Core) (c : Nat) (vs : List Tm) :
    Option (List Tm × Core) :=
  match lookupBr brs c with
  | some body => some (vs, body)
  | none => els.map (([], ·))

theorem sizeOf_selectBr {brs : List Br} {els : Option Core} {c : Nat} {vs pre : List Tm}
    {body : Core} (h : selectBr brs els c vs = some (pre, body)) : sizeOf body < sizeOf brs + sizeOf els := by
  unfold selectBr at h
  split at h
  · rename_i hb; simp at h; obtain ⟨-, rfl⟩ := h; have := sizeOf_lookupBr hb; omega
  · cases els <;> simp at h; obtain ⟨-, rfl⟩ := h; simp; omega

def realCount (brs : List Br) (els : Option Core) : Nat :=
  (brs.filter (·.2.2.2.real)).length + (els.filter Core.real).isSome.toNat

structure FnDef where
  er : Bool := false
  np : Nat
  tele : Tm
  body : Core
  dele : Option Nat := none
  u : Bool := false
  hm : List Bool := []
  atf : Bool := false
  deriving Repr, Inhabited

structure Group where
  ers : List Bool := []
  ghost : Bool := false
  lvl : Nat
  fns : List FnDef
  caps : List (Nat × Bool) := []
  deriving Repr, Inhabited

structure Adt where
  params : Tm
  ctors : List Tm
  name : String := ""
  ctorNames : List String := []
  lifted : Nat := 0
  phantom : List Bool := []
  union : Bool := false
  newtype : Bool := false
  extern : Bool := false
  coercible : Bool := false
  opq : Bool := false
  deriving Repr, Inhabited

def Tm.coer (d : Nat) (sa A a sb B b : Tm) : Tm := .app (.tyc d .nil) (.ofList [sa, A, a, sb, B, b])

def sharingD : Nat := 1

def sharedTm : Tm := .app (.vc sharingD 1 .nil) .nil

def uniqueTm : Tm := .app (.vc sharingD 0 .nil) .nil

def sideTm (u : Bool) : Tm := if u then uniqueTm else sharedTm

def Adt.mtbl (D : Adt) (d : Nat) (ls : Tm) : Tm :=
  .mtbl D.union D.newtype D.extern ((List.range D.ctors.length).map (D.phantom.getD · false)) (.tyc d ls)
    (.ofList ((List.range D.ctors.length).map (.vc d · ls)))

def iterFix {α : Type} [BEq α] (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => let y := f x; if y == x then x else iterFix f n y

def Adt.isoSize (D : Adt) (d : Nat) : Nat := D.params.size + (D.mtbl d .nil).size + (D.ctors.map Tm.size).sum

def isoFuelOf (decls ctors size : Nat) : Nat := let n := decls + ctors + 2; n * (size + n) + 1

def isoFuelOfAdts (adts : Array Adt) : Nat :=
  isoFuelOf adts.size (adts.toList.map (·.ctors.length)).sum (adts.toList.zipIdx.map fun (D, d) => D.isoSize d).sum

structure Prog where
  adts : Array Adt
  groups : List Group
  main : Core
  hidden : Nat := 0
  natD : Option Nat := none
  isoFuel : Nat := 0
  worldD : Option Nat := none
  requestD : Option Nat := none
  ask : Nat → Nat → Tm × Tm := fun _ _ => (.tok, .tok)
  placedD : Option Nat := none
  deriving Inhabited

def Tm.noClo : Tm → Bool
  | .clo .. => false
  | .cons a b | .app a b | .bind _ a b => a.noClo && b.noClo
  | .tyc _ a | .vc _ _ a | .tyCtor a | .valCtor a => a.noClo
  | .predates a b c => a.noClo && b.noClo && c.noClo
  | .subterm a b c d => a.noClo && b.noClo && c.noClo && d.noClo
  | .fn a _ b _ _ | .mtbl _ _ _ _ a b => a.noClo && b.noClo
  | _ => true

mutual
def Tm.sdata : Tm → Bool
  | .app (.vc _ _ .nil) fs => Tm.sdataL fs
  | .nat _ | .tok | .wld _ | .nil | .vc _ _ .nil => true
  | _ => false

def Tm.sdataL : Tm → Bool
  | .cons a as => a.sdata && Tm.sdataL as
  | .nil => true
  | _ => false
end

def Tm.wnext : Tm → Tm
  | .wld k => .wld (k + 1)
  | _ => .tok

def Prog.answer (P : Prog) : Tm → Tm → Tm × Tm
  | .wld k, .app (.vc _ c _) _ => P.ask k c
  | _, _ => (.tok, .tok)

def marks : Tm → Nat → List Bool
  | .bind k _ r, n + 1 => k.marked :: marks r n
  | _, _ => []

def Prog.k (P : Prog) : Nat :=
  P.groups.foldr (fun G acc => G.fns.foldr (fun F acc => max ((marks F.tele F.np).count true) acc) acc) 0

def eqSig (q : Nat) (k1 k2 k3 : Ent) : Tm :=
  .bind k1 .univ (.bind k2 (.bv 0) (.bind k3 (.app (.tyc q .nil) (.cons (.bv 1) (.cons (.bv 0) (.cons (.bv 0) .nil)))) .nil))

def Prog.ctor (P : Prog) (d c : Nat) : Option Tm := (P.adts[d]?).bind (·.ctors[c]?)

def Prog.lifted (P : Prog) (d : Nat) : Nat := ((P.adts[d]?).map (·.lifted)).getD 0

def Prog.phantom (P : Prog) (d c : Nat) : Bool := ((P.adts[d]?).bind (·.phantom[c]?)).getD false

def Prog.isNt (P : Prog) (d : Nat) : Bool := ((P.adts[d]?).map (·.newtype)).getD false

def Prog.slotOK (P : Prog) : Bool := match P.adts[slotD]? with
  | some D => (match D.ctors with
      | [.bind (.ty ..) (.app (.tyc d .nil) .nil) .nil] => d == slotD
      | _ => false) && D.lifted == 0 && !D.newtype && !D.opq && !P.phantom slotD 0
  | none => false

def Prog.wrapField (P : Prog) (d c : Nat) : Option Nat :=
  if P.isNt d && !P.phantom d c then (P.ctor d c).bind fun sig => (sig.skip (P.lifted d)).ntField else none

mutual
def Prog.unwrapArgs (P : Prog) : Tm → Tm
  | .cons a as => .cons (P.unwrap a) (P.unwrapArgs as)
  | t => t

def Prog.unwrap (P : Prog) : Tm → Tm
  | .app (.vc d c ls) args => match P.wrapField d c with
    | some k => (P.unwrapArgs args).toList.getD k .nil
    | none => .app (.vc d c ls) (P.unwrapArgs args)
  | t => t
end

def realBr (brs : List Br) (els : Option Core) : Option (List Tm × Core) :=
  match brs.filter (·.2.2.2.real), els with
  | [(n, _, _, body)], _ => some (List.replicate n .tok, body)
  | [], some e => some ([], e)
  | _, _ => none

theorem sizeOf_realBr {brs : List Br} {els : Option Core} {pre : List Tm} {body : Core}
    (h : realBr brs els = some (pre, body)) : sizeOf body < sizeOf brs + sizeOf els := by
  unfold realBr at h
  split at h
  · rename_i n c k b hf
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hm : (n, c, k, b) ∈ brs.filter (·.2.2.2.real) := by rw [hf]; simp
    have := List.sizeOf_lt_of_mem (List.mem_filter.mp hm).1
    simp at this ⊢; omega
  · simp at h; obtain ⟨-, rfl⟩ := h; simp; omega
  · cases h

def FnDef.type (G : Group) (F : FnDef) : Tm := .fn (.fv G.lvl) F.np F.tele F.u F.hm

def closures (env : List Tm) (gid : Nat) (G : Group) : List Tm :=
  (List.range G.fns.length).map (.clo (.ofList env) gid)

def markedIndex : Tm → Nat → Nat → Option Nat
  | .bind k _ _, 0, i => if k.marked then some i else none
  | .bind k _ r, pos + 1, i => markedIndex r pos (if k.marked then i + 1 else i)
  | _, _, _ => none

def markedArgs : Tm → Tm → List Tm
  | .bind k _ r, .cons a as => if k.marked then a :: markedArgs r as else markedArgs r as
  | _, _ => []

end Minimal
