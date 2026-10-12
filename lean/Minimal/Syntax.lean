namespace Minimal

inductive Ent where
  | ty (mark : Bool)
  | is
  deriving DecidableEq, Repr, Inhabited

def Ent.marked : Ent → Bool
  | ty m => m
  | is => false

inductive Tm where
  | fv (i : Nat)
  | bv (i : Nat)
  | nil
  | cons (h t : Tm)
  | bind (k : Ent) (ty rest : Tm)
  | ty (d : Nat) (args : Tm)
  | con (d c : Nat) (args : Tm)
  | univ
  | level
  | predates (A x L : Tm)
  | subterm (A a B b : Tm)
  | fn (l : Tm) (np : Nat) (tele : Tm)
  | lvl (n : Nat)
  | tok
  | clo (env : Tm) (gid j : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Tm

def subst (f : Nat → Tm) : Tm → Tm
  | fv i => f i
  | cons h t => cons (h.subst f) (t.subst f)
  | bind m a r => bind m (a.subst f) (r.subst f)
  | ty d a => ty d (a.subst f)
  | con d c a => con d c (a.subst f)
  | predates A x L => predates (A.subst f) (x.subst f) (L.subst f)
  | subterm A a B b => subterm (A.subst f) (a.subst f) (B.subst f) (b.subst f)
  | fn l np t => fn (l.subst f) np (t.subst f)
  | t => t

def inst : Tm → Tm → Nat → Tm
  | bv i, u, k => if i = k then u else if k < i then bv (i - 1) else bv i
  | cons h t, u, k => cons (h.inst u k) (t.inst u k)
  | bind m a r, u, k => bind m (a.inst u k) (r.inst u (k + 1))
  | ty d a, u, k => ty d (a.inst u k)
  | con d c a, u, k => con d c (a.inst u k)
  | predates A x L, u, k => predates (A.inst u k) (x.inst u k) (L.inst u k)
  | subterm A a B b, u, k => subterm (A.inst u k) (a.inst u k) (B.inst u k) (b.inst u k)
  | fn l np t, u, k => fn (l.inst u k) np (t.inst u k)
  | t, _, _ => t

def size : Tm → Nat
  | cons h t => h.size + t.size + 1
  | bind _ a r => a.size + r.size + 1
  | ty _ a => a.size + 1
  | con _ _ a => a.size + 1
  | predates A x L => A.size + x.size + L.size + 1
  | subterm A a B b => A.size + a.size + B.size + b.size + 1
  | fn l _ t => l.size + t.size + 1
  | clo e _ _ => e.size + 1
  | _ => 1

def levels : Tm → List Nat
  | lvl n => [n]
  | cons h t => h.levels ++ t.levels
  | bind _ a r => a.levels ++ r.levels
  | ty _ a => a.levels
  | con _ _ a => a.levels
  | predates A x L => A.levels ++ x.levels ++ L.levels
  | subterm A a B b => A.levels ++ a.levels ++ B.levels ++ b.levels
  | fn l _ t => l.levels ++ t.levels
  | clo e _ _ => e.levels
  | _ => []

def static (n : Nat) : Nat → Tm → Bool
  | _, fv i => i < n
  | d, bv i => i < d
  | d, cons h t => h.static n d && t.static n d
  | d, bind _ a r => a.static n d && r.static n (d + 1)
  | d, ty _ a => a.static n d
  | d, con _ _ a => a.static n d
  | d, predates A x L => A.static n d && x.static n d && L.static n d
  | d, subterm A a B b => A.static n d && a.static n d && B.static n d && b.static n d
  | d, fn l _ t => l.static n d && t.static n d
  | _, nil | _, univ | _, level => true
  | _, lvl _ | _, tok | _, clo .. => false

def bound : Nat → Tm → Bool
  | d, bv i => i < d
  | d, cons h t => h.bound d && t.bound d
  | d, bind _ a r => a.bound d && r.bound (d + 1)
  | d, ty _ a => a.bound d
  | d, con _ _ a => a.bound d
  | d, predates A x L => A.bound d && x.bound d && L.bound d
  | d, subterm A a B b => A.bound d && a.bound d && B.bound d && b.bound d
  | d, fn l _ t => l.bound d && t.bound d
  | _, _ => true

def lc : Nat → Tm → Prop
  | _, fv _ => False
  | d, bv i => i < d
  | d, cons h t => h.lc d ∧ t.lc d
  | d, bind _ a r => a.lc d ∧ r.lc (d + 1)
  | d, ty _ a => a.lc d
  | d, con _ _ a => a.lc d
  | d, predates A x L => A.lc d ∧ x.lc d ∧ L.lc d
  | d, subterm A a B b => A.lc d ∧ a.lc d ∧ B.lc d ∧ b.lc d
  | d, fn l _ t => l.lc d ∧ t.lc d
  | _, _ => True

def fvs : Tm → List Nat
  | fv i => [i]
  | cons h t => h.fvs ++ t.fvs
  | bind _ a r => a.fvs ++ r.fvs
  | ty _ a => a.fvs
  | con _ _ a => a.fvs
  | predates A x L => A.fvs ++ x.fvs ++ L.fvs
  | subterm A a B b => A.fvs ++ a.fvs ++ B.fvs ++ b.fvs
  | fn l _ t => l.fvs ++ t.fvs
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

inductive PSub : Tm → Tm → Prop
  | head : PSub h (cons h t)
  | tail : PSub t (cons h t)
  | ty : PSub a (ty d a)
  | con : PSub a (con d c a)
  | trans : PSub a b → PSub b c → PSub a c

def strictSub (a : Tm) : Tm → Bool
  | cons h t => a == h || a == t || a.strictSub h || a.strictSub t
  | ty _ x | con _ _ x => a == x || a.strictSub x
  | _ => false

def env (ρ : List Tm) (i : Nat) : Tm := ρ.getD i nil

end Tm

inductive Dec where
  | none
  | predates (p : Tm)
  | subterm (pos : Nat) (p : Tm)
  deriving Repr, Inhabited

inductive Prim where
  | tm (t : Tm)
  | proveSubterm (a b : Tm)
  | provePredates (x L : Nat)
  | predatesTrans (p q : Tm)
  | subtermTrans (p q : Tm)
  | predatesSubterm (p q : Tm)
  deriving Repr, Inhabited

inductive Core where
  | ret (ts : Tm)
  | call (f : Tm) (dec : Dec) (args : Tm) (n : Nat) (rest : Core)
  | mtch (s : Tm) (rets : Tm) (brs : List (Nat × Nat × Core)) (rest : Core)
  | prim (p : Prim) (rest : Core)
  | defLvl (rest : Core)
  | defFns (gid : Nat) (rest : Core)
  | chk (isType : Bool) (a b : Tm) (rest : Core)
  deriving Repr, Inhabited

def lookupBr (brs : List (Nat × Nat × Core)) (c : Nat) : Option Core := (brs.find? (·.2.1 == c)).map (·.2.2)

theorem sizeOf_lookupBr {brs : List (Nat × Nat × Core)} {c : Nat} {body : Core}
    (h : lookupBr brs c = some body) : sizeOf body < sizeOf brs := by
  simp only [lookupBr, Option.map_eq_some_iff] at h
  obtain ⟨⟨x, y, z⟩, he, rfl⟩ := h
  have := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some he)
  simp at this ⊢; omega

structure FnDef where
  np : Nat
  tele : Tm
  body : Core
  deriving Repr, Inhabited

structure Group where
  lvl : Nat
  fns : List FnDef
  deriving Repr, Inhabited

structure Adt where
  params : Tm
  ctors : List Tm
  name : String := ""
  ctorNames : List String := []
  deriving Repr, Inhabited

structure Prog where
  adts : List Adt
  groups : List Group
  main : Core
  deriving Repr, Inhabited

def marks : Tm → Nat → List Bool
  | .bind k _ r, n + 1 => k.marked :: marks r n
  | _, _ => []

def Prog.k (P : Prog) : Nat :=
  P.groups.foldr (fun G acc => G.fns.foldr (fun F acc => max ((marks F.tele F.np).count true) acc) acc) 0

def Prog.ctor (P : Prog) (d c : Nat) : Option Tm := (P.adts[d]?).bind (·.ctors[c]?)

def FnDef.type (G : Group) (F : FnDef) : Tm := .fn (.fv G.lvl) F.np F.tele

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
