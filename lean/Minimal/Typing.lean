import Minimal.Unify

namespace Minimal

structure Ctx where
  tys : List Tm
  σ : Nat → Option Tm := fun _ => none
  mints : List Nat := []
  cur : Option Nat := none
  subs : List Nat := []

namespace Ctx

def n (Γ : Ctx) : Nat := Γ.tys.length

def canon (Γ : Ctx) (t : Tm) : Tm := t.subst fun i => (Γ.σ i).getD (.fv i)

def push (Γ : Ctx) (T : Tm) : Ctx := { Γ with tys := Γ.tys ++ [T] }

def openTele : Ctx → Tm → Nat → Ctx × Tm
  | Γ, .bind _ A r, m + 1 => (Γ.push A).openTele (r.inst (.fv Γ.n) 0) m
  | Γ, t, _ => (Γ, t)

def pushTele (Γ : Ctx) (R : Tm) : Ctx := (Γ.openTele R R.len).1

def withRule (Γ : Ctx) (e : Nat) (t : Tm) : Ctx := { Γ with σ := fun i => if i = e then some t else Γ.σ i }

def pushPrim (Γ : Ctx) (T : Tm) : Prim → Ctx
  | .tm t => (Γ.push T).withRule Γ.n (Γ.canon t)
  | _ => Γ.push T

def pushMint (Γ : Ctx) : Ctx := { Γ.push .level with mints := Γ.mints ++ [Γ.n] }

def pushFns (Γ : Ctx) (G : Group) : Ctx := { Γ with tys := Γ.tys ++ G.fns.map (FnDef.type G) }

def fields (Γ : Ctx) (m : Nat) : Tm := .ofList ((List.range m).map fun j => .fv (Γ.n + j))

def body (Γ : Ctx) (G : Group) (F : FnDef) : Ctx × Tm :=
  let Γ1 := Γ.pushFns G
  let (Γ2, rem) := Γ1.openTele F.tele F.np
  ({ Γ2 with cur := some G.lvl,
             subs := (markedArgs F.tele (Γ1.fields F.np)).filterMap Tm.fvIdx },
   rem)

def branch (Γ : Ctx) (s : Tm) (d c : Nat) (idx sig : Tm) : Ctx × UResult :=
  let m := sig.len - 1
  let (Γf, rem) := Γ.openTele sig m
  match rem with
  | .bind _ R .nil =>
    (Γf, unify Γf.n Γf.σ [] [(Γ.canon s, .con d c (Γ.fields m)), (Γ.canon (.ty d idx), Γf.canon R)])
  | _ => (Γf, .unknown)

end Ctx

variable (P : Prog)

mutual
inductive TmTy : Ctx → Tm → Tm → Prop
  | fv : Γ.tys[i]? = some T → TmTy Γ (.fv i) T
  | univ : TmTy Γ .univ .univ
  | level : TmTy Γ .level .univ
  | ty : P.adts[d]? = some D → ArgsTy Γ args D.params .nil → TmTy Γ (.ty d args) .univ
  | con : P.ctor d c = some sig → ArgsTy Γ args sig (.bind m T .nil) → TmTy Γ (.con d c args) T
  | predates : TmTy Γ A U → Γ.canon U = .univ → TmTy Γ x X → Γ.canon X = Γ.canon A →
      TmTy Γ L K → Γ.canon K = .level → TmTy Γ (.predates A x L) .univ
  | subterm : TmTy Γ A U → Γ.canon U = .univ → TmTy Γ a A' → Γ.canon A' = Γ.canon A →
      TmTy Γ B V → Γ.canon V = .univ → TmTy Γ b B' → Γ.canon B' = Γ.canon B →
      TmTy Γ (.subterm A a B b) .univ
  | fn : TmTy Γ l K → Γ.canon K = .level → TeleOK Γ t → np ≤ t.len →
      (Tm.fn l np t).static Γ.n 0 → TmTy Γ (.fn l np t) .univ

inductive ArgsTy : Ctx → Tm → Tm → Tm → Prop
  | nil : ArgsTy Γ .nil t t
  | cons : TmTy Γ a T → Γ.canon T = Γ.canon A → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind m A r) out

inductive TeleOK : Ctx → Tm → Prop
  | nil : TeleOK Γ .nil
  | cons : TmTy Γ A U → Γ.canon U = .univ → TeleOK (Γ.push A) (r.inst (.fv Γ.n) 0) →
      TeleOK Γ (.bind m A r)
end

inductive DecOK : Ctx → Dec → Tm → Tm → Tm → Prop
  | top : Γ.cur = none → DecOK Γ .none l t args
  | lower : Γ.cur = some c → TmTy P Γ p Pt → Γ.canon Pt = .predates A x L →
      Γ.canon x = Γ.canon l → Γ.canon L = Γ.canon (.fv c) → DecOK Γ (.predates p) l t args
  | same : Γ.cur = some c → Γ.canon l = Γ.canon (.fv c) → markedIndex t pos 0 = some i →
      (markedArgs t args)[i]? = some a → Γ.subs[i]? = some s →
      (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
        Γ.canon a' = Γ.canon (.fv s')) →
      TmTy P Γ p Pt → Γ.canon Pt = .subterm A a0 B b0 →
      Γ.canon a0 = Γ.canon a → Γ.canon b0 = Γ.canon (.fv s) → DecOK Γ (.subterm pos p) l t args

inductive PrimTy : Ctx → Prim → Tm → Prop
  | tm : TmTy P Γ t T → PrimTy Γ (.tm t) T
  | proveSubterm : TmTy P Γ a A → TmTy P Γ b B → (Γ.canon a).strictSub (Γ.canon b) →
      PrimTy Γ (.proveSubterm a b) (.subterm A a B b)
  | provePredates : x < L → L ∈ Γ.mints → Γ.tys[x]? = some X →
      PrimTy Γ (.provePredates x L) (.predates X (.fv x) (.fv L))
  | predatesTrans : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .predates A a l1 →
      Γ.canon Qt = .predates C l1 l2 → PrimTy Γ (.predatesTrans p q) (.predates A a l2)
  | subtermTrans : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .subterm A a B b →
      Γ.canon Qt = .subterm B b C c → PrimTy Γ (.subtermTrans p q) (.subterm A a C c)
  | predatesSubterm : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .predates A a l →
      Γ.canon Qt = .subterm B b A a → PrimTy Γ (.predatesSubterm p q) (.predates B b l)

mutual
inductive CoreTy : Nat → Ctx → Core → Tm → Prop
  | ret : ArgsTy P Γ ts rets .nil → CoreTy b Γ (.ret ts) rets
  | call : TmTy P Γ f Ft → Γ.canon Ft = .fn l np t → t.isTele → ArgsTy P Γ args t outs → args.len = np →
      DecOK P Γ dec l t args → outs.len = n → CoreTy b (Γ.pushTele outs) rest rets →
      CoreTy b Γ (.call f dec args n rest) rets
  | mtch : TmTy P Γ s St → Γ.canon St = .ty d idx → P.adts[d]? = some D →
      (∀ e ∈ brs, e.1 = d ∧ e.2.1 < D.ctors.length) → TeleOK P Γ R → R.static Γ.n 0 → R.isTele →
      (∀ (c : Nat) sig, D.ctors[c]? = some sig → BranchOK b Γ s d idx c sig R (lookupBr brs c)) →
      CoreTy b (Γ.pushTele R) rest rets → CoreTy b Γ (.mtch s R brs rest) rets
  | prim : PrimTy P Γ p T → CoreTy b (Γ.pushPrim T p) rest rets → CoreTy b Γ (.prim p rest) rets
  | defLvl : CoreTy b Γ.pushMint rest rets → CoreTy b Γ (.defLvl rest) rets
  | defFns : gid < b → P.groups[gid]? = some G → GroupOK gid Γ G →
      CoreTy b (Γ.pushFns G) rest rets → CoreTy b Γ (.defFns gid rest) rets

inductive BranchOK : Nat → Ctx → Tm → Nat → Tm → Nat → Tm → Tm → Option Core → Prop
  | live : Γ.branch s d c idx sig = (Γf, .ok σ) → CoreTy b { Γf with σ := σ } body R →
      BranchOK b Γ s d idx c sig R (some body)
  | dead : (Γ.branch s d c idx sig).2 = .contra → BranchOK b Γ s d idx c sig R none

inductive GroupOK : Nat → Ctx → Group → Prop
  | mk {G : Group} : Γ.tys[G.lvl]? = some K → Γ.canon K = .level →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → TmTy P Γ (F.type G) .univ) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → (marks F.tele F.np).count true ≤ P.k) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → CoreTy gid (Γ.body G F).1 F.body (Γ.body G F).2) →
      GroupOK gid Γ G
end

end Minimal
