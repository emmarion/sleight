import Minimal.Unify

namespace Minimal

structure Ctx where
  tys : List Tm
  σ : Nat → Option Tm := fun _ => none
  mints : List Nat := []
  cur : Option Nat := none
  subs : List Nat := []
  er : Nat → Bool := fun _ => true
  ghost : Bool := false

namespace Ctx

def n (Γ : Ctx) : Nat := Γ.tys.length

def canon (Γ : Ctx) (t : Tm) : Tm := t.subst fun i => (Γ.σ i).getD (.fv i)

def push (Γ : Ctx) (T : Tm) (e : Bool := false) : Ctx :=
  { Γ with tys := Γ.tys ++ [T], er := fun i => if i = Γ.n then e else Γ.er i }

def withRule (Γ : Ctx) (e : Nat) (t : Tm) : Ctx := { Γ with σ := fun i => if i = e then some t else Γ.σ i }

def pushPrim (Γ : Ctx) (T : Tm) (er : Bool) : Prim → Ctx
  | .tm t => (Γ.push T er).withRule Γ.n (Γ.canon t)
  | _ => Γ.push T er

def pushEnt (Γ : Ctx) : Ent → Tm → Ctx
  | .ty _ e, A => Γ.push A e
  | .is e, x => (Γ.push .nil e).withRule Γ.n (Γ.canon x)

def openTele : Ctx → Tm → Nat → Ctx × Tm
  | Γ, .bind k A r, m + 1 => (Γ.pushEnt k A).openTele (r.inst (.fv Γ.n) 0) m
  | Γ, t, _ => (Γ, t)

def setErs (Γ Γ' : Ctx) : Option (List Bool) → Ctx
  | none => Γ'
  | some ms => { Γ' with er := fun i => if Γ.n ≤ i then ms.getD (i - Γ.n) true else Γ'.er i }

def pushTele (Γ : Ctx) (R : Tm) (ov : Option (List Bool) := none) : Ctx := Γ.setErs (Γ.openTele R R.len).1 ov

def pushMint (Γ : Ctx) : Ctx := { Γ.push .level true with mints := Γ.mints ++ [Γ.n] }

def pushFns (Γ : Ctx) (G : Group) : Ctx :=
  { Γ with tys := Γ.tys ++ G.fns.map (FnDef.type G),
           er := fun i => if Γ.n ≤ i then (G.fns[i - Γ.n]?.map (·.er)).getD true else Γ.er i }

def fields (Γ : Ctx) (m : Nat) : Tm := .ofList ((List.range m).map fun j => .fv (Γ.n + j))

def body (Γ : Ctx) (G : Group) (F : FnDef) : Ctx × Tm :=
  let Γ1 := Γ.pushFns G
  let (Γ2, rem) := Γ1.openTele F.tele F.np
  ({ Γ2 with cur := some G.lvl, ghost := Γ.ghost || F.er,
             subs := (markedArgs F.tele (Γ1.fields F.np)).filterMap Tm.fvIdx },
   rem)

def branch (Γ : Ctx) (s : Tm) (d c : Nat) (idx sig : Tm) : Ctx × UResult :=
  let m := sig.len - 1
  let (Γf, rem) := Γ.openTele sig m
  match rem with
  | .bind (.ty _ _) R .nil =>
    (Γf, unify Γf.n Γf.σ [] [(Γ.canon s, Γf.canon (.app (.vc d c) (Γ.fields m))), (Γ.canon (.app (.tyc d) idx), Γf.canon R)])
  | _ => (Γf, .unknown)

end Ctx

def compat : List Bool → Tm → Bool
  | m :: ms, .bind k _ r => (m || !k.er) && compat ms r
  | _, _ => true

variable (P : Prog)

mutual
def rt (Γ : Ctx) : Tm → Bool
  | .fv i => !Γ.er i
  | .app (.vc d c) args => match P.ctor d c with
    | some sig => !P.phantom d c && rtArgs Γ args sig
    | none => false
  | .app (.fv i) args => match (Γ.tys[i]?).map Γ.canon with
    | some (.valCtor sig) => !Γ.er i && rtArgs Γ args sig
    | _ => false
  | .vc d c => !P.phantom d c
  | _ => false

def rtArgs (Γ : Ctx) : Tm → Tm → Bool
  | .nil, _ => true
  | .cons a as, .bind k _ r => (k.er || rt Γ a) && rtArgs Γ as r
  | _, _ => false
end

def Ctx.ok (Γ : Ctx) (b : Bool) : Bool := Γ.ghost || b

def Prim.rt (Γ : Ctx) : Prim → Bool
  | .tm t | .lit t => Minimal.rt P Γ t
  | _ => false

mutual
inductive TmTy : Ctx → Tm → Tm → Prop
  | fv : Γ.tys[i]? = some T → TmTy Γ (.fv i) T
  | fvIs : Γ.tys[i]? = some .nil → Γ.σ i = some t → TmTy Γ t T → TmTy Γ (.fv i) T
  | univ : TmTy Γ .univ .univ
  | level : TmTy Γ .level .univ
  | tyc : P.adts[d]? = some D → TmTy Γ (.tyc d) (.tyCtor D.params)
  | vc : P.ctor d c = some sig → TmTy Γ (.vc d c) (.valCtor sig)
  | tyApp : TmTy Γ h H → Γ.canon H = .tyCtor ps → ArgsTy Γ args ps .nil → TmTy Γ (.app h args) .univ
  | vcApp : TmTy Γ h H → Γ.canon H = .valCtor sig → ArgsTy Γ args sig (.bind (.ty m e) T .nil) →
      TmTy Γ (.app h args) T
  | tyCtor : TeleOK Γ ps → (Tm.tyCtor ps).static Γ.n 0 → TmTy Γ (.tyCtor ps) .univ
  | valCtor : TeleOK Γ sig → (Tm.valCtor sig).static Γ.n 0 → sig.valRet 0 → TmTy Γ (.valCtor sig) .univ
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
      ArgsTy Γ (.cons a as) (.bind (.ty m e) A r) out
  | isCons : TmTy Γ a T → Γ.canon a = Γ.canon e → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind (.is _) e r) out
  | anyCons : TmTy Γ a T → ArgsTy Γ as (r.inst a 0) out → ArgsTy Γ (.cons a as) (.bind (.ty m e) .nil r) out

inductive TeleOK : Ctx → Tm → Prop
  | nil : TeleOK Γ .nil
  | cons : TmTy Γ A U → Γ.canon U = .univ → TeleOK (Γ.push A) (r.inst (.fv Γ.n) 0) →
      TeleOK Γ (.bind (.ty m e) A r)
  | isCons : TmTy Γ e T → TeleOK (Γ.pushEnt (.is false) e) (r.inst (.fv Γ.n) 0) → TeleOK Γ (.bind (.is _) e r)
end

inductive DecOK : Ctx → Dec → Tm → Tm → Tm → Prop
  | top : Γ.cur = none → DecOK Γ .none l t args
  | lower : Γ.cur = some c → TmTy P Γ p Pt → Γ.canon Pt = .predates A x L →
      Γ.canon x = Γ.canon l → Γ.canon L = Γ.canon (.fv c) → Γ.canon l ≠ Γ.canon (.fv c) →
      DecOK Γ (.predates p) l t args
  | same : Γ.cur = some c → Γ.canon l = Γ.canon (.fv c) → markedIndex t pos 0 = some i →
      (markedArgs t args)[i]? = some a → Γ.subs[i]? = some s →
      (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
        Γ.canon a' = Γ.canon (.fv s')) →
      TmTy P Γ p Pt → Γ.canon Pt = .subterm A a0 B b0 →
      Γ.canon a0 = Γ.canon a → Γ.canon b0 = Γ.canon (.fv s) → DecOK Γ (.subterm pos p) l t args
  | autoPred : Γ.cur = some c → Γ.canon l = .fv x → x < c → c ∈ Γ.mints → DecOK Γ .none l t args
  | autoSub {i : Nat} : Γ.cur = some c → Γ.canon l = Γ.canon (.fv c) →
      (markedArgs t args)[i]? = some a → Γ.subs[i]? = some s →
      (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
        Γ.canon a' = Γ.canon (.fv s')) →
      (Γ.canon a).strictSub (Γ.canon (.fv s)) → DecOK Γ .none l t args

inductive PrimTy : Ctx → Prim → Tm → Prop
  | tm : TmTy P Γ t T → PrimTy Γ (.tm t) T
  | lit : TmTy P Γ t T → PrimTy Γ (.lit t) T
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
  | ret : ArgsTy P Γ ts rets .nil → Γ.ok (rtArgs P Γ ts rets) → CoreTy b Γ (.ret ts) rets
  | call : TmTy P Γ f Ft → Γ.canon Ft = .fn l np t → t.isTele → ArgsTy P Γ args t outs → args.len = np →
      DecOK P Γ dec l t args → outs.len = ms.length →
      (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outs)) →
      CoreTy b (Γ.pushTele outs (some (ms.map (er || ·)))) rest rets →
      CoreTy b Γ (.call f dec args er ms rest) rets
  | mtch : TmTy P Γ s St → Γ.canon St = .app (.tyc d) idx → P.adts[d]? = some D →
      (∀ e ∈ brs, e.1 = d ∧ e.2.1 < D.ctors.length) → TeleOK P Γ R → R.static Γ.n 0 → R.isTele →
      (er || Γ.ok (rt P Γ s)) →
      (∀ (c : Nat) sig, D.ctors[c]? = some sig →
        BranchOK b false { Γ with ghost := Γ.ghost || er || P.phantom d c } s d idx c sig R (lookupBr brs c) els.isSome) →
      (∀ e, els = some e → CoreTy b { Γ with ghost := Γ.ghost || er } e R) →
      CoreTy b (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) rest rets →
      CoreTy b Γ (.mtch s R brs els er rest) rets
  | case : TmTy P Γ s St → Γ.canon St = .app (.tyc d) idx → P.adts[d]? = some D →
      (∀ e ∈ brs, e.1 = d ∧ e.2.1 < D.ctors.length) → (er || Γ.ok (rt P Γ s)) → (Γ.ghost = false → er → realCount brs els ≤ 1) →
      (∀ (c : Nat) sig, D.ctors[c]? = some sig →
        BranchOK b er { Γ with ghost := Γ.ghost || (!er && P.phantom d c) } s d idx c sig rets (lookupBr brs c) els.isSome) →
      (∀ e, els = some e → CoreTy b Γ e rets) →
      CoreTy b Γ (.case s brs els er) rets
  | prim : PrimTy P Γ p T → (er || Γ.ok (p.rt P Γ)) → CoreTy b (Γ.pushPrim T er p) rest rets →
      CoreTy b Γ (.prim p er rest) rets
  | defLvl : CoreTy b Γ.pushMint rest rets → CoreTy b Γ (.defLvl rest) rets
  | defFns : gid < b → P.groups[gid]? = some G → GroupOK gid Γ G →
      CoreTy b (Γ.pushFns G) rest rets → CoreTy b Γ (.defFns gid rest) rets
  | chkIs : TmTy P Γ e E → Γ.canon a = Γ.canon e → CoreTy b Γ rest rets → CoreTy b Γ (.chk .is a e rest) rets
  | chkTy : TmTy P Γ a A → TmTy P Γ T U → Γ.canon U = .univ → Γ.canon A = Γ.canon T → CoreTy b Γ rest rets →
      CoreTy b Γ (.chk .ty a T rest) rets
  | chkRt : Γ.ok (rt P Γ a) → CoreTy b Γ rest rets → CoreTy b Γ (.chk .rt a x rest) rets
  | absurd : CoreTy b { Γ with ghost := true } body .nil → body.noRet = true → CoreTy b Γ (.absurd body) rets

inductive BranchOK : Nat → Bool → Ctx → Tm → Nat → Tm → Nat → Tm → Tm → Option Core → Bool → Prop
  | live : Γ.branch s d c idx sig = (Γf, .ok σ) →
      CoreTy b (Γ.setErs { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)) body R →
      BranchOK b fe Γ s d idx c sig R (some body) els
  | dead : (Γ.branch s d c idx sig).2 = .contra → BranchOK b fe Γ s d idx c sig R none els
  | covered : BranchOK b fe Γ s d idx c sig R none true
  | refuted : (Γ.branch s d c idx sig).2 = .contra → BranchOK b fe Γ s d idx c sig R (some .dead) els

inductive GroupOK : Nat → Ctx → Group → Prop
  | mk {G : Group} : Γ.tys[G.lvl]? = some K → Γ.canon K = .level →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → TmTy P Γ (F.type G) .univ) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → (marks F.tele F.np).count true ≤ P.k) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → CoreTy gid (Γ.body G F).1 F.body (Γ.body G F).2) →
      (∀ i < Γ.n, Γ.er i = G.ers.getD i true) → Γ.ghost = G.ghost →
      GroupOK gid Γ G
end

end Minimal
