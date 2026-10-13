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
  opened : List (Nat × Bool) := []

namespace Ctx

def n (Γ : Ctx) : Nat := Γ.tys.length

def canon (Γ : Ctx) (t : Tm) : Tm := canonBy Γ.σ t

def sig (Γ : Ctx) (i : Nat) : Option Tm := match (Γ.tys[i]?).map Γ.canon with
  | some (.tyCtor ps) => some (.tyCtor ps)
  | some (.valCtor s) => some (.valCtor s)
  | _ => none

def push (Γ : Ctx) (T : Tm) (e : Bool := false) : Ctx :=
  { Γ with tys := Γ.tys ++ [T], er := fun i => if i = Γ.n then e else Γ.er i }

def withRule (Γ : Ctx) (e : Nat) (t : Tm) : Ctx := { Γ with σ := fun i => if i = e then some t else Γ.σ i }

def pushPrim (Γ : Ctx) (T : Tm) (er : Bool) : Prim → Ctx
  | .tm t => (Γ.push T er).withRule Γ.n (Γ.canon t)
  | _ => Γ.push T er

def pushEnt (Γ : Ctx) : Ent → Tm → Ctx
  | .ty _ e, A => Γ.push A e
  | .is _ e, x => (Γ.push .nil e).withRule Γ.n (Γ.canon x)

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

end Ctx

def compat : List Bool → Tm → Bool
  | m :: ms, .bind k _ r => (m || !k.er) && compat ms r
  | _, _ => true

variable (P : Prog)

def declMtbl : Tm → List Tm
  | .tyc d | .vc d _ => ((P.adts[d]?).map (·.mtbl d)).toList
  | _ => []

def sigOf (Γ : Ctx) : Tm → Option Tm
  | .fv i => Γ.sig i
  | .tyc d => (P.adts[d]?).map fun D => .tyCtor D.params
  | .vc d c => (P.ctor d c).map .valCtor
  | _ => none

def declShape : Tm → Option (Tm × Option Tm)
  | .tyc d => (P.adts[d]?).map fun D => (.tyCtor D.params, some (D.mtbl d))
  | .vc d c => (P.adts[d]?).bind fun D => (D.ctors[c]?).map fun sig => (.valCtor sig, some (D.mtbl d))
  | .univ | .level => some (.tyCtor .nil, none)
  | _ => none

def clash : Tm → Tm → Bool
  | .vc d c, .vc d' c' => d == d' && c != c'
  | _, _ => false

def declIso : Nat → List (List Tm) → List (Tm × Tm) → Bool
  | _, _, [] => true
  | 0, _, _ => false
  | fuel + 1, cls, (a, b) :: work =>
    let ca := (cls.find? (·.contains a)).getD [a]
    let cb := (cls.find? (·.contains b)).getD [b]
    if ca.contains b then declIso fuel cls work
    else if ca.any fun x => cb.any (clash x) then false
    else match declShape P a, declShape P b with
      | some (s, m), some (s', m') =>
        match pairsOf ((s, s') :: (match m, m' with | some x, some y => [(x, y)] | _, _ => [])) with
        | some ps => declIso fuel ((ca ++ cb) :: cls.filter fun c => !c.contains a && !c.contains b) (ps ++ work)
        | none => false
      | _, _ => false

def Prog.isoFuel : Nat :=
  let n := P.adts.length + (P.adts.map (·.ctors.length)).sum + 2
  n * ((P.adts.zipIdx.map fun (D, d) => D.params.size + (D.mtbl d).size + (D.ctors.map Tm.size).sum).sum + n) + 1

def Ctx.lists (Γ : Ctx) (σ : Nat → Option Tm) : List (Tm × Tm × List Tm) :=
  Γ.opened.filterMap fun (m, _) => match (Γ.tys[m]?).map (canonBy σ) with
    | some (.mtbl u nt ex ph T cs) => some (.mtbl u nt ex ph T cs, T, cs.toList)
    | _ => none

def Ctx.atoms (Γ : Ctx) : Atoms := fun σ a b =>
  let ls := Γ.lists σ
  if ls.any (fun (_, _, ks) => match ks.idxOf? a, ks.idxOf? b with
      | some i, some j => i != j
      | _, _ => false) then none
  else if a.isAtom && b.isAtom then if declIso P P.isoFuel [] [(a, b)] then some [] else none
  else
    let names (x : Tm) := ls.filterMap (fun (M, T, ks) => if T == x || ks.contains x then some M else none) ++ declMtbl P x
    let ms := names a ++ names b
    let sigs := match sigOf P Γ a, sigOf P Γ b with
      | some s, some s' => [(canonBy σ s, canonBy σ s')]
      | _, _ => []
    some (sigs ++ ms.map (ms.headD .nil, ·))

def Ctx.openEqs (Γ : Ctx) (xs : List Tm) : List (Tm × Tm) := xs.flatMap fun x => (Γ.atoms P Γ.σ x x).getD []

def Ctx.branch (Γ : Ctx) (s k H idx sig : Tm) : Ctx × UResult :=
  let m := sig.len - 1
  let (Γf, rem) := Γ.openTele sig m
  match rem with
  | .bind (.ty _ _) R .nil =>
    (Γf, unify Γf.n (Γf.atoms P) Γf.σ [] [(Γ.canon s, Γf.canon (.app k (Γ.fields m))), (Γ.canon (.app H idx), Γf.canon R)])
  | _ => (Γf, .unknown)

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
  | .mtblOf _ => true
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
  | mtbl : (Tm.mtbl u nt ex ph T cs).static Γ.n 0 → TmTy Γ (.mtbl u nt ex ph T cs) .univ

inductive ArgsTy : Ctx → Tm → Tm → Tm → Prop
  | nil : ArgsTy Γ .nil t t
  | cons : TmTy Γ a T → Γ.canon T = Γ.canon A → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind (.ty m e) A r) out
  | isCons : TmTy Γ a T → Γ.canon a = Γ.canon e → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind (.is _ _) e r) out
  | anyCons : TmTy Γ a T → ArgsTy Γ as (r.inst a 0) out → ArgsTy Γ (.cons a as) (.bind (.ty m e) .nil r) out

inductive TeleOK : Ctx → Tm → Prop
  | nil : TeleOK Γ .nil
  | cons : TmTy Γ A U → Γ.canon U = .univ → TeleOK (Γ.push A) (r.inst (.fv Γ.n) 0) →
      TeleOK Γ (.bind (.ty m e) A r)
  | isCons : TmTy Γ e T → TeleOK (Γ.pushEnt (.is false false) e) (r.inst (.fv Γ.n) 0) → TeleOK Γ (.bind (.is _ _) e r)
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
  | mtblOf : P.adts[d]? = some D → D.lifted = 0 → PrimTy Γ (.mtblOf d) (D.mtbl d)
  | predatesSubterm : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .predates A a l →
      Γ.canon Qt = .subterm B b A a → PrimTy Γ (.predatesSubterm p q) (.predates B b l)

abbrev Arm := Tm × Tm × Bool

inductive Shape : Ctx → Bool → Tm → List Arm → Prop
  | decl : P.adts[d]? = some D → Shape Γ er (.tyc d) (D.ctors.zipIdx.map fun (sig, c) => (.vc d c, sig, P.phantom d c))
  | opened : (m, oe) ∈ Γ.opened → Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs → cs.isList →
      shp.map (·.1) = cs.toList →
      (∀ i k sig p, shp[i]? = some (k, sig, p) → p = ph.getD i false ∧ sig.isTele ∧ sig.static Γ.n 0 ∧
        ∃ K, TmTy P Γ k K ∧ Γ.canon K = .valCtor sig) →
      (er || Γ.ok (!oe && !Γ.er m)) → Shape Γ er H shp

def armsOK (Γ : Ctx) (shp : List Arm) (brs : List Br) : Bool :=
  brs.all fun (n, c, k, _) => match shp[c]? with
    | some (k', sig, _) => n == sig.len - 1 && Γ.canon k == Γ.canon k'
    | none => false

mutual
inductive CoreTy : Nat → Ctx → Core → Tm → Prop
  | ret : ArgsTy P Γ ts rets .nil → Γ.ok (rtArgs P Γ ts rets) → CoreTy b Γ (.ret ts) rets
  | call : TmTy P Γ f Ft → Γ.canon Ft = .fn l np t → t.isTele → ArgsTy P Γ args t outs → args.len = np →
      DecOK P Γ dec l t args → outs.len = ms.length →
      (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outs)) →
      CoreTy b (Γ.pushTele outs (some (ms.map (er || ·)))) rest rets →
      CoreTy b Γ (.call f dec args er ms rest) rets
  | mtch : TmTy P Γ s St → Γ.canon St = .app H idx → Shape P Γ er H shp →
      armsOK Γ shp brs = true → TeleOK P Γ R → R.static Γ.n 0 → R.isTele →
      (er || Γ.ok (rt P Γ s)) →
      (∀ c k sig p, shp[c]? = some (k, sig, p) →
        BranchOK b false { Γ with ghost := Γ.ghost || er || p } s k H idx sig R (lookupBr brs c) els.isSome) →
      (∀ e, els = some e → CoreTy b { Γ with ghost := Γ.ghost || er } e R) →
      CoreTy b (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) rest rets →
      CoreTy b Γ (.mtch s R brs els er rest) rets
  | case : TmTy P Γ s St → Γ.canon St = .app H idx → Shape P Γ er H shp →
      armsOK Γ shp brs = true → (er || Γ.ok (rt P Γ s)) → (Γ.ghost = false → er → realCount brs els ≤ 1) →
      (∀ c k sig p, shp[c]? = some (k, sig, p) →
        BranchOK b er { Γ with ghost := Γ.ghost || (!er && p) } s k H idx sig rets (lookupBr brs c) els.isSome) →
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
  | chkOpn : Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs → cs.toList.Nodup →
      unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .ok σ' →
      CoreTy b { Γ with opened := (m, oe) :: Γ.opened, σ := σ' } rest rets → CoreTy b Γ (.chk (.opn oe) (.fv m) x rest) rets
  | chkOpnFail : Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs →
      (¬ cs.toList.Nodup ∨ unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .contra) →
      CoreTy b Γ (.chk (.opn oe) (.fv m) x .dead) rets
  | absurd : CoreTy b { Γ with ghost := true } body .nil → body.noRet = true → CoreTy b Γ (.absurd body) rets
  | seq : TeleOK P Γ R → R.static Γ.n 0 → R.isTele → CoreTy b Γ body R → CoreTy b (Γ.pushTele R) rest rets →
      CoreTy b Γ (.seq R body rest) rets

inductive BranchOK : Nat → Bool → Ctx → Tm → Tm → Tm → Tm → Tm → Tm → Option Core → Bool → Prop
  | live : Γ.branch P s k H idx sig = (Γf, .ok σ) →
      CoreTy b (Γ.setErs { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)) body R →
      BranchOK b fe Γ s k H idx sig R (some body) els
  | dead : (Γ.branch P s k H idx sig).2 = .contra → BranchOK b fe Γ s k H idx sig R none els
  | covered : BranchOK b fe Γ s k H idx sig R none true
  | refuted : (Γ.branch P s k H idx sig).2 = .contra → BranchOK b fe Γ s k H idx sig R (some .dead) els

inductive GroupOK : Nat → Ctx → Group → Prop
  | mk {G : Group} : Γ.tys[G.lvl]? = some K → Γ.canon K = .level →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → TmTy P Γ (F.type G) .univ) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → (marks F.tele F.np).count true ≤ P.k) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → CoreTy gid (Γ.body G F).1 F.body (Γ.body G F).2) →
      (∀ i < Γ.n, Γ.er i = G.ers.getD i true) → Γ.ghost = G.ghost →
      GroupOK gid Γ G
end

end Minimal
