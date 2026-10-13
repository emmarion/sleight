import Minimal.Unify
import Minimal.Strip

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
  fixed : List (Option Tm) := []
  cmode : Bool := false
  deles : List (Nat × Nat) := []

namespace Ctx

def n (Γ : Ctx) : Nat := Γ.tys.length

def canon (Γ : Ctx) (t : Tm) : Tm := canonBy Γ.σ t

def sig (Γ : Ctx) (i : Nat) : Option Tm := match (Γ.tys[i]?).map Γ.canon with
  | some (.tyCtor ps) => some (.tyCtor ps)
  | some (.valCtor s) => some (.valCtor s)
  | _ => none

def push (Γ : Ctx) (T : Tm) (e : Bool := false) : Ctx :=
  let k := Γ.n
  { Γ with tys := Γ.tys ++ [T], er := fun i => if i = k then e else Γ.er i }

def withRule (Γ : Ctx) (e : Nat) (t : Tm) : Ctx := { Γ with σ := fun i => if i = e then some t else Γ.σ i }

def pushPrim (Γ : Ctx) (T : Tm) (er : Bool) : Prim → Ctx
  | .tm t | .coerce _ t _ => (Γ.push T er).withRule Γ.n (Γ.canon t)
  | _ => Γ.push T er

def pushEnt (Γ : Ctx) : Ent → Tm → Ctx
  | .ty _ e _, A => Γ.push A e
  | .is _ e _, x => (Γ.push .nil e).withRule Γ.n (Γ.canon x)

def openTele : Ctx → Tm → Nat → Ctx × Tm
  | Γ, .bind k A r, m + 1 => (Γ.pushEnt k A).openTele (r.inst (.fv Γ.n) 0) m
  | Γ, t, _ => (Γ, t)

def setErs (Γ Γ' : Ctx) : Option (List Bool) → Ctx
  | none => Γ'
  | some ms => let k := Γ.n; { Γ' with er := fun i => if k ≤ i then ms.getD (i - k) true else Γ'.er i }

def pushTele (Γ : Ctx) (R : Tm) (ov : Option (List Bool) := none) : Ctx := Γ.setErs (Γ.openTele R R.len).1 ov

def pushMint (Γ : Ctx) : Ctx := { Γ.push .level true with mints := Γ.mints ++ [Γ.n] }

def pushFns (Γ : Ctx) (G : Group) : Ctx :=
  let k := Γ.n
  { Γ with tys := Γ.tys ++ G.fns.map (FnDef.type G),
           er := fun i => if k ≤ i then (G.fns[i - k]?.map (·.er)).getD true else Γ.er i,
           deles := Γ.deles ++ G.fns.zipIdx.filterMap fun (F, j) =>
             if F.er || G.ghost then none else F.dele.map (k + j, ·) }

def fields (Γ : Ctx) (m : Nat) : Tm := .ofList ((List.range m).map fun j => .fv (Γ.n + j))

def body (Γ : Ctx) (G : Group) (F : FnDef) : Ctx × Tm :=
  let Γ1 := Γ.pushFns G
  let (Γ2, rem) := Γ1.openTele F.tele F.np
  ({ Γ2 with cur := some G.lvl, ghost := Γ.ghost || F.er,
             subs := (markedArgs F.tele (Γ1.fields F.np)).filterMap Tm.fvIdx,
             er := fun i => (F.dele.isSome && i < Γ1.n && F.dele != some i) || Γ2.er i },
   rem)

def ready (Γ : Ctx) : Bool :=
  Γ.fixed.length == Γ.n && Γ.cur.isNone && !Γ.ghost && (List.range Γ.n).all fun i => (Γ.fixed[i]?.join).isSome || Γ.er i

def strip (Γ : Ctx) : List Tm := Γ.fixed.map (·.getD .tok)

def record (Γ Γ' : Ctx) (vs : List Tm) : Ctx :=
  { Γ' with fixed := Γ.fixed ++ vs.zipIdx.map fun (v, k) => if Γ'.er (Γ.n + k) then none else some v }

end Ctx

opaque fixFuel : Nat := 1000000000

def stepS (P : Prog) (ρ : List Tm) : Core → Option (List Tm)
  | .call _ _ _ true ms _ _ => some (List.replicate ms.length .tok)
  | .call f _ args false _ ve _ => match P.sub ρ f with
    | .clo env gid j => do
      let G ← P.groups[gid]?
      let F ← G.fns[j]?
      let outs ← runS P fixFuel (env.toList ++ closuresS env.toList gid G ++ F.spreadIn ve (args.toList.map (P.sub ρ))) F.body
      some (F.spreadOut ve args.toList.length outs)
    | _ => none
  | .mtch _ R _ _ true _ => some (List.replicate R.len .tok)
  | .mtch s _ brs els false _ => match P.sub ρ s with
    | .app (.vc _ c _) vs => do
      let (pre, body) ← selectBr brs els c vs.toList
      runS P fixFuel (ρ ++ pre) body
    | _ => none
  | .seq _ body _ => runS P fixFuel ρ body
  | .prim p er _ => some [if er then .tok else p.evalS P ρ]
  | .defLvl _ => some [.tok]
  | .defFns gid _ => (P.groups[gid]?).map (closuresS ρ gid)
  | _ => none

def Ctx.adv (P : Prog) (Γ Γ' : Ctx) (c : Core) : Ctx :=
  if Γ.ready then match stepS P Γ.strip c with
    | some vs => Γ.record Γ' vs
    | none => Γ'
  else Γ'

def Ctx.known (Γ : Ctx) : Tm → Option (Nat × Nat)
  | .vc d c _ => some (d, c)
  | .fv y => match Γ.fixed[y]?.join with
    | some (.vc d c _) => some (d, c)
    | _ => none
  | _ => none

def Ctx.advBr (P : Prog) (Γ Γ' : Ctx) (s k : Tm) (fe : Bool) (n : Nat) : Ctx :=
  if Γ.ready then
    if fe then Γ.record Γ' (List.replicate n .tok)
    else match s, Γ.known k with
      | .fv x, some (d, c) => if P.isNt d then Γ' else match Γ.fixed[x]?.join with
        | some (.app (.vc d' c' _) vs) => if d' = d ∧ c' = c then Γ.record Γ' vs.toList else Γ'
        | _ => Γ'
      | _, _ => Γ'
  else Γ'

def Ctx.fixedEnv (Γ : Ctx) (i : Nat) : Tm := (Γ.fixed[i]?.join).getD .nil

def fieldsSimple (S : List Nat) : Tm → Bool
  | .bind (.ty _ false _) (.app (.tyc d .nil) .nil) r@(.bind ..) => S.contains d && fieldsSimple S r
  | .bind (.ty _ false _) _ .nil => true
  | _ => false

def Prog.simpleStep (P : Prog) (S : List Nat) : List Nat :=
  S.filter fun d => match P.adts[d]? with
    | some D => D.params == .nil && !D.newtype && !D.coercible && !D.opq && D.phantom.all (!·) && D.ctors.all (fieldsSimple S)
    | none => false

def Prog.simple (P : Prog) : List Nat :=
  (List.range (P.adts.length + 1)).foldl (fun S _ => P.simpleStep S) (List.range P.adts.length)

def compat : List Bool → Tm → Bool
  | m :: ms, .bind k _ r => (m || !k.er) && compat ms r
  | _, _ => true

variable (P : Prog)

def declMtbl : Tm → List Tm
  | .tyc d .nil | .vc d _ .nil => ((P.adts[d]?).map (·.mtbl d .nil)).toList
  | _ => []

def sigOf (Γ : Ctx) : Tm → Option Tm
  | .fv i => Γ.sig i
  | .tyc d .nil => if P.lifted d = 0 then (P.adts[d]?).map fun D => .tyCtor D.params else none
  | .vc d c .nil => if P.lifted d = 0 then (P.ctor d c).map .valCtor else none
  | _ => none

def declShape : Tm → Option (Tm × Option Tm)
  | .tyc d .nil => if P.lifted d = 0 then (P.adts[d]?).map fun D => (.tyCtor D.params, some (D.mtbl d .nil)) else none
  | .vc d c .nil => if P.lifted d = 0 then
      (P.adts[d]?).bind fun D => (D.ctors[c]?).map fun sig => (.valCtor sig, some (D.mtbl d .nil)) else none
  | .univ | .level => some (.tyCtor .nil, none)
  | _ => none

def clash : Tm → Tm → Bool
  | .vc d c _, .vc d' c' _ => d == d' && c != c'
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
  n * ((P.adts.zipIdx.map fun (D, d) => D.params.size + (D.mtbl d .nil).size + (D.ctors.map Tm.size).sum).sum + n) + 1

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
  | .bind (.ty ..) R .nil =>
    (Γf, unify Γf.n (Γf.atoms P) Γf.σ [] [(Γ.canon s, Γf.canon (.app k (Γ.fields m))), (Γ.canon (.app H idx), Γf.canon R)])
  | _ => (Γf, .unknown)

mutual
def rt (Γ : Ctx) : Tm → Bool
  | .fv i => !Γ.er i
  | .app (.vc d c ls) args => match P.ctor d c with
    | some sig => !P.phantom d c && ls.len == P.lifted d && rtArgs Γ args (sig.skip (P.lifted d))
    | none => false
  | .app (.fv i) args => match (Γ.tys[i]?).map Γ.canon with
    | some (.valCtor sig) => !Γ.er i && rtArgs Γ args sig
    | _ => false
  | .vc d c _ => !P.phantom d c
  | _ => false

def rtArgs (Γ : Ctx) : Tm → Tm → Bool
  | .nil, _ => true
  | .cons a as, .bind k _ r => (k.er || rt Γ a) && rtArgs Γ as r
  | _, _ => false
end

def Ctx.ok (Γ : Ctx) (b : Bool) : Bool := Γ.ghost || b

def Prim.rt (Γ : Ctx) : Prim → Bool
  | .tm t | .lit t | .coerce t _ _ => Minimal.rt P Γ t
  | .mtblOf .. | .atom _ | .axm _ => true
  | _ => false

mutual
inductive TmTy : Ctx → Tm → Tm → Prop
  | fv : Γ.tys[i]? = some T → TmTy Γ (.fv i) T
  | fvIs : Γ.tys[i]? = some .nil → Γ.σ i = some t → TmTy Γ t T → TmTy Γ (.fv i) T
  | univ : TmTy Γ .univ .univ
  | level : TmTy Γ .level .univ
  | tyc : P.adts[d]? = some D → ls.len = D.lifted → ArgsTy Γ ls D.params out → TmTy Γ (.tyc d ls) (.tyCtor out)
  | vc : P.ctor d c = some sig → ls.len = P.lifted d → ArgsTy Γ ls sig out → TmTy Γ (.vc d c ls) (.valCtor out)
  | tyApp : TmTy Γ h H → Γ.canon H = .tyCtor ps → ArgsTy Γ args ps .nil → TmTy Γ (.app h args) .univ
  | vcApp : TmTy Γ h H → Γ.canon H = .valCtor sig → ArgsTy Γ args sig (.bind (.ty m e u) T .nil) →
      TmTy Γ (.app h args) T
  | tyCtor : TeleOK Γ ps → (Tm.tyCtor ps).static Γ.n 0 → TmTy Γ (.tyCtor ps) .univ
  | valCtor : TeleOK Γ sig → (Tm.valCtor sig).static Γ.n 0 → sig.valRet 0 → TmTy Γ (.valCtor sig) .univ
  | predates : TmTy Γ A U → Γ.canon U = .univ → TmTy Γ x X → Γ.canon X = Γ.canon A →
      TmTy Γ L K → Γ.canon K = .level → TmTy Γ (.predates A x L) .univ
  | subterm : TmTy Γ A U → Γ.canon U = .univ → TmTy Γ a A' → Γ.canon A' = Γ.canon A →
      TmTy Γ B V → Γ.canon V = .univ → TmTy Γ b B' → Γ.canon B' = Γ.canon B →
      TmTy Γ (.subterm A a B b) .univ
  | fn : TmTy Γ l K → Γ.canon K = .level → TeleOK Γ t → np ≤ t.len →
      (Tm.fn l np t u hm).static Γ.n 0 → TmTy Γ (.fn l np t u hm) .univ
  | mtbl : (Tm.mtbl u nt ex ph T cs).static Γ.n 0 → TmTy Γ (.mtbl u nt ex ph T cs) .univ

inductive ArgsTy : Ctx → Tm → Tm → Tm → Prop
  | nil : ArgsTy Γ .nil t t
  | cons : TmTy Γ a T → Γ.canon T = Γ.canon A → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind (.ty m e u) A r) out
  | isCons : TmTy Γ a T → Γ.canon a = Γ.canon e → ArgsTy Γ as (r.inst a 0) out →
      ArgsTy Γ (.cons a as) (.bind (.is ..) e r) out
  | anyCons : TmTy Γ a T → ArgsTy Γ as (r.inst a 0) out → ArgsTy Γ (.cons a as) (.bind (.ty m e u) .nil r) out

inductive TeleOK : Ctx → Tm → Prop
  | nil : TeleOK Γ .nil
  | cons : TmTy Γ A U → Γ.canon U = .univ → TeleOK (Γ.push A) (r.inst (.fv Γ.n) 0) →
      TeleOK Γ (.bind (.ty m e u) A r)
  | isCons : TmTy Γ e T → TeleOK (Γ.pushEnt (.is false false false) e) (r.inst (.fv Γ.n) 0) → TeleOK Γ (.bind (.is ..) e r)
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
  | autoPred : Γ.cur = some c → Γ.canon l = .fv x → x < c → c ∈ Γ.mints → (dec = .none ∨ dec = .predates Tm.hole) →
      DecOK Γ dec l t args
  | autoSub {i : Nat} : Γ.cur = some c → Γ.canon l = Γ.canon (.fv c) →
      (markedArgs t args)[i]? = some a → Γ.subs[i]? = some s →
      (∀ j < i, ∀ a' s', (markedArgs t args)[j]? = some a' → Γ.subs[j]? = some s' →
        Γ.canon a' = Γ.canon (.fv s')) →
      (Γ.canon a).strictSub (Γ.canon (.fv s)) → (dec = .none ∨ ∃ pos, dec = .subterm pos Tm.hole ∧ markedIndex t pos 0 = some i) →
      DecOK Γ dec l t args

inductive WrapOK : Ctx → Tm → Nat → Prop
  | decl : Γ.canon C = .vc d c ls → P.wrapField d c = some k → WrapOK Γ C k
  | opened : (m, oe) ∈ Γ.opened → Γ.tys[m]? = some M → Γ.canon M = .mtbl u true ex ph H cs → cs.isList →
      cs.toList[i]? = some C' → Γ.canon C = Γ.canon C' → ph.getD i false = false →
      TmTy P Γ C K → Γ.canon K = .valCtor sig → sig.isTele → sig.ntField = some k → WrapOK Γ C k

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
  | mtblOf : P.adts[d]? = some D → ls.len = D.lifted → ArgsTy P Γ ls D.params out → D.coercible = false → D.opq = false →
      PrimTy Γ (.mtblOf d ls) (D.mtbl d ls)
  | atom : P.adts[d]? = some D → D.ctors = [.bind (.ty m e u) (.app (.tyc d .nil) .nil) .nil] → D.lifted = 0 →
      D.newtype = false → P.phantom d 0 = false → PrimTy Γ (.atom d) (.app (.tyc d .nil) .nil)
  | axm : TmTy P Γ A U → Γ.canon U = .univ → Γ.canon A = .app (.tyc d ls) idx → P.adts[d]? = some D → D.opq = true →
      PrimTy Γ (.axm A) A
  | predatesSubterm : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .predates A a l →
      Γ.canon Qt = .subterm B b A a → PrimTy Γ (.predatesSubterm p q) (.predates B b l)
  | assert : TmTy P Γ t T → t.static 0 0 → P.simpleStep P.simple = P.simple →
      (∀ i ∈ A.fvs, ∃ d vS, Γ.tys[i]? = some (.app (.tyc d .nil) .nil) ∧ d ∈ P.simple ∧ Γ.fixed[i]?.join = some vS) →
      A.subst Γ.fixedEnv = T → A.static Γ.n 0 → PrimTy Γ (.assert t A) A
  | coerce : TmTy P Γ p Pt → Γ.canon Pt = Tm.coer dC sa A a' sb B b' → P.adts[dC]? = some D → D.coercible = true →
      Γ.canon a = Γ.canon a' → TmTy P Γ b Tb → Γ.canon b = Γ.canon b' → Γ.canon Tb = Γ.canon B →
      PrimTy Γ (.coerce a b p) B
  | coerRefl : TmTy P Γ s S → TmTy P Γ e E → P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerRefl s e) (Tm.coer dC s E e s E e)
  | deleOf : (g, t) ∈ Γ.deles → Γ.tys[g]? = some Tg → Γ.tys[t]? = some Tt → P.adts[dD]? = some D →
      D.coercible = true → PrimTy Γ (.deleOf g t) (Tm.coer dD (fnSide (Γ.canon Tg)) Tg (.fv g) (fnSide (Γ.canon Tt)) Tt (.fv t))
  | coerOf : TmTy P Γ p Pt → Γ.canon Pt = Tm.coer dD sa A a sb B b → P.adts[dD]? = some D → D.coercible = true →
      P.adts[dC]? = some C → C.coercible = true → PrimTy Γ (.coerOf p) (Tm.coer dC sa A a sb B b)
  | coerSym : TmTy P Γ p Pt → Γ.canon Pt = Tm.coer dC sa A a sb B b → P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerSym p) (Tm.coer dC sb B b sa A a)
  | coerTrans : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = Tm.coer dC sa A a sb B b →
      Γ.canon Qt = Tm.coer dC sb B b sc C c → P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerTrans p q) (Tm.coer dC sa A a sc C c)
  | coerShare : TmTy P Γ p Pt → Γ.canon Pt = Tm.coer dC sa A a sb B b → P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerShare p) (Tm.coer dC sharedTm A a sharedTm B b)
  | coerWrap : TmTy P Γ s S → TmTy P Γ (.app C args) T0 → WrapOK P Γ C k →
      TmTy P Γ (args.toList.getD k .nil) F → P.adts[dC]? = some D → D.coercible = true → (src = sharedTm ∨ src = s) →
      PrimTy Γ (.coerWrap s C args) (Tm.coer dC src F (args.toList.getD k .nil) s T0 (.app C args))
  | coerCtor : TmTy P Γ s S → TmTy P Γ C K → Γ.canon K = .valCtor sig → sig.isTele → TmTy P Γ (.app C srcs) Ts →
      TmTy P Γ (.app C tgts) Tt → srcs.len = tgts.len →
      (∀ j < srcs.len, sig.ers.getD j true = false → ∃ p Pt sa A x sb B y, ps.toList[j]? = some p ∧ TmTy P Γ p Pt ∧
        Γ.canon Pt = Tm.coer dC sa A x sb B y ∧ Γ.canon x = Γ.canon (srcs.toList.getD j .nil) ∧
        Γ.canon y = Γ.canon (tgts.toList.getD j .nil)) →
      P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerCtor s C srcs tgts ps) (Tm.coer dC s Ts (.app C srcs) s Tt (.app C tgts))

abbrev Arm := Tm × Tm × Bool

inductive Shape : Ctx → Bool → Tm → List Arm → Bool → Prop
  | decl : P.adts[d]? = some D → D.coercible = false → D.opq = false → ls.len = D.lifted → ls.isList → ls.static Γ.n 0 →
      Shape Γ er (.tyc d ls) (D.ctors.zipIdx.map fun (sig, c) => (.vc d c ls, sig.peel ls, P.phantom d c)) D.newtype
  | opened : (m, oe) ∈ Γ.opened → Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs → cs.isList →
      shp.map (·.1) = cs.toList →
      (∀ i k sig p, shp[i]? = some (k, sig, p) → p = ph.getD i false ∧ sig.isTele ∧ sig.static Γ.n 0 ∧
        ∃ K, TmTy P Γ k K ∧ Γ.canon K = .valCtor sig) →
      (er || Γ.ok (!oe && !Γ.er m)) → Shape Γ er H shp nt

def armsOK (Γ : Ctx) (shp : List Arm) (brs : List Br) : Bool :=
  brs.all fun (n, c, k, _) => match shp[c]? with
    | some (k', sig, _) => n == sig.len - 1 && Γ.canon k == Γ.canon k'
    | none => false

def rank (bs : List Bool) (k : Nat) : Nat := ((bs.take k).filter (!·)).length

def symSpread (o : Bool) (bs : List Bool) : List (Option (Bool × Nat)) :=
  (List.range bs.length).map fun k => if bs.getD k true then none else some (o, rank bs k)

def resolve (n0 : Nat) (al : List (Option (Bool × Nat))) : Tm → Option (Bool × Nat)
  | .fv i => if n0 ≤ i then (al[i - n0]?).join else none
  | _ => none

def delegWalk (t n0 cnt : Nat) (re : List Bool) : Bool → List (Option (Bool × Nat)) → Core → Bool
  | ph, al, .chk _ _ _ r => delegWalk t n0 cnt re ph al r
  | ph, al, .prim p er r => delegWalk t n0 cnt re ph (al ++ [if er then none else match p with
      | .tm x | .coerce x _ _ => resolve n0 al x
      | _ => none]) r
  | ph, al, .call _ _ _ true ms _ r => delegWalk t n0 cnt re ph (al ++ List.replicate ms.length none) r
  | ph, al, .mtch _ R _ _ true r => delegWalk t n0 cnt re ph (al ++ List.replicate R.len none) r
  | ph, al, .defLvl r => delegWalk t n0 cnt re ph (al ++ [none]) r
  | ph, al, .defFns gid r => match P.groups[gid]? with
    | some G => delegWalk t n0 cnt re ph (al ++ List.replicate G.fns.length none) r
    | none => false
  | false, al, .call f _ args false _ (some ve) r =>
    f == .fv t && (filt (ve.take args.toList.length) args.toList).map (resolve n0 al) == (List.range cnt).map (fun r => some (false, r)) &&
      delegWalk t n0 cnt re true (al ++ symSpread true (ve.drop args.toList.length)) r
  | true, al, .ret ts => ts.toList.length == re.length &&
    (filt re ts.toList).map (resolve n0 al) == (List.range (re.count false)).map (fun r => some (true, r))
  | ph, al, .case _ brs els true _ => match h : realBr brs els with
    | some (pre, body) =>
      have := sizeOf_realBr h
      delegWalk t n0 cnt re ph (al ++ pre.map fun _ => none) body
    | none => false
  | _, _, _ => false
termination_by _ _ c => sizeOf c
decreasing_by all_goals simp_wf <;> omega

def Group.deleOK (G : Group) (n : Nat) : Bool :=
  G.fns.zipIdx.all fun (F, j) => match F.dele with
    | none => true
    | some t => t < n + j && (if t < n then !G.ers.getD t true else !((G.fns[t - n]?.map (·.er)).getD true)) &&
      delegWalk P t (n + G.fns.length) ((F.tele.ers.take F.np).count false) (F.tele.ers.drop F.np) false
        (symSpread false (F.tele.ers.take F.np)) F.body

mutual
inductive CoreTy : Nat → Ctx → Core → Tm → Prop
  | ret : ArgsTy P Γ ts rets .nil → Γ.ok (rtArgs P Γ ts rets) → CoreTy b Γ (.ret ts) rets
  | call : TmTy P Γ f Ft → Γ.canon Ft = .fn l np t uf hm → t.isTele → ArgsTy P Γ args t outs → args.len = np →
      DecOK P Γ dec l t args → outs.len = ms.length →
      (er || Γ.ok (rt P Γ f && rtArgs P Γ args t && compat ms outs)) → ve = some t.ers →
      CoreTy b (Ctx.adv P Γ (Γ.pushTele outs (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)) rest rets →
      CoreTy b Γ (.call f dec args er ms ve rest) rets
  | mtch : TmTy P Γ s St → Γ.canon St = .app H idx → Shape P Γ er H shp ntf → (er || !ntf) →
      armsOK Γ shp brs = true → TeleOK P Γ R → R.static Γ.n 0 → R.isTele →
      (er || Γ.ok (rt P Γ s)) →
      (∀ c k sig p, shp[c]? = some (k, sig, p) →
        BranchOK b false { Γ with ghost := Γ.ghost || er || p } s k H idx sig R (lookupBr brs c) els.isSome) →
      (∀ e, els = some e → CoreTy b { Γ with ghost := Γ.ghost || er } e R) →
      CoreTy b (Ctx.adv P Γ (Γ.pushTele R (if er then some (List.replicate R.len true) else none)) (.mtch s R brs els er rest)) rest rets →
      CoreTy b Γ (.mtch s R brs els er rest) rets
  | case : TmTy P Γ s St → Γ.canon St = .app H idx → Shape P Γ er H shp ntf → nt = (ntf && !er) →
      armsOK Γ shp brs = true → (er || Γ.ok (rt P Γ s)) → (Γ.ghost = false → (er || nt) → realCount brs els ≤ 1) →
      (∀ c k sig p, shp[c]? = some (k, sig, p) →
        BranchOK b er { Γ with ghost := Γ.ghost || (!er && p) } s k H idx sig rets (lookupBr brs c) els.isSome) →
      (∀ e, els = some e → CoreTy b Γ e rets) →
      CoreTy b Γ (.case s brs els er nt) rets
  | prim : PrimTy P Γ p T → (er || Γ.ok (p.rt P Γ)) → CoreTy b (Ctx.adv P Γ (Γ.pushPrim T er p) (.prim p er rest)) rest rets →
      CoreTy b Γ (.prim p er rest) rets
  | defLvl : CoreTy b (Ctx.adv P Γ Γ.pushMint (.defLvl rest)) rest rets → CoreTy b Γ (.defLvl rest) rets
  | defFns : gid < b → P.groups[gid]? = some G → GroupOK gid Γ G →
      CoreTy b (Ctx.adv P Γ (Γ.pushFns G) (.defFns gid rest)) rest rets → CoreTy b Γ (.defFns gid rest) rets
  | chkIs : TmTy P Γ e E → Γ.canon a = Γ.canon e → CoreTy b Γ rest rets → CoreTy b Γ (.chk .is a e rest) rets
  | chkTy : TmTy P Γ a A → TmTy P Γ T U → Γ.canon U = .univ → Γ.canon A = Γ.canon T → CoreTy b Γ rest rets →
      CoreTy b Γ (.chk .ty a T rest) rets
  | chkRt : Γ.ok (rt P Γ a) → CoreTy b Γ rest rets → CoreTy b Γ (.chk .rt a x rest) rets
  | chkCm : CoreTy b { Γ with cmode := true } rest rets → CoreTy b Γ (.chk .cm a x rest) rets
  | chkOpn : Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs → cs.toList.Nodup →
      unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .ok σ' →
      CoreTy b { Γ with opened := (m, oe) :: Γ.opened, σ := σ' } rest rets → CoreTy b Γ (.chk (.opn oe) (.fv m) x rest) rets
  | chkOpnFail : Γ.tys[m]? = some M → Γ.canon M = .mtbl u nt ex ph H cs →
      (¬ cs.toList.Nodup ∨ unify Γ.n (Ctx.atoms P { Γ with opened := (m, oe) :: Γ.opened }) Γ.σ []
        (Ctx.openEqs P { Γ with opened := (m, oe) :: Γ.opened } (H :: cs.toList)) = .contra) →
      CoreTy b Γ (.chk (.opn oe) (.fv m) x .dead) rets
  | absurd : CoreTy b { Γ with ghost := true } body .nil → body.noRet = true → CoreTy b Γ (.absurd body) rets
  | seq : TeleOK P Γ R → R.static Γ.n 0 → R.isTele → CoreTy b Γ body R →
      CoreTy b (Ctx.adv P Γ (Γ.pushTele R) (.seq R body rest)) rest rets →
      CoreTy b Γ (.seq R body rest) rets

inductive BranchOK : Nat → Bool → Ctx → Tm → Tm → Tm → Tm → Tm → Tm → Option Core → Bool → Prop
  | live : Γ.branch P s k H idx sig = (Γf, .ok σ) →
      CoreTy b { Γ.advBr P (Γ.setErs { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none))
        s k fe (sig.len - 1) with cmode := false } body R →
      BranchOK b fe Γ s k H idx sig R (some body) els
  | dead : (Γ.branch P s k H idx sig).2 = .contra → BranchOK b fe Γ s k H idx sig R none els
  | covered : BranchOK b fe Γ s k H idx sig R none true
  | fixedOut : Γ.cmode = true → Γ.fixed[x]?.join = some (.app (.vc d c0 ls) vs) → Γ.known k = some (d, c) → c ≠ c0 →
      P.isNt d = false →
      BranchOK b fe Γ (.fv x) k H idx sig R none els
  | refuted : (Γ.branch P s k H idx sig).2 = .contra → BranchOK b fe Γ s k H idx sig R (some .dead) els

inductive GroupOK : Nat → Ctx → Group → Prop
  | mk {G : Group} : Γ.tys[G.lvl]? = some K → Γ.canon K = .level →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → TmTy P Γ (F.type G) .univ) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → (marks F.tele F.np).count true ≤ P.k) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → CoreTy gid (Γ.body G F).1 F.body (Γ.body G F).2) →
      (∀ i < Γ.n, Γ.er i = G.ers.getD i true) → Γ.ghost = G.ghost → G.deleOK P Γ.n = true →
      GroupOK gid Γ G
end

end Minimal
