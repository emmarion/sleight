import Minimal.Check

namespace Minimal

def holeBase : Nat := 2 ^ 40

def Tm.hole : Tm := .fv holeBase

def Tm.isHole : Tm → Bool
  | .fv i => holeBase ≤ i
  | _ => false

def Tm.hasHole (t : Tm) : Bool := t.fvs.any (holeBase ≤ ·)

variable (P : Prog)

structure Metas where
  Γ : Ctx
  base : Nat
  eqs : List (Tm × Tm) := []

def Metas.typeOf (m : Metas) (t : Tm) : Option Tm :=
  match checkTm P m.Γ t with
  | .ok ⟨T, _⟩ => some T
  | .error _ => none

def Metas.expect (m : Metas) (t : Tm) : Option Tm → Metas
  | some A => match m.typeOf P t with
    | some T => { m with eqs := (T, A) :: m.eqs }
    | none => m
  | none => m

mutual
partial def Metas.openTm (m : Metas) (t : Tm) (A : Option Tm) : Except String (Metas × Tm) :=
  if t.isHole then match A with
    | some A => .ok ({ m with Γ := m.Γ.push A }, .fv m.Γ.n)
    | none => .error "cannot infer `_` here"
  else match t with
  | .app h args =>
    if !args.hasHole then .ok (m.expect P t A, t)
    else match m.typeOf P h with
      | some H => match m.Γ.canon H with
        | .tyCtor ps | .valCtor ps => do
          let (m, args, _) ← m.openArgs args.toList ps
          let t := .app h (.ofList args)
          .ok (m.expect P t A, t)
        | _ => .ok (m, t)
      | none => .ok (m, t)
  | t => .ok (m.expect P t A, t)

partial def Metas.openArgs (m : Metas) : List Tm → Tm → Except String (Metas × List Tm × Tm)
  | a :: as, .bind (.is _) e r => do
    let a := if a.isHole then e else a
    let (m, as, out) ← m.openArgs as (r.inst a 0)
    .ok ({ m with eqs := (a, e) :: m.eqs }, a :: as, out)
  | a :: as, .bind _ A r => do
    let (m, a) ← m.openTm a (some A)
    let (m, as, out) ← m.openArgs as (r.inst a 0)
    .ok (m, a :: as, out)
  | as, t => .ok (m, as, t)
end

def Metas.resolve (m : Metas) (sol : List (Nat × Tm)) (t : Tm) : Tm :=
  (List.range (sol.length + 1)).foldl (fun t _ => t.subst fun i => (sol.lookup i).getD (.fv i)) t

partial def Metas.match1 (m : Metas) (sol : List (Nat × Tm)) : Tm × Tm → List (Nat × Tm) × List (Tm × Tm)
  | (a, b) =>
    let a := m.Γ.canon (m.resolve sol a)
    let b := m.Γ.canon (m.resolve sol b)
    if a == b then (sol, []) else
    let isMeta : Tm → Bool
      | .fv i => m.base ≤ i ∧ i < m.Γ.n
      | _ => false
    let bind (i : Nat) (t : Tm) : List (Nat × Tm) × List (Tm × Tm) :=
      if i ∈ t.fvs then (sol, []) else
      ((i, t) :: sol, match m.Γ.tys[i]?, m.typeOf P t with
        | some A, some T => [(T, A)]
        | _, _ => [])
    match a, b with
    | .fv i, t => if isMeta a then bind i t else if isMeta t then match t with | .fv j => bind j a | _ => (sol, []) else (sol, [])
    | t, .fv i => if isMeta b then bind i t else (sol, [])
    | a, b =>
      if a.sameHead b then
        (a.kids.zip b.kids).foldl (fun (sol, eqs) p => let (sol, e) := m.match1 sol p; (sol, eqs ++ e)) (sol, [])
      else (sol, [])

partial def Metas.solve (m : Metas) (sol : List (Nat × Tm)) (eqs : List (Tm × Tm)) (fuel : Nat) : List (Nat × Tm) :=
  match fuel with
  | 0 => sol
  | fuel + 1 =>
    let (sol', more) := eqs.foldl (fun (sol, more) p => let (sol, e) := m.match1 P sol p; (sol, more ++ e)) (sol, [])
    if sol'.length == sol.length then sol' else m.solve sol' (eqs ++ more) fuel

def Metas.fill (m : Metas) (ts : List Tm) : Except String (List Tm) := do
  let sol := m.solve P [] m.eqs (m.Γ.n - m.base + 1)
  let ts := ts.map (m.resolve sol)
  if ts.any (·.fvs.any (m.base ≤ ·)) then .error "cannot infer `_`" else .ok ts

def inferArgs (Γ : Ctx) (args : List Tm) (tele : Tm) : Except String (List Tm) := do
  let (m, args, _) ← ({ Γ, base := Γ.n } : Metas).openArgs P args tele
  m.fill P args

def inferTerm (Γ : Ctx) (t : Tm) (A : Option Tm) : Except String Tm := do
  let (m, t) ← ({ Γ, base := Γ.n } : Metas).openTm P t A
  let [t] ← m.fill P [t] | .error "cannot infer `_`"
  .ok t

abbrev IM := StateT (List Group) (Except String)

def scrutOf (Γ : Ctx) (s : Tm) : Option (Nat × Tm) :=
  match checkTm P Γ s with
  | .ok ⟨St, _⟩ => match Γ.canon St with
    | .app (.tyc d) idx => some (d, idx)
    | _ => none
  | .error _ => none

partial def inferCore (Γ : Ctx) (rets : Option Tm) : Core → IM Core
  | .ret ts => do
    if !ts.hasHole then return .ret ts
    match rets with
    | some R => return .ret (.ofList (← inferArgs P Γ ts.toList R))
    | none => return .ret (.ofList (← ts.toList.mapM (inferTerm P Γ · none)))
  | .call f dec args er ms rest => do
    let ty := match checkTm P Γ f with
      | .ok ⟨Ft, _⟩ => match Γ.canon Ft with
        | .fn _ _ t => some t
        | _ => none
      | .error _ => none
    let some t := ty | return .call f dec args er ms rest
    let args ← if args.hasHole then Tm.ofList <$> inferArgs P Γ args.toList t else pure args
    match checkArgs P Γ args t with
    | .ok ⟨outs, _⟩ => return .call f dec args er ms (← inferCore (Γ.pushTele outs) rets rest)
    | .error _ => return .call f dec args er ms rest
  | .mtch s R brs els er rest => do
    let (brs, els) ← inferArms Γ s brs els (some R)
    return .mtch s R brs els er (← inferCore (Γ.pushTele R) rets rest)
  | .case s brs els er => do
    let (brs, els) ← inferArms Γ s brs els rets
    return .case s brs els er
  | .prim p er rest => do
    let p ← match p with
      | .tm t =>
        if !t.hasHole then pure p else
        let A := match rest with
          | .chk .ty (.fv i) T _ => if i = Γ.n then some T else none
          | _ => none
        pure (.tm (← inferTerm P Γ t A))
      | p => pure p
    match checkPrim P Γ p with
    | .ok ⟨T, _⟩ => return .prim p er (← inferCore (Γ.pushPrim T er p) rets rest)
    | .error _ => return .prim p er rest
  | .defLvl rest => return .defLvl (← inferCore Γ.pushMint rets rest)
  | .defFns gid rest => do
    let some G := (← get)[gid]? | return .defFns gid rest
    let fns ← G.fns.mapM fun F => do
      let (Γb, R) := Γ.body G F
      return { F with body := ← inferCore Γb (some R) F.body }
    modify fun gs => gs.set gid { G with fns }
    return .defFns gid (← inferCore (Γ.pushFns G) rets rest)
  | .chk k a b rest => return .chk k a b (← inferCore Γ rets rest)
  | .absurd body => return .absurd (← inferCore Γ none body)
  | .dead => return .dead
where
  inferArms (Γ : Ctx) (s : Tm) (brs : List (Nat × Nat × Core)) (els : Option Core) (R : Option Tm) :
      IM (List (Nat × Nat × Core) × Option Core) := do
    let brs ← brs.mapM fun (d, c, body) => do
      match scrutOf P Γ s, P.ctor d c with
      | some (_, idx), some sig => match Γ.branch s d c idx sig with
        | (Γf, .ok σ) => return (d, c, ← inferCore { Γf with σ := σ } R body)
        | _ => return (d, c, body)
      | _, _ => return (d, c, body)
    let els ← els.mapM (inferCore Γ R)
    return (brs, els)

def Prog.infer (P : Prog) : Except String Prog := do
  let (main, groups) ← (inferCore P {tys := []} none P.main).run P.groups
  return { P with main, groups }

end Minimal
