import Minimal.Check

namespace Minimal

def Tm.isHole : Tm → Bool
  | .fv i => holeBase ≤ i
  | _ => false

def Tm.hasHole (t : Tm) : Bool := t.fvs.any (holeBase ≤ ·)

def outerBase : Nat := 2 ^ 39

def isOuter (i : Nat) : Bool := outerBase ≤ i && i < outerBase + 2 ^ 20

variable (P : Prog)

structure Metas where
  Γ : Ctx
  base : Nat
  eqs : List (Tm × Tm) := []

def coerOf' (T : Tm) : Option (Tm × Tm × Tm × Tm × Tm × Tm) := match T with
  | .app (.tyc _ .nil) (.cons sa (.cons A (.cons a (.cons sb (.cons B (.cons b .nil)))))) => some (sa, A, a, sb, B, b)
  | _ => none

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
          let (m, args, out) ← m.openArgs args.toList ps
          let t := .app h (.ofList args)
          match out, A with
          | .bind _ R .nil, some A => .ok ({ m with eqs := (R, A) :: m.eqs }, t)
          | _, _ => .ok (m.expect P t A, t)
        | _ => .ok (m, t)
      | none => .ok (m, t)
  | t => .ok (m.expect P t A, t)

partial def Metas.openArgs (m : Metas) : List Tm → Tm → Except String (Metas × List Tm × Tm)
  | a :: as, .bind (.is ..) e r => do
    let (m, a) ← if a.isHole then pure (m, e) else if a.hasHole then m.openTm a (m.typeOf P e) else pure (m, a)
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
      | .fv i => (m.base ≤ i ∧ i < m.Γ.n) ∨ isOuter i
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

def Metas.sol (m : Metas) : List (Nat × Tm) :=
  m.solve P [] m.eqs (m.Γ.n - m.base + 1 + ((m.eqs.flatMap fun (a, b) => a.fvs ++ b.fvs).filter isOuter).eraseDups.length)

def Metas.fill (m : Metas) (ts : List Tm) : Except String (List Tm) := do
  let sol := m.sol P
  let ts := ts.map (m.resolve sol)
  if ts.any (·.fvs.any (m.base ≤ ·)) then .error "cannot infer `_`" else .ok ts

def teleEqs (k : Nat) : Tm → Tm → List (Tm × Tm)
  | .bind e A r, .bind e' A' r' =>
    let x := Tm.fv (holeBase - 1 - k)
    (match e, e' with | .ty .., .ty .. => [(A, A')] | _, _ => []) ++ teleEqs (k + 1) (r.inst x 0) (r'.inst x 0)
  | _, _ => []
termination_by t => t.size
decreasing_by rw [Tm.size_inst_fv]; simp only [Tm.size]; omega

def inferArgs (Γ : Ctx) (args : List Tm) (tele : Tm) (exp : Option Tm := none) : Except String (List Tm) := do
  let (m, args, out) ← ({ Γ, base := Γ.n } : Metas).openArgs P args tele
  { m with eqs := m.eqs ++ (exp.map (teleEqs 0 out ·)).getD [] }.fill P args

def useTele : Nat → Tm → Tm
  | 0, A => .bind (.ty false false false) A .nil
  | k + 1, A => .bind (.is false false false) .hole (useTele k A)

def Core.returnsNext (Γ : Ctx) (k : Nat) : Core → Bool
  | .ret ts => ts.toList == (List.range k).map (.fv <| Γ.n + ·)
  | _ => false


mutual
partial def inferTerm (Γ : Ctx) (t : Tm) (A : Option Tm) : Except String Tm := do
  match t with
  | .valCtor sig => return .valCtor (← inferTele Γ sig)
  | .tyCtor ps => return .tyCtor (← inferTele Γ ps)
  | .fn l np tele u hm => return .fn l np (← inferTele Γ tele) u hm
  | t => do
    let m0 : Metas := { Γ, base := Γ.n }
    let (m, A) ← match A with
      | some A => if A.hasHole then (fun (m, A) => (m, some A)) <$> m0.openTm P A (some .univ) else pure (m0, some A)
      | none => pure (m0, none)
    let (m, t) ← m.openTm P t A
    let [t] ← m.fill P [t] | .error "cannot infer `_`"
    .ok t

partial def inferTele (Γ : Ctx) : Tm → Except String Tm
  | .bind k A r => do
    let A ← if A.hasHole then inferTerm Γ A (if k matches .ty .. then some .univ else none) else pure A
    let r ← if r.hasHole then (inferTele (Γ.pushEnt k A) (r.inst (.fv Γ.n) 0)).map (·.close Γ.n 0) else pure r
    return .bind k A r
  | t => return t

partial def inferTeleAgainst (Γ : Ctx) : Tm → Tm → Except String Tm
  | .bind k A r, .bind k' A' r' => do
    let A ← if !A.hasHole then pure A else do
      let (m, A1) ← ({ Γ, base := Γ.n } : Metas).openTm P A (if k matches .ty .. then some .univ else none)
      let [A1] ← { m with eqs := (A1, A') :: m.eqs }.fill P [A1] | .error "cannot infer `_`"
      pure A1
    let Γ' := Γ.pushEnt k A
    let r ← if r.hasHole then (inferTeleAgainst Γ' (r.inst (.fv Γ.n) 0) (r'.inst (.fv Γ.n) 0)).map (·.close Γ.n 0) else pure r
    return .bind k A r
  | R, _ => inferTele Γ R

end

def fvClosure (f : Nat → List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen | _, [], seen => seen
  | fuel + 1, i :: todo, seen =>
    let new := ((f i).filter (!seen.contains ·)).eraseDups
    fvClosure f fuel (todo ++ new) (seen ++ new)

def addMentions (Γ : Ctx) (ts : Tm) : Tm × Nat :=
  match ts.toList.mapM fun t => (checkTm P Γ t).toOption.map fun ⟨T, _⟩ => Γ.canon T with
  | none => (ts, 0)
  | some Ts =>
    let tyFvs (i : Nat) : List Nat := ((Γ.tys[i]?).map fun T => (Γ.canon T).fvs).getD []
    let init := (Ts.flatMap Tm.fvs).eraseDups
    let ms := (fvClosure tyFvs (Γ.n + init.length + 1) init init).mergeSort
    (.ofList (ms.map Tm.fv ++ ts.toList), ms.length)

abbrev IM := StateT (List Group × Nat) (Except String)

def scrutOf (Γ : Ctx) (s : Tm) : Option (Tm × Tm × List Arm) :=
  match checkTm P Γ s with
  | .ok ⟨St, _⟩ => match Γ.canon St with
    | .app H idx => match shapeOf P Γ true H with
      | .ok ⟨shp, _, _⟩ => some (H, idx, shp)
      | .error _ => none
    | _ => none
  | .error _ => none

def stepCtx (Γ : Ctx) : Core → Option (Ctx × Core × (Core → Core))
  | .call f dec args er ms ve rest => do
    let ⟨Ft, _⟩ ← (checkTm P Γ f).toOption
    let .fn _ _ t _ _ := Γ.canon Ft | none
    let ⟨outs, _⟩ ← (checkArgs P Γ args t).toOption
    some (Γ.pushTele outs (some (ms.map (er || ·))), rest, fun (r : Core) => .call f dec args er ms ve r)
  | .mtch s R brs els er rest =>
    some (Γ.pushTele R (if er then some (List.replicate R.len true) else none), rest, fun (r : Core) => .mtch s R brs els er r)
  | .prim p er rest => do
    let T ← match p with
      | .assert _ A => some A
      | p => (checkPrim P Γ p).toOption.map (·.1)
    some (Γ.pushPrim T er p, rest, fun (r : Core) => .prim p er r)
  | .wdo w req rest => do
    let ⟨Tw, _⟩ ← (checkPrim P Γ (.wNext w)).toOption
    let ⟨A, _⟩ ← (checkPrim P Γ (.wAsk w req)).toOption
    some ((Γ.push Tw false).push A false, rest, fun (r : Core) => .wdo w req r)
  | .defLvl rest => some (Γ.pushMint, rest, fun (r : Core) => .defLvl r)
  | .defFns gid rest => do let G ← P.groups[gid]?; some (Γ.pushFns G, rest, fun (r : Core) => .defFns gid r)
  | .chk (.opn oe) (.fv m) b rest =>
    let Γo : Ctx := { Γ with opened := (m, oe) :: Γ.opened }
    let σ' := match (Γ.tys[m]?).map Γ.canon with
      | some (.mtbl _ _ _ _ H cs) => match unify Γ.n (Γo.atoms P) Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
        | .ok σ' => σ'
        | _ => Γ.σ
      | _ => Γ.σ
    some ({ Γo with σ := σ' }, rest, fun (r : Core) => .chk (.opn oe) (.fv m) b r)
  | .chk k a b rest => some (Γ, rest, fun (r : Core) => .chk k a b r)
  | .seq R body rest => some (Γ.pushTele R, rest, fun (r : Core) => .seq R body r)
  | .case s brs els er nt =>
    let live : Option (Ctx × Core × (Core → Core)) := brs.zipIdx.findSome? fun ((n, c, k', body), j) => do
      if !body.real then none
      let (H, idx, shp) ← scrutOf P Γ s
      let (k, sig, _) ← shp[c]?
      match Γ.branch P s k H idx sig with
      | (Γf, .ok σ) => some ({ Γf with σ := σ }, body, fun (b : Core) => .case s (brs.set j (n, c, k', b)) els er nt)
      | _ => none
    live <|> els.map fun e => (Γ, e, fun (b : Core) => .case s brs (some b) er nt)
  | _ => none

partial def typeAtUse (j : Nat) (rets : Option Tm) (Γ : Ctx) : Core → Option Tm
  | .ret ts => do argsUse Γ ts.toList (← rets)
  | c => (match c with
      | .call f _ args _ _ _ _ => do
        let ⟨Ft, _⟩ ← (checkTm P Γ f).toOption
        let .fn _ _ t _ _ := Γ.canon Ft | none
        argsUse Γ args.toList t
      | .prim (.tm t) _ _ => termUse Γ t
      | _ => none) <|> do
    let (Γ', rest, _) ← stepCtx P Γ c
    typeAtUse j rets Γ' rest
where
  argsUse (Γ : Ctx) : List Tm → Tm → Option Tm
    | a :: as, .bind k A r => if a == .fv j then (if k matches .ty .. then some A else (checkTm P Γ A).toOption.map (·.1))
      else termUse Γ a <|> argsUse Γ as (r.inst a 0)
    | _, _ => none
  termUse (Γ : Ctx) : Tm → Option Tm
    | .app h args => do
      let ⟨H, _⟩ ← (checkTm P Γ h).toOption
      match Γ.canon H with
      | .tyCtor ps | .valCtor ps => argsUse Γ args.toList ps
      | _ => none
    | _ => none

partial def outerAt (Γ : Ctx) (rets : Option Tm) : Core → List (Nat × Tm)
  | c =>
    let solveAt (ts : List Tm) (T : Tm) : List (Nat × Tm) := match ({ Γ, base := Γ.n } : Metas).openArgs P ts T with
      | .ok (m, _, _) => let sol := m.sol P; (sol.filter (isOuter ·.1)).map fun (i, t) => (i, m.resolve sol t)
      | .error _ => []
    let here := match c, rets with
      | .ret ts, some R => solveAt ts.toList R
      | .call f _ args _ _ _ _, _ => match checkTm P Γ f with
        | .ok ⟨Ft, _⟩ => match Γ.canon Ft with
          | .fn _ _ t _ _ => solveAt args.toList t
          | _ => []
        | .error _ => []
      | _, _ => []
    if !here.isEmpty then here else match stepCtx P Γ c with
      | some (Γ', rest, _) => outerAt Γ' rets rest
      | none => []

partial def sideAt (Γ : Ctx) (rets : Option Tm) (tgt : Bool) (i : Nat) : Core → Option Tm
  | .chk .ty (.fv k) T _ => if k = i then side T else none
  | c => useSide (Γ.push .hole) c (i + 1) <|> (typeAtUse P i rets (Γ.push .hole) c).bind side
where
  side (T : Tm) : Option Tm := (coerOf' T).map fun (sa, _, _, sb, _) => if tgt then sb else sa
  useSide (Γk : Ctx) : Core → Nat → Option Tm
    | .prim (.coerCtor s C _ _ ps) _ rest, k => match ps.toList.idxOf? (.fv i) with
      | some j => do
        let s ← if s.isHole then sideAt Γk rets false k rest else some s
        let ⟨K, _⟩ ← (checkTm P Γk C).toOption
        let .valCtor sig := Γk.canon K | none
        some (if sig.uAt j then s else sharedTm)
      | none => useSide (Γk.push .hole) rest (k + 1)
    | .prim (.coerSym (.fv x)) _ rest, k =>
      if x = i then sideAt Γk rets (!tgt) k rest else useSide (Γk.push .hole) rest (k + 1)
    | .prim _ _ rest, k => useSide (Γk.push .hole) rest (k + 1)
    | _, _ => none

partial def inferCore (Γ : Ctx) (rets : Option Tm) (top : Bool) : Core → IM Core
  | .ret ts => do
    let ts ← if !ts.hasHole then pure ts else match rets with
      | some R => pure (.ofList (← inferArgs P Γ ts.toList R))
      | none => pure (.ofList (← ts.toList.mapM (inferTerm P Γ · none)))
    if !top then return .ret ts
    let (ts, k) := addMentions P Γ ts
    modify fun (gs, _) => (gs, k)
    return .ret ts
  | .call f dec args er ms ve rest => do
    let ty := match checkTm P Γ f with
      | .ok ⟨Ft, _⟩ => match Γ.canon Ft with
        | .fn _ _ t _ _ => some t
        | _ => none
      | .error _ => none
    let some t := ty | return .call f dec args er ms ve rest
    let exp := if rest.returnsNext Γ ms.length then rets else none
    let args ← if !args.hasHole then pure args else
      match inferArgs P Γ args.toList t exp with
      | .ok as => pure (Tm.ofList as)
      | .error e => do
        let args' := args.toList.zipIdx.map fun (a, k) => if a.isHole then .fv (outerBase + k) else a
        let Γo := Γ.pushTele (t.peel (.ofList args'))
        let st ← get
        let used ← tryCatch (some <$> inferCore Γo rets top rest) fun _ => pure none
        set st
        let sol := (used.map (outerAt P Γo rets)).getD []
        let solved := args'.map fun a => match a with
          | .fv i => if isOuter i then ((sol.lookup i).filter (·.fvs.all (· < Γ.n))).getD .hole else a
          | a => a
        match inferArgs P Γ solved t exp with
        | .ok as => pure (Tm.ofList as)
        | .error _ =>
        let A := (used.bind fun r => (List.range ms.length).findSome? fun k =>
          (typeAtUse P (Γ.n + k) rets Γo r).map (k, ·)).filter fun (_, A) => A.fvs.all (· < Γ.n)
        match A with
        | some (k, A) => Tm.ofList <$> inferArgs P Γ args.toList t (some (useTele k A))
        | none => throw e
    match checkArgs P Γ args t with
    | .ok ⟨outs, _⟩ => return .call f dec args er ms (some t.ers) (← inferCore (Γ.pushTele outs) rets top rest)
    | .error _ => return .call f dec args er ms ve rest
  | .mtch s R brs els er rest => do
    let R ← match rets with
      | some E => if rest.returnsNext Γ R.len then inferTeleAgainst P Γ R E else inferTele P Γ R
      | none => inferTele P Γ R
    let (brs, els) ← inferArms Γ s brs els (some R) false
    return .mtch s R brs els er (← inferCore (Γ.pushTele R) rets top rest)
  | .case s brs els er nt => do
    let (brs, els) ← inferArms Γ s brs els rets top
    return .case s brs els er nt
  | .wdo w req rest => do
    let Tw := ((checkPrim P Γ (.wNext w)).toOption.map (·.1)).getD .hole
    let A := ((checkPrim P Γ (.wAsk w req)).toOption.map (·.1)).getD .hole
    return .wdo w req (← inferCore ((Γ.push Tw false).push A false) rets top rest)
  | .prim p er rest => do
    let coerOf (q : Tm) : Option (Tm × Tm × Tm × Tm × Tm × Tm) := do
      let ⟨T, _⟩ ← (checkTm P Γ q).toOption
      let ⟨(dC, _), _⟩ ← (coerAdt P).toOption
      let ⟨x, _⟩ ← coerParts dC (Γ.canon T)
      some x
    let tgt := match p with | .coerWrap .. => true | _ => false
    let expSide : Tm → Tm := fun s => if !s.isHole then s else (sideAt P Γ rets tgt Γ.n rest).getD s
    let p ← match p with
      | .coerce a b q =>
        match coerOf q with
        | some (sa, _, _, sb, _, b') =>
          pure (.coerce a (if b.isHole then b' else b) q)
        | none => pure p
      | .coerRefl s e => pure (.coerRefl (expSide s) e)
      | .coerWrap s C args =>
        let args := if !args.hasHole then args else match checkTm P Γ C with
          | .ok ⟨K, _⟩ => match Γ.canon K with
            | .valCtor sig => ((inferArgs P Γ args.toList sig).toOption.map Tm.ofList).getD args
            | _ => args
          | .error _ => args
        pure (.coerWrap (expSide s) C args)
      | .coerCtor s C srcs tgts ps =>
        let fill (l : List Tm) (pick : Tm × Tm × Tm × Tm × Tm × Tm → Tm) : Tm := .ofList (l.zipIdx.map fun (t, j) =>
          if t.isHole then (((ps.toList[j]?).bind coerOf).map pick).getD t
          else if t.hasHole then (inferTerm P Γ t none).toOption.getD t else t)
        pure (.coerCtor (expSide s) C (fill srcs.toList (·.2.2.1)) (fill tgts.toList (·.2.2.2.2.2)) ps)
      | .place a (.app h (.cons s (.cons B (.cons a' .nil)))) =>
        if !B.hasHole then pure p else match checkTm P Γ a with
          | .ok ⟨A, _⟩ => pure (.place a (.app h (.cons s (.cons (Γ.canon A) (.cons a' .nil)))))
          | .error _ => pure p
      | .unplace a v =>
        if !v.hasHole then pure p else match checkTm P Γ a with
          | .ok ⟨A, _⟩ => match Γ.canon A with
            | .app _ (.cons _ (.cons _ (.cons w .nil))) => pure (.unplace a w)
            | _ => pure p
          | .error _ => pure p
      | .tm t =>
        if !t.hasHole then pure p else
        let A := match rest with
          | .chk .ty (.fv i) T _ => if i = Γ.n then some T else none
          | _ => none
        let A := A <|> (typeAtUse P Γ.n rets (Γ.push .hole) rest).filter (·.fvs.all (· < Γ.n))
        pure (.tm (← inferTerm P Γ t A))
      | p => pure p
    match p, checkPrim P Γ p with
    | .assert _ A, _ => return .prim p er (← inferCore (Γ.pushPrim A er p) rets top rest)
    | _, .ok ⟨T, _⟩ => return .prim p er (← inferCore (Γ.pushPrim T er p) rets top rest)
    | _, .error _ => return .prim p er rest
  | .defLvl rest => return .defLvl (← inferCore Γ.pushMint rets top rest)
  | .defFns gid rest => do
    let some G := (← get).1[gid]? | return .defFns gid rest
    let fns ← G.fns.mapM fun F => do
      let F := { F with tele := ← inferTele P Γ F.tele }
      let (Γb, R) := Γ.body G F
      return { F with body := ← inferCore Γb (some R) false F.body }
    modify fun (gs, h) => (gs.set gid { G with fns }, h)
    return .defFns gid (← inferCore (Γ.pushFns { G with fns }) rets top rest)
  | .chk (.opn oe) (.fv m) b rest => do
    let Γo : Ctx := { Γ with opened := (m, oe) :: Γ.opened }
    let σ' := match (Γ.tys[m]?).map Γ.canon with
      | some (.mtbl _ _ _ _ H cs) => match unify Γ.n (Γo.atoms P) Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
        | .ok σ' => σ'
        | _ => Γ.σ
      | _ => Γ.σ
    return .chk (.opn oe) (.fv m) b (← inferCore { Γo with σ := σ' } rets top rest)
  | .chk .ty a T rest => do
    if !T.hasHole then return .chk .ty a T (← inferCore Γ rets top rest)
    let (m, T') ← ({ Γ, base := Γ.n } : Metas).openTm P T (some .univ)
    let m := match checkTm P Γ a with
      | .ok ⟨A, _⟩ => { m with eqs := (A, T') :: m.eqs }
      | .error _ => m
    let [T] ← m.fill P [T'] | throw "cannot infer `_`"
    return .chk .ty a T (← inferCore Γ rets top rest)
  | .chk k a b rest => return .chk k a b (← inferCore Γ rets top rest)
  | .absurd body => return .absurd (← inferCore Γ none false body)
  | .seq R body rest => return .seq R (← inferCore Γ (some R) false body) (← inferCore (Γ.pushTele R) rets top rest)
  | .dead => return .dead
where
  inferArms (Γ : Ctx) (s : Tm) (brs : List Br) (els : Option Core) (R : Option Tm) (top : Bool) :
      IM (List Br × Option Core) := do
    let brs ← brs.mapM fun (n, c, k', body) => do
      match scrutOf P Γ s with
      | some (H, idx, shp) => match shp[c]? with
        | some (k, sig, _) => match Γ.branch P s k H idx sig with
          | (Γf, .ok σ) => return (n, c, k', ← inferCore { Γf with σ := σ } R top body)
          | _ => return (n, c, k', body)
        | none => return (n, c, k', body)
      | none => return (n, c, k', body)
    let els ← els.mapM (inferCore Γ R top)
    return (brs, els)

partial def mapRet {β : Type} (f : Ctx → Tm → Tm × β) (Γ : Ctx) : Core → Option (Core × β)
  | .ret ts => let (ts', b) := f Γ ts; some (.ret ts', b)
  | c => do
    let (Γ', rest, rebuild) ← stepCtx P Γ c
    let (r, b) ← mapRet f Γ' rest
    some (rebuild r, b)

def retTypes (Γ : Ctx) (c : Core) : Option (List Tm) :=
  (mapRet P (fun Γ ts => (ts, ts.toList.mapM fun t => (checkTm P Γ t).toOption.map fun ⟨T, _⟩ => Γ.canon T)) Γ c).bind (·.2)

def Prog.infer (P : Prog) : Except String Prog := do
  let adts ← P.adts.mapM fun D => do
    return { D with params := ← inferTele P {tys := #[]} D.params, ctors := ← D.ctors.mapM (inferTele P {tys := #[]}) }
  let P := { P with adts, isoFuel := isoFuelOfAdts adts }
  let (main, groups, hidden) ← (inferCore P {tys := #[]} none true P.main).run (P.groups, 0)
  return { P with main, groups, hidden }

end Minimal
