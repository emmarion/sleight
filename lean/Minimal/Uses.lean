import Minimal.Check

namespace Minimal

abbrev Uses := List (Nat × Bool)

def Uses.add (U : Uses) (i : Nat) (u : Bool) : Option Uses :=
  match U.lookup i with
  | some true => none
  | some false => if u then none else some U
  | none => some ((i, u) :: U)

def Uses.seq (A B : Uses) : Option Uses := B.foldlM (fun U (i, u) => Uses.add U i u) A

def Uses.join (A B : Uses) : Uses := B.foldl (fun U (i, u) => match U.lookup i with
  | some true => U
  | some false => if u then (i, true) :: U.filter (·.1 != i) else U
  | none => (i, u) :: U) A

def Uses.below (U : Uses) (n : Nat) : Uses := U.filter (·.1 < n)

def Tm.isFv : Tm → Bool
  | .fv _ => true
  | _ => false

abbrev Caps := List (Nat × Uses)

abbrev UR := Option (Uses × Caps)

def UR.seq (a b : Uses × Caps) : UR := do some (← Uses.seq a.1 b.1, a.2 ++ b.2)

def UR.join (a b : Uses × Caps) : Uses × Caps := (Uses.join a.1 b.1, a.2 ++ b.2)

def UR.below (a : Uses × Caps) (n : Nat) : Uses × Caps := (Uses.below a.1 n, a.2)

def UR.lift (o : Option Uses) : UR := o.map (·, [])

def Uses.sub (A B : Uses) : Bool := A.all fun (i, u) => match B.lookup i with
  | some v => !u || v
  | none => false

def teleUs : Tm → List Bool
  | .bind k _ r => k.u :: teleUs r
  | _ => []

structure UCtx where
  Γ : Ctx
  uq : List Nat := []
  scr : Bool := false
  ents : List Bool := []
  rebind : Option Tm := none
  uscr : Option Tm := none
  cellOk : Bool := false
  fill : Bool := false

variable (P : Prog)

namespace UCtx

def next (G : UCtx) (Γ' : Ctx) (us : List Bool) : UCtx :=
  { Γ := Γ', uq := G.uq ++ ((us.take (Γ'.n - G.Γ.n)).zipIdx.filterMap fun (u, k) => if u then some (G.Γ.n + k) else none),
    uscr := G.uscr,
    fill := G.fill }

def adv (G : UCtx) (Γ' : Ctx) (c : Core) : Ctx := if G.fill then Γ' else Ctx.adv P G.Γ Γ' c

def sigOf (G : UCtx) (h : Tm) : Option Tm := match checkTm P G.Γ h with
  | .ok ⟨H, _⟩ => match G.Γ.canon H with
    | .valCtor sig | .tyCtor sig => some sig
    | _ => none
  | .error _ => none

def use (G : UCtx) (i : Nat) (u : Bool) : Option Uses :=
  if G.Γ.n ≤ i || G.Γ.er i || u && !G.uq.contains i then none else some [(i, u)]

mutual
def termUses (G : UCtx) (u : Bool) : Tm → Option Uses
  | .fv i => G.use i u
  | .app h args => match G.sigOf P h with
    | some sig => do
      let A ← G.argsUses (fun k => u && k.u) args sig
      match h with
      | .fv i => Uses.seq (← G.use i false) A
      | _ => some A
    | none => none
  | .vc .. | .tyc .. | .nil | .sfv _ => some []
  | _ => none

def argsUses (G : UCtx) (md : Ent → Bool) : Tm → Tm → Option Uses
  | .cons a as, .bind k _ r => do
    let A ← if k.er then some [] else G.termUses (md k) a
    let B ← G.argsUses md as r
    Uses.seq A B
  | _, _ => some []
end

def retUses (G : UCtx) : List Bool → Tm → Tm → Option Uses
  | u :: us, .cons a as, .bind k _ r => do
    let A ← if k.er then some [] else G.termUses P u a
    Uses.seq A (← G.retUses us as r)
  | _, .cons a as, .bind k _ r => do
    let A ← if k.er then some [] else G.termUses P false a
    Uses.seq A (← G.retUses [] as r)
  | _, _, _ => some []

def callee (G : UCtx) (f args : Tm) : Option (Tm × Tm × Bool) := match checkTm P G.Γ f with
  | .ok ⟨Ft, _⟩ => match G.Γ.canon Ft with
    | .fn _ _ t uf _ => match checkArgs P G.Γ args t with
      | .ok ⟨outs, _⟩ => some (t, outs, uf)
      | .error _ => none
    | _ => none
  | .error _ => none

def primTy (G : UCtx) (p : Prim) : Option Tm := match p with
  | .assert _ A => some A
  | p => match checkPrim P G.Γ p with
    | .ok ⟨T, _⟩ => some T
    | .error _ => none

def sideU (t : Tm) : Option Bool := if t == uniqueTm then some true else if t == sharedTm then some false else none

def coerSides (G : UCtx) (q : Tm) : Option (Bool × Bool) := do
  let ⟨T, _⟩ ← (checkTm P G.Γ q).toOption
  match G.Γ.canon T with
  | .app (.tyc _ .nil) (.cons sa (.cons _ (.cons _ (.cons sb _)))) => some (← sideU sa, ← sideU sb)
  | _ => none

def primUses (G : UCtx) (u : Bool) : Prim → Option Uses
  | .tm t | .place t _ | .unplace t _ => G.termUses P u t
  | .coerce a _ q => do
    let (su, tu) ← G.coerSides P q
    if u && !tu then none else G.termUses P su a
  | .axm _ => if u && !G.cellOk then none else some []
  | .atom _ => some []
  | .lit t => if u then none else G.termUses P false t
  | _ => if u then none else some []

def fnCtx (G : UCtx) (Gr : Group) (F : FnDef) : UCtx :=
  let uq := G.uq ++ (((teleUs F.tele).take F.np).zipIdx.filterMap fun (u, k) =>
    if u then some (G.Γ.n + Gr.fns.length + k) else none)
  { G with Γ := (G.Γ.body Gr F).1, ents := [], scr := false, rebind := none, uscr := none, cellOk := false, uq := uq }

def defOK (G : UCtx) (Gr : Group) (O : Uses) : Bool :=
  Uses.sub O Gr.caps && Uses.sub Gr.caps O && Gr.caps.all (fun (i, u) => (G.use i u).isSome) &&
  (!Gr.caps.any (·.2) || (Gr.fns.filter (·.u)).length ≤ 1) &&
  Gr.fns.all (fun F => F.dele.all fun t => if t < G.Γ.n then Gr.caps.lookup t == some (F.u && G.Γ.fnU t) else true)

def cellTy (G : UCtx) (i : Nat) : Bool := match (G.Γ.tys[i]?).map G.Γ.canon with
  | some (.app (.tyc d _) _) => ((P.adts[d]?).map (·.opq)).getD false && P.placedD != some d && P.worldD != some d
  | _ => false

def arms (G : UCtx) (s : Tm) (er : Bool) : Option (Tm × Tm × List Arm) := do
  let ⟨St, _⟩ ← (checkTm P G.Γ s).toOption
  match G.Γ.canon St with
  | .app H idx => do let ⟨shp, _⟩ ← (shapeOf P G.Γ er H).toOption; some (H, idx, shp)
  | _ => none

def branchCtx (G : UCtx) (s k H idx sig : Tm) (fe ph uscr cell : Bool) : Option UCtx :=
  let Γg := { G.Γ with ghost := G.Γ.ghost || ph }
  match Γg.branch P s k H idx sig with
  | (Γf, .ok σ) =>
    let Γs := Γg.setErs { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)
    let Γb := { (if G.fill then Γs else Γg.advBr P Γs s k fe (sig.len - 1)) with cmode := false }
    let us := uscr && !fe
    some { G.next Γb (if us then (teleUs sig).dropLast else []) with uscr := if us && cell then some s else none }
  | _ => none

end UCtx

def Core.marked : Core → Bool
  | .chk (.mark _) _ _ _ => true
  | _ => false

mutual
def usesCore (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) : Core → UR
  | .ret ts => if G.Γ.ghost then some ([], []) else UR.lift (G.retUses P ru ts rets)
  | .call f dec args er ms ve rest => do
    let (t, outs, uf) ← G.callee P f args
    let Γ' := G.adv P (G.Γ.pushTele outs (some (ms.map (er || ·)))) (.call f dec args er ms ve rest)
    let C ← usesCore b (G.next Γ' (if er || G.Γ.ghost then [] else teleUs outs)) ru rets rest
    if er || G.Γ.ghost then some C else do
      let A ← G.termUses P uf f
      let B ← G.argsUses P (·.u) args t
      UR.seq (← Uses.seq A B, []) C
  | .mtch s R brs els er rest => do
    let C ← usesCore b (G.next (G.adv P (G.Γ.pushTele R (if er then some (List.replicate R.len true) else none))
      (.mtch s R brs els er rest)) (if er || G.Γ.ghost then [] else G.ents)) ru rets rest
    if er || G.Γ.ghost then some C else do
      let (H, idx, shp) ← G.arms P s er
      let S ← G.termUses P G.scr s
      let B ← usesArms b G G.ents R s H idx shp false true brs
      let E ← usesEls b G G.ents R s els
      UR.seq (← UR.seq (S, []) (UR.join B E)) C
  | .case s brs els er nt =>
    if G.Γ.ghost then some ([], []) else do
      let (H, idx, shp) ← G.arms P s er
      let S ← if er then some [] else G.termUses P G.scr s
      let B ← usesArms b G ru rets s H idx shp er (!nt) brs
      let E ← usesEls b { G with scr := G.scr && !er } ru rets s els
      UR.seq (S, []) (UR.join B E)
  | .seq R body rest => do
    let A := UR.below (← usesCore b { G with ents := [], uscr := none, cellOk := false, rebind := none } G.ents R body) G.Γ.n
    let C ← usesCore b (G.next (G.adv P (G.Γ.pushTele R) (.seq R body rest)) (if G.Γ.ghost then [] else G.ents)) ru rets rest
    UR.seq A C
  | .prim p er rest => do
    let T ← G.primTy P p
    let u := G.ents.headD false
    let C ← usesCore b (G.next (G.adv P (G.Γ.pushPrim P T er p) (.prim p er rest)) (if er || G.Γ.ghost then [] else [u])) ru rets rest
    if er || G.Γ.ghost then some C else UR.seq (← G.primUses P u p, []) C
  | .wdo w req rest => do
    let Tw ← G.primTy P (.wNext w)
    let A ← G.primTy P (.wAsk w req)
    let C ← usesCore b (G.next (G.adv P ((G.Γ.push Tw false).push A false) (.wdo w req rest))
      (if G.Γ.ghost then [] else [true, false])) ru rets rest
    if G.Γ.ghost then some C
    else if w.isFv && req.isFv then UR.seq (← Uses.seq (← G.termUses P true w) (← G.termUses P true req), []) C
    else none
  | .defLvl rest => usesCore b (G.next (G.adv P G.Γ.pushMint (.defLvl rest)) []) ru rets rest
  | .defFns gid rest => do
    let Gr ← P.groups[gid]?
    let C ← usesCore b (G.next (G.adv P (G.Γ.pushFns Gr) (.defFns gid rest)) (if G.Γ.ghost then [] else Gr.fns.map (·.u))) ru rets rest
    if h : gid < b then do
      let (O, K) ← usesFns gid G Gr Gr.fns
      let K := (gid, O) :: K
      if G.fill then UR.seq (O, K) C
      else if G.defOK Gr O then UR.seq (Gr.caps, K) C else none
    else none
  | .chk (.mark m) a _ rest => let G := { G with Γ := G.Γ.markPd m a }; match m, a with
    | .uq ms, _ => usesCore b { G with ents := ms } ru rets rest
    | .uqScr, _ => usesCore b { G with scr := true } ru rets rest
    | .rebind, _ => match hr : rest with
      | .prim _ true _ => usesCore b G ru rets rest
      | .prim (.tm t) false rest' => if G.rebind == some t then do
          let T ← G.primTy P (.tm t)
          usesCore b (G.next (G.adv P (G.Γ.pushPrim P T false (.tm t)) (.prim (.tm t) false rest')) (G.ents.take 1)) ru rets rest'
        else usesCore b G ru rets rest
      | _ => none
    | .reuse u, .fv i | .write u, .fv i =>
      if u && !G.Γ.ghost && !G.cellTy P i then none else do
      let C ← usesCore b { G with cellOk := true } ru rets rest
      if G.Γ.ghost then some C else UR.seq (← G.use i u, []) C
    | .alloc, _ => usesCore b { G with cellOk := true } ru rets rest
    | .cellOf, x => if G.Γ.ghost || G.uscr == some x then usesCore b { G with cellOk := true, uscr := none } ru rets rest
      else none
    | _, _ => usesCore b G ru rets rest
  | .chk (.opn oe) (.fv m) _ rest =>
    let Γo : Ctx := { G.Γ with opened := (m, oe) :: G.Γ.opened }
    match (G.Γ.tys[m]?).map G.Γ.canon with
    | some (.mtbl _ _ _ _ H cs) => match unify G.Γ.n (Γo.atoms P) G.Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
      | .ok σ' => usesCore b { G with Γ := { Γo with σ := σ' } } ru rets rest
      | _ => some ([], [])
    | _ => none
  | .chk .cm _ _ rest => usesCore b { G with Γ := { G.Γ with cmode := true } } ru rets rest
  | .chk .slf (.fv s) _ rest => match G.Γ.slotSelf s with
    | some Γ' => usesCore b { G with Γ := Γ' } ru rets rest
    | none => none
  | .chk _ _ _ rest => usesCore b G ru rets rest
  | .absurd _ | .dead => some ([], [])
termination_by c => (b, sizeOf c)

def usesArms (b : Nat) (G : UCtx) (ru : List Bool) (R s H idx : Tm) (shp : List Arm) (fe cell : Bool) : List Br → UR
  | [] => some ([], [])
  | (_, c, _, body) :: brs => do
    let U ← match shp[c]? with
      | some (k, sig, ph) => do
        let some Gb := G.branchCtx P s k H idx sig fe (!fe && ph) G.scr cell | some ([], [])
        some (UR.below (← usesCore b Gb ru R body) G.Γ.n)
      | none => none
    some (UR.join U (← usesArms b G ru R s H idx shp fe cell brs))
termination_by l => (b, sizeOf l)

def usesEls (b : Nat) (G : UCtx) (ru : List Bool) (R s : Tm) : Option Core → UR
  | none => some ([], [])
  | some e => do some (UR.below (← usesCore b { G with scr := false, ents := [], rebind := if G.scr && s.isFv then some s else none, uscr := none, cellOk := false } ru R e) G.Γ.n)
termination_by o => (b, sizeOf o)

def usesFns (gid : Nat) (G : UCtx) (Gr : Group) : List FnDef → UR
  | [] => some ([], [])
  | F :: Fs => do
    let U ← usesCore gid (G.fnCtx Gr F) ((teleUs F.tele).drop F.np) (G.Γ.body Gr F).2 F.body
    let O := UR.below U G.Γ.n
    if !F.u && O.1.any (·.2) || Gr.fns.zipIdx.any (fun (F', k) => F'.u && (U.1.lookup (G.Γ.n + k)).isSome) then none
    else UR.seq O (← usesFns gid G Gr Fs)
termination_by l => (gid, sizeOf l)
decreasing_by all_goals (cases F; simp_wf; omega)
end

def Prog.usesOK (P : Prog) (rets : Tm) : Bool := (usesCore P P.groups.length {Γ := {tys := #[]}} [] rets P.main).isSome

def Prog.fillCaps (P : Prog) (rets : Tm) : Prog :=
  match usesCore P P.groups.length {Γ := {tys := #[]}, fill := true} [] rets P.main with
  | some (_, K) => { P with groups := P.groups.zipIdx.map fun (G, gid) => { G with caps := (K.lookup gid).getD [] } }
  | none => P

end Minimal
