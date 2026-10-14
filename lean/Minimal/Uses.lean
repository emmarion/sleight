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

def teleUs : Tm → List Bool
  | .bind k _ r => k.u :: teleUs r
  | _ => []

structure UCtx where
  Γ : Ctx
  uq : List Nat := []
  scr : Bool := false
  ents : List Bool := []
  rebind : Option Tm := none

variable (P : Prog)

namespace UCtx

def next (G : UCtx) (Γ' : Ctx) (us : List Bool) : UCtx :=
  { Γ := Γ', uq := G.uq ++ (us.zipIdx.filterMap fun (u, k) => if u then some (G.Γ.n + k) else none) }

def sigOf (G : UCtx) (h : Tm) : Option Tm := match checkTm P G.Γ h with
  | .ok ⟨H, _⟩ => match G.Γ.canon H with
    | .valCtor sig | .tyCtor sig => some sig
    | _ => none
  | .error _ => none

def use (G : UCtx) (i : Nat) (u : Bool) : Option Uses :=
  if u && !G.uq.contains i then none else some [(i, u)]

mutual
def termUses (G : UCtx) (u : Bool) : Tm → Option Uses
  | .fv i => G.use i u
  | .app h args => match G.sigOf P h with
    | some sig => G.argsUses (fun k => u && k.u) args sig
    | none => none
  | .vc .. | .tyc .. | .nil => some []
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

def coerSrc (G : UCtx) (q : Tm) : Option Bool := do
  let ⟨T, _⟩ ← (checkTm P G.Γ q).toOption
  match G.Γ.canon T with
  | .app (.tyc _ .nil) (.cons sa _) => some (sa == uniqueTm)
  | _ => none

def primUses (G : UCtx) (u : Bool) : Prim → Option Uses
  | .tm t => G.termUses P u t
  | .coerce a _ q => do G.termUses P (← G.coerSrc P q) a
  | _ => some []

def arms (G : UCtx) (s : Tm) (er : Bool) : Option (Tm × Tm × List Arm) := do
  let ⟨St, _⟩ ← (checkTm P G.Γ s).toOption
  match G.Γ.canon St with
  | .app H idx => do let ⟨shp, _⟩ ← (shapeOf P G.Γ er H).toOption; some (H, idx, shp)
  | _ => none

def branchCtx (G : UCtx) (s k H idx sig : Tm) (fe ph uscr : Bool) : Option UCtx :=
  match G.Γ.branch P s k H idx sig with
  | (Γf, .ok σ) =>
    let Γb := G.Γ.setErs { Γf with σ := σ } (if fe then some (List.replicate (sig.len - 1) true) else none)
    some (G.next { Γb with ghost := G.Γ.ghost || ph } (if uscr && !fe then (teleUs sig).dropLast else []))
  | _ => none

end UCtx

def Core.marked : Core → Bool
  | .chk (.mark _) _ _ _ => true
  | _ => false

mutual
def usesCore (b : Nat) (G : UCtx) (ru : List Bool) (rets : Tm) : Core → Option Uses
  | .ret ts => if G.Γ.ghost then some [] else G.retUses P ru ts rets
  | .call f _ args er ms _ rest => do
    let (t, outs, uf) ← G.callee P f args
    let Γ' := G.Γ.pushTele outs (some (ms.map (er || ·)))
    let C ← usesCore b (G.next Γ' (if er || G.Γ.ghost then [] else teleUs outs)) ru rets rest
    if er || G.Γ.ghost then some C else do
      let A ← G.termUses P uf f
      let B ← G.argsUses P (·.u) args t
      Uses.seq (← Uses.seq A B) C
  | .mtch s R brs els er rest => do
    let C ← usesCore b (G.next (G.Γ.pushTele R (if er then some (List.replicate R.len true) else none))
      (if er || G.Γ.ghost then [] else G.ents)) ru rets rest
    if er || G.Γ.ghost then some C else do
      let (H, idx, shp) ← G.arms P s er
      let S ← G.termUses P G.scr s
      let B ← usesArms b G G.ents R s H idx shp false brs
      let E ← usesEls b G G.ents R s els
      Uses.seq (← Uses.seq S (Uses.join B E)) C
  | .case s brs els er _ =>
    if G.Γ.ghost then some [] else do
      let (H, idx, shp) ← G.arms P s er
      let S ← if er then some [] else G.termUses P G.scr s
      let B ← usesArms b G ru rets s H idx shp er brs
      let E ← usesEls b G ru rets s els
      Uses.seq S (Uses.join B E)
  | .seq R body rest => do
    let A := Uses.below (← usesCore b { G with ents := [] } G.ents R body) G.Γ.n
    let C ← usesCore b (G.next (G.Γ.pushTele R) (if G.Γ.ghost then [] else G.ents)) ru rets rest
    Uses.seq A C
  | .prim p er rest => do
    let T ← G.primTy P p
    let u := G.ents.headD false
    let C ← usesCore b (G.next (G.Γ.pushPrim T er p) (if er || G.Γ.ghost then [] else [u])) ru rets rest
    if er || G.Γ.ghost then some C else Uses.seq (← G.primUses P u p) C
  | .defLvl rest => usesCore b (G.next G.Γ.pushMint []) ru rets rest
  | .defFns gid rest => do
    let Gr ← P.groups[gid]?
    let C ← usesCore b (G.next (G.Γ.pushFns Gr) (if G.Γ.ghost then [] else Gr.fns.map (·.u))) ru rets rest
    if h : gid < b then Uses.seq (← usesFns gid G Gr Gr.fns) C else none
  | .chk (.mark m) a _ rest => match m, a with
    | .uq ms, _ => usesCore b { G with ents := ms } ru rets rest
    | .uqScr, _ => usesCore b { G with scr := true } ru rets rest
    | .rebind, _ => match hr : rest with
      | .prim _ true _ => usesCore b G ru rets rest
      | .prim (.tm t) false rest' => if G.rebind == some t then do
          let T ← G.primTy P (.tm t)
          usesCore b (G.next (G.Γ.pushPrim T false (.tm t)) (G.ents.take 1)) ru rets rest'
        else none
      | _ => none
    | .reuse u, .fv i | .write u, .fv i => do
      let C ← usesCore b G ru rets rest
      if G.Γ.ghost then some C else Uses.seq (← G.use i u) C
    | _, _ => usesCore b G ru rets rest
  | .chk (.opn oe) (.fv m) _ rest =>
    let Γo : Ctx := { G.Γ with opened := (m, oe) :: G.Γ.opened }
    match (G.Γ.tys[m]?).map G.Γ.canon with
    | some (.mtbl _ _ _ _ H cs) => match unify G.Γ.n (Γo.atoms P) G.Γ.σ [] (Γo.openEqs P (H :: cs.toList)) with
      | .ok σ' => usesCore b { G with Γ := { Γo with σ := σ' } } ru rets rest
      | _ => some []
    | _ => none
  | .chk _ _ _ rest => usesCore b G ru rets rest
  | .absurd _ | .dead => some []
termination_by c => (b, sizeOf c)

def usesArms (b : Nat) (G : UCtx) (ru : List Bool) (R s H idx : Tm) (shp : List Arm) (fe : Bool) : List Br → Option Uses
  | [] => some []
  | (_, c, _, body) :: brs => do
    let U ← match shp[c]? with
      | some (k, sig, ph) => do
        let some Gb := G.branchCtx P s k H idx sig fe (!fe && ph) G.scr | some []
        some (Uses.below (← usesCore b Gb ru R body) G.Γ.n)
      | none => none
    some (Uses.join U (← usesArms b G ru R s H idx shp fe brs))
termination_by l => (b, sizeOf l)

def usesEls (b : Nat) (G : UCtx) (ru : List Bool) (R s : Tm) : Option Core → Option Uses
  | none => some []
  | some e => do some (Uses.below (← usesCore b { G with scr := false, ents := [], rebind := some s } ru R e) G.Γ.n)
termination_by o => (b, sizeOf o)

def usesFns (gid : Nat) (G : UCtx) (Gr : Group) : List FnDef → Option Uses
  | [] => some []
  | F :: Fs => do
    let (Γb, R) := G.Γ.body Gr F
    let ps := (teleUs F.tele).take F.np
    let Ub := { G with Γ := Γb, uq := G.uq ++ (ps.zipIdx.filterMap fun (u, k) => if u then some (G.Γ.n + Gr.fns.length + k) else none) }
    let U ← usesCore gid Ub ((teleUs F.tele).drop F.np) R F.body
    let O := Uses.below U G.Γ.n
    if !F.u && O.any (·.2) then none
    else Uses.seq O (← usesFns gid G Gr Fs)
termination_by l => (gid, sizeOf l)
decreasing_by all_goals (cases F; simp_wf; omega)
end

end Minimal
