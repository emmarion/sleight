import Minimal.Eval

set_option linter.unusedVariables false

namespace Minimal

structure FHeap where
  blk : Nat → Option Tm := fun _ => none
  next : Nat := 0

namespace FHeap

def alloc (H : FHeap) (t : Tm) : FHeap × Nat :=
  ({ blk := fun a => if a = H.next then some t else H.blk a, next := H.next + 1 }, H.next)

def box (H : FHeap) : Tm → FHeap × Tm
  | .app (.vc d c ls) args =>
    let (H, args) := H.box args
    let (H, a) := H.alloc (.app (.vc d c ls) args)
    (H, .ptr a)
  | .cons h t =>
    let (H, h) := H.box h
    let (H, t) := H.box t
    (H, .cons h t)
  | t => (H, t)

def boxList (H : FHeap) : List Tm → FHeap × List Tm
  | [] => (H, [])
  | t :: ts =>
    let (H, w) := H.box t
    let (H, ws) := H.boxList ts
    (H, w :: ws)

def dec (H : FHeap) : Nat → Tm → Tm
  | n + 1, .ptr a => match H.blk a with
    | some t => H.dec n t
    | none => .ptr a
  | n, .cons h t => .cons (H.dec n h) (H.dec n t)
  | n, .app h a => .app (H.dec n h) (H.dec n a)
  | n, .tyc d ls => .tyc d (H.dec n ls)
  | n, .vc d c ls => .vc d c (H.dec n ls)
  | n, .bind k a r => .bind k (H.dec n a) (H.dec n r)
  | n, .tyCtor p => .tyCtor (H.dec n p)
  | n, .valCtor p => .valCtor (H.dec n p)
  | n, .predates A x L => .predates (H.dec n A) (H.dec n x) (H.dec n L)
  | n, .subterm A a B b => .subterm (H.dec n A) (H.dec n a) (H.dec n B) (H.dec n b)
  | n, .fn l np t u hm => .fn (H.dec n l) np (H.dec n t) u hm
  | n, .mtbl u nt ex ph T cs => .mtbl u nt ex ph (H.dec n T) (H.dec n cs)
  | n, .clo env gid j => .clo (H.dec n env) gid j
  | _, t => t

def decode (H : FHeap) (w : Tm) : Tm := H.dec H.next w

def view (H : FHeap) : Tm → Tm
  | .ptr a => (H.blk a).getD (.ptr a)
  | t => t

end FHeap

variable (P : Prog)

def Prim.evalH (H : FHeap) (ρ : List Tm) : Prim → FHeap × Tm
  | .wAsk w req => H.box (P.answer (w.subst (Tm.env ρ)) (H.view (req.subst (Tm.env ρ)))).2
  | p => H.box (p.eval P ρ)

def evalH (μ : Option (List Nat)) (H : FHeap) (ρ : List Tm) (cnt : Nat) : Core → Except String (FHeap × List Tm × Nat)
  | .ret ts =>
    let (H, ws) := H.boxList (ts.toList.map (·.subst (Tm.env ρ)))
    .ok (H, ws, cnt)
  | .call f _ args _ _ _ rest =>
    match callee P (f.subst (Tm.env ρ)) with
    | some (env, n, gid, G, F) =>
      let (H, argv) := H.boxList (args.toList.map (·.subst (Tm.env ρ)))
      let μ' := some (n :: (markedArgs F.tele (.ofList argv)).map fun w => (H.decode w).size)
      if h : muLt P.k μ' μ then
        match evalH μ' H (env ++ closures env gid G ++ argv) cnt F.body with
        | .ok (H, outs, cnt) => evalH μ H (ρ ++ outs) cnt rest
        | .error e => .error e
      else .error "call does not decrease"
    | none => .error "callee is not a function"
  | .mtch s _ brs els _ rest =>
    match H.view (s.subst (Tm.env ρ)) with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) =>
        match evalH μ H (ρ ++ pre) cnt body with
        | .ok (H, outs, cnt) => evalH μ H (ρ ++ outs) cnt rest
        | .error e => .error e
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .prim p _ rest =>
    let (H, w) := p.evalH P H ρ
    evalH μ H (ρ ++ [w]) cnt rest
  | .wdo w req rest =>
    let (H, w1) := (Prim.wNext w).evalH P H ρ
    let (H, w2) := (Prim.wAsk w req).evalH P H ρ
    evalH μ H (ρ ++ [w1, w2]) cnt rest
  | .defLvl rest => evalH μ H (ρ ++ [.lvl cnt]) (cnt + 1) rest
  | .defFns gid rest =>
    match P.groups[gid]? with
    | some G => evalH μ H (ρ ++ closures ρ gid G) cnt rest
    | none => .error "no group"
  | .chk _ _ _ rest => evalH μ H ρ cnt rest
  | .absurd body => match evalH μ H ρ cnt body with
    | .ok _ => .error "an absurd body returned"
    | .error e => .error e
  | .dead => .error "a refuted branch was reached"
  | .case s brs els _ _ =>
    match H.view (s.subst (Tm.env ρ)) with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) => evalH μ H (ρ ++ pre) cnt body
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .seq _ body rest =>
    match evalH μ H ρ cnt body with
    | .ok (H, outs, cnt) => evalH μ H (ρ ++ outs) cnt rest
    | .error e => .error e
termination_by c => ((⟨μ⟩ : Mu P.k), sizeOf c)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ h
    | (apply Prod.Lex.right; simp; try omega)
  all_goals (have := sizeOf_selectBr hb; simp; omega)

end Minimal
