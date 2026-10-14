import Minimal.Strip

namespace Minimal

abbrev Blk := Nat × Nat × List Tm

structure Heap where
  blk : Nat → Option Blk := fun _ => none
  next : Nat := 0

def Heap.alloc (H : Heap) (b : Blk) : Heap × Nat :=
  ({ blk := fun a => if a = H.next then some b else H.blk a, next := H.next + 1 }, H.next)

def Heap.write (H : Heap) (a : Nat) (b : Blk) : Heap :=
  { H with blk := fun x => if x = a then some b else H.blk x }

variable (P : Prog)

def Prog.place (P : Prog) (H : Heap) : Tm → Heap × Tm
  | .app (.vc d c _) fs => let (H, a) := H.alloc (d, c, fs.toList); (H, .ptr a)
  | v => (H, v)

mutual
def Prog.build (P : Prog) (H : Heap) (f : Nat → Tm) : Tm → Heap × Tm
  | .fv i => (H, f i)
  | .vc d c _ => (H, .vc d c .nil)
  | .app h args =>
    let (H, args') := P.buildArgs H f args
    match P.subU f h with
    | .vc d c _ => match P.wrapField d c with
      | some k => (H, args'.toList.getD k .nil)
      | none => P.place H (P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) args')))
    | h' => (H, .app h' args')
  | t => (H, t.subst f)

def Prog.buildArgs (P : Prog) (H : Heap) (f : Nat → Tm) : Tm → Heap × Tm
  | .cons a as =>
    let (H, a') := P.build H f a
    let (H, as') := P.buildArgs H f as
    (H, .cons a' as')
  | t => (H, t.subst f)
end

def Prog.buildList (P : Prog) (H : Heap) (f : Nat → Tm) : List Tm → Heap × List Tm
  | [] => (H, [])
  | t :: ts =>
    let (H, v) := P.build H f t
    let (H, vs) := P.buildList H f ts
    (H, v :: vs)

def Prog.viewM (P : Prog) (H : Heap) : Tm → Tm
  | .ptr a => match H.blk a with
    | some (d, c, ws) => .app (.vc d c .nil) (.ofList ws)
    | none => .ptr a
  | v => P.view v

def Prog.evalM (P : Prog) (H : Heap) (ρ : List Tm) : Prim → Heap × Tm
  | .tm t | .lit t | .coerce t _ _ => P.build H (Tm.env ρ) t
  | p => (H, p.evalS P ρ)

def Prog.reuse (P : Prog) (H : Heap) (ρ : List Tm) (u : Nat) : Tm → Option (Heap × Tm)
  | .app h args => match Tm.env ρ u, P.subU (Tm.env ρ) h with
    | .ptr a, .vc d c _ =>
      if P.wrapField d c = none ∧ P.natD ≠ some d then
        let (H, args') := P.buildArgs H (Tm.env ρ) args
        some (H.write a (d, c, (maskArgs (P.ctorErs d c) args').toList), .ptr a)
      else none
    | _, _ => none
  | _ => none

def Chk.plain : Chk → Bool
  | .mark (.reuse true) | .mark .alloc => false
  | _ => true

inductive RunM : Heap → List Tm → Core → Heap → List Tm → Prop
  | ret : P.buildList H (Tm.env ρ) ts.toList = (H', vs) → RunM H ρ (.ret ts) H' vs
  | callE : RunM H (ρ ++ List.replicate ms.length .tok) rest H' out → RunM H ρ (.call f dec args true ms ve rest) H' out
  | call : P.subU (Tm.env ρ) f = .clo env gid j → P.groups[gid]? = some G → G.fns[j]? = some F →
      P.buildList H (Tm.env ρ) args.toList = (H1, as) →
      RunM H1 (env.toList ++ closuresS env.toList gid G ++ F.spreadIn ve as) F.body H2 outs →
      RunM H2 (ρ ++ F.spreadOut ve args.toList.length outs) rest H' out → RunM H ρ (.call f dec args false ms ve rest) H' out
  | mtchE : RunM H (ρ ++ List.replicate R.len .tok) rest H' out → RunM H ρ (.mtch s R brs els true rest) H' out
  | mtch : P.build H (Tm.env ρ) s = (H1, w) → P.viewM H1 w = .app (.vc d c ls) vs →
      selectBr brs els c vs.toList = some (pre, body) →
      RunM H1 (ρ ++ pre) body H2 outs → RunM H2 (ρ ++ outs) rest H' out → RunM H ρ (.mtch s R brs els false rest) H' out
  | caseE : realBr brs els = some (pre, body) → RunM H (ρ ++ pre) body H' out → RunM H ρ (.case s brs els true nt) H' out
  | caseN : realBr brs els = some (pre, body) → P.build H (Tm.env ρ) s = (H1, w) →
      RunM H1 (ρ ++ pre.map fun _ => w) body H' out → RunM H ρ (.case s brs els false true) H' out
  | case : P.build H (Tm.env ρ) s = (H1, w) → P.viewM H1 w = .app (.vc d c ls) vs →
      selectBr brs els c vs.toList = some (pre, body) →
      RunM H1 (ρ ++ pre) body H' out → RunM H ρ (.case s brs els false false) H' out
  | seq : RunM H ρ body H1 outs → RunM H1 (ρ ++ outs) rest H' out → RunM H ρ (.seq R body rest) H' out
  | prim : (if er then (H, Tm.tok) else P.evalM H ρ p) = (H1, v) → RunM H1 (ρ ++ [v]) rest H' out →
      RunM H ρ (.prim p er rest) H' out
  | defLvl : RunM H (ρ ++ [.tok]) rest H' out → RunM H ρ (.defLvl rest) H' out
  | defFns : P.groups[gid]? = some G → RunM H (ρ ++ closuresS ρ gid G) rest H' out → RunM H ρ (.defFns gid rest) H' out
  | chk : k.plain = true → RunM H ρ rest H' out → RunM H ρ (.chk k a b rest) H' out
  | reuse : P.reuse H ρ u t = some (H1, v) → RunM H1 (ρ ++ [v]) rest H' out →
      RunM H ρ (.chk (.mark (.reuse true)) (.fv u) x (.prim (.tm t) false rest)) H' out
  | reuseNo : (∀ u' t' rest', a = .fv u' → c = .prim (.tm t') false rest' → P.reuse H ρ u' t' = none) →
      RunM H ρ c H' out → RunM H ρ (.chk (.mark (.reuse true)) a x c) H' out
  | alloc : H.alloc (0, 0, []) = (H1, a) → RunM H1 (ρ ++ [.ptr a]) rest H' out →
      RunM H ρ (.chk (.mark .alloc) x y (.prim (.axm T) false rest)) H' out
  | allocNo : (∀ T rest', c ≠ .prim (.axm T) false rest') → RunM H ρ c H' out → RunM H ρ (.chk (.mark .alloc) x y c) H' out

mutual
inductive MDec (H : Heap) : Tm → Tm → Prop
  | ptr : H.blk a = some (d, c, ws) → MDecs H ws vs → MDec H (.ptr a) (.app (.vc d c .nil) (.ofList vs))
  | clo : P.groups[gid]? = some G → envM.length = envS.length →
      (∀ i, G.ers.getD i true = false → MDec H (Tm.env envM i) (Tm.env envS i)) →
      MDec H (.clo (.ofList envM) gid j) (.clo (.ofList envS) gid j)
  | tok : MDec H w .tok
  | nat : MDec H (.nat n) (.nat n)
  | vc : MDec H (.vc d c .nil) (.vc d c .nil)

inductive MDecs (H : Heap) : List Tm → List Tm → Prop
  | nil : MDecs H [] []
  | cons : MDec H w v → MDecs H ws vs → MDecs H (w :: ws) (v :: vs)
end

end Minimal
