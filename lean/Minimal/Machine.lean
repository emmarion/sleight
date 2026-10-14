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

def Prog.rd (gid i : Nat) : Bool := ((P.groups[gid]?).map fun G => G.caps.any (·.1 == i)).getD false

mutual
inductive MDec (H : Heap) : Tm → Tm → Prop
  | ptr : H.blk a = some (d, c, ws) → MDecs H ws vs → MDec H (.ptr a) (.app (.vc d c .nil) (.ofList vs))
  | clo : envM.length = envS.length → (∀ i, P.rd gid i = true → MDec H (Tm.env envM i) (Tm.env envS i)) →
      MDec H (.clo (.ofList envM) gid j) (.clo (.ofList envS) gid j)
  | tok : (w = .tok ∨ ∃ a, w = .ptr a) → MDec H w .tok
  | nat : MDec H (.nat n) (.nat n)
  | vc : MDec H (.vc d c .nil) (.vc d c .nil)
  | nil : MDec H .nil .nil

inductive MDecs (H : Heap) : List Tm → List Tm → Prop
  | nil : MDecs H [] []
  | cons : MDec H w v → MDecs H ws vs → MDecs H (w :: ws) (v :: vs)
end

inductive Foot (H : Heap) : Tm → Tm → Nat → Prop
  | here : Foot H (.ptr a) v a
  | field {k : Nat} {vs : Tm} : H.blk a = some (d, c, ws) → ws[k]? = some w → vs.toList[k]? = some v → Foot H w v b →
      Foot H (.ptr a) (.app (.vc d c .nil) vs) b
  | clo {eM eS : Tm} : P.rd gid i = true → Foot H (Tm.env eM.toList i) (Tm.env eS.toList i) b →
      Foot H (.clo eM gid j) (.clo eS gid j) b

def Heap.WF (H : Heap) : Prop := ∀ a, H.next ≤ a → H.blk a = none

def Heap.Ext (H H' : Heap) : Prop := H.next ≤ H'.next ∧ ∀ a b, H.blk a = some b → H'.blk a = some b

def Agree (H H' : Heap) (S : Nat → Prop) : Prop := ∀ a, S a → H'.blk a = H.blk a

variable {P}

theorem Heap.Ext.refl (H : Heap) : H.Ext H := ⟨Nat.le_refl _, fun _ _ h => h⟩

theorem Heap.Ext.trans {H1 H2 H3 : Heap} (a : H1.Ext H2) (b : H2.Ext H3) : H1.Ext H3 :=
  ⟨Nat.le_trans a.1 b.1, fun x y h => b.2 x y (a.2 x y h)⟩

theorem Heap.alloc_ext {H : Heap} (hW : H.WF) (b : Blk) : H.Ext (H.alloc b).1 ∧ (H.alloc b).1.WF := by
  refine ⟨⟨by simp [Heap.alloc], fun a b' h => ?_⟩, fun a ha => ?_⟩
  · simp only [Heap.alloc]
    have : a ≠ H.next := fun e => by rw [e, hW _ (Nat.le_refl _)] at h; cases h
    simp [this, h]
  · simp only [Heap.alloc] at ha ⊢
    rw [ite_eq_right_iff.mpr (by omega)]; exact hW a (by omega)

theorem Heap.alloc_new (H : Heap) (b : Blk) : (H.alloc b).1.blk (H.alloc b).2 = some b := by simp [Heap.alloc]

mutual
theorem MDec.mono {H H' : Heap} (he : H.Ext H') : ∀ {w v : Tm}, MDec P H w v → MDec P H' w v
  | _, _, .ptr hb hs => .ptr (he.2 _ _ hb) (MDecs.mono he hs)
  | _, _, .clo hl hs => .clo hl fun i hi => (hs i hi).mono he
  | _, _, .tok h => .tok h
  | _, _, .nat => .nat
  | _, _, .vc => .vc
  | _, _, .nil => .nil

theorem MDecs.mono {H H' : Heap} (he : H.Ext H') : ∀ {ws vs : List Tm}, MDecs P H ws vs → MDecs P H' ws vs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.mono he) (MDecs.mono he hs)
end

theorem MDecs.get {H : Heap} : ∀ {ws vs : List Tm}, MDecs P H ws vs → ∀ (k : Nat) w v, ws[k]? = some w → vs[k]? = some v →
    MDec P H w v
  | _, _, .cons h _, 0, _, _, h1, h2 => by simp at h1 h2; subst h1 h2; exact h
  | _, _, .cons _ hs, k + 1, _, _, h1, h2 => hs.get k _ _ (by simpa using h1) (by simpa using h2)
  | _, _, .nil, _, _, _, h1, _ => by simp at h1

mutual
theorem MDec.frame {H H' : Heap} : ∀ {w v : Tm}, MDec P H w v → Agree H H' (Foot P H w v) → MDec P H' w v
  | _, _, .ptr hb hs, hA => .ptr (by rw [hA _ .here]; exact hb)
      (MDecs.frame hs fun k w v hw hv a ha => hA a (.field hb hw (by rw [Tm.toList_ofList]; exact hv) ha))
  | _, _, .clo hl hs, hA => .clo hl fun i hi => (hs i hi).frame fun a ha =>
      hA a (.clo hi (by rw [Tm.toList_ofList, Tm.toList_ofList]; exact ha))
  | _, _, .tok h, _ => .tok h
  | _, _, .nat, _ => .nat
  | _, _, .vc, _ => .vc
  | _, _, .nil, _ => .nil

theorem MDecs.frame {H H' : Heap} : ∀ {ws vs : List Tm}, MDecs P H ws vs →
    (∀ (k : Nat) w v, ws[k]? = some w → vs[k]? = some v → Agree H H' (Foot P H w v)) → MDecs P H' ws vs
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, hA => .cons (h.frame (hA 0 _ _ (by simp) (by simp)))
      (MDecs.frame hs fun k w v hw hv => hA (k + 1) w v (by simpa using hw) (by simpa using hv))
end

end Minimal
