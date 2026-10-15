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

mutual
def Heap.placeDeep (H : Heap) : Tm → Heap × Tm
  | .app (.vc d c _) fs => let (H, ws) := H.placeDeepL fs; let (H, a) := H.alloc (d, c, ws); (H, .ptr a)
  | v => (H, v)

def Heap.placeDeepL (H : Heap) : Tm → Heap × List Tm
  | .cons a as => let (H, w) := H.placeDeep a; let (H, ws) := H.placeDeepL as; (H, w :: ws)
  | _ => (H, [])
end

def Prog.viewM (P : Prog) (H : Heap) : Tm → Tm
  | .ptr a => match H.blk a with
    | some (d, c, ws) => .app (.vc d c .nil) (.ofList ws)
    | none => .ptr a
  | v => P.view v

def Prog.evalM (P : Prog) (H : Heap) (ρ : List Tm) : Prim → Heap × Tm
  | .tm t | .lit t | .coerce t _ _ | .place t _ | .unplace t _ => P.build H (Tm.env ρ) t
  | p => (H, p.evalS P ρ)

def Prog.askM (P : Prog) (H : Heap) (w req : Tm) : Heap × Tm := H.placeDeep (P.answer w (P.viewM H req)).1

def Prog.reuse (P : Prog) (H : Heap) (ρ : List Tm) (u : Nat) : Tm → Option (Heap × Tm)
  | .app h args => match Tm.env ρ u, P.subU (Tm.env ρ) h with
    | .ptr a, .vc d c _ =>
      if P.wrapField d c = none ∧ P.natD ≠ some d then
        let (H, args') := P.buildArgs H (Tm.env ρ) args
        some (H.write a (d, c, (maskArgs (P.ctorErs d c) args').toList), .ptr a)
      else none
    | _, _ => none
  | _ => none

def Mark.pend : Mark → Bool
  | .reuse true | .alloc | .cellOf | .write true => true
  | _ => false

abbrev Pend := Option (Mark × Tm)

def Prog.evalP (P : Prog) (H : Heap) (ρ : List Tm) : Pend → Prim → Heap × Tm
  | some (.reuse true, .fv u), .tm t => ((P.reuse H ρ u t).getD (P.build H (Tm.env ρ) t))
  | some (.alloc, _), .axm _ => let (H, a) := H.alloc (0, 0, []); (H, .ptr a)
  | some (.cellOf, .fv x), .axm _ | some (.write true, .fv x), .axm _ => (H, match Tm.env ρ x with
    | .ptr a => .ptr a
    | _ => .tok)
  | _, p => P.evalM H ρ p

inductive RunM : Heap → List Tm → Pend → Core → Heap → List Tm → Prop
  | ret : P.buildList H (Tm.env ρ) ts.toList = (H', vs) → RunM H ρ pd (.ret ts) H' vs
  | callE : RunM H (ρ ++ List.replicate ms.length .tok) none rest H' out → RunM H ρ pd (.call f dec args true ms ve rest) H' out
  | call : P.subU (Tm.env ρ) f = .clo env gid j → P.groups[gid]? = some G → G.fns[j]? = some F →
      P.buildList H (Tm.env ρ) (maskArgs (ve.getD []) args).toList = (H1, as) →
      RunM H1 (env.toList ++ closuresS env.toList gid G ++ F.spreadIn ve as) none F.body H2 outs →
      RunM H2 (ρ ++ F.spreadOut ve args.toList.length outs) none rest H' out →
      RunM H ρ pd (.call f dec args false ms ve rest) H' out
  | mtchE : RunM H (ρ ++ List.replicate R.len .tok) none rest H' out → RunM H ρ pd (.mtch s R brs els true rest) H' out
  | mtch : P.build H (Tm.env ρ) s = (H1, w) → P.viewM H1 w = .app (.vc d c ls) vs →
      selectBr brs els c vs.toList = some (pre, body) →
      RunM H1 (ρ ++ pre) none body H2 outs → RunM H2 (ρ ++ outs) none rest H' out →
      RunM H ρ pd (.mtch s R brs els false rest) H' out
  | caseE : realBr brs els = some (pre, body) → RunM H (ρ ++ pre) none body H' out →
      RunM H ρ pd (.case s brs els true nt) H' out
  | caseN : realBr brs els = some (pre, body) → P.build H (Tm.env ρ) s = (H1, w) →
      RunM H1 (ρ ++ pre.map fun _ => w) none body H' out → RunM H ρ pd (.case s brs els false true) H' out
  | case : P.build H (Tm.env ρ) s = (H1, w) → P.viewM H1 w = .app (.vc d c ls) vs →
      selectBr brs els c vs.toList = some (pre, body) →
      RunM H1 (ρ ++ pre) none body H' out → RunM H ρ pd (.case s brs els false false) H' out
  | seq : RunM H ρ none body H1 outs → RunM H1 (ρ ++ outs) none rest H' out → RunM H ρ pd (.seq R body rest) H' out
  | prim : (if er then (H, Tm.tok) else P.evalP H ρ pd p) = (H1, v) → RunM H1 (ρ ++ [v]) none rest H' out →
      RunM H ρ pd (.prim p er rest) H' out
  | wdo : P.askM H (P.sub ρ w) (P.sub ρ req) = (H1, v) → RunM H1 (ρ ++ [(P.sub ρ w).wnext, v]) none rest H' out →
      RunM H ρ pd (.wdo w req rest) H' out
  | defLvl : RunM H (ρ ++ [.tok]) none rest H' out → RunM H ρ pd (.defLvl rest) H' out
  | defFns : P.groups[gid]? = some G → RunM H (ρ ++ closuresS ρ gid G) none rest H' out →
      RunM H ρ pd (.defFns gid rest) H' out
  | mark : m.pend = true → RunM H ρ (some (m, a)) rest H' out → RunM H ρ pd (.chk (.mark m) a b rest) H' out
  | chk : (∀ m, k = .mark m → m.pend = false) → RunM H ρ pd rest H' out → RunM H ρ pd (.chk k a b rest) H' out

def Prog.fnU (gid j : Nat) : Bool := (((P.groups[gid]?).bind (·.fns[j]?)).map fun F => F.u && F.dele.isNone).getD false

def Prog.rd (gid j i : Nat) : Bool :=
  ((P.groups[gid]?).map fun G => (G.caps.lookup i).any fun u => !u || P.fnU gid j).getD false

mutual
inductive MDec (H : Heap) : Tm → Tm → Prop
  | ptr : H.blk a = some (d, c, ws) → MDecs H ws vs → MDec H (.ptr a) (.app (.vc d c .nil) (.ofList vs))
  | clo : envM.length = envS.length → (∀ i, P.rd gid j i = true → MDec H (Tm.env envM i) (Tm.env envS i)) →
      MDec H (.clo (.ofList envM) gid j) (.clo (.ofList envS) gid j)
  | tok : (w = .tok ∨ ∃ a, w = .ptr a ∧ (H.blk a).isSome) → MDec H w .tok
  | nat : MDec H (.nat n) (.nat n)
  | wld : MDec H (.wld k) (.wld k)
  | vc : MDec H (.vc d c .nil) (.vc d c .nil)
  | imm : MDec H (.app (.vc d c .nil) .nil) (.app (.vc d c .nil) .nil)
  | nil : MDec H .nil .nil

inductive MDecs (H : Heap) : List Tm → List Tm → Prop
  | nil : MDecs H [] []
  | cons : MDec H w v → MDecs H ws vs → MDecs H (w :: ws) (v :: vs)
end

inductive Foot (H : Heap) : Tm → Tm → Nat → Prop
  | here : Foot H (.ptr a) v a
  | field {k : Nat} {vs : Tm} : H.blk a = some (d, c, ws) → ws[k]? = some w → vs.toList[k]? = some v → Foot H w v b →
      Foot H (.ptr a) (.app (.vc d c .nil) vs) b
  | clo {eM eS : Tm} : P.rd gid j i = true → Foot H (Tm.env eM.toList i) (Tm.env eS.toList i) b →
      Foot H (.clo eM gid j) (.clo eS gid j) b

def Prog.rdU (gid j i : Nat) : Bool :=
  P.fnU gid j && ((P.groups[gid]?).map fun G => G.caps.lookup i == some true).getD false

inductive Spine (H : Heap) : Tm → Tm → Tm → Nat → Prop
  | top {vs : Tm} : P.wrapField d c = none → Spine H (.ptr a) u (.app (.vc d c ls) vs) a
  | field {k : Nat} {vsS vs : Tm} : H.blk a = some (d, c, ws) → P.wrapField d c = none → P.ctor d c = some sig →
      (sig.skip (P.lifted d)).uAt k = true → ws[k]? = some w → vsS.toList[k]? = some u → vs.toList[k]? = some v →
      Spine H w u v b → Spine H (.ptr a) (.app (.vc d c .nil) vsS) (.app (.vc d c ls) vs) b
  | wrap {k : Nat} {vs : Tm} : P.wrapField d c = some k → P.ctor d c = some sig → (sig.skip (P.lifted d)).uAt k = true →
      vs.toList[k]? = some v → Spine H w u v b → Spine H w u (.app (.vc d c ls) vs) b
  | clo {eM eS eF : Tm} : P.rdU gid j i = true →
      Spine H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i) b →
      Spine H (.clo eM gid j) (.clo eS gid j) (.clo eF gid j) b
  | cell : Spine H (.ptr a) u .tok a
  | dele {eF : Tm} {G : Group} {F : FnDef} : P.groups[gid]? = some G → G.fns[j]? = some F → F.dele = some t → F.u = true →
      Spine H w u (Tm.env (eF.toList ++ closures eF.toList gid G) t) b → Spine H w u (.clo eF gid j) b

def Disj (A B : Nat → Prop) : Prop := ∀ a, A a → B a → False

inductive WO (H : Heap) : Tm → Tm → Tm → Prop
  | ptr {vsS vs : Tm} : H.blk a = some (d, c, ws) → P.wrapField d c = none → P.ctor d c = some sig →
      (∀ (k : Nat) w u, ws[k]? = some w → vsS.toList[k]? = some u → ¬ Foot P H w u a) →
      (∀ (k : Nat) w u v, (sig.skip (P.lifted d)).uAt k = true → ws[k]? = some w → vsS.toList[k]? = some u →
        vs.toList[k]? = some v → WO H w u v) →
      (∀ (k : Nat) w u v, (sig.skip (P.lifted d)).uAt k = true → ws[k]? = some w → vsS.toList[k]? = some u →
        vs.toList[k]? = some v → ∀ (j : Nat) w' u', j ≠ k → ws[j]? = some w' → vsS.toList[j]? = some u' →
        Disj (Spine P H w u v) (Foot P H w' u')) →
      WO H (.ptr a) (.app (.vc d c .nil) vsS) (.app (.vc d c ls) vs)
  | wrap {vs : Tm} : P.wrapField d c = some k → P.ctor d c = some sig → (sig.skip (P.lifted d)).uAt k = true →
      vs.toList[k]? = some v → WO H w u v → WO H w u (.app (.vc d c ls) vs)
  | clo {eM eS eF : Tm} : (∀ G F, P.groups[gid]? = some G → G.fns[j]? = some F → F.dele = none) →
      (∀ i, P.rdU gid j i = true → WO H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i)) →
      (∀ i, P.rdU gid j i = true → ∀ i', i' ≠ i → P.rd gid j i' = true →
        Disj (Spine P H (Tm.env eM.toList i) (Tm.env eS.toList i) (Tm.env eF.toList i))
          (Foot P H (Tm.env eM.toList i') (Tm.env eS.toList i'))) →
      WO H (.clo eM gid j) (.clo eS gid j) (.clo eF gid j)
  | cell : WO H (.ptr a) u .tok
  | dele {eF : Tm} {G : Group} {F : FnDef} : P.groups[gid]? = some G → G.fns[j]? = some F → F.dele = some t → F.u = true →
      WO H w u (Tm.env (eF.toList ++ closures eF.toList gid G) t) → WO H w u (.clo eF gid j)
  | free : (∀ b, ¬ Spine P H w u v b) → WO H w u v

def Heap.WF (H : Heap) : Prop := ∀ a, H.next ≤ a → H.blk a = none

def Heap.Ext (H H' : Heap) : Prop :=
  H.next ≤ H'.next ∧ (∀ a b, H.blk a = some b → H'.blk a = some b) ∧ ∀ a, a < H.next → H'.blk a = H.blk a

def Agree (H H' : Heap) (S : Nat → Prop) : Prop := ∀ a, S a → H'.blk a = H.blk a

variable {P}

theorem Heap.Ext.refl (H : Heap) : H.Ext H := ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ => rfl⟩

theorem Heap.Ext.trans {H1 H2 H3 : Heap} (a : H1.Ext H2) (b : H2.Ext H3) : H1.Ext H3 :=
  ⟨Nat.le_trans a.1 b.1, fun x y h => b.2.1 x y (a.2.1 x y h),
   fun x hx => by rw [b.2.2 x (Nat.lt_of_lt_of_le hx a.1), a.2.2 x hx]⟩

theorem Heap.alloc_ext {H : Heap} (hW : H.WF) (b : Blk) : H.Ext (H.alloc b).1 ∧ (H.alloc b).1.WF := by
  refine ⟨⟨by simp [Heap.alloc], fun a b' h => ?_, fun a ha => ?_⟩, fun a ha => ?_⟩
  · simp only [Heap.alloc]
    have : a ≠ H.next := fun e => by rw [e, hW _ (Nat.le_refl _)] at h; cases h
    simp [this, h]
  · simp only [Heap.alloc]; rw [if_neg (by omega)]
  · simp only [Heap.alloc] at ha ⊢
    rw [ite_eq_right_iff.mpr (by omega)]; exact hW a (by omega)

theorem Heap.alloc_new (H : Heap) (b : Blk) : (H.alloc b).1.blk (H.alloc b).2 = some b := by simp [Heap.alloc]

mutual
theorem MDec.mono {H H' : Heap} (he : H.Ext H') : ∀ {w v : Tm}, MDec P H w v → MDec P H' w v
  | _, _, .ptr hb hs => .ptr (he.2.1 _ _ hb) (MDecs.mono he hs)
  | _, _, .clo hl hs => .clo hl fun i hi => (hs i hi).mono he
  | _, _, .tok h => .tok (by
      rcases h with h | ⟨a, rfl, hb⟩
      · exact .inl h
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hb
        exact .inr ⟨a, rfl, by rw [he.2.1 _ _ hb]; rfl⟩)
  | _, _, .nat => .nat
  | _, _, .wld => .wld
  | _, _, .vc => .vc
  | _, _, .imm => .imm
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
  | _, _, .tok h, hA => .tok (by
      rcases h with h | ⟨a, rfl, hb⟩
      · exact .inl h
      · exact .inr ⟨a, rfl, by rw [hA a .here]; exact hb⟩)
  | _, _, .nat, _ => .nat
  | _, _, .wld, _ => .wld
  | _, _, .vc, _ => .vc
  | _, _, .imm, _ => .imm
  | _, _, .nil, _ => .nil

theorem MDecs.frame {H H' : Heap} : ∀ {ws vs : List Tm}, MDecs P H ws vs →
    (∀ (k : Nat) w v, ws[k]? = some w → vs[k]? = some v → Agree H H' (Foot P H w v)) → MDecs P H' ws vs
  | _, _, .nil, _ => .nil
  | _, _, .cons h hs, hA => .cons (h.frame (hA 0 _ _ (by simp) (by simp)))
      (MDecs.frame hs fun k w v hw hv => hA (k + 1) w v (by simpa using hw) (by simpa using hv))
end


variable (P)

def Twin (v1 v2 : Tm) : Prop :=
  ∀ H w u, (∀ b, Spine P H w u v1 b ↔ Spine P H w u v2 b) ∧ (WO P H w u v1 ↔ WO P H w u v2)

def NoSpine (v : Tm) : Prop := ∀ H w u b, ¬ Spine P H w u v b

variable {P}

theorem Twin.refl (v : Tm) : Twin P v v := fun _ _ _ => ⟨fun _ => Iff.rfl, Iff.rfl⟩

theorem Twin.symm {v1 v2 : Tm} (h : Twin P v1 v2) : Twin P v2 v1 :=
  fun H w u => ⟨fun b => ((h H w u).1 b).symm, (h H w u).2.symm⟩

theorem Twin.trans {v1 v2 v3 : Tm} (h : Twin P v1 v2) (h' : Twin P v2 v3) : Twin P v1 v3 :=
  fun H w u => ⟨fun b => ((h H w u).1 b).trans ((h' H w u).1 b), (h H w u).2.trans (h' H w u).2⟩

theorem Twin.none {v1 v2 : Tm} (h1 : NoSpine P v1) (h2 : NoSpine P v2) : Twin P v1 v2 :=
  fun H w u => ⟨fun b => ⟨fun h => (h1 H w u b h).elim, fun h => (h2 H w u b h).elim⟩,
    ⟨fun _ => .free (h2 H w u), fun _ => .free (h1 H w u)⟩⟩

theorem NoSpine.wrap {d c k : Nat} {sig ls vs : Tm} (hw : P.wrapField d c = some k) (hs : P.ctor d c = some sig)
    (hu : (sig.skip (P.lifted d)).uAt k = false ∨ vs.toList[k]? = none) : NoSpine P (.app (.vc d c ls) vs) := by
  intro H w u b h
  cases h with
  | top h => rw [hw] at h; cases h
  | field _ h => rw [hw] at h; cases h
  | wrap h hs' hu' hv =>
    rw [hw] at h; cases h; rw [hs] at hs'; cases hs'
    rcases hu with hu | hu
    · rw [hu] at hu'; cases hu'
    · rw [hu] at hv; cases hv

theorem Twin.wrap {d c k : Nat} {sig ls vs v : Tm} (hw : P.wrapField d c = some k) (hs : P.ctor d c = some sig)
    (hu : (sig.skip (P.lifted d)).uAt k = true) (hv : vs.toList[k]? = some v) : Twin P v (.app (.vc d c ls) vs) := by
  intro H w u
  have hsp : ∀ b, Spine P H w u (.app (.vc d c ls) vs) b ↔ Spine P H w u v b := fun b =>
    ⟨fun h => by
      cases h with
      | top h => rw [hw] at h; cases h
      | field _ h => rw [hw] at h; cases h
      | wrap h _ _ hv' h' => rw [hw] at h; cases h; rw [hv] at hv'; cases hv'; exact h',
     fun h => .wrap hw hs hu hv h⟩
  refine ⟨fun b => (hsp b).symm, ⟨fun h => .wrap hw hs hu hv h, fun h => ?_⟩⟩
  cases h with
  | ptr _ h => rw [hw] at h; cases h
  | wrap h _ _ hv' h' => rw [hw] at h; cases h; rw [hv] at hv'; cases hv'; exact h'
  | free h => exact .free fun b h' => h b ((hsp b).mpr h')

theorem List.getElem?_of_length {α β : Type} {l1 : List α} {l2 : List β} {k : Nat} {v : α}
    (hl : l1.length = l2.length) (h : l1[k]? = some v) : ∃ v', l2[k]? = some v' :=
  ⟨_, List.getElem?_eq_getElem (hl ▸ (List.getElem?_eq_some_iff.mp h).1)⟩

theorem Spine.ctor_mp {d c : Nat} {sig ls1 ls2 vs1 vs2 : Tm} (hs : P.ctor d c = some sig)
    (hl : vs1.toList.length = vs2.toList.length)
    (h : ∀ k v1 v2, (sig.skip (P.lifted d)).uAt k = true → vs1.toList[k]? = some v1 → vs2.toList[k]? = some v2 →
      Twin P v1 v2) {H : Heap} {w u : Tm} {b : Nat} (hsp : Spine P H w u (.app (.vc d c ls1) vs1) b) :
    Spine P H w u (.app (.vc d c ls2) vs2) b := by
  cases hsp with
  | top hw => exact .top hw
  | field ha hw hs' hu hwk hu' hv h' =>
    rw [hs] at hs'; cases hs'
    obtain ⟨v2, hv2⟩ := List.getElem?_of_length hl hv
    exact .field ha hw hs hu hwk hu' hv2 (((h _ _ _ hu hv hv2) _ _ _).1 _ |>.mp h')
  | wrap hw hs' hu hv h' =>
    rw [hs] at hs'; cases hs'
    obtain ⟨v2, hv2⟩ := List.getElem?_of_length hl hv
    exact .wrap hw hs hu hv2 (((h _ _ _ hu hv hv2) _ _ _).1 _ |>.mp h')

theorem WO.ctor_mp {d c : Nat} {sig ls1 ls2 vs1 vs2 : Tm} (hs : P.ctor d c = some sig)
    (hl : vs1.toList.length = vs2.toList.length)
    (h : ∀ k v1 v2, (sig.skip (P.lifted d)).uAt k = true → vs1.toList[k]? = some v1 → vs2.toList[k]? = some v2 →
      Twin P v1 v2) {H : Heap} {w u : Tm}
    (hsp : ∀ b, Spine P H w u (.app (.vc d c ls2) vs2) b → Spine P H w u (.app (.vc d c ls1) vs1) b)
    (hwo : WO P H w u (.app (.vc d c ls1) vs1)) : WO P H w u (.app (.vc d c ls2) vs2) := by
  have get := fun {k v2} (hv : vs2.toList[k]? = some v2) => List.getElem?_of_length hl.symm hv
  cases hwo with
  | ptr ha hw hs' hf hw1 hd =>
    rw [hs] at hs'; cases hs'
    refine .ptr ha hw hs hf (fun k w u v hu hwk hu' hv => ?_) (fun k w u v hu hwk hu' hv j w' u' hj hw' hu2 b h1 h2 => ?_)
    · obtain ⟨v1, hv1⟩ := get hv
      exact ((h _ _ _ hu hv1 hv) _ _ _).2.mp (hw1 k w u v1 hu hwk hu' hv1)
    · obtain ⟨v1, hv1⟩ := get hv
      exact hd k w u v1 hu hwk hu' hv1 j w' u' hj hw' hu2 b ((((h _ _ _ hu hv1 hv) _ _ _).1 b).mpr h1) h2
  | wrap hw hs' hu hv h' =>
    rw [hs] at hs'; cases hs'
    obtain ⟨v2, hv2⟩ := List.getElem?_of_length hl hv
    exact .wrap hw hs hu hv2 (((h _ _ _ hu hv hv2) _ _ _).2.mp h')
  | free hn => exact .free fun b h' => hn b (hsp b h')

theorem Twin.ctor {d c : Nat} {sig ls1 ls2 vs1 vs2 : Tm} (hs : P.ctor d c = some sig)
    (hl : vs1.toList.length = vs2.toList.length)
    (h : ∀ k v1 v2, (sig.skip (P.lifted d)).uAt k = true → vs1.toList[k]? = some v1 → vs2.toList[k]? = some v2 →
      Twin P v1 v2) : Twin P (.app (.vc d c ls1) vs1) (.app (.vc d c ls2) vs2) := by
  have h' : ∀ k v1 v2, (sig.skip (P.lifted d)).uAt k = true → vs2.toList[k]? = some v1 → vs1.toList[k]? = some v2 →
      Twin P v1 v2 := fun k v1 v2 hu h1 h2 => (h k v2 v1 hu h2 h1).symm
  intro H w u
  exact ⟨fun b => ⟨Spine.ctor_mp hs hl h, Spine.ctor_mp hs hl.symm h'⟩,
    ⟨WO.ctor_mp hs hl h fun _ => Spine.ctor_mp hs hl.symm h', WO.ctor_mp hs hl.symm h' fun _ => Spine.ctor_mp hs hl h⟩⟩

end Minimal
