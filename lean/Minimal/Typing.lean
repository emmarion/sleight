import Minimal.Unify
import Minimal.Native

namespace Minimal

def arrSet (a : Array Bool) (k : Nat) (v : Bool) : Array Bool :=
  if k = a.size then a.push v else Array.ofFn (n := max a.size (k + 1)) fun j => if j.1 = k then v else a.getD j.1 true

theorem arrSet_getD (a : Array Bool) (k : Nat) (v : Bool) (i : Nat) :
    (arrSet a k v).getD i true = if i = k then v else a.getD i true := by
  unfold arrSet
  split
  · rename_i h; subst h
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    split <;> rename_i h1
    · subst h1; simp
    · rcases Nat.lt_or_ge i a.size with h2 | h2
      · simp [h1]
      · simp [Array.getElem?_eq_none (show a.size ≤ i by omega), h1]
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    split <;> rename_i h1
    · simp
    · have : a.size ≤ i := by omega
      simp [Array.getElem?_eq_none this, show i ≠ k by omega]

def arrFrom (a : Array Bool) (k : Nat) (ms : List Bool) : Array Bool :=
  Array.ofFn (n := k) (fun j => a.getD j.1 true) ++ ms.toArray

theorem arrFrom_getD (a : Array Bool) (k : Nat) (ms : List Bool) (i : Nat) :
    (arrFrom a k ms).getD i true = if k ≤ i then ms.getD (i - k) true else a.getD i true := by
  unfold arrFrom
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_ofFn, List.getD_eq_getElem?_getD]
  split <;> rename_i h1
  · simp [show ¬ k ≤ i by omega, h1, Array.getD_eq_getD_getElem?]
  · simp [show k ≤ i by omega]

def arrOr (a : Array Bool) (n : Nat) (c : Nat → Bool) : Array Bool :=
  Array.ofFn (n := max a.size n) fun j => (c j.1 && decide (j.1 < n)) || a.getD j.1 true

theorem arrOr_getD (a : Array Bool) (n : Nat) (c : Nat → Bool) (i : Nat) :
    (arrOr a n c).getD i true = ((c i && decide (i < n)) || a.getD i true) := by
  unfold arrOr
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> rename_i h
  · simp
  · have : a.size ≤ i := by omega
    simp [Array.getElem?_eq_none this]

structure Ctx where
  tys : Array Tm
  σ : Nat → Option Tm := fun _ => none
  ς : Nat → Option Tm := fun _ => none
  mints : List Nat := []
  cur : Option Nat := none
  subs : List Nat := []
  erA : Array Bool := #[]
  ghost : Bool := false
  opened : List (Nat × Bool) := []
  fixed : List (Option Tm) := []
  cmode : Bool := false
  deles : List (Nat × Nat × Bool × Bool) := []
  pd : Option Tm := none

namespace Ctx

def n (Γ : Ctx) : Nat := Γ.tys.size

def er (Γ : Ctx) (i : Nat) : Bool := Γ.erA.getD i true

def canon (Γ : Ctx) (t : Tm) : Tm := canonBy Γ.σ Γ.ς t

instance (priority := high) decCanonEq (Γ : Ctx) (a b : Tm) : Decidable (Γ.canon a = Γ.canon b) :=
  if h : a = b then isTrue (h ▸ rfl) else inferInstanceAs (Decidable (canonBy Γ.σ Γ.ς a = canonBy Γ.σ Γ.ς b))

def sig (Γ : Ctx) (i : Nat) : Option Tm := match (Γ.tys[i]?).map Γ.canon with
  | some (.tyCtor ps) => some (.tyCtor ps)
  | some (.valCtor s) => some (.valCtor s)
  | _ => none

def push (Γ : Ctx) (T : Tm) (e : Bool := false) : Ctx :=
  let k := Γ.n
  { Γ with tys := Γ.tys.push T, erA := arrSet Γ.erA k e }

def withRule (Γ : Ctx) (e : Nat) (t : Tm) : Ctx := { Γ with σ := fun i => if i = e then some t else Γ.σ i }

def _root_.Minimal.Tm.varSlot : Tm → Option Tm
  | .fv i | .sfv i => some (.sfv i)
  | t => if t = Tm.vacant then some Tm.vacant else none

def _root_.Minimal.Prim.src : Prim → Option Tm
  | .tm t | .coerce t _ _ | .place t _ | .unplace t _ => t.varSlot
  | _ => none

def _root_.Minimal.Prim.srcAt (P : Prog) (pd : Option Tm) : Prim → Option Tm
  | .tm (.app h as) => (P.unwrap (.app h as)).varSlot <|> pd
  | .axm _ => pd
  | p => p.src

def markPd (Γ : Ctx) : Mark → Tm → Ctx
  | .reuse true, .fv i | .write true, .fv i => { Γ with pd := some (.sfv i) }
  | .cellOf, a => { Γ with pd := a.varSlot }
  | _, _ => Γ

theorem markPd_nf (Γ : Ctx) {m : Mark} {a : Tm} (hm : m ≠ .cellOf) (ha : ∀ i, a ≠ .fv i) : Γ.markPd m a = Γ := by
  unfold markPd; split <;> simp_all

def slotSub (r : Nat) (s : Tm) : Tm → Tm := canonBy (fun _ => none) (fun j => if j = r then some s else none)

def bindSlot (Γ : Ctx) (r : Nat) (s : Tm) : Ctx :=
  { Γ with σ := fun i => (Γ.σ i).map (slotSub r s), ς := fun i => if i = r then some s else (Γ.ς i).map (slotSub r s) }

def slotBind (Γ : Ctx) (e : Nat) (s : Tm) : Option (Nat × Tm) :=
  if s.isSlotVal Γ.n ∧ e < Γ.n then match Γ.canon (.sfv e), s with
    | .sfv r, s => if s = .sfv r then none else some (r, s)
    | a, .sfv r => if a.isSlotVal Γ.n then some (r, a) else none
    | _, _ => none
  else none

@[simp] theorem markPd_tys (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).tys = Γ.tys := by unfold markPd; split <;> rfl
@[simp] theorem markPd_σ (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).σ = Γ.σ := by unfold markPd; split <;> rfl
@[simp] theorem markPd_ς (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).ς = Γ.ς := by unfold markPd; split <;> rfl
@[simp] theorem markPd_erA (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).erA = Γ.erA := by unfold markPd; split <;> rfl
@[simp] theorem markPd_mints (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).mints = Γ.mints := by unfold markPd; split <;> rfl
@[simp] theorem markPd_cur (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).cur = Γ.cur := by unfold markPd; split <;> rfl
@[simp] theorem markPd_subs (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).subs = Γ.subs := by unfold markPd; split <;> rfl
@[simp] theorem markPd_ghost (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).ghost = Γ.ghost := by unfold markPd; split <;> rfl
@[simp] theorem markPd_opened (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).opened = Γ.opened := by unfold markPd; split <;> rfl
@[simp] theorem markPd_fixed (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).fixed = Γ.fixed := by unfold markPd; split <;> rfl
@[simp] theorem markPd_cmode (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).cmode = Γ.cmode := by unfold markPd; split <;> rfl
@[simp] theorem markPd_deles (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).deles = Γ.deles := by unfold markPd; split <;> rfl
@[simp] theorem markPd_n (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).n = Γ.n := by simp [n]
@[simp] theorem markPd_er (Γ : Ctx) (m : Mark) (a : Tm) : (Γ.markPd m a).er = Γ.er := by funext i; simp [er]

def withSlot (Γ : Ctx) (e : Nat) (s : Tm) : Ctx := match Γ.slotBind e s with
  | some (r, s) => Γ.bindSlot r s
  | none => Γ

def slotIf (Γ : Ctx) (b : Bool) (e : Nat) (s : Tm) : Ctx := if b then Γ.withSlot e s else Γ

section
variable (Γ : Ctx) (e : Nat) (s : Tm)
@[simp] theorem withSlot_tys : (Γ.withSlot e s).tys = Γ.tys := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_erA : (Γ.withSlot e s).erA = Γ.erA := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_mints : (Γ.withSlot e s).mints = Γ.mints := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_cur : (Γ.withSlot e s).cur = Γ.cur := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_subs : (Γ.withSlot e s).subs = Γ.subs := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_ghost : (Γ.withSlot e s).ghost = Γ.ghost := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_opened : (Γ.withSlot e s).opened = Γ.opened := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_fixed : (Γ.withSlot e s).fixed = Γ.fixed := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_cmode : (Γ.withSlot e s).cmode = Γ.cmode := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_deles : (Γ.withSlot e s).deles = Γ.deles := by unfold withSlot; split <;> rfl
@[simp] theorem withSlot_n : (Γ.withSlot e s).n = Γ.n := by simp [n]
@[simp] theorem withSlot_er : (Γ.withSlot e s).er = Γ.er := by funext i; simp [er]
theorem withSlot_upd_ghost (g : Bool) : ({ Γ with ghost := g } : Ctx).withSlot e s = { Γ.withSlot e s with ghost := g } := by
  unfold withSlot; rw [show ({ Γ with ghost := g } : Ctx).slotBind e s = Γ.slotBind e s from rfl]; split <;> rfl
end

section
variable (Γ : Ctx) (b : Bool) (e : Nat) (s : Tm)
@[simp] theorem slotIf_tys : (Γ.slotIf b e s).tys = Γ.tys := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_erA : (Γ.slotIf b e s).erA = Γ.erA := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_mints : (Γ.slotIf b e s).mints = Γ.mints := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_cur : (Γ.slotIf b e s).cur = Γ.cur := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_subs : (Γ.slotIf b e s).subs = Γ.subs := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_ghost : (Γ.slotIf b e s).ghost = Γ.ghost := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_opened : (Γ.slotIf b e s).opened = Γ.opened := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_fixed : (Γ.slotIf b e s).fixed = Γ.fixed := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_cmode : (Γ.slotIf b e s).cmode = Γ.cmode := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_deles : (Γ.slotIf b e s).deles = Γ.deles := by cases b <;> simp [slotIf]
@[simp] theorem slotIf_n : (Γ.slotIf b e s).n = Γ.n := by simp [n]
@[simp] theorem slotIf_er : (Γ.slotIf b e s).er = Γ.er := by funext i; simp [er]
theorem slotIf_upd_ghost (g : Bool) : ({ Γ with ghost := g } : Ctx).slotIf b e s = { Γ.slotIf b e s with ghost := g } := by
  cases b <;> simp [slotIf, withSlot_upd_ghost]
end

def slotSelf (Γ : Ctx) (s : Nat) : Option Ctx :=
  let c := Γ.canon (.fv s)
  if c.isSlotVal Γ.n then some (Γ.withSlot s c)
  else if c = .fv s then some (Γ.withRule s (Γ.canon (.sfv s)))
  else none

def chkStep (Γ : Ctx) : Chk → Tm → Ctx
  | .mark m, a => Γ.markPd m a
  | .slf, .fv s => (Γ.slotSelf s).getD Γ
  | .slotAt, a => { Γ with pd := a.varSlot }
  | _, _ => Γ

def pushWdo (Γ : Ctx) (Tw A w : Tm) : Ctx :=
  ((Γ.push Tw false).slotIf w.varSlot.isSome Γ.n (Γ.canon (w.varSlot.getD .nil))).push A false

@[simp] theorem pushWdo_n (Γ : Ctx) (Tw A w : Tm) : (Γ.pushWdo Tw A w).n = Γ.n + 2 := by
  simp [pushWdo, push, n]

def pushPrim0 (Γ : Ctx) (T : Tm) (er : Bool) : Prim → Ctx
  | .tm t | .coerce _ t _ | .unplace _ t => (Γ.push T er).withRule Γ.n (Γ.canon t)
  | _ => Γ.push T er

def pushPrim (P : Prog) (Γ : Ctx) (T : Tm) (er : Bool) (p : Prim) : Ctx :=
  ({ Γ.pushPrim0 T er p with pd := none } : Ctx).slotIf (p.srcAt P Γ.pd).isSome Γ.n (Γ.canon ((p.srcAt P Γ.pd).getD .nil))

def pushEnt (Γ : Ctx) : Ent → Tm → Ctx
  | .ty _ e _, A => Γ.push A e
  | .is _ e _ sl, x => ((Γ.push .nil e).withRule Γ.n (Γ.canon x)).slotIf sl (Γ.n - 1) (Γ.canon x)

def openTele : Ctx → Tm → Nat → Ctx × Tm
  | Γ, .bind k A r, m + 1 => (Γ.pushEnt k A).openTele (r.inst (.fv Γ.n) 0) m
  | Γ, t, _ => (Γ, t)

def setErs (Γ Γ' : Ctx) : Option (List Bool) → Ctx
  | none => Γ'
  | some ms => { Γ' with erA := arrFrom Γ'.erA Γ.n ms }

def pushTele (Γ : Ctx) (R : Tm) (ov : Option (List Bool) := none) : Ctx := Γ.setErs (Γ.openTele R R.len).1 ov

def pushMint (Γ : Ctx) : Ctx := { Γ.push .level true with mints := Γ.mints ++ [Γ.n] }

def fnSide (Γ : Ctx) (i : Nat) : Option Bool := match (Γ.tys[i]?).map Γ.canon with
  | some (.fn _ _ _ u _) => some u
  | _ => none

def fnU (Γ : Ctx) (i : Nat) : Bool := (Γ.fnSide i).getD false

def deleSide (Γ : Ctx) (G : Group) (t : Nat) : Bool := fnU { Γ with tys := Γ.tys ++ (G.fns.map (FnDef.type G)).toArray } t

theorem withSlot_eq (Γ : Ctx) (e : Nat) (s : Tm) : ∃ σ ς, Γ.withSlot e s = { Γ with σ := σ, ς := ς } := by
  unfold withSlot; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨Γ.σ, Γ.ς, rfl⟩

def deleSlots (k : Nat) (fns : List FnDef) (Γ : Ctx) : Ctx :=
  fns.zipIdx.foldl (fun Γ' (F, j) => match F.dele with
    | some t => Γ'.withSlot (k + j) (Γ'.canon (.sfv t))
    | none => Γ') Γ

theorem deleSlots_eq (k : Nat) (fns : List FnDef) (Γ : Ctx) : ∃ σ ς, deleSlots k fns Γ = { Γ with σ := σ, ς := ς } := by
  unfold deleSlots
  generalize fns.zipIdx = L
  induction L generalizing Γ with
  | nil => exact ⟨Γ.σ, Γ.ς, rfl⟩
  | cons p L ih =>
    simp only [List.foldl_cons]
    obtain ⟨σ1, ς1, h1⟩ : ∃ σ ς, (match p.1.dele with
        | some t => Γ.withSlot (k + p.2) (Γ.canon (.sfv t))
        | none => Γ) = { Γ with σ := σ, ς := ς } := by
      split
      · exact withSlot_eq _ _ _
      · exact ⟨Γ.σ, Γ.ς, rfl⟩
    obtain ⟨σ2, ς2, h2⟩ := ih (match p.1.dele with
        | some t => Γ.withSlot (k + p.2) (Γ.canon (.sfv t))
        | none => Γ)
    exact ⟨σ2, ς2, by rw [h2, h1]⟩

@[simp] theorem deleSlots_tys (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).tys = Γ.tys := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_erA (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).erA = Γ.erA := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_mints (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).mints = Γ.mints := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_cur (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).cur = Γ.cur := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_subs (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).subs = Γ.subs := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_ghost (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).ghost = Γ.ghost := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_opened (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).opened = Γ.opened := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_fixed (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).fixed = Γ.fixed := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_cmode (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).cmode = Γ.cmode := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_deles (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).deles = Γ.deles := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_pd (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).pd = Γ.pd := by
  obtain ⟨σ, ς, h⟩ := deleSlots_eq k fns Γ; rw [h]
@[simp] theorem deleSlots_n (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).n = Γ.n := by simp [n]
@[simp] theorem deleSlots_er (k : Nat) (fns : List FnDef) (Γ : Ctx) : (deleSlots k fns Γ).er = Γ.er := by funext i; simp [er]

def pushFns (Γ : Ctx) (G : Group) : Ctx :=
  let k := Γ.n
  let Γ1 : Ctx :=
    { Γ with tys := Γ.tys ++ (G.fns.map (FnDef.type G)).toArray,
             erA := arrFrom Γ.erA k (G.fns.map (·.er)),
             deles := Γ.deles ++ G.fns.zipIdx.filterMap fun (F, j) =>
               if F.er || G.ghost then none else F.dele.map fun t => (k + j, t, F.u, Γ.deleSide G t) }
  deleSlots k G.fns Γ1

@[simp] theorem pushFns_mints (Γ : Ctx) (G : Group) : (Γ.pushFns G).mints = Γ.mints := by simp [pushFns]
@[simp] theorem pushFns_cur (Γ : Ctx) (G : Group) : (Γ.pushFns G).cur = Γ.cur := by simp [pushFns]
@[simp] theorem pushFns_subs (Γ : Ctx) (G : Group) : (Γ.pushFns G).subs = Γ.subs := by simp [pushFns]
@[simp] theorem pushFns_ghost (Γ : Ctx) (G : Group) : (Γ.pushFns G).ghost = Γ.ghost := by simp [pushFns]
@[simp] theorem pushFns_opened (Γ : Ctx) (G : Group) : (Γ.pushFns G).opened = Γ.opened := by simp [pushFns]
@[simp] theorem pushFns_fixed (Γ : Ctx) (G : Group) : (Γ.pushFns G).fixed = Γ.fixed := by simp [pushFns]
@[simp] theorem pushFns_cmode (Γ : Ctx) (G : Group) : (Γ.pushFns G).cmode = Γ.cmode := by simp [pushFns]
@[simp] theorem pushFns_pd (Γ : Ctx) (G : Group) : (Γ.pushFns G).pd = Γ.pd := by simp [pushFns]

def fields (Γ : Ctx) (m : Nat) : Tm := .ofList ((List.range m).map fun j => .fv (Γ.n + j))

def body (Γ : Ctx) (G : Group) (F : FnDef) : Ctx × Tm :=
  let Γ1 := Γ.pushFns G
  let (Γ2, rem) := Γ1.openTele F.tele F.np
  ({ Γ2 with cur := some G.lvl, ghost := Γ.ghost || F.er,
             subs := (markedArgs F.tele (Γ1.fields F.np)).filterMap Tm.fvIdx,
             erA := arrOr Γ2.erA Γ1.n fun i => F.dele.isSome && F.dele != some i },
   rem)

def ready (Γ : Ctx) : Bool :=
  Γ.fixed.length == Γ.n && Γ.cur.isNone && !Γ.ghost && Γ.fixed.zipIdx.all fun (o, i) => o.isSome || Γ.er i

def strip (Γ : Ctx) : List Tm := Γ.fixed.map (·.getD .tok)

def record (Γ Γ' : Ctx) (vs : List Tm) : Ctx :=
  { Γ' with fixed := Γ.fixed ++ vs.zipIdx.map fun (v, k) => if Γ'.er (Γ.n + k) then none else some v }

@[simp] theorem er_withRule (Γ : Ctx) (e : Nat) (t : Tm) : (Γ.withRule e t).er = Γ.er := rfl
@[simp] theorem er_upd_cmode (Γ : Ctx) (b : Bool) : ({ Γ with cmode := b } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_ghost (Γ : Ctx) (b : Bool) : ({ Γ with ghost := b } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_σ (Γ : Ctx) (s : Nat → Option Tm) : ({ Γ with σ := s } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_fixed (Γ : Ctx) (f : List (Option Tm)) : ({ Γ with fixed := f } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_cur (Γ : Ctx) (c : Option Nat) : ({ Γ with cur := c } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_opened (Γ : Ctx) (o : List (Nat × Bool)) : ({ Γ with opened := o } : Ctx).er = Γ.er := rfl
@[simp] theorem er_upd_mints (Γ : Ctx) (m : List Nat) : ({ Γ with mints := m } : Ctx).er = Γ.er := rfl

@[simp] theorem er_push (Γ : Ctx) (T : Tm) (e : Bool) (i : Nat) :
    (Γ.push T e).er i = if i = Γ.n then e else Γ.er i := by
  simp only [push, er, arrSet_getD]

@[simp] theorem pushWdo_ghost (Γ : Ctx) (Tw A w : Tm) : (Γ.pushWdo Tw A w).ghost = Γ.ghost := by simp [pushWdo, push]

theorem er_pushWdo (Γ : Ctx) (Tw A w : Tm) (i : Nat) :
    (Γ.pushWdo Tw A w).er i = if i = Γ.n + 1 then false else if i = Γ.n then false else Γ.er i := by
  unfold pushWdo; rw [er_push, slotIf_er, er_push]; simp only [push, n]
  by_cases h1 : i = Γ.tys.size + 1 <;> simp [h1]

@[simp] theorem er_pushMint (Γ : Ctx) (i : Nat) : Γ.pushMint.er i = if i = Γ.n then true else Γ.er i := by
  simp only [pushMint, er, push, arrSet_getD]

@[simp] theorem er_setErs (Γ Γ' : Ctx) (ms : List Bool) (i : Nat) :
    (Γ.setErs Γ' (some ms)).er i = if Γ.n ≤ i then ms.getD (i - Γ.n) true else Γ'.er i := by
  simp only [setErs, er, arrFrom_getD]

@[simp] theorem er_pushFns (Γ : Ctx) (G : Group) (i : Nat) :
    (Γ.pushFns G).er i = if Γ.n ≤ i then (G.fns[i - Γ.n]?.map (·.er)).getD true else Γ.er i := by
  simp only [pushFns, er, deleSlots_erA, arrFrom_getD, List.getD_eq_getElem?_getD, List.getElem?_map]

@[simp] theorem er_body (Γ : Ctx) (G : Group) (F : FnDef) (i : Nat) :
    (Γ.body G F).1.er i = ((F.dele.isSome && decide (i < (Γ.pushFns G).n) && F.dele != some i) ||
      ((Γ.pushFns G).openTele F.tele F.np).1.er i) := by
  simp only [body, er, arrOr_getD]
  cases F.dele.isSome <;> cases decide (i < (Γ.pushFns G).n) <;> simp

end Ctx

opaque fixFuel : Nat := 1000000000

def stepS (P : Prog) (ρ : List Tm) : Core → Option (List Tm)
  | .call _ _ _ true ms _ _ => some (List.replicate ms.length .tok)
  | .call f _ args false _ ve _ => match P.sub ρ f with
    | .clo env gid j => do
      let G ← P.groups[gid]?
      let F ← G.fns[j]?
      let outs ← runA P fixFuel (env.toList ++ closuresS env.toList gid G ++ F.spreadIn ve (args.toList.map (P.sub ρ))).toArray F.body
      some (F.spreadOut ve args.toList.length outs)
    | _ => none
  | .mtch _ R _ _ true _ => some (List.replicate R.len .tok)
  | .mtch s _ brs els false _ => match P.view (P.sub ρ s) with
    | .app (.vc _ c _) vs => do
      let (pre, body) ← selectBr brs els c vs.toList
      runA P fixFuel (ρ ++ pre).toArray body
    | _ => none
  | .seq _ body _ => runA P fixFuel ρ.toArray body
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
      | .fv x, some (d, c) => if P.isNt d then (match Γ.fixed[x]?.join with
          | some w => Γ.record Γ' (List.replicate n w)
          | none => Γ') else match (Γ.fixed[x]?.join).map P.view with
        | some (.app (.vc d' c' _) vs) => if d' = d ∧ c' = c then Γ.record Γ' vs.toList else Γ'
        | _ => Γ'
      | _, _ => Γ'
  else Γ'

def Ctx.fixedEnv (P : Prog) (Γ : Ctx) (i : Nat) : Tm := P.unnat ((Γ.fixed[i]?.join).getD .nil)

def fieldsSimple (S : List Nat) : Tm → Bool
  | .bind (.ty _ false _) (.app (.tyc d .nil) .nil) r@(.bind ..) => S.contains d && fieldsSimple S r
  | .bind (.ty _ false _) _ .nil => true
  | _ => false

def Prog.simpleStep (P : Prog) (S : List Nat) : List Nat :=
  S.filter fun d => match P.adts[d]? with
    | some D => D.params == .nil && !D.newtype && !D.coercible && !D.opq && P.placedD != some d && D.phantom.all (!·) &&
      D.ctors.all (fieldsSimple S)
    | none => false

def Prog.simple (P : Prog) : List Nat :=
  iterFix P.simpleStep (P.adts.size + 1) (List.range P.adts.size)

def Prog.natOK (P : Prog) (d : Nat) : Bool := match P.adts[d]? with
  | some D => P.natD == some d && D.lifted == 0 && !D.newtype && !(D.phantom.getD 0 false) && !(D.phantom.getD 1 false) &&
    match D.ctors with
    | [.bind (.ty ..) z .nil, .bind (.ty _ false _) a (.bind (.ty ..) s .nil)] => z == natTy d && a == natTy d && s == natTy d
    | _ => false
  | none => false

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
  | .tyc d ls => if P.lifted d = ls.len then
      (P.adts[d]?).map fun D => (.tyCtor (D.params.peel ls), some (D.mtbl d ls)) else none
  | .vc d c ls => if P.lifted d = ls.len then
      (P.adts[d]?).bind fun D => (D.ctors[c]?).map fun sig => (.valCtor (sig.peel ls), some (D.mtbl d ls)) else none
  | .univ | .level => some (.tyCtor .nil, none)
  | _ => none

def clash : Tm → Tm → Bool
  | .vc d c _, .vc d' c' _ => d == d' && c != c'
  | _, _ => false

def declIso : Nat → List (List Tm) → List (Tm × Tm) → Option (List (Tm × Tm))
  | _, _, [] => some []
  | 0, _, _ => none
  | fuel + 1, cls, (a, b) :: work =>
    let ca := (cls.find? (·.contains a)).getD [a]
    let cb := (cls.find? (·.contains b)).getD [b]
    if a matches .fv _ || b matches .fv _ then ((a, b) :: ·) <$> declIso fuel cls work
    else if ca.contains b then declIso fuel cls work
    else if ca.any fun x => cb.any (clash x) then none
    else match declShape P a, declShape P b with
      | some (s, m), some (s', m') =>
        match pairsOf ((s, s') :: (match m, m' with | some x, some y => [(x, y)] | _, _ => [])) with
        | some ps => declIso fuel ((ca ++ cb) :: cls.filter fun c => !c.contains a && !c.contains b) (ps ++ work)
        | none => none
      | _, _ => none

def Ctx.lists (Γ : Ctx) (σ : Nat → Option Tm) : List (Tm × Tm × List Tm) :=
  Γ.opened.filterMap fun (m, _) => match (Γ.tys[m]?).map (canonBy σ Γ.ς) with
    | some (.mtbl u nt ex ph T cs) => some (.mtbl u nt ex ph T cs, T, cs.toList)
    | _ => none

def Ctx.atoms (Γ : Ctx) : Atoms := fun σ a b =>
  let ls := Γ.lists σ
  if ls.any (fun (_, _, ks) => match ks.idxOf? a, ks.idxOf? b with
      | some i, some j => i != j
      | _, _ => false) then none
  else if a.isHead && b.isHead then if a.sameHead b then some [] else declIso P P.isoFuel [] [(a, b)]
  else
    let names (x : Tm) := ls.filterMap (fun (M, T, ks) => if T == x || ks.contains x then some M else none) ++ declMtbl P x
    let ms := names a ++ names b
    let sigs := match sigOf P Γ a, sigOf P Γ b with
      | some s, some s' => [(canonBy σ Γ.ς s, canonBy σ Γ.ς s')]
      | _, _ => []
    some (sigs ++ ms.map (ms.headD .nil, ·))

def Ctx.openEqs (Γ : Ctx) (xs : List Tm) : List (Tm × Tm) := xs.flatMap fun x => (Γ.atoms P Γ.σ x x).getD []

def Ctx.ntSlot (Γ Γf : Ctx) (s k : Tm) : Ctx :=
  match Γ.known k, s.varSlot with
  | some (d, c), some σ => match P.wrapField d c with
    | some j => Γf.withSlot (Γ.n + j) (Γ.canon σ)
    | none => Γf
  | _, _ => Γf

theorem Ctx.ntSlot_fields (Γ Γf : Ctx) (s k : Tm) :
    (Γ.ntSlot P Γf s k).ghost = Γf.ghost ∧ (Γ.ntSlot P Γf s k).er = Γf.er ∧ (Γ.ntSlot P Γf s k).n = Γf.n := by
  unfold Ctx.ntSlot; split <;> (try split) <;> simp

def Ctx.slotEq (Γ : Ctx) : Tm × Tm → Ctx
  | (.sfv r, b) => Γ.withSlot r (Γ.canon b)
  | (a, .sfv r) => Γ.withSlot r (Γ.canon a)
  | _ => Γ

def Ctx.forceSlots (Γ : Ctx) (eqs : List (Tm × Tm)) : Ctx :=
  (((pairsOf (eqs.map fun e => (Γ.canon e.1, Γ.canon e.2))).getD []).filter fun e => e.1.isSlot || e.2.isSlot).foldl Ctx.slotEq Γ

def Ctx.branch (Γ : Ctx) (s k H idx sig : Tm) : Ctx × UResult :=
  let m := sig.len - 1
  let (Γf, rem) := Γ.openTele sig m
  let Γf := Γ.ntSlot P Γf s k
  match rem with
  | .bind (.ty ..) R .nil =>
    let eqs := [(Γ.canon s, Γf.canon (.app k (Γ.fields m))), (Γ.canon (.app H idx), Γf.canon R)]
    match unify Γf.n (Γf.atoms P) Γf.σ [] eqs with
    | .ok σ => let Γu := ({ Γf with σ := σ } : Ctx).forceSlots eqs; (Γu, .ok Γu.σ)
    | r => (Γf, r)
  | _ => (Γf, .unknown)

mutual
def rt (Γ : Ctx) : Tm → Bool
  | .fv i => !Γ.er i
  | .sfv i => !Γ.er i && P.slotOK
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

def Ctx.atArgs (Γ : Ctx) : Tm → Tm → Option Tm → Bool
  | .bind (.is _ _ _ true) _ r, .cons a as, some (.fv j) => Γ.canon a == Γ.canon (.sfv j) && Γ.atArgs r as (some a)
  | .bind (.is _ _ _ true) _ _, .cons _ _, _ => false
  | .bind _ _ r, .cons a as, _ => Γ.atArgs r as (some a)
  | _, _, _ => true

def Prim.rt (Γ : Ctx) : Prim → Bool
  | .tm t | .lit t | .coerce t _ _ | .place t _ | .unplace t _ => Minimal.rt P Γ t
  | .mtblOf .. | .atom _ | .axm _ | .num .. => true
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
  | sfv : i < Γ.n → P.slotOK = true → TmTy Γ (.sfv i) (.app (.tyc slotD .nil) .nil)

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
  | isCons : TmTy Γ e T → TeleOK (Γ.pushEnt (.is mk er u sl) e) (r.inst (.fv Γ.n) 0) → TeleOK Γ (.bind (.is mk er u sl) e r)
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
  | wAsk : P.worldD = some wd → P.requestD = some rd → TmTy P Γ w W → Γ.canon W = .app (.tyc wd .nil) .nil →
      TmTy P Γ req R → Γ.canon R = .app (.tyc rd ls) (.cons A .nil) → PrimTy Γ (.wAsk w req) A
  | wNext : P.worldD = some wd → TmTy P Γ w W → Γ.canon W = .app (.tyc wd .nil) .nil →
      PrimTy Γ (.wNext w) (.app (.tyc wd .nil) .nil)
  | atom : P.adts[d]? = some D → D.ctors = [.bind (.ty m e u) (.app (.tyc d .nil) .nil) .nil] → D.lifted = 0 →
      D.newtype = false → P.phantom d 0 = false → PrimTy Γ (.atom d) (.app (.tyc d .nil) .nil)
  | num : P.natOK d = true → PrimTy Γ (.num d n) (natTy d)
  | atomEq : P.adts[d]? = some D → D.ctors = [.bind (.ty m e u) (.app (.tyc d .nil) .nil) .nil] → D.lifted = 0 →
      D.opq = false → P.adts[q]? = some E → E.ctors = [eqSig q (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)] → E.lifted = 0 →
      TmTy P Γ a A → Γ.canon A = .app (.tyc d .nil) .nil → TmTy P Γ b B → Γ.canon B = .app (.tyc d .nil) .nil →
      PrimTy Γ (.atomEq d q a b) (.app (.tyc q .nil) (.cons (.app (.tyc d .nil) .nil) (.cons a (.cons b .nil))))
  | axm : TmTy P Γ A U → Γ.canon U = .univ → Γ.canon A = .app (.tyc d ls) idx → P.adts[d]? = some D → D.opq = true →
      P.placedD ≠ some d → P.worldD ≠ some d → PrimTy Γ (.axm A) A
  | place : P.placedD = some q → TmTy P Γ a A → Γ.canon A = Γ.canon B → B.static Γ.n 0 → s.static Γ.n 0 →
      PrimTy Γ (.place a (.app (.tyc q .nil) (.cons s (.cons B (.cons a .nil)))))
        (.app (.tyc q .nil) (.cons s (.cons B (.cons a .nil))))
  | unplace : P.placedD = some q → TmTy P Γ a A → Γ.canon A = .app (.tyc q .nil) (.cons s (.cons B (.cons w .nil))) →
      Γ.canon v = w → PrimTy Γ (.unplace a v) B
  | placedEq : P.placedD = some q → P.adts[e]? = some E → E.ctors = [eqSig e (.ty m1 e1 u1) (.ty m2 e2 u2) (.ty m3 e3 u3)] →
      E.lifted = 0 → TmTy P Γ C U → Γ.canon C = .app (.tyc q .nil) (.cons s (.cons B (.cons w .nil))) →
      TmTy P Γ a A → Γ.canon A = Γ.canon C → TmTy P Γ b B' → Γ.canon B' = Γ.canon C →
      PrimTy Γ (.placedEq e C a b) (.app (.tyc e .nil) (.cons C (.cons a (.cons b .nil))))
  | predatesSubterm : TmTy P Γ p Pt → TmTy P Γ q Qt → Γ.canon Pt = .predates A a l →
      Γ.canon Qt = .subterm B b A a → PrimTy Γ (.predatesSubterm p q) (.predates B b l)
  | assert : TmTy P Γ t T → t.static 0 0 → P.simpleStep P.simple = P.simple →
      (∀ i ∈ A.fvs, ∃ d vS, Γ.tys[i]? = some (.app (.tyc d .nil) .nil) ∧ d ∈ P.simple ∧ Γ.fixed[i]?.join = some vS) →
      A.subst (Γ.fixedEnv P) = T → A.static Γ.n 0 → PrimTy Γ (.assert t A) A
  | coerce : TmTy P Γ p Pt → Γ.canon Pt = Tm.coer dC sa A a' sb B b' → P.adts[dC]? = some D → D.coercible = true →
      Γ.canon a = Γ.canon a' → TmTy P Γ b Tb → Γ.canon b = Γ.canon b' → Γ.canon Tb = Γ.canon B →
      PrimTy Γ (.coerce a b p) B
  | coerRefl : TmTy P Γ s S → TmTy P Γ e E → P.adts[dC]? = some D → D.coercible = true →
      PrimTy Γ (.coerRefl s e) (Tm.coer dC s E e s E e)
  | deleOf : (g, t, sg, st) ∈ Γ.deles → Γ.tys[g]? = some Tg → Γ.tys[t]? = some Tt → P.adts[dD]? = some D →
      D.coercible = true → PrimTy Γ (.deleOf g t) (Tm.coer dD (sideTm sg) Tg (.fv g) (sideTm st) Tt (.fv t))
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
      TmTy P Γ (args.toList.getD k .nil) F → P.adts[dC]? = some D → D.coercible = true → TmTy P Γ C K →
      Γ.canon K = .valCtor sig → sig.isTele → src = (if sig.uAt k then s else sharedTm) →
      PrimTy Γ (.coerWrap s C args) (Tm.coer dC src F (args.toList.getD k .nil) s T0 (.app C args))
  | coerCtor : TmTy P Γ s S → TmTy P Γ C K → Γ.canon K = .valCtor sig → sig.isTele → TmTy P Γ (.app C srcs) Ts →
      TmTy P Γ (.app C tgts) Tt → srcs.len = tgts.len →
      (∀ j < srcs.len, sig.ers.getD j true = false → ∃ p Pt sa A x sb B y, ps.toList[j]? = some p ∧ TmTy P Γ p Pt ∧
        Γ.canon Pt = Tm.coer dC sa A x sb B y ∧ Γ.canon x = Γ.canon (srcs.toList.getD j .nil) ∧
        Γ.canon y = Γ.canon (tgts.toList.getD j .nil) ∧
        (if sig.uAt j then Γ.canon sa = Γ.canon s ∧ Γ.canon sb = Γ.canon s
          else Γ.canon sa = sharedTm ∧ Γ.canon sb = sharedTm)) →
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

def Prim.inert : Prim → Bool
  | .tm (.fv _) | .coerce (.fv _) _ _ | .place (.fv _) _ | .unplace (.fv _) _ => true
  | .tm _ | .coerce .. | .place .. | .unplace .. | .lit _ | .axm _ => false
  | _ => true

def delegWalk (t n0 cnt : Nat) (re : List Bool) : Bool → List (Option (Bool × Nat)) → Core → Bool
  | ph, al, .chk _ _ _ r => delegWalk t n0 cnt re ph al r
  | ph, al, .prim p er r => (er || p.inert) && delegWalk t n0 cnt re ph (al ++ [if er then none else match p with
      | .tm x | .coerce x _ _ | .place x _ | .unplace x _ => resolve n0 al x
      | _ => none]) r
  | ph, al, .call _ _ _ true ms _ r => delegWalk t n0 cnt re ph (al ++ List.replicate ms.length none) r
  | ph, al, .mtch _ R _ _ true r => delegWalk t n0 cnt re ph (al ++ List.replicate R.len none) r
  | ph, al, .defLvl r => delegWalk t n0 cnt re ph (al ++ [none]) r
  | ph, al, .defFns gid r => match P.groups[gid]? with
    | some G => delegWalk t n0 cnt re ph (al ++ List.replicate G.fns.length none) r
    | none => false
  | false, al, .call f _ args false _ (some ve) r =>
    f == .fv t && args.toList.length ≤ ve.length &&
      (filt (ve.take args.toList.length) args.toList).map (resolve n0 al) == (List.range cnt).map (fun r => some (false, r)) &&
      delegWalk t n0 cnt re true (al ++ symSpread true (ve.drop args.toList.length)) r
  | true, al, .ret ts => ts.toList.length == re.length && ts.toList.all (· matches .fv _) &&
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

def Group.sidesOK (G : Group) (Γ : Ctx) : Bool :=
  G.ghost || G.fns.all fun F => F.dele.all fun t =>
    (F.er || !Γ.deleSide G t || F.u) &&
    if t < Γ.n then (Γ.fnSide t).isSome else (G.fns[t - Γ.n]?.map (·.u)) == some false

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
  | prim : PrimTy P Γ p T → (er || Γ.ok (p.rt P Γ)) → CoreTy b (Ctx.adv P Γ (Γ.pushPrim P T er p) (.prim p er rest)) rest rets →
      CoreTy b Γ (.prim p er rest) rets
  | wdo : PrimTy P Γ (.wNext w) Tw → PrimTy P Γ (.wAsk w req) A → Γ.ok (rt P Γ w && rt P Γ req) →
      CoreTy b (Ctx.adv P Γ (Γ.pushWdo Tw A w) (.wdo w req rest)) rest rets → CoreTy b Γ (.wdo w req rest) rets
  | defLvl : CoreTy b (Ctx.adv P Γ Γ.pushMint (.defLvl rest)) rest rets → CoreTy b Γ (.defLvl rest) rets
  | defFns : gid < b → P.groups[gid]? = some G → GroupOK gid Γ G →
      CoreTy b (Ctx.adv P Γ (Γ.pushFns G) (.defFns gid rest)) rest rets → CoreTy b Γ (.defFns gid rest) rets
  | chkIs : TmTy P Γ e E → Γ.canon a = Γ.canon e → CoreTy b Γ rest rets → CoreTy b Γ (.chk .is a e rest) rets
  | chkTy : TmTy P Γ a A → TmTy P Γ T U → Γ.canon U = .univ → Γ.canon A = Γ.canon T → CoreTy b Γ rest rets →
      CoreTy b Γ (.chk .ty a T rest) rets
  | chkRt : Γ.ok (rt P Γ a) → CoreTy b Γ rest rets → CoreTy b Γ (.chk .rt a x rest) rets
  | chkMark : CoreTy b (Γ.markPd m a) rest rets → CoreTy b Γ (.chk (.mark m) a x rest) rets
  | chkCm : CoreTy b { Γ with cmode := true } rest rets → CoreTy b Γ (.chk .cm a x rest) rets
  | chkSlotAt : CoreTy b { Γ with pd := a.varSlot } rest rets → CoreTy b Γ (.chk .slotAt a x rest) rets
  | chkSlf : P.slotOK = true → TmTy P Γ (.fv s) S → Γ.canon S = .app (.tyc slotD .nil) .nil →
      Γ.slotSelf s = some Γ' → CoreTy b Γ' rest rets → CoreTy b Γ (.chk .slf (.fv s) x rest) rets
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
  | fixedOut : Γ.cmode = true → (Γ.fixed[x]?.join).map P.view = some (.app (.vc d c0 ls) vs) → Γ.known k = some (d, c) → c ≠ c0 →
      P.isNt d = false →
      BranchOK b fe Γ (.fv x) k H idx sig R none els
  | refuted : (Γ.branch P s k H idx sig).2 = .contra → BranchOK b fe Γ s k H idx sig R (some .dead) els

inductive GroupOK : Nat → Ctx → Group → Prop
  | mk {G : Group} : Γ.tys[G.lvl]? = some K → Γ.canon K = .level →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → TmTy P Γ (F.type G) .univ) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → (marks F.tele F.np).count true ≤ P.k) →
      (∀ (j : Nat) (F : FnDef), G.fns[j]? = some F → CoreTy gid (Γ.body G F).1 F.body (Γ.body G F).2) →
      (∀ i < Γ.n, Γ.er i = G.ers.getD i true) → Γ.ghost = G.ghost → G.deleOK P Γ.n = true → G.sidesOK Γ = true →
      GroupOK gid Γ G
end

end Minimal
