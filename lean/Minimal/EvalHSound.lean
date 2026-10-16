import Minimal.EvalH
import Minimal.Lemmas

namespace Minimal

def Tm.ptrBelow (n : Nat) : Tm → Bool
  | .ptr a => a < n
  | .cons h t | .app h t => h.ptrBelow n && t.ptrBelow n
  | .tyc _ ls | .vc _ _ ls => ls.ptrBelow n
  | .bind _ a r => a.ptrBelow n && r.ptrBelow n
  | .tyCtor p | .valCtor p => p.ptrBelow n
  | .predates A x L => A.ptrBelow n && x.ptrBelow n && L.ptrBelow n
  | .subterm A a B b => A.ptrBelow n && a.ptrBelow n && B.ptrBelow n && b.ptrBelow n
  | .fn l _ t _ _ => l.ptrBelow n && t.ptrBelow n
  | .mtbl _ _ _ _ T cs => T.ptrBelow n && cs.ptrBelow n
  | .clo env _ _ => env.ptrBelow n
  | _ => true

theorem Tm.ptrBelow_mono {n m : Nat} (h : n ≤ m) : ∀ t : Tm, t.ptrBelow n → t.ptrBelow m := by
  intro t; induction t <;> simp_all [ptrBelow] <;> omega

def Prim.tms : Prim → List Tm
  | .tm t | .lit t | .place t _ | .unplace t _ | .assert t _ | .coerce _ t _ | .wNext t | .placedSlot _ _ t _ => [t]
  | .placedEq _ A a _ | .wAsk A a => [A, a]
  | _ => []

mutual
def Core.ptrFree : Core → Bool
  | .ret ts => ts.ptrBelow 0
  | .call f _ args _ _ _ r => f.ptrBelow 0 && args.ptrBelow 0 && r.ptrFree
  | .mtch s _ brs els _ r => s.ptrBelow 0 && Core.brsPtrFree brs && Core.optPtrFree els && r.ptrFree
  | .prim p _ r => p.tms.all (·.ptrBelow 0) && r.ptrFree
  | .wdo w req r => w.ptrBelow 0 && req.ptrBelow 0 && r.ptrFree
  | .defLvl r | .defFns _ r | .chk _ _ _ r | .absurd r => r.ptrFree
  | .case s brs els _ _ => s.ptrBelow 0 && Core.brsPtrFree brs && Core.optPtrFree els
  | .seq _ b r => b.ptrFree && r.ptrFree
  | .dead => true

def Core.brsPtrFree : List Br → Bool
  | [] => true
  | (_, _, _, b) :: t => b.ptrFree && Core.brsPtrFree t

def Core.optPtrFree : Option Core → Bool
  | none => true
  | some e => e.ptrFree
end

def Prog.PtrFree (P : Prog) : Prop :=
  (∀ k c, (P.ask k c).2.ptrBelow 0) ∧ ∀ G ∈ P.groups, ∀ F ∈ G.fns, F.body.ptrFree

theorem natTm'_ptrBelow (d : Nat) : ∀ k, (natTm' d k).ptrBelow 0
  | 0 => rfl
  | k + 1 => by simp [natTm', Tm.ptrBelow, natTm'_ptrBelow d k]

namespace FHeap

def OK (H : FHeap) : Prop :=
  ∀ a t, H.blk a = some t → a < H.next ∧ t.ptrBelow a ∧ ∃ d c ls args, t = .app (.vc d c ls) args

def Ext (H H' : FHeap) : Prop := H.next ≤ H'.next ∧ ∀ a, a < H.next → H'.blk a = H.blk a

theorem Ext.refl (H : FHeap) : H.Ext H := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {H1 H2 H3 : FHeap} (a : H1.Ext H2) (b : H2.Ext H3) : H1.Ext H3 :=
  ⟨Nat.le_trans a.1 b.1, fun x hx => (b.2 x (Nat.lt_of_lt_of_le hx a.1)).trans (a.2 x hx)⟩

theorem dec_noPtr (H : FHeap) : ∀ (n : Nat) (t : Tm), t.ptrBelow 0 → H.dec n t = t := by
  intro n t; induction t generalizing n <;> intro h <;> cases n <;> simp_all [dec, Tm.ptrBelow]

theorem dec_fuel {H : FHeap} (hH : H.OK) : ∀ k n (t : Tm), t.ptrBelow k → k ≤ n → H.dec n t = H.dec k t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
    intro n t
    induction t generalizing n <;> intro ht hkn <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
    case ptr a =>
      simp only [decide_eq_true_eq] at ht
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [dec]
      cases hb : H.blk a with
      | none => rfl
      | some t' =>
        obtain ⟨-, hb', -⟩ := hH a t' hb
        show H.dec n' t' = H.dec k' t'
        rw [ihk k' (by omega) n' t' (Tm.ptrBelow_mono (by omega) t' hb') (by omega),
          ihk k' (by omega) k' t' (Tm.ptrBelow_mono (by omega) t' hb') (Nat.le_refl _)]
    all_goals (cases n <;> cases k <;> simp_all [dec])

theorem dec_ext {H H' : FHeap} (hH : H.OK) (he : H.Ext H') : ∀ n (t : Tm), t.ptrBelow H.next → H'.dec n t = H.dec n t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro t
    induction t <;> intro ht <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
    case ptr a =>
      simp only [decide_eq_true_eq] at ht
      cases n with
      | zero => simp [dec]
      | succ n' =>
        simp only [dec, he.2 a ht]
        cases hb : H.blk a with
        | none => simp
        | some t' =>
          obtain ⟨-, hb', -⟩ := hH a t' hb
          exact ihn n' (by omega) t' (Tm.ptrBelow_mono (by omega) t' hb')
    all_goals (cases n <;> simp_all [dec])

theorem slotOf_dec {H : FHeap} (hH : H.OK) (n : Nat) (w : Tm) : Tm.slotOf (H.dec n w) = Tm.slotOf w := by
  cases w <;> cases n <;> simp [dec, Tm.slotOf]
  rename_i a n
  cases hb : H.blk a with
  | none => simp
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec]

theorem dec_subst {H : FHeap} (hH : H.OK) (n : Nat) (f : Nat → Tm) : ∀ t : Tm, t.ptrBelow 0 →
    H.dec n (t.subst f) = t.subst (fun i => H.dec n (f i)) := by
  intro t; induction t generalizing n <;> intro ht <;> simp only [Tm.ptrBelow, Bool.and_eq_true] at ht
  case fv i => simp [Tm.subst]
  case sfv i =>
    simp only [Tm.subst, slotOf_dec hH]
    cases f i <;> cases n <;> simp [Tm.slotOf, dec, Tm.vacant]
  case ptr => simp at ht
  all_goals (cases n <;> simp_all [Tm.subst, dec, dec_noPtr])

theorem env_map_dec (H : FHeap) (n : Nat) (ρ : List Tm) :
    (fun i => H.dec n (Tm.env ρ i)) = Tm.env (ρ.map (H.dec n)) := by
  funext i; simp only [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ρ[i]? <;> cases n <;> simp [dec]

theorem alloc_ok {H : FHeap} (hH : H.OK) {d c : Nat} {ls args : Tm} (hp : (Tm.app (.vc d c ls) args).ptrBelow H.next) :
    (H.alloc (.app (.vc d c ls) args)).1.OK ∧ H.Ext (H.alloc (.app (.vc d c ls) args)).1 := by
  refine ⟨fun a t h => ?_, by simp [alloc], fun a ha => by simp [alloc]; omega⟩
  simp only [alloc] at h ⊢
  split at h
  · cases h; subst_vars; exact ⟨by omega, hp, d, c, ls, args, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hH a t h; exact ⟨by omega, h2, h3⟩

theorem alloc_next (H : FHeap) (t : Tm) : (H.alloc t).1.next = H.next + 1 := rfl

theorem alloc_dec (H : FHeap) (t : Tm) (n : Nat) : (H.alloc t).1.dec (n + 1) (.ptr (H.alloc t).2) = (H.alloc t).1.dec n t := by
  simp [alloc, dec]

theorem decode_eq {H : FHeap} (hH : H.OK) {t : Tm} (ht : t.ptrBelow H.next) {k : Nat} (hk : H.next ≤ k) :
    H.dec k t = H.decode t := dec_fuel hH _ _ _ ht hk

theorem decode_ext {H H' : FHeap} (hH : H.OK) (he : H.Ext H') {t : Tm} (ht : t.ptrBelow H.next) :
    H'.decode t = H.decode t := by
  simp only [decode]; rw [dec_ext hH he _ t ht]; exact dec_fuel hH _ _ _ ht he.1

theorem box_spec {H : FHeap} (hH : H.OK) : ∀ t : Tm, t.ptrBelow H.next →
    (H.box t).1.OK ∧ H.Ext (H.box t).1 ∧ (H.box t).2.ptrBelow (H.box t).1.next ∧
      (H.box t).1.decode (H.box t).2 = H.decode t := by
  intro t
  induction t generalizing H with
  | cons h t ihh iht =>
    intro hp; simp only [Tm.ptrBelow, Bool.and_eq_true] at hp
    obtain ⟨o1, e1, p1, d1⟩ := ihh hH hp.1
    obtain ⟨o2, e2, p2, d2⟩ := iht o1 (Tm.ptrBelow_mono e1.1 _ hp.2)
    simp only [box]
    refine ⟨o2, e1.trans e2, by simp [Tm.ptrBelow, p2, Tm.ptrBelow_mono e2.1 _ p1], ?_⟩
    have a1 := (decode_ext o1 e2 p1).trans d1
    have a2 := d2.trans (decode_ext hH e1 hp.2)
    simp only [decode, dec] at a1 a2 ⊢
    rw [a1, a2]
  | app h args ihh iha =>
    intro hp
    cases h with
    | vc d c ls =>
      simp only [Tm.ptrBelow, Bool.and_eq_true] at hp
      obtain ⟨o1, e1, p1, d1⟩ := iha hH hp.2
      have hb : (Tm.app (.vc d c ls) (H.box args).2).ptrBelow (H.box args).1.next := by
        simp [Tm.ptrBelow, p1, Tm.ptrBelow_mono e1.1 _ hp.1]
      obtain ⟨o2, e2⟩ := alloc_ok o1 hb
      simp only [box]
      refine ⟨o2, e1.trans e2, by simp [Tm.ptrBelow, alloc], ?_⟩
      have hls := decode_ext hH e1 hp.1
      simp only [decode] at d1 hls ⊢
      rw [alloc_next, alloc_dec]
      simp only [dec]
      rw [dec_ext o1 e2 _ _ p1, dec_ext o1 e2 _ _ (Tm.ptrBelow_mono e1.1 _ hp.1), d1, hls]
    | _ => exact ⟨hH, Ext.refl H, hp, rfl⟩
  | _ => intro hp; exact ⟨hH, Ext.refl H, hp, rfl⟩

theorem boxList_spec {H : FHeap} (hH : H.OK) : ∀ ts : List Tm, (∀ t ∈ ts, t.ptrBelow H.next) →
    (H.boxList ts).1.OK ∧ H.Ext (H.boxList ts).1 ∧ (∀ w ∈ (H.boxList ts).2, w.ptrBelow (H.boxList ts).1.next) ∧
      (H.boxList ts).2.map (H.boxList ts).1.decode = ts.map H.decode := by
  intro ts
  induction ts generalizing H with
  | nil => intro; exact ⟨hH, Ext.refl H, by simp [boxList], by simp [boxList]⟩
  | cons t ts ih =>
    intro hp
    obtain ⟨o1, e1, p1, d1⟩ := box_spec hH t (hp t (by simp))
    obtain ⟨o2, e2, p2, d2⟩ := ih o1 (fun u hu => Tm.ptrBelow_mono e1.1 _ (hp u (by simp [hu])))
    simp only [boxList]
    refine ⟨o2, e1.trans e2, ?_, ?_⟩
    · simp only [List.mem_cons]; rintro w (rfl | hw)
      · exact Tm.ptrBelow_mono e2.1 _ p1
      · exact p2 w hw
    · simp only [List.map_cons, d2, decode_ext o1 e2 p1, d1, List.cons.injEq, true_and]
      exact List.map_congr_left (fun u hu => decode_ext hH e1 (hp u (by simp [hu])))

theorem dec_toList {H : FHeap} (hH : H.OK) (n : Nat) : ∀ t : Tm, (H.dec n t).toList = t.toList.map (H.dec n) := by
  intro t; induction t <;> cases n <;> simp_all [dec, Tm.toList]
  rename_i a n
  cases hb : H.blk a with
  | none => simp [Tm.toList]
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec, Tm.toList]

theorem dec_ofList (H : FHeap) (n : Nat) : ∀ l : List Tm, H.dec n (Tm.ofList l) = Tm.ofList (l.map (H.dec n))
  | [] => by cases n <;> simp [dec, Tm.ofList]
  | t :: l => by cases n <;> simp [dec, Tm.ofList, dec_ofList H _ l]

theorem dec_lvl {H : FHeap} (hH : H.OK) (n m : Nat) (t : Tm) : H.dec n t = .lvl m ↔ t = .lvl m := by
  cases t <;> cases n <;> simp [dec]
  rename_i a n
  cases hb : H.blk a with
  | none => simp
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec]

theorem dec_vc {H : FHeap} (hH : H.OK) {n d c : Nat} {ls : Tm} : ∀ {t : Tm}, H.dec n t = .vc d c ls → ∃ ls', t = .vc d c ls' := by
  intro t h
  cases t <;> cases n <;> simp [dec] at h ⊢ <;> try exact h.1
  all_goals first
    | (obtain ⟨rfl, rfl, -⟩ := h; simp)
    | skip
  rename_i a n
  revert h
  cases hb : H.blk a with
  | none => simp
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec]

theorem ptrBelow_toList {n : Nat} : ∀ {t : Tm}, t.ptrBelow n → ∀ x ∈ t.toList, x.ptrBelow n := by
  intro t; induction t <;> simp_all [Tm.toList, Tm.ptrBelow]

theorem subst_ptrBelow {n : Nat} {f : Nat → Tm} (hf : ∀ i, (f i).ptrBelow n) : ∀ t : Tm, t.ptrBelow 0 → (t.subst f).ptrBelow n := by
  intro t; induction t <;> intro ht
  case sfv i => simp only [Tm.subst]; cases f i <;> simp [Tm.slotOf, Tm.vacant, Tm.ptrBelow]
  case clo => exact Tm.ptrBelow_mono (Nat.zero_le _) _ ht
  all_goals simp_all [Tm.subst, Tm.ptrBelow]

theorem env_ptrBelow {n : Nat} {ρ : List Tm} (h : ∀ w ∈ ρ, w.ptrBelow n) (i : Nat) : (Tm.env ρ i).ptrBelow n := by
  simp only [Tm.env, List.getD_eq_getElem?_getD]
  cases hi : ρ[i]? with
  | none => simp [Tm.ptrBelow]
  | some w => exact h w (List.mem_of_getElem? hi)

theorem view_spec {H : FHeap} (hH : H.OK) {w : Tm} (hw : w.ptrBelow H.next) :
    (H.view w).ptrBelow H.next ∧ H.decode (H.view w) = H.decode w := by
  cases w <;> try exact ⟨hw, rfl⟩
  rename_i a
  simp only [view]
  cases hb : H.blk a with
  | none => exact ⟨hw, rfl⟩
  | some t =>
    obtain ⟨ha, ht, -⟩ := hH a t hb
    refine ⟨Tm.ptrBelow_mono (by omega) t ht, ?_⟩
    simp only [Option.getD_some, decode]
    obtain ⟨k, hk⟩ : ∃ k, H.next = k + 1 := ⟨H.next - 1, by omega⟩
    rw [hk]; simp only [dec, hb]
    rw [dec_fuel hH a k t ht (by omega), dec_fuel hH a (k + 1) t ht (by omega)]

theorem callee_dec (P : Prog) {H : FHeap} (hH : H.OK) (n : Nat) (w : Tm) :
    callee P (H.dec n w) = (callee P w).map fun (env, m, gid, G, F) => (env.map (H.dec n), m, gid, G, F) := by
  cases w
  case ptr a =>
    cases n with
    | zero => simp [dec, callee]
    | succ n =>
      simp only [dec]
      cases hb : H.blk a with
      | none => simp [callee]
      | some t =>
        obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
        cases n <;> simp [dec, callee]
  case clo env gid j =>
    have e : H.dec n (.clo env gid j) = .clo (H.dec n env) gid j := by cases n <;> simp [dec]
    rw [e]; simp only [callee]
    cases P.groups[gid]? <;> try simp
    rename_i G
    cases G.fns[j]? <;> try simp
    rw [dec_toList hH]
    simp only [List.getElem?_map]
    cases env.toList[G.lvl]? with
    | none => simp
    | some x =>
      by_cases hx : ∃ m, x = .lvl m
      · obtain ⟨m, rfl⟩ := hx; cases n <;> simp [dec]
      · have h1 : ∀ m, H.dec n x ≠ .lvl m := fun m h => hx ⟨m, (dec_lvl hH n m x).1 h⟩
        split
        · rename_i h; simp at h; exact absurd h (h1 _)
        · split
          · rename_i h; simp at h; exact absurd ⟨_, h⟩ hx
          · rfl
  all_goals cases n <;> simp [dec, callee]

theorem closures_dec (H : FHeap) (n : Nat) (env : List Tm) (gid : Nat) (G : Group) :
    closures (env.map (H.dec n)) gid G = (closures env gid G).map (H.dec n) := by
  simp only [closures, List.map_map]; congr 1; funext j; cases n <;> simp [dec, dec_ofList]

theorem markedArgs_map (f : Tm → Tm) : ∀ (t : Tm) (l : List Tm), markedArgs t (.ofList (l.map f)) = (markedArgs t (.ofList l)).map f := by
  intro t; induction t <;> intro l <;> cases l <;> simp [markedArgs, Tm.ofList]
  rename_i ih _ _; split <;> simp [ih]

theorem dec_wld {H : FHeap} (hH : H.OK) (n m : Nat) (t : Tm) : H.dec n t = .wld m ↔ t = .wld m := by
  cases t <;> cases n <;> simp [dec]
  rename_i a n
  cases hb : H.blk a with
  | none => simp
  | some t =>
    obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH a t hb
    cases n <;> simp [dec]

theorem dec_wnext {H : FHeap} (hH : H.OK) (n : Nat) (t : Tm) : H.dec n t.wnext = (H.dec n t).wnext := by
  by_cases h : ∃ m, t = .wld m
  · obtain ⟨m, rfl⟩ := h; cases n <;> simp [dec, Tm.wnext]
  · have h1 : ∀ m, H.dec n t ≠ .wld m := fun m e => h ⟨m, (dec_wld hH n m t).1 e⟩
    rw [show t.wnext = .tok by unfold Tm.wnext; split <;> simp_all,
      show (H.dec n t).wnext = .tok by unfold Tm.wnext; split <;> simp_all]
    cases n <;> simp [dec]

theorem view_noBlk {H : FHeap} (hH : H.OK) {w : Tm} {a : Nat} (h : H.view w = .ptr a) : H.blk a = none := by
  cases w <;> simp [view] at h
  rename_i b
  cases hb : H.blk b with
  | none => simp [hb] at h; subst h; exact hb
  | some t => obtain ⟨-, -, d, c, ls, args, rfl⟩ := hH b t hb; simp [hb] at h

theorem answer_tok1 (P : Prog) (y z : Tm) (h : ∀ m, y ≠ .wld m) : P.answer y z = (.tok, .tok) := by
  unfold Prog.answer; split <;> simp_all

theorem answer_tok2 (P : Prog) (y z : Tm) (h : ∀ d c ls vs, z ≠ .app (.vc d c ls) vs) : P.answer y z = (.tok, .tok) := by
  unfold Prog.answer; split
  · exact absurd rfl (h _ _ _ _)
  · rfl

theorem answer_dec (P : Prog) {H : FHeap} (hH : H.OK) (n : Nat) (y z : Tm) (hz : ∀ a, z = .ptr a → H.blk a = none) :
    P.answer (H.dec n y) (H.dec n z) = P.answer y z := by
  by_cases hy : ∃ m, y = .wld m
  · obtain ⟨m, rfl⟩ := hy
    rw [show H.dec n (.wld m) = .wld m by cases n <;> simp [dec]]
    by_cases hd : ∃ d c ls vs, z = .app (.vc d c ls) vs
    · obtain ⟨d, c, ls, vs, rfl⟩ := hd; cases n <;> simp [dec, Prog.answer]
    · have : ∀ d c ls vs, H.dec n z ≠ .app (.vc d c ls) vs := by
        intro d c ls vs e
        cases z <;> cases n <;> simp [dec] at e
        all_goals first
          | (obtain ⟨ls', rfl⟩ := dec_vc hH e.1; exact hd ⟨_, _, _, _, rfl⟩)
          | (rename_i a _; rw [hz a rfl] at e; simp at e)
      rw [answer_tok2 P _ _ this, answer_tok2 P _ _ fun d c ls vs e => hd ⟨d, c, ls, vs, e⟩]
  · rw [answer_tok1 P _ _ fun m e => hy ⟨m, (dec_wld hH n m y).1 e⟩, answer_tok1 P _ _ fun m e => hy ⟨m, e⟩]

theorem subst_spec {H : FHeap} (hH : H.OK) {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {t : Tm} (ht : t.ptrBelow 0) :
    (t.subst (Tm.env ρ)).ptrBelow H.next ∧ H.decode (t.subst (Tm.env ρ)) = t.subst (Tm.env (ρ.map H.decode)) := by
  refine ⟨subst_ptrBelow (env_ptrBelow hρ) t ht, ?_⟩
  simp only [decode]; rw [dec_subst hH _ _ t ht, env_map_dec]; rfl

theorem prim_spec {H : FHeap} (hH : H.OK) {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {p : Prim}
    (hp : p.tms.all (·.ptrBelow 0)) (hw : ∀ w r, p ≠ .wAsk w r) :
    (p.eval P ρ).ptrBelow H.next ∧ H.decode (p.eval P ρ) = p.eval P (ρ.map H.decode) := by
  have noP : ∀ t : Tm, t.ptrBelow 0 → t.ptrBelow H.next ∧ H.decode t = t :=
    fun t ht => ⟨Tm.ptrBelow_mono (Nat.zero_le _) t ht, dec_noPtr H _ t ht⟩
  cases p <;> simp only [Prim.tms, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
  case wAsk => exact absurd rfl (hw _ _)
  case tm t | lit t | place t _ | unplace t _ | coerce _ t _ => exact subst_spec hH hρ hp
  case assert t _ => exact noP t hp
  case num d k => exact noP _ (natTm'_ptrBelow d k)
  case wNext t =>
    obtain ⟨h1, h2⟩ := subst_spec hH hρ hp
    refine ⟨?_, ?_⟩
    · simp only [Prim.eval]; unfold Tm.wnext; split <;> simp [Tm.ptrBelow]
    · simp only [Prim.eval, decode] at h2 ⊢; rw [dec_wnext hH, h2]
  case placedSlot d q a _ =>
    obtain ⟨h1, h2⟩ := subst_spec hH hρ hp
    simp only [decode] at h2
    simp [Prim.eval, Tm.ptrBelow, h1, decode, dec, h2]
  case placedEq q A a _ =>
    obtain ⟨h1, h2⟩ := subst_spec hH hρ hp.1
    obtain ⟨h3, h4⟩ := subst_spec hH hρ hp.2
    simp only [decode] at h2 h4
    simp [Prim.eval, Tm.ptrBelow, h1, h3, decode, dec, h2, h4]
  all_goals exact noP _ rfl

theorem answer_ptrFree {P : Prog} (hask : ∀ k c, (P.ask k c).2.ptrBelow 0) (y z : Tm) : (P.answer y z).2.ptrBelow 0 := by
  unfold Prog.answer; split
  · exact hask _ _
  · rfl

theorem primH_spec {H : FHeap} (hH : H.OK) (hask : ∀ k c, (P.ask k c).2.ptrBelow 0) {ρ : List Tm}
    (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {p : Prim} (hp : p.tms.all (·.ptrBelow 0)) :
    (p.evalH P H ρ).1.OK ∧ H.Ext (p.evalH P H ρ).1 ∧ (p.evalH P H ρ).2.ptrBelow (p.evalH P H ρ).1.next ∧
      (p.evalH P H ρ).1.decode (p.evalH P H ρ).2 = p.eval P (ρ.map H.decode) := by
  by_cases hw : ∃ w r, p = .wAsk w r
  · obtain ⟨w, r, rfl⟩ := hw
    simp only [Prim.tms, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
    have ha := answer_ptrFree hask (w.subst (Tm.env ρ)) (H.view (r.subst (Tm.env ρ)))
    obtain ⟨o, e, pb, d⟩ := box_spec hH _ (Tm.ptrBelow_mono (Nat.zero_le _) _ ha)
    refine ⟨o, e, pb, ?_⟩
    simp only [Prim.evalH, Prim.eval] at d ⊢
    rw [d, decode, dec_noPtr H _ _ ha]
    obtain ⟨-, h2⟩ := subst_spec hH hρ hp.1
    obtain ⟨h3, h4⟩ := subst_spec hH hρ hp.2
    obtain ⟨-, h5⟩ := view_spec hH h3
    rw [← h2, ← h4, ← h5]
    exact (congrArg Prod.snd (answer_dec P hH _ _ _ fun a e => view_noBlk hH e)).symm
  · have hw' : ∀ w r, p ≠ .wAsk w r := fun w r e => hw ⟨w, r, e⟩
    obtain ⟨h1, h2⟩ := prim_spec (P := P) hH hρ hp hw'
    have he : p.evalH P H ρ = H.box (p.eval P ρ) := by
      cases p <;> first | rfl | exact absurd rfl (hw' _ _)
    rw [he]
    obtain ⟨o, e, pb, d⟩ := box_spec hH _ h1
    exact ⟨o, e, pb, d.trans h2⟩

theorem map_decode_ext {H H' : FHeap} (hH : H.OK) (he : H.Ext H') {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) :
    ρ.map H'.decode = ρ.map H.decode :=
  List.map_congr_left fun w hw => decode_ext hH he (hρ w hw)

theorem ofList_ptrBelow {n : Nat} : ∀ {l : List Tm}, (∀ w ∈ l, w.ptrBelow n) → (Tm.ofList l).ptrBelow n
  | [], _ => rfl
  | _ :: _, h => by simp only [Tm.ofList, Tm.ptrBelow, Bool.and_eq_true]; exact ⟨h _ (by simp), ofList_ptrBelow fun w hw => h w (by simp [hw])⟩

theorem closures_ptrBelow {n : Nat} {env : List Tm} (h : ∀ w ∈ env, w.ptrBelow n) (gid : Nat) (G : Group) :
    ∀ w ∈ closures env gid G, w.ptrBelow n := by
  simp only [closures, List.mem_map]; rintro _ ⟨j, -, rfl⟩; exact ofList_ptrBelow h

theorem decode_data {H : FHeap} (hH : H.OK) {w : Tm} (hw : w.ptrBelow H.next) {d c : Nat} {ls vs : Tm}
    (h : H.view w = .app (.vc d c ls) vs) :
    vs.ptrBelow H.next ∧ H.decode w = .app (.vc d c (H.decode ls)) (H.decode vs) := by
  obtain ⟨h1, h2⟩ := view_spec hH hw
  rw [h] at h1 h2; simp only [Tm.ptrBelow, Bool.and_eq_true] at h1
  refine ⟨h1.2, ?_⟩
  rw [← h2]; simp only [decode]; cases H.next <;> simp [dec]

theorem decode_notData {H : FHeap} (hH : H.OK) {w : Tm} (hw : w.ptrBelow H.next)
    (h : ∀ d c ls vs, H.view w = .app (.vc d c ls) vs → False) : ∀ d c ls vs, H.decode w = .app (.vc d c ls) vs → False := by
  intro d c ls vs e
  obtain ⟨-, h2⟩ := view_spec hH hw
  rw [← h2] at e
  have hz : ∀ a, H.view w = .ptr a → H.blk a = none := fun a e => view_noBlk hH e
  revert h e hz
  generalize H.view w = v
  intro h e hz
  cases v <;> simp only [decode] at e <;> cases hn : H.next <;> rw [hn] at e <;> simp [dec] at e
  all_goals first
    | (obtain ⟨ls', rfl⟩ := dec_vc hH e.1; exact h _ _ _ _ rfl)
    | (rename_i a _; rw [hz a rfl] at e; simp at e)

theorem selectBr_map (f : Tm → Tm) (brs : List Br) (els : Option Core) (c : Nat) (l : List Tm) :
    selectBr brs els c (l.map f) = (selectBr brs els c l).map fun (pre, b) => (pre.map f, b) := by
  unfold selectBr; split <;> cases els <;> simp

theorem callee_spec {P : Prog} {w : Tm} {env : List Tm} {n gid : Nat} {G : Group} {F : FnDef} {m : Nat}
    (h : callee P w = some (env, n, gid, G, F)) (hw : w.ptrBelow m) :
    G ∈ P.groups ∧ F ∈ G.fns ∧ ∀ x ∈ env, x.ptrBelow m := by
  cases w <;> simp [callee] at h
  rename_i e gid' j
  simp only [Tm.ptrBelow] at hw
  cases hg : P.groups[gid']? <;> simp [hg] at h
  rename_i G'
  cases hf : G'.fns[j]? <;> simp [hf] at h
  split at h <;> simp at h
  obtain ⟨rfl, -, rfl, rfl, rfl⟩ := h
  exact ⟨List.mem_of_getElem? hg, List.mem_of_getElem? hf, ptrBelow_toList hw⟩

end FHeap

open FHeap

def HRes (H : FHeap) : Except String (FHeap × List Tm × Nat) → Except String (List Tm × Nat) → Prop
  | .ok (H', ws, c), r => H'.OK ∧ H.Ext H' ∧ (∀ w ∈ ws, w.ptrBelow H'.next) ∧ r = .ok (ws.map H'.decode, c)
  | .error e, r => r = .error e

theorem HRes.ext {H H1 : FHeap} (he : H.Ext H1) {r r'} (h : HRes H1 r r') : HRes H r r' := by
  match r, h with
  | .ok _, ⟨o, e, p, d⟩ => exact ⟨o, he.trans e, p, d⟩
  | .error _, h => exact h

theorem substs_spec {H : FHeap} (hH : H.OK) {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {ts : Tm} (ht : ts.ptrBelow 0) :
    (∀ t ∈ ts.toList.map (·.subst (Tm.env ρ)), t.ptrBelow H.next) ∧
      (ts.toList.map (·.subst (Tm.env ρ))).map H.decode = ts.toList.map (·.subst (Tm.env (ρ.map H.decode))) := by
  refine ⟨?_, ?_⟩
  · simp only [List.mem_map]; rintro _ ⟨t, htm, rfl⟩; exact (subst_spec hH hρ (ptrBelow_toList ht t htm)).1
  · simp only [List.map_map]; exact List.map_congr_left fun t htm => (subst_spec hH hρ (ptrBelow_toList ht t htm)).2

theorem ptrs_app {H H1 : FHeap} {ρ ws : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) (e : H.Ext H1)
    (hw : ∀ w ∈ ws, w.ptrBelow H1.next) : ∀ w ∈ ρ ++ ws, w.ptrBelow H1.next := by
  intro w hw'; rcases List.mem_append.mp hw' with h | h
  · exact Tm.ptrBelow_mono e.1 w (hρ w h)
  · exact hw w h

theorem call_spec {P : Prog} {H H1 : FHeap} (hH : H.OK) {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {f args : Tm}
    (hcf : f.ptrBelow 0) (hca : args.ptrBelow 0) {env ws : List Tm} {n gid : Nat} {G : Group} {F : FnDef}
    (hcal : callee P (f.subst (Tm.env ρ)) = some (env, n, gid, G, F))
    (hbx : H.boxList (args.toList.map (·.subst (Tm.env ρ))) = (H1, ws)) :
    H1.OK ∧ H.Ext H1 ∧ (∀ w ∈ env ++ closures env gid G ++ ws, w.ptrBelow H1.next) ∧ G ∈ P.groups ∧ F ∈ G.fns ∧
      callee P (f.subst (Tm.env (ρ.map H.decode))) = some (env.map H1.decode, n, gid, G, F) ∧
      args.toList.map (·.subst (Tm.env (ρ.map H.decode))) = ws.map H1.decode ∧
      (env ++ closures env gid G ++ ws).map H1.decode = env.map H1.decode ++ closures (env.map H1.decode) gid G ++ ws.map H1.decode := by
  obtain ⟨hf1, hf2⟩ := subst_spec hH hρ hcf
  obtain ⟨hG, hF, henv⟩ := callee_spec hcal hf1
  obtain ⟨hs1, hs2⟩ := substs_spec hH hρ hca
  obtain ⟨o, e, p, d⟩ := boxList_spec hH _ hs1
  rw [hbx] at o e p d
  have henv1 := fun x hx => Tm.ptrBelow_mono e.1 x (henv x hx)
  refine ⟨o, e, ?_, hG, hF, ?_, by rw [← hs2, d], ?_⟩
  rotate_left 2
  · rw [List.map_append, List.map_append]; congr 2; exact (closures_dec H1 H1.next env gid G).symm
  · intro w hw; simp only [List.mem_append] at hw
    rcases hw with (h | h) | h
    · exact henv1 w h
    · exact closures_ptrBelow henv1 gid G w h
    · exact p w h
  · rw [← hf2, decode, callee_dec P hH, hcal, map_decode_ext hH e henv]; rfl

theorem brs_ptrFree {brs : List Br} (h : Core.brsPtrFree brs) {c : Nat} {body : Core} (hl : lookupBr brs c = some body) :
    body.ptrFree := by
  induction brs with
  | nil => simp [lookupBr] at hl
  | cons b t ih =>
    obtain ⟨n, c', k, b'⟩ := b
    simp only [Core.brsPtrFree, Bool.and_eq_true] at h
    simp only [lookupBr, List.find?_cons] at hl
    split at hl
    · simp at hl; exact hl ▸ h.1
    · exact ih h.2 hl

theorem selectBr_spec {brs : List Br} {els : Option Core} {c : Nat} {l pre : List Tm} {body : Core}
    (h : selectBr brs els c l = some (pre, body)) (hb : Core.brsPtrFree brs) (he : Core.optPtrFree els) :
    (∀ x ∈ pre, x ∈ l) ∧ body.ptrFree := by
  unfold selectBr at h; split at h
  · rename_i hl; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨fun _ h => h, brs_ptrFree hb hl⟩
  · cases els <;> simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨by simp, he⟩

theorem mtch_spec {H : FHeap} (hH : H.OK) {ρ : List Tm} (hρ : ∀ w ∈ ρ, w.ptrBelow H.next) {s : Tm} (hcs : s.ptrBelow 0)
    {d c : Nat} {ls vs : Tm} (hs : H.view (s.subst (Tm.env ρ)) = .app (.vc d c ls) vs) :
    (∀ w ∈ vs.toList, w.ptrBelow H.next) ∧
      s.subst (Tm.env (ρ.map H.decode)) = .app (.vc d c (H.decode ls)) (H.decode vs) ∧
      (H.decode vs).toList = vs.toList.map H.decode := by
  obtain ⟨hs1, hs2⟩ := subst_spec hH hρ hcs
  obtain ⟨hvs, hd⟩ := decode_data hH hs1 hs
  exact ⟨ptrBelow_toList hvs, by rw [← hs2, hd], dec_toList hH _ vs⟩

theorem evalH_sim (hP : P.PtrFree) : ∀ μ H ρ cnt c, c.ptrFree → H.OK → (∀ w ∈ ρ, w.ptrBelow H.next) →
    HRes H (evalH P μ H ρ cnt c) (eval P μ (ρ.map H.decode) cnt c) := by
  intro μ H ρ cnt c
  induction μ, H, ρ, cnt, c using evalH.induct P with
  | case1 μ H ρ cnt ts H1 ws hb =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    obtain ⟨hs1, hs2⟩ := substs_spec hH hρ hc
    obtain ⟨o, e, p, d⟩ := boxList_spec hH _ hs1
    rw [hb] at o e p d
    rw [evalH, eval]; simp only [hb]
    exact ⟨o, e, p, by rw [d, hs2]⟩
  | case10 μ H ρ cnt p er rest H1 w hpe ih =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨o, e, pb, d⟩ := primH_spec (P := P) hH hP.1 hρ hc.1
    rw [hpe] at o e pb d
    rw [evalH, eval]; simp only [hpe]
    have := ih hc.2 o (ptrs_app hρ e (by simpa using pb))
    rw [List.map_append, map_decode_ext hH e hρ] at this
    simp only [List.map_cons, List.map_nil, d] at this
    exact this.ext e
  | case11 μ H ρ cnt w req rest H1 w1 h1 H2 w2 h2 ih =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨o1, e1, p1, d1⟩ := primH_spec (P := P) (p := .wNext w) hH hP.1 hρ (by simp [Prim.tms, hc.1.1])
    rw [h1] at o1 e1 p1 d1
    have hρ1 := fun x hx => Tm.ptrBelow_mono e1.1 x (hρ x hx)
    obtain ⟨o2, e2, p2, d2⟩ := primH_spec (P := P) (p := .wAsk w req) o1 hP.1 hρ1 (by simp [Prim.tms, hc.1.1, hc.1.2])
    rw [h2] at o2 e2 p2 d2
    rw [evalH, eval]; simp only [h1, h2]
    have := ih hc.2 o2 (ptrs_app hρ (e1.trans e2) (by simp [p2, Tm.ptrBelow_mono e2.1 _ p1]))
    rw [List.map_append, map_decode_ext hH (e1.trans e2) hρ] at this
    simp only [List.map_cons, List.map_nil, d2, decode_ext o1 e2 p1, d1, map_decode_ext hH e1 hρ] at this
    exact this.ext (e1.trans e2)
  | case12 μ H ρ cnt rest ih =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    rw [evalH, eval]
    have := ih hc hH (ptrs_app hρ (Ext.refl H) (by simp [Tm.ptrBelow]))
    have hl : H.decode (.lvl cnt) = .lvl cnt := by simp only [decode]; cases H.next <;> simp [dec]
    simpa [hl] using this
  | case13 μ H ρ cnt gid rest G hg ih =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    rw [evalH, eval]; simp only [hg]
    have := ih hc hH (ptrs_app hρ (Ext.refl H) (closures_ptrBelow hρ gid G))
    rwa [List.map_append, show (closures ρ gid G).map H.decode = closures (ρ.map H.decode) gid G from
      (closures_dec H _ ρ gid G).symm] at this
  | case14 μ H ρ cnt gid rest hg =>
    intro hc hH hρ
    rw [evalH, eval]; simp only [hg]; rfl
  | case15 μ H ρ cnt k a b rest ih =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    rw [evalH, eval]; exact ih hc hH hρ
  | case16 μ H ρ cnt body r hev ih =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    have := ih hc hH hρ
    rw [hev] at this
    obtain ⟨H', ws, c⟩ := r
    obtain ⟨-, -, -, d⟩ := this
    rw [evalH, eval]; simp only [hev, d]; rfl
  | case17 μ H ρ cnt body e hev ih =>
    intro hc hH hρ
    simp only [Core.ptrFree] at hc
    have := ih hc hH hρ
    rw [hev] at this
    rw [evalH, eval]; simp only [hev]; simp only [HRes] at this; simp only [this]; rfl
  | case18 μ H ρ cnt =>
    intro hc hH hρ
    rw [evalH, eval]; rfl
  | case22 μ H ρ cnt R body rest H1 outs cnt1 hev ihb ihr =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    have := ihb hc.1 hH hρ
    rw [hev] at this
    obtain ⟨o, e, pb, d⟩ := this
    have := ihr hc.2 o (ptrs_app hρ e pb)
    rw [List.map_append, map_decode_ext hH e hρ] at this
    rw [evalH, eval]; simp only [hev, d]
    exact this.ext e
  | case23 μ H ρ cnt R body rest e hev ihb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    have := ihb hc.1 hH hρ
    rw [hev] at this
    rw [evalH, eval]; simp only [hev]; simp only [HRes] at this; simp only [this]; rfl
  | case2 μ H ρ cnt f dec args er ms ve rest env n gid G F hcal H1 ws hbx μ' hmu H2 outs cnt1 hev ihb ihr =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨o, e, pw, hG, hF, hcal', hargs, hbe⟩ := call_spec hH hρ hc.1.1 hc.1.2 hcal hbx
    have := ihb (hP.2 G hG F hF) o pw
    rw [hev, hbe] at this
    obtain ⟨o2, e2, p2, d2⟩ := this
    have := ihr hc.2 o2 (ptrs_app hρ (e.trans e2) p2)
    rw [List.map_append, map_decode_ext hH (e.trans e2) hρ] at this
    rw [evalH, eval]; simp only [hcal, hbx, hcal', hargs, markedArgs_map, List.map_map]
    simp only [Function.comp_def]
    rw [dite_eq_left hmu, dite_eq_left hmu]
    simp only [μ'] at hev d2; simp only [hev, d2]
    exact (this.ext e2).ext e
  | case3 μ H ρ cnt f dec args er ms ve rest env n gid G F hcal H1 ws hbx μ' hmu e hev ihb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨o, -, pw, hG, hF, hcal', hargs, hbe⟩ := call_spec hH hρ hc.1.1 hc.1.2 hcal hbx
    have := ihb (hP.2 G hG F hF) o pw
    rw [hev, hbe] at this
    rw [evalH, eval]; simp only [hcal, hbx, hcal', hargs, markedArgs_map, List.map_map]
    simp only [Function.comp_def]
    rw [dite_eq_left hmu, dite_eq_left hmu]
    simp only [μ'] at hev this; simp only [HRes] at this; simp only [hev, this]; rfl
  | case4 μ H ρ cnt f dec args er ms ve rest env n gid G F hcal H1 ws hbx μ' hmu =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨-, -, -, -, -, hcal', hargs, -⟩ := call_spec hH hρ hc.1.1 hc.1.2 hcal hbx
    rw [evalH, eval]; simp only [hcal, hbx, hcal', hargs, markedArgs_map, List.map_map]
    simp only [Function.comp_def]
    rw [dite_eq_right hmu, dite_eq_right hmu]; rfl
  | case5 μ H ρ cnt f dec args er ms ve rest hcal =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hf1, hf2⟩ := subst_spec hH hρ hc.1.1
    rw [evalH, eval, ← hf2, decode, callee_dec P hH, hcal]; rfl
  | case6 μ H ρ cnt s rets brs els er rest d c ls vs hs pre body hb H1 outs cnt1 hev ihb ihr =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hvs, hs', hl⟩ := mtch_spec hH hρ hc.1.1.1 hs
    obtain ⟨hpre, hbody⟩ := selectBr_spec hb hc.1.1.2 hc.1.2
    have hb' : selectBr brs els c (H.decode vs).toList = some (pre.map H.decode, body) := by
      rw [hl, selectBr_map, hb]; rfl
    have := ihb hbody hH (ptrs_app hρ (Ext.refl H) fun w hw => hvs w (hpre w hw))
    rw [hev, List.map_append] at this
    obtain ⟨o, e, p, d⟩ := this
    have := ihr hc.2 o (ptrs_app hρ e p)
    rw [List.map_append, map_decode_ext hH e hρ] at this
    rw [evalH, eval]; simp only [hs, hs']
    split
    next p1 b1 h1 =>
      rw [hb] at h1; cases h1
      simp only [hev]
      split
      next p2 b2 h2 =>
        rw [hb'] at h2; cases h2
        simp only [d]; exact this.ext e
      next h2 => rw [hb'] at h2; cases h2
    next h1 => rw [hb] at h1; cases h1
  | case7 μ H ρ cnt s rets brs els er rest d c ls vs hs pre body hb e hev ihb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hvs, hs', hl⟩ := mtch_spec hH hρ hc.1.1.1 hs
    obtain ⟨hpre, hbody⟩ := selectBr_spec hb hc.1.1.2 hc.1.2
    have hb' : selectBr brs els c (H.decode vs).toList = some (pre.map H.decode, body) := by
      rw [hl, selectBr_map, hb]; rfl
    have := ihb hbody hH (ptrs_app hρ (Ext.refl H) fun w hw => hvs w (hpre w hw))
    rw [hev, List.map_append] at this; simp only [HRes] at this
    rw [evalH, eval]; simp only [hs, hs']
    split
    next p1 b1 h1 =>
      rw [hb] at h1; cases h1
      simp only [hev]
      split
      next p2 b2 h2 => rw [hb'] at h2; cases h2; simp only [this]; rfl
      next h2 => rw [hb'] at h2; cases h2
    next h1 => rw [hb] at h1; cases h1
  | case8 μ H ρ cnt s rets brs els er rest d c ls vs hs hb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨-, hs', hl⟩ := mtch_spec hH hρ hc.1.1.1 hs
    have hb' : selectBr brs els c (H.decode vs).toList = none := by rw [hl, selectBr_map, hb]; rfl
    rw [evalH, eval]; simp only [hs, hs']
    split
    next p1 b1 h1 => rw [hb] at h1; cases h1
    next h1 =>
      split
      next p2 b2 h2 => rw [hb'] at h2; cases h2
      next h2 => rfl
  | case9 μ H ρ cnt s rets brs els er rest hs =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hs1, hs2⟩ := subst_spec hH hρ hc.1.1.1
    have hn := decode_notData hH hs1 hs
    rw [evalH, eval, ← hs2]
    split
    next d c ls vs h1 => exact absurd h1 (hs d c ls vs ·)
    next =>
      split
      next d c ls vs h2 => exact absurd h2 (hn d c ls vs ·)
      next => rfl
  | case19 μ H ρ cnt s brs els er nt d c ls vs hs pre body hb ihb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hvs, hs', hl⟩ := mtch_spec hH hρ hc.1.1 hs
    obtain ⟨hpre, hbody⟩ := selectBr_spec hb hc.1.2 hc.2
    have hb' : selectBr brs els c (H.decode vs).toList = some (pre.map H.decode, body) := by
      rw [hl, selectBr_map, hb]; rfl
    have := ihb hbody hH (ptrs_app hρ (Ext.refl H) fun w hw => hvs w (hpre w hw))
    rw [List.map_append] at this
    rw [evalH, eval]; simp only [hs, hs']
    split
    next p1 b1 h1 =>
      rw [hb] at h1; cases h1
      split
      next p2 b2 h2 => rw [hb'] at h2; cases h2; exact this
      next h2 => rw [hb'] at h2; cases h2
    next h1 => rw [hb] at h1; cases h1
  | case20 μ H ρ cnt s brs els er nt d c ls vs hs hb =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨-, hs', hl⟩ := mtch_spec hH hρ hc.1.1 hs
    have hb' : selectBr brs els c (H.decode vs).toList = none := by rw [hl, selectBr_map, hb]; rfl
    rw [evalH, eval]; simp only [hs, hs']
    split
    next p1 b1 h1 => rw [hb] at h1; cases h1
    next h1 =>
      split
      next p2 b2 h2 => rw [hb'] at h2; cases h2
      next h2 => rfl
  | case21 μ H ρ cnt s brs els er nt hs =>
    intro hc hH hρ
    simp only [Core.ptrFree, Bool.and_eq_true] at hc
    obtain ⟨hs1, hs2⟩ := subst_spec hH hρ hc.1.1
    have hn := decode_notData hH hs1 hs
    rw [evalH, eval, ← hs2]
    split
    next d c ls vs h1 => exact absurd h1 (hs d c ls vs ·)
    next =>
      split
      next d c ls vs h2 => exact absurd h2 (hn d c ls vs ·)
      next => rfl

theorem evalH_main (hP : P.PtrFree) (hm : P.main.ptrFree) :
    HRes {} (evalH P none {} [] 0 P.main) (eval P none [] 0 P.main) :=
  evalH_sim hP none {} [] 0 P.main hm (fun _ _ h => by cases h) (by simp)

end Minimal
