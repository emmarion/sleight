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

end FHeap

end Minimal
