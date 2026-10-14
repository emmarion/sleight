import Minimal.Typing

namespace Minimal

theorem getD_take {bs : List Bool} {n k : Nat} (h : k < n) : (bs.take n).getD k true = bs.getD k true := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem length_spread : ∀ (bs : List Bool) (xs : List Tm), (spread bs xs).length = bs.length
  | [], _ => rfl
  | true :: bs, xs | false :: bs, xs => by simp [spread, length_spread bs]

theorem spread_filt : ∀ (bs : List Bool) (xs : List Tm), bs.length = xs.length → ∀ k, bs.getD k true = false →
    (spread bs (filt bs xs))[k]? = xs[k]?
  | [], _, _, k, h => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | b :: bs, x :: xs, h, k, hk => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    cases b <;> cases k <;> simp_all [spread, filt, spread_filt bs xs h]

theorem env_app_right {ρ vs : List Tm} (i : Nat) : Tm.env (ρ ++ vs) (ρ.length + i) = vs.getD i .nil := by
  simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem env_app_left {ρ vs : List Tm} {i : Nat} (h : i < ρ.length) : Tm.env (ρ ++ vs) i = Tm.env ρ i := by
  simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem spread_get : ∀ (bs : List Bool) (xs : List Tm) (k : Nat), bs.getD k true = false →
    (spread bs xs)[k]? = some (xs.getD (rank bs k) .nil)
  | [], _, k, h => by simp at h
  | true :: bs, xs, 0, h => by simp at h
  | false :: bs, xs, 0, _ => by cases xs <;> simp [spread, rank]
  | true :: bs, xs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    simp [spread, spread_get bs xs k h, rank, List.take_succ_cons]
  | false :: bs, xs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    cases xs <;> simp [spread, spread_get bs _ k h, rank, List.take_succ_cons]

theorem length_filt : ∀ (bs : List Bool) (xs : List Tm), bs.length = xs.length → (filt bs xs).length = bs.count false
  | [], [], _ => rfl
  | b :: bs, x :: xs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    cases b <;> simp [filt, length_filt bs xs h]

theorem filt_map (g : Tm → Tm) : ∀ (bs : List Bool) (xs : List Tm), filt bs (xs.map g) = (filt bs xs).map g
  | [], _ => by cases ‹List Tm› <;> rfl
  | _ :: _, [] => rfl
  | b :: bs, x :: xs => by cases b <;> simp [filt, filt_map g bs xs]

theorem filt_get : ∀ (bs : List Bool) (xs : List Tm) (k : Nat), bs.getD k true = false →
    (filt bs xs)[rank bs k]? = xs[k]?
  | [], _, k, h => by simp at h
  | _ :: _, [], _, _ => by simp [filt]
  | true :: bs, x :: xs, 0, h => by simp at h
  | false :: bs, x :: xs, 0, _ => by simp [filt, rank]
  | true :: bs, x :: xs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    simp [filt, rank, List.take_succ_cons, ← filt_get bs xs k h]
  | false :: bs, x :: xs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    have := filt_get bs xs k h
    simp only [rank] at this
    simp [filt, rank, List.take_succ_cons, this]

theorem rank_lt : ∀ (bs : List Bool) (k : Nat), bs.getD k true = false → rank bs k < bs.count false
  | [], k, h => by simp at h
  | true :: bs, 0, h => by simp at h
  | false :: bs, 0, _ => by simp [rank]
  | true :: bs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    have := rank_lt bs k h; simp only [rank] at this; simp [rank, List.take_succ_cons, this]
  | false :: bs, k + 1, h => by
    simp only [List.getD_cons_succ] at h
    have := rank_lt bs k h; simp only [rank] at this; simp [rank, List.take_succ_cons]; omega

theorem range_getD_eq : ∀ (S : List Tm), (List.range S.length).map (S.getD · .nil) = S := by
  intro S; apply List.ext_getElem <;> simp
  intro i h1 _; simp [List.getElem?_eq_getElem h1]

def WInv (n0 : Nat) (ρ : List Tm) (al : List (Option (Bool × Nat))) (S so : List Tm) : Prop :=
  ρ.length = n0 + al.length ∧
    ∀ idx b r, al[idx]? = some (some (b, r)) → Tm.env ρ (n0 + idx) = (if b then so else S).getD r .nil

theorem WInv.push {n0 : Nat} {ρ vs : List Tm} {al os : List (Option (Bool × Nat))} {S so : List Tm}
    (h : WInv n0 ρ al S so) (hl : vs.length = os.length)
    (hv : ∀ i b r, os[i]? = some (some (b, r)) → vs.getD i .nil = (if b then so else S).getD r .nil) :
    WInv n0 (ρ ++ vs) (al ++ os) S so := by
  refine ⟨by simp [h.1, hl]; omega, fun idx b r he => ?_⟩
  by_cases hi : idx < al.length
  · rw [List.getElem?_append_left hi] at he
    rw [env_app_left (by rw [h.1]; omega)]; exact h.2 idx b r he
  · rw [List.getElem?_append_right (by omega)] at he
    have := env_app_right (ρ := ρ) (vs := vs) (idx - al.length)
    rw [h.1, show n0 + al.length + (idx - al.length) = n0 + idx by omega] at this
    rw [this]; exact hv _ b r he

theorem resolve_spec (P : Prog) {n0 : Nat} {ρ : List Tm} {al : List (Option (Bool × Nat))} {S so : List Tm}
    (h : WInv n0 ρ al S so) {x : Tm} {b : Bool} {r : Nat} (hx : resolve n0 al x = some (b, r)) :
    P.sub ρ x = (if b then so else S).getD r .nil := by
  cases x with
  | fv i =>
    simp only [resolve] at hx
    split at hx
    · have := h.2 (i - n0) b r (by
        cases hh : al[i - n0]? with
        | none => simp [hh] at hx
        | some o => simp [hh] at hx; simp [hx])
      rw [show n0 + (i - n0) = i by omega] at this
      simpa [Prog.sub, Prog.subU] using this
    · cases hx
  | _ => simp [resolve] at hx

theorem symSpread_get {o : Bool} {bs : List Bool} {i : Nat} {b : Bool} {r : Nat}
    (h : (symSpread o bs)[i]? = some (some (b, r))) : bs.getD i true = false ∧ b = o ∧ r = rank bs i := by
  simp only [symSpread, List.getElem?_map] at h
  rcases Nat.lt_or_ge i bs.length with hi | hi
  · rw [List.getElem?_range hi] at h
    simp only [Option.map_some, Option.some.injEq] at h
    split at h
    · cases h
    · rename_i hb; simp at h; exact ⟨by simpa using hb, h.1.symm, h.2.symm⟩
  · have : (List.range bs.length)[i]? = none := List.getElem?_eq_none (by simpa using hi)
    simp [this] at h

theorem WInv.init {n0 : Nat} {E : List Tm} (hE : E.length = n0) (pe : List Bool) (S so : List Tm) :
    WInv n0 (E ++ spread pe S) (symSpread false pe) S so := by
  refine ⟨by simp [hE, length_spread, symSpread], fun idx b r he => ?_⟩
  obtain ⟨h1, rfl, rfl⟩ := symSpread_get he
  rw [← hE, env_app_right, List.getD_eq_getElem?_getD, spread_get _ _ _ h1]; rfl

variable {P : Prog}

theorem prim_resolve {n0 : Nat} {ρ : List Tm} {al : List (Option (Bool × Nat))} {S so : List Tm}
    (h : WInv n0 ρ al S so) (p : Prim) (er : Bool) :
    WInv n0 (ρ ++ [if er then .tok else p.evalS P ρ]) (al ++ [if er then none else match p with
      | .tm x | .coerce x _ _ => resolve n0 al x
      | _ => none]) S so := by
  refine h.push (by simp) fun i b r he => ?_
  cases i with
  | succ => simp at he
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    cases er with
    | true => cases he
    | false =>
      simp only [Bool.false_eq_true, if_false] at he ⊢
      cases p <;> simp at he ⊢ <;> simp only [Prim.evalS] <;> exact resolve_spec P h he

theorem WInv.toks {n0 : Nat} {ρ : List Tm} {al : List (Option (Bool × Nat))} {S so : List Tm}
    (h : WInv n0 ρ al S so) (m : Nat) :
    WInv n0 (ρ ++ List.replicate m .tok) (al ++ List.replicate m none) S so :=
  h.push (by simp) fun i b r he => by simp [List.getElem?_replicate] at he

theorem walk2 {t n0 cnt : Nat} {re : List Bool} {S so : List Tm} :
    ∀ {ρ c out}, RunS P ρ c out → ∀ al, delegWalk P t n0 cnt re true al c = true → WInv n0 ρ al S so →
      ∀ k, re.getD k true = false → out.getD k .nil = so.getD (rank re k) .nil := by
  intro ρ c out h
  induction h with
  | @ret ρ ts =>
    intro al hw hI k hk
    simp only [delegWalk, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨hlen, -⟩, heq⟩ := hw
    have hkl : k < re.length := by
      rcases Nat.lt_or_ge k re.length with h | h
      · exact h
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hk
    have hx := filt_get re ts.toList k hk
    obtain ⟨x, hx'⟩ : ∃ x, ts.toList[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hkl)⟩
    rw [hx'] at hx
    have := congrArg (·[rank re k]?) heq
    simp only [List.getElem?_map, hx, Option.map_some, List.getElem?_range (rank_lt re k hk)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx']
    simpa using resolve_spec P hI (Option.some.inj this)
  | callE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw (hI.toks _)
  | mtchE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw (hI.toks _)
  | prim _ ih => intro al hw hI; unfold delegWalk at hw; exact ih _ (Bool.and_eq_true _ _ ▸ hw).2 (prim_resolve hI _ _)
  | defLvl _ ih =>
    intro al hw hI; simp only [delegWalk] at hw
    exact ih _ hw (hI.push (by simp) fun i b r he => by cases i <;> simp at he)
  | chk _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | defFns hG _ ih =>
    intro al hw hI; simp only [delegWalk, hG] at hw
    exact ih _ hw (hI.push (by simp [closuresS_length]) fun i b r he => by simp [List.getElem?_replicate] at he)
  | caseE hsel _ ih =>
    intro al hw hI; rw [delegWalk] at hw; split at hw
    · rename_i hsel'; rw [hsel] at hsel'; cases hsel'
      exact ih _ hw (hI.push (by simp) fun i b r he => by simp at he)
    · cases hw
  | _ => intro al hw; simp [delegWalk] at hw

theorem WInv.spreadOut {n0 : Nat} {ρ : List Tm} {al : List (Option (Bool × Nat))} {S so : List Tm}
    (h : WInv n0 ρ al S so) (bs : List Bool) :
    WInv n0 (ρ ++ spread bs so) (al ++ symSpread true bs) S so :=
  h.push (by simp [length_spread, symSpread]) fun i b r he => by
    obtain ⟨h1, rfl, rfl⟩ := symSpread_get he
    rw [List.getD_eq_getElem?_getD, spread_get _ _ _ h1]; rfl

theorem walk1_tr {t n0 : Nat} {re : List Bool} {S out ρ vs : List Tm} {al : List (Option (Bool × Nat))}
    (ht : t < n0) (hI : ∀ so, WInv n0 ρ al S so) :
    (∃ env gid j G F outs, Tm.env (ρ ++ vs) t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
      RunS P (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) F.body outs ∧
      ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil) →
    ∃ env gid j G F outs, Tm.env ρ t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
      RunS P (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) F.body outs ∧
      ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil :=
  fun ⟨e, g, j, G, F, o, h1, h2⟩ =>
    ⟨e, g, j, G, F, o, by rw [← env_app_left (vs := vs) (by rw [(hI []).1]; omega)]; exact h1, h2⟩

theorem walk1 {t n0 cnt : Nat} {re : List Bool} {S : List Tm} (hS : S.length = cnt) (ht : t < n0) :
    ∀ {ρ c out}, RunS P ρ c out → ∀ al, delegWalk P t n0 cnt re false al c = true → (∀ so, WInv n0 ρ al S so) →
      ∃ env gid j G F outs, Tm.env ρ t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
        RunS P (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) F.body outs ∧
        ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil := by
  intro ρ c out h
  induction h with
  | @call ρ f env gid j G F ve outs rest out dec args ms hf hG hF hb hr _ _ =>
    intro al hw hI
    cases ve with
    | none => simp [delegWalk] at hw
    | some ve =>
    simp only [delegWalk, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨⟨rfl, -⟩, hargs⟩, hw⟩ := hw
    refine ⟨env, gid, j, G, F, outs, by simpa [Prog.sub, Prog.subU] using hf, hG, hF, ?_, ?_⟩
    · have hl := congrArg List.length hargs
      simp only [List.length_map, List.length_range] at hl
      have : (filt (ve.take args.toList.length) args.toList).map (P.sub ρ) = S := by
        apply List.ext_getElem (by simp [hl, hS])
        intro i h1 h2
        have := congrArg (·[i]?) hargs
        simp only [List.getElem?_map, List.getElem?_range (show i < cnt by simpa [hl] using h1),
          List.getElem?_eq_getElem (show i < (filt (ve.take args.toList.length) args.toList).length by simpa using h1),
          Option.map_some, Option.some.injEq] at this
        simpa [List.getElem?_eq_getElem h2] using resolve_spec P (hI []) this
      simpa [FnDef.spreadIn, filt_map, this] using hb
    · exact walk2 (by simpa [FnDef.spreadOut] using hr) _ hw ((hI _).spreadOut _)
  | callE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact walk1_tr ht hI (ih _ hw fun so => (hI so).toks _)
  | mtchE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact walk1_tr ht hI (ih _ hw fun so => (hI so).toks _)
  | prim _ ih =>
    intro al hw hI; unfold delegWalk at hw
    exact walk1_tr ht hI (ih _ (Bool.and_eq_true _ _ ▸ hw).2 fun so => prim_resolve (hI so) _ _)
  | defLvl _ ih =>
    intro al hw hI; simp only [delegWalk] at hw
    exact walk1_tr ht hI (ih _ hw fun so => (hI so).push (by simp) fun i b r he => by cases i <;> simp at he)
  | chk _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | defFns hG _ ih =>
    intro al hw hI; simp only [delegWalk, hG] at hw
    exact walk1_tr ht hI (ih _ hw fun so => (hI so).push (by simp [closuresS_length]) fun i b r he => by
      simp [List.getElem?_replicate] at he)
  | caseE hsel _ ih =>
    intro al hw hI; rw [delegWalk] at hw; split at hw
    · rename_i hsel'; rw [hsel] at hsel'; cases hsel'
      exact walk1_tr ht hI (ih _ hw fun so => (hI so).push (by simp) fun i b r he => by simp at he)
    · cases hw
  | _ => intro al hw; simp [delegWalk] at hw

end Minimal
