import Minimal.Strip

namespace Minimal

def addBody (s p d e : Nat) : Core :=
  .case (.fv p)
    [(1, 1, .vc d 1 .nil,
      .call (.fv s) .none (.ofList [.fv (p + 2), .fv (p + 1)]) false [false, true] (some [false, false, false, true])
        (.chk .rt (.fv (p + 3)) .nil
          (.ret (.ofList [.app (.vc d 1 .nil) (.ofList [.fv (p + 3)]),
            .app (.vc e 1 .nil) (.ofList [.fv (p + 2), .fv (p + 1), .fv (p + 3), .fv (p + 4)])])))),
     (0, 0, .vc d 0 .nil, .ret (.ofList [.fv (p + 1), .app (.vc e 0 .nil) (.ofList [.fv (p + 1)])]))]
    none false false

def addProof (s p d : Nat) : Core → Option Nat
  | .case (.fv p0) [(1, 1, .vc d1 1 .nil, .call (.fv s0) .none args false [false, true] (some [false, false, false, true])
        (.chk .rt q .nil (.ret ts))), (0, 0, .vc d0 0 .nil, .ret ts0)] none false false =>
    match ts0 with
    | .cons b (.cons (.app (.vc e 0 .nil) pb) .nil) =>
      if p0 = p ∧ d1 = d ∧ s0 = s ∧ args = .ofList [.fv (p + 2), .fv (p + 1)] ∧ q = .fv (p + 3) ∧
        ts = .ofList [.app (.vc d 1 .nil) (.ofList [.fv (p + 3)]),
          .app (.vc e 1 .nil) (.ofList [.fv (p + 2), .fv (p + 1), .fv (p + 3), .fv (p + 4)])] ∧
        d0 = d ∧ b = .fv (p + 1) ∧ pb = .ofList [.fv (p + 1)] then some e else none
    | _ => none
  | _ => none

theorem addProof_spec {s p d e : Nat} {c : Core} (h : addProof s p d c = some e) : c = addBody s p d e := by
  unfold addProof at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        rename_i hc; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
        rfl
      · cases h
    · cases h
  · cases h

def FnDef.isAdd (F : FnDef) (s p d : Nat) : Bool :=
  F.np == 2 && F.tele.ers == [false, false, false, true] && F.dele.isNone && (addProof s p d F.body).isSome

def Prog.native (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat a, .nat b] => match P.natD with
    | some d => if P.wrapField d 1 = none ∧ F.isAdd (env.length + j) (env.length + G.fns.length) d = true then
        some [.nat (a + b), .tok] else none
    | none => none
  | _ => none

theorem foldl_snoc (g : List Tm → FnDef → Tm) : ∀ (Fs : List FnDef) (acc : List Tm),
    (Fs.foldl (fun acc F => acc ++ [g acc F]) acc).length = acc.length + Fs.length ∧
    (Fs.foldl (fun acc F => acc ++ [g acc F]) acc).take acc.length = acc ∧
    ∀ i (h : i < Fs.length), (Fs.foldl (fun acc F => acc ++ [g acc F]) acc)[acc.length + i]? =
      some (g ((Fs.foldl (fun acc F => acc ++ [g acc F]) acc).take (acc.length + i)) Fs[i])
  | [], acc => by simp
  | F :: Fs, acc => by
    obtain ⟨h1, h2, h3⟩ := foldl_snoc g Fs (acc ++ [g acc F])
    show (Fs.foldl _ (acc ++ [g acc F])).length = _ ∧ (Fs.foldl _ (acc ++ [g acc F])).take _ = _ ∧
      ∀ i (h : i < (F :: Fs).length), (Fs.foldl _ (acc ++ [g acc F]))[acc.length + i]? =
        some (g ((Fs.foldl _ (acc ++ [g acc F])).take (acc.length + i)) (F :: Fs)[i])
    generalize Fs.foldl (fun acc F => acc ++ [g acc F]) (acc ++ [g acc F]) = R at h1 h2 h3 ⊢
    simp only [List.length_append, List.length_singleton] at h1 h2 h3
    have ht : R.take acc.length = acc := by
      have := congrArg (List.take acc.length) h2
      rwa [List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl] at this
    refine ⟨by simp; omega, ht, fun i hi => ?_⟩
    cases i with
    | zero =>
      have : R[acc.length]? = (R.take (acc.length + 1))[acc.length]? := by rw [List.getElem?_take]; simp
      rw [Nat.add_zero, this, h2, ht]; simp
    | succ i =>
      have := h3 i (by simpa using hi)
      rw [show acc.length + (i + 1) = acc.length + 1 + i by omega, this]; simp

theorem closuresS_length (env : List Tm) (gid : Nat) (G : Group) : (closuresS env gid G).length = G.fns.length := by
  simpa [closuresS] using (foldl_snoc (cval env gid) G.fns []).1

theorem Tm.toList_ofList : ∀ l : List Tm, (Tm.ofList l).toList = l
  | [] => rfl
  | _ :: l => by simp [Tm.ofList, Tm.toList, Tm.toList_ofList l]

theorem RunS.ret' {P : Prog} {ρ out : List Tm} {ts : Tm} (h : out = ts.toList.map (P.sub ρ)) :
    RunS P ρ (.ret ts) out := h ▸ .ret

theorem closuresS_self {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} (hF : G.fns[j]? = some F)
    (hd : F.dele = none) : (closuresS env gid G).getD j .nil = .clo (.ofList env) gid j := by
  have hj : j < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have hFj : G.fns[j] = F := (List.getElem?_eq_some_iff.mp hF).2
  obtain ⟨h1, -, h3⟩ := foldl_snoc (cval env gid) G.fns []
  have := h3 j hj
  simp only [List.length_nil, Nat.zero_add] at this h1
  unfold closuresS
  generalize List.foldl (fun acc F => acc ++ [cval env gid acc F]) [] G.fns = R at h1 this ⊢
  rw [List.getD_eq_getElem?_getD, this]
  simp only [Option.getD_some, cval, hFj, hd, List.length_take]
  congr 1; omega

theorem add_run {P : Prog} {d e gid j : Nat} {G : Group} {F : FnDef} {env : List Tm} (hd : P.natD = some d)
    (hw : P.wrapField d 1 = none) (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (hdl : F.dele = none)
    (hers : F.tele.ers = [false, false, false, true]) (hnp : F.np = 2)
    (hb : F.body = addBody (env.length + j) (env.length + G.fns.length) d e) :
    ∀ a b, ∃ pf, RunS P (env ++ closuresS env gid G ++ [.nat a, .nat b]) F.body [.nat (a + b), pf] := by
  have hcl := closuresS_self (env := env) (gid := gid) hF hdl
  have hL : (env ++ closuresS env gid G).length = env.length + G.fns.length := by simp [closuresS_length]
  have get : ∀ (xs : List Tm) i, Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + G.fns.length + i) = xs.getD i .nil := by
    intro xs i; simp only [Tm.env, List.getD_eq_getElem?_getD]
    rw [← List.append_assoc, List.getElem?_append_right (by omega)]; congr 2; omega
  have get0 : ∀ (xs : List Tm), Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + G.fns.length) = xs.getD 0 .nil := by
    intro xs; simpa using get xs 0
  have hj : j < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have self : ∀ (xs : List Tm), Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + j) = .clo (.ofList env) gid j := by
    intro xs; simp only [Tm.env, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_append_left (by simp [closuresS_length]; omega)]
    simpa [List.getD_eq_getElem?_getD] using hcl
  intro a b
  induction a with
  | zero =>
    refine ⟨P.sub (env ++ closuresS env gid G ++ [.nat 0, .nat b])
      (.app (.vc e 0 .nil) (.ofList [.fv (env.length + G.fns.length + 1)])), ?_⟩
    rw [hb]; unfold addBody
    exact RunS.case (d := d) (c := 0) (ls := .nil) (vs := .nil) (by simp [Prog.sub, Prog.subU, get0, Prog.view, hd]) rfl
      (RunS.ret' (by simp [Tm.ofList, Tm.toList, Prog.sub, Prog.subU, get]))
  | succ k ih =>
    obtain ⟨pf, hk⟩ := ih
    refine ⟨P.sub (env ++ closuresS env gid G ++ [.nat (k + 1), .nat b] ++ [.nat k] ++ [.nat (k + b), .tok])
      (.app (.vc e 1 .nil) (.ofList [.fv (env.length + G.fns.length + 2), .fv (env.length + G.fns.length + 1),
        .fv (env.length + G.fns.length + 3), .fv (env.length + G.fns.length + 4)])), ?_⟩
    rw [hb]; unfold addBody
    refine RunS.case (d := d) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil)
      (by simp [Prog.sub, Prog.subU, get0, Prog.view, hd]) rfl ?_
    refine RunS.call (env := .ofList env) (G := G) (F := F) (outs := [.nat (k + b), pf]) ?_ hG hF ?_ ?_
    · simp [Prog.sub, Prog.subU, self]
    · rw [Tm.toList_ofList]
      have hs : F.spreadIn (some [false, false, false, true])
          (List.map (P.sub (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ ((Tm.nat k).cons Tm.nil).toList))
            (Tm.ofList [Tm.fv (env.length + G.fns.length + 2), Tm.fv (env.length + G.fns.length + 1)]).toList) =
          [.nat k, .nat b] := by
        simp [FnDef.spreadIn, hers, hnp, filt, spread, Tm.ofList, Tm.toList, Prog.sub, Prog.subU, get]
      rw [hs]; exact hk
    · have hso : F.spreadOut (some [false, false, false, true])
          (Tm.ofList [Tm.fv (env.length + G.fns.length + 2), Tm.fv (env.length + G.fns.length + 1)]).toList.length
          [Tm.nat (k + b), pf] = [.nat (k + b), .tok] := by
        simp [FnDef.spreadOut, hers, hnp, filt, spread, Tm.toList_ofList]
      have hpre : ((Tm.nat k).cons Tm.nil).toList = [.nat k] := rfl
      rw [hso, hpre]
      refine RunS.chk (RunS.ret' ?_)
      rw [Tm.toList_ofList]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      have h3 : P.sub (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ [Tm.nat k] ++ [Tm.nat (k + b), Tm.tok])
          (.fv (env.length + G.fns.length + 3)) = .nat (k + b) := by
        simp only [Prog.sub, Prog.subU, List.append_assoc, List.cons_append, List.nil_append]
        rw [get]; rfl
      have h3' : P.subU (Tm.env (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ [Tm.nat k] ++
          [Tm.nat (k + b), Tm.tok])) (.fv (env.length + G.fns.length + 3)) = .nat (k + b) := h3
      simp only [Prog.sub, Prog.subU]
      rw [hw]
      simp only [Tm.ofList, Prog.subUArgs, h3', Tm.subst]
      simp [Prog.norm, hd]; omega

theorem native_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm} {ve : Option (List Bool)} {n : Nat}
    (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (h : P.native env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.native at h
  split at h
  · rename_i a b
    split at h
    · rename_i d hd
      split at h
      · rename_i hc
        obtain ⟨hw, hadd⟩ := hc
        simp only [FnDef.isAdd, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hadd
        obtain ⟨⟨⟨hnp, hers⟩, hdl⟩, e, he⟩ := hadd
        cases h
        obtain ⟨pf, hr⟩ := add_run hd hw hG hF hdl hers hnp (addProof_spec he) a b
        exact ⟨_, hr, by simp [FnDef.spreadOut, hers, hnp, filt]⟩
      · cases h
    · cases h
  · cases h

variable (P : Prog)

def runS : Nat → List Tm → Core → Option (List Tm)
  | 0, _, _ => none
  | fuel + 1, ρ, c => match c with
    | .ret ts => some (ts.toList.map (P.sub ρ))
    | .call _ _ _ true ms _ rest => runS fuel (ρ ++ List.replicate ms.length .tok) rest
    | .call f _ args false _ ve rest => match P.sub ρ f with
      | .clo env gid j => do
        let G ← P.groups[gid]?
        let F ← G.fns[j]?
        let xs := F.spreadIn ve (args.toList.map (P.sub ρ))
        let outs ← (P.native env.toList G j F xs).orElse fun _ => runS fuel (env.toList ++ closuresS env.toList gid G ++ xs) F.body
        runS fuel (ρ ++ F.spreadOut ve args.toList.length outs) rest
      | _ => none
    | .mtch _ R _ _ true rest => runS fuel (ρ ++ List.replicate R.len .tok) rest
    | .mtch s _ brs els false rest => match P.view (P.sub ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        let outs ← runS fuel (ρ ++ pre) body
        runS fuel (ρ ++ outs) rest
      | _ => none
    | .case _ brs els true _ => do
      let (pre, body) ← realBr brs els
      runS fuel (ρ ++ pre) body
    | .case s brs els false true => do
      let (pre, body) ← realBr brs els
      runS fuel (ρ ++ pre.map fun _ => P.sub ρ s) body
    | .case s brs els false false => match P.view (P.sub ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        runS fuel (ρ ++ pre) body
      | _ => none
    | .seq _ body rest => do
      let outs ← runS fuel ρ body
      runS fuel (ρ ++ outs) rest
    | .prim p er rest => runS fuel (ρ ++ [if er then .tok else p.evalS P ρ]) rest
    | .defLvl rest => runS fuel (ρ ++ [.tok]) rest
    | .defFns gid rest => do runS fuel (ρ ++ closuresS ρ gid (← P.groups[gid]?)) rest
    | .chk _ _ _ rest => runS fuel ρ rest
    | .absurd _ | .dead => none

variable {P} in
theorem runS_sound : ∀ fuel ρ c out, runS P fuel ρ c = some out → RunS P ρ c out := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ h; simp [runS] at h
  | succ fuel ih =>
    intro ρ c out h
    unfold runS at h
    split at h
    · cases h; exact .ret
    · exact .callE (ih _ _ _ h)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨G, hG, F, hF, outs, hb, hr⟩ := h
        cases hn : P.native _ G _ F _ with
        | none =>
          rw [hn] at hb
          exact .call ‹_› hG hF (ih _ _ _ hb) (ih _ _ _ hr)
        | some outs' =>
          rw [hn] at hb; cases hb
          obtain ⟨outs2, hb2, hsp⟩ := native_run hG hF hn
          exact .call ‹_› hG hF hb2 (hsp ▸ ih _ _ _ hr)
      · simp at h
    · exact .mtchE (ih _ _ _ h)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨pre, body⟩, hsel, outs, hb, hr⟩ := h
        exact .mtch ‹_› hsel (ih _ _ _ hb) (ih _ _ _ hr)
      · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
      exact .caseE hsel (ih _ _ _ hb)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
      exact .caseN hsel (ih _ _ _ hb)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
        exact .case ‹_› hsel (ih _ _ _ hb)
      · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨outs, hb, hr⟩ := h
      exact .seq (ih _ _ _ hb) (ih _ _ _ hr)
    · exact .prim (ih _ _ _ h)
    · exact .defLvl (ih _ _ _ h)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨G, hG, hr⟩ := h
      exact .defFns hG (ih _ _ _ hr)
    · exact .chk (ih _ _ _ h)
    · simp at h
    · simp at h

end Minimal
