import Minimal.MachineRun

namespace Minimal

variable {P : Prog}

def Tm.flat : Tm → Bool
  | .fv _ | .tok => true
  | _ => false

theorem build_flat {H : Heap} {f : Nat → Tm} {x : Tm} (h : x.flat = true) : P.build H f x = (H, P.subU f x) := by
  cases x <;> simp [Tm.flat] at h <;> simp [Prog.build, Prog.subU, Tm.subst]

theorem buildList_flat {H : Heap} {f : Nat → Tm} : ∀ {ts : List Tm}, (∀ x ∈ ts, x.flat = true) →
    P.buildList H f ts = (H, ts.map (P.subU f))
  | [], _ => rfl
  | x :: ts, h => by
    have h1 := build_flat (P := P) (H := H) (f := f) (h x (by simp))
    have h2 : P.buildList H f ts = (H, ts.map (P.subU f)) := buildList_flat fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [Prog.buildList, h1, h2, List.map_cons]

theorem evalP_other {H : Heap} {ρ : List Tm} {pd : Pend} {p : Prim} (h1 : ∀ t, p ≠ .tm t) (h2 : ∀ A, p ≠ .axm A) :
    P.evalP H ρ pd p = P.evalM H ρ p := by
  unfold Prog.evalP; split
  · exact absurd rfl (h1 _)
  · exact absurd rfl (h2 _)
  · exact absurd rfl (h2 _)
  · exact absurd rfl (h2 _)
  · rfl

theorem evalP_inert {H : Heap} {ρ : List Tm} {pd : Pend} {p : Prim} {er : Bool} (hi : (er || p.inert) = true) :
    (if er then (H, Tm.tok) else P.evalP H ρ pd p) = (H, if er then .tok else p.evalS P ρ) := by
  cases er with
  | true => rfl
  | false =>
    simp only [Bool.false_or] at hi
    simp only [Bool.false_eq_true, ite_false]
    have hM : P.evalM H ρ p = (H, p.evalS P ρ) := by
      cases p with
      | tm t => cases t <;> simp [Prim.inert] at hi; simp [Prog.evalM, Prog.build, Prim.evalS, Prog.sub, Prog.subU]
      | coerce t b q => cases t <;> simp [Prim.inert] at hi; simp [Prog.evalM, Prog.build, Prim.evalS, Prog.sub, Prog.subU]
      | place t T => cases t <;> simp [Prim.inert] at hi; simp [Prog.evalM, Prog.build, Prim.evalS, Prog.sub, Prog.subU]
      | unplace t v => cases t <;> simp [Prim.inert] at hi; simp [Prog.evalM, Prog.build, Prim.evalS, Prog.sub, Prog.subU]
      | lit t => simp [Prim.inert] at hi
      | axm A => simp [Prim.inert] at hi
      | _ => rfl
    rcases pd with _ | ⟨m, a⟩
    · exact hM
    · cases p
      case tm x =>
        cases x <;> simp [Prim.inert] at hi
        cases m <;> (try rename_i bb; cases bb) <;> cases a <;>
          simp [Prog.evalP, Prog.reuse, Prog.build, Prim.evalS, Prog.sub, Prog.subU] <;>
          simpa [Prim.evalS, Prog.sub, Prog.subU] using hM
      case lit => simp [Prim.inert] at hi
      case axm => simp [Prim.inert] at hi
      all_goals (rw [evalP_other (fun _ h => by cases h) (fun _ h => by cases h)]; exact hM)


theorem spread_tok : ∀ (bs : List Bool) (xs : List Tm) (k : Nat), k < bs.length → bs.getD k true = true →
    (spread bs xs)[k]? = some .tok
  | [], _, k, h, _ => by simp at h
  | true :: bs, xs, 0, _, _ => by simp [spread]
  | false :: bs, xs, 0, _, h => by simp at h
  | true :: bs, xs, k + 1, h, h' => by simpa [spread] using spread_tok bs xs k (by simpa using h) (by simpa using h')
  | false :: bs, xs, k + 1, h, h' => by simpa [spread] using spread_tok bs xs.tail k (by simpa using h) (by simpa using h')

theorem filt_mask : ∀ (es : List Bool) (args : Tm) (n : Nat),
    filt (es.take n) (maskArgs es args).toList = filt (es.take n) args.toList
  | [], _, n => by simp [maskArgs]
  | e :: es, .cons a as, 0 => by simp [filt]
  | e :: es, .cons a as, n + 1 => by cases e <;> simp [maskArgs, Tm.toList, filt, filt_mask es as n]
  | _ :: _, .nil, _ | _ :: _, .fv _, _ | _ :: _, .bv _, _ | _ :: _, .univ, _ | _ :: _, .level, _
  | _ :: _, .tyc .., _ | _ :: _, .vc .., _ | _ :: _, .app .., _ | _ :: _, .bind .., _
  | _ :: _, .tyCtor _, _ | _ :: _, .valCtor _, _ | _ :: _, .predates .., _ | _ :: _, .subterm .., _
  | _ :: _, .fn .., _ | _ :: _, .mtbl .., _ | _ :: _, .lvl _, _ | _ :: _, .tok, _ | _ :: _, .clo .., _
  | _ :: _, .nat _, _ | _ :: _, .ptr _, _ => by simp [maskArgs]

theorem resolve_fv {n0 : Nat} {al : List (Option (Bool × Nat))} {x : Tm} {b : Bool} {r : Nat}
    (h : resolve n0 al x = some (b, r)) : x.flat = true := by
  cases x <;> simp [resolve, Tm.flat] at h ⊢

theorem walkM2 {t n0 cnt : Nat} {re : List Bool} {S so : List Tm} :
    ∀ {H ρ pd c H' out}, RunM P H ρ pd c H' out → ∀ al, delegWalk P t n0 cnt re true al c = true →
      WInv n0 ρ al S so → H' = H ∧ ∀ k, re.getD k true = false → out.getD k .nil = so.getD (rank re k) .nil := by
  intro H ρ pd c H' out h
  induction h with
  | @ret H ρ ts H' vs pd hb =>
    intro al hw hI
    have hw0 := hw
    simp only [delegWalk, Bool.and_eq_true, List.all_eq_true] at hw
    rw [buildList_flat fun x hx => by have := hw.1.2 x hx; cases x <;> simp_all [Tm.flat]] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb
    exact ⟨rfl, walk2 (P := P) RunS.ret al hw0 hI⟩
  | callE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw (hI.toks _)
  | mtchE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw (hI.toks _)
  | prim hev _ ih =>
    intro al hw hI; unfold delegWalk at hw
    obtain ⟨hi, hw⟩ := (Bool.and_eq_true _ _).mp hw
    rw [evalP_inert hi] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact ih _ hw (prim_resolve hI _ _)
  | defLvl _ ih =>
    intro al hw hI; simp only [delegWalk] at hw
    exact ih _ hw (hI.push (by simp) fun i b r he => by cases i <;> simp at he)
  | mark _ _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | chk _ _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | defFns hG _ ih =>
    intro al hw hI; simp only [delegWalk, hG] at hw
    exact ih _ hw (hI.push (by simp [closuresS_length]) fun i b r he => by simp [List.getElem?_replicate] at he)
  | caseE hsel _ ih =>
    intro al hw hI; rw [delegWalk] at hw; split at hw
    · rename_i hsel'; rw [hsel] at hsel'; cases hsel'
      exact ih _ hw (hI.push (by simp) fun i b r he => by simp at he)
    · cases hw
  | _ => intro al hw; simp [delegWalk] at hw


theorem mem_mask : ∀ (es : List Bool) (args : Tm) {x : Tm}, x ∈ (maskArgs es args).toList →
    args.toList.length ≤ es.length → x = .tok ∨ x ∈ filt (es.take args.toList.length) args.toList
  | [], args, x, hx, hl => by
    cases h : args.toList with
    | nil => simp [maskArgs, h] at hx
    | cons a as => rw [h] at hl; simp at hl
  | e :: es, .cons a as, x, hx, hl => by
    simp only [maskArgs, Tm.toList, List.mem_cons, List.length_cons, List.take_succ_cons] at hx hl ⊢
    rcases hx with rfl | hx
    · cases e <;> simp [filt]
    · rcases mem_mask es as hx (by omega) with h | h
      · exact .inl h
      · cases e <;> simp [filt, h]
  | _ :: _, .nil, _, hx, _ | _ :: _, .fv _, _, hx, _ | _ :: _, .bv _, _, hx, _ | _ :: _, .univ, _, hx, _
  | _ :: _, .level, _, hx, _ | _ :: _, .tyc .., _, hx, _ | _ :: _, .vc .., _, hx, _ | _ :: _, .app .., _, hx, _
  | _ :: _, .bind .., _, hx, _ | _ :: _, .tyCtor _, _, hx, _ | _ :: _, .valCtor _, _, hx, _
  | _ :: _, .predates .., _, hx, _ | _ :: _, .subterm .., _, hx, _ | _ :: _, .fn .., _, hx, _
  | _ :: _, .mtbl .., _, hx, _ | _ :: _, .lvl _, _, hx, _ | _ :: _, .tok, _, hx, _ | _ :: _, .clo .., _, hx, _
  | _ :: _, .nat _, _, hx, _ | _ :: _, .ptr _, _, hx, _ => by simp [maskArgs, Tm.toList] at hx

theorem walkM1_tr {t n0 : Nat} {re : List Bool} {S out ρ vs : List Tm} {al : List (Option (Bool × Nat))} {H H' : Heap}
    (ht : t < n0) (hI : ∀ so, WInv n0 ρ al S so) :
    (∃ env gid j G F outs, Tm.env (ρ ++ vs) t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
      RunM P H (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) none F.body H' outs ∧
      ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil) →
    ∃ env gid j G F outs, Tm.env ρ t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
      RunM P H (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) none F.body H' outs ∧
      ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil :=
  fun ⟨e, g, j, G, F, o, h1, h2⟩ =>
    ⟨e, g, j, G, F, o, by rw [← env_app_left (vs := vs) (by rw [(hI []).1]; omega)]; exact h1, h2⟩

theorem walkM1 {t n0 cnt : Nat} {re : List Bool} {S : List Tm} (hS : S.length = cnt) (ht : t < n0) :
    ∀ {H ρ pd c H' out}, RunM P H ρ pd c H' out → ∀ al, delegWalk P t n0 cnt re false al c = true →
      (∀ so, WInv n0 ρ al S so) →
      ∃ env gid j G F outs, Tm.env ρ t = .clo env gid j ∧ P.groups[gid]? = some G ∧ G.fns[j]? = some F ∧
        RunM P H (env.toList ++ closuresS env.toList gid G ++ spread (F.tele.ers.take F.np) S) none F.body H' outs ∧
        ∀ k, re.getD k true = false → out.getD k .nil = (filt (F.tele.ers.drop F.np) outs).getD (rank re k) .nil := by
  intro H ρ pd c H' out h
  induction h with
  | @call ρ f env gid j G F H args H1 as ve H2 outs rest H' out pd dec ms hf hG hF hbl hb hr _ _ =>
    intro al hw hI
    cases ve with
    | none => simp [delegWalk] at hw
    | some ve =>
    simp only [delegWalk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨rfl, hle⟩, hargs⟩, hw⟩ := hw
    have hflat : ∀ x ∈ (maskArgs ve args).toList, x.flat = true := by
      intro x hx
      rcases mem_mask ve args hx hle with rfl | hx
      · rfl
      · have := List.mem_map_of_mem (f := resolve n0 al) hx
        rw [hargs] at this
        simp only [List.mem_map, List.mem_range] at this
        obtain ⟨r, -, hr⟩ := this
        exact resolve_fv hr.symm
    simp only [Option.getD_some] at hbl
    rw [buildList_flat hflat] at hbl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbl
    have hl := congrArg List.length hargs
    simp only [List.length_map, List.length_range] at hl
    have hSeq : (filt (ve.take args.toList.length) args.toList).map (P.sub ρ) = S := by
      apply List.ext_getElem (by simp [hl, hS])
      intro i h1 h2
      have := congrArg (·[i]?) hargs
      simp only [List.getElem?_map, List.getElem?_range (show i < cnt by simpa [hl] using h1),
        List.getElem?_eq_getElem (show i < (filt (ve.take args.toList.length) args.toList).length by simpa using h1),
        Option.map_some, Option.some.injEq] at this
      simpa [List.getElem?_eq_getElem h2] using resolve_spec P (hI []) this
    obtain ⟨rfl, hres⟩ := walkM2 (by simpa [FnDef.spreadOut] using hr) _ hw ((hI _).spreadOut _)
    refine ⟨env, gid, j, G, F, outs, by simpa [Prog.sub, Prog.subU] using hf, hG, hF, ?_, hres⟩
    have : F.spreadIn (some ve) ((maskArgs ve args).toList.map (P.subU (Tm.env ρ))) =
        spread (F.tele.ers.take F.np) S := by
      simp only [FnDef.spreadIn, Option.getD_some, List.length_map, mask_length, filt_map, filt_mask]
      rw [← hSeq]; rfl
    rw [← this]; exact hb
  | callE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact walkM1_tr ht hI (ih _ hw fun so => (hI so).toks _)
  | mtchE _ ih => intro al hw hI; simp only [delegWalk] at hw; exact walkM1_tr ht hI (ih _ hw fun so => (hI so).toks _)
  | prim hev _ ih =>
    intro al hw hI; unfold delegWalk at hw
    obtain ⟨hi, hw⟩ := (Bool.and_eq_true _ _).mp hw
    rw [evalP_inert hi] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact walkM1_tr ht hI (ih _ hw fun so => prim_resolve (hI so) _ _)
  | defLvl _ ih =>
    intro al hw hI; simp only [delegWalk] at hw
    exact walkM1_tr ht hI (ih _ hw fun so => (hI so).push (by simp) fun i b r he => by cases i <;> simp at he)
  | mark _ _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | chk _ _ ih => intro al hw hI; simp only [delegWalk] at hw; exact ih _ hw hI
  | defFns hG _ ih =>
    intro al hw hI; simp only [delegWalk, hG] at hw
    exact walkM1_tr ht hI (ih _ hw fun so => (hI so).push (by simp [closuresS_length]) fun i b r he => by
      simp [List.getElem?_replicate] at he)
  | caseE hsel _ ih =>
    intro al hw hI; rw [delegWalk] at hw; split at hw
    · rename_i hsel'; rw [hsel] at hsel'; cases hsel'
      exact walkM1_tr ht hI (ih _ hw fun so => (hI so).push (by simp) fun i b r he => by simp at he)
    · cases hw
  | _ => intro al hw; simp [delegWalk] at hw


theorem WO.dele_inv {H : Heap} {w u : Tm} {envF : List Tm} {gid j t : Nat} {G : Group} {F : FnDef}
    (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (hd : F.dele = some t) (hu : F.u = true)
    (h : WO P H w u (.clo (.ofList envF) gid j)) : WO P H w u (Tm.env (envF ++ closures envF gid G) t) := by
  cases h with
  | clo hn => rw [hn G F hG hF] at hd; cases hd
  | dele hG' hF' hd' _ h =>
    rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'; rw [hd] at hd'; cases hd'
    simpa [Tm.toList_ofList] using h
  | free hn => exact .free fun b h => hn b (.dele hG hF hd hu (by simpa [Tm.toList_ofList] using h))

theorem dele_body (hP : ProgOK P) {G : UCtx} {ρ ρS ρM : List Tm} {fi : Nat} {args t : Tm} {uf : Bool}
    {A B AB : Uses} (hE : EnvOK P ρ G.Γ) (hS : SimEnv P G.Γ.er ρS ρ) (hrta : rtArgs P G.Γ args t = true)
    (hA : G.termUses P uf (.fv fi) = some A) (hB : G.argsUses P (·.u) args t = some B) (hAB : Uses.seq A B = some AB)
    {envS : Tm} {gid' j' : Nat} {Gr' : Group} {F' : FnDef} (hfS : P.sub ρS (.fv fi) = .clo envS gid' j')
    (hGr' : P.groups[gid']? = some Gr') (hF' : Gr'.fns[j']? = some F')
    {envF : List Tm} {gid j tg : Nat} {Gr : Group} {F : FnDef} (hfF : Tm.env ρ fi = .clo (.ofList envF) gid j)
    (hGr : P.groups[gid]? = some Gr) (hF : Gr.fns[j]? = some F) (hdt : F.dele = some tg) (hFu : F.u = uf)
    (htg : tg < envF.length + Gr.fns.length)
    (hwalk : delegWalk P tg (envF.length + Gr.fns.length) ((F.tele.ers.take F.np).count false) (F.tele.ers.drop F.np)
      false (symSpread false (F.tele.ers.take F.np)) F.body = true)
    (hpe : F.tele.ers.take F.np = t.ers.take args.toList.length) (htl : args.toList.length ≤ t.ers.length)
    (hre : F.tele.ers.drop F.np = t.ers.drop args.toList.length)
    {ve : Option (List Bool)} (hve : ve = some t.ers) {Gb : UCtx} {rub : List Bool} {Rb : Tm} {Ub : Uses} {Kb : Caps}
    (hUb : usesCore P gid Gb rub Rb F.body = some (Ub, Kb))
    (hGn : Gb.Γ.n = envF.length + Gr.fns.length + args.toList.length)
    (hGok : ∀ H ρM ρS ρ Shr, GOK P Gb none H ρM ρS ρ (fun _ => False) Shr)
    (herb : ∀ i < envF.length + Gr.fns.length, i ≠ tg → Gb.Γ.er i = true)
    (hUt : Ub.lookup tg = some true → Gb.Γ.er tg = false → uf = true)
    (hpU : ∀ k < args.toList.length, Ub.lookup (envF.length + Gr.fns.length + k) = some true →
      Gb.Γ.er (envF.length + Gr.fns.length + k) = false → (t.kinds.map (·.u)).getD k false = true)
    (hsprI : ∀ xs : List Tm, xs.length = args.toList.length → (F.spreadIn ve xs).length = args.toList.length ∧
      ∀ k, k < args.toList.length → Gb.Γ.er (envF.length + Gr.fns.length + k) = false →
        t.ers.getD k true = false ∧ (F.spreadIn ve xs)[k]? = xs[k]?)
    (hRbe : Rb.ers = t.ers.drop args.toList.length)
    {ruC : List Bool} {m : Nat}
    (hru : ∀ k, ruC.getD k false = true → Rb.ers.getD k true = false → rub.getD k false = true)
    {outsFb outsSb' outsSb : List Tm}
    (hbody : MRun P gid Gb rub Rb F.body (envF ++ closures envF gid Gr ++ args.toList.map (·.subst (Tm.env ρ))) outsFb)
    (hsimb : SimEnv P Gb.Γ.er ((List.replicate (envF.length + Gr.fns.length) .tok).set tg (P.sub ρS (.fv fi)) ++
      F.spreadIn ve (args.toList.map (P.sub ρS))) (envF ++ closures envF gid Gr ++ args.toList.map (·.subst (Tm.env ρ))))
    (hrunSb : RunS P ((List.replicate (envF.length + Gr.fns.length) .tok).set tg (P.sub ρS (.fv fi)) ++
      F.spreadIn ve (args.toList.map (P.sub ρS))) F.body outsSb')
    (hrunS : RunS P (envS.toList ++ closuresS envS.toList gid' Gr' ++ F'.spreadIn ve (args.toList.map (P.sub ρS)))
      F'.body outsSb)
    (hlS : outsSb'.length = Rb.ers.length)
    {H : Heap} {Out' Shr : Nat → Prop} (hM : MFrame P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Out' Shr) :
    ∃ envM H1 as H2 outsMb, P.subU (Tm.env ρM) (.fv fi) = .clo envM gid' j' ∧
      P.buildList H (Tm.env ρM) (maskArgs (ve.getD []) args).toList = (H1, as) ∧
      RunM P H1 (envM.toList ++ closuresS envM.toList gid' Gr' ++ F'.spreadIn ve as) none F'.body H2 outsMb ∧
      MOut P AB G.Γ.n G.Γ.er H ρM ρS ρ (fun _ => False) Shr (plainTele m) ruC H2
        (F'.spreadOut ve args.toList.length outsMb) (F'.spreadOut ve args.toList.length outsSb) outsFb := by
  subst hve
  simp only [UCtx.termUses, UCtx.use] at hA
  split at hA
  · cases hA
  rename_i hc
  simp only [Option.some.injEq] at hA; subst hA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hc
  have hfi : fi < G.Γ.n := by omega
  have hfe : G.Γ.er fi = false := by simpa using hc.1.2
  obtain ⟨sA, sB⟩ := Uses.seq_sub hAB
  have hfree := (Uses.seq_spec hAB).1
  have hAfi : [(fi, uf)].lookup fi = some uf := by simp [List.lookup]
  have hfU : (AB.lookup fi).isSome := sA.1 fi (by simp [hAfi])
  have hfB : B.lookup fi ≠ some true := fun h => by have := (hfree fi).2 h; rw [hAfi] at this; cases this
  have hfB' : AB.lookup fi = some true → B.lookup fi = none := fun h => by
    cases uf
    · cases hb : B.lookup fi with
      | none => rfl
      | some v =>
        cases v
        · rw [(Uses.seq_spec hAB).2 fi, hAfi, hb] at h; simp [Uses.merge] at h
        · exact absurd hb hfB
    · exact (hfree fi).1 hAfi
  have hABu : uf = true → AB.lookup fi = some true := fun hu => sA.2 fi (by simp [hAfi, hu])
  have hfd := hM.dec fi hfi hfU hfe
  have hfS' : Tm.env ρS fi = .clo envS gid' j' := by simpa [Prog.sub, Prog.subU] using hfS
  rw [hfS'] at hfd
  obtain ⟨lM, lS, hfM, rfl, -, -⟩ := MDec.clo_inv' hfd
  obtain ⟨H1, as, hbl, hOa⟩ := args_val hP hE hS hrta hB (hM.subB (sB.subB _))
  have hlas : as.length = args.toList.length := by
    have := (buildList_ext (P := P) hM.wf (Tm.env ρM) (maskArgs t.ers args).toList).2.2
    rw [hbl, mask_length] at this; exact this
  obtain ⟨hlI, hkI⟩ := hsprI as hlas
  obtain ⟨hlIS, hkIS⟩ := hsprI (args.toList.map (P.sub ρS)) (by simp)
  have hnm : envF.length + Gr.fns.length + (args.toList.map (·.subst (Tm.env ρ))).length = Gb.Γ.n := by simp [hGn]
  have eT : ∀ (w : Tm), Tm.env ((List.replicate (envF.length + Gr.fns.length) Tm.tok).set tg w) tg = w := fun w => by
    simp [Tm.env, List.getD_eq_getElem?_getD, htg]
  have eO : ∀ (w : Tm) z, z < envF.length + Gr.fns.length → z ≠ tg →
      Tm.env ((List.replicate (envF.length + Gr.fns.length) Tm.tok).set tg w) z = .tok := fun w z hz hne => by
    simp [Tm.env, List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hne, hz]
  have hEq : ∀ z, z < envF.length + Gr.fns.length → (Ub.lookup z).isSome → Gb.Γ.er z = false → z = tg :=
    fun z hz _ he => by
      by_cases hne : z = tg
      · exact hne
      · rw [herb z hz hne] at he; cases he
  obtain ⟨hMb, hown, hlive⟩ := body_frame hM sB hfi hfe hfU hfB hfB'
    (cM := (List.replicate (envF.length + Gr.fns.length) Tm.tok).set tg (Tm.env ρM fi))
    (cS := (List.replicate (envF.length + Gr.fns.length) Tm.tok).set tg (Tm.env ρS fi))
    (cF := envF ++ closures envF gid Gr) (by simp) (by simp) (by simp [closures]) hOa
    (pM := F.spreadIn (some t.ers) as) (pS := F.spreadIn (some t.ers) (args.toList.map (P.sub ρS))) (Ub := Ub)
    (erb := Gb.Γ.er) (by simp [hlI]) (by simp [hlIS])
    (fun k hk he => by
      have hk' : k < args.toList.length := by simpa using hk
      have h1 := hkI k hk' he
      have h2 := hkIS k hk' he
      refine ⟨h1.1, h1.2, h2.2, ?_, ?_⟩
      · rw [get_getD (by omega)]; rfl
      · rw [get_getD (by simpa using hk')]; rfl)
    (fun z hz hU he => by
      obtain rfl := hEq z hz hU he
      rw [eT, eT]; exact ⟨hM.dec fi hfi hfU hfe, fun b hb => hb⟩)
    (fun z hz hU he => by
      obtain rfl := hEq z hz (by simp [hU]) he
      have hu := hUt hU he
      have hAB := hABu hu
      have hwo := hM.wo fi hfi hAB hfe
      rw [hfF] at hwo
      rw [eT, eT]
      refine ⟨hAB, WO.dele_inv hGr hF hdt (by rw [hFu, hu]) hwo, fun b hb => ?_⟩
      rw [hfF]; exact .dele hGr hF hdt (by rw [hFu, hu]) (by simpa [Tm.toList_ofList] using hb))
    (fun z hz z' hz' hne hU hU' he he' => by
      obtain rfl := hEq z hz (by simp [hU]) he
      obtain rfl := hEq z' hz' hU' he'
      exact absurd rfl hne)
    (fun k hk hU he => hpU k (by simpa using hk) hU he)
  rw [hnm] at hMb hown hlive
  have hfS'' : P.sub ρS (.fv fi) = Tm.env ρS fi := by simp [Prog.sub, Prog.subU]
  rw [hfS''] at hsimb hrunSb
  obtain ⟨H2, vsM, hrb, hOb⟩ := hbody Ub Kb hUb _ outsSb' hsimb hrunSb H1 _ _ Out' Shr none hMb (hGok _ _ _ _ _)
  have hlen : (filt (t.ers.take args.toList.length) as).length = (F.tele.ers.take F.np).count false := by
    rw [hpe, length_filt _ _ (by simp [hlas]; omega)]
  have hspI : ∀ xs : List Tm, xs.length = args.toList.length →
      F.spreadIn (some t.ers) xs = spread (F.tele.ers.take F.np) (filt (t.ers.take args.toList.length) xs) :=
    fun xs hx => by simp [FnDef.spreadIn, hx]
  have hspI' : ∀ xs : List Tm, xs.length = args.toList.length →
      F'.spreadIn (some t.ers) xs = spread (F'.tele.ers.take F'.np) (filt (t.ers.take args.toList.length) xs) :=
    fun xs hx => by simp [FnDef.spreadIn, hx]
  rw [hspI as hlas] at hrb
  obtain ⟨env', gid'', j'', G'', F'', outs'', hcl, hG'', hF'', hrunT, hres⟩ :=
    walkM1 (re := F.tele.ers.drop F.np) hlen htg hrb _ hwalk (fun so => WInv.init (by simp) _ _ so)
  rw [env_app_left (by simp; exact htg), eT, hfM] at hcl
  simp only [Tm.clo.injEq] at hcl; obtain ⟨rfl, rfl, rfl⟩ := hcl
  rw [hGr'] at hG''; cases hG''; rw [hF'] at hF''; cases hF''
  have hlenS : (filt (t.ers.take args.toList.length) (args.toList.map (P.sub ρS))).length =
      (F.tele.ers.take F.np).count false := by
    rw [hpe, length_filt _ _ (by simp; omega)]
  rw [hspI _ (by simp)] at hrunSb
  obtain ⟨envS', gidS, jS, GS, FS, outsT, hclS, hGS, hFS, hrunT', hresS⟩ :=
    walk1 (re := F.tele.ers.drop F.np) hlenS htg hrunSb _ hwalk (fun so => WInv.init (by simp) _ _ so)
  rw [env_app_left (by simp; exact htg), eT, hfS'] at hclS
  simp only [Tm.clo.injEq] at hclS; obtain ⟨rfl, rfl, rfl⟩ := hclS
  rw [hGr'] at hGS; cases hGS; rw [hF'] at hFS; cases hFS
  rw [hspI' _ (by simp)] at hrunS
  have hdet := RunS.det hrunT' hrunS; subst hdet
  have hbs : ∀ xs : List Tm, F'.spreadOut (some t.ers) args.toList.length xs =
      spread (t.ers.drop args.toList.length) (filt (F'.tele.ers.drop F'.np) xs) := fun xs => by simp [FnDef.spreadOut]
  refine ⟨.ofList lM, H1, as, H2, outs'', by simpa [Prog.subU] using hfM, hbl,
    by rw [Tm.toList_ofList, hspI' as hlas]; simpa [Tm.toList_ofList] using hrunT, ?_⟩
  have hvl : vsM.length = (t.ers.drop args.toList.length).length := by rw [hOb.len, hlS, hRbe]
  have hsl : outsSb'.length = (t.ers.drop args.toList.length).length := by rw [hlS, hRbe]
  refine callee_out hOa sB hOb hown hlive (by rw [hbs, hbs, length_spread, length_spread])
    (fun k w u hw hu => ?_) hru
  rw [hbs] at hw hu
  have hk : k < (t.ers.drop args.toList.length).length := by
    have := (List.getElem?_eq_some_iff.mp hw).1; rwa [length_spread] at this
  cases hb : (t.ers.drop args.toList.length).getD k true
  · rw [spread_get _ _ _ hb] at hw hu
    simp only [Option.some.injEq] at hw hu; subst hw hu
    refine .inr ⟨by rw [hRbe]; exact hb, ?_, ?_⟩
    · rw [get_getD (by omega), hres k (by rw [hre]; exact hb), hre]
    · rw [get_getD (by omega), hresS k (by rw [hre]; exact hb), hre]
  · rw [spread_tok _ _ _ hk hb] at hw hu
    cases hw; cases hu; exact .inl ⟨rfl, rfl⟩

end Minimal
