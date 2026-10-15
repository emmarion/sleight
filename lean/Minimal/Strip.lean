import Minimal.Eval

namespace Minimal

def Prog.view (P : Prog) : Tm → Tm
  | .nat n => match P.natD with
    | some d => match n with
      | 0 => .app (.vc d 0 .nil) .nil
      | k + 1 => .app (.vc d 1 .nil) (.cons (.nat k) .nil)
    | none => .nat n
  | t => t

def Prog.unnat (P : Prog) : Tm → Tm
  | .nat n => match P.natD with
    | some d => natTm' d n
    | none => .nat n
  | .app h a => .app (P.unnat h) (P.unnat a)
  | .cons h t => .cons (P.unnat h) (P.unnat t)
  | t => t

def Prog.norm (P : Prog) : Tm → Tm
  | .app (.vc d 0 .nil) .nil => if P.natD = some d then .nat 0 else .app (.vc d 0 .nil) .nil
  | .app (.vc d 1 .nil) (.cons (.nat k) .nil) =>
    if P.natD = some d then .nat (k + 1) else .app (.vc d 1 .nil) (.cons (.nat k) .nil)
  | t => t

def Prog.ctorErs (P : Prog) (d c : Nat) : List Bool := ((P.ctor d c).map fun sig => (sig.skip (P.lifted d)).ers).getD []

def maskArgs : List Bool → Tm → Tm
  | e :: es, .cons a as => .cons (if e then .tok else a) (maskArgs es as)
  | _, t => t

mutual
def Prog.subU (P : Prog) (f : Nat → Tm) : Tm → Tm
  | .fv i => f i
  | .vc d c _ => .vc d c .nil
  | .app h args =>
    let args' := P.subUArgs f args
    match P.subU f h with
    | .vc d c _ => match P.wrapField d c with
      | some k => args'.toList.getD k .nil
      | none => P.norm (.app (.vc d c .nil) (maskArgs (P.ctorErs d c) args'))
    | h' => .app h' args'
  | t => t.subst f

def Prog.subUArgs (P : Prog) (f : Nat → Tm) : Tm → Tm
  | .cons a as => .cons (P.subU f a) (P.subUArgs f as)
  | t => t.subst f
end

def Prog.sub (P : Prog) (ρ : List Tm) (t : Tm) : Tm := P.subU (Tm.env ρ) t

def filt : List Bool → List Tm → List Tm
  | b :: bs, x :: xs => if b then filt bs xs else x :: filt bs xs
  | _, _ => []

def spread : List Bool → List Tm → List Tm
  | [], _ => []
  | true :: bs, xs => .tok :: spread bs xs
  | false :: bs, xs => xs.headD .nil :: spread bs xs.tail

def FnDef.spreadIn (F : FnDef) (ve : Option (List Bool)) (args : List Tm) : List Tm :=
  spread (F.tele.ers.take F.np) (filt ((ve.getD F.tele.ers).take args.length) args)

def FnDef.spreadOut (F : FnDef) (ve : Option (List Bool)) (np : Nat) (outs : List Tm) : List Tm :=
  spread ((ve.getD F.tele.ers).drop np) (filt (F.tele.ers.drop F.np) outs)

def Prim.evalS (P : Prog) (ρ : List Tm) : Prim → Tm
  | .tm t | .lit t | .coerce t _ _ | .place t _ | .unplace t _ => P.sub ρ t
  | .num _ n => .nat n
  | p => p.eval ρ

def cval (env : List Tm) (gid : Nat) (acc : List Tm) (F : FnDef) : Tm := match F.dele with
  | some t => (env ++ acc).getD t .nil
  | none => .clo (.ofList env) gid acc.length

def closuresS (env : List Tm) (gid : Nat) (G : Group) : List Tm :=
  G.fns.foldl (fun acc F => acc ++ [cval env gid acc F]) []

variable (P : Prog)

inductive RunS : List Tm → Core → List Tm → Prop
  | ret : RunS ρ (.ret ts) (ts.toList.map (P.sub ρ))
  | callE : RunS (ρ ++ List.replicate ms.length .tok) rest out → RunS ρ (.call f dec args true ms ve rest) out
  | call : P.sub ρ f = .clo env gid j → P.groups[gid]? = some G → G.fns[j]? = some F →
      RunS (env.toList ++ closuresS env.toList gid G ++ F.spreadIn ve (args.toList.map (P.sub ρ))) F.body outs →
      RunS (ρ ++ F.spreadOut ve args.toList.length outs) rest out → RunS ρ (.call f dec args false ms ve rest) out
  | mtchE : RunS (ρ ++ List.replicate R.len .tok) rest out → RunS ρ (.mtch s R brs els true rest) out
  | mtch : P.view (P.sub ρ s) = .app (.vc d c ls) vs → selectBr brs els c vs.toList = some (pre, body) →
      RunS (ρ ++ pre) body outs → RunS (ρ ++ outs) rest out → RunS ρ (.mtch s R brs els false rest) out
  | caseE : realBr brs els = some (pre, body) → RunS (ρ ++ pre) body out → RunS ρ (.case s brs els true nt) out
  | caseN : realBr brs els = some (pre, body) → RunS (ρ ++ pre.map fun _ => P.sub ρ s) body out →
      RunS ρ (.case s brs els false true) out
  | case : P.view (P.sub ρ s) = .app (.vc d c ls) vs → selectBr brs els c vs.toList = some (pre, body) →
      RunS (ρ ++ pre) body out → RunS ρ (.case s brs els false false) out
  | seq : RunS ρ body outs → RunS (ρ ++ outs) rest out → RunS ρ (.seq R body rest) out
  | prim : RunS (ρ ++ [if er then .tok else p.evalS P ρ]) rest out → RunS ρ (.prim p er rest) out
  | defLvl : RunS (ρ ++ [.tok]) rest out → RunS ρ (.defLvl rest) out
  | defFns : P.groups[gid]? = some G → RunS (ρ ++ closuresS ρ gid G) rest out → RunS ρ (.defFns gid rest) out
  | chk : RunS ρ rest out → RunS ρ (.chk k a b rest) out

variable {P} in
theorem RunS.det {ρ : List Tm} {c : Core} {a b : List Tm} (h1 : RunS P ρ c a) (h2 : RunS P ρ c b) : a = b := by
  induction h1 generalizing b with
  | ret => cases h2; rfl
  | callE _ ih => cases h2 with | callE h => exact ih h
  | call hf hG hF _ _ ihb ihr =>
    cases h2 with
    | call hf' hG' hF' hb hr =>
      rw [hf] at hf'; cases hf'; rw [hG] at hG'; cases hG'; rw [hF] at hF'; cases hF'
      cases ihb hb; exact ihr hr
  | mtchE _ ih => cases h2 with | mtchE h => exact ih h
  | mtch hs hsel _ _ ihb ihr =>
    cases h2 with
    | mtch hs' hsel' hb hr =>
      rw [hs] at hs'; cases hs'; rw [hsel] at hsel'; cases hsel'
      cases ihb hb; exact ihr hr
  | caseE hsel _ ih => cases h2 with | caseE hsel' h => rw [hsel] at hsel'; cases hsel'; exact ih h
  | caseN hsel _ ih => cases h2 with | caseN hsel' h => rw [hsel] at hsel'; cases hsel'; exact ih h
  | case hs hsel _ ih =>
    cases h2 with
    | case hs' hsel' h => rw [hs] at hs'; cases hs'; rw [hsel] at hsel'; cases hsel'; exact ih h
  | seq _ _ ihb ihr => cases h2 with | seq hb hr => cases ihb hb; exact ihr hr
  | prim _ ih => cases h2 with | prim h => exact ih h
  | defLvl _ ih => cases h2 with | defLvl h => exact ih h
  | defFns hG _ ih => cases h2 with | defFns hG' h => rw [hG] at hG'; cases hG'; exact ih h
  | chk _ ih => cases h2 with | chk h => exact ih h

mutual
inductive Real : Tm → Tm → Prop
  | con : P.ctor d c = some sig → P.phantom d c = false → P.wrapField d c = none → Reals vsS vs (sig.skip (P.lifted d)) →
      Real (.app (.vc d c .nil) vsS) (.app (.vc d c ls) vs)
  | wrap : P.wrapField d c = some k → Real vS (vs.toList.getD k .nil) → Real vS (.app (.vc d c ls) vs)
  | vc : P.phantom d c = false → Real (.vc d c .nil) (.vc d c ls)
  | clo : P.groups[gid]? = some G → G.ghost = false → G.fns[j]? = some F → F.er = false → F.dele = none →
      envS.length = env.length → (∀ i, G.ers.getD i true = false → Real (Tm.env envS i) (Tm.env env i)) →
      Real (.clo (.ofList envS) gid j) (.clo (.ofList env) gid j)
  | dele : P.groups[gid]? = some G → G.ghost = false → G.fns[j]? = some F → F.er = false → F.dele = some t →
      Real vS (Tm.env (env ++ closures env gid G) t) → Real vS (.clo (.ofList env) gid j)
  | nat : P.natD = some e → Real (P.view (.nat n)) v → Real (.nat n) v
  | other : (∀ d c ls vs, v ≠ .app (.vc d c ls) vs) → (∀ d c ls, v ≠ .vc d c ls) → (∀ e g j, v ≠ .clo e g j) → Real vS v

inductive Reals : Tm → Tm → Tm → Prop
  | nil : Reals .nil .nil t
  | cons : (k.er = false → Real a b) → Reals as bs r → Reals (.cons a as) (.cons b bs) (.bind k A r)
end

def SimEnv (er : Nat → Bool) (ρS ρ : List Tm) : Prop :=
  ρS.length = ρ.length ∧ ∀ i, er i = false → Real P (Tm.env ρS i) (Tm.env ρ i)



theorem Real.nat_view' {P : Prog} : ∀ {vS v : Tm}, Real P vS v → ∀ n, vS = .nat n → Real P (P.view (.nat n)) v
  | _, _, .nat _ h, _, rfl => h
  | _, _, .wrap hw h, n, e => .wrap hw (Real.nat_view' h n e)
  | _, _, .dele hG hg hF he hd h, n, e => .dele hG hg hF he hd (Real.nat_view' h n e)
  | _, _, .other h1 h2 h3, _, _ => .other h1 h2 h3
  | _, _, .con .., _, e => by cases e
  | _, _, .vc .., _, e => by cases e
  | _, _, .clo .., _, e => by cases e

theorem Real.nat_view {P : Prog} {n : Nat} {v : Tm} (h : Real P (.nat n) v) : Real P (P.view (.nat n)) v :=
  Real.nat_view' h n rfl

theorem Prog.view_nat {P : Prog} {e n : Nat} (he : P.natD = some e) :
    ∃ c args, P.view (.nat n) = .app (.vc e c .nil) args := by
  cases n <;> simp [Prog.view, he]

theorem Real.view {P : Prog} {vS v : Tm} (h : Real P vS v) : Real P (P.view vS) v := by
  cases vS <;> first | exact h | exact Real.nat_view h

theorem Reals.mask {P : Prog} : ∀ {a b t : Tm}, Reals P a b t → Reals P (maskArgs t.ers a) b t
  | _, _, _, .nil => by cases ‹Tm› <;> exact .nil
  | _, _, _, .cons (k := k) hr hs => by
    simp only [Tm.ers, maskArgs]
    exact .cons (fun hk => by simpa [hk] using hr hk) hs.mask

theorem Real.natInd {P : Prog} {v w : Tm}
    (main : ∀ vS, (∀ k e, vS = .nat k → P.natD = some e → Real P (P.view vS) w) → Real P vS v → Real P vS w) :
    ∀ vS, Real P vS v → Real P vS w := by
  intro vS h
  refine main vS (fun k e hk he => ?_) h
  subst hk
  obtain ⟨c', a', hv⟩ := Prog.view_nat (n := k) he
  rw [hv]
  exact main _ (fun k' _ hk' _ => by simp at hk') (by rw [← hv]; exact Real.nat_view h)

theorem Real.norm {P : Prog} {x v : Tm} (h : Real P x v) : Real P (P.norm x) v := by
  unfold Prog.norm
  split
  · split
    · rename_i d hd; exact .nat hd (by simpa [Prog.view, hd] using h)
    · exact h
  · split
    · rename_i d _ hd; exact .nat hd (by simpa [Prog.view, hd] using h)
    · exact h
  · exact h

theorem Prog.unnat_view {P : Prog} {e n : Nat} (he : P.natD = some e) : P.unnat (P.view (.nat n)) = P.unnat (.nat n) := by
  cases n <;> simp [Prog.view, Prog.unnat, he, natTm']
end Minimal
