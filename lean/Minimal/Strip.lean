import Minimal.Check
import Minimal.Eval

namespace Minimal

variable (P : Prog)

inductive RunS : List Tm → Core → List Tm → Prop
  | ret : RunS ρ (.ret ts) (ts.toList.map (·.subst (Tm.env ρ)))
  | callE : RunS (ρ ++ List.replicate ms.length .tok) rest out → RunS ρ (.call f dec args true ms rest) out
  | call : f.subst (Tm.env ρ) = .clo env gid j → P.groups[gid]? = some G → G.fns[j]? = some F →
      RunS (env.toList ++ closures env.toList gid G ++ args.toList.map (·.subst (Tm.env ρ))) F.body outs →
      RunS (ρ ++ outs) rest out → RunS ρ (.call f dec args false ms rest) out
  | mtchE : RunS (ρ ++ List.replicate R.len .tok) rest out → RunS ρ (.mtch s R brs els true rest) out
  | mtch : s.subst (Tm.env ρ) = .app (.vc d c) vs → selectBr brs els c vs.toList = some (pre, body) →
      RunS (ρ ++ pre) body outs → RunS (ρ ++ outs) rest out → RunS ρ (.mtch s R brs els false rest) out
  | caseE : realBr P brs els = some (pre, body) → RunS (ρ ++ pre) body out → RunS ρ (.case s brs els true) out
  | case : s.subst (Tm.env ρ) = .app (.vc d c) vs → selectBr brs els c vs.toList = some (pre, body) →
      RunS (ρ ++ pre) body out → RunS ρ (.case s brs els false) out
  | seq : RunS ρ body outs → RunS (ρ ++ outs) rest out → RunS ρ (.seq R body rest) out
  | prim : RunS (ρ ++ [if er then .tok else p.eval ρ]) rest out → RunS ρ (.prim p er rest) out
  | defLvl : RunS (ρ ++ [.tok]) rest out → RunS ρ (.defLvl rest) out
  | defFns : P.groups[gid]? = some G → RunS (ρ ++ closures ρ gid G) rest out → RunS ρ (.defFns gid rest) out
  | chk : RunS ρ rest out → RunS ρ (.chk k a b rest) out

def runS : Nat → List Tm → Core → Option (List Tm)
  | 0, _, _ => none
  | fuel + 1, ρ, c => match c with
    | .ret ts => some (ts.toList.map (·.subst (Tm.env ρ)))
    | .call _ _ _ true ms rest => runS fuel (ρ ++ List.replicate ms.length .tok) rest
    | .call f _ args false _ rest => match f.subst (Tm.env ρ) with
      | .clo env gid j => do
        let G ← P.groups[gid]?
        let F ← G.fns[j]?
        let outs ← runS fuel (env.toList ++ closures env.toList gid G ++ args.toList.map (·.subst (Tm.env ρ))) F.body
        runS fuel (ρ ++ outs) rest
      | _ => none
    | .mtch _ R _ _ true rest => runS fuel (ρ ++ List.replicate R.len .tok) rest
    | .mtch s _ brs els false rest => match s.subst (Tm.env ρ) with
      | .app (.vc _ c) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        let outs ← runS fuel (ρ ++ pre) body
        runS fuel (ρ ++ outs) rest
      | _ => none
    | .case _ brs els true => do
      let (pre, body) ← realBr P brs els
      runS fuel (ρ ++ pre) body
    | .case s brs els false => match s.subst (Tm.env ρ) with
      | .app (.vc _ c) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        runS fuel (ρ ++ pre) body
      | _ => none
    | .seq _ body rest => do
      let outs ← runS fuel ρ body
      runS fuel (ρ ++ outs) rest
    | .prim p er rest => runS fuel (ρ ++ [if er then .tok else p.eval ρ]) rest
    | .defLvl rest => runS fuel (ρ ++ [.tok]) rest
    | .defFns gid rest => do runS fuel (ρ ++ closures ρ gid (← P.groups[gid]?)) rest
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
        exact .call ‹_› hG hF (ih _ _ _ hb) (ih _ _ _ hr)
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
  | con : P.ctor d c = some sig → P.phantom d c = false → Reals vsS vs sig →
      Real (.app (.vc d c) vsS) (.app (.vc d c) vs)
  | vc : P.phantom d c = false → Real (.vc d c) (.vc d c)
  | clo : P.groups[gid]? = some G → G.ghost = false → G.fns[j]? = some F → F.er = false →
      envS.length = env.length → (∀ i, G.ers.getD i true = false → Real (Tm.env envS i) (Tm.env env i)) →
      Real (.clo (.ofList envS) gid j) (.clo (.ofList env) gid j)
  | other : (∀ d c vs, v ≠ .app (.vc d c) vs) → (∀ d c, v ≠ .vc d c) → (∀ e g j, v ≠ .clo e g j) → Real vS v

inductive Reals : Tm → Tm → Tm → Prop
  | nil : Reals .nil .nil t
  | cons : (k.er = false → Real a b) → Reals as bs r → Reals (.cons a as) (.cons b bs) (.bind k A r)
end

def SimEnv (er : Nat → Bool) (ρS ρ : List Tm) : Prop :=
  ρS.length = ρ.length ∧ ∀ i, er i = false → Real P (Tm.env ρS i) (Tm.env ρ i)

end Minimal
