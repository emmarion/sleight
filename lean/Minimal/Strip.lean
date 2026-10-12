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
  | mtch : s.subst (Tm.env ρ) = .con d c vs → selectBr brs els c vs.toList = some (pre, body) →
      RunS (ρ ++ pre) body outs → RunS (ρ ++ outs) rest out → RunS ρ (.mtch s R brs els false rest) out
  | prim : RunS (ρ ++ [if er then .tok else p.eval ρ]) rest out → RunS ρ (.prim p er rest) out
  | defLvl : RunS (ρ ++ [.tok]) rest out → RunS ρ (.defLvl rest) out
  | defFns : P.groups[gid]? = some G → RunS (ρ ++ closures ρ gid G) rest out → RunS ρ (.defFns gid rest) out
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
  | prim _ ih => cases h2 with | prim h => exact ih h
  | defLvl _ ih => cases h2 with | defLvl h => exact ih h
  | defFns hG _ ih => cases h2 with | defFns hG' h => rw [hG] at hG'; cases hG'; exact ih h
  | chk _ ih => cases h2 with | chk h => exact ih h

mutual
inductive Real : Tm → Tm → Prop
  | con : P.ctor d c = some sig → Reals vsS vs sig → Real (.con d c vsS) (.con d c vs)
  | clo : P.groups[gid]? = some G → G.ghost = false → G.fns[j]? = some F → F.er = false →
      envS.length = env.length → (∀ i, G.ers.getD i true = false → Real (Tm.env envS i) (Tm.env env i)) →
      Real (.clo (.ofList envS) gid j) (.clo (.ofList env) gid j)
  | other : (∀ d c vs, v ≠ .con d c vs) → (∀ e g j, v ≠ .clo e g j) → Real vS v

inductive Reals : Tm → Tm → Tm → Prop
  | nil : Reals .nil .nil t
  | cons : (k.er = false → Real a b) → Reals as bs r → Reals (.cons a as) (.cons b bs) (.bind k A r)
end

def SimEnv (er : Nat → Bool) (ρS ρ : List Tm) : Prop :=
  ρS.length = ρ.length ∧ ∀ i, er i = false → Real P (Tm.env ρS i) (Tm.env ρ i)

end Minimal
