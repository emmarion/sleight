import Minimal.Syntax

set_option linter.unusedVariables false

namespace Minimal

def lexLt : Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | k + 1, a, b => a.headD 0 < b.headD 0 || (a.headD 0 == b.headD 0 && lexLt k a.tail b.tail)

theorem lexLt_wf : ∀ k, WellFounded (fun a b => lexLt k a b = true)
  | 0 => ⟨fun a => ⟨a, fun _ h => by simp [lexLt] at h⟩⟩
  | k + 1 => by
    have := InvImage.wf (fun a : List Nat => (a.headD 0, a.tail))
      (Prod.lex Nat.lt_wfRel ⟨_, lexLt_wf k⟩).wf
    refine Subrelation.wf (fun {a b} h => ?_) this
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact Prod.Lex.left _ _ h
    · show Prod.Lex _ _ (a.headD 0, a.tail) (b.headD 0, b.tail)
      rw [h1]; exact Prod.Lex.right _ h2

def muLt (k : Nat) : Option (List Nat) → Option (List Nat) → Bool
  | some a, some b => lexLt (k + 1) a b
  | some _, none => true
  | none, _ => false

def MuLt (k : Nat) (a b : Option (List Nat)) : Prop := muLt k a b = true

theorem MuLt_wf (k : Nat) : WellFounded (MuLt k) := by
  have hs : ∀ a, Acc (MuLt k) (some a) := fun a =>
    (lexLt_wf (k + 1)).induction (C := fun a => Acc (MuLt k) (some a)) a fun a ih =>
      ⟨_, fun y h => match y, h with | some b, h => ih b h⟩
  exact ⟨fun
    | some a => hs a
    | none => ⟨_, fun y h => match y, h with | some b, _ => hs b | none, h => by simp [MuLt, muLt] at h⟩⟩

structure Mu (k : Nat) where
  μ : Option (List Nat)

instance (k : Nat) : WellFoundedRelation (Mu k) := ⟨fun a b => MuLt k a.μ b.μ, InvImage.wf _ (MuLt_wf k)⟩

def Prim.eval (ρ : List Tm) : Prim → Tm
  | .tm t | .lit t => t.subst (Tm.env ρ)
  | .assert t _ => t
  | .coerce _ b _ => b.subst (Tm.env ρ)
  | .atom d => .app (.vc d 0 .nil) .nil
  | .num d n => natTm' d n
  | _ => .tok

def callee (P : Prog) : Tm → Option (List Tm × Nat × Nat × Group × FnDef)
  | .clo env gid j => do
    let G ← P.groups[gid]?
    let F ← G.fns[j]?
    match env.toList[G.lvl]? with
    | some (.lvl n) => some (env.toList, n, gid, G, F)
    | _ => none
  | _ => none

def eval (P : Prog) (μ : Option (List Nat)) (ρ : List Tm) (cnt : Nat) : Core → Except String (List Tm × Nat)
  | .ret ts => .ok (ts.toList.map (·.subst (Tm.env ρ)), cnt)
  | .call f _ args _ _ _ rest =>
    match callee P (f.subst (Tm.env ρ)) with
    | some (env, n, gid, G, F) =>
      let argv := args.toList.map (·.subst (Tm.env ρ))
      let μ' := some (n :: (markedArgs F.tele (.ofList argv)).map Tm.size)
      if h : muLt P.k μ' μ then
        match eval P μ' (env ++ closures env gid G ++ argv) cnt F.body with
        | .ok (outs, cnt) => eval P μ (ρ ++ outs) cnt rest
        | .error e => .error e
      else .error "call does not decrease"
    | none => .error "callee is not a function"
  | .mtch s _ brs els _ rest =>
    match s.subst (Tm.env ρ) with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) =>
        match eval P μ (ρ ++ pre) cnt body with
        | .ok (outs, cnt) => eval P μ (ρ ++ outs) cnt rest
        | .error e => .error e
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .prim p _ rest => eval P μ (ρ ++ [p.eval ρ]) cnt rest
  | .defLvl rest => eval P μ (ρ ++ [.lvl cnt]) (cnt + 1) rest
  | .defFns gid rest =>
    match P.groups[gid]? with
    | some G => eval P μ (ρ ++ closures ρ gid G) cnt rest
    | none => .error "no group"
  | .chk _ _ _ rest => eval P μ ρ cnt rest
  | .absurd body => match eval P μ ρ cnt body with
    | .ok _ => .error "an absurd body returned"
    | .error e => .error e
  | .dead => .error "a refuted branch was reached"
  | .case s brs els _ _ =>
    match s.subst (Tm.env ρ) with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) => eval P μ (ρ ++ pre) cnt body
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .seq _ body rest =>
    match eval P μ ρ cnt body with
    | .ok (outs, cnt) => eval P μ (ρ ++ outs) cnt rest
    | .error e => .error e
termination_by c => ((⟨μ⟩ : Mu P.k), sizeOf c)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ h
    | (apply Prod.Lex.right; simp; try omega)
  all_goals (have := sizeOf_selectBr hb; simp; omega)

end Minimal
