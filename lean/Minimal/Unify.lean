import Minimal.Syntax

set_option linter.unusedVariables false

namespace Minimal

namespace Tm

def kids : Tm → List Tm
  | cons h t => [h, t]
  | bind _ a r => [a, r]
  | app h a => [h, a]
  | tyCtor p | valCtor p => [p]
  | predates A x L => [A, x, L]
  | subterm A a B b => [A, a, B, b]
  | fn l _ t => [l, t]
  | mtbl _ _ _ _ T cs => [T, cs]
  | _ => []

def sameHead : Tm → Tm → Bool
  | fv _, _ | _, fv _ => false
  | cons .., cons .. | predates .., predates .. | subterm .., subterm .. => true
  | bind m .., bind m' .. => m == m'
  | app .., app .. | tyCtor _, tyCtor _ | valCtor _, valCtor _ => true
  | fn _ np _, fn _ np' _ => np == np'
  | mtbl u nt ex ph _ _, mtbl u' nt' ex' ph' _ _ => u == u' && nt == nt' && ex == ex' && ph == ph'
  | a, b => a == b

theorem kids_size (t : Tm) : (t.kids.map size).sum < t.size := by
  cases t <;> simp [kids, size] <;> omega

theorem size_pos (t : Tm) : 0 < t.size := by cases t <;> simp [size] <;> omega

end Tm

def eqsSize (l : List (Tm × Tm)) : Nat := (l.map fun p => p.1.size + p.2.size).sum

theorem eqsSize_zip : ∀ (xs ys : List Tm),
    eqsSize (xs.zip ys) ≤ (xs.map Tm.size).sum + (ys.map Tm.size).sum
  | [], _ | _ :: _, [] => by simp [eqsSize]
  | x :: xs, y :: ys => by
    have := eqsSize_zip xs ys
    simp [eqsSize] at *; omega

inductive UResult where
  | ok (σ : Nat → Option Tm)
  | contra
  | unknown

def varSide : Tm → Tm → Option (Nat × Tm)
  | .fv e, t | t, .fv e => some (e, t)
  | _, _ => none

def substOne (e : Nat) (t : Tm) : Tm → Tm := Tm.subst fun i => if i = e then t else .fv i

def assign (e : Nat) (t : Tm) (σ : Nat → Option Tm) (x : Nat) : Option Tm :=
  if x = e then some t else (σ x).map (substOne e t)

def canonBy (σ : Nat → Option Tm) (t : Tm) : Tm := t.subst fun i => (σ i).getD (.fv i)

abbrev Atoms := (Nat → Option Tm) → Tm → Tm → Option (List (Tm × Tm))

def unify (n : Nat) (atoms : Atoms) (σ : Nat → Option Tm) (dom : List Nat) : List (Tm × Tm) → UResult
  | [] => .ok σ
  | (a, b) :: rest =>
    if a = b then unify n atoms σ dom rest
    else match varSide a b with
      | some (e, t) =>
        if e ∈ t.fvs ∨ t.bound 0 = false then .contra
        else match atoms σ (.fv e) t with
          | none => .contra
          | some more =>
            if h : dom.length < n ∧ e ∉ dom ∧ e < n ∧ t.static n 0 then
              unify n atoms (assign e t σ) (e :: dom)
                ((more ++ rest).map fun p => (substOne e t p.1, substOne e t p.2))
            else .unknown
      | none =>
        if a.sameHead b then unify n atoms σ dom (a.kids.zip b.kids ++ rest) else .contra
termination_by eqs => (n + 1 - dom.length, eqsSize eqs)
decreasing_by
  · apply Prod.Lex.right; have := a.size_pos; simp [eqsSize]; omega
  · apply Prod.Lex.left; simp; omega
  · apply Prod.Lex.right
    have := eqsSize_zip a.kids b.kids
    have := a.kids_size; have := b.kids_size
    simp [eqsSize] at *; omega

end Minimal
