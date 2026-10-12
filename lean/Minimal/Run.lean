import Minimal.Reader
import Minimal.Strip

namespace Minimal

def Prog.nat (P : Prog) : Option Nat := P.adts.findIdx? (·.name == "Nat")

def Prog.lifted (P : Prog) (d : Nat) : Nat := ((P.adts[d]?).map (·.lifted)).getD 0

def Prog.natOf (nat : Option Nat) : Tm → Option Nat
  | .app (.vc d 0) .nil => if nat = some d then some 0 else none
  | .app (.vc d 1) (.cons x .nil) => if nat = some d then (Prog.natOf nat x).map (· + 1) else none
  | _ => none

def Prog.name (P : Prog) : Tm → String
  | .vc d c => ((P.adts[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}"
  | .tyc d => ((P.adts[d]?).map (·.name)).getD s!"T{d}"
  | _ => "_"

mutual
partial def Prog.show (P : Prog) (nat : Option Nat) (t : Tm) : String :=
  match Prog.natOf nat t, t with
  | some n, _ => toString n
  | none, .app h@(.vc d _) _ =>
    match P.adts[d]? with
    | some D => if D.union && (D.phantom.filter (!·)).length + (D.ctors.length - D.phantom.length) > 1 then "_"
      else P.showApp nat h t
    | none => P.showApp nat h t
  | none, .app h args => "(" ++ P.inner nat h args ++ ")"
  | none, .vc .. | none, .tyc .. => P.name t
  | none, .univ => "Type"
  | none, .level => "(Level)"
  | none, _ => "_"

partial def Prog.showApp (P : Prog) (nat : Option Nat) (h t : Tm) : String :=
  match t with
  | .app _ args => "(" ++ P.inner nat h args ++ ")"
  | _ => "_"

partial def Prog.inner (P : Prog) (nat : Option Nat) (h args : Tm) : String :=
  let (d, ers) := match h with
    | .vc d c => (d, ((P.ctor d c).map fieldErs).getD [])
    | .tyc d => (d, [])
    | _ => (0, [])
  let vs : List (Tm × Bool) := (args.toList.zipIdx.map fun (v, k) => (v, ers.getD k false)).drop (P.lifted d)
  let shown := vs.zipIdx.map fun ((v, er), k) =>
    if er then "_"
    else
      let sv := P.show nat v
      if k + 1 == vs.length && v matches .app (.vc ..) _ && sv.startsWith "(" then
        "$ " ++ (sv.drop 1).dropRight 1
      else sv
  " ".intercalate (P.name h :: shown)
end

def Prog.thunk (P : Prog) : Tm → Option (List Tm × Group × FnDef)
  | .clo env gid j => do
    let G ← P.groups[gid]?
    let F ← G.fns[j]?
    if F.np = 0 then some (env.toList ++ closures env.toList gid G, G, F) else none
  | _ => none

def Prog.run (P : Prog) : String :=
  match eval P none [] 0 P.main with
  | .ok ([v], cnt) => match P.thunk v with
    | some (ρ, _, F) => match eval P none ρ cnt F.body with
      | .ok (vs, _) => " ".intercalate (vs.map (P.show P.nat))
      | .error e => s!"stuck: {e}"
    | none => P.show P.nat v
  | .ok (vs, _) => " ".intercalate (vs.map (P.show P.nat))
  | .error e => s!"stuck: {e}"

def Prog.runStripped (P : Prog) : String :=
  match runS P 1000000 [] P.main with
  | some [v] => match P.thunk v with
    | some (ρ, _, F) => match runS P 1000000 ρ F.body with
      | some vs => " ".intercalate (vs.map (P.show P.nat))
      | none => "stuck"
    | none => P.show P.nat v
  | some vs => " ".intercalate (vs.map (P.show P.nat))
  | none => "stuck"

def prelude : String := include_str "../prelude.sl"

def runSource (src : String) (mode : String) (pre : Bool) : String :=
  match load ((if pre then prelude else "") ++ src) pre with
  | .error e => s!"error: {e}"
  | .ok P => match P.infer with
  | .error e => s!"error: {e}"
  | .ok P =>
    if mode == "--unchecked" then P.run
    else match checkProg P with
      | .error e => s!"refused: {e}"
      | .ok _ => if mode == "--stripped" then P.runStripped else P.run

end Minimal
