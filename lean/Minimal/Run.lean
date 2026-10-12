import Minimal.Reader
import Minimal.Strip

namespace Minimal

def Prog.lifted (P : Prog) (d : Nat) : Nat := ((P.adts[d]?).map (·.lifted)).getD 0

partial def Prog.show (P : Prog) : Tm → String
  | .app h args =>
    let d := match h with | .tyc d | .vc d _ => d | _ => 0
    "(" ++ " ".intercalate (P.show h :: (args.toList.drop (P.lifted d)).map P.show) ++ ")"
  | .vc d c => ((P.adts[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}"
  | .tyc d => ((P.adts[d]?).map (·.name)).getD s!"T{d}"
  | .tyCtor .. => "(TyCtor ...)"
  | .valCtor .. => "(ValCtor ...)"
  | .univ => "Type"
  | .level => "(Level)"
  | .lvl n => s!"<level {n}>"
  | .tok => "_"
  | .clo .. => "<function>"
  | .fn .. => "(Fn ...)"
  | .predates .. => "(Predates ...)"
  | .subterm .. => "(Subterm ...)"
  | t => reprStr t

def Prog.run (P : Prog) : String :=
  match eval P none [] 0 P.main with
  | .ok (vs, _) => " ".intercalate (vs.map P.show)
  | .error e => s!"stuck: {e}"

def Prog.runStripped (P : Prog) : String :=
  match runS P 1000000 [] P.main with
  | some vs => " ".intercalate (vs.map P.show)
  | none => "stuck"

def prelude : String := include_str "../prelude.sl"

def runSource (src : String) (mode : String) (pre : Bool) : String :=
  match load ((if pre then prelude else "") ++ src) with
  | .error e => s!"error: {e}"
  | .ok P => match P.infer with
  | .error e => s!"error: {e}"
  | .ok P =>
    if mode == "--unchecked" then P.run
    else match checkProg P with
      | .error e => s!"refused: {e}"
      | .ok _ => if mode == "--stripped" then P.runStripped else P.run

end Minimal
