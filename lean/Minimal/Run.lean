import Minimal.Reader
import Minimal.Eval

namespace Minimal

partial def Prog.show (P : Prog) : Tm → String
  | .con d c args =>
    let name := ((P.adts[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}"
    "(" ++ " ".intercalate (name :: args.toList.map P.show) ++ ")"
  | .ty d args =>
    let name := ((P.adts[d]?).map (·.name)).getD s!"T{d}"
    "(" ++ " ".intercalate (name :: args.toList.map P.show) ++ ")"
  | .univ => "Type"
  | .level => "(Level)"
  | .lvl n => s!"<level {n}>"
  | .tok => "<proof>"
  | .clo .. => "<function>"
  | .fn .. => "(Fn ...)"
  | .predates .. => "(Predates ...)"
  | .subterm .. => "(Subterm ...)"
  | t => reprStr t

def Prog.run (P : Prog) : String :=
  match eval P none [] 0 P.main with
  | .ok (vs, _) => " ".intercalate (vs.map P.show)
  | .error e => s!"stuck: {e}"

def runSource (src : String) (checked : Bool) : String :=
  match load src with
  | .error e => s!"syntax error: {e}"
  | .ok P =>
    if checked then
      match checkProg P with
      | .error e => s!"refused: {e}"
      | .ok _ => P.run
    else P.run

end Minimal
