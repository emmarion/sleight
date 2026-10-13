import Minimal.Reader
import Minimal.Strip

namespace Minimal

def Prog.nat (P : Prog) : Option Nat := P.adts.findIdx? (·.name == "Nat")

def Prog.lifted (P : Prog) (d : Nat) : Nat := ((P.adts[d]?).map (·.lifted)).getD 0

def Prog.natOf (nat : Option Nat) : Tm → Option Nat
  | .app (.vc d 0) .nil => if nat = some d then some 0 else none
  | .app (.vc d 1) (.cons x .nil) => if nat = some d then (Prog.natOf nat x).map (· + 1) else none
  | _ => none

def Prog.charOf (P : Prog) (nat : Option Nat) : Tm → Option Nat
  | .app (.vc d 0) args =>
    if P.adts.findIdx? (·.name == "Char") != some d then none else
    match args.toList.getLast? with
    | some (.app (.vc _ 0) uargs) => let us := uargs.toList; Prog.natOf nat (us.getD (us.length - 2) .nil)
    | _ => none
  | _ => none

partial def Prog.strOf (P : Prog) (nat : Option Nat) : Tm → Option (List Nat)
  | .app (.vc d c) args =>
    if P.adts.findIdx? (·.name == "String") != some d then none
    else if c == 0 then some []
    else
      let as := args.toList
      match P.charOf nat (as.getD (as.length - 2) .nil), P.strOf nat (as.getD (as.length - 1) .nil) with
      | some ch, some rest => some (ch :: rest)
      | _, _ => none
  | _ => none

def hex2 (n : Nat) : String :=
  let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (n / 16), d (n % 16)]

def showChar (c : Nat) : String :=
  if c == 32 then "#\\space" else if c == 10 then "#\\newline" else if c == 9 then "#\\tab"
  else if 33 ≤ c && c ≤ 126 && c != 40 && c != 41 && c != 59 then "#\\" ++ (Char.ofNat c).toString
  else "#\\x" ++ hex2 c

def showStr (cs : List Nat) : String :=
  "\"" ++ String.join (cs.map fun c =>
    if c == 34 then "\\\"" else if c == 92 then "\\\\" else if c == 10 then "\\n" else if c == 9 then "\\t"
    else if 32 ≤ c && c ≤ 126 then (Char.ofNat c).toString else "\\x" ++ hex2 c) ++ "\""

def Prog.name (P : Prog) : Tm → String
  | .vc d c => showName (((P.adts[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}")
  | .tyc d => showName (((P.adts[d]?).map (·.name)).getD s!"T{d}")
  | _ => "_"

mutual
partial def Prog.show (P : Prog) (nat : Option Nat) (t : Tm) : String :=
  match Prog.natOf nat t, t with
  | some n, _ => toString n
  | none, _ => match P.charOf nat t, P.strOf nat t with
  | some c, _ => showChar c
  | _, some cs => showStr cs
  | _, _ => match t with
  | .app h@(.vc d _) _ =>
    match P.adts[d]? with
    | some D => if D.union && (D.phantom.filter (!·)).length + (D.ctors.length - D.phantom.length) > 1 then "_"
      else P.showApp nat h t
    | none => P.showApp nat h t
  | .app h args => "(" ++ P.inner nat h args ++ ")"
  | .vc .. | .tyc .. => P.name t
  | .univ => "Type"
  | .level => "(Level)"
  | _ => "_"

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

def Prog.thunk (P : Prog) : Tm → Except String (Option (List Tm × Group × FnDef))
  | .clo env gid j => match P.groups[gid]?, (P.groups[gid]?).bind (·.fns[j]?) with
    | some G, some F =>
      if F.np = 0 && F.tele matches .bind (.ty _ false) _ .nil then .ok (some (env.toList ++ closures env.toList gid G, G, F))
      else .error "error: a final function must be `(Fn L -> (many T y))`"
    | _, _ => .ok none
  | _ => .ok none

def Prog.final (P : Prog) (go : List Tm → Core → Option (List Tm)) : Option (List Tm) → String
  | some [v] => match P.thunk v with
    | .ok (some (ρ, _, F)) => match go ρ F.body with
      | some vs => " ".intercalate (vs.map (P.show P.nat))
      | none => "stuck"
    | .ok none => P.show P.nat v
    | .error e => e
  | some vs => " ".intercalate (vs.map (P.show P.nat))
  | none => "stuck"

def Prog.run (P : Prog) : String :=
  match eval P none [] 0 P.main with
  | .ok (vs, cnt) => P.final (fun ρ c => match eval P none ρ cnt c with | .ok (vs, _) => some vs | .error _ => none) (some vs)
  | .error e => s!"stuck: {e}"

def Prog.runStripped (P : Prog) : String :=
  P.final (runS P 100000000) (runS P 100000000 [] P.main)

def prelude : String := include_str "../prelude.sl"

def runProg (P : Prog) (mode : String) : String :=
  match P.infer with
  | .error e => s!"error: {e}"
  | .ok P =>
    if mode == "--unchecked" then P.run
    else match checkProg P with
      | .error e => s!"refused: {e}"
      | .ok _ => if mode == "--full" then P.run else P.runStripped

def runSource (src : String) (mode : String) (pre : Bool) : List String × String :=
  match load ((if pre then prelude ++ "\n(__prelude-end)\n" else "") ++ src) pre with
  | .error e => ([], s!"error: {e}")
  | .ok (P, ws) => (ws, runProg P mode)

end Minimal
