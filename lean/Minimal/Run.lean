import Minimal.Reader
import Minimal.Uses
import Minimal.Strip

namespace Minimal

def Prog.nat (P : Prog) : Option Nat := P.adts.findIdx? (·.name == "Nat")

def Prog.ownErs (P : Prog) (d c : Nat) : List Bool := ((P.ctor d c).map fun sig => fieldErs (sig.skip (P.lifted d))).getD []

def Prog.natOf (nat : Option Nat) : Tm → Option Nat
  | .nat n => if nat.isSome then some n else none
  | .app (.vc d 0 _) .nil => if nat = some d then some 0 else none
  | .app (.vc d 1 _) (.cons x .nil) => if nat = some d then (Prog.natOf nat x).map (· + 1) else none
  | _ => none

def Prog.charOf (P : Prog) (nat : Option Nat) : Tm → Option Nat
  | .app (.vc d 0 _) args =>
    if P.adts.findIdx? (·.name == "Char") != some d then none else
    match args.toList.getLast? with
    | some (.app (.vc _ 0 _) uargs) => let us := uargs.toList; Prog.natOf nat (us.getD (us.length - 2) .nil)
    | _ => none
  | _ => none

partial def Prog.strOf (P : Prog) (nat : Option Nat) : Tm → Option (List Nat)
  | .app (.vc d c _) args =>
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
  | .vc d c _ => showName (((P.adts[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}")
  | .tyc d _ => showName (((P.adts[d]?).map (·.name)).getD s!"T{d}")
  | _ => "_"

mutual
partial def Prog.show (P : Prog) (nat : Option Nat) (t : Tm) : String :=
  match Prog.natOf nat t, t with
  | some n, _ => toString n
  | none, .nat n => if P.view (.nat n) == .nat n then "_" else P.show nat (P.unnat (.nat n))
  | none, _ => match P.charOf nat t, P.strOf nat t with
  | some c, _ => showChar c
  | _, some cs => showStr cs
  | _, _ => match t with
  | .app h@(.vc d _ _) _ =>
    match P.adts[d]? with
    | some D => if D.name == "Slot" || D.union && (D.phantom.filter (!·)).length + (D.ctors.length - D.phantom.length) > 1 then "_"
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
  let ers := match h with
    | .vc d c _ => P.ownErs d c
    | _ => []
  let vs : List (Tm × Bool) := args.toList.zipIdx.map fun (v, k) => (v, ers.getD k false)
  let shown := vs.zipIdx.map fun ((v, er), k) =>
    if er then "_"
    else
      let sv := P.show nat v
      if k + 1 == vs.length && (v matches .app (.vc ..) _ || v matches .nat _) && sv.startsWith "(" then
        "$ " ++ (sv.drop 1).dropRight 1
      else sv
  " ".intercalate (P.name h :: shown)
end

def printHole : Nat := 2 ^ 41

partial def matchTy (sol : List (Nat × Tm)) : Tm → Tm → List (Nat × Tm)
  | .fv i, t => if printHole ≤ i && (sol.lookup i).isNone then (i, t) :: sol else sol
  | .app h a, .app h' a' => matchTy (matchTy sol h h') a a'
  | .tyc _ l, .tyc _ l' => matchTy sol l l'
  | .cons h t, .cons h' t' => matchTy (matchTy sol h h') t t'
  | _, _ => sol

partial def openSig : Nat → Tm → List (Option Tm) × Tm
  | j, .bind k A r@(.bind ..) =>
    let (fs, R) := openSig (j + 1) (r.inst (.fv (printHole + j)) 0)
    ((if k matches .ty .. then some A else none) :: fs, R)
  | _, .bind _ A _ => ([], A)
  | _, t => ([], t)

def Prog.fieldTys (P : Prog) (d c : Nat) (T : Tm) : List (Option Tm) :=
  let (fs, R) := openSig 0 ((P.ctor d c).getD .nil)
  let sol := matchTy [] R T
  (fs.drop (P.lifted d)).map fun F => F.bind fun F =>
    let F := F.subst fun i => (sol.lookup i).getD (.fv i)
    if (F.fvs.any (printHole ≤ ·) && !(F matches .app (.tyc ..) _)) || F.levels.length > 0 then none else some F

def Prog.adtIs (P : Prog) (d : Nat) (name : String) : Bool := P.adts.findIdx? (·.name == name) == some d

partial def Prog.strT (P : Prog) (nat : Option Nat) : Tm → Option (List Nat)
  | .app (.vc _ 0 _) _ => some []
  | .app (.vc _ 1 _) args => do
    let as := args.toList
    let c ← Prog.natOf nat (as.getD (as.length - 2) .nil)
    let rest ← P.strT nat (as.getD (as.length - 1) .nil)
    some (c :: rest)
  | _ => none

mutual
partial def Prog.showT (P : Prog) (nat : Option Nat) : Option Tm → Tm → String × Bool
  | some (.app (.tyc d ls) idx), v =>
    let lit : Option String :=
      if nat == some d then (Prog.natOf nat v).map toString
      else if nat.isSome && P.adtIs d "Char" then (Prog.natOf nat v).map showChar
      else if nat.isSome && P.adtIs d "String" then (P.strT nat v).map showStr
      else none
    match lit, P.adts[d]? with
    | some l, _ => (l, false)
    | none, some D =>
      let live := (List.range D.ctors.length).filter (!P.phantom d ·)
      if D.name == "Slot" || D.opq then ("_", false)
      else if D.newtype then match live with
        | [c] => match P.wrapField d c with
          | some k =>
            let n := (P.ownErs d c).length
            P.showCon nat (.app (.tyc d ls) idx) d c ((List.range n).map fun j => if j == k then v else .tok)
          | none => ("_", false)
        | _ => ("_", false)
      else if D.union && live.length > 1 then ("_", false)
      else match v with
        | .app (.vc d' c _) args => if d' == d then P.showCon nat (.app (.tyc d ls) idx) d c args.toList else (P.show nat v, false)
        | _ => (P.show nat v, false)
    | none, none => (P.show nat v, false)
  | _, v => (P.show nat v, v matches .app (.vc ..) _ || v matches .nat _)

partial def Prog.showCon (P : Prog) (nat : Option Nat) (T : Tm) (d c : Nat) (args : List Tm) : String × Bool :=
  let ers := P.ownErs d c
  let tys := P.fieldTys d c T
  let vs := args.zipIdx.map fun (v, k) => (v, ers.getD k false, (tys.getD k none))
  let shown := vs.zipIdx.map fun ((v, er, ty), k) =>
    if er then "_"
    else
      let (sv, ap) := P.showT nat ty v
      if k + 1 == vs.length && ap && sv.startsWith "(" then "$ " ++ (sv.drop 1).dropRight 1 else sv
  ("(" ++ " ".intercalate (P.name (.vc d c .nil) :: shown) ++ ")", true)
end

def Prog.typesOf : Tm → List Tm → List (Option Tm)
  | .bind k A r, v :: vs => (if k matches .ty .. && A != .nil then some A else none) :: Prog.typesOf (r.inst v 0) vs
  | _, vs => vs.map fun _ => none

def Prog.strD (P : Prog) : Option Nat := P.adts.findIdx? (·.name == "String")

def Prog.isStr (P : Prog) : Tm → Bool
  | .app (.tyc d _) _ => P.strD == some d
  | _ => false

def Prog.mkStr (P : Prog) (wrapped : Bool) (bytes : List Nat) : Tm := Id.run do
  let some sd := P.strD | return .nil
  let nat := P.nat.getD 0
  let lift (d : Nat) : Tm := .ofList (List.replicate (P.lifted d) .tok)
  let natT (n : Nat) : Tm := (List.range n).foldl (fun t _ => Tm.app (.vc nat 1 .nil) (.cons t .nil)) (.app (.vc nat 0 .nil) .nil)
  let ch (n : Nat) : Tm := match wrapped, P.adts.findIdx? (·.name == "Char"), P.adts.findIdx? (·.name == "U8") with
    | true, some chr, some u8 =>
      .app (.vc chr 0 (lift chr)) (.ofList [.app (.vc u8 0 (lift u8)) (.ofList [natT n, .tok])])
    | _, _, _ => natT n
  return bytes.foldr (fun b acc => .app (.vc sd 1 (lift sd)) (.ofList [ch b, acc])) (.app (.vc sd 0 (lift sd)) .nil)

inductive Out where
  | text (s : String)
  | io (k : List Nat → Except String (List Nat))
  | world (run : IO UInt32)

def Prog.adtNamed (P : Prog) (name : String) : Option Nat := P.adts.findIdx? (·.name == name)

def Prog.conS (P : Prog) (name ctor : String) (vals : List Tm) : Tm := Id.run do
  let some d := P.adtNamed name | return .tok
  let some c := ((P.adts[d]?).map (·.ctorNames.idxOf ctor)) | return .tok
  let rec fill : List Bool → List Tm → List Tm
    | true :: bs, vs => .tok :: fill bs vs
    | false :: bs, v :: vs => v :: fill bs vs
    | _, _ => []
  let fs := fill (P.ownErs d c) vals
  return match P.wrapField d c with
    | some k => fs.getD k .tok
    | none => .app (.vc d c .nil) (.ofList fs)

def Prog.fieldsS (P : Prog) : Tm → Option (String × List Tm)
  | .app (.vc d c _) args => do
    let n ← (P.adts[d]?).bind (·.ctorNames[c]?)
    some (n, (args.toList.zip (P.ownErs d c)).filterMap fun (a, e) => if e then none else some a)
  | _ => none

def Prog.perform (P : Prog) (req : Tm) : ExceptT String IO Tm := do
  let nat := P.nat
  let str (bs : List Nat) : Tm := P.mkStr false bs
  let ofStr (t : Tm) : ExceptT String IO String := match P.strT nat t with
    | some bs => pure (String.fromUTF8! (ByteArray.mk (bs.map (·.toUInt8)).toArray))
    | none => throw "runtime error: a request's text is not a String"
  let host (s : String) : Tm := str (s.toUTF8.toList.map (·.toNat))
  let unit := P.conS "Unit" "MkUnit" []
  let write (h : IO.FS.Stream) (t : Tm) : ExceptT String IO Tm := do
    h.putStr (← ofStr t); h.flush; pure unit
  let some (name, fs) := P.fieldsS req | throw "runtime error: a request is not a `Request`"
  match name, fs with
  | "WriteOut", [t] => write (← IO.getStdout) t
  | "WriteErr", [t] => write (← IO.getStderr) t
  | "ReadLine", [] =>
    let l ← (← IO.getStdin).getLine
    pure (if l.isEmpty then P.conS "Maybe" "None" [] else P.conS "Maybe" "Some" [host (l.dropRightWhile (· == '\n'))])
  | "ReadRemaining", [] => pure (str ((← (← IO.getStdin).readBinToEnd).toList.map (·.toNat)))
  | "GetEnv", [n] => pure (match ← IO.getEnv (← ofStr n) with
    | some v => P.conS "Maybe" "Some" [host v]
    | none => P.conS "Maybe" "None" [])
  | "GetCwd", [] => pure (host (← IO.currentDir).toString)
  | _, _ => throw s!"runtime error: the request `{name}` is not supported by the Lean runner"

partial def Prog.drive (P : Prog) (fuel : Nat) (k : Nat) (v : Tm) : ExceptT String IO UInt32 := do
  match P.fieldsS v with
  | some ("Exit", [code]) => match Prog.natOf P.nat code with
    | some n => pure n.toUInt32
    | none => throw "stuck: an exit code is not a number"
  | some ("Continue", [.clo env gid j]) =>
    let some G := P.groups[gid]? | throw "stuck"
    let some F := G.fns[j]? | throw "stuck"
    let outs ← runAM P (m := ExceptT String IO) (fun _ => throw "stuck") (fun _ r => P.perform r) fuel
      (env.toList ++ closures env.toList gid G ++ spread (F.tele.ers.take F.np) [Tm.wld k]).toArray F.body
    match outs.getLast? with
    | some next => P.drive fuel (k + 1) next
    | none => throw "stuck"
  | _ => throw "stuck: a `Program` is neither `Exit` nor `Continue`"

def Prog.thunk (P : Prog) (pre : Bool) : Tm → Except String (Option (List Tm × Group × FnDef))
  | .clo env gid j => match P.groups[gid]?, (P.groups[gid]?).bind (·.fns[j]?) with
    | some G, some F =>
      let ok := match F.np, F.tele with
        | 0, .bind (.ty _ false _) _ .nil => true
        | 1, .bind (.ty _ false _) A (.bind (.ty _ false _) B .nil) => pre && P.isStr A && P.isStr B
        | _, _ => false
      if ok then .ok (some (env.toList ++ closures env.toList gid G, G, F))
      else .error "error: a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`"
    | _, _ => .ok none
  | _ => .ok none

def Prog.showAll (P : Prog) (pre typed : Bool) (Ts : List (Option Tm)) (vs : List Tm) : String :=
  let nat := if pre then P.nat else none
  if typed then " ".intercalate ((vs.zip (Ts ++ vs.map fun _ => none)).map fun (v, T) => (P.showT nat T (P.unwrap v)).1)
  else " ".intercalate (vs.map (P.show nat))

def Prog.final (P : Prog) (pre typed wrapped : Bool) (R : List Tm → List (Option Tm)) (go : List Tm → Core → Option (List Tm))
    (res : Option (List Tm)) : Out :=
  let R := fun vs => (R (List.replicate P.hidden .tok ++ vs)).drop P.hidden
  match res.map (·.drop P.hidden) with
  | some [v] => match P.thunk pre v with
    | .ok (some (ρ, _, F)) =>
      if F.np = 1 then .io fun bytes => match go (ρ ++ [P.mkStr wrapped bytes]) F.body with
        | some [r] => match P.strT P.nat (P.unwrap r) with
          | some bs => .ok bs
          | none => .error "stuck: the result is not a String"
        | _ => .error "stuck"
      else match go ρ F.body with
        | some vs => .text (P.showAll pre typed (Prog.typesOf (F.tele.subst (Tm.env ρ)) vs) vs)
        | none => .text "stuck"
    | .ok none => .text (P.showAll pre typed (R [v]) [v])
    | .error e => .text e
  | some vs => .text (P.showAll pre typed (R vs) vs)
  | none => .text "stuck"

def Prog.isProgram (P : Prog) (pre : Bool) : Option (List Tm) → Bool
  | some [.app (.vc d _ _) _] => pre && P.adtNamed "Program" == some d
  | _ => false

def Prog.run (P : Prog) (pre typed : Bool) (R : List Tm → List (Option Tm)) : Out :=
  match eval P none [] 0 P.main with
  | .ok (vs, cnt) =>
    if P.isProgram pre (some (vs.drop P.hidden)) then .text "error: the full run does not drive a `Program`, which is not supported"
    else P.final pre typed true R (fun ρ c => match eval P none ρ cnt c with | .ok (vs, _) => some vs | .error _ => none) (some vs)
  | .error e => .text s!"stuck: {e}"

def Prog.runStripped (P : Prog) (pre : Bool) (R : List Tm → List (Option Tm)) : Out :=
  let res := runA P 100000000 #[] P.main
  let fin := P.final pre true false R (fun ρ c => runA P 100000000 ρ.toArray c) res
  match res.map (·.drop P.hidden) with
  | some [v] => if !P.isProgram pre (some [v]) then fin else .world do
    match ← (P.drive 100000000 0 v).run with
    | .ok n => pure n
    | .error e => IO.eprintln e; pure 1
  | _ => fin

def prelude : String := include_str "../prelude.sl"

def preludeFull : String := include_str "../prelude-full.sl"

def runProg (P : Prog) (mode : String) (pre : Bool) : Out :=
  match P.infer with
  | .error e => .text s!"error: {e}"
  | .ok P =>
    let P := P.fillCaps .nil
    if mode == "--unchecked" then P.run pre false fun _ => []
    else match checkProg P with
      | .error e => .text s!"refused: {e}"
      | .ok ⟨R, _⟩ =>
        if !P.usesOK R then .text "refused: the uses of a unique value do not check" else
        let rec anyTy : Tm → Bool
          | .bind (.ty ..) .nil _ => true
          | .bind _ _ r => anyTy r
          | _ => false
        let tys (vs : List Tm) := if anyTy R then
            match retTypes P {tys := #[]} P.main with
            | some Ts => Ts.map some
            | none => Prog.typesOf R vs
          else Prog.typesOf R vs
        if mode == "--full" then P.run pre true tys else P.runStripped pre tys

def dropFinal (items : List Sx) : List Sx := match items.reverse with
  | e@(.list (.atom h :: _)) :: rest => if statements.contains h then items else (rest.reverse ++ [.list [.atom "let", .list [.list [.atom "erased", .atom "_"]], e]])
  | e :: rest => if isPragmaSx e then items else rest.reverse ++ [.list [.atom "let", .list [.list [.atom "erased", .atom "_"]], e]]
  | [] => []

def runSources (srcs : List String) (mode : String) (pre : Bool) : List String × Out :=
  let pl := if pre then (if mode == "--full" || mode == "--unchecked" then preludeFull else prelude) ++ "\n(__prelude-end)\n" else ""
  let load (fin : Mode) : Except String (Prog × List String) := do
    let files ← srcs.mapM parse
    let items := (files.dropLast.map dropFinal).flatten ++ files.getLastD []
    elabProgram ((← parse pl) ++ items) pre fin
  let run : Except String (Prog × List String) → List String × Out
    | .error e => ([], .text s!"error: {e}")
    | .ok (P, ws) => (ws, runProg P mode pre)
  let many := load .many
  let first := run many
  let isWorld (o : Out) : Bool := o matches .world _
  if !(isWorld first.2 || many matches .error _) then first else
  let r := run (load .uniq)
  if isWorld r.2 || isWorld first.2 then r else first
def runSource (src : String) (mode : String) (pre : Bool) : List String × Out := runSources [src] mode pre

end Minimal
