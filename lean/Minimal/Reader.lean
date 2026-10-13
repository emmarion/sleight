import Minimal.Infer

namespace Minimal

inductive Sx where
  | atom (s : String)
  | list (xs : List Sx)
  deriving Repr, Inhabited, BEq

partial def Sx.show : Sx → String
  | .atom a => a
  | .list xs => "(" ++ " ".intercalate (xs.map Sx.show) ++ ")"

partial def Sx.numerals : Sx → List Nat
  | .atom a => if !a.isEmpty && a.all Char.isDigit && (a == "0" || !a.startsWith "0") then [a.toNat!] else []
  | .list xs => xs.flatMap Sx.numerals

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

partial def readStr : List Char → List Char → Except String (List Char × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: rest, acc => .ok (acc.reverse, rest)
  | '\\' :: c :: rest, acc => match c with
    | 'n' => readStr rest ('\n' :: acc)
    | 't' => readStr rest ('\t' :: acc)
    | '"' => readStr rest ('"' :: acc)
    | '\\' => readStr rest ('\\' :: acc)
    | 'x' => match rest with
      | a :: b :: rest => match hexVal a, hexVal b with
        | some x, some y => readStr rest (Char.ofNat (16 * x + y) :: acc)
        | _, _ => .error "malformed \\x escape"
      | _ => .error "malformed \\x escape"
    | c => .error s!"unknown escape \\{c}"
  | c :: rest, acc => readStr rest (c :: acc)

def charCode (a : String) : Option Nat :=
  if !a.startsWith "#\\" then none else
  match a.toList.drop 2 with
  | [c] => some c.toNat
  | ['x', h1, h2] => do let x ← hexVal h1; let y ← hexVal h2; some (16 * x + y)
  | cs => match String.ofList cs with
    | "space" => some 32
    | "newline" => some 10
    | "tab" => some 9
    | _ => none

def numeralOf : Sx → Option Nat
  | e@(.atom _) => match e.numerals with
    | [n] => some n
    | _ => none
  | _ => none

def litOf : Sx → Option Nat
  | .atom a => match (Sx.atom a).numerals with
    | [n] => some n
    | _ => charCode a
  | _ => none

def ffiNames : List String :=
  let src := include_str "../../lib/ffi.ml"
  let seg := ((src.splitOn "let types").getD 1 "").splitOn "let plain_shapes" |>.headD ""
  let parts := seg.splitOn "\""
  (List.range (parts.length / 2)).filterMap fun k =>
    let before := (parts.getD (2 * k) "").trimAsciiEnd.toString
    let after := parts.getD (2 * k + 2) ""
    if before.endsWith "(" && after.startsWith "," then some (parts.getD (2 * k + 1) "") else none

def ffiArity (name : String) : Option Nat :=
  let src := include_str "../../lib/ffi.ml"
  let num (t : String) : Option Nat :=
    let t := (t.drop 4).trimAsciiStart.toString
    let t := if t.startsWith "~needs:[" then ((t.splitOn "]").drop 1 |> String.intercalate "]").trimAsciiStart.toString else t
    (String.ofList (t.toList.takeWhile Char.isDigit)).toNat?
  match (src.splitOn ("(\"" ++ name ++ "\",")).drop 1 |>.head? with
  | some rest =>
    let t := rest.trimAsciiStart.toString
    if t.startsWith "spec" then num t
    else
      let id := String.ofList (t.toList.takeWhile fun c => c.isAlphanum || c == '_')
      match (src.splitOn ("let " ++ id ++ " = ")).drop 1 |>.head? with
      | some d => if d.startsWith "spec" then num d else none
      | none => none
  | none => none

def specialNames : List String :=
  ["let", "def-lvl", "def-fns", "def-unique", "def-adts", "comptime-match", "let-match", "open-adt", "slot-self",
   "open-at-fn", "unary", "dump-context", "compile-error", "compile-warn", "Fn", "UniqueFn", "TyCtor", "ValCtor",
   "Matchable", "Cell", "match", "values", "coerce", "share", "cell-alloc", "cell-write", "cell-match",
   "open-absurd", "world-do", "settled-of", "settled-type", "settled-erase", "settled-mult", "settled-value",
   "gensym", "settled-eq", "intern-nat", "intern-char", "intern-string", "resolve", "read-file", "place-at",
   "place-at-many", "unplace-at", "unplace-at-many", "placed-slot", "placed-eq", "at",
   "prove-subterm", "prove-predates", "predates-trans", "subterm-trans", "predates-subterm", "gensym-unique",
   "coercible-refl", "coercible-sym", "coercible-trans", "coercible-share", "coercible-wrap", "coercible-ctor",
   "coercible-of", "prove-literal-lt", "level-of", "matchable-of", "delegate-of", "numeral-of", "slot-of",
   "at-fn-of", "erased", "many", "unique", ":", "is", "->", "subterm", "predates", "enum", "union", "newtype",
   "extern", "absurd", "tail", "notail", "delegate", "else"]

def plainName (s : String) : Bool :=
  !s.isEmpty && s != "_" && s != "$" && !s.all Char.isDigit && !s.startsWith "#" && !s.startsWith "\"" &&
    !s.startsWith "__" && s.all fun c => !c.isWhitespace && c != '(' && c != ')' && c != ';' && 32 < c.toNat && c.toNat < 127

def rawName (s : String) : String := if plainName s then s else "\x01" ++ s

partial def tokenize (cs : List Char) (acc : List String) : Except String (List String) :=
  match cs with
  | [] => .ok acc.reverse
  | ';' :: '!' :: rest => let l := rest.takeWhile (· != '\n'); tokenize (rest.drop l.length) ((";!" ++ String.ofList l) :: acc)
  | ';' :: rest => tokenize (rest.dropWhile (· != '\n')) acc
  | '"' :: rest => do let (s, rest) ← readStr rest []; tokenize rest (("\"" ++ String.ofList s) :: acc)
  | '#' :: '"' :: rest => do let (s, rest) ← readStr rest []; tokenize rest (rawName (String.ofList s) :: acc)
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc
    else if c == '(' || c == ')' then tokenize rest (c.toString :: acc)
    else
      let w := cs.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')' && c != ';'
      tokenize (cs.drop w.length) (String.ofList w :: acc)

def isPragma (s : String) : Bool := s.startsWith ";!"

partial def parseItems : List String → Except String (List Sx × List String)
  | [] => .ok ([], [])
  | ")" :: rest => .ok ([], ")" :: rest)
  | "(" :: rest => do
    let (xs, rest) ← parseItems rest
    match rest with
    | ")" :: rest => let (ys, rest) ← parseItems rest; .ok (.list xs :: ys, rest)
    | _ => .error "missing )"
  | "$" :: rest => do
    let (xs, rest) ← parseItems rest
    .ok ([.list xs], rest)
  | a :: rest => do let (ys, rest) ← parseItems rest; .ok (.atom a :: ys, rest)

def isPragmaSx : Sx → Bool
  | .atom a => isPragma a
  | _ => false

def bytes (s : String) : List Char := s.toUTF8.toList.map (Char.ofNat ·.toNat)

def parse (src : String) : Except String (List Sx) := do
  match ← parseItems (← tokenize (bytes src) []) with
  | (xs, []) => .ok xs
  | _ => .error "unbalanced )"

inductive Mode where
  | er
  | many
  | uniq
  deriving BEq, Inhabited, Repr

def Mode.isEr : Mode → Bool
  | .er => true
  | _ => false

instance : Coe Bool Mode := ⟨fun b => if b then .er else .many⟩

def Ent.md (k : Ent) : Mode := if k.er then .er else if k.u then .uniq else .many

inductive Ref where
  | fv (i : Nat)
  | bnd (lv : Nat)
  | fn (i lvl : Nat) (ers : List Mode)
  | ctor (i : Nat)

structure ESt where
  n : Nat := 0
  ers : List Bool := []
  ghost : Bool := false
  top : Bool := true
  rhs : Bool := true
  lits : List (Nat × Nat) := []
  pre : Bool := true
  inPrelude : Bool := true
  tail : Bool := false
  refute : Bool := false
  known : List (Nat × Tm) := []
  inl : List (Nat × Tm) := []
  lifts : List (Nat × List Nat) := []
  adts : List (String × Nat) := []
  ctors : List (String × Nat × Nat) := []
  decls : List Adt := []
  groups : List Group := []
  opened : List Nat := []
  dele : Option (Nat × List (Nat × Bool)) := none
  delegated : Bool := false
  deles : List (Nat × Nat) := []
  delePf : List (Nat × Nat) := []
  renames : List (Nat × Nat) := []
  prims : List (String × Tm × Nat) := []
  uq : List Nat := []
  sides : List (Nat × Option Mode × Option Mode) := []
  uses : List (Nat × Bool) := []
  captures : Nat := 0
  warns : List String := []
  pwarn : List (Tm × String) := []
  supp : List (String × Option Tm × Nat) := []
  vals : List Tm := []
  facts : List (Nat × Tm) := []
  chars : List (Nat × Nat) := []
  strs : List (List Nat × Nat) := []
  numPf : List (Nat × Nat) := []
  ltPf : List ((Nat × Nat) × Nat) := []
  eqPf : List ((Nat × Option Nat) × Nat) := []
  u8mod : Option Nat := none
  special : Nat := 0
  depthTop : Bool := true
  mtbls : List (Nat × Nat) := []
  topCtx : Option Ctx := some {tys := []}
  claimed : List String := []

abbrev M := StateT ESt (Except String)

def ESt.settledVal (st : ESt) (i : Nat) : Option Tm :=
  if i < st.vals.length && !(st.ers.getD i true) then st.vals[i]? else none

def ESt.firstAdt (st : ESt) (name : String) : Option Nat := st.decls.findIdx? (·.name == name)

partial def ESt.factCanon (st : ESt) : Nat → Tm → Tm
  | 0, t => t
  | k + 1, .fv j => match st.facts.lookup j with
    | some t => st.factCanon k t
    | none => .fv j
  | _, t => t

def ESt.mintedSpecial (st : ESt) (i : Nat) : Bool :=
  match st.inl.lookup i, ((st.known.filter (·.1 == i)).getLast?).map (·.2), st.topCtx with
  | some (.app (.vc d _ _) .nil), _, _ => d == st.special
  | _, _, some Γ => ((Γ.tys[i]?).map Γ.canon) == some (.app (.tyc st.special .nil) .nil)
  | _, some T, none => st.factCanon 100 T == .app (.tyc st.special .nil) .nil
  | _, _, _ => false

def warn (msg : String) : M Unit := modify fun st => { st with warns := st.warns ++ [msg] }

def warnUse (t : Tm) (kind shown : String) : M Unit := do
  let t := match t with | .vc d c _ => .vc d c .nil | .tyc d _ => .tyc d .nil | t => t
  let st ← get
  if st.inPrelude then return
  let some (_, msg) := st.pwarn.find? (·.1 == t) | return
  match st.supp.findIdx? (·.2.1 == some t) with
  | some k => set { st with supp := st.supp.modify k fun (x, y, n) => (x, y, n + 1) }
  | none => warn (if kind == "match" then s!"match on `{shown}`: {msg}" else s!"{kind} of `{shown}`: {msg}")

def primNames : List String :=
  ["gensym", "gensym-unique", "settled-type", "settled-erase", "settled-mult", "settled-value", "settled-eq", "intern-nat",
   "intern-char", "intern-string", "resolve", "read-file", "place-at", "place-at-many", "unplace-at", "unplace-at-many",
   "placed-slot", "placed-eq"]

def keywords : List String := specialNames ++ ["Type", "Level", "Predates", "Subterm"]

def showName (x : String) : String :=
  if x.startsWith "\x01" then
    "#\"" ++ String.join ((x.toList.drop 1).map fun c =>
      if c == '"' || c == '\\' then "\\" ++ c.toString
      else if 32 ≤ c.toNat && c.toNat < 127 then c.toString
      else "\\x" ++ String.ofList (Nat.toDigits 16 c.toNat |>.reverse |>.take 2 |>.reverse |> fun ds =>
        if ds.length < 2 then '0' :: ds else ds)) ++ "\""
  else x

abbrev Scope := List (String × Ref)

def ESt.liftTm (st : ESt) (d : Nat) : Tm := .ofList (((st.lifts.lookup d).getD []).map Tm.fv)

def look (sc : Scope) (depth : Nat) (x : String) : M Tm := do
  if x == "_" then return .hole
  match sc.lookup x with
  | some (.fv i) | some (.fn i _ _) | some (.ctor i) => pure (.fv i)
  | some (.bnd lv) => pure (.bv (depth - 1 - lv))
  | none => do
    let st ← get
    match st.adts.lookup x, st.ctors.lookup x with
    | some d, _ => pure (.tyc d (st.liftTm d))
    | _, some (d, c) => pure (.vc d c (st.liftTm d))
    | _, _ =>
      match specialNames.idxOf? x with
      | some c => if st.decls.length > 0 then pure (.app (.vc st.special c .nil) .nil) else throw s!"unbound name {showName x}"
      | none => throw s!"unbound name {showName x}"

def refOf (sc : Scope) (i : Nat) : Ref :=
  (sc.findSome? fun
    | (_, .fn j l ms) => if j == i then some (Ref.fn j l ms) else none
    | (_, .ctor j) => if j == i then some (Ref.ctor j) else none
    | _ => none).getD (.fv i)

def isCtorTy : Tm → Bool
  | .tyCtor _ | .valCtor _ => true
  | _ => false

def entRef (i : Nat) (T : Tm) : Ref := if isCtorTy T then .ctor i else .fv i

def teleTys : Tm → List Tm
  | .bind _ A r => A :: teleTys r
  | _ => []

def levelOf (sc : Scope) (f : String) : M Nat := do
  match sc.lookup f with
  | some (.fn _ l _) => pure l
  | some (.fv i) | some (.ctor i) => match (← get).known.lookup i with
    | some (.fn (.fv l) _ _ _) => pure l
    | _ => throw s!"level-of: the level of {f} is not known"
  | _ => throw s!"level-of: {f} is not a function in scope"

def splitMd (need : Bool := true) : List Sx → M (Mode × List Sx)
  | .atom "erased" :: xs => pure (.er, xs)
  | .atom "many" :: xs => pure (.many, xs)
  | .atom "unique" :: xs => pure (.uniq, xs)
  | xs => if need then throw "a multiplicity is required" else pure (.many, xs)

def splitMult (need : Bool := true) (xs : List Sx) : M (Bool × List Sx) := do
  let (m, xs) ← splitMd need xs
  pure (m.isEr, xs)

def splitArrow (xs : List Sx) : M (List Sx × List Sx) :=
  match xs.idxOf? (.atom "->") with
  | some k => pure (xs.take k, xs.drop (k + 1))
  | none => throw "missing ->"

def name : Sx → M String
  | .atom x =>
    if x ∈ ["erased", "many", "unique", "is", ":", "->", "$"] || x.all Char.isDigit || x.startsWith "\"" ||
        x.startsWith "#\\" || isPragma x then throw s!"{x} is not a name"
    else if x.startsWith "__" then throw s!"{x} begins with __, which is reserved"
    else do
      if x ∈ keywords then warn s!"declaration of `{x}` shadows a built-in"
      pure x
  | _ => throw "malformed name"

def parseEntry (need : Bool) : Sx → M (Ent × Sx × List String)
  | .list xs => do
    if xs.contains (.atom "at") then throw "at is not supported"
    let (sub, xs) := match xs with | .atom "subterm" :: xs => (true, xs) | xs => (false, xs)
    let (m, xs) ← splitMd need xs
    match xs with
    | [e, .atom "is", x] => pure (.is sub m.isEr (m == .uniq), e, [← name x])
    | T :: x :: xs => pure (.ty sub m.isEr (m == .uniq), T, ← (x :: xs).mapM name)
    | _ => throw "malformed telescope entry"
  | _ => throw "malformed telescope entry"

def entryErs (need : Bool) (es : List Sx) : M (List (String × Bool)) :=
  es.flatMapM fun e => do let (k, _, xs) ← parseEntry need e; pure (xs.map (·, k.er))

def entryMds (need : Bool) (es : List Sx) : M (List Mode) :=
  es.flatMapM fun e => do let (k, _, xs) ← parseEntry need e; pure (xs.map fun _ => k.md)

def teleMds : Tm → List Mode
  | .bind k _ r => k.md :: teleMds r
  | _ => []

def Ent.withEr : Ent → Bool → Ent
  | .ty m _ u, e => .ty m e u
  | .is m _ u, e => .is m e u

def setErs : Tm → List Bool → Tm
  | .bind k A r, e :: es => .bind (k.withEr e) A (setErs r es)
  | t, _ => t

def fieldMds : Tm → List Mode
  | .bind k _ r@(.bind ..) => k.md :: fieldMds r
  | _ => []

def fieldErs : Tm → List Bool
  | .bind k _ r@(.bind ..) => k.er :: fieldErs r
  | _ => []

def resolveHead (sc : Scope) (use : Nat → M Unit) : Sx → M Sx
  | e@(.list (.atom h :: args)) => do
    let st ← get
    match sc.lookup h with
    | some r =>
      let i := match r with | .fv i | .fn i _ _ | .ctor i => some i | _ => none
      match i.bind st.settledVal with
      | some (.app (.vc d c _) _) =>
        if d == st.special && st.decls.length > 0 && (i.map st.mintedSpecial).getD false then
          let s := specialNames.getD c ""
          if (sc.lookup s).isSome then throw s!"the special form {s} is shadowed where {showName h} dispatches to it"
          if let some i := i then use i
          return .list (.atom s :: args)
        else if h ∈ keywords then return .list (.list [.atom "\x03var", .atom h] :: args) else return e
      | _ => if h ∈ keywords then return .list (.list [.atom "\x03var", .atom h] :: args) else return e
    | none => return e
  | e => return e

partial def natOfVal : Tm → Option Nat
  | .app (.vc _ 0 _) .nil => some 0
  | .app (.vc _ 1 _) (.cons x .nil) => (natOfVal x).map (· + 1)
  | _ => none

def ESt.adtName (st : ESt) (d : Nat) : String := ((st.decls[d]?).map (·.name)).getD ""

partial def ESt.strOfVal (st : ESt) : Tm → Option (List Char)
  | .app (.vc d 0 _) _ => if st.firstAdt "String" == some d then some [] else none
  | .app (.vc d 1 _) args => do
    if st.firstAdt "String" != some d then none
    let as := args.toList
    let n ← natOfVal as[as.length - 2]!
    let rest ← st.strOfVal as.getLast!
    some (Char.ofNat n :: rest)
  | _ => none

def compileMsg (sc : Scope) : Sx → M String
  | .atom a => do
    if a.startsWith "\"" then return String.ofList (a.toList.drop 1)
    let st ← get
    let i := match sc.lookup a with | some (.fv i) | some (.fn i _ _) | some (.ctor i) => some i | _ => none
    match (i.bind st.settledVal).bind st.strOfVal with
    | some cs => return String.ofList cs
    | none => throw s!"the message of compile-error or compile-warn must be a Settled, non-erased String; `{showName a}` is not one"
  | _ => throw "the message of compile-error or compile-warn must be a Settled, non-erased String"

mutual
partial def ESt.showTm (st : ESt) (nm : Nat → String) : Tm → String
  | .fv i => nm i
  | .bv k => s!"#{k}"
  | .univ => "Type"
  | .level => "(Level)"
  | .tyc d _ => showName ((st.decls[d]?).map (·.name) |>.getD s!"T{d}")
  | .vc d c _ => showName (((st.decls[d]?).bind (·.ctorNames[c]?)).getD s!"C{d}.{c}")
  | .app h args => "(" ++ " ".intercalate (st.showTm nm h :: args.toList.map (st.showTm nm)) ++ ")"
  | .predates A x L => s!"(Predates {st.showTm nm A} {st.showTm nm x} {st.showTm nm L})"
  | .subterm A a B b => s!"(Subterm {st.showTm nm A} {st.showTm nm a} {st.showTm nm B} {st.showTm nm b})"
  | .fn l np t u => s!"({if u then "UniqueFn" else "Fn"} {st.showTm nm l} {st.showTele nm np t})"
  | .tyCtor t => s!"(TyCtor {st.showTele nm t.len t} Type)"
  | .valCtor t => s!"(ValCtor {st.showTele nm (t.len - 1) t})"
  | .mtbl u nt ex ph T cs =>
    let marks := (if nt then " newtype" else "") ++ (if ex then " extern" else "")
    let es := (cs.toList.zipIdx.map fun (c, k) => s!"({if ph.getD k false then "erased" else "many"} {st.showTm nm c})")
    s!"(Matchable {if u then "union" else "enum"}{marks} {st.showTm nm T}" ++ String.join (es.map (" " ++ ·)) ++ ")"
  | .nil => "_"
  | _ => "_"

partial def ESt.showTele (st : ESt) (nm : Nat → String) (np : Nat) : Tm → String
  | t =>
    let rec go (k : Nat) : Tm → List String
      | .bind e A r =>
        let m := if e.er then "erased" else "many"
        let ent := match e with
          | .ty .. => s!"({m} {st.showTm nm A} _)"
          | .is .. => s!"({m} {st.showTm nm A} is _)"
        (if k == np then ["->", ent] else [ent]) ++ go (k + 1) r
      | _ => if k == np then ["->"] else []
    " ".intercalate (go 0 t)
end

def dumpContext (sc : Scope) : M String := do
  let st ← get
  let named := (sc.filter (!·.1.startsWith " ")).filterMap fun (x, r) => match r with
    | .fv i | .fn i _ _ | .ctor i => some (x, i)
    | .bnd _ => none
  let nm (i : Nat) : String := ((named.find? (·.2 == i)).map (showName ·.1)).getD s!"__{i}"
  let seen := named.foldl (fun (acc : List (String × Nat)) (x, i) => if acc.any (·.1 == x) then acc else acc ++ [(x, i)]) []
  let lines := seen.map fun (x, i) =>
    let ty := match st.known.lookup i <|> (st.topCtx.bind fun Γ => (Γ.tys[i]?).filter (· != .nil)) with
      | some T => " : " ++ st.showTm nm T
      | none => ""
    let mult := if st.ers.getD i true then "erased" else "many"
    let state := if i < st.vals.length then "Settled" else "Hypothetical"
    let rule := match st.inl.lookup i with
      | some t => s!"; is {st.showTm nm t}"
      | none => ""
    s!"{showName x}{ty}  [{mult}, {state}{rule}]"
  let where_ := if st.top then "in run position: binders here are Settled once their form has run"
    else "inside a function body or a match branch: binders here are Hypothetical"
  return "`dump-context` stops elaboration here and reports what the checker knows\n" ++ where_ ++
    String.join (lines.map ("\n" ++ ·))

mutual
partial def elabTm (sc : Scope) (depth : Nat) (e : Sx) : M Tm := do
  match ← resolveHead sc (fun _ => pure ()) e with
  | .list [.atom "\x03var", .atom x] => look sc depth x
  | .list (.list [.atom "\x03var", .atom x] :: args) =>
    return .app (← look sc depth x) (.ofList (← args.mapM (elabTm sc depth)))
  | e => elabTm' sc depth e

partial def elabTm' (sc : Scope) (depth : Nat) : Sx → M Tm
  | .atom "Type" => pure .univ
  | .list [.atom "compile-error", m] => do throw (← compileMsg sc m)
  | .list [.atom "dump-context"] => do throw (← dumpContext sc)
  | e@(.atom x) => match e.numerals with
    | [n] => do match (← get).lits.lookup n with
      | some i => pure (.fv i)
      | none => throw s!"the numeral {x} is not interned"
    | _ =>
      if x.startsWith "\"" then do
        match (← get).strs.lookup ((x.toList.drop 1).map Char.toNat) with
        | some i => pure (.fv i)
        | none => throw s!"the string literal {x} is not interned"
      else match charCode x with
        | some c => do match (← get).chars.lookup c with
          | some i => pure (.fv i)
          | none => throw s!"the character literal {x} is not interned"
        | none => if x.startsWith "#\\" then throw s!"malformed character literal {x}" else look sc depth x
  | .list [.atom "numeral-of", x] => do
    match litOf x with
    | some n => match (← get).numPf.lookup n with
      | some i => pure (.fv i)
      | none => throw "numeral-of: not interned"
    | none => throw "`numeral-of` takes a numeral or a character literal"
  | .list (.atom "numeral-of" :: _) => throw "malformed `numeral-of` form"
  | .list [.atom "prove-literal-lt", a, b] => do
    match numeralOf a, numeralOf b with
    | some x, some y => match (← get).ltPf.lookup (x, y) with
      | some i => pure (.fv i)
      | none => throw s!"prove-literal-lt: {x} is not below {y}"
    | _, _ => throw "`prove-literal-lt` takes two numerals"
  | .list (.atom "prove-literal-lt" :: _) => throw "`prove-literal-lt` takes two numerals"
  | .list [.atom "Level"] => pure .level
  | .list [.atom "matchable-of", .atom T] => do
    let st ← get
    let some d := st.adts.lookup T | throw s!"matchable-of: {T} is not a declared type"
    match st.mtbls.lookup d with
    | some i => pure (.fv i)
    | none => throw s!"matchable-of: {T} mentions top-level entries and is not first class"
  | .list (.atom "matchable-of" :: _) => throw "matchable-of takes a type constructor"
  | .list [.atom "level-of", .atom f] => return .fv (← levelOf sc f)
  | .list [.atom "delegate-of", .atom f] => do
    let pf := (← get).delePf
    match (match sc.lookup f with | some (.fv i) | some (.fn i _ _) => pf.lookup i | _ => none) with
    | some k => pure (.fv k)
    | none => throw s!"delegate-of: {showName f} is not a non-erased function with a `delegate` body defined before this type"
  | .list [.atom "Predates", A, x, L] =>
    return .predates (← elabTm sc depth A) (← elabTm sc depth x) (← elabTm sc depth L)
  | .list [.atom "Subterm", A, a, B, b] =>
    return .subterm (← elabTm sc depth A) (← elabTm sc depth a) (← elabTm sc depth B) (← elabTm sc depth b)
  | .list (.atom "Fn" :: l :: es) => elabFn sc depth l es false
  | .list (.atom "UniqueFn" :: l :: es) => elabFn sc depth l es true
  | .list (.atom "Matchable" :: .atom tag :: rest) => do
    unless tag == "enum" || tag == "union" do throw "Matchable: the tag is enum or union"
    let (marks, T :: es) := rest.span (· matches .atom "newtype" | .atom "extern") | throw "Matchable: no type constructor"
    let es ← es.mapM fun
      | .list [.atom m, C] => do
        let (er, _) ← splitMult true [.atom m]
        pure (er, ← elabTm sc depth C)
      | _ => throw "Matchable: an entry is (m C)"
    return .mtbl (tag == "union") (marks.contains (.atom "newtype")) (marks.contains (.atom "extern")) (es.map (·.1))
      (← elabTm sc depth T)
      (.ofList (es.map (·.2)))
  | .list (.atom "TyCtor" :: es) => do
    let (ps, [.atom "Type"]) ← splitArrow es | throw "a TyCtor returns Type"
    return .tyCtor (← elabTele sc depth false ps)
  | .list (.atom "ValCtor" :: es) => do
    let (fs, [ret]) ← splitArrow es | throw "a ValCtor has one return"
    return .valCtor (← elabTele sc depth true (fs ++ [.list [.atom "many", ret, .atom "_"]]))
  | .list (.atom h :: args) => do
    let st ← get
    let args ← args.mapM (elabTm sc depth)
    let lift d := ((st.lifts.lookup d).getD []).map Tm.fv
    match sc.lookup h, st.adts.lookup h, st.ctors.lookup h with
    | none, some d, _ => pure (.app (.tyc d (.ofList (lift d))) (.ofList args))
    | none, _, some (d, c) => pure (.app (.vc d c (.ofList (lift d))) (.ofList args))
    | some _, _, _ => pure (.app (← look sc depth h) (.ofList args))
    | _, _, _ => throw s!"{h} is not a type or constructor, in a type"
  | e => throw s!"malformed term {e.show.take 40}"

partial def elabFn (sc : Scope) (depth : Nat) (l : Sx) (es : List Sx) (u : Bool) : M Tm := do
  let l ← elabTm sc depth l
  let (ps, rs) ← splitArrow es
  let t ← elabTele sc depth true (ps ++ rs)
  return .fn l (← entryErs true ps).length t u

partial def elabTele (sc : Scope) (depth : Nat) (need : Bool) : List Sx → M Tm
  | [] => pure .nil
  | e :: es => do
    let (k, T, xs) ← parseEntry need e
    let Ts ← (List.range xs.length).mapM fun j => elabTm sc (depth + j) T
    let sc := xs.zipIdx.foldl (fun sc (x, j) => (x, .bnd (depth + j)) :: sc) sc
    let r ← elabTele sc (depth + xs.length) need es
    return Ts.foldr (.bind k) r
end

def fresh (ms : List Bool) : M (List Nat) :=
  modifyGet fun st => (List.range' st.n ms.length, { st with n := st.n + ms.length, ers := st.ers ++ ms })

def freshMd (ms : List Mode) : M (List Nat) := do
  let is ← fresh (ms.map (·.isEr))
  modify fun st => { st with uq := st.uq ++ (is.zip ms).filterMap fun (i, m) => if m == .uniq then some i else none }
  return is

def reset (base : Nat) : M Unit := modify fun st =>
  { st with n := base, ers := st.ers.take base, known := st.known.filter (·.1 < base),
            inl := st.inl.filter (·.1 < base), opened := st.opened.filter (· < base),
            uq := st.uq.filter (· < base), uses := st.uses.filter (·.1 < base),
            sides := st.sides.filter (·.1 < base), deles := st.deles.filter (·.1 < base),
            delePf := st.delePf.filter (·.2 < base), renames := st.renames.filter (·.1 < base) }

def liftTm (d : Nat) : M Tm := return (← get).liftTm d

def note (i : Nat) (T : Tm) (isTerm : Bool := false) : M Unit := modify fun st =>
  if isTerm then { st with inl := (i, T) :: st.inl } else { st with known := (i, T) :: st.known }

def abst (ids : List Nat) : Nat → Tm → Tm
  | D, .fv i => match ids.idxOf? i with
    | some k => .bv (D - 1 - k)
    | none => .fv i
  | D, .tyc d ls => .tyc d (abst ids D ls)
  | D, .vc d c ls => .vc d c (abst ids D ls)
  | D, .cons h t => .cons (abst ids D h) (abst ids D t)
  | D, .bind k a r => .bind k (abst ids D a) (abst ids (D + 1) r)
  | D, .app h a => .app (abst ids D h) (abst ids D a)
  | D, .tyCtor p => .tyCtor (abst ids D p)
  | D, .valCtor p => .valCtor (abst ids D p)
  | D, .predates A x L => .predates (abst ids D A) (abst ids D x) (abst ids D L)
  | D, .subterm A a B b => .subterm (abst ids D A) (abst ids D a) (abst ids D B) (abst ids D b)
  | D, .fn l np t u => .fn (abst ids D l) np (abst ids D t) u
  | _, t => t

def teleAppend : Tm → Tm → Tm
  | .bind k a r, t => .bind k a (teleAppend r t)
  | _, t => t

def declareAdts (sc : Scope) (blocks : List Sx) : M Unit := do
  let heads ← blocks.mapM fun (b : Sx) => match b with
    | .list (.list (T :: .atom ":" :: es) :: kws) => do
      let (ps, [.atom "Type"]) ← splitArrow es | throw "a type constructor returns Type"
      let (kw, cs) := kws.span (· matches .atom _)
      unless (kw.filter (· matches .atom "enum" | .atom "union")) matches [.atom "enum"] | [.atom "union"] do
        throw "a type is declared enum or union"
      let cs ← cs.mapM fun
        | .list xs => do
          let (p, xs) ← splitMult true xs
          let C :: .atom ":" :: es := xs | throw "malformed constructor"
          let (fs, [ret]) ← splitArrow es | throw "a constructor has one return"
          pure (p, ← name C, fs, ret)
        | _ => throw "malformed constructor"
      pure (← name T, ps, cs)
    | _ => throw "malformed def-adts"
  let st ← get
  let base := st.decls.length
  let mut ctors := st.ctors
  for ((_, _, cs), j) in heads.zipIdx do
    for (c, ci) in cs.zipIdx do
      ctors := (c.2.1, base + j, ci) :: ctors
  set { st with adts := (heads.zipIdx.map fun ((h : String × List Sx × List (Bool × String × List Sx × Sx)), j) => (h.1, base + j)).reverse ++ st.adts, ctors }
  let inline (t : Tm) : Tm := (List.range st.inl.length).foldl
    (fun t _ => t.subst fun i => (st.inl.lookup i).getD (.fv i)) t
  let elabSigs := heads.mapM fun (_, ps, cs) => do
    let params ← elabTele sc 0 false ps
    let sigs ← cs.mapM fun (_, _, fs, ret) => elabTele sc 0 true (fs ++ [.list [.atom "many", ret, .atom "_"]])
    pure (inline params, sigs.map inline)
  let raw ← elabSigs
  let mut ids : List Nat := ((raw.flatMap fun (p, ss) => p.fvs ++ ss.flatMap Tm.fvs).filter (· < holeBase)).eraseDups
  let tyOf (i : Nat) : Option Tm := st.known.lookup i <|>
    (st.topCtx.bind fun Γ => (Γ.tys[i]?).filter (· != .nil))
  for _ in List.range (st.n + 1) do
    let more ← ids.flatMapM fun i => match tyOf i with
      | some T => pure (inline T).fvs
      | none => throw "a def-adts signature may mention only an entry whose type the elaborator knows: a top-level entry, a level, a def-fns function, a parameter, or a let binder written with a type or a term"
    ids := (ids ++ more).eraseDups
  ids := ids.mergeSort
  let liftTele := ids.zipIdx.foldr (fun (i, k) r =>
    .bind (.ty false true false) (abst ids k (inline ((tyOf i).getD .nil))) r) .nil
  modify fun st => { st with lifts := (heads.zipIdx.map fun (_, j) => (base + j, ids)) ++ st.lifts }
  if !(← get).inPrelude && blocks.any (fun | .list (_ :: kws) => kws.contains (.atom "extern") | _ => false) then
    throw "only the prelude may mark a definition `extern`"
  for (b, (T, _, _)) in blocks.zip heads do
    if let .list (_ :: kws) := b then
      if kws.contains (.atom "extern") then
        unless ffiNames.contains T do throw s!"no extern implementation for `{showName T}`"
        if (← get).claimed.contains T then throw s!"`{showName T}` is already bound to its extern implementation by another declaration"
        modify fun st => { st with claimed := T :: st.claimed }
  let kinds := blocks.map fun
    | .list (_ :: kws) => (kws.contains (.atom "union"), kws.contains (.atom "newtype"), kws.contains (.atom "extern"))
    | _ => (false, false, false)
  for (((T, _, cs), (params, sigs)), (union, newtype, extern)) in (heads.zip (← elabSigs)).zip kinds do
    let real := (cs.zip sigs).filter (!·.1.1)
    if newtype && (real.isEmpty || (!union && real.length != 1) ||
        real.any fun (_, sig) => (fieldErs sig).count false != 1) then
      throw s!"{T} does not have newtype shape"
    let ctorNames := cs.map (·.2.1)
    let adt : Adt := { params := teleAppend liftTele (abst ids ids.length params),
                       ctors := sigs.map (fun s => teleAppend liftTele (abst ids ids.length s)), name := T, ctorNames,
                       lifted := ids.length, phantom := cs.map (·.1), union, newtype, extern }
    modify fun st => { st with decls := st.decls ++ [adt] }

def withTail {α : Type} (b : Bool) (x : M α) : M α := do
  let t0 := (← get).tail
  modify fun st => { st with tail := b }
  let r ← x
  modify fun st => { st with tail := t0 }
  return r

def returnsBinders (xs : List String) (want : List Mode) : List Sx → Bool
  | [.list (.atom "values" :: es)] => (es.zip want).filterMap (fun (e, w) => if w.isEr then none else some e) == xs.map .atom
  | [.list [.atom "coerce", e, _]] => returnsBinders xs want [e]
  | [e] => !(want.head?.getD .er).isEr && xs == [e.show]
  | .list (.atom "let" :: .list bs :: _) :: rest =>
    bs.all (· matches .list (.atom "erased" :: _)) && returnsBinders xs want rest
  | _ => false

def ghostly {α : Type} (g : Bool) (x : M α) : M α := do
  let st0 ← get
  modify fun st => { st with ghost := st0.ghost || g, top := false }
  let r ← x
  modify fun st => { st with ghost := st0.ghost, top := st0.top }
  return r

abbrev Stmt := Core → Core

def close (ss : List Stmt) (ts : List Tm) : Core := ss.foldr (· ·) (.ret (.ofList ts))

def recordTop (n0 : Nat) (ss : List Stmt) : M Unit := do
  let st ← get
  if !st.top || st.vals.length < n0 then return
  let P : Prog := { adts := st.decls, groups := st.groups, main := .dead }
  let c := close ss ((List.range (st.n - n0)).map (Tm.fv <| n0 + ·))
  let topCtx := st.topCtx.bind fun Γ => if Γ.n == n0 then
      ((mapRet P (fun Γ ts => (ts, Γ)) Γ c).map (·.2)).filter (·.n == st.n)
    else none
  set { st with topCtx }
  match runS P 10000000 (st.vals.take n0) c with
  | some vs => if vs.length == st.n - n0 then set { st with vals := st.vals.take n0 ++ vs, topCtx }
  | none => pure ()

def entry (sc : Scope) : Sx → M Nat
  | .atom x => match sc.lookup x with
    | some (.fv i) | some (.fn i _ _) => pure i
    | _ => throw s!"{x} is not an entry"
  | .list [.atom "level-of", .atom f] => levelOf sc f
  | _ => throw "not an entry"

partial def Sx.litForms : Sx → List Sx
  | e@(.atom _) => [e]
  | .list xs => .list xs :: xs.flatMap Sx.litForms

def natTm (d z sc : Nat) (n : Nat) : Tm :=
  (List.range n).foldl (fun t _ => Tm.app (.vc d sc .nil) (.cons t .nil)) (.app (.vc d z .nil) .nil)

def ctorIx (d : Nat) (c : String) : M Nat := do
  match ((← get).decls[d]?).bind (·.ctorNames.idxOf? c) with
  | some i => pure i
  | none => throw s!"literals need the prelude's {c}"

def preAdt (name : String) : M Nat := do
  let st ← get
  let some d := st.firstAdt name | throw s!"literals need the prelude's {name}"
  unless ((st.lifts.lookup d).getD []).isEmpty || name == "Char" || name == "U8" || name == "String" do
    throw s!"the prelude's {name} mentions top-level entries"
  pure d

def app (h : Tm) (args : List Tm) : Tm := .app h (.ofList args)

def internLits (e : Sx) : M (List Stmt) := do
  let st0 ← get
  let forms := e.litForms
  let atoms := forms.filterMap fun | .atom a => some a | _ => none
  let strs := (atoms.filter (·.startsWith "\"")).map fun a => (a.toList.drop 1).map Char.toNat
  let charsWanted := (atoms.filterMap charCode ++ strs.flatten).eraseDups
  let numOf := forms.filterMap fun | .list [.atom "numeral-of", x] => litOf x | _ => none
  let ltOf := forms.filterMap fun
    | .list [.atom "prove-literal-lt", a, b] => do let x ← numeralOf a; let y ← numeralOf b; if x < y then some (x, y) else none
    | _ => none
  let eqOf := forms.filterMap fun
    | .list [.atom "unary", a] => (litOf a).map (·, none)
    | .list [.atom "unary", a, b] => do let x ← litOf a; let y ← litOf b; if y < x then some (x, some y) else none
    | _ => none
  let nums := ((e.numerals ++ charsWanted ++ numOf ++ ltOf.flatMap (fun (a, b) => [a, b]) ++
    eqOf.flatMap (fun (a, b) => a :: b.toList)).filter fun n => (st0.lits.lookup n).isNone).eraseDups
  let fresh1 (er : Bool) : M Nat := do
    let is ← fresh [er]
    match is with
    | [i] => pure i
    | _ => throw "fresh"
  let mut out : List Stmt := []
  if nums.isEmpty && strs.all (fun s => (st0.strs.lookup s).isSome) && charsWanted.all (fun c => (st0.chars.lookup c).isSome)
      && numOf.all (fun n => (st0.numPf.lookup n).isSome) && ltOf.all (fun p => (st0.ltPf.lookup p).isSome)
      && eqOf.all (fun p => (st0.eqPf.lookup p).isSome) then return []
  unless st0.pre do throw "a literal needs the prelude, which --no-prelude leaves out"
  if nums.any (· > 100000) then throw "a numeral above 100000 is not supported: the runner holds a Nat in unary"
  let nat ← preAdt "Nat"
  let z ← ctorIx nat "Zero"
  let sc ← ctorIx nat "Succ"
  let nt := natTm nat z sc
  let natTy := Tm.app (.tyc nat .nil) .nil
  for n in nums do
    let i ← fresh1 false
    note i natTy
    modify fun st => { st with lits := (n, i) :: st.lits }
    out := out ++ [.prim (.lit (nt n)) false]
  let lit (n : Nat) : M Tm := do
    match (← get).lits.lookup n with
    | some i => pure (.fv i)
    | none => throw "unreachable"
  let assertPf (t A : Tm) : M (Nat × Stmt) := do
    let i ← fresh1 true
    note i A
    pure (i, .prim (.assert t A) true)
  let ltD ← preAdt "Lt"
  let ltTm : Nat → Nat → M Tm := fun a b => do
    let lz ← ctorIx ltD "LtZ"
    let ls ← ctorIx ltD "LtS"
    pure <| (List.range a).foldr (fun k t => app (.vc ltD ls .nil) [nt (a - 1 - k), nt (b - 1 - k), t])
      (app (.vc ltD lz .nil) [nt (b - a - 1)])
  let stc ← get
  let newChars := charsWanted.filter fun c => (stc.chars.lookup c).isNone
  if !newChars.isEmpty then
    let chr ← preAdt "Char"
    let u8 ← preAdt "U8"
    let some m := (← get).u8mod | throw "character literals need the prelude's u8-modulus"
    for c in newChars do
      if c > 255 then throw "a character literal is one byte"
      let (p, sp) ← assertPf (← ltTm c 256) (app (.tyc ltD .nil) [← lit c, .fv m])
      out := out ++ [sp]
      let i ← fresh1 false
      let t := app (.vc chr 0 (← liftTm chr)) [app (.vc u8 0 (← liftTm u8)) [← lit c, .fv p]]
      note i (app (.tyc chr (← liftTm chr)) [])
      note i t true
      modify fun st => { st with chars := (c, i) :: st.chars }
      out := out ++ [.prim (.tm t) false]
  for str in strs.eraseDups do
    if ((← get).strs.lookup str).isSome then continue
    let sd ← preAdt "String"
    let nilC ← ctorIx sd "SNil"
    let consC ← ctorIx sd "SCons"
    let ls ← liftTm sd
    let mut t := app (.vc sd nilC ls) []
    for c in str.reverse do
      let some ci := (← get).chars.lookup c | throw "unreachable"
      t := app (.vc sd consC ls) [.fv ci, t]
    let i ← fresh1 false
    note i (app (.tyc sd ls) [])
    modify fun st => { st with strs := (str, i) :: st.strs }
    out := out ++ [.prim (.lit t) false]
  if !numOf.isEmpty then
    let bin ← preAdt "Bin"
    let numD ← preAdt "Numeral"
    let dbl ← preAdt "Double"
    let (bz, b1, b2) := (← ctorIx bin "BZ", ← ctorIx bin "B1", ← ctorIx bin "B2")
    let (nz, n1, n2) := (← ctorIx numD "NZ", ← ctorIx numD "N1", ← ctorIx numD "N2")
    let (d0, ds) := (← ctorIx dbl "D0", ← ctorIx dbl "DS")
    let dblTm (m : Nat) : Tm := (List.range m).foldl (fun t k => app (.vc dbl ds .nil) [nt k, nt (2 * k), t]) (app (.vc dbl d0 .nil) [])
    let rec spell : Nat → Nat → Tm × Tm
      | 0, _ => (app (.vc bin bz .nil) [], app (.vc numD nz .nil) [])
      | _, 0 => (app (.vc bin bz .nil) [], app (.vc numD nz .nil) [])
      | fuel + 1, n + 1 =>
        let m := n / 2
        let (b, v) := spell fuel m
        if n % 2 == 0 then (app (.vc bin b1 .nil) [b], app (.vc numD n1 .nil) [b, nt m, nt (2 * m), v, dblTm m])
        else (app (.vc bin b2 .nil) [b], app (.vc numD n2 .nil) [b, nt m, nt (2 * m), v, dblTm m])
    for n in numOf.eraseDups do
      if ((← get).numPf.lookup n).isSome then continue
      let (b, v) := spell (n + 1) n
      let (i, sp) ← assertPf v (app (.tyc numD .nil) [b, ← lit n])
      out := out ++ [sp]
      modify fun st => { st with numPf := (n, i) :: st.numPf }
  for (a, b) in ltOf.eraseDups do
    if ((← get).ltPf.lookup (a, b)).isSome then continue
    let (i, sp) ← assertPf (← ltTm a b) (app (.tyc ltD .nil) [← lit a, ← lit b])
    out := out ++ [sp]
    modify fun st => { st with ltPf := ((a, b), i) :: st.ltPf }
  for (a, b) in eqOf.eraseDups do
    if ((← get).eqPf.lookup (a, b)).isSome then continue
    let eqD ← preAdt "Eq"
    let refl ← ctorIx eqD "Refl"
    let floor ← match b with | some b => lit b | none => pure (nt 0)
    let k := a - b.getD 0
    let rhs := (List.range k).foldl (fun t _ => app (.vc nat sc .nil) [t]) floor
    let (i, sp) ← assertPf (app (.vc eqD refl .nil) [natTy, nt a]) (app (.tyc eqD .nil) [natTy, ← lit a, rhs])
    out := out ++ [sp]
    modify fun st => { st with eqPf := ((a, b), i) :: st.eqPf }
  return out

def peelTele : Tm → List Tm → Tm
  | .bind _ _ r, x :: xs => peelTele (r.inst x 0) xs
  | t, _ => t

structure CtorInfo where
  k : Tm
  pos : Nat
  sig : Tm
  phantom : Bool
  union : Bool
  nt : Bool

def ctorInfo (sc : Scope) (c : String) : M CtorInfo := do
  let st ← get
  let global (d ci : Nat) : M CtorInfo := do
    let some D := st.decls[d]? | throw s!"unknown constructor {c}"
    let ls := ((st.lifts.lookup d).getD []).map Tm.fv
    return ⟨.vc d ci (.ofList ls), ci, peelTele (D.ctors.getD ci .nil) ls, D.phantom.getD ci false, D.union, D.newtype⟩
  match sc.lookup c with
  | some (.ctor i) | some (.fv i) =>
    if let some (.vc d ci _) := st.inl.lookup i then return ← global d ci
    let found := st.opened.findSome? fun m => match st.known.lookup m with
      | some (.mtbl u nt _ ph _ cs) => (cs.toList.idxOf? (.fv i)).map fun p => (p, u, ph.getD p false, nt)
      | _ => none
    match found, st.known.lookup i with
    | some (p, u, ph, nt), some (.valCtor sig) => return ⟨.fv i, p, sig, ph, u, nt⟩
    | some _, _ => throw s!"{c} is not a value constructor"
    | none, _ => throw s!"{c} has no Matchable open"
  | _ => match st.ctors.lookup c with
    | some (d, ci) => global d ci
    | none => throw s!"unknown constructor {c}"

def openPattern (sc : Scope) (md : Mode) : Sx → M (Nat × CtorInfo × Scope)
  | .list (.atom c :: xs) => do
    let ci ← ctorInfo sc c
    let names ← xs.mapM name
    if names.length == (fieldErs ci.sig).length + 1 then throw "a cell binder in a pattern is not supported"
    unless names.length == (fieldErs ci.sig).length do throw s!"a pattern for {c} binds the wrong number of fields"
    let fs ← freshMd (if md.isEr || ci.phantom then names.map fun _ => Mode.er
      else (fieldMds ci.sig).map fun m => if m == .uniq && md != .uniq then .many else m)
    return (names.length, ci, (names.zip (fs.zipWith (fun i T => entRef i T) (teleTys ci.sig))).reverse ++ sc)
  | _ => throw "malformed pattern"

def erasedPos (want : List Mode) : M Bool := return (← get).ghost || (!want.isEmpty && want.all (·.isEr))

def useVar (i : Nat) (m : Mode) (sharing : Bool := false) : M Unit := do
  let st ← get
  if m.isEr || st.ghost then return
  let u := st.uq.contains i
  if m == .uniq && !u then throw "a value not declared `unique` is used at unique"
  if m == .many && u && !sharing then throw "a unique value is used at many without `share`"
  if !u then return
  if m == .uniq && i < st.captures then throw "`def-fns` cannot capture a unique value at unique"
  match st.uses.lookup i with
  | some true => throw "a unique value has conflicting non-erased uses: it is already used at unique"
  | some false => if m == .uniq then throw "a unique value has conflicting non-erased uses: it is already shared"
  | none => pure ()
  modify fun st => { st with uses := (i, m == .uniq) :: st.uses.filter (·.1 != i) }

def mintDele (i t : Nat) : M (Stmt × Nat) := do
  let [k] ← fresh [true] | throw "fresh"
  let uq := (← get).uq
  let side (j : Nat) : Mode := if uq.contains j then .uniq else .many
  modify fun st => { st with sides := (k, some (side i), some (side t)) :: st.sides }
  return (.prim (.deleOf i t) true, k)

def headUse (want : List Mode) (i : Nat) : M Unit := do
  unless ← erasedPos want do useVar i .many

def useTm (t : Tm) (want : List Mode) : M Unit := do
  if let (.fv i, [m]) := (t, want) then useVar i m

def supply (want sup : List Mode) : M Unit := do
  if (← get).ghost then return
  for (w, s) in want.zip sup do
    if w == .uniq && s == .many then throw "a result not declared `unique` is used at unique"
    if w == .many && s == .uniq then throw "a unique result is used at many without `share`"

def joinUses (a b : List (Nat × Bool)) : List (Nat × Bool) :=
  b.foldl (fun acc (i, c) => match acc.lookup i with
    | some true => acc
    | _ => (i, c) :: acc.filter (·.1 != i)) a

def sideMode : Tm → Option Mode
  | .app (.vc d 0 _) .nil => if d == sharingD then some .uniq else none
  | .app (.vc d 1 _) .nil => if d == sharingD then some .many else none
  | _ => none

def coerSides (t : Tm) : M (Option Mode × Option Mode) := do
  let st ← get
  let .fv i := t | return (none, none)
  let (ka, kb) := match st.known.lookup i with
    | some (.app (.tyc _ _) args) => match args.toList with
      | [sa, _, _, sb, _, _] => (sideMode sa, sideMode sb)
      | _ => (none, none)
    | _ => (none, none)
  let (pa, pb) := (st.sides.lookup i).getD (none, none)
  return (ka <|> pa, kb <|> pb)

def primSides : Prim → M (Option Mode × Option Mode)
  | .coerRefl s _ | .coerCtor s .. => return (sideMode s, sideMode s)
  | .coerSym q => return (← coerSides q).swap
  | .coerShare _ => return (some .many, some .many)
  | .coerTrans q r => return ((← coerSides q).1, (← coerSides r).2)
  | .coerOf d => coerSides d
  | .coerWrap s C _ => do
    let st ← get
    let sig := match C with
      | .vc d c ls => peelTele (((st.decls[d]?).bind (·.ctors[c]?)).getD .nil) ls.toList
      | .fv i => match st.known.lookup i with | some (.valCtor sig) => sig | _ => .nil
      | _ => .nil
    return (if (fieldMds sig).contains .uniq then sideMode s else some .many, sideMode s)
  | _ => return (none, none)

def bindTemp (sc : Scope) (t : Tm) (er : Bool) : M (List Stmt × Ref) := do
  match t with
  | .fv i => return ([], match (← get).inl.lookup i with | some (.vc ..) | some (.tyc ..) => .ctor i | _ => refOf sc i)
  | _ => do
    let [j] ← fresh [er] | throw "fresh"
    note j t true
    return ([.prim (.tm t) er], match t with | .vc .. | .tyc .. => .ctor j | _ => .fv j)

def warnMatch (ks : List Tm) : M Unit := do
  let st ← get
  if let some d := ks.findSome? (fun | .vc d _ _ => some d | _ => none) then
    warnUse (.tyc d .nil) "match" (showName ((st.decls[d]?).map (·.name)).get!)

def warnTarget (sc : Scope) (x : String) : M Tm := do
  let st ← get
  let fnTy (i : Nat) := match st.known.lookup i with | some (.fn ..) => true | _ => false
  match sc.lookup x with
  | some (.fn i _ _) => return .fv i
  | some (.fv i) | some (.ctor i) => match st.inl.lookup i with
    | some (.vc d c _) => return .vc d c .nil
    | some (.tyc d _) => return .tyc d .nil
    | _ => if fnTy i then return .fv i else throw s!"`;! warn` names `{showName x}`, which is neither a constructor nor a function"
  | some _ => throw s!"`;! warn` names `{showName x}`, which is neither a constructor nor a function"
  | none => match st.adts.lookup x, st.ctors.lookup x with
    | some d, _ => return .tyc d .nil
    | _, some (d, c) => return .vc d c .nil
    | _, _ => throw s!"`;! warn` names `{showName x}`, which {if x ∈ specialNames then "is neither a constructor nor a function" else "is not in scope"}"

def pragmaWords (p : String) : Except String (List String × String) := do
  let cs := (p.toList.drop 2).dropWhile (· == ' ')
  let w1 := cs.takeWhile (· != ' ')
  let cs := (cs.drop w1.length).dropWhile (· == ' ')
  if String.ofList w1 != "warn" && !["suppress", "restore"].contains (String.ofList w1) then
    return ([String.ofList w1], "")
  let w := if String.ofList w1 == "warn" then [] else cs.takeWhile (· != ' ')
  let (w2, cs) := (w, (cs.drop w.length).dropWhile (· == ' '))
  let (nm, rest) ← match cs with
    | '#' :: '"' :: r => do let (s, r) ← readStr r []; pure (rawName (String.ofList s), r)
    | _ => let w := cs.takeWhile (· != ' '); pure (String.ofList w, cs.drop w.length)
  let words := [String.ofList w1] ++ (if w2.isEmpty then [] else [String.ofList w2]) ++ (if nm.isEmpty then [] else [nm])
  return (words, (String.ofList rest).trimAscii.toString)

def pragma (sc : Scope) (p : String) : M Unit := do
  let (ws, msg) ← match pragmaWords p with | .ok r => pure r | .error e => throw e
  let st ← get
  match ws with
  | ["warn", x] =>
    unless st.depthTop do throw "`;! warn` must be written between top-level forms"
    if msg.isEmpty then throw s!"`;! warn` for `{showName x}` has no message"
    let t ← warnTarget sc x
    if st.pwarn.any (·.1 == t) then throw s!"a second `;! warn` for `{showName x}`"
    modify fun st => { st with pwarn := (t, msg) :: st.pwarn }
  | ["warn"] => throw "`;! warn` names nothing"
  | ["suppress", "warn", x] =>
    if st.supp.any (·.1 == x) then throw s!"a second `;! suppress warn` for `{showName x}` is already open"
    let t ← try some <$> warnTarget sc x catch _ => pure none
    modify fun st => { st with supp := (x, t, 0) :: st.supp }
  | ["restore", "warn", x] =>
    match st.supp.find? (·.1 == x) with
    | none => throw s!"`;! restore warn` for `{showName x}` has no open `;! suppress warn`"
    | some (_, _, n) =>
      if n == 0 then warn s!"`;! suppress warn` for `{showName x}` silenced nothing"
      modify fun st => { st with supp := st.supp.filter (·.1 != x) }
  | w :: _ => throw s!"unknown pragma `{w}`"
  | [] => throw "unknown pragma ``"

mutual
partial def elabExpr (sc : Scope) (want : List Mode) (exp : Option Tm) (e : Sx) : M (List Stmt × List Tm) := do
  match ← resolveHead sc (headUse want) e with
  | .list [.atom "\x03var", .atom x] => do let t ← look sc 0 x; useTm t want; return ([], [t])
  | e@(.list (hd@(.list _) :: args)) => do
    if let some (ss, e') ← dispatchComputed sc e then
      let (ss2, ts) ← elabExpr sc want exp e'
      return (ss ++ ss2, ts)
    let hm ← if ← erasedPos want then pure Mode.er else headMode sc hd
    let (ss, ts) ← withTail false (elabExpr sc [hm] none hd)
    let [t] := ts | throw "a computed head has one value"
    let (ss2, r) ← bindTemp sc t (← erasedPos want)
    let (ss3, ts) ← elabExpr ((" head", r) :: sc) want exp (.list (.atom " head" :: args))
    return (ss ++ ss2 ++ ss3, ts)
  | e => elabExpr' sc want exp e

partial def headMode (sc : Scope) : Sx → M Mode
  | .list [.atom "values", x] => headMode sc x
  | .list (.atom "match" :: _ :: _ :: .list [.list (T :: _)] :: _) =>
    pure (if T matches .list (.atom "UniqueFn" :: _) then .uniq else .many)
  | .atom x => do
    let st ← get
    match sc.lookup x with
    | some (.fv i) | some (.fn i _ _) => pure (if st.known.lookup i matches some (.fn _ _ _ true) then .uniq else .many)
    | _ => pure .many
  | .list (.atom f :: _) => do
    let st ← get
    match sc.lookup f with
    | some (.fv i) | some (.fn i _ _) => match st.known.lookup i with
      | some (.fn _ np tele _) => match (teleMds tele).drop np, (teleTys tele).drop np with
        | [m], [T] => pure (if m == .uniq || T matches .fn _ _ _ true then .uniq else .many)
        | _, _ => pure .many
      | _ => pure .many
    | _ => pure .many
  | _ => pure .many

partial def dispatchComputed (sc : Scope) : Sx → M (Option (List Stmt × Sx))
  | .list (hd@(.list _) :: args) => do
    let st0 ← get
    if !st0.top || st0.vals.length != st0.n then return none
    let some (ss, ts) ← tryCatch (some <$> withTail false (elabExpr sc [false] none hd)) (fun _ => do set st0; pure none)
      | return none
    let [t] := ts | throw "a computed head has one value"
    let st ← get
    let P : Prog := { adts := st.decls, groups := st.groups, main := .dead }
    match runS P 10000000 st0.vals (close ss [t]) with
    | some [.app (.vc d c _) _] =>
      if d == st.special && st.decls.length > 0 then
        let f := specialNames.getD c ""
        if (sc.lookup f).isSome then throw s!"the special form {f} is shadowed where a computed head dispatches to it"
        recordTop st0.n ss
        return some (ss, .list (.atom f :: args))
      else set st0; return none
    | _ => set st0; return none
  | _ => return none

partial def compileMsgE (sc : Scope) (m : Sx) : M (List Stmt × String) := do
  if let .atom a := m then
    if a.startsWith "\"" then return ([], String.ofList (a.toList.drop 1))
  let n0 := (← get).n
  let (ss, ts) ← withTail false (elabExpr sc [false] none m)
  let [t] := ts | throw "the message of compile-error or compile-warn is one value"
  recordTop n0 ss
  let st ← get
  let v := match t with
    | .fv i => st.settledVal i
    | t => if st.top && st.vals.length == st.n then
        (runS { adts := st.decls, groups := st.groups, main := .dead } 10000000 st.vals (close [] [t])).bind (·.head?)
      else none
  match v.bind st.strOfVal with
  | some cs => return (ss, String.ofList cs)
  | none => throw s!"the message of compile-error or compile-warn must be a Settled, non-erased String; `{m.show.take 40}` is not one"

partial def elabExpr' (sc : Scope) (want : List Mode) (exp : Option Tm) : Sx → M (List Stmt × List Tm)
  | .list (.atom "values" :: es) => elabArgs sc es want
  | .list [.atom "compile-error", m] => do throw (← compileMsgE sc m).2
  | .list [.atom "dump-context"] => do throw (← dumpContext sc)
  | e@(.list (.atom h :: args)) => do
    let st ← get
    if h ∈ ["prove-subterm", "prove-predates", "predates-trans", "subterm-trans", "predates-subterm"] then
      let (ss, ts) ← elabArgs sc args
      let p ← match h, ts, args with
        | "prove-subterm", [a, b], _ => pure (.proveSubterm a b)
        | "prove-predates", _, [x, L] => do
          pure (Prim.provePredates (← entry sc x) (← entry sc L))
        | "predates-trans", [p, q], _ => pure (.predatesTrans p q)
        | "subterm-trans", [p, q], _ => pure (.subtermTrans p q)
        | "predates-subterm", [p, q], _ => pure (.predatesSubterm p q)
        | _, _, _ => throw s!"malformed {h}"
      let [i] ← fresh [true] | throw "fresh"
      return (ss ++ [.prim p true], [.fv i])
    else if h == "delegate-of" && (sc.lookup h).isNone then
      let [.atom g] := args | throw "hint: usage: (delegate-of <function>)"
      if (sc.lookup g).isNone then throw s!"unbound name {showName g}"
      let i ← entry sc (.atom g)
      if let some k := (← get).delePf.lookup i then return ([], [.fv k])
      let some t := (← get).deles.lookup i | throw s!"delegate-of: {showName g} is not a non-erased function with a `delegate` body"
      let (s, k) ← mintDele i t
      return ([s], [.fv k])
    else if h == "coercible-of" && (sc.lookup h).isNone then
      let [d] := args | throw "hint: usage: (coercible-of <Delegate proof>)"
      let (ss, ts) ← elabArgs sc [d] [true]
      let [k] ← fresh [true] | throw "fresh"
      let sd ← primSides (.coerOf ts[0]!)
      modify fun st => { st with sides := (k, sd) :: st.sides }
      return (ss ++ [.prim (.coerOf ts[0]!) true], [.fv k])
    else if h.startsWith "coercible-" && (sc.lookup h).isNone && h != "coercible-of" then
      let p ← match h, args with
        | "coercible-refl", [s, e] => do
          let (ss, ts) ← elabArgs sc [s, e] [true, true]
          pure (ss, Prim.coerRefl ts[0]! ts[1]!)
        | "coercible-sym", [p] => do let (ss, ts) ← elabArgs sc [p] [true]; pure (ss, Prim.coerSym ts[0]!)
        | "coercible-share", [p] => do let (ss, ts) ← elabArgs sc [p] [true]; pure (ss, Prim.coerShare ts[0]!)
        | "coercible-trans", [p, q] => do
          let (ss, ts) ← elabArgs sc [p, q] [true, true]; pure (ss, Prim.coerTrans ts[0]! ts[1]!)
        | "coercible-wrap", s :: .atom c :: xs => do
          let ci ← ctorInfo sc c
          let n := (fieldErs ci.sig).length
          unless xs.length == n do
            throw s!"`coercible-wrap` of `{c}` expects {n} more arguments, got {xs.length}"
          let (ss, ts) ← elabArgs sc (s :: xs) (List.replicate (xs.length + 1) true)
          pure (ss, Prim.coerWrap ts[0]! ci.k (.ofList (ts.drop 1)))
        | "coercible-ctor", s :: .atom c :: xs => do
          let ci ← try ctorInfo sc c catch e => do
            let st ← get
            match sc.lookup c with
            | some (.ctor i) | some (.fv i) => match st.known.lookup i with
              | some (.valCtor sig) => pure ⟨.fv i, 0, sig, false, false, false⟩
              | _ => throw e
            | _ => throw e
          let ers := fieldErs ci.sig
          let want := (ers.map fun e => if e then 2 else 1).sum
          unless xs.length == want do
            throw s!"`coercible-ctor` of `{c}` expects {want} more arguments, got {xs.length}: expected a source and a target for each erased field and a `Coercible` proof for each other field"
          let (ss, ts) ← elabArgs sc (s :: xs) (List.replicate (xs.length + 1) true)
          let (srcs, tgts, ps, _) := ers.foldl (fun (srcs, tgts, ps, k) e =>
            if e then (srcs ++ [ts[k]!], tgts ++ [ts[k + 1]!], ps ++ [Tm.nil], k + 2)
            else (srcs ++ [Tm.hole], tgts ++ [Tm.hole], ps ++ [ts[k]!], k + 1)) ([], [], [], 1)
          pure (ss, Prim.coerCtor ts[0]! ci.k (.ofList srcs) (.ofList tgts) (.ofList ps))
        | _, _ => throw s!"malformed {h}"
      let [i] ← fresh [true] | throw "fresh"
      let sd ← primSides p.2
      modify fun st => { st with sides := (i, sd) :: st.sides }
      return (p.1 ++ [.prim p.2 true], [.fv i])
    else if h == "coerce" && (sc.lookup h).isNone then
      let [a, p] := args | throw "hint: usage: (coerce <value> <proof>)"
      let er ← erasedPos want
      let (ss1, tp) ← elabArgs sc [p] [true]
      let (sa, sb) ← coerSides tp[0]!
      let uq := (← get).uq
      let dflt := match a with
        | .atom x => match sc.lookup x with
          | some (.fv j) | some (.fn j _ _) => if uq.contains j then Mode.uniq else .many
          | _ => .many
        | _ => .many
      let (ss2, ta) ← elabArgs sc [a] [if er then .er else sa.getD dflt]
      let bm := if er then Mode.er else sb.getD (want.headD .many)
      supply want [bm]
      let [i] ← freshMd [bm] | throw "fresh"
      if let .fv j := ta[0]! then modify fun st => { st with renames := (i, j) :: st.renames }
      return (ss1 ++ ss2 ++ [.prim (.coerce ta[0]! .hole tp[0]!) er], [.fv i])
    else if h == "match" then elabMatch sc want exp args
    else if h == "share" && (sc.lookup h).isNone then
      if ← erasedPos want then throw "`share` in an erased position, where nothing is used"
      let [x] := args | throw "hint: usage: (share <expression>)"
      let (ss, t) ← match x with
        | .atom a => do
          let t ← look sc 0 a
          if let .fv i := t then
            if !(← get).uq.contains i && !(← get).ghost then throw "`share` needs a unique value"
            useVar i .many true
          pure ([], t)
        | x => do
          let (ss, ts) ← elabExpr sc [.uniq] none x
          let [t] := ts | throw "`share` takes one value"
          pure (ss, t)
      supply want [.many]
      let [j] ← freshMd [.many] | throw "fresh"
      note j t true
      return (ss ++ [.prim (.tm t) false], [.fv j])
    else if h == "open-absurd" && (sc.lookup h).isNone then
      let [e, _] := args | throw "open-absurd takes an expression and an annotation"
      let (ss, ts) ← withTail false (elabExpr sc [true] none e)
      let [t] := ts | throw "open-absurd: one value"
      let (ss2, i) ← (match t with
        | .fv i => pure ([], i)
        | t => do
          let js ← fresh [true]
          pure ([.prim (.tm t) true], js.headD 0) : M (List Stmt × Nat))
      let outs ← freshMd want
      return (ss ++ ss2 ++ [fun _ => .chk (.opn true) (.fv i) .nil .dead], outs.map .fv)
    else if h == "matchable-of" && (sc.lookup h).isNone then
      return ([], [← elabTm sc 0 e])
    else if h == "delegate" && (sc.lookup h).isNone then
      let [x@(.list (.atom f :: cargs))] := args | throw "delegate wraps a call"
      if st.ghost || (!want.isEmpty && want.all (·.isEr)) then throw "delegate in an erased position"
      if !st.tail then throw "delegate: the call is not in tail position"
      let some (tgt, params) := st.dele | throw "a delegate body needs `at f` on its function's header"
      unless (← look sc 0 f) == .fv tgt do throw "delegate: the call is not to the function its header names"
      let ms := match sc.lookup f with | some (.fn _ _ ms) => ms | _ => []
      let plain := cargs.filter fun | .list [.atom "predates", _] | .list [.atom "subterm", _] => false | _ => true
      let rn := (← get).renames
      let passed ← ((plain.zip ms).filter (!·.2.isEr)).mapM fun (a, _) => do
        return (List.range rn.length).foldl (fun i _ => (rn.lookup i).getD i) (← entry sc a)
      unless passed == params.filterMap (fun (i, e) => if e then none else some i) do
        throw "delegate: the non-erased parameters are not passed straight through, in order"
      modify fun st => { st with delegated := true }
      elabExpr sc want exp x
    else if (h == "tail" || h == "notail") && (sc.lookup h).isNone then
      let [x@(.list (.atom f :: _))] := args | throw s!"{h} wraps a call"
      if (st.adts.lookup f).isSome || (st.ctors.lookup f).isSome || keywords.contains f then throw s!"{h} wraps a call"
      if st.ghost || (!want.isEmpty && want.all (·.isEr)) then throw s!"{h} in an erased position"
      if h == "tail" && !st.tail then throw "tail: the call is not in tail position"
      if h == "notail" && st.tail then throw "notail: the call is in tail position"
      elabExpr sc want exp x
    else if let (some (tele, np), none) := (st.prims.lookup h, sc.lookup h) then
      let (ss, ts) ← elabArgs sc args ((teleMds tele).take np)
      unless ts.length == np do throw s!"`{h}` takes {np} arguments"
      let mut t := tele
      let mut out : List Stmt := []
      for a in ts do
        let .bind k A r := t | throw s!"`{h}` takes {np} arguments"
        if k matches .ty .. then out := out ++ [(fun c => .chk .ty a A c : Stmt)]
        t := r.inst a 0
      let mut rs : List Tm := []
      while true do
        let .bind _ R r := t | break
        let [i] ← fresh [true] | throw "fresh"
        note i R
        out := out ++ [.prim (.axm R) true]
        rs := rs ++ [.fv i]
        t := r.inst (.fv i) 0
      return (ss ++ out, rs)
    else if h ∈ keywords || (sc.lookup h).isNone then
      match st.adts.lookup h, st.ctors.lookup h with
      | some d, _ => let (ss, ts) ← elabArgs sc args; return (ss, [.app (.tyc d (← liftTm d)) (.ofList ts)])
      | _, some (d, c) =>
        let sig := ((st.decls[d]?).bind (·.ctors[c]?)).getD .nil
        unless ← erasedPos want do warnUse (.vc d c .nil) "application" (showName h)
        let fm := fun (m : Mode) => if m == .uniq && want != [.uniq] then Mode.many else m
        let (ss, ts) ← elabArgs sc args (((fieldMds sig).drop ((st.lifts.lookup d).getD []).length).map fm)
        return (ss, [.app (.vc d c (← liftTm d)) (.ofList ts)])
      | _, _ =>
        unless h ∈ ["Fn", "UniqueFn", "TyCtor", "ValCtor", "Matchable", "Level", "Predates", "Subterm", "level-of", "numeral-of", "prove-literal-lt"] do
          throw (if h ∈ specialNames then s!"{h} is not supported here" else s!"unbound name {showName h}")
        return ([], [← elabTm sc 0 e])
    else if let some (.ctor i) := sc.lookup h then
      unless ← erasedPos want do if let some t := st.inl.lookup i then warnUse t "application" (showName h)
      let (ss, ts) ← elabArgs sc args; return (ss, [.app (.fv i) (.ofList ts)])
    else do
      let f ← look sc 0 h
      let isDec : Sx → Bool | .list [.atom "predates", _] | .list [.atom "subterm", _] => true | _ => false
      if (args.filter isDec).length > 1 then throw "a call carries at most one decrease annotation"
      if (args.drop 1).any (· matches .list [.atom "predates", _]) then
        throw "predates is written immediately after the callee"
      let (pd, args) ← (match args with
        | .list [.atom "predates", p] :: rest => pure (some p, rest)
        | _ => pure (none, args) : M (Option Sx × List Sx))
      let (dec, ss0, args) ← match pd with
        | some p => do let (ss, ps) ← elabArgs sc [p] [true]; pure (Dec.predates ps.head!, ss, args)
        | none => match args.findIdx? (fun (x : Sx) => match x with | .list [.atom "subterm", _] => true | _ => false) with
          | some pos => match args[pos]! with
            | .list [_, p] => do
              let (ss, ps) ← elabArgs sc [p] [true]
              pure (Dec.subterm pos ps.head!, ss, args.eraseIdx pos)
            | _ => throw "unreachable"
          | none => pure (Dec.none, [], args)
      unless ← erasedPos want do warnUse f "call" (showName h)
      let kty := match f with
        | .fv i => st.known.lookup i <|> (match st.inl.lookup i with | some (.fv k) => st.known.lookup k | _ => none)
        | _ => none
      let (ss, ts) ← elabArgs sc args (match sc.lookup h, kty with
        | some (.fn _ _ ms), _ => ms
        | _, some (.fn _ np tele _) => (teleMds tele).take np
        | _, _ => [])
      if let .fv i := f then
        useVar i (if kty matches some (.fn _ _ _ true) || (kty.isNone && st.uq.contains i) then .uniq else .many)
      if let some (.fn _ np tele _) := kty then supply want ((teleMds tele).drop np)
      let outs ← freshMd want
      let known := (← get).known
      if let some (.fn _ _ tele _) := (match f with | .fv i => known.lookup i | _ => none) then
        let _ ← (ts ++ outs.map Tm.fv).zipIdx.foldlM (fun t (a, k) => match t with
          | .bind k' A r => do
            if ts.length ≤ k then
              note (outs.getD (k - ts.length) 0) A (k' matches .is ..)
            pure (r.inst a 0)
          | t => pure t) tele
      let ve := match (match f with | .fv i => known.lookup i | _ => none) with
        | some (.fn _ _ tele _) => some tele.ers
        | _ => none
      return (ss0 ++ ss ++ [.call f dec (.ofList ts) (!want.isEmpty && want.all (·.isEr)) (want.map (·.isEr)) ve], outs.map .fv)
  | e => do
    let t ← elabTm sc 0 e
    if e matches .atom _ then useTm t want
    return ([], [t])

partial def elabArgs (sc : Scope) (es : List Sx) (ms : List Mode := []) : M (List Stmt × List Tm) := withTail false do
  let rs ← es.zipIdx.mapM fun (e, i) => elabExpr sc [ms.getD i .many] none e
  return (rs.flatMap (·.1), rs.flatMap (·.2))

partial def elabArms (sc : Scope) (md : Mode) (gEr : Bool) (rms : List Mode) (R : Option Tm) (brs : List Sx)
    (extra : Nat := 0) : M (List Br × Option Core × Bool) := do
  let st ← get
  let er := md.isEr
  let base := st.n
  let u0 := st.uses
  let mut uses := u0
  let mut out : List Br := []
  let mut infos : List CtorInfo := []
  let mut els : Option Core := none
  for br in brs do
    if let .list (.atom "else" :: items) := br then
      if els.isSome then throw "match: two else branches"
      reset base
      modify fun st => { st with uses := u0 }
      els := some (← ghostly gEr (elabBody sc rms items R))
      uses := joinUses uses (← get).uses
      continue
    if let .list [.atom "absurd", .atom c] := br then
      let ci ← ctorInfo sc c
      out := out ++ [((fieldErs ci.sig).length, ci.pos, ci.k, .dead)]
      infos := infos ++ [ci]
      continue
    let (ab, br) := match br with
      | .list (.atom "absurd" :: rest) => (true, Sx.list rest)
      | br => (false, br)
    let .list (.list (.atom c :: xs) :: items) := br | throw "malformed branch"
    reset base
    modify fun st => { st with uses := u0 }
    let (n, ci, fsc) ← openPattern sc md (.list (.atom c :: xs))
    let body ← ghostly (gEr || ab || (ci.phantom && !er)) (elabBody fsc (if ab then [true] else rms) items (if ab then none else R) ab)
    uses := joinUses uses (← get).uses
    if out.any (·.2.1 == ci.pos) then throw "two branches for one constructor"
    out := out ++ [(n, ci.pos, ci.k, if ab then .absurd body else body)]
    infos := infos ++ [ci]
  reset base
  modify fun st => { st with uses := uses.filter (·.1 < base) }
  if !er && !(← get).ghost && infos.any (·.union) &&
      extra + ((out.zip infos).filter fun ((_, _, _, b), ci) => b.real && !ci.phantom).length + els.isSome.toNat > 1 then
    throw "a match without a runtime discriminant can have only one real branch"
  return (out, els, !er && infos.any (·.nt))

partial def elabMatch (sc : Scope) (want : List Mode) (exp : Option Tm) (args : List Sx) : M (List Stmt × List Tm) := do
  let (md, args) ← splitMd true args
  let er := md.isEr
  if !er && ((← get).ghost || (!want.isEmpty && want.all (·.isEr))) then throw "a match written many in an erased position"
  let s :: ann :: brs := args | throw "malformed match"
  let R0 ← match ann, exp with
    | .list rets, _ => elabTele sc 0 false rets
    | .atom "_", some R => pure R
    | _, _ => throw "a match annotation `_` where no telescope is expected"
  let (ss, sts) ← withTail false (elabExpr sc [md] none s)
  let [s] := sts | throw "match: one scrutinee"
  let real := er && !(← get).ghost && want.length == R0.len && want.any (!·.isEr)
  let rms := if er && !real then List.replicate R0.len Mode.er else want
  let R := setErs R0 (rms.map (·.isEr))
  let (out, els, nt) ← elabArms sc md (er && !real) rms (some R) brs
  unless er || (← get).ghost do warnMatch (out.map (·.2.2.1))
  let outs ← freshMd rms
  return (ss ++ [if real || nt then .seq R (.case s out els er nt) else .mtch s R out els er], outs.map .fv)

partial def elabSeq (sc : Scope) (want : List Mode) (exp : Option Tm := none) (items : List Sx) :
    M (List Stmt × List Tm) := do
  let n0 := (← get).n
  let ss ← match items with
    | e :: _ => if (← get).top then internLits e else pure []
    | [] => pure []
  unless ss.isEmpty do recordTop n0 ss
  match items with
  | .atom a :: rest =>
    if isPragma a then pragma sc a; let (ss2, ts) ← elabSeq sc want exp rest; return (ss ++ ss2, ts)
    else let (ss2, ts) ← elabSeq' sc want exp items; return (ss ++ ss2, ts)
  | e :: rest =>
    let e ← resolveHead sc (headUse want) e
    if let some (ss1, e') ← dispatchComputed sc e then
      let (ss2, ts) ← elabSeq sc want exp (e' :: rest)
      return (ss ++ ss1 ++ ss2, ts)
    if !rest.isEmpty && rest.all isPragmaSx then
      let (ss2, ts) ← elabSeq' sc want exp [e]
      for p in rest do if let .atom a := p then pragma sc a
      return (ss ++ ss2, ts)
    let (ss2, ts) ← elabSeq' sc want exp (e :: rest)
    return (ss ++ ss2, ts)
  | [] => let (ss2, ts) ← elabSeq' sc want exp items; return (ss ++ ss2, ts)

partial def elabSeq' (sc : Scope) (want : List Mode) (exp : Option Tm) : List Sx → M (List Stmt × List Tm)
  | [] => throw "empty body"
  | [e] => do
    if !(← get).refute then return ← elabExpr sc want exp e
    match e with
    | .list (.atom "match" :: args@(_ :: _ :: .atom "_" :: _)) => do
      let (true, s :: _ :: brs) ← splitMult true args | throw "a refuting match is erased"
      let (ss, [s]) ← withTail false (elabExpr sc [true] none s) | throw "match: one scrutinee"
      let (out, els, _) ← elabArms sc .er true [] none brs
      if els.isSome then throw "a refuting match has no else"
      return (ss ++ [(fun _ => .case s out none true false : Stmt)], [])
    | e => do
      let (ss, [t]) ← elabExpr sc [true] none e | throw "a refutation is one value"
      return (ss ++ [(fun _ => .case t [] none true false : Stmt)], [])
  | .list [.atom "__prelude-end"] :: rest => do
    let u8 : Option Nat := match sc.lookup "u8-modulus" with
      | some (.fv i) => some i
      | _ => none
    modify fun st => { st with inPrelude := !st.pre, u8mod := u8 }
    elabSeq sc want exp rest
  | .list (.atom "def-opaque" :: bs) :: rest => do
    unless (← get).inPrelude do throw "only the prelude may write `def-opaque`"
    let base := (← get).decls.length
    declareAdts sc (bs.map fun | .list (h :: _) => .list [h, .atom "enum"] | b => b)
    modify fun st => { st with decls := st.decls.mapIdx fun d D => if base ≤ d then { D with opq := true } else D }
    elabSeq sc want exp rest
  | .list (.atom "def-prim" :: bs) :: rest => do
    unless (← get).inPrelude do throw "only the prelude may write `def-prim`"
    for b in bs do
      let .list [.list xs] := b | throw "malformed def-prim"
      let (md, xs) ← splitMd true xs
      let .atom p :: .atom ":" :: es := xs | throw "malformed def-prim"
      unless primNames.contains p do throw s!"`{p}` names no primitive the compilers implement"
      if ((← get).prims.lookup p).isSome then throw s!"a second `def-prim` for `{p}`"
      let (ps, rs) ← splitArrow es
      if ps.any (· matches .list (.atom "subterm" :: _)) then throw "`subterm` is not allowed here"
      unless md.isEr || (← entryMds true rs).all (·.isEr) do
        throw s!"the compilers have no implementation of `{p}`, so its returns must be erased"
      let tele ← elabTele sc 0 true (ps ++ rs)
      let tele := if md.isEr then setErs tele (tele.ers.map fun _ => true) else tele
      let np := (← entryMds true ps).length
      modify fun st => { st with prims := (p, tele, np) :: st.prims }
    elabSeq sc want exp rest
  | .list (.atom "def-adts" :: bs) :: rest => do
    let base := (← get).decls.length
    declareAdts sc bs
    let st ← get
    let n0 := st.n
    let mut ss : List Stmt := []
    for d in List.range' base (st.decls.length - base) do
      if let some D := st.decls[d]? then
        let ls := st.liftTm d
        let [i] ← fresh [false] | throw "fresh"
        note i (D.mtbl d ls)
        modify fun st => { st with mtbls := (d, i) :: st.mtbls }
        ss := ss ++ [.prim (.mtblOf d ls) false]
    recordTop n0 ss
    let (ss2, ts) ← elabSeq sc want exp rest
    return (ss ++ ss2, ts)
  | .list [.atom "def-lvl", .atom L] :: rest => do
    if L != " _" then discard <| name (.atom L)
    let [i] ← fresh [true] | throw "fresh"
    note i .level
    recordTop i [Core.defLvl]
    let (ss, ts) ← elabSeq ((L, .fv i) :: sc) want exp rest
    return (.defLvl :: ss, ts)
  | .list (.atom "let" :: .list xs :: items) :: rest => do
    let n0 := (← get).n
    let bs ← xs.mapM fun
      | .list xs => do
        let (md, xs) ← splitMd true xs
        if !md.isEr && (← get).ghost then throw "a let binder written many in an erased position"
        match xs with
        | [x] => pure (← name x, md, none)
        | [e, .atom "is", x] => pure (← name x, md, some (Chk.is, e))
        | [T, x] => pure (← name x, md, some (Chk.ty, T))
        | _ => throw "malformed let binder"
      | _ => throw "malformed let binder"
    let bexp ← if bs.all (·.2.2.isSome) then some <$> elabTele sc 0 true xs else pure none
    let (r0, f0, d0) := ((← get).rhs, (← get).refute, (← get).depthTop)
    modify fun st => { st with rhs := true, refute := false, depthTop := false }
    let (ss, ts) ← withTail ((← get).tail && returnsBinders ((bs.filter (!·.2.1.isEr)).map (·.1)) want rest) (elabSeq sc (bs.map (·.2.1)) bexp items)
    modify fun st => { st with rhs := r0, refute := f0, depthTop := d0 }
    if ts.length != bs.length then throw "let: wrong number of binders"
    let mut ss := ss
    let mut sc' := sc
    for ((x, md, ann), t) in bs.zip ts do
      let st ← get
      let er := md.isEr
      let token : Bool := match t with
        | .fv i => (er && (st.settledVal i).isSome) || (!er && (md == .uniq || st.uq.contains i))
        | _ => false
      let i ← match t, token with
        | .fv i, false => do
          if !er then ss := ss ++ [.chk .rt (.fv i) .nil]
          pure i
        | _, _ => do
          let [j] ← freshMd [md] | throw "fresh"
          ss := ss ++ [.prim (.tm t) er]
          note j t true
          pure j
      let mut r := match t with
        | .tyc .. | .vc .. => .ctor i
        | .fv i0 => if token then (match refOf sc i0 with | .ctor _ => .ctor i | _ => .fv i) else refOf sc i
        | _ => refOf sc i
      if r matches .fv _ && ((← get).known.lookup i).any isCtorTy then r := .ctor i
      if let some (k, a) := ann then
        let a ← elabTm sc' 0 a
        ss := ss ++ [.chk k (.fv i) a]
        if k == .ty then
          note i a
          r := if isCtorTy a then .ctor i else r
      sc' := (x, r) :: sc'
    recordTop n0 ss
    let (ss2, ts2) ← elabSeq sc' want exp rest
    return (ss ++ ss2, ts2)
  | .list (.atom "let-match" :: args) :: rest => do
    let n0 := (← get).n
    let (md, args) ← splitMd true args
    let er := md.isEr
    if !er && (← get).ghost then throw "a let-match written many in an erased position"
    let s :: pat :: brs := args | throw "malformed let-match"
    let (ss, sts) ← withTail false (elabExpr sc [md] none s)
    let [s] := sts | throw "let-match: one scrutinee"
    if (← get).rhs && brs.any (fun | .list (.atom "absurd" :: _) => false | _ => true) then
      throw "a let-match with more than one real branch outside a body"
    let (out, els, _) ← elabArms sc md false want exp brs 1
    let (n, ci, fsc) ← openPattern sc md pat
    let nt := !er && ci.nt
    unless er || (← get).ghost do warnMatch (ci.k :: out.map (·.2.2.1))
    if out.any (·.2.1 == ci.pos) then throw "two branches for one constructor"
    if !er && ci.phantom then throw "a let-match on a phantom constructor at many"
    recordTop n0 (ss ++ [(fun k => .case s ((n, ci.pos, ci.k, k) :: out) els er nt : Stmt)])
    if (← get).top then
      if let .fv j := s then
        if let some (.app (.tyc d _) idx) := (← get).known.lookup j then
          if (← get).firstAdt "Eq" == some d then
            if let [_, .fv x, y] := idx.toList then modify fun st => { st with facts := (x, y) :: st.facts }
    let (ss2, ts) ← elabSeq fsc want exp rest
    return (ss ++ [fun k => .case s ((n, ci.pos, ci.k, k) :: out) els er nt] ++ ss2, ts)
  | .list (.atom "comptime-match" :: args) :: rest => do
    let n0 := (← get).n
    let (md, args) ← splitMd true args
    let st ← get
    unless st.top do throw "comptime-match is confined to run position"
    if md.isEr then throw "comptime-match is written many or unique"
    let [s, pat] := args | throw "malformed comptime-match"
    if md == .uniq && s matches .list [.atom "share", _] then throw "comptime-match: `(share x)` at unique"
    let (ss, sts) ← withTail false (elabExpr sc [md] none s)
    let [t] := sts | throw "comptime-match: one scrutinee"
    let (ss1, x) ← match t with
      | .fv x => pure ([], x)
      | t => do
        let [j] ← fresh [false] | throw "fresh"
        note j t true
        pure ([(.prim (.tm t) false : Stmt)], j)
    let (n, ci, fsc) ← openPattern sc md pat
    if ci.union then throw "comptime-match on a union"
    if ci.phantom then throw "comptime-match on a phantom constructor"
    warnMatch [ci.k]
    let cm : Stmt := fun k => Core.chk .cm (.fv x) .nil (.case (.fv x) [(n, ci.pos, ci.k, k)] none false ci.nt)
    recordTop n0 (ss ++ ss1 ++ [cm])
    if let some v := (← get).settledVal x then
      if let .app (.vc _ c _) _ := v then
        if c != ci.pos && !ci.nt then throw s!"comptime-match: expected `{showName pat.show}`, got a value headed by another constructor"
    let (ss2, ts) ← elabSeq fsc want exp rest
    return (ss ++ ss1 ++ [fun k => .chk .cm (.fv x) .nil (.case (.fv x) [(n, ci.pos, ci.k, k)] none false ci.nt)] ++ ss2, ts)
  | .list [.atom "open-adt", m, e] :: rest =>
    elabSeq sc want exp (.list [.atom "let", .list [.list [m, .atom " open"]], e] :: .list [.atom " opened", m] :: rest)
  | .list [.atom " opened", m] :: rest => do
    let (oe, _) ← splitMult true [m]
    let i ← match sc.lookup " open" with
      | some (.fv i) | some (.ctor i) | some (.fn i _ _) => pure i
      | _ => throw "open-adt: no entry"
    modify fun st => { st with opened := i :: st.opened }
    let (ss, ts) ← elabSeq sc want exp rest
    return ((fun k => .chk (.opn oe) (.fv i) .nil k) :: ss, ts)
  | .list (.atom "unary" :: args) :: rest => do
    let lits ← args.mapM fun a => match litOf a with
      | some n => pure n
      | none => throw "`unary` takes a numeral or a character literal"
    let key ← match lits with
      | [a] => pure (a, none)
      | [a, b] => if b < a then pure (a, some b) else throw "unary: the floor is not below the literal"
      | _ => throw "malformed `unary` form"
    let some i := (← get).eqPf.lookup key | throw "unary: not interned"
    elabSeq ((" unary", .fv i) :: sc) want exp
      (.list [.atom "let-match", .atom "erased", .atom " unary", .list [.atom "Refl", .atom "_", .atom "_"]] :: rest)
  | .list [.atom "compile-warn", m] :: rest => do
    let (ss, msg) ← compileMsgE sc m
    warn msg
    let (ss2, ts) ← elabSeq sc want exp rest
    return (ss ++ ss2, ts)
  | e@(.list (.atom "compile-error" :: _)) :: _ | e@(.list (.atom "dump-context" :: _)) :: _ => do
    let _ ← elabExpr sc want exp e
    throw "unreachable"
  | .list (.atom kw :: .atom "_" :: fns) :: rest =>
    if kw != "def-fns" && kw != "def-unique" then throw s!"({kw} _ ...) is not a statement" else
    elabSeq sc want exp (.list [.atom "def-lvl", .atom " _"] :: .list (.atom kw :: .atom " _" :: fns) :: rest)
  | .list (.atom kw :: .atom L :: fns) :: rest => do
    if kw != "def-fns" && kw != "def-unique" then
      throw (if ["def-opaque", "def-prim", "slot-self", "open-at-fn"].contains kw then s!"{kw} is not supported"
        else s!"({kw} {L} ...) is not a statement")
    let isU := kw == "def-unique"
    if isU && fns.length != 1 then throw "def-unique defines one function"
    let lvl ← entry sc (.atom L)
    let sigs ← fns.mapM fun
      | .list (.list xs :: items) => do
        let (md, xs) ← splitMd true xs
        if isU && md == .many then throw "a def-unique function is marked `unique` or `erased`"
        if !isU && md == .uniq then throw "a def-fns function is marked `many` or `erased`; use def-unique for a unique function"
        let er := md.isEr
        let rec marks : List Sx → List String × List Sx
          | .atom m :: x :: rest =>
            if ["absurd", "extern", "at"].contains m && x != .atom ":" then
              let (ms, r) := marks (x :: rest); (m :: ms, r)
            else ([], .atom m :: x :: rest)
          | xs => ([], xs)
        let (ms, xs) := marks xs
        if ms.contains "at" then throw "`at` on a def-fns line is not supported"
        let ab := ms.contains "absurd"
        let (f, tgt, es) ← match xs with
          | f :: .atom "at" :: g :: .atom ":" :: es => pure (f, some g, es)
          | f :: .atom ":" :: es => pure (f, none, es)
          | _ => throw "malformed def-fns"
        if ms.contains "extern" then
          let st ← get
          unless st.inPrelude do throw "only the prelude may mark a definition `extern`"
          if tgt.isSome then throw "a function marked `extern` cannot have a `delegate` body"
          if let .atom n := f then
            unless ffiNames.contains n do throw s!"no extern implementation for `{showName n}`"
            if st.claimed.contains n then throw s!"`{showName n}` is already bound to its extern implementation by another declaration"
            let arity := ((← entryErs true (← splitArrow es).1).filter (!·.2)).length
            if let some k := ffiArity n then
              unless k == arity do throw s!"the extern implementation of `{showName n}` takes {k} arguments, its model {arity}"
            modify fun st => { st with claimed := n :: st.claimed }
        let (ps, rs) ← splitArrow es
        pure (← name f, (er, ab, tgt), ps, rs, items, ← entryMds true ps)
      | _ => throw "malformed def-fns"
    let st ← get
    let base := st.n
    let ers := st.ers
    let _ ← freshMd (sigs.map fun sg => if sg.2.1.1 then Mode.er else if isU then .uniq else .many)
    let cap0 := (← get).captures
    if !isU then modify fun st => { st with captures := base }
    let (d0, g0) := ((← get).dele, (← get).delegated)
    let fnsc := (sigs.zipIdx.map fun ((f, _), j) => (f, Ref.fn (base + j) lvl sigs[j]!.2.2.2.2.2)).reverse ++ sc
    let tgts ← sigs.zipIdx.mapM fun ((_, (_, _, tgt), _), j) => tgt.mapM (entry (fnsc.drop (sigs.length - j)))
    let g0 := (← get).ghost
    modify fun st => { st with deles := st.deles ++ (sigs.zip tgts).zipIdx.filterMap fun (((_, (er, _), _), t), j) =>
      if er || g0 then none else t.map (base + j, ·) }
    let defs ← sigs.zipIdx.mapM fun ((_, (er, ab, _), ps, rs, items, _), j) => do
      let tgt := tgts[j]!
      let ds0 := (← get).deles
      let ers0 := (← get).ers
      if let some t := tgt then
        modify fun st => { st with ers := st.ers.zipIdx.map fun (e, i) => e || (i < base + sigs.length && i != t) }
      let tele ← elabTele (fnsc.drop (sigs.length - j)) 0 true (ps ++ rs)
      reset (base + sigs.length)
      let pents ← entryErs true ps
      let pids ← freshMd (← entryMds true ps)
      let _ ← pids.foldlM (fun t i => match t with
        | .bind (.is ..) e r => do note i e true; pure (r.inst (.fv i) 0)
        | .bind _ A r => do note i A; pure (r.inst (.fv i) 0)
        | t => pure t) tele
      let rents ← entryMds true rs
      modify fun st => { st with dele := tgt.map (·, pids.zip (pents.map (·.2))), delegated := false }
      let body ← withTail (!ab) <| ghostly (er || ab) (elabBody ((pents.map (·.1)).zip (pids.zipWith entRef (teleTys tele)) |>.reverse |>.append (if isU then sc else fnsc))
        (if ab then [Mode.er] else rents.map fun e => if er then .er else e) items
        (if ab then none else some (pids.foldl (fun t i => match t with | .bind _ _ r => r.inst (.fv i) 0 | t => t) tele)) ab)
      if tgt.isSome && !(← get).delegated then throw "a function written `at f` must have a `delegate` body"
      modify fun st => { st with deles := ds0, ers := ers0 ++ st.ers.drop ers0.length }
      pure { er, np := pents.length, tele, body := if ab then .absurd body else body, dele := tgt, u := isU : FnDef }
    modify fun st => { st with dele := d0, delegated := g0, captures := cap0 }
    let gid := (← get).groups.length
    reset (base + sigs.length)
    for (F, j) in defs.zipIdx do note (base + j) (F.type { lvl, fns := defs })
    modify fun st => { st with groups := st.groups ++ [{ ers, ghost := st.ghost, lvl, fns := defs }] }
    recordTop base [Core.defFns gid]
    let pfs ← ((← get).deles.filter (·.1 ≥ base)).mapM fun (i, t) => do
      let (s, k) ← mintDele i t
      recordTop k [s]
      modify fun st => { st with delePf := (i, k) :: st.delePf }
      pure s
    let (ss, ts) ← elabSeq fnsc want exp rest
    return (.defFns gid :: pfs ++ ss, ts)
  | e :: _ => match e with
    | .list (.atom h :: _) =>
      if ["comptime-match", "compile-warn", "compile-error", "dump-context", "def-opaque",
          "def-prim", "slot-self", "open-at-fn", "unary"].contains h then throw s!"{h} is not supported"
      else throw s!"{e.show.take 40} is not a statement"
    | _ => throw s!"{e.show.take 40} is not a statement"

partial def elabBody (sc : Scope) (want : List Mode) (items : List Sx) (exp : Option Tm := none)
    (refute : Bool := false) : M Core := do
  let (r0, f0, a0, c0, o0) := ((← get).rhs, (← get).refute, (← get).adts, (← get).ctors, (← get).opened)
  let d0 := (← get).depthTop
  modify fun st => { st with rhs := false, refute, depthTop := false }
  let (ss, ts) ← elabSeq sc want exp items
  modify fun st => { st with rhs := r0, refute := f0, adts := a0, ctors := c0, opened := o0, depthTop := d0 }
  return close ss ts
end

def statements : List String := ["def-adts", "def-lvl", "def-fns", "let", "let-match", "open-adt", "def-unique",
  "comptime-match", "unary", "compile-warn", "dump-context", "slot-self", "open-at-fn", "def-opaque", "def-prim"]

def nullary (name : String) (d : Nat) (cs : List String) : Adt :=
  { params := .nil, ctors := cs.map fun _ => .bind (.ty false false false) (.app (.tyc d .nil) .nil) .nil, name, ctorNames := cs }

def coercibleAdt : Adt :=
  let sh : Tm := .app (.tyc sharingD .nil) .nil
  let e (A : Tm) (r : Tm) : Tm := .bind (.ty false true false) A r
  { params := e sh (e .univ (e (.bv 0) (e sh (e .univ (e (.bv 0) .nil))))), ctors := [], name := "Coercible",
    coercible := true }

def delegateAdt : Adt := { coercibleAdt with name := "Delegate" }

def builtins : ESt :=
  { decls := [nullary "Special" 0 (specialNames.map ("%" ++ ·)), nullary "Sharing" sharingD ["Unique", "Shared"], coercibleAdt,
      delegateAdt],
    adts := [("Delegate", 3), ("Coercible", 2), ("Sharing", sharingD), ("Special", 0)],
    ctors := [("Shared", sharingD, 1), ("Unique", sharingD, 0)] ++ specialNames.mapIdx fun i n => ("%" ++ n, 0, i),
    special := 0 }

def elabProgram (items : List Sx) (pre : Bool) : Except String (Prog × List String) := do
  let stmt := match (items.filter (!isPragmaSx ·)).getLast? with
    | some (.list (.atom h :: _)) => statements.contains h
    | _ => false
  let ((ss, ts), st) ← (elabSeq [] (if stmt then [] else [false]) none
    (if stmt then items ++ [.list [.atom "values"]] else items)).run { builtins with pre }
  unless ts.length == (if stmt then 0 else 1) do throw "the top level has size one"
  let ws := st.warns ++ (st.supp.filter (·.2.2 == 0)).map fun (x, _, _) => s!"`;! suppress warn` for `{x}` silenced nothing"
  return ({ adts := st.decls, groups := st.groups, main := close ss ts }, ws)

def load (src : String) (pre : Bool := true) : Except String (Prog × List String) := do elabProgram (← parse src) pre

end Minimal
