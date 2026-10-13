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

def specialNames : List String :=
  ["let", "def-lvl", "def-fns", "def-unique", "def-adts", "comptime-match", "let-match", "open-adt", "slot-self",
   "open-at-fn", "unary", "dump-context", "compile-error", "compile-warn", "Fn", "UniqueFn", "TyCtor", "ValCtor",
   "Matchable", "Cell", "match", "values", "coerce", "share", "cell-alloc", "cell-write", "cell-match",
   "open-absurd", "world-do", "settled-of", "settled-type", "settled-erase", "settled-mult", "settled-value",
   "gensym", "settled-eq", "intern-nat", "intern-char", "intern-string", "resolve", "read-file", "at",
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

inductive Ref where
  | fv (i : Nat)
  | bnd (lv : Nat)
  | fn (i lvl : Nat) (ers : List Bool)
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
  match st.inl.lookup i, ((st.known.filter (·.1 == i)).getLast?).map (·.2) with
  | some (.app (.vc d _) .nil), _ => d == st.special
  | _, some T => st.factCanon 100 T == .app (.tyc st.special) .nil
  | _, _ => false

def warn (msg : String) : M Unit := modify fun st => { st with warns := st.warns ++ [msg] }

def warnUse (t : Tm) (kind shown : String) : M Unit := do
  let st ← get
  if st.inPrelude then return
  let some (_, msg) := st.pwarn.find? (·.1 == t) | return
  match st.supp.findIdx? (·.2.1 == some t) with
  | some k => set { st with supp := st.supp.modify k fun (x, y, n) => (x, y, n + 1) }
  | none => warn (if kind == "match" then s!"match on `{shown}`: {msg}" else s!"{kind} of `{shown}`: {msg}")

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

def look (sc : Scope) (depth : Nat) (x : String) : M Tm := do
  if x == "_" then return .hole
  match sc.lookup x with
  | some (.fv i) | some (.fn i _ _) | some (.ctor i) => pure (.fv i)
  | some (.bnd lv) => pure (.bv (depth - 1 - lv))
  | none => do
    let st ← get
    let first (d : Nat) := if ((st.lifts.lookup d).getD []).isEmpty then pure () else
      throw s!"{x} mentions top-level entries and is not first class"
    match st.adts.lookup x, st.ctors.lookup x with
    | some d, _ => first d; pure (.tyc d)
    | _, some (d, c) => first d; pure (.vc d c)
    | _, _ =>
      match specialNames.idxOf? x with
      | some c => if st.decls.length > 0 then pure (.app (.vc st.special c) .nil) else throw s!"unbound name {showName x}"
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
    | some (.fn (.fv l) _ _) => pure l
    | _ => throw s!"level-of: the level of {f} is not known"
  | _ => throw s!"level-of: {f} is not a function in scope"

def splitMult (need : Bool := true) : List Sx → M (Bool × List Sx)
  | .atom "erased" :: xs => pure (true, xs)
  | .atom "many" :: xs => pure (false, xs)
  | .atom "unique" :: _ => throw "unique is not supported"
  | xs => if need then throw "a multiplicity is required" else pure (false, xs)

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
    let (er, xs) ← splitMult need xs
    match xs with
    | [e, .atom "is", x] => pure (.is sub er, e, [← name x])
    | T :: x :: xs => pure (.ty sub er, T, ← (x :: xs).mapM name)
    | _ => throw "malformed telescope entry"
  | _ => throw "malformed telescope entry"

def entryErs (need : Bool) (es : List Sx) : M (List (String × Bool)) :=
  es.flatMapM fun e => do let (k, _, xs) ← parseEntry need e; pure (xs.map (·, k.er))

def Ent.withEr : Ent → Bool → Ent
  | .ty m _, e => .ty m e
  | .is m _, e => .is m e

def setErs : Tm → List Bool → Tm
  | .bind k A r, e :: es => .bind (k.withEr e) A (setErs r es)
  | t, _ => t

def fieldErs : Tm → List Bool
  | .bind k _ r@(.bind ..) => k.er :: fieldErs r
  | _ => []

def resolveHead (sc : Scope) : Sx → M Sx
  | e@(.list (.atom h :: args)) => do
    let st ← get
    match sc.lookup h with
    | some r =>
      let i := match r with | .fv i | .fn i _ _ | .ctor i => some i | _ => none
      match i.bind st.settledVal with
      | some (.app (.vc d c) _) =>
        if d == st.special && st.decls.length > 0 && (i.map st.mintedSpecial).getD false then
          let s := specialNames.getD c ""
          if (sc.lookup s).isSome then throw s!"the special form {s} is shadowed where {showName h} dispatches to it"
          return .list (.atom s :: args)
        else if h ∈ keywords then return .list (.list [.atom "\x03var", .atom h] :: args) else return e
      | _ => if h ∈ keywords then return .list (.list [.atom "\x03var", .atom h] :: args) else return e
    | none => return e
  | e => return e

partial def natOfVal : Tm → Option Nat
  | .app (.vc _ 0) .nil => some 0
  | .app (.vc _ 1) (.cons x .nil) => (natOfVal x).map (· + 1)
  | _ => none

def ESt.adtName (st : ESt) (d : Nat) : String := ((st.decls[d]?).map (·.name)).getD ""

partial def ESt.strOfVal (st : ESt) : Tm → Option (List Char)
  | .app (.vc d 0) _ => if st.firstAdt "String" == some d then some [] else none
  | .app (.vc d 1) args => do
    if st.firstAdt "String" != some d then none
    let as := args.toList
    let .app (.vc _ 0) cargs := as[as.length - 2]! | none
    let .app (.vc _ 0) uargs := cargs.toList.getLast! | none
    let us := uargs.toList
    let n ← natOfVal us[us.length - 2]!
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

def dumpContext (sc : Scope) : String :=
  "`dump-context` stops elaboration here and reports what the checker knows; in scope: " ++
    ", ".intercalate ((sc.map (showName ·.1)).filter (!·.startsWith " ")).eraseDups

mutual
partial def elabTm (sc : Scope) (depth : Nat) (e : Sx) : M Tm := do
  match ← resolveHead sc e with
  | .list [.atom "\x03var", .atom x] => look sc depth x
  | .list (.list [.atom "\x03var", .atom x] :: args) =>
    return .app (← look sc depth x) (.ofList (← args.mapM (elabTm sc depth)))
  | e => elabTm' sc depth e

partial def elabTm' (sc : Scope) (depth : Nat) : Sx → M Tm
  | .atom "Type" => pure .univ
  | .list [.atom "compile-error", m] => do throw (← compileMsg sc m)
  | .list [.atom "dump-context"] => throw (dumpContext sc)
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
  | .list [.atom "level-of", .atom f] => return .fv (← levelOf sc f)
  | .list [.atom "Predates", A, x, L] =>
    return .predates (← elabTm sc depth A) (← elabTm sc depth x) (← elabTm sc depth L)
  | .list [.atom "Subterm", A, a, B, b] =>
    return .subterm (← elabTm sc depth A) (← elabTm sc depth a) (← elabTm sc depth B) (← elabTm sc depth b)
  | .list (.atom "Fn" :: l :: es) => do
    let l ← elabTm sc depth l
    let (ps, rs) ← splitArrow es
    let t ← elabTele sc depth true (ps ++ rs)
    return .fn l (← entryErs true ps).length t
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
    | none, some d, _ => pure (.app (.tyc d) (.ofList (lift d ++ args)))
    | none, _, some (d, c) => pure (.app (.vc d c) (.ofList (lift d ++ args)))
    | some _, _, _ => pure (.app (← look sc depth h) (.ofList args))
    | _, _, _ => throw s!"{h} is not a type or constructor, in a type"
  | e => throw s!"malformed term {e.show.take 40}"

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

def reset (base : Nat) : M Unit := modify fun st =>
  { st with n := base, ers := st.ers.take base, known := st.known.filter (·.1 < base),
            inl := st.inl.filter (·.1 < base), opened := st.opened.filter (· < base) }

def liftOf (d : Nat) : M (List Tm) := return (((← get).lifts.lookup d).getD []).map Tm.fv

def note (i : Nat) (T : Tm) (isTerm : Bool := false) : M Unit := modify fun st =>
  if isTerm then { st with inl := (i, T) :: st.inl } else { st with known := (i, T) :: st.known }

def abst (ids : List Nat) : Nat → Tm → Tm
  | D, .fv i => match ids.idxOf? i with
    | some k => .bv (D - 1 - k)
    | none => .fv i
  | D, .cons h t => .cons (abst ids D h) (abst ids D t)
  | D, .bind k a r => .bind k (abst ids D a) (abst ids (D + 1) r)
  | D, .app h a => .app (abst ids D h) (abst ids D a)
  | D, .tyCtor p => .tyCtor (abst ids D p)
  | D, .valCtor p => .valCtor (abst ids D p)
  | D, .predates A x L => .predates (abst ids D A) (abst ids D x) (abst ids D L)
  | D, .subterm A a B b => .subterm (abst ids D A) (abst ids D a) (abst ids D B) (abst ids D b)
  | D, .fn l np t => .fn (abst ids D l) np (abst ids D t)
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
  for _ in List.range (st.n + 1) do
    let more ← ids.flatMapM fun i => match st.known.lookup i with
      | some T => pure (inline T).fvs
      | none => throw "a def-adts signature may mention only levels, def-fns functions and let binders written with a type or a term"
    ids := (ids ++ more).eraseDups
  ids := ids.mergeSort
  let liftTele := ids.zipIdx.foldr (fun (i, k) r =>
    .bind (.ty false true) (abst ids k (inline ((st.known.lookup i).getD .nil))) r) .nil
  modify fun st => { st with lifts := (heads.zipIdx.map fun (_, j) => (base + j, ids)) ++ st.lifts }
  if !(← get).inPrelude && blocks.any (fun | .list (_ :: kws) => kws.contains (.atom "extern") | _ => false) then
    throw "only the prelude may mark a definition `extern`"
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

def returnsBinders (xs : List String) (want : List Bool) : List Sx → Bool
  | [.list (.atom "values" :: es)] => (es.zip want).filterMap (fun (e, w) => if w then none else some e) == xs.map .atom
  | [e] => !want.head?.getD true && xs == [e.show]
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
  match runS P 10000000 (st.vals.take n0) c with
  | some vs => if vs.length == st.n - n0 then set { st with vals := st.vals.take n0 ++ vs }
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
  (List.range n).foldl (fun t _ => Tm.app (.vc d sc) (.cons t .nil)) (.app (.vc d z) .nil)

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
  let natTy := Tm.app (.tyc nat) .nil
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
    pure <| (List.range a).foldr (fun k t => app (.vc ltD ls) [nt (a - 1 - k), nt (b - 1 - k), t])
      (app (.vc ltD lz) [nt (b - a - 1)])
  let stc ← get
  let newChars := charsWanted.filter fun c => (stc.chars.lookup c).isNone
  if !newChars.isEmpty then
    let chr ← preAdt "Char"
    let u8 ← preAdt "U8"
    let some m := (← get).u8mod | throw "character literals need the prelude's u8-modulus"
    for c in newChars do
      if c > 255 then throw "a character literal is one byte"
      let (p, sp) ← assertPf (← ltTm c 256) (app (.tyc ltD) [← lit c, .fv m])
      out := out ++ [sp]
      let i ← fresh1 false
      let t := app (.vc chr 0) ((← liftOf chr) ++ [app (.vc u8 0) ((← liftOf u8) ++ [← lit c, .fv p])])
      note i (app (.tyc chr) (← liftOf chr))
      note i t true
      modify fun st => { st with chars := (c, i) :: st.chars }
      out := out ++ [.prim (.tm t) false]
  for str in strs.eraseDups do
    if ((← get).strs.lookup str).isSome then continue
    let sd ← preAdt "String"
    let nilC ← ctorIx sd "SNil"
    let consC ← ctorIx sd "SCons"
    let ls ← liftOf sd
    let mut t := app (.vc sd nilC) ls
    for c in str.reverse do
      let some ci := (← get).chars.lookup c | throw "unreachable"
      t := app (.vc sd consC) (ls ++ [.fv ci, t])
    let i ← fresh1 false
    note i (app (.tyc sd) ls)
    modify fun st => { st with strs := (str, i) :: st.strs }
    out := out ++ [.prim (.lit t) false]
  if !numOf.isEmpty then
    let bin ← preAdt "Bin"
    let numD ← preAdt "Numeral"
    let dbl ← preAdt "Double"
    let (bz, b1, b2) := (← ctorIx bin "BZ", ← ctorIx bin "B1", ← ctorIx bin "B2")
    let (nz, n1, n2) := (← ctorIx numD "NZ", ← ctorIx numD "N1", ← ctorIx numD "N2")
    let (d0, ds) := (← ctorIx dbl "D0", ← ctorIx dbl "DS")
    let dblTm (m : Nat) : Tm := (List.range m).foldl (fun t k => app (.vc dbl ds) [nt k, nt (2 * k), t]) (app (.vc dbl d0) [])
    let rec spell : Nat → Nat → Tm × Tm
      | 0, _ => (app (.vc bin bz) [], app (.vc numD nz) [])
      | _, 0 => (app (.vc bin bz) [], app (.vc numD nz) [])
      | fuel + 1, n + 1 =>
        let m := n / 2
        let (b, v) := spell fuel m
        if n % 2 == 0 then (app (.vc bin b1) [b], app (.vc numD n1) [b, nt m, nt (2 * m), v, dblTm m])
        else (app (.vc bin b2) [b], app (.vc numD n2) [b, nt m, nt (2 * m), v, dblTm m])
    for n in numOf.eraseDups do
      if ((← get).numPf.lookup n).isSome then continue
      let (b, v) := spell (n + 1) n
      let (i, sp) ← assertPf v (app (.tyc numD) [b, ← lit n])
      out := out ++ [sp]
      modify fun st => { st with numPf := (n, i) :: st.numPf }
  for (a, b) in ltOf.eraseDups do
    if ((← get).ltPf.lookup (a, b)).isSome then continue
    let (i, sp) ← assertPf (← ltTm a b) (app (.tyc ltD) [← lit a, ← lit b])
    out := out ++ [sp]
    modify fun st => { st with ltPf := ((a, b), i) :: st.ltPf }
  for (a, b) in eqOf.eraseDups do
    if ((← get).eqPf.lookup (a, b)).isSome then continue
    let eqD ← preAdt "Eq"
    let refl ← ctorIx eqD "Refl"
    let floor ← match b with | some b => lit b | none => pure (nt 0)
    let k := a - b.getD 0
    let rhs := (List.range k).foldl (fun t _ => app (.vc nat sc) [t]) floor
    let (i, sp) ← assertPf (app (.vc eqD refl) [natTy, nt a]) (app (.tyc eqD) [natTy, ← lit a, rhs])
    out := out ++ [sp]
    modify fun st => { st with eqPf := ((a, b), i) :: st.eqPf }
  return out

structure CtorInfo where
  k : Tm
  pos : Nat
  sig : Tm
  phantom : Bool
  union : Bool
  lifted : Nat

def ctorInfo (sc : Scope) (c : String) : M CtorInfo := do
  let st ← get
  let global (d ci : Nat) : M CtorInfo := do
    let some D := st.decls[d]? | throw s!"unknown constructor {c}"
    return ⟨.vc d ci, ci, D.ctors.getD ci .nil, D.phantom.getD ci false, D.union, D.lifted⟩
  match sc.lookup c with
  | some (.ctor i) | some (.fv i) =>
    if let some (.vc d ci) := st.inl.lookup i then return ← global d ci
    let found := st.opened.findSome? fun m => match st.known.lookup m with
      | some (.mtbl u _ _ ph _ cs) => (cs.toList.idxOf? (.fv i)).map fun p => (p, u, ph.getD p false)
      | _ => none
    match found, st.known.lookup i with
    | some (p, u, ph), some (.valCtor sig) => return ⟨.fv i, p, sig, ph, u, 0⟩
    | some _, _ => throw s!"{c} is not a value constructor"
    | none, _ => throw s!"{c} has no Matchable open"
  | _ => match st.ctors.lookup c with
    | some (d, ci) => global d ci
    | none => throw s!"unknown constructor {c}"

def openPattern (sc : Scope) (er : Bool) : Sx → M (Nat × CtorInfo × Scope)
  | .list (.atom c :: xs) => do
    let ci ← ctorInfo sc c
    let names ← xs.mapM name
    let names := (List.replicate ci.lifted " lift") ++ names
    unless names.length == (fieldErs ci.sig).length do throw s!"a pattern for {c} binds the wrong number of fields"
    let fs ← fresh (if er || ci.phantom then names.map fun _ => true else fieldErs ci.sig)
    return (names.length, ci, (names.zip (fs.zipWith (fun i T => entRef i T) (teleTys ci.sig))).reverse ++ sc)
  | _ => throw "malformed pattern"

def erasedPos (want : List Bool) : M Bool := return (← get).ghost || (!want.isEmpty && want.all id)

def bindTemp (sc : Scope) (t : Tm) (er : Bool) : M (List Stmt × Ref) := do
  match t with
  | .fv i => return ([], match (← get).inl.lookup i with | some (.vc ..) | some (.tyc _) => .ctor i | _ => refOf sc i)
  | _ => do
    let [j] ← fresh [er] | throw "fresh"
    note j t true
    return ([.prim (.tm t) er], match t with | .vc .. | .tyc _ => .ctor j | _ => .fv j)

def warnMatch (ks : List Tm) : M Unit := do
  let st ← get
  if let some d := ks.findSome? (fun | .vc d _ => some d | _ => none) then
    warnUse (.tyc d) "match" (showName ((st.decls[d]?).map (·.name)).get!)

def warnTarget (sc : Scope) (x : String) : M Tm := do
  let st ← get
  let fnTy (i : Nat) := match st.known.lookup i with | some (.fn ..) => true | _ => false
  match sc.lookup x with
  | some (.fn i _ _) => return .fv i
  | some (.fv i) | some (.ctor i) => match st.inl.lookup i with
    | some (.vc d c) => return .vc d c
    | some (.tyc d) => return .tyc d
    | _ => if fnTy i then return .fv i else throw s!"`;! warn` names `{showName x}`, which is neither a constructor nor a function"
  | some _ => throw s!"`;! warn` names `{showName x}`, which is neither a constructor nor a function"
  | none => match st.adts.lookup x, st.ctors.lookup x with
    | some d, _ => return .tyc d
    | _, some (d, c) => return .vc d c
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
partial def elabExpr (sc : Scope) (want : List Bool) (exp : Option Tm) (e : Sx) : M (List Stmt × List Tm) := do
  match ← resolveHead sc e with
  | .list [.atom "\x03var", .atom x] => return ([], [← look sc 0 x])
  | e@(.list (hd@(.list _) :: args)) => do
    if let some (ss, e') ← dispatchComputed sc e then
      let (ss2, ts) ← elabExpr sc want exp e'
      return (ss ++ ss2, ts)
    let (ss, ts) ← withTail false (elabExpr sc [(← erasedPos want)] none hd)
    let [t] := ts | throw "a computed head has one value"
    let (ss2, r) ← bindTemp sc t (← erasedPos want)
    let (ss3, ts) ← elabExpr ((" head", r) :: sc) want exp (.list (.atom " head" :: args))
    return (ss ++ ss2 ++ ss3, ts)
  | e => elabExpr' sc want exp e

partial def dispatchComputed (sc : Scope) : Sx → M (Option (List Stmt × Sx))
  | .list (hd@(.list _) :: args) => do
    let st0 ← get
    if !st0.top || st0.vals.length != st0.n then return none
    let (ss, ts) ← withTail false (elabExpr sc [false] none hd)
    let [t] := ts | throw "a computed head has one value"
    let st ← get
    let P : Prog := { adts := st.decls, groups := st.groups, main := .dead }
    match runS P 10000000 st0.vals (close ss [t]) with
    | some [.app (.vc d c) _] =>
      if d == st.special && st.decls.length > 0 then
        let f := specialNames.getD c ""
        if (sc.lookup f).isSome then throw s!"the special form {f} is shadowed where a computed head dispatches to it"
        return some (ss, .list (.atom f :: args))
      else set st0; return none
    | _ => set st0; return none
  | _ => return none

partial def elabExpr' (sc : Scope) (want : List Bool) (exp : Option Tm) : Sx → M (List Stmt × List Tm)
  | .list (.atom "values" :: es) => elabArgs sc es want
  | .list [.atom "compile-error", m] => do throw (← compileMsg sc m)
  | .list [.atom "dump-context"] => throw (dumpContext sc)
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
    else if h == "match" then elabMatch sc want exp args
    else if h == "open-absurd" && (sc.lookup h).isNone then
      let [e, _] := args | throw "open-absurd takes an expression and an annotation"
      let (ss, ts) ← withTail false (elabExpr sc [true] none e)
      let [t] := ts | throw "open-absurd: one value"
      let (ss2, i) ← (match t with
        | .fv i => pure ([], i)
        | t => do
          let js ← fresh [true]
          pure ([.prim (.tm t) true], js.headD 0) : M (List Stmt × Nat))
      let outs ← fresh want
      return (ss ++ ss2 ++ [fun _ => .chk (.opn true) (.fv i) .nil .dead], outs.map .fv)
    else if h == "matchable-of" && (sc.lookup h).isNone then
      let [.atom T] := args | throw "matchable-of takes a type constructor"
      let some d := st.adts.lookup T | throw s!"matchable-of: {T} is not a declared type"
      let [i] ← fresh [false] | throw "fresh"
      if let some D := st.decls[d]? then note i (D.mtbl d)
      return ([.prim (.mtblOf d) false], [.fv i])
    else if h == "delegate" && (sc.lookup h).isNone then
      let [x@(.list (.atom f :: cargs))] := args | throw "delegate wraps a call"
      if st.ghost || (!want.isEmpty && want.all id) then throw "delegate in an erased position"
      if !st.tail then throw "delegate: the call is not in tail position"
      let some (tgt, params) := st.dele | throw "a delegate body needs `at f` on its function's header"
      unless (← look sc 0 f) == .fv tgt do throw "delegate: the call is not to the function its header names"
      let ms := match sc.lookup f with | some (.fn _ _ ms) => ms | _ => []
      let plain := cargs.filter fun | .list [.atom "predates", _] | .list [.atom "subterm", _] => false | _ => true
      let passed ← ((plain.zip ms).filter (!·.2)).mapM fun (a, _) => entry sc a
      unless passed == params.filterMap (fun (i, e) => if e then none else some i) do
        throw "delegate: the non-erased parameters are not passed straight through, in order"
      modify fun st => { st with delegated := true }
      elabExpr sc want exp x
    else if (h == "tail" || h == "notail") && (sc.lookup h).isNone then
      let [x@(.list (.atom f :: _))] := args | throw s!"{h} wraps a call"
      if (st.adts.lookup f).isSome || (st.ctors.lookup f).isSome || keywords.contains f then throw s!"{h} wraps a call"
      if st.ghost || (!want.isEmpty && want.all id) then throw s!"{h} in an erased position"
      if h == "tail" && !st.tail then throw "tail: the call is not in tail position"
      if h == "notail" && st.tail then throw "notail: the call is in tail position"
      elabExpr sc want exp x
    else if h ∈ keywords || (sc.lookup h).isNone then
      match st.adts.lookup h, st.ctors.lookup h with
      | some d, _ => let (ss, ts) ← elabArgs sc args; return (ss, [.app (.tyc d) (.ofList ((← liftOf d) ++ ts))])
      | _, some (d, c) =>
        let sig := ((st.decls[d]?).bind (·.ctors[c]?)).getD .nil
        unless ← erasedPos want do warnUse (.vc d c) "application" (showName h)
        let (ss, ts) ← elabArgs sc args ((fieldErs sig).drop ((st.lifts.lookup d).getD []).length); return (ss, [.app (.vc d c) (.ofList ((← liftOf d) ++ ts))])
      | _, _ =>
        unless h ∈ ["Fn", "TyCtor", "ValCtor", "Matchable", "Level", "Predates", "Subterm", "level-of", "numeral-of", "prove-literal-lt"] do
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
      let args := args.filter fun | .list [.atom "predates", .atom "_"] | .list [.atom "subterm", .atom "_"] => false
                                  | _ => true
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
      let (ss, ts) ← elabArgs sc args (match sc.lookup h with | some (.fn _ _ ms) => ms | _ => [])
      let outs ← fresh want
      let known := (← get).known
      if let some (.fn _ _ tele) := (match f with | .fv i => known.lookup i | _ => none) then
        let _ ← (ts ++ outs.map Tm.fv).zipIdx.foldlM (fun t (a, k) => match t with
          | .bind k' A r => do
            if ts.length ≤ k then
              note (outs.getD (k - ts.length) 0) A (k' matches .is _ _)
            pure (r.inst a 0)
          | t => pure t) tele
      return (ss0 ++ ss ++ [.call f dec (.ofList ts) (!want.isEmpty && want.all id) want], outs.map .fv)
  | e => return ([], [← elabTm sc 0 e])

partial def elabArgs (sc : Scope) (es : List Sx) (ms : List Bool := []) : M (List Stmt × List Tm) := withTail false do
  let rs ← es.zipIdx.mapM fun (e, i) => elabExpr sc [ms.getD i false] none e
  return (rs.flatMap (·.1), rs.flatMap (·.2))

partial def elabArms (sc : Scope) (er gEr : Bool) (rms : List Bool) (R : Option Tm) (brs : List Sx) (extra : Nat := 0) :
    M (List Br × Option Core) := do
  let st ← get
  let base := st.n
  let mut out : List Br := []
  let mut infos : List CtorInfo := []
  let mut els : Option Core := none
  for br in brs do
    if let .list (.atom "else" :: items) := br then
      if els.isSome then throw "match: two else branches"
      reset base
      els := some (← ghostly gEr (elabBody sc rms items R))
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
    let (n, ci, fsc) ← openPattern sc er (.list (.atom c :: xs))
    let body ← ghostly (gEr || ab || (ci.phantom && !er)) (elabBody fsc (if ab then [true] else rms) items (if ab then none else R) ab)
    if out.any (·.2.1 == ci.pos) then throw "two branches for one constructor"
    out := out ++ [(n, ci.pos, ci.k, if ab then .absurd body else body)]
    infos := infos ++ [ci]
  reset base
  if !er && !(← get).ghost && infos.any (·.union) &&
      extra + ((out.zip infos).filter fun ((_, _, _, b), ci) => b.real && !ci.phantom).length + els.isSome.toNat > 1 then
    throw "a match without a runtime discriminant can have only one real branch"
  return (out, els)

partial def elabMatch (sc : Scope) (want : List Bool) (exp : Option Tm) (args : List Sx) : M (List Stmt × List Tm) := do
  let (er, args) ← splitMult true args
  if !er && ((← get).ghost || (!want.isEmpty && want.all id)) then throw "a match written many in an erased position"
  let s :: ann :: brs := args | throw "malformed match"
  let R0 ← match ann, exp with
    | .list rets, _ => elabTele sc 0 false rets
    | .atom "_", some R => pure R
    | _, _ => throw "a match annotation `_` where no telescope is expected"
  let (ss, sts) ← withTail false (elabExpr sc [er] none s)
  let [s] := sts | throw "match: one scrutinee"
  let real := er && !(← get).ghost && want.length == R0.len && want.any (!·)
  let rms := if er && !real then List.replicate R0.len true else want
  let R := setErs R0 rms
  let (out, els) ← elabArms sc er (er && !real) rms (some R) brs
  unless er || (← get).ghost do warnMatch (out.map (·.2.2.1))
  let outs ← fresh rms
  return (ss ++ [if real then .seq R (.case s out els true) else .mtch s R out els er], outs.map .fv)

partial def elabSeq (sc : Scope) (want : List Bool) (exp : Option Tm := none) (items : List Sx) :
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
    let e ← resolveHead sc e
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

partial def elabSeq' (sc : Scope) (want : List Bool) (exp : Option Tm) : List Sx → M (List Stmt × List Tm)
  | [] => throw "empty body"
  | [e] => do
    if !(← get).refute then return ← elabExpr sc want exp e
    match e with
    | .list (.atom "match" :: args@(_ :: _ :: .atom "_" :: _)) => do
      let (true, s :: _ :: brs) ← splitMult true args | throw "a refuting match is erased"
      let (ss, [s]) ← withTail false (elabExpr sc [true] none s) | throw "match: one scrutinee"
      let (out, els) ← elabArms sc true true [] none brs
      if els.isSome then throw "a refuting match has no else"
      return (ss ++ [(fun _ => .case s out none true : Stmt)], [])
    | e => do
      let (ss, [t]) ← elabExpr sc [true] none e | throw "a refutation is one value"
      return (ss ++ [(fun _ => .case t [] none true : Stmt)], [])
  | .list [.atom "__prelude-end"] :: rest => do
    let u8 : Option Nat := match sc.lookup "u8-modulus" with
      | some (.fv i) => some i
      | _ => none
    modify fun st => { st with inPrelude := !st.pre, u8mod := u8 }
    elabSeq sc want exp rest
  | .list (.atom "def-adts" :: bs) :: rest => do
    declareAdts sc bs
    elabSeq sc want exp rest
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
        let (er, xs) ← splitMult true xs
        if !er && (← get).ghost then throw "a let binder written many in an erased position"
        match xs with
        | [x] => pure (← name x, er, none)
        | [e, .atom "is", x] => pure (← name x, er, some (Chk.is, e))
        | [T, x] => pure (← name x, er, some (Chk.ty, T))
        | _ => throw "malformed let binder"
      | _ => throw "malformed let binder"
    let bexp ← if bs.all (·.2.2.isSome) then some <$> elabTele sc 0 true xs else pure none
    let (r0, f0, d0) := ((← get).rhs, (← get).refute, (← get).depthTop)
    modify fun st => { st with rhs := true, refute := false, depthTop := false }
    let (ss, ts) ← withTail ((← get).tail && returnsBinders ((bs.filter (!·.2.1)).map (·.1)) want rest) (elabSeq sc (bs.map (·.2.1)) bexp items)
    modify fun st => { st with rhs := r0, refute := f0, depthTop := d0 }
    if ts.length != bs.length then throw "let: wrong number of binders"
    let mut ss := ss
    let mut sc' := sc
    for ((x, er, ann), t) in bs.zip ts do
      let i ← match t with
        | .fv i => do
          if !er then ss := ss ++ [.chk .rt (.fv i) .nil]
          pure i
        | _ => do
          let [j] ← fresh [er] | throw "fresh"
          ss := ss ++ [.prim (.tm t) er]
          note j t true
          pure j
      let mut r := match t with | .tyc _ | .vc .. => .ctor i | _ => refOf sc i
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
    let (er, args) ← splitMult true args
    if !er && (← get).ghost then throw "a let-match written many in an erased position"
    let s :: pat :: brs := args | throw "malformed let-match"
    let (ss, sts) ← withTail false (elabExpr sc [er] none s)
    let [s] := sts | throw "let-match: one scrutinee"
    if (← get).rhs && brs.any (fun | .list (.atom "absurd" :: _) => false | _ => true) then
      throw "a let-match with more than one real branch outside a body"
    let (out, els) ← elabArms sc er false want exp brs 1
    let (n, ci, fsc) ← openPattern sc er pat
    unless er || (← get).ghost do warnMatch (ci.k :: out.map (·.2.2.1))
    if out.any (·.2.1 == ci.pos) then throw "two branches for one constructor"
    if !er && ci.phantom then throw "a let-match on a phantom constructor at many"
    recordTop n0 (ss ++ [(fun k => .case s ((n, ci.pos, ci.k, k) :: out) els er : Stmt)])
    if (← get).top then
      if let .fv j := s then
        if let some (.app (.tyc d) idx) := (← get).known.lookup j then
          if (← get).firstAdt "Eq" == some d then
            if let [_, .fv x, y] := idx.toList then modify fun st => { st with facts := (x, y) :: st.facts }
    let (ss2, ts) ← elabSeq fsc want exp rest
    return (ss ++ [fun k => .case s ((n, ci.pos, ci.k, k) :: out) els er] ++ ss2, ts)
  | .list (.atom "comptime-match" :: args) :: rest => do
    let n0 := (← get).n
    let (er, args) ← splitMult true args
    let st ← get
    unless st.top do throw "comptime-match is confined to run position"
    if er then throw "comptime-match is written many or unique"
    let [s, pat] := args | throw "malformed comptime-match"
    let (ss, sts) ← withTail false (elabExpr sc [false] none s)
    let [t] := sts | throw "comptime-match: one scrutinee"
    let (ss1, x) ← match t with
      | .fv x => pure ([], x)
      | t => do
        let [j] ← fresh [false] | throw "fresh"
        note j t true
        pure ([(.prim (.tm t) false : Stmt)], j)
    let (n, ci, fsc) ← openPattern sc false pat
    if ci.union then throw "comptime-match on a union"
    if ci.phantom then throw "comptime-match on a phantom constructor"
    warnMatch [ci.k]
    let cm : Stmt := fun k => Core.chk .cm (.fv x) .nil (.case (.fv x) [(n, ci.pos, ci.k, k)] none false)
    recordTop n0 (ss ++ ss1 ++ [cm])
    if let some v := (← get).settledVal x then
      if let .app (.vc _ c) _ := v then
        if c != ci.pos then throw s!"comptime-match: expected `{showName pat.show}`, got a value headed by another constructor"
    let (ss2, ts) ← elabSeq fsc want exp rest
    return (ss ++ ss1 ++ [fun k => .chk .cm (.fv x) .nil (.case (.fv x) [(n, ci.pos, ci.k, k)] none false)] ++ ss2, ts)
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
  | .list (.atom "def-fns" :: .atom "_" :: fns) :: rest =>
    elabSeq sc want exp (.list [.atom "def-lvl", .atom " _"] :: .list (.atom "def-fns" :: .atom " _" :: fns) :: rest)
  | .list (.atom "def-fns" :: .atom L :: fns) :: rest => do
    let lvl ← entry sc (.atom L)
    let sigs ← fns.mapM fun
      | .list (.list xs :: items) => do
        let (er, xs) ← splitMult true xs
        let (ab, xs) := match xs with | .atom "absurd" :: xs => (true, xs) | xs => (false, xs)
        let (f, tgt, es) ← match xs with
          | .atom m :: _ :: _ => if m == "at" || m == "extern" then throw s!"`{m}` on a def-fns line is not supported" else
            match xs with
            | f :: .atom "at" :: g :: .atom ":" :: es => pure (f, some g, es)
            | f :: .atom ":" :: es => pure (f, none, es)
            | _ => throw "malformed def-fns"
          | _ => throw "malformed def-fns"
        let (ps, rs) ← splitArrow es
        pure (← name f, (er, ab, tgt), ps, rs, items, (← entryErs true ps).map (·.2))
      | _ => throw "malformed def-fns"
    let st ← get
    let base := st.n
    let ers := st.ers
    let _ ← fresh (sigs.map (·.2.1.1))
    let (d0, g0) := ((← get).dele, (← get).delegated)
    let fnsc := (sigs.zipIdx.map fun ((f, _), j) => (f, Ref.fn (base + j) lvl sigs[j]!.2.2.2.2.2)).reverse ++ sc
    let defs ← sigs.zipIdx.mapM fun ((_, (er, ab, tgt), ps, rs, items, _), j) => do
      let tgt ← tgt.mapM (entry (fnsc.drop (sigs.length - j)))
      let tele ← elabTele sc 0 true (ps ++ rs)
      reset (base + sigs.length)
      let pents ← entryErs true ps
      let pids ← fresh (pents.map (·.2))
      let _ ← pids.foldlM (fun t i => match t with
        | .bind (.is _ _) e r => do note i e true; pure (r.inst (.fv i) 0)
        | .bind _ A r => do note i A; pure (r.inst (.fv i) 0)
        | t => pure t) tele
      let rents ← entryErs true rs
      modify fun st => { st with dele := tgt.map (·, pids.zip (pents.map (·.2))), delegated := false }
      let body ← withTail (!ab) <| ghostly (er || ab) (elabBody ((pents.map (·.1)).zip (pids.zipWith entRef (teleTys tele)) |>.reverse |>.append fnsc)
        (if ab then [true] else rents.map fun e => er || e.2) items
        (if ab then none else some (pids.foldl (fun t i => match t with | .bind _ _ r => r.inst (.fv i) 0 | t => t) tele)) ab)
      if tgt.isSome && !(← get).delegated then throw "a function written `at f` must have a `delegate` body"
      pure { er, np := pents.length, tele, body := if ab then .absurd body else body : FnDef }
    modify fun st => { st with dele := d0, delegated := g0 }
    let gid := (← get).groups.length
    reset (base + sigs.length)
    for (F, j) in defs.zipIdx do note (base + j) (F.type { lvl, fns := defs })
    modify fun st => { st with groups := st.groups ++ [{ ers, ghost := st.ghost, lvl, fns := defs }] }
    recordTop base [Core.defFns gid]
    let (ss, ts) ← elabSeq fnsc want exp rest
    return (.defFns gid :: ss, ts)
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
    warn (← compileMsg sc m)
    elabSeq sc want exp rest
  | e@(.list (.atom "compile-error" :: _)) :: _ | e@(.list (.atom "dump-context" :: _)) :: _ => do
    let _ ← elabExpr sc want exp e
    throw "unreachable"
  | e :: _ => match e with
    | .list (.atom h :: _) =>
      if ["comptime-match", "def-unique", "compile-warn", "compile-error", "dump-context", "def-opaque",
          "def-prim", "slot-self", "open-at-fn", "unary"].contains h then throw s!"{h} is not supported"
      else throw s!"{e.show.take 40} is not a statement"
    | _ => throw s!"{e.show.take 40} is not a statement"

partial def elabBody (sc : Scope) (want : List Bool) (items : List Sx) (exp : Option Tm := none)
    (refute : Bool := false) : M Core := do
  let (r0, f0, a0, c0, o0) := ((← get).rhs, (← get).refute, (← get).adts, (← get).ctors, (← get).opened)
  let d0 := (← get).depthTop
  modify fun st => { st with rhs := false, refute, depthTop := false }
  let (ss, ts) ← elabSeq sc want exp items
  modify fun st => { st with rhs := r0, refute := f0, adts := a0, ctors := c0, opened := o0, depthTop := d0 }
  return close ss ts
end

def statements : List String := ["def-adts", "def-lvl", "def-fns", "let", "let-match", "open-adt", "def-unique",
  "comptime-match", "unary", "compile-warn", "dump-context", "slot-self", "open-at-fn"]

def nullary (name : String) (d : Nat) (cs : List String) : Adt :=
  { params := .nil, ctors := cs.map fun _ => .bind (.ty false false) (.app (.tyc d) .nil) .nil, name, ctorNames := cs }

def builtins : ESt :=
  { decls := [nullary "Special" 0 (specialNames.map ("%" ++ ·)), nullary "Sharing" 1 ["Unique", "Shared"]],
    adts := [("Sharing", 1), ("Special", 0)], ctors := [("Shared", 1, 1), ("Unique", 1, 0)], special := 0 }

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
