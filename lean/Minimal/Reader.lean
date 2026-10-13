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

partial def tokenize (cs : List Char) (acc : List String) : List String :=
  match cs with
  | [] => acc.reverse
  | ';' :: '!' :: _ => (";!" :: acc).reverse
  | ';' :: rest => tokenize (rest.dropWhile (· != '\n')) acc
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc
    else if c == '(' || c == ')' then tokenize rest (c.toString :: acc)
    else
      let w := cs.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')' && c != ';'
      tokenize (cs.drop w.length) (String.ofList w :: acc)

partial def parseItems : List String → Except String (List Sx × List String)
  | [] => .ok ([], [])
  | ";!" :: _ => .error "pragmas are not supported"
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

def parse (src : String) : Except String (List Sx) := do
  match ← parseItems (tokenize src.toList []) with
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

abbrev M := StateT ESt (Except String)

def keywords : List String :=
  ["def-adts", "def-lvl", "def-fns", "let", "match", "values", "prove-subterm", "prove-predates",
   "predates-trans", "subterm-trans", "predates-subterm", "predates", "subterm", "is", "level-of", "else",
   "erased", "many", "unique", "absurd", "Fn", "Type", "Level", "Predates", "Subterm"]

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
    | _, _ => throw s!"unbound name {x}"

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
    if x ∈ keywords || x.all Char.isDigit || x.startsWith "\"" || x.startsWith "#\\" then throw s!"{x} is not a name"
    else if x.startsWith "__" then throw s!"{x} begins with __, which is reserved"
    else pure x
  | _ => throw "malformed name"

def parseEntry (need : Bool) : Sx → M (Ent × Sx × List String)
  | .list xs => do
    if xs.contains (.atom "at") then throw "at is not supported"
    let (sub, xs) := match xs with | .atom "subterm" :: xs => (true, xs) | xs => (false, xs)
    let (er, xs) ← splitMult need xs
    match xs with
    | [e, .atom "is", x] => if sub then throw "an is entry cannot be subterm" else pure (.is er, e, [← name x])
    | T :: x :: xs => pure (.ty sub er, T, ← (x :: xs).mapM name)
    | _ => throw "malformed telescope entry"
  | _ => throw "malformed telescope entry"

def entryErs (need : Bool) (es : List Sx) : M (List (String × Bool)) :=
  es.flatMapM fun e => do let (k, _, xs) ← parseEntry need e; pure (xs.map (·, k.er))

def Ent.withEr : Ent → Bool → Ent
  | .ty m _, e => .ty m e
  | .is _, e => .is e

def setErs : Tm → List Bool → Tm
  | .bind k A r, e :: es => .bind (k.withEr e) A (setErs r es)
  | t, _ => t

def fieldErs : Tm → List Bool
  | .bind k _ r@(.bind ..) => k.er :: fieldErs r
  | _ => []

mutual
partial def elabTm (sc : Scope) (depth : Nat) : Sx → M Tm
  | .atom "Type" => pure .univ
  | e@(.atom x) => match e.numerals with
    | [n] => do match (← get).lits.lookup n with
      | some i => pure (.fv i)
      | none => throw s!"the numeral {x} is not interned"
    | _ => look sc depth x
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
  let mut ids : List Nat := (raw.flatMap fun (p, ss) => p.fvs ++ ss.flatMap Tm.fvs).eraseDups
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

def entry (sc : Scope) : Sx → M Nat
  | .atom x => match sc.lookup x with
    | some (.fv i) | some (.fn i _ _) => pure i
    | _ => throw s!"{x} is not an entry"
  | .list [.atom "level-of", .atom f] => levelOf sc f
  | _ => throw "not an entry"

def internLits (e : Sx) : M (List Stmt) := do
  let st ← get
  let ns := (e.numerals.filter fun n => (st.lits.lookup n).isNone).eraseDups
  if ns.isEmpty then return []
  unless st.pre do throw "a numeral needs the prelude's Nat, which --no-prelude leaves out"
  if ns.any (· > 100000) then throw "a numeral above 100000 is not supported: the runner holds a Nat in unary"
  let some d := (st.adts.filter (·.1 == "Nat")).getLast?.map (·.2) | throw "a numeral needs the prelude's Nat"
  let ctor (c : String) := (st.ctors.find? fun (x, d', _) => x == c && d' == d).map (·.2.2)
  let (some z, some sc) := (ctor "Zero", ctor "Succ") | throw "a numeral needs the prelude's Nat"
  ns.mapM fun n => do
    let [i] ← fresh [false] | throw "fresh"
    note i (.app (.tyc d) .nil)
    modify fun st => { st with lits := (n, i) :: st.lits }
    let t := (List.range n).foldl (fun t _ => Tm.app (.vc d sc) (.cons t .nil)) (.app (.vc d z) .nil)
    return (.prim (.lit t) false : Stmt)

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

mutual
partial def elabExpr (sc : Scope) (want : List Bool) (exp : Option Tm) : Sx → M (List Stmt × List Tm)
  | .list (.atom "values" :: es) => elabArgs sc es want
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
        let (ss, ts) ← elabArgs sc args ((fieldErs sig).drop ((st.lifts.lookup d).getD []).length); return (ss, [.app (.vc d c) (.ofList ((← liftOf d) ++ ts))])
      | _, _ =>
        unless h ∈ keywords ++ ["TyCtor", "ValCtor", "Matchable"] do throw s!"unbound name {h}"
        return ([], [← elabTm sc 0 e])
    else if let some (.ctor i) := sc.lookup h then
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
        | some p => do let (ss, ps) ← elabArgs sc [p]; pure (Dec.predates ps.head!, ss, args)
        | none => match args.findIdx? (fun (x : Sx) => match x with | .list [.atom "subterm", _] => true | _ => false) with
          | some pos => match args[pos]! with
            | .list [_, p] => do
              let (ss, ps) ← elabArgs sc [p]
              pure (Dec.subterm pos ps.head!, ss, args.eraseIdx pos)
            | _ => throw "unreachable"
          | none => pure (Dec.none, [], args)
      let (ss, ts) ← elabArgs sc args (match sc.lookup h with | some (.fn _ _ ms) => ms | _ => [])
      let outs ← fresh want
      let known := (← get).known
      if let some (.fn _ _ tele) := (match f with | .fv i => known.lookup i | _ => none) then
        let _ ← (ts ++ outs.map Tm.fv).zipIdx.foldlM (fun t (a, k) => match t with
          | .bind k' A r => do
            if ts.length ≤ k then
              note (outs.getD (k - ts.length) 0) A (k' matches .is _)
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
  let outs ← fresh rms
  return (ss ++ [if real then .seq R (.case s out els true) else .mtch s R out els er], outs.map .fv)

partial def elabSeq (sc : Scope) (want : List Bool) (exp : Option Tm := none) (items : List Sx) :
    M (List Stmt × List Tm) := do
  let ss ← match items with
    | e :: _ => if (← get).top then internLits e else pure []
    | [] => pure []
  let (ss2, ts) ← elabSeq' sc want exp items
  return (ss ++ ss2, ts)

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
    modify fun st => { st with inPrelude := !st.pre }
    elabSeq sc want exp rest
  | .list (.atom "def-adts" :: bs) :: rest => do
    declareAdts sc bs
    elabSeq sc want exp rest
  | .list [.atom "def-lvl", .atom L] :: rest => do
    if L != " _" then discard <| name (.atom L)
    let [i] ← fresh [true] | throw "fresh"
    note i .level
    let (ss, ts) ← elabSeq ((L, .fv i) :: sc) want exp rest
    return (.defLvl :: ss, ts)
  | .list (.atom "let" :: .list xs :: items) :: rest => do
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
    let (r0, f0) := ((← get).rhs, (← get).refute)
    modify fun st => { st with rhs := true, refute := false }
    let (ss, ts) ← withTail ((← get).tail && returnsBinders ((bs.filter (!·.2.1)).map (·.1)) want rest) (elabSeq sc (bs.map (·.2.1)) bexp items)
    modify fun st => { st with rhs := r0, refute := f0 }
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
    let (ss2, ts2) ← elabSeq sc' want exp rest
    return (ss ++ ss2, ts2)
  | .list (.atom "let-match" :: args) :: rest => do
    let (er, args) ← splitMult true args
    if !er && (← get).ghost then throw "a let-match written many in an erased position"
    let s :: pat :: brs := args | throw "malformed let-match"
    let (ss, sts) ← withTail false (elabExpr sc [er] none s)
    let [s] := sts | throw "let-match: one scrutinee"
    if (← get).rhs && brs.any (fun | .list (.atom "absurd" :: _) => false | _ => true) then
      throw "a let-match with more than one real branch outside a body"
    let (out, els) ← elabArms sc er false want exp brs 1
    let (n, ci, fsc) ← openPattern sc er pat
    if out.any (·.2.1 == ci.pos) then throw "two branches for one constructor"
    if !er && ci.phantom then throw "a let-match on a phantom constructor at many"
    let (ss2, ts) ← elabSeq fsc want exp rest
    return (ss ++ [fun k => .case s ((n, ci.pos, ci.k, k) :: out) els er] ++ ss2, ts)
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
        let f :: .atom ":" :: es := xs | throw "malformed def-fns"
        let (ps, rs) ← splitArrow es
        pure (← name f, (er, ab), ps, rs, items, (← entryErs true ps).map (·.2))
      | _ => throw "malformed def-fns"
    let st ← get
    let base := st.n
    let ers := st.ers
    let _ ← fresh (sigs.map (·.2.1.1))
    let fnsc := (sigs.zipIdx.map fun ((f, _), j) => (f, Ref.fn (base + j) lvl sigs[j]!.2.2.2.2.2)).reverse ++ sc
    let defs ← sigs.mapM fun (_, (er, ab), ps, rs, items, _) => do
      let tele ← elabTele sc 0 true (ps ++ rs)
      reset (base + sigs.length)
      let pents ← entryErs true ps
      let pids ← fresh (pents.map (·.2))
      let _ ← pids.foldlM (fun t i => match t with
        | .bind (.is _) e r => do note i e true; pure (r.inst (.fv i) 0)
        | .bind _ A r => do note i A; pure (r.inst (.fv i) 0)
        | t => pure t) tele
      let rents ← entryErs true rs
      let body ← withTail (!ab) <| ghostly (er || ab) (elabBody ((pents.map (·.1)).zip (pids.zipWith entRef (teleTys tele)) |>.reverse |>.append fnsc)
        (if ab then [true] else rents.map fun e => er || e.2) items
        (if ab then none else some (pids.foldl (fun t i => match t with | .bind _ _ r => r.inst (.fv i) 0 | t => t) tele)) ab)
      pure { er, np := pents.length, tele, body := if ab then .absurd body else body : FnDef }
    let gid := (← get).groups.length
    reset (base + sigs.length)
    for (F, j) in defs.zipIdx do note (base + j) (F.type { lvl, fns := defs })
    modify fun st => { st with groups := st.groups ++ [{ ers, ghost := st.ghost, lvl, fns := defs }] }
    let (ss, ts) ← elabSeq fnsc want exp rest
    return (.defFns gid :: ss, ts)
  | e :: _ => match e with
    | .list (.atom h :: _) =>
      if ["comptime-match", "def-unique", "compile-warn", "compile-error", "dump-context", "def-opaque",
          "def-prim", "slot-self", "open-at-fn", "unary"].contains h then throw s!"{h} is not supported"
      else throw s!"{e.show.take 40} is not a statement"
    | _ => throw s!"{e.show.take 40} is not a statement"

partial def elabBody (sc : Scope) (want : List Bool) (items : List Sx) (exp : Option Tm := none)
    (refute : Bool := false) : M Core := do
  let (r0, f0, a0, c0, o0) := ((← get).rhs, (← get).refute, (← get).adts, (← get).ctors, (← get).opened)
  modify fun st => { st with rhs := false, refute }
  let (ss, ts) ← elabSeq sc want exp items
  modify fun st => { st with rhs := r0, refute := f0, adts := a0, ctors := c0, opened := o0 }
  return close ss ts
end

def statements : List String := ["def-adts", "def-lvl", "def-fns", "let", "let-match", "open-adt"]

def elabProgram (items : List Sx) (pre : Bool) : Except String Prog := do
  let stmt := match items.getLast? with
    | some (.list (.atom h :: _)) => statements.contains h
    | _ => false
  let ((ss, ts), st) ← (elabSeq [] (if stmt then [] else [false]) none
    (if stmt then items ++ [.list [.atom "values"]] else items)).run { pre }
  unless ts.length == (if stmt then 0 else 1) do throw "the top level has size one"
  return { adts := st.decls, groups := st.groups, main := close ss ts }

def load (src : String) (pre : Bool := true) : Except String Prog := do elabProgram (← parse src) pre

end Minimal
