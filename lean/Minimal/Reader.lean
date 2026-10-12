import Minimal.Check

namespace Minimal

inductive Sx where
  | atom (s : String)
  | list (xs : List Sx)
  deriving Repr, Inhabited, BEq

partial def tokenize (cs : List Char) (acc : List String) : List String :=
  match cs with
  | [] => acc.reverse
  | ';' :: rest => tokenize (rest.dropWhile (· != '\n')) acc
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc
    else if c == '(' || c == ')' then tokenize rest (c.toString :: acc)
    else
      let w := cs.takeWhile fun c => !c.isWhitespace && c != '(' && c != ')' && c != ';'
      tokenize (cs.drop w.length) (String.ofList w :: acc)

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
  known : List (Nat × Tm) := []
  inl : List (Nat × Tm) := []
  lifts : List (Nat × List Nat) := []
  adts : List (String × Nat) := []
  ctors : List (String × Nat × Nat) := []
  decls : List Adt := []
  groups : List Group := []

abbrev M := StateT ESt (Except String)

def keywords : List String :=
  ["def-adts", "def-lvl", "def-fns", "let", "match", "values", "prove-subterm", "prove-predates",
   "predates-trans", "subterm-trans", "predates-subterm", "predates", "subterm", "is", "level-of", "else",
   "erased", "many", "unique", "absurd", "Fn", "Type", "Level", "Predates", "Subterm"]

abbrev Scope := List (String × Ref)

def look (sc : Scope) (depth : Nat) (x : String) : M Tm := do
  if x == "_" then throw "`_` as an inferred argument is not supported"
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
  | _ => throw s!"level-of: {f} is not named by a def-fns in scope"

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
  | .atom x => if x ∈ keywords then throw s!"{x} is not a name" else pure x
  | _ => throw "malformed name"

def parseEntry (need : Bool) : Sx → M (Ent × Sx × List String)
  | .list xs => do
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
  | .atom x => look sc depth x
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
  | _ => throw "malformed term"

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
            inl := st.inl.filter (·.1 < base) }

def liftOf (d : Nat) : M (List Tm) := return (((← get).lifts.lookup d).getD []).map Tm.fv

def note (i : Nat) (T : Tm) (isTerm : Bool := false) : M Unit := modify fun st =>
  if !st.top then st else if isTerm then { st with inl := (i, T) :: st.inl } else { st with known := (i, T) :: st.known }

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
      if kw.any (· matches .atom "union" | .atom "newtype" | .atom "extern") then
        throw "union, newtype and extern types are not supported"
      unless kw matches [.atom "enum"] do throw "a type is declared enum"
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
  if !st.top then throw "def-adts is confined to the top level"
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
  for ((T, _, cs), (params, sigs)) in heads.zip (← elabSigs) do
    let ctorNames := cs.map (·.2.1)
    let adt : Adt := { params := teleAppend liftTele (abst ids ids.length params),
                       ctors := sigs.map (fun s => teleAppend liftTele (abst ids ids.length s)), name := T, ctorNames,
                       lifted := ids.length, phantom := cs.map (·.1) }
    modify fun st => { st with decls := st.decls ++ [adt] }

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

mutual
partial def elabExpr (sc : Scope) (want : List Bool) : Sx → M (List Stmt × List Tm)
  | .list (.atom "values" :: es) => elabArgs sc es
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
    else if h == "match" then elabMatch sc want args
    else if h ∈ keywords || (sc.lookup h).isNone then
      match st.adts.lookup h, st.ctors.lookup h with
      | some d, _ => let (ss, ts) ← elabArgs sc args; return (ss, [.app (.tyc d) (.ofList ((← liftOf d) ++ ts))])
      | _, some (d, c) =>
        let sig := ((st.decls[d]?).bind (·.ctors[c]?)).getD .nil
        let (ss, ts) ← elabArgs sc args ((fieldErs sig).drop ((st.lifts.lookup d).getD []).length); return (ss, [.app (.vc d c) (.ofList ((← liftOf d) ++ ts))])
      | _, _ => return ([], [← elabTm sc 0 e])
    else if let some (.ctor i) := sc.lookup h then
      let (ss, ts) ← elabArgs sc args; return (ss, [.app (.fv i) (.ofList ts)])
    else do
      let f ← look sc 0 h
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
      return (ss0 ++ ss ++ [.call f dec (.ofList ts) (!want.isEmpty && want.all id) want], outs.map .fv)
  | e => return ([], [← elabTm sc 0 e])

partial def elabArgs (sc : Scope) (es : List Sx) (ms : List Bool := []) : M (List Stmt × List Tm) := do
  let rs ← es.zipIdx.mapM fun (e, i) => elabExpr sc [ms.getD i false] e
  return (rs.flatMap (·.1), rs.flatMap (·.2))

partial def elabMatch (sc : Scope) (want : List Bool) (args : List Sx) : M (List Stmt × List Tm) := do
  let (er, args) ← splitMult true args
  if let _ :: .atom "_" :: _ := args then throw "a match annotation `_` is not supported"
  let s :: .list rets :: brs := args | throw "malformed match"
  let (ss, sts) ← elabExpr sc [false] s
  let [s] := sts | throw "match: one scrutinee"
  let n := (← entryErs false rets).length
  let rms := if er then List.replicate n true else want
  let R := setErs (← elabTele sc 0 false rets) rms
  let st ← get
  let base := st.n
  let mut out : List (Nat × Nat × Core) := []
  let mut els : Option Core := none
  for br in brs do
    if let .list (.atom "else" :: items) := br then
      if els.isSome then throw "match: two else branches"
      reset base
      els := some (← ghostly er (elabBody sc rms items))
      continue
    if let .list [.atom "absurd", .atom c] := br then
      let some (d', ci) := st.ctors.lookup c | throw s!"unknown constructor {c}"
      out := out ++ [(d', ci, .dead)]
      continue
    let (ab, br) := match br with
      | .list (.atom "absurd" :: rest) => (true, Sx.list rest)
      | br => (false, br)
    let .list (.list (.atom c :: xs) :: items) := br | throw "malformed branch"
    let some (d', ci) := st.ctors.lookup c | throw s!"unknown constructor {c}"
    let names ← xs.mapM fun | .atom x => pure x | _ => throw "malformed pattern"
    let names := ((← liftOf d').map fun _ => " lift") ++ names
    let sig := ((st.decls[d']?).bind (·.ctors[ci]?)).getD .nil
    reset base
    let ph := ((st.decls[d']?).bind (·.phantom[ci]?)).getD false
    let fs ← fresh (if er || ph then names.map fun _ => true else (fieldErs sig).take names.length)
    let body ← ghostly (er || ab || ph) (elabBody ((names.zip (fs.zipWith (fun i T => entRef i T) (teleTys sig))).reverse ++ sc)
      (if ab then [true] else rms) items)
    out := out ++ [(d', ci, if ab then .absurd body else body)]
  reset base
  let outs ← fresh rms
  return (ss ++ [.mtch s R out els er], outs.map .fv)

partial def elabSeq (sc : Scope) (want : List Bool) : List Sx → M (List Stmt × List Tm)
  | [] => throw "empty body"
  | [e] => elabExpr sc want e
  | .list (.atom "def-adts" :: bs) :: rest => do
    declareAdts sc bs
    elabSeq sc want rest
  | .list [.atom "def-lvl", .atom L] :: rest => do
    let [i] ← fresh [true] | throw "fresh"
    note i .level
    let (ss, ts) ← elabSeq ((L, .fv i) :: sc) want rest
    return (.defLvl :: ss, ts)
  | .list (.atom "let" :: .list xs :: items) :: rest => do
    let bs ← xs.mapM fun
      | .list xs => do
        let (er, xs) ← splitMult true xs
        match xs with
        | [x] => pure (← name x, er, none)
        | [e, .atom "is", x] => pure (← name x, er, some (Chk.is, e))
        | [T, x] => pure (← name x, er, some (Chk.ty, T))
        | _ => throw "malformed let binder"
      | _ => throw "malformed let binder"
    let (ss, ts) ← elabSeq sc (bs.map (·.2.1)) items
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
    let (ss2, ts2) ← elabSeq sc' want rest
    return (ss ++ ss2, ts2)
  | .list (.atom "def-fns" :: .atom "_" :: fns) :: rest =>
    elabSeq sc want (.list [.atom "def-lvl", .atom " _"] :: .list (.atom "def-fns" :: .atom " _" :: fns) :: rest)
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
      let rents ← entryErs true rs
      let body ← ghostly (er || ab) (elabBody ((pents.map (·.1)).zip (pids.zipWith entRef (teleTys tele)) |>.reverse |>.append fnsc)
        (if ab then [true] else rents.map fun e => er || e.2) items)
      pure { er, np := pents.length, tele, body := if ab then .absurd body else body : FnDef }
    let gid := (← get).groups.length
    reset (base + sigs.length)
    for (F, j) in defs.zipIdx do note (base + j) (F.type { lvl, fns := defs })
    modify fun st => { st with groups := st.groups ++ [{ ers, ghost := st.ghost, lvl, fns := defs }] }
    let (ss, ts) ← elabSeq fnsc want rest
    return (.defFns gid :: ss, ts)
  | e :: rest => do
    let (ss, _) ← elabExpr sc [] e
    let (ss2, ts) ← elabSeq sc want rest
    return (ss ++ ss2, ts)

partial def elabBody (sc : Scope) (want : List Bool) (items : List Sx) : M Core := do
  let (ss, ts) ← elabSeq sc want items
  return close ss ts
end

def elabProgram (items : List Sx) : Except String Prog := do
  let ((ss, ts), st) ← (elabSeq [] [false] items).run {}
  unless ts.length == 1 do throw "the top level has size one"
  return { adts := st.decls, groups := st.groups, main := close ss ts }

def load (src : String) : Except String Prog := do elabProgram (← parse src)

end Minimal
