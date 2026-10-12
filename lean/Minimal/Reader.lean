import Minimal.Check

namespace Minimal

inductive Sx where
  | atom (s : String)
  | list (xs : List Sx)
  deriving Repr, Inhabited

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

structure ESt where
  n : Nat := 0
  adts : List (String × Nat) := []
  ctors : List (String × Nat × Nat) := []
  decls : List Adt := []
  groups : List Group := []

abbrev M := StateT ESt (Except String)

def keywords : List String :=
  ["def-adts", "def-lvl", "def-fns", "let", "match", "values", "prove-subterm", "prove-predates",
   "predates-trans", "subterm-trans", "predates-subterm", "predates", "subterm", "is", "Fn", "Type", "Level",
   "Predates", "Subterm"]

abbrev Scope := List (String × Ref)

def look (sc : Scope) (depth : Nat) (x : String) : M Tm := do
  match sc.lookup x with
  | some (.fv i) => pure (.fv i)
  | some (.bnd lv) => pure (.bv (depth - 1 - lv))
  | none => throw s!"unbound name {x}"

mutual
partial def elabTm (sc : Scope) (depth : Nat) : Sx → M Tm
  | .atom "Type" => pure .univ
  | .atom x => look sc depth x
  | .list [.atom "Level"] => pure .level
  | .list [.atom "Predates", A, x, L] =>
    return .predates (← elabTm sc depth A) (← elabTm sc depth x) (← elabTm sc depth L)
  | .list [.atom "Subterm", A, a, B, b] =>
    return .subterm (← elabTm sc depth A) (← elabTm sc depth a) (← elabTm sc depth B) (← elabTm sc depth b)
  | .list [.atom "Fn", l, .list ps, .list rs] => do
    let l ← elabTm sc depth l
    let t ← elabTele sc depth (ps ++ rs)
    return .fn l ps.length t
  | .list (.atom h :: args) => do
    let st ← get
    let args ← args.mapM (elabTm sc depth)
    match st.adts.lookup h, st.ctors.lookup h with
    | some d, _ => pure (.ty d (.ofList args))
    | _, some (d, c) => pure (.con d c (.ofList args))
    | _, _ => throw s!"{h} is not a type or constructor, in a type"
  | _ => throw "malformed term"

partial def elabTele (sc : Scope) (depth : Nat) : List Sx → M Tm
  | [] => pure .nil
  | e :: es => do
    let (m, T, x) ← match e with
      | .list [.atom "subterm", T, .atom x] => pure (true, T, x)
      | .list [T, .atom x] => pure (false, T, x)
      | _ => throw "malformed telescope entry"
    let T ← elabTm sc depth T
    let r ← elabTele ((x, .bnd depth) :: sc) (depth + 1) es
    return .bind m T r
end

def fresh (k : Nat) : M (List Nat) := modifyGet fun st => (List.range' st.n k, { st with n := st.n + k })

inductive Stmt where
  | call (f : Tm) (dec : Dec) (args : Tm) (n : Nat)
  | mtch (s : Tm) (rets : Tm) (brs : List (Nat × Nat × Core))
  | prim (p : Prim)
  | defLvl
  | defFns (gid : Nat)
  | chk (isType : Bool) (a b : Tm)

def Stmt.wrap (rest : Core) : Stmt → Core
  | .call f d a n => .call f d a n rest
  | .mtch s r b => .mtch s r b rest
  | .prim p => .prim p rest
  | .defLvl => .defLvl rest
  | .defFns g => .defFns g rest
  | .chk k a b => .chk k a b rest

def close (ss : List Stmt) (ts : List Tm) : Core := ss.foldr (fun s c => s.wrap c) (.ret (.ofList ts))

def entry (sc : Scope) (x : String) : M Nat := do
  match sc.lookup x with
  | some (.fv i) => pure i
  | _ => throw s!"{x} is not an entry"

mutual
partial def elabExpr (sc : Scope) (want : Nat) : Sx → M (List Stmt × List Tm)
  | .list (.atom "values" :: es) => elabArgs sc es
  | e@(.list (.atom h :: args)) => do
    let st ← get
    if h ∈ ["prove-subterm", "prove-predates", "predates-trans", "subterm-trans", "predates-subterm"] then
      let (ss, ts) ← elabArgs sc args
      let p ← match h, ts, args with
        | "prove-subterm", [a, b], _ => pure (.proveSubterm a b)
        | "prove-predates", _, [.atom x, .atom L] => do
          pure (Prim.provePredates (← entry sc x) (← entry sc L))
        | "predates-trans", [p, q], _ => pure (.predatesTrans p q)
        | "subterm-trans", [p, q], _ => pure (.subtermTrans p q)
        | "predates-subterm", [p, q], _ => pure (.predatesSubterm p q)
        | _, _, _ => throw s!"malformed {h}"
      let [i] ← fresh 1 | throw "fresh"
      return (ss ++ [.prim p], [.fv i])
    else if h == "match" then elabMatch sc want args
    else if h ∈ keywords || (st.adts.lookup h).isSome || (st.ctors.lookup h).isSome then
      match st.adts.lookup h, st.ctors.lookup h with
      | some d, _ => let (ss, ts) ← elabArgs sc args; return (ss, [.ty d (.ofList ts)])
      | _, some (d, c) => let (ss, ts) ← elabArgs sc args; return (ss, [.con d c (.ofList ts)])
      | _, _ => return ([], [← elabTm sc 0 e])
    else do
      let f ← look sc 0 h
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
      let (ss, ts) ← elabArgs sc args
      let outs ← fresh want
      return (ss0 ++ ss ++ [.call f dec (.ofList ts) want], outs.map .fv)
  | e => return ([], [← elabTm sc 0 e])

partial def elabArgs (sc : Scope) (es : List Sx) : M (List Stmt × List Tm) := do
  let rs ← es.mapM (elabExpr sc 1)
  return (rs.flatMap (·.1), rs.flatMap (·.2))

partial def elabMatch (sc : Scope) (_want : Nat) : List Sx → M (List Stmt × List Tm)
  | s :: .list rets :: brs => do
    let (ss, sts) ← elabExpr sc 1 s
    let [s] := sts | throw "match: one scrutinee"
    let R ← elabTele sc 0 rets
    let st ← get
    let base := st.n
    let mut out : List (Nat × Nat × Core) := []
    for br in brs do
      let .list (.list (.atom c :: xs) :: items) := br | throw "malformed branch"
      let some (d', ci) := st.ctors.lookup c | throw s!"unknown constructor {c}"
      let names ← xs.mapM fun | .atom x => pure x | _ => throw "malformed pattern"
      modify fun st => { st with n := base }
      let fs ← fresh names.length
      let body ← elabBody ((names.zip (fs.map Ref.fv)).reverse ++ sc) rets.length items
      out := out ++ [(d', ci, body)]
    modify fun st => { st with n := base }
    let outs ← fresh rets.length
    return (ss ++ [.mtch s R out], outs.map .fv)
  | _ => throw "malformed match"

partial def elabSeq (sc : Scope) (want : Nat) : List Sx → M (List Stmt × List Tm)
  | [] => throw "empty body"
  | [e] => elabExpr sc want e
  | .list [.atom "def-lvl", .atom L] :: rest => do
    let [i] ← fresh 1 | throw "fresh"
    let (ss, ts) ← elabSeq ((L, .fv i) :: sc) want rest
    return (.defLvl :: ss, ts)
  | .list (.atom "let" :: .list xs :: items) :: rest => do
    let bs ← xs.mapM fun
      | .atom x => pure (x, none)
      | .list [e, .atom "is", .atom x] => pure (x, some (false, e))
      | .list [T, .atom x] => pure (x, some (true, T))
      | _ => throw "malformed let binder"
    let (ss, ts) ← elabSeq sc bs.length items
    if ts.length != bs.length then throw "let: wrong number of binders"
    let mut ss := ss
    let mut sc' := sc
    for ((x, ann), t) in bs.zip ts do
      let i ← match t with
        | .fv i => pure i
        | _ => do
          let [j] ← fresh 1 | throw "fresh"
          ss := ss ++ [.prim (.tm t)]
          pure j
      if let some (k, a) := ann then ss := ss ++ [.chk k (.fv i) (← elabTm sc' 0 a)]
      sc' := (x, .fv i) :: sc'
    let (ss2, ts2) ← elabSeq sc' want rest
    return (ss ++ ss2, ts2)
  | .list (.atom "def-fns" :: .atom L :: fns) :: rest => do
    let lvl ← entry sc L
    let sigs ← fns.mapM fun
      | .list (.atom f :: .list ps :: .list rs :: items) => pure (f, ps, rs, items)
      | _ => throw "malformed def-fns"
    let base := (← get).n
    let fnsc := (sigs.zipIdx.map fun ((f, _), j) => (f, Ref.fv (base + j))).reverse ++ sc
    let defs ← sigs.mapM fun (_, ps, rs, items) => do
      let tele ← elabTele sc 0 (ps ++ rs)
      modify fun st => { st with n := base + sigs.length }
      let pids ← fresh ps.length
      let pnames ← ps.mapM fun | .list [.atom "subterm", _, .atom x] | .list [_, .atom x] => pure x
                                | _ => throw "malformed parameter"
      let body ← elabBody ((pnames.zip (pids.map Ref.fv)).reverse ++ fnsc) rs.length items
      pure { np := ps.length, tele, body : FnDef }
    let gid := (← get).groups.length
    modify fun st => { st with n := base + sigs.length, groups := st.groups ++ [{ lvl, fns := defs }] }
    let (ss, ts) ← elabSeq fnsc want rest
    return (.defFns gid :: ss, ts)
  | e :: rest => do
    let (ss, _) ← elabExpr sc 0 e
    let (ss2, ts) ← elabSeq sc want rest
    return (ss ++ ss2, ts)

partial def elabBody (sc : Scope) (want : Nat) (items : List Sx) : M Core := do
  let (ss, ts) ← elabSeq sc want items
  return close ss ts
end

def declareAdts (blocks : List Sx) : M Unit := do
  let heads ← blocks.mapM fun (b : Sx) => match b with
    | .list (.atom T :: .list ps :: cs) => pure (T, ps, cs)
    | _ => throw "malformed def-adts"
  let st ← get
  let base := st.decls.length
  let mut ctors := st.ctors
  for ((_, _, cs), j) in heads.zipIdx do
    for (c, ci) in cs.zipIdx do
      let .list (.atom C :: _) := c | throw "malformed constructor"
      ctors := (C, base + j, ci) :: ctors
  set { st with adts := (heads.zipIdx.map fun ((h : String × List Sx × List Sx), j) => (h.1, base + j)).reverse ++ st.adts, ctors }
  for (T, ps, cs) in heads do
    let params ← elabTele [] 0 ps
    let sigs ← cs.mapM fun (c : Sx) => match c with
      | .list [_, .list fs, ret] => elabTele [] 0 (fs ++ [.list [ret, .atom "_"]])
      | _ => throw "malformed constructor"
    let ctorNames := cs.filterMap fun | .list (.atom C :: _) => some C | _ => none
    modify fun st => { st with decls := st.decls ++ [{ params, ctors := sigs, name := T, ctorNames }] }

def elabProgram (items : List Sx) : Except String Prog := do
  let adts := items.filterMap fun | .list (.atom "def-adts" :: bs) => some bs | _ => none
  let rest := items.filter fun | .list (.atom "def-adts" :: _) => false | _ => true
  let (main, st) ← (do adts.forM declareAdts; elabBody [] 1 rest).run {}
  return { adts := st.decls, groups := st.groups, main }

def load (src : String) : Except String Prog := do elabProgram (← parse src)

end Minimal
