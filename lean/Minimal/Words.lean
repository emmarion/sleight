import Minimal.Typing

namespace Minimal

structure Ident where
  new : Nat → Tm → Nat
  fn : Tm → Nat

def Ident.fresh : Ident := ⟨fun n _ => n, fun _ => 0⟩

namespace Tm

def unwd : Tm → Tm
  | wd _ v => v
  | t => t

def slotV (w : Word) : Tm := wd w vacant

def natVal : Tm → Nat
  | app _ (cons (wd _ p) _) | app _ (cons p _) => p.natVal + 1
  | _ => 0

def slotWord (ρ : List Tm) : Tm → Word
  | sfv i => (env ρ i).word
  | wd w _ => w
  | _ => .imm 0

end Tm

def Prog.tagged (P : Prog) (d : Nat) : Bool := match P.adts[d]? with
  | some D => !D.union && ((List.range D.ctors.length).filter (!P.phantom d ·)).length > 1
  | none => false

def Prog.tag (P : Prog) (d c : Nat) : Nat := ((List.range c).filter (!P.phantom d ·)).length

def Prog.ctorWord (P : Prog) (ι : Ident) (cnt d c : Nat) (v : Tm) (fs : List Tm) : Word × Nat :=
  match P.wrapField d c with
  | some k => ((fs.getD k .nil).word, cnt)
  | none =>
    if P.natD = some d then (.imm v.natVal, cnt)
    else if (P.ctorErs d c).all id then (.imm (if P.tagged d then P.tag d c else 0), cnt)
    else (.blk (ι.new cnt v), cnt + 1)

def Tm.envT (ρ : List Tm) (t : Tm) : Tm := t.subst2 (env ρ) fun i => slotW (env ρ i).word

mutual
def Prog.evT (P : Prog) (ι : Ident) (ρ : List Tm) : Tm → Nat → Tm × Nat
  | .fv i, cnt => (Tm.env ρ i, cnt)
  | .sfv i, cnt => (Tm.slotV (Tm.env ρ i).word, cnt)
  | .app h args, cnt =>
    match (h.envT ρ).unwd with
    | .vc d c ls =>
      let (fs, cnt) := P.evTs ι ρ args cnt
      let v := Tm.app (.vc d c ls) fs
      let (w, cnt) := P.ctorWord ι cnt d c v fs.toList
      (.wd w v, cnt)
    | h' => (.wd (.imm 0) (.app h' (args.envT ρ)), cnt)
  | t, cnt => (.wd (.imm 0) (t.envT ρ), cnt)

def Prog.evTs (P : Prog) (ι : Ident) (ρ : List Tm) : Tm → Nat → Tm × Nat
  | .cons a as, cnt =>
    let (v, cnt) := P.evT ι ρ a cnt
    let (vs, cnt) := P.evTs ι ρ as cnt
    (.cons v vs, cnt)
  | t, cnt => (t.envT ρ, cnt)
end

def Prog.evList (P : Prog) (ι : Ident) (ρ : List Tm) : List Tm → Nat → List Tm × Nat
  | [], cnt => ([], cnt)
  | t :: ts, cnt =>
    let (v, cnt) := P.evT ι ρ t cnt
    let (vs, cnt) := P.evList ι ρ ts cnt
    (v :: vs, cnt)

def Prim.term : Prim → Option Tm
  | .tm t | .lit t | .place t _ | .unplace t _ | .assert t _ | .coerce _ t _ => some t
  | .placedSlot d q a _ => some (.app (.vc q 0 .nil) (.cons (.app (.tyc d .nil) .nil) (.cons a .nil)))
  | .placedEq q A a _ => some (.app (.vc q 0 .nil) (.cons A (.cons a .nil)))
  | .num d n => some (natTm' d n)
  | _ => none

def Prog.evP (P : Prog) (ι : Ident) (ρ : List Tm) (pd : Option Tm) (p : Prim) (cnt : Nat) : Tm × Nat :=
  let (v, cnt) := match p.term, p with
    | some t, _ => P.evT ι ρ t cnt
    | none, .wAsk w req => P.evT ι [] (P.answer (P.evT ι ρ w 0).1.unwd (P.evT ι ρ req 0).1.unwd).2 cnt
    | none, .wNext w => let w' := (P.evT ι ρ w 0).1; (.wd w'.word w'.unwd.wnext, cnt)
    | none, _ => (.wd (.imm 0) .tok, cnt)
  match p.srcAt P pd with
  | some s => (.wd (s.slotWord ρ) v.unwd, cnt)
  | none => (v, cnt)

def closuresW (ι : Ident) (env : List Tm) (gid : Nat) (G : Group) : List Tm :=
  G.fns.zipIdx.foldl (fun acc (F, j) =>
    let c := Tm.clo (.ofList env) gid j
    acc ++ [.wd (match F.dele with
      | some t => ((env ++ acc).getD t .nil).word
      | none => .blk (ι.fn c)) c]) []

def calleeW (P : Prog) (ι : Ident) (f : Tm) : Option (List Tm × Nat × Nat × Group × FnDef) := do
  let .clo env gid j := f.unwd | none
  let G ← P.groups[gid]?
  let F ← G.fns[j]?
  match (env.toList[G.lvl]?).map Tm.unwd with
  | some (.lvl n) => some (env.toList, n, gid, G, F)
  | _ => none

def pend (ρ : List Tm) (pd : Option Tm) (cnt : Nat) (ι : Ident) : Chk → Tm → Option Tm × Nat
  | .mark (.reuse true), .fv i | .mark (.write true), .fv i => (some (.sfv i), cnt)
  | .mark .cellOf, a | .slotAt, a => (a.varSlot, cnt)
  | .mark .alloc, _ => (some (Tm.slotV (.blk (ι.new cnt .tok))), cnt + 1)
  | _, _ => (pd, cnt)

def evalW (P : Prog) (ι : Ident) (μ : Option (List Nat)) (ρ : List Tm) (pd : Option Tm) (cnt : Nat) :
    Core → Except String (List Tm × Nat)
  | .ret ts => .ok (P.evList ι ρ ts.toList cnt)
  | .call f _ args _ _ _ rest =>
    let (fv, cnt) := P.evT ι ρ f cnt
    match calleeW P ι fv with
    | some (env, n, gid, G, F) =>
      let (argv, cnt) := P.evList ι ρ args.toList cnt
      let μ' := some (n :: (markedArgs F.tele (.ofList argv)).map Tm.size)
      if h : muLt P.k μ' μ then
        match evalW P ι μ' (env ++ closuresW ι env gid G ++ argv) none cnt F.body with
        | .ok (outs, cnt) => evalW P ι μ (ρ ++ outs) none cnt rest
        | .error e => .error e
      else .error "call does not decrease"
    | none => .error "callee is not a function"
  | .mtch s _ brs els _ rest =>
    let (sv, cnt) := P.evT ι ρ s cnt
    match sv.unwd with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) =>
        match evalW P ι μ (ρ ++ pre) none cnt body with
        | .ok (outs, cnt) => evalW P ι μ (ρ ++ outs) none cnt rest
        | .error e => .error e
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .prim p _ rest => let (v, cnt) := P.evP ι ρ pd p cnt; evalW P ι μ (ρ ++ [v]) none cnt rest
  | .wdo w req rest =>
    let (a, cnt) := P.evP ι ρ none (.wNext w) cnt
    let (b, cnt) := P.evP ι ρ none (.wAsk w req) cnt
    evalW P ι μ (ρ ++ [a, b]) none cnt rest
  | .defLvl rest => evalW P ι μ (ρ ++ [.wd (.imm 0) (.lvl cnt)]) none (cnt + 1) rest
  | .defFns gid rest =>
    match P.groups[gid]? with
    | some G => evalW P ι μ (ρ ++ closuresW ι ρ gid G) none cnt rest
    | none => .error "no group"
  | .chk k a _ rest => let (pd, cnt) := pend ρ pd cnt ι k a; evalW P ι μ ρ pd cnt rest
  | .absurd body => match evalW P ι μ ρ pd cnt body with
    | .ok _ => .error "an absurd body returned"
    | .error e => .error e
  | .dead => .error "a refuted branch was reached"
  | .case s brs els _ _ =>
    let (sv, cnt) := P.evT ι ρ s cnt
    match sv.unwd with
    | .app (.vc _ c _) vs =>
      match hb : selectBr brs els c vs.toList with
      | some (pre, body) => evalW P ι μ (ρ ++ pre) none cnt body
      | none => .error "no branch"
    | _ => .error "scrutinee is not data"
  | .seq _ body rest =>
    match evalW P ι μ ρ none cnt body with
    | .ok (outs, cnt) => evalW P ι μ (ρ ++ outs) none cnt rest
    | .error e => .error e
termination_by c => ((⟨μ⟩ : Mu P.k), sizeOf c)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ h
    | (apply Prod.Lex.right; simp; try omega)
  all_goals (have := sizeOf_selectBr hb; simp; omega)

def WordsOK (ρ : List Tm) (Γ : Ctx) : Prop :=
  ∀ i < Γ.n, (Tm.env ρ i).word = (Γ.canon (.sfv i)).slotWord ρ

end Minimal
