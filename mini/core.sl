; mini/core.sl -- what the minimal language's programs elaborate to and evaluate to: core code with every
; binder an entry id, runtime values, and environments. Types are data (DESIGN.md section 17), so a type
; former in value position is a [CFormer] and evaluates to itself closed by the environment; a level or a
; proof is a [CToken], unit at runtime (MINIMAL.md). One session's proposal.

(def-adts
  ((Core : -> Type)
    enum
    (many CVar : (many (Nat) id) -> (Core))
    (many CApp : (many (Core) head) (many (List (Core)) args) -> (Core))
    (many CCall : (many (Core) fn) (many (List (Core)) args) -> (Core))
    (many CMatch : (many (Core) scrut) (many (List (Branch)) branches) -> (Core))
    (many CValues : (many (List (Core)) items) -> (Core))
    (many CFormer : (many (Term) t) -> (Core))
    (many CToken : -> (Core))
    (many CStmt : (many (Stmt) s) (many (Core) rest) -> (Core)))
  ((Branch : -> Type)
    enum
    (many MkBranch : (many (Nat) ctor) (many (List (Nat)) fields) (many (Core) body) -> (Branch)))
  ((Stmt : -> Type)
    enum
    (many SLet : (many (List (Nat)) ids) (many (Core) rhs) -> (Stmt))
    (many SDefLvl : (many (Nat) id) -> (Stmt))
    (many SDefFns : (many (List (FnDef)) defs) -> (Stmt))
    (many SDefAdts : (many (List (Nat)) ids) -> (Stmt)))
  ((FnDef : -> Type)
    enum
    (many MkFnDef : (many (Nat) id) (many (List (Nat)) params) (many (Core) body) -> (FnDef))))

; A value: a constructor or type constructor applied, one unapplied, a type former closed by an environment,
; a closure over a def-fns group, or the token every level and proof is.
(def-adts
  ((Val : -> Type)
    enum
    (many VCon : (many (Nat) head) (many (List (Val)) args) -> (Val))
    (many VAtom : (many (Nat) id) -> (Val))
    (many VFormer : (many (Term) t) (many (Env) env) -> (Val))
    (many VClo : (many (Env) env) (many (List (FnDef)) group) (many (FnDef) def) -> (Val))
    (many VToken : -> (Val)))
  ((Env : -> Type)
    enum
    (many ENil : -> (Env))
    (many ECons : (many (Nat) id) (many (Val) v) (many (Env) rest) -> (Env))))

(def-adts
  ((EnvOf : ((Env) env) ((Nat) x) ((Val) v) -> Type)
    enum
    (many EnvHere : (erased (Nat) x) (erased (Val) v) (erased (Env) rest) -> (EnvOf (ECons x v rest) x v))
    (many EnvThere : (erased (Nat) x) (erased (Nat) y) (erased (Val) v) (erased (Val) w) (erased (Env) rest) (erased (Neq x y) n) (erased (EnvOf rest x v) p)
       -> (EnvOf (ECons y w rest) x v)))
  ((EnvDec : ((Env) env) ((Nat) x) -> Type)
    enum
    (many EnvHit : (erased (Env) env) (erased (Nat) x) (many (Val) v) (erased (EnvOf env x v) p) -> (EnvDec env x))
    (many EnvMiss : (erased (Env) env) (erased (Nat) x) -> (EnvDec env x))))

(def-fns _ $ (many env-dec : (subterm many (Env) env) (many (Nat) x) -> (many (EnvDec env x) r))
  (let-match many env (ECons y w rest) ((ENil) (EnvMiss _ _)))
  (let-match many (nat-dec x y) (NDDiff z u n) ((NDSame z) (EnvHit _ _ w $ EnvHere x w rest)))
  (match many (notail $ env-dec rest x) _
    ((EnvHit e z2 v p) (EnvHit _ _ v $ EnvThere x y v w rest n p))
    ((EnvMiss e z2) (EnvMiss _ _))))

; Binding a list of ids to as many values, the first id outermost.
(def-adts
  ((BindAll : ((Env) env) ((List (Nat)) ids) ((List (Val)) vs) ((Env) out) -> Type)
    enum
    (many BANil : (erased (Env) env) -> (BindAll env (Nil (Nat)) (Nil (Val)) env))
    (many BACons : (erased (Env) env) (erased (Nat) x) (erased (Val) v) (erased (List (Nat)) ids) (erased (List (Val)) vs) (erased (Env) out)
       (erased (BindAll (ECons x v env) ids vs out) p) -> (BindAll env (Cons (Nat) x ids) (Cons (Val) v vs) out)))
  ((BindDec : ((Env) env) ((List (Nat)) ids) ((List (Val)) vs) -> Type)
    enum
    (many BDOk : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) (many (Env) out) (erased (BindAll env ids vs out) p) -> (BindDec env ids vs))
    (many BDStuck : (erased (Env) env) (erased (List (Nat)) ids) (erased (List (Val)) vs) -> (BindDec env ids vs))))

(def-fns _ $ (many bind-all : (many (Env) env) (subterm many (List (Nat)) ids) (many (List (Val)) vs) -> (many (BindDec env ids vs) r))
  (let-match many ids (Cons a x rest)
    ((Nil a) (match many vs _ ((Nil b) (BDOk _ _ _ env $ BANil env)) ((Cons b v rest) (BDStuck _ _ _)))))
  (let-match many vs (Cons b v vrest) ((Nil b) (BDStuck _ _ _)))
  (match many (notail $ bind-all (ECons x v env) rest vrest) _
    ((BDStuck c d e) (BDStuck _ _ _))
    ((BDOk c d e out p) (BDOk _ _ _ out $ BACons env x v rest vrest out p))))

; Binding a def-fns group: each function becomes a closure over the environment the group was defined in,
; [cenv], and applying one rebinds the whole group, which is how the group recurses.
(def-adts
  ((BindGroup : ((Env) cenv) ((List (FnDef)) group) ((List (FnDef)) defs) ((Env) env) ((Env) out) -> Type)
    enum
    (many BGNil : (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Env) env) -> (BindGroup cenv group (Nil (FnDef)) env env))
    (many BGCons : (erased (Env) cenv) (erased (List (FnDef)) group) (erased (Nat) id) (erased (List (Nat)) ps) (erased (Core) body) (erased (List (FnDef)) defs) (erased (Env) env) (erased (Env) out)
       (erased (BindGroup cenv group defs (ECons id (VClo cenv group (MkFnDef id ps body)) env) out) p)
       -> (BindGroup cenv group (Cons (FnDef) (MkFnDef id ps body) defs) env out))))

(def-fns _ $ (many bind-group : (many (Env) cenv) (many (List (FnDef)) group) (subterm many (List (FnDef)) defs) (many (Env) env) -> (many (Env) out) (erased (BindGroup cenv group defs env out) p))
  (let-match many defs (Cons a def rest) ((Nil a) (values env (BGNil cenv group env))))
  (match many def _
    ((MkFnDef id ps body)
      (let ((many out) (erased p)) (tail $ bind-group cenv group rest (ECons id (VClo cenv group (MkFnDef id ps body)) env)))
      (values out (BGCons cenv group id ps body rest env out p)))))

(def-adts
  ((BindAtoms : ((Env) env) ((List (Nat)) ids) ((Env) out) -> Type)
    enum
    (many BTNil : (erased (Env) env) -> (BindAtoms env (Nil (Nat)) env))
    (many BTCons : (erased (Env) env) (erased (Nat) x) (erased (List (Nat)) ids) (erased (Env) out) (erased (BindAtoms (ECons x (VAtom x) env) ids out) p)
       -> (BindAtoms env (Cons (Nat) x ids) out))))

(def-fns _ $ (many bind-atoms : (many (Env) env) (subterm many (List (Nat)) ids) -> (many (Env) out) (erased (BindAtoms env ids out) p))
  (let-match many ids (Cons a x rest) ((Nil a) (values env (BTNil env))))
  (let ((many out) (erased p)) (tail $ bind-atoms (ECons x (VAtom x) env) rest))
  (values out (BTCons env x rest out p)))

; The branch a constructor selects.
(def-adts
  ((BranchOf : ((List (Branch)) bs) ((Nat) c) ((List (Nat)) fields) ((Core) body) -> Type)
    enum
    (many BrHere : (erased (Nat) c) (erased (List (Nat)) fields) (erased (Core) body) (erased (List (Branch)) rest) -> (BranchOf (Cons (Branch) (MkBranch c fields body) rest) c fields body))
    (many BrThere : (erased (Nat) c) (erased (Nat) d) (erased (List (Nat)) fields) (erased (List (Nat)) fields2) (erased (Core) body) (erased (Core) body2) (erased (List (Branch)) rest)
       (erased (Neq c d) n) (erased (BranchOf rest c fields body) p) -> (BranchOf (Cons (Branch) (MkBranch d fields2 body2) rest) c fields body)))
  ((BranchDec : ((List (Branch)) bs) ((Nat) c) -> Type)
    enum
    (many BrHit : (erased (List (Branch)) bs) (erased (Nat) c) (many (List (Nat)) fields) (many (Core) body) (erased (BranchOf bs c fields body) p) -> (BranchDec bs c))
    (many BrMiss : (erased (List (Branch)) bs) (erased (Nat) c) -> (BranchDec bs c))))

(def-fns _ $ (many branch-dec : (subterm many (List (Branch)) bs) (many (Nat) c) -> (many (BranchDec bs c) r))
  (let-match many bs (Cons a b rest) ((Nil a) (BrMiss _ _)))
  (match many b _
    ((MkBranch d fields2 body2)
      (let-match many (nat-dec c d) (NDDiff z w n) ((NDSame z) (BrHit _ _ fields2 body2 $ BrHere c fields2 body2 rest)))
      (match many (notail $ branch-dec rest c) _
        ((BrHit l z2 fields body p) (BrHit _ _ fields body $ BrThere c d fields fields2 body body2 rest n p))
        ((BrMiss l z2) (BrMiss _ _))))))

(MkUnit)
