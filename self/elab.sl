; self/elab.sl -- the elaborator and checker (self/README.md): head dispatch (DESIGN.md section 6), erasure
; by position (section 14), calls with their proofs, matches with refutation and else (sections 21, 24, 33),
; the seven statements with run-position statements run at once (sections 27, 29), literals, and the sugar
; expansions. It mirrors lib/elab.ml with every check ported (ASSUMPTIONS 91); an error is recorded as a
; value and elaboration goes on, so a program may be refused with more than one message.

(def-adts $ (Res : -> Type)
  enum
  (many MkRes : (many (Term) term) (many (Term) ty) (many (Multiplicity) erasure) (many (Maybe $ Term) place) -> (Res)))

(def-fns _ $ (many res-term : (many (Res) r) -> (many (Term) t)) (match many r _ ((MkRes t _ _ _) t)))
(def-fns _ $ (many res-ty : (many (Res) r) -> (many (Term) t)) (match many r _ ((MkRes _ ty _ _) ty)))
(def-fns _ $ (many res-erasure : (many (Res) r) -> (many (Multiplicity) t)) (match many r _ ((MkRes _ _ e _) e)))

(def-fns _ $ (many res-place : (many (Res) r) -> (many (Maybe $ Term) p))
  (match many r _ ((MkRes _ _ _ p) p)))

(def-fns _ $ (many res-with-place : (many (Res) r) (many (Maybe $ Term) p) -> (many (Res) r2))
  (match many r _ ((MkRes t ty m _) (MkRes t ty m p))))

(def-fns _ $ (many res-of : (many (Env) env) (many (Nat) x) -> (many (Res) r))
  (MkRes (TVar x) (type-of env x) (entry-mult-of env x) $ Some _ $ slot-atom x))

(let ((many no-res)) $ MkRes (TErr "no value") (TErr "no value") (Erased) $ None _)
(let ((many erased-one)) $ Cons _ (Erased) $ Nil _)
(let ((many expansion-limit)) 10000)

; One value's code at the shape the position expects, that position read from the shape; a shape of another
; count has its count reported at the expression's end.
(def-fns _ $ (many single : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (erased (Multiplicity) pos) (erased (PosOf expect pos) pf) (many (Code ctx (Cons (Multiplicity) pos (Nil (Multiplicity)))) c) -> (many (Code ctx expect) r))
  (let-match many expect (Cons _ m rest) ((Nil _) (CError _ expect "size")))
  (let-match many rest (Nil _) ((Cons _ _ _) (CError _ expect "size")))
  (match many m _
    ((Many)
      (let-match erased pf (PoMany _))
      c)
    ((Once)
      (let-match erased pf (PoOnce _))
      (recast _ expect many-one (MsManyOnce _ _ $ MsNil) c))
    ((Erased)
      (let-match erased pf (PoOnly))
      c)))

(def-fns _ $ (many first-res : (erased (Multiplicity) m) (erased (List $ Multiplicity) ms) (many (List $ Res) rs) (erased (Lockstep (Multiplicity) (Res) (Cons (Multiplicity) m ms) rs) lock) -> (many (Res) r))
  (let-match erased lock (LsCons _ _ _ _ _ _ _))
  (let-match many rs (Cons _ r _))
  r)

; What a statement leaves in the code after it (lib/elab.ml's wrap functions), and the frame it binds.
(def-adts $ (StmtCode : ((List $ List $ Nat) ctx) ((List $ List $ Nat) ctx2) -> Type)
  enum
  (many SNone : (erased (List $ List $ Nat) ctx) -> (StmtCode ctx ctx))
  (many SLet : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (many (Code ctx ms) rhs) -> (StmtCode ctx (Cons (List (Nat)) ids ctx)))
  (many SLetRec : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) gids) (many (Group gids ctx) g) -> (StmtCode ctx (Cons (List (Nat)) gids ctx)))
  (many SMatch : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (Nat) disc) (many (List $ Nat) ids) -> (StmtCode ctx (Cons (List (Nat)) ids ctx)))
  (many SSeq : (erased (List $ List $ Nat) ctx) (erased (List $ List $ Nat) ctx1) (erased (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx1) first) (many (StmtCode ctx1 ctx2) then) -> (StmtCode ctx ctx2)))

(def-fns _ $ (many consts-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) cs) ->
    (many (List $ Multiplicity) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) ipk) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk))
  (let-match many cs (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _))))
  (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) $ notail $ consts-codes ctx rest)
  (match many p _
    ((MkPair _ _ id v) (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk) (Cons _ (CValue _ v) codes) (PkMany _ ms (CValue _ v) codes cpk)))))

(def-fns _ $ (many wrap-stmt : (erased (List $ List $ Nat) ctx) (erased (List $ List $ Nat) ctx2) (many (List $ Multiplicity) ns) (subterm many (StmtCode ctx ctx2) sc) (many (Code ctx2 ns) rest) -> (many (Code ctx ns) r))
  (match many sc _
    ((SNone _) rest)
    ((SLet _ ms ids pk rhs) (CLet _ ms _ ids pk rhs rest))
    ((SLetRec _ _ g) (CLetRec _ _ _ g rest))
    ((SMatch _ scrut shape disc ids) (CMatch _ ns scrut shape (Cons _ (MkBranch _ _ disc ids rest) $ Nil _) (None _) $ Cons _ disc $ Nil _))
    ((SSeq _ _ _ first then) (tail $ wrap-stmt _ _ ns first $ notail $ wrap-stmt _ _ ns then rest))))

(def-adts $ (Hoisted : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ms) -> Type)
  enum
  ; ctx2 is ctx under the frames of pre, the temporaries hoisted while the code was elaborated (sections 15, 27)
  (many MkHoisted : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre) (many (Code ctx2 ms) code) -> (Hoisted ctx ms)))

(def-fns _ $ (many hoist-none : (many (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (Code ctx ms) code) -> (many (Hoisted ctx ms) r))
  (MkHoisted _ _ ctx (SNone _) code))

(def-fns _ $ (many hoisted-code : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Hoisted ctx ms) h) -> (many (Code ctx ms) r))
  (match many h _ ((MkHoisted _ _ _ pre code) (wrap-stmt _ _ ms pre code))))

(def-fns _ $ (many hoist-after : (erased (List $ List $ Nat) ctx) (erased (List $ List $ Nat) ctx1) (erased (List $ Multiplicity) ms) (many (StmtCode ctx ctx1) sc) (many (Hoisted ctx1 ms) h) -> (many (Hoisted ctx ms) r))
  (match many h _ ((MkHoisted _ _ ctx2 pre code) (MkHoisted _ _ ctx2 (SSeq _ _ _ sc pre) code))))

(def-fns _ $ (many hoist-temp : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) id) (many (Code ctx many-one) code) ->
    (many (Env) env2) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
  (let ((many frame)) $ Cons _ id $ Nil _)
  (let-match many (and (env-run-pos env) $ not $ env-failed env) (BTrue)
    ((BFalse) (values env (Cons _ frame ctx) $ SLet _ many-one frame (PkMany _ (Nil _) id (Nil _) $ PkNil _) code)))
  (let-match many ctx (Nil _) ((Cons _ _ _) (values env (Cons _ frame ctx) $ SLet _ many-one frame (PkMany _ (Nil _) id (Nil _) $ PkNil _) code)))
  (values (env-run-let env many-one code frame) ctx $ SNone _))

; ---- Syn helpers and the special-form head test

(def-fns _ $ (many raw-atom : (many (Syn) r) -> (many (Maybe $ Name) s))
  (match many r _ ((RAtom _ s) (Some _ s)) (else (None $ Name))))

(def-fns _ $ (many made : (many (Env) env) (many (Syn) raw) (many (Nat) x) -> (many (Multiplicity) m))
  (let-match many raw (RAtom _ n) (else (entry-mult-of env x)))
  (match many n _ ((NHandle _ _ m _) m) (else (entry-mult-of env x))))

(def-fns _ $ (many raw-items : (many (Syn) r) -> (many (List $ Syn) items))
  (match many r _ ((RList _ items) items) (else (Nil $ Syn))))

(def-fns _ $ (many raw-handle : (many (Syn) r) -> (many (Bool) b))
  (let-match many r (RAtom _ s) (else (BFalse)))
  (match many s _ ((NHandle _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many raw-name : (many (Syn) r) -> (many (Maybe $ Name) s))
  (match many (raw-handle r) _ ((BTrue) (None _)) ((BFalse) (raw-atom r))))

(def-fns _ $ (many raw-binder : (many (Syn) r) -> (many (Maybe $ Maybe $ Name) b))
  (match many r _ ((RWild _) (Some _ $ None _)) (else (match many (raw-name r) _ ((Some _ s) (Some _ $ Some _ s)) ((None _) (None _))))))

(def-fns _ $ (many raw-is-literal : (many (Syn) r) -> (many (Bool) b))
  (match many r _ ((RNat _ _) (BTrue)) ((RChr _ _) (BTrue)) ((RString _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many atoms-only : (subterm many (List $ Syn) rs) -> (many (Bool) r))
  (let-match many rs (Cons _ r rest)
    ((Nil _) (BTrue)))
  (match many (raw-binder r) _ ((None _) (BFalse)) ((Some _ _) (tail $ atoms-only rest))))

(def-fns _ $ (many first-atom : (subterm many (List $ Syn) rs) -> (many (Maybe $ Syn) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (None _)))
  (match many r _ ((RList _ _) (tail $ first-atom rest)) (else (Some _ r))))

(def-fns _ $ (many is-underscore : (many (Syn) r) -> (many (Bool) b))
  (match many r _ ((RWild _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many term-var : (many (Term) t) -> (many (Nat) x))
  (match many t _ ((TVar x) x) (else (Zero))))

; A special form's head: a Settled, non-erased entry of type (Special) holding one of its variants (section 6).
(def-fns _ $ (many special-of-entry : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Sp) r))
  (let ((erased _) (many blk)) $ env-block env x)
  (let-match many blk (Some _ b2) ((None _) (None _)))
  (let-match many b2 (BTag _ ct _) (else (None $ Sp)))
  (let ((erased _) (many s)) $ entry-state env x)
  (let-match many s (SSettled _ _ m) ((SHypothetical _) (None _)))
  (let-match many (and (mult-is-many $ entry-mult-of env x) $ term-eq (minted-type env m) special-term) (BTrue)
    ((BFalse) (None _)))
  (sp-of-index $ ctor-index ct))

(def-fns _ $ (many special-of-atom : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Sp) r))
  (let-match many (raw-atom raw) (Some _ n) ((None _) (None _)))
  (let-match many (lookup env n) (Some _ x) ((None _) (None _)))
  (let-match many n (NHandle _ _ m _) (else (special-of-entry env x)))
  (match many (mult-is-many m) _ ((BTrue) (special-of-entry env x)) ((BFalse) (None _))))

(def-fns _ $ (many held-key : (many (Env) env) (many (Maybe $ Nat) except) (many (Nat) x) -> (many (Maybe $ String) r))
  (let-match many (special-of-entry env x) (None _) ((Some _ sp) (Some _ $ sp-name sp)))
  (let-match many (match many except (((Bool) _)) ((None _) (BTrue)) ((Some _ e) (not $ nat-eq e x))) (BTrue) ((BFalse) (None _)))
  (match many (equal-env env (TVar x) type-term) _ ((BTrue) (Some _ universe-key)) ((BFalse) (None _))))

(def-fns _ $ (many kw-held : (many (Env) env) (many (Maybe $ Nat) except) (subterm many (List $ Pair (Name) (Nat)) ns) (many (List $ Pair (String) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (String) $ Pair (Nat) (String)) r))
  (let-match many ns (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ n x))
  (let-match many (held-key env except x) (Some _ b) ((None _) (tail $ kw-held env except rest acc)))
  (let ((many (Bool) newer)) $ match many (kw-find acc b) _ ((None _) (BTrue)) ((Some _ q) (match many q _ ((MkPair _ _ y _) (nat-lt y x)))))
  (tail $ kw-held env except rest $ match many newer (((List $ Pair (String) $ Pair (Nat) (String)) _)) ((BTrue) (Cons _ (MkPair _ _ b $ MkPair _ _ x $ spell-name n) acc)) ((BFalse) acc)))

; A built-in no name holds is spelled `_` and its name, marked with the binder that shadows it.
(def-fns _ $ (many kw-fallbacks : (many (Env) env) (subterm many (List $ SpEntry) es) (many (List $ Pair (String) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (String) $ Pair (Nat) (String)) r))
  (let-match many es (Cons _ e rest) ((Nil _) acc))
  (let-match many e (MkSpEntry b _))
  (let ((many (Maybe $ Loc) site)) $ match many (lookup env $ NSrc b) _ ((None _) (None _)) ((Some _ x) (env-entry-at env x)))
  (tail $ kw-fallbacks env rest $ match many (kw-find acc b) (((List $ Pair (String) $ Pair (Nat) (String)) _))
    ((Some _ _) acc)
    ((None _) (Cons _ (MkPair _ _ b $ MkPair _ _ 0 $ rope-str $ rcat4 (RChar #\x01) (RStr "k") (RStr b) $ rcat3 (RChar #\x01) (RStr $ loc-str site) (RChar #\x02)) acc))))

(def-fns _ $ (many kws-except : (many (Env) env) (many (Maybe $ Nat) except) -> (many (List $ Pair (String) $ Pair (Nat) (String)) r))
  (kw-fallbacks env sp-table $ kw-held env except (name-index-entries _ $ scope-names $ env-scope env) $ Nil _))

(def-fns _ $ (many kws-of : (many (Env) env) -> (many (List $ Pair (String) $ Pair (Nat) (String)) r))
  (kws-except env $ None _))

; A message's own template with each keyword that stands for syntax spelled as kws-of spells it: inside
; backticks, or anywhere in [code], a piece of syntax such as a usage hint (lib/env.ml's respell). Only a
; template is respelled, never text a name was interpolated into.
(def-fns _ $ (many spell-tok : (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (Bool) quoted) (many (Rope) tok) -> (many (String) r))
  (let ((many t)) $ rope-str tok)
  (match many (and quoted $ is-some _ $ kw-find kws t) _ ((BTrue) (kw-spell kws t)) ((BFalse) t)))

(def-fns _ $ (many respell-scan : (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (Bool) code) (subterm many (String) s) (many (Bool) quoted) (many (Rope) tok) (many (Rope) out) -> (many (Rope) r))
  (let-match many s (SCons c rest) ((SNil) (rcat out $ RStr $ spell-tok kws quoted tok)))
  (let-match many (or (char-is c 96) $ or (char-is c 32) $ or (char-is c 40) $ or (char-is c 41) $ char-is c 10) (BTrue)
    ((BFalse) (tail $ respell-scan kws code rest quoted (rcat tok $ RChar c) out)))
  (let ((many q2)) $ match many (and (char-is c 96) $ not code) (((Bool) _)) ((BTrue) (not quoted)) ((BFalse) quoted))
  (tail $ respell-scan kws code rest q2 (REmpty) (rcat3 out (RStr $ spell-tok kws quoted tok) $ RChar c)))

(def-fns _ $ (many say : (many (Env) env) (many (String) s) -> (many (String) r))
  (rope-str $ respell-scan (kws-of env) (BFalse) s (BFalse) (REmpty) (REmpty)))

(def-fns _ $ (many say-code : (many (Env) env) (many (String) s) -> (many (String) r))
  (rope-str $ respell-scan (kws-of env) (BTrue) s (BTrue) (REmpty) (REmpty)))

; error-unless and error-when with the message respelled, on the failing branch only.
(def-fns _ $ (many refuse-unless : (many (Env) env) (many (Bool) ok) (many (String) msg) -> (many (Env) r))
  (match many ok _ ((BTrue) env) ((BFalse) (env-error env $ say env msg))))

(def-fns _ $ (many refuse-when : (many (Env) env) (many (Bool) bad) (many (String) msg) -> (many (Env) r))
  (match many bad _ ((BTrue) (env-error env $ say env msg)) ((BFalse) env)))


(def-adts $ (ExprDemand : ((List $ Multiplicity) expect) -> Type)
  enum
  (many Fixed : (erased (List $ Multiplicity) expect) -> (ExprDemand expect))
  (many CallableHead : (many (Multiplicity) pos) -> (ExprDemand many-one))
  (many FinalDemand : -> (ExprDemand many-one)))

(def-adts $ (DemandBridge : ((List $ Multiplicity) outer) ((List $ Multiplicity) inner) -> Type)
  enum
  (many KeepDemand : (erased (List $ Multiplicity) ms) -> (DemandBridge ms ms))
  (many HeadDemand : (many (Multiplicity) mode) -> (DemandBridge many-one (Cons (Multiplicity) mode (Nil (Multiplicity))))))

(def-fns _ $ (many head-demand : (many (Env) env) (many (Term) ty) (many (Multiplicity) pos) -> (many (Multiplicity) m))
  (let-match many (canon-env env ty) (TFn uq _ _ _)
    ((TCell _ _) pos)
    (else (Many)))
  (match many uq _ ((BTrue) (Once)) ((BFalse) (Many))))

(def-fns _ $ (many special-of : (many (Env) env) (subterm many (Syn) raw) -> (many (Maybe $ Sp) r))
  (let-match many raw (RList _ items) (else (special-of-atom env raw)))
  (let-match many items (Cons _ h tail2) ((Nil _) (None _)))
  (let-match many tail2 (Cons _ arg more) ((Nil _) (None _)))
  (let-match many (notail $ special-of env h) (Some _ sp) ((None _) (None _)))
  (match many (and (sp-eq sp $ SpExpr $ ExShare) $ list-is-empty _ more) _
    ((BFalse) (None _))
    ((BTrue) (tail $ special-of env arg))))

(def-fns _ $ (many is-special : (many (Env) env) (many (Syn) raw) (many (Sp) sp) -> (many (Bool) r))
  (match many (special-of env raw) _
    ((None _) (BFalse))
    ((Some _ s) (sp-eq s sp))))

(def-fns _ $ (many is-mark : (many (Env) env) (many (Syn) raw) (many (MarkK) k) -> (many (Bool) r))
  (is-special env raw $ SpMark k))

(def-fns _ $ (many at-hole : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Syn) r))
  (let-match many raw (RList _ items) (else (None _)))
  (let-match many items (Cons _ a more) ((Nil _) (None _)))
  (let-match many more (Cons _ h last) ((Nil _) (None _)))
  (match many (and (is-mark env a $ MkAt) $ and (is-underscore h) $ list-is-empty _ last) _
    ((BFalse) (None _))
    ((BTrue) (Some _ h))))

(def-fns _ $ (many mult-of : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Multiplicity) r))
  (let-match many (special-of env raw) (Some _ s) ((None _) (None _)))
  (let-match many (sp-eq s $ SpMark $ MkErased) (BFalse)
    ((BTrue) (Some _ $ Erased)))
  (let-match many (sp-eq s $ SpMark $ MkMany) (BFalse) ((BTrue) (Some _ $ Many)))
  (match many (sp-eq s $ SpMark $ MkUnique) _ ((BTrue) (Some _ $ Once)) ((BFalse) (None _))))

(def-fns _ $ (many stmt-of : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ StmtK) r))
  (let-match many (raw-items raw) (Cons _ h _) ((Nil _) (None _)))
  (let-match many (special-of env h) (Some _ sp) ((None _) (None _)))
  (match many sp _
    ((SpStmt k) (Some _ k)) (else (None $ StmtK))))

(def-fns _ $ (many is-statement : (many (Env) env) (many (Syn) raw) -> (many (Bool) r))
  (match many (stmt-of env raw) _ ((None _) (BFalse)) ((Some _ _) (BTrue))))

(def-fns _ $ (many share-arg : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Syn) r))
  (let-match many (raw-items raw) (Cons _ h rest) ((Nil _) (None _)))
  (let-match many rest (Cons _ arg more) ((Nil _) (None _)))
  (match many (and (list-is-empty _ more) $ is-special env h $ SpExpr $ ExShare) _
    ((BTrue) (Some _ arg))
    ((BFalse) (None _))))


; The numeral and character literals, each with its canonical form.
(def-fns _ $ (many lit-terms : (many (Env) env) (subterm many (List $ LitEntry) lits) -> (many (List $ Pair (Term) (LitEntry)) r))
  (let-match many lits (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ lit-terms env rest)
  (let-match many l (MkLitEntry x _ _ _ _))
  (let-match many (lit-entry-spelling l) (Some _ s) ((None _) more))
  (match many (is-literal-name s) _
    ((BTrue) (Cons _ (MkPair _ _ (canon-env env $ TVar x) l) more))
    ((BFalse) more)))

; An atom is shown by the best of the entries equal to it that a reader can name where the message is: a
; numeral or string literal, by its spelling, else the newest binding the scope still names, else its id. What
; canonicalization picks to represent a class is an accident of minting order, so it does not decide the name
; (lib/env.ml's show). A candidate is the atom it would name, its entry, and the name.
(def-fns _ $ (many cand-of : (many (Env) env) (many (List $ Nat) atoms) (many (Nat) x) (many (String) n) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let ((many (Maybe $ Nat) canonical)) $ match many (canon-env env $ TVar x) _ ((TVar a) (match many (list-mem-bin atoms a) _ ((BTrue) (Some _ a)) ((BFalse) (None _)))) (else (None _)))
  (let-match many canonical (None _)
    ((Some _ a) (Cons _ (MkPair _ _ a $ MkPair _ _ x n) acc)))
  (match many (list-mem-bin atoms x) _ ((BTrue) (Cons _ (MkPair _ _ x $ MkPair _ _ x n) acc)) ((BFalse) acc)))

(def-fns _ $ (many name-cands : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) (subterm many (List $ Pair (Name) (Nat)) ns) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ns (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ n x))
  (let ((many (Bool) skip)) $ match many except _ ((None _) (BFalse)) ((Some _ e) (nat-eq e x)))
  (tail $ name-cands env atoms except rest $ match many skip (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) acc) ((BFalse) (cand-of env atoms x (spell-name n) acc))))

(def-fns _ $ (many names-lit : (many (String) s) -> (many (Bool) r))
  (or (all-digits s) $ match many s _ ((SCons c _) (char-is c 34)) ((SNil) (BFalse))))

(def-fns _ $ (many lit-cands : (many (Env) env) (many (List $ Nat) atoms) (subterm many (List $ LitEntry) ls) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) acc))
  (let-match many l (MkLitEntry x _ _ _ _))
  (let-match many (lit-entry-spelling l) (Some _ s) ((None _) (tail $ lit-cands env atoms rest acc)))
  (tail $ lit-cands env atoms rest $ match many (names-lit s) (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) (cand-of env atoms x s acc)) ((BFalse) acc)))

(def-fns _ $ (many best-cand : (many (Nat) a) (subterm many (List $ Pair (Nat) $ Pair (Nat) (String)) cs) (many (Maybe $ Pair (Nat) (String)) best) -> (many (Maybe $ Pair (Nat) (String)) r))
  (let-match many cs (Cons _ c rest) ((Nil _) best))
  (let-match many c (MkPair _ _ a2 xn))
  (let-match many xn (MkPair _ _ x _))
  (let ((many (Bool) newer)) $ match many best (((Bool) _)) ((None _) (BTrue)) ((Some _ b) (match many b _ ((MkPair _ _ y _) (nat-lt y x)))))
  (tail $ best-cand a rest $ match many (and (nat-eq a a2) newer) (((Maybe $ Pair (Nat) (String)) _)) ((BTrue) (Some _ xn)) ((BFalse) best)))

(def-fns _ $ (many name-atoms : (many (Env) env) (subterm many (List $ Nat) atoms) (many (List $ Pair (Nat) $ Pair (Nat) (String)) lits) (many (List $ Pair (Nat) $ Pair (Nat) (String)) names) (many (List $ Pair (Nat) $ Pair (Nat) (String)) fetches) -> (many (Env) r))
  (let-match many atoms (Cons _ a rest) ((Nil _) env))
  (let ((many (String) fetched)) $ match many (best-cand a fetches $ None _) (((String) _)) ((Some _ p) (match many p _ ((MkPair _ _ _ fm) fm))) ((None _) (anon-mark env a)))
  (let ((many (String) fallback)) $ match many (best-cand a names $ None _) (((String) _)) ((Some _ p) (match many p _ ((MkPair _ _ _ nm) nm))) ((None _) fetched))
  (let ((many (String) n)) $ match many (best-cand a lits $ None _) (((String) _)) ((Some _ p) (match many p _ ((MkPair _ _ _ sp) sp))) ((None _) fallback))
  (tail $ name-atoms (env-name-entry env a n) rest lits names fetches))

(def-fns _ $ (many all-named : (subterm many (List $ Nat) atoms) (many (List $ Pair (Nat) $ Pair (Nat) (String)) lits) (many (List $ Pair (Nat) $ Pair (Nat) (String)) names) -> (many (Bool) r))
  (let-match many atoms (Cons _ a rest) ((Nil _) (BTrue)))
  (let-match many (or (is-some _ $ best-cand a names $ None _) (is-some _ $ best-cand a lits $ None _)) (BTrue) ((BFalse) (BFalse)))
  (tail $ all-named rest lits names))

(def-fns _ $ (many canon-id : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (match many (canon-env env $ TVar x) _ ((TVar a) (Some _ a)) (else (None _))))

(def-fns _ $ (many fetch-form : (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (String) head) (many (String) arg) -> (many (String) r))
  (str-cat3 "(" (kw-spell kws head) $ str-cat3 " " arg ")"))

; An atom no name reaches may still be what a fetch form yields here, written with a name as its argument
; (lib/env.ml's fetches): each candidate keyed by the canonical atom the form yields.
(def-fns _ $ (many named-cands : (many (Env) env) (many (Maybe $ Nat) except) (subterm many (List $ Pair (Name) (Nat)) ns) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ns (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ n x))
  (let ((many (Bool) skip)) $ match many except _ ((None _) (BFalse)) ((Some _ e) (nat-eq e x)))
  (let-match many skip (BFalse) ((BTrue) (tail $ named-cands env except rest acc)))
  (tail $ named-cands env except rest $ match many (canon-id env x) (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((Some _ a) (Cons _ (MkPair _ _ a $ MkPair _ _ x $ spell-name n) acc))
    ((None _) acc)))

(def-fns _ $ (many level-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (subterm many (List $ Pair (Nat) $ Pair (Nat) (String)) named) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many named (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ _ xn))
  (let-match many xn (MkPair _ _ x n))
  (tail $ level-cands env kws rest $ match many (canon-env env $ type-of env x) (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((TFn _ lv _ _) (match many lv (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((TVar l) (Cons _ (MkPair _ _ l $ MkPair _ _ x $ fetch-form kws "level-of" n) acc)) (else acc)))
    (else acc)))

(def-fns _ $ (many matchable-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Pair (Nat) $ Pair (Nat) (String)) named) (subterm many (List $ Opened) os) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many os (Cons _ o rest) ((Nil _) acc))
  (let ((many m0)) $ opened-x o)
  (let ((many (List $ Pair (Nat) $ Pair (Nat) (String)) acc2))
    (match many (canon-env env $ type-of env m0) _
      ((TMatchable _ _ _ t _)
        (let-match many (canon-env env t) (TVar tv) (else acc))
        (let-match many (best-cand tv named $ None _) (Some _ q) ((None _) acc))
        (let-match many q (MkPair _ _ _ n))
        (let-match many (canon-id env m0) (Some _ m) ((None _) acc))
        (Cons _ (MkPair _ _ m $ MkPair _ _ m0 $ fetch-form kws "matchable-of" n) acc))
      (else acc)))
  (tail $ matchable-cands env kws named rest acc2))

; The function an anonymous proof of the constructor [ctor] (`Delegate` or `AtFn`) is about: its argument
; [index] of [arity], when a variable.
(def-fns _ $ (many proof-target : (many (Env) env) (many (Nat) y) (many (Nat) ctor) (many (Nat) arity) (many (Nat) index) -> (many (Maybe $ Nat) g))
  (let-match many (env-entry-name env y) (None _) ((Some _ _) (None _)))
  (let-match many (type-of env y) (TApp h args) (else (None _)))
  (let-match many (and (term-eq h $ TVar ctor) $ nat-eq (list-length _ args) arity) (BTrue) ((BFalse) (None _)))
  (let-match many (list-nth _ args index) (NthHit _ _ _ t _) ((NthMiss _ _ _ _) (None _)))
  (match many t _ ((TVar g) (Some _ g)) (else (None _))))

; `(delegate-of n)` and `(at-fn-of n)` for each anonymous proof about a named function, the proof's kind
; told by its constructor [ctor] and the function read at [index] of its [arity] arguments.
(def-fns _ $ (many proof-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Pair (Nat) $ Pair (Nat) (String)) named) (many (Nat) ctor) (many (Nat) arity) (many (Nat) index) (many (String) form) (subterm many (List $ Nat) ys) (many (List $ Nat) seen) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ys (Cons _ y rest) ((Nil _) acc))
  (let-match many (proof-target env y ctor arity index) (Some _ g) ((None _) (tail $ proof-cands env kws named ctor arity index form rest seen acc)))
  (let-match many (list-mem-bin seen g) (BFalse) ((BTrue) (tail $ proof-cands env kws named ctor arity index form rest seen acc)))
  (tail $ proof-cands env kws named ctor arity index form rest (Cons _ g seen) $ match many (best-cand g named $ None _) (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((Some _ q) (match many q _ ((MkPair _ _ _ n) (Cons _ (MkPair _ _ y $ MkPair _ _ y $ fetch-form kws form n) acc))))
    ((None _) acc)))

; `(slot-of n)` for a named entry whose slot canonicalizes to an atom; the newest entry of that slot wins,
; as the reference's `fetches` has it.
(def-fns _ $ (many slot-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (Maybe $ Nat) except) (subterm many (List $ Pair (Name) (Nat)) ns) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ns (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ n x))
  (let ((many (Bool) skip)) $ match many except (((Bool) _)) ((None _) (BFalse)) ((Some _ e) (nat-eq e x)))
  (let-match many skip (BFalse) ((BTrue) (tail $ slot-cands env kws except rest acc)))
  (tail $ slot-cands env kws except rest $ match many (canon-env env $ slot-atom x) (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((TVar a) (Cons _ (MkPair _ _ a $ MkPair _ _ x $ fetch-form kws "slot-of" $ spell-name n) acc))
    (else acc)))

(def-fns _ $ (many numeral-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (subterm many (List $ LitEntry) ls) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) acc))
  (let-match many l (MkLitEntry _ proof _ _ _))
  (let-match many (lit-entry-spelling l) (Some _ sp) ((None _) (tail $ numeral-cands env kws rest acc)))
  (tail $ numeral-cands env kws rest $ match many proof (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((Some _ p) (match many (canon-id env p) (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((Some _ a) (Cons _ (MkPair _ _ a $ MkPair _ _ p $ fetch-form kws "numeral-of" sp) acc)) ((None _) acc)))
    ((None _) acc)))

(def-fns _ $ (many fetch-cands : (many (Env) env) (many (Maybe $ Nat) except) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let ((many kws)) $ kws-of env)
  (let ((many named)) $ named-cands env except (name-index-entries _ $ scope-names $ env-scope env) $ Nil _)
  (level-cands env kws named $ slot-cands env kws except (name-index-entries _ $ scope-names $ env-scope env) $ matchable-cands env kws named (env-opens env) $ proof-cands env kws named delegate-id 6 2 "delegate-of" (env-objects env) (Nil _) $ proof-cands env kws named atfn-id 2 1 "at-fn-of" (env-objects env) (Nil _) $ numeral-cands env kws (env-lits env) $ Nil _))

(def-fns _ $ (many plain-atoms : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) (Nil _)))
  (match many (is-meta env x) _ ((BTrue) (tail $ plain-atoms env rest)) ((BFalse) (Cons _ x $ notail $ plain-atoms env rest))))

(def-fns _ $ (many naming : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) -> (many (Env) r))
  (let-match many atoms (Cons _ _ _) ((Nil _) env))
  (let ((many lits)) $ lit-cands env atoms (env-lits env) $ Nil _)
  (let ((many names)) $ name-cands env atoms except (name-index-entries _ $ scope-names $ env-scope env) $ Nil _)
  (name-atoms env atoms lits names $ match many (all-named atoms lits names) _ ((BTrue) (Nil _)) ((BFalse) (fetch-cands env except))))

(def-fns _ $ (many lit-name : (many (Env) env) (many (Nat) x) -> (many (Maybe $ String) r))
  (let-match many (lit-spelling (env-lits env) x) (Some _ s) ((None _) (None _)))
  (match many (names-lit s) _ ((BTrue) (Some _ s)) ((BFalse) (None _))))

; An entry by its own name, else by the numeral or string literal it is, else by a fetch form yielding it, else as
; an anonymous marker (Env.name_of).
(def-fns _ $ (many shown-name : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let-match many (env-entry-name env x) (None _) ((Some _ n) (name-text n)))
  (let-match many (lit-name env x) (None _) ((Some _ s) s))
  (let-match many (is-meta env x) (BFalse) ((BTrue) (anon-mark env x)))
  (let-match many (best-cand x (fetch-cands env $ None _) $ None _) (Some _ p)
    ((None _) (anon-mark env x)))
  (match many p _ ((MkPair _ _ _ fm) fm)))

(def-fns _ $ (many qshown : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (tick $ shown-name env x))

(def-fns _ $ (many spell : (many (Env) env) (many (String) b) -> (many (String) r))
  (kw-spell (kws-of env) b))

; A keyword deferred until a message is built on failure: [form], shown with every special form's use, is
; built whether or not anything is refused (lib/elab.ml's form).
(def-fns _ $ (many kw-mark : (many (String) b) -> (many (String) r))
  (rope-str $ rcat3 (RChar #\x05) (RStr b) (RChar #\x05)))

(def-fns _ $ (many spell-marks-scan : (many (Env) env) (subterm many (String) s) (many (Bool) inmark) (many (Rope) mark) (many (Rope) out) -> (many (Rope) r))
  (let-match many s (SCons c rest) ((SNil) out))
  (match many (char-is c 5) _
    ((BTrue) (match many inmark _
      ((BTrue) (tail $ spell-marks-scan env rest (BFalse) (REmpty) (rcat out $ RStr $ spell env $ rope-str mark)))
      ((BFalse) (tail $ spell-marks-scan env rest (BTrue) (REmpty) out))))
    ((BFalse) (match many inmark _
      ((BTrue) (tail $ spell-marks-scan env rest inmark (rcat mark $ RChar c) out))
      ((BFalse) (tail $ spell-marks-scan env rest inmark mark (rcat out $ RChar c)))))))

(def-fns _ $ (many spell-marks : (many (Env) env) (many (String) s) -> (many (String) r))
  (rope-str $ spell-marks-scan env s (BFalse) (REmpty) (REmpty)))

(def-fns _ $ (many declared : (many (Env) env) (many (String) how) (many (Nat) x) -> (many (List $ Pair (Loc) $ String) r))
  (match many (env-entry-at env x) _
    ((None _) (Nil _))
    ((Some _ l) (Cons _ (MkPair _ _ l $ str-cat3 (qshown env x) " is declared" $ str-cat how " here") $ Nil _))))

; A use of an entry at a position's multiplicity (section 14, DESIGN.md section 15), its message built only when the
; use is refused.
(def-fns _ $ (many show-t-except : (many (Env) env) (many (Term) t) (many (Maybe $ Nat) except) -> (many (String) s))
  (let ((many c)) $ canon-env env t)
  (rope-str $ show-term c (naming env (plain-atoms env $ term-vars c $ Nil _) except) (kws-except env except) $ Nil _))

(def-fns _ $ (many show-t : (many (Env) env) (many (Term) t) -> (many (String) s))
  (show-t-except env t $ None _))

(def-fns _ $ (many qshow : (many (Env) env) (many (Term) t) -> (many (String) s))
  (tick $ show-t env t))

(def-fns _ $ (many use-entry-as : (many (Env) env0) (many (Multiplicity) pos) (many (Nat) x) (many (Bool) sharing) (many (Maybe $ Name) written) -> (many (Env) r))
  (let ((many live)) $ and (mult-is-many pos) $ not $ env-usage-erased env0)
  (let ((many env)) $ env-refer env0 live x)
  (let-match many live (BTrue) ((BFalse) env))
  (let ((many m)) (entry-mult-of env x))
  (let ((many (Maybe $ Multiplicity) hmade)) $ match many written _ ((Some _ w) (match many w (((Maybe $ Multiplicity) _)) ((NHandle _ _ hm _) (Some _ hm)) (else (None _)))) ((None _) (None _)))
  (let ((many (Bool) lit-many)) $ match many hmade (((Bool) _))
    ((Some _ hm) (match many (mult-eq hm $ Many) (((Bool) _)) ((BTrue) (is-some _ $ lit-spelling (env-lits env) x)) ((BFalse) (BFalse))))
    ((None _) (BFalse)))
  (let ((many (Maybe $ Multiplicity) handle)) $ match many lit-many _ ((BTrue) (None _)) ((BFalse) hmade))
  (let ((many supply)) $ match many (and sharing $ not $ mult-is-once pos) (((Multiplicity) _)) ((BTrue) (Many)) ((BFalse) (match many handle _ ((Some _ hm) hm) ((None _) m))))
  (let ((many env1))
    (match many (misuse pos supply) (((Env) _))
      ((None _) env)
      ((Some _ how)
        (let ((many notes) (many what)) $ match many handle (((List $ Pair (Loc) $ String) _) ((String) _))
          ((Some _ hm) (values (Nil _) $ str-cat3 "a handle to " (qshow env $ TVar x) $ str-cat ", made " $ tick $ spell env $ mult-name hm))
          ((None _) (match many (lit-spelling (env-lits env) x) (((List $ Pair (Loc) $ String) _) ((String) _))
            ((Some _ k) (values (Nil _) $ str-cat3 (tick $ match many written (((String) _)) ((Some _ w) (name-text w)) ((None _) k)) ", a literal and so " $ mult-name m))
            ((None _) (values (declared env "" x) $ str-cat3 (qshown env x) ", declared " $ tick $ spell env $ mult-name m)))))
        (env-error-with env notes $ str-cat3 what ", " $ say env how))))
  (let-match many m (Once) (else env1))
  (let ((many env2)) (match many (match many (mult-is-once pos) (((Bool) _)) ((BTrue) (list-mem-bin (env-captures env) x)) ((BFalse) (BFalse))) (((Env) _)) ((BFalse) env1) ((BTrue) (env-error env1 $ str-cat3 (say env "`def-fns` cannot capture ") (qshown env x) " at unique"))))
  (let ((many (Maybe $ Pair (Loc) $ String) conflict))
    (match many (idmap-get _ x $ uses-map $ env-uses env2) (((Maybe $ Pair (Loc) $ String) _))
      ((Miss _ _ _ _) (None _))
      ((Hit _ _ _ prior _)
        (let-match many prior (UseShared la) ((UseConsumed la) (Some _ $ MkPair _ _ la "already used at unique here")))
        (match many (mult-is-once pos) (((Maybe $ Pair (Loc) $ String) _))
          ((BTrue) (Some _ $ MkPair _ _ la "already shared here"))
          ((BFalse) (None _))))))
  (let ((many env3))
    (match many conflict (((Env) _))
      ((None _) env2)
      ((Some _ p)
        (match many p (((Env) _))
          ((MkPair _ _ la why)
            (env-error-with env2 (Cons _ (MkPair _ _ la why) $ Nil _) $ str-cat3 "unique value " (qshown env x) " has conflicting non-erased uses"))))))
  (env-set-uses env3 $ uses-set (env-uses env3) x $ match many (mult-is-once pos) (((Use) _)) ((BTrue) (UseConsumed $ env-loc env3)) ((BFalse) (UseShared $ env-loc env3))))

(def-fns _ $ (many use-entry : (many (Env) env) (many (Multiplicity) pos) (many (Nat) x) (many (Bool) sharing) -> (many (Env) r))
  (use-entry-as env pos x sharing $ None _))

(def-fns _ $ (many read-special : (many (Env) env) (subterm many (Syn) raw) (many (Bool) sharing) (many (Multiplicity) pos) -> (many (Env) r))
  (let-match many raw (RList _ items)
    ((RAtom _ n) (match many (lookup env n) _ ((None _) env) ((Some _ x) (use-entry-as env (Many) x sharing $ Some _ n))))
    (else env))
  (let-match many items (Cons _ h rest) ((Nil _) env))
  (let-match many rest (Cons _ arg _) ((Nil _) env))
  (let ((many env14)) (match many (mult-is-many pos) (((Env) _))
    ((BTrue) env)
    ((BFalse) (env-error env (say env "`share` in an erased position")))))
  (tail $ read-special (notail $ read-special env14 h (BFalse) pos) arg (BTrue) pos))

(def-fns _ $ (many slot-holder : (many (Env) env) (many (Term) s) (subterm many (List $ Nat) ids) -> (many (Maybe $ Term) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (None _)))
  (match many (equal-env env (slot-atom x) s) _
    ((BTrue) (Some _ $ TSlotOf $ TVar x))
    ((BFalse) (tail $ slot-holder env s rest))))

(def-fns _ $ (many shown-place : (many (Env) env) (many (Maybe $ Term) cplace) -> (many (Maybe $ Term) r))
  (let-match many cplace (Some _ p) ((None _) cplace))
  (let-match many p (TVar _) (else cplace))
  (match many (slot-holder env p $ list-rev _ $ scope-ids $ env-scope env) _
    ((Some _ h) (Some _ h))
    ((None _) cplace)))

; A place is shown as written, `at x`, its variable read through its rule where that is a variable, as the
; reference's namer names an atom; canonicalizing it would show the slot atom instead.
(def-fns _ $ (many shown-places : (many (Env) env) (subterm many (List $ Entry) es) (many (List $ Entry) ces) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) ces))
  (let-match many ces (Cons _ ce crest) ((Nil _) ces))
  (let-match many ce (MkEntry nm s mu sg cplace site))
  (let ((many (Maybe $ Term) place))
    (match many (entry-place e) _
      ((Some _ p)
        (let-match many p (TSlotOf c) (else (shown-place env cplace)))
        (let-match many c (TVar x) (else (shown-place env cplace)))
        (Some _ $ TSlotOf $ match many (canon-env env $ TVar x) (((Term) _)) ((TVar a) (TVar a)) (else c)))
      ((None _) cplace)))
  (Cons _ (MkEntry nm s mu sg place site) $ notail $ shown-places env rest crest))

(def-fns _ $ (many show-tele-t : (many (Env) env) (many (List $ Entry) es) (many (Bool) marked) -> (many (String) s))
  (let ((many ces)) $ shown-places env es $ canon-env-tele env es)
  (let ((many r) (many _)) $ show-tele ces (naming env (plain-atoms env $ term-vars-tele ces $ Nil _) $ None _) (kws-of env) (Nil _) marked)
  (let ((many spaced)) $ rope-str r)
  (let-match many spaced (SCons _ shown) ((SNil) ""))
  shown)

(def-fns _ $ (many count-errs : (subterm many (List $ Entry) tele) -> (many (List $ Term) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (TErr "argument count") $ notail $ count-errs rest))))

(def-fns _ $ (many clash-str : (many (Env) env) (subterm many (Clash) c) -> (many (String) s))
  (match many c _
    ((CText s) s)
    ((CTerm t) (tick $ show-t env t))
    ((CName x) (qshown env x))
    ((CIllTyped x t) (str-cat3 (qshown env x) " would be " $ tick $ show-t env t))
    ((CCat a b) (str-cat (notail $ clash-str env a) $ notail $ clash-str env b))))

(def-fns _ $ (many show-r : (many (Syn) r) -> (many (String) s))
  (rope-str $ show-raw r))

(def-adts $ (Callee : -> Type)
  enum
  (many CalleeHead : (many (Env) env) (many (Syn) head) (many (Term) h) (many (Term) ty) -> (Callee))
  (many CalleeWrap : (many (Env) env) (many (Nat) c) -> (Callee))
  (many CalleeForm : (many (Env) env) (many (String) name) -> (Callee)))

(def-adts $ (Invoke : ((List $ List $ Nat) ctx) -> Type)
  enum
  (many InvApp : (erased (List $ List $ Nat) ctx) (many (Nat) hid) (many (List $ Code ctx many-one) actuals) (many (CC) cc) (many (Bool) skipped) -> (Invoke ctx))
  (many InvWorld : (erased (List $ List $ Nat) ctx) (many (List $ Code ctx many-one) actuals) -> (Invoke ctx))
  (many InvPrim : (erased (List $ List $ Nat) ctx) (many (Sp) prim) (many (List $ Code ctx many-one) actuals) -> (Invoke ctx)))

(def-fns _ $ (many prim-sig-in : (subterm many (List $ PrimSig) ps) (many (Sp) sp) -> (many (Maybe $ PrimSig) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPrimSig q _ _ _))
  (match many (sp-eq q sp) _ ((BTrue) (Some _ p)) ((BFalse) (tail $ prim-sig-in rest sp))))

(def-fns _ $ (many prim-sig : (many (Env) env) (many (Sp) sp) -> (many (Maybe $ PrimSig) r))
  (prim-sig-in (env-prims env) sp))

(let ((many implemented)) $ Cons _ (SpExpr $ ExGensym) $ Cons _ (SpExpr $ ExSettledType) $ Cons _ (SpExpr $ ExSettledErase) $ Cons _ (SpExpr $ ExSettledEq) $ Cons _ (SpExpr $ ExResolve) $ Cons _ (SpExpr $ ExReadFile) $ Cons _ (SpExpr $ ExSettledMult) $ Cons _ (SpExpr $ ExSettledValue) $ Cons _ (SpExpr $ ExInternNat) $ Cons _ (SpExpr $ ExInternChar) $ Cons _ (SpExpr $ ExInternString) $ Cons _ (SpExpr $ ExMintSettled) $ Cons _ (SpExpr $ ExMintSettledErased) $ Cons _ (SpExpr $ ExSlotEq) $ Nil _)
(let ((many primitives)) $ Cons _ (SpExpr $ ExGensymUnique) $ Cons _ (SpExpr $ ExPlaceAt) $ Cons _ (SpExpr $ ExPlaceAtMany) $ Cons _ (SpExpr $ ExUnplaceAt) $ Cons _ (SpExpr $ ExUnplaceAtMany) $ Cons _ (SpExpr $ ExPlacedSlot) $ Cons _ (SpExpr $ ExPlacedEq) implemented)

(def-fns _ $ (many nullary-ctor-code : (erased (List $ List $ Nat) ctx) (many (Nat) c) -> (many (Code ctx many-one) r))
  (CApp _ many-one (CConst _ c) (Nil _) (CCCtor)))

(def-fns _ $ (many prim-named : (subterm many (List $ Sp) ps) (many (String) s) -> (many (Maybe $ Sp) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (None _)))
  (match many (str-eq (sp-name p) s) _ ((BTrue) (Some _ p)) ((BFalse) (tail $ prim-named rest s))))

(def-fns _ $ (many entries-erased : (subterm many (List $ Entry) es) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many e (MkEntry n s _ sg p site))
  (Cons _ (MkEntry n s (Erased) sg p site) $ notail $ entries-erased rest))

(def-fns _ $ (many any-stored : (subterm many (List $ Entry) es) -> (many (Bool) r))
  (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
  (or (entry-stored e) $ notail $ any-stored rest))

(def-fns _ $ (many kind-name : (many (Env) env) (many (Term) ty) -> (many (String) s))
  (let-match many (canon-env env ty) (TFn uq _ _ _)
    ((TValCtor _ _) "value constructor")
    ((TTyCtor _) "type constructor")
    (else "value"))
  (match many uq _ ((BTrue) "unique function") ((BFalse) "function")))

(def-fns _ $ (many declared-as : (many (Env) env) (many (Nat) x) -> (many (List $ Pair (Loc) $ String) r))
  (match many (env-entry-at env x) _
    ((None _) (Nil _))
    ((Some _ l) (Cons _ (MkPair _ _ l $ str-cat3 (kind-name env $ type-of env x) " " $ str-cat (qshown env x) " is declared here") $ Nil _))))

(def-fns _ $ (many term-shown : (many (Env) env) (many (Term) t) -> (many (String) s))
  (match many t _ ((TVar x) (qshown env x)) (else (qshow env t))))

(def-fns _ $ (many term-declared : (many (Env) env) (many (Term) t) -> (many (List $ Pair (Loc) $ String) r))
  (match many t _ ((TVar x) (declared-as env x)) (else (Nil _))))

(def-fns _ $ (many computed-raw : (many (Env) env) (many (Syn) raw) -> (many (Bool) r))
  (let-match many raw (RAtom _ n) (else (BFalse)))
  (let-match many n (NHandle x rd _ _) (else (BFalse)))
  (let-match many rd (MintedIs) (else (BFalse)))
  (let ((erased _) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ nm _ _ _ _ _ _) (not $ is-some _ nm))))

(def-fns _ $ (many describe : (many (Env) env) (many (Syn) head) (many (Term) h) (many (Term) hty) -> (many (Callee) c))
  (CalleeHead env (match many (computed-raw env head) (((Syn) _)) ((BTrue) (RList (raw-pos head) $ Nil _)) ((BFalse) head)) h hty))

(def-fns _ $ (many callee-view : (many (Callee) c) ->
    (many (String) subject) (many (Bool) apposed) (many (List $ Pair (Loc) $ String) notes) (many (Bool) marked) (many (Bool) fields) (many (String) noun))
  (let-match many c (CalleeHead env head h hty)
    ((CalleeWrap env cid) (values (str-cat (say env "`coercible-wrap` of ") $ qshown env cid) (BFalse) (declared-as env cid) (BTrue) (BTrue) "more argument"))
    ((CalleeForm env name) (values (tick $ spell env name) (BFalse) (Nil _) (BTrue) (BFalse) "argument")))
  (let ((many ty)) $ canon-env env hty)
  (let ((many kind)) $ kind-name env ty)
  (let ((many fields)) $ match many ty (((Bool) _)) ((TFn _ _ _ _) (BFalse)) (else (BTrue)))
  (let ((many marked)) $ match many ty (((Bool) _)) ((TTyCtor _) (BFalse)) (else (BTrue)))
  (let ((many named)) $ match many head (((Bool) _)) ((RAtom _ _) (match many h (((Bool) _)) ((TVar _) (BTrue)) (else (BFalse)))) (else (BFalse)))
  (let ((many here)) $ loc-in env $ raw-pos head)
  (match many ty _
    ((TCell cc _)
      (let ((many of)) $ term-shown env cc)
      (match many named _
        ((BTrue) (values (str-cat3 (term-shown env h) (say env ", a `Cell` of ") of) (BTrue) (term-declared env cc) marked fields "argument"))
        ((BFalse) (values (str-cat (say env "the computed `Cell` of ") of) (BFalse) (Cons _ (MkPair _ _ here $ say env "the `Cell` is computed here") $ term-declared env cc) marked fields "argument"))))
    (else (match many named _
      ((BTrue) (values (term-shown env h) (BFalse) (term-declared env h) marked fields "argument"))
      ((BFalse) (values (str-cat "the computed " kind) (BFalse) (Cons _ (MkPair _ _ here $ str-cat3 "the " kind " is computed here") $ Nil _) marked fields "argument"))))))

(def-fns _ $ (many callee-notes : (many (Callee) c) -> (many (List $ Pair (Loc) $ String) r))
  (let ((many _) (many _) (many notes) (many _) (many _) (many _)) $ callee-view c)
  notes)

(def-fns _ $ (many callee-subject : (many (Callee) c) -> (many (String) r))
  (let ((many subject) (many _) (many _) (many _) (many _) (many _)) $ callee-view c)
  subject)

(def-fns _ $ (many counted : (many (Nat) n) (many (String) what) -> (many (String) s))
  (str-cat3 (nat-str n) (str-cat " " what) $ match many (nat-eq n 1) (((String) _)) ((BTrue) "") ((BFalse) "s")))

(def-fns _ $ (many expected-str : (many (String) shown) -> (many (String) s))
  (match many (str-is-empty shown) _ ((BTrue) "") ((BFalse) (str-cat ": expected " $ tick shown))))

(def-fns _ $ (many tele-used : (subterm many (List $ Entry) es) (many (Multiplicity) pos) (many (Bool) fields) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many e (MkEntry n s m sg place site))
  (let ((many m2)) $ match many fields (((Multiplicity) _)) ((BTrue) (field-under pos m)) ((BFalse) (under pos m)))
  (Cons _ (MkEntry n s m2 sg place site) $ notail $ tele-used rest pos fields))

(def-fns _ $ (many tele-with-mults : (subterm many (List $ Entry) es) (many (List $ Multiplicity) ms) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many ms (Cons _ m mrest) ((Nil _) es))
  (let-match many e (MkEntry n s _ sg place site))
  (Cons _ (MkEntry n s m sg place site) $ notail $ tele-with-mults rest mrest))

(def-fns _ $ (many count-mismatch : (many (Env) env) (many (Callee) c) (many (List $ Entry) tele) (many (Multiplicity) pos) (many (Nat) got) -> (many (Env) r))
  (let ((many subject) (many apposed) (many notes) (many marked) (many fields) (many noun)) $ callee-view c)
  (env-error-with env notes $ str-cat3 subject (match many apposed (((String) _)) ((BTrue) ",") ((BFalse) ""))
    $ str-cat3 " expects " (counted (list-length _ tele) noun) $ str-cat3 ", got " (nat-str got) $ expected-str $ show-tele-t env (tele-used tele pos fields) marked))

(def-fns _ $ (many argument-label : (many (Callee) c) (many (Nat) i) (many (Maybe $ Name) name) -> (many (String) s))
  (str-cat3 (str-cat "argument " $ nat-str i) (match many name (((String) _)) ((Some _ n) (str-cat3 ", " (tick-name n) ",")) ((None _) "")) $ str-cat " of " $ callee-subject c))

(def-adts $ (AtCheck : -> Type)
  enum
  (many MkAtCheck : (many (Spot) pos) (many (Nat) i) (many (Maybe $ Name) name) (many (Term) target) (many (Maybe $ Term) place) -> (AtCheck)))

(def-fns _ $ (many report-ats : (subterm many (List $ AtCheck) ats) (many (Callee) c) (many (Env) env) -> (many (Env) r))
  (let-match many ats (Cons _ a rest) ((Nil _) env))
  (let-match many a (MkAtCheck pos i name p place))
  (let ((many ok)) $ match many place (((Bool) _)) ((None _) (BFalse)) ((Some _ q) (equal-env env p q)))
  (let ((many env2)) $ match many ok (((Env) _)) ((BTrue) env) ((BFalse) (env-back env $ env-error-with (env-at env pos) (callee-notes c) $ str-cat3 (argument-label c i name) " does not satisfy `at` " $ qshow env p)))
  (tail $ report-ats rest c env2))

(def-fns _ $ (many meta-ids : (many (Env) env) (subterm many (List $ Nat) xs) (many (List $ Nat) seen) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (match many (and (is-meta env x) $ not $ list-mem-bin seen x) _
    ((BTrue) (Cons _ x $ notail $ meta-ids env rest $ Cons _ x seen))
    ((BFalse) (tail $ meta-ids env rest seen))))

(def-fns _ $ (many term-metas : (many (Env) env) (many (Term) t) -> (many (List $ Nat) r))
  (meta-ids env (term-vars (canon-env env t) $ Nil _) $ Nil _))

(def-fns _ $ (many meta-names : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (qshow env $ TVar x) $ notail $ meta-names env rest))

(def-fns _ $ (many cannot-infer : (many (Env) env) (many (Term) t) -> (many (String) s))
  (str-cat3 "cannot infer " (join-strs (meta-names env $ term-metas env t) " and ") $ str-cat " in " $ qshow env t))

(def-fns _ $ (many hint-at : (many (Env) env) (many (Maybe $ Loc) site) (many (String) x) -> (many (String) r))
  (match many site _
    ((Some _ l) (str-cat "\n" $ located (env-at-loc env l) ": hint: " x))
    ((None _) (str-cat "\nhint: " x))))

(def-fns _ $ (many entry-site : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Loc) r))
  (let ((erased _) (many e)) $ entry env x)
  (match many e _ ((MkEInfo _ _ _ _ _ _ _ site) site)))

(def-fns _ $ (many same-value : (many (Env) env) (many (Nat) x) (subterm many (List $ Pair (Nat) (Name)) found) -> (many (Bool) r))
  (let-match many found (Cons _ f rest) ((Nil _) (BFalse)))
  (let-match many f (MkPair _ _ y _))
  (or (equal-env env (TVar x) (TVar y)) $ notail $ same-value env x rest))

(def-fns _ $ (many typed-entries : (many (Env) env) (many (Term) ty) (subterm many (List $ Nat) xs) (many (List $ Pair (Nat) (Name)) found) -> (many (List $ Pair (Nat) (Name)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) found))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (let-match many n (Some _ name) ((None _) (tail $ typed-entries env ty rest found)))
  (let ((many visible)) $ match many (lookup env name) (((Bool) _)) ((Some _ y) (nat-eq x y)) ((None _) (BFalse)))
  (let-match many (and visible $ and (equal-env env (type-of env x) ty) $ not $ same-value env x found) (BTrue)
    ((BFalse) (tail $ typed-entries env ty rest found)))
  (let ((many more) (erased _)) (list-append _ found $ list1 _ $ MkPair _ _ x name))
  (tail $ typed-entries env ty rest more))

(def-fns _ $ (many candidate-hints : (many (Env) env) (subterm many (List $ Pair (Nat) (Name)) found) -> (many (String) r))
  (let-match many found (Cons _ f rest) ((Nil _) ""))
  (let-match many f (MkPair _ _ y name))
  (let ((many site)) $ entry-site env y)
  (str-cat (hint-at env site $ str-cat (tick-name name) $ match many site (((String) _)) ((Some _ _) ", bound here") ((None _) "")) $ notail $ candidate-hints env rest))

(def-fns _ $ (many hole-hint : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (let ((many ty)) $ canon-env env $ type-of env x)
  (let-match many (or (has-meta-env env ty) $ equal-env env ty type-term) (BFalse) ((BTrue) ""))
  (let ((many found)) $ typed-entries env ty (scope-ids $ env-scope env) $ Nil _)
  (let ((many k)) $ list-length _ found)
  (let-match many (and (nat-lt 0 k) $ nat-lt k 6) (BTrue) ((BFalse) ""))
  (str-cat (hint-at env (entry-site env x) $ str-cat3 (qshow env $ TVar x) " has type " $ str-cat3 (qshow env ty) ", as " $ match many (nat-eq k 1) (((String) _)) ((BTrue) "does:") ((BFalse) "do:"))
    $ candidate-hints env found))

(def-fns _ $ (many hole-hints-of : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) ""))
  (str-cat (hole-hint env x) $ notail $ hole-hints-of env rest))

(def-fns _ $ (many hole-hints : (many (Env) env) (many (Term) t) -> (many (String) r))
  (hole-hints-of env $ term-metas env t))

; A binder whose type or rule still holds an open `_` is refused (lib/env.ml's bind), the term shown as any
; message shows one, after core.sl's checks on the binder's name.
(def-fns _ $ (many refuse-open : (many (Env) before) (many (Env) env) (many (Bool) meta) (many (Bool) holes) (many (Term) ty) (many (Maybe $ Term) rule) -> (many (Env) r))
  (match many (open-in before meta holes ty rule) _
    ((None _) env)
    ((Some _ t) (env-error-hinted env (Nil _) (cannot-infer before t) $ hole-hints before t))))

(def-fns _ $ (many bind-as : (many (Env) env) (many (Bool) meta) (many (Bool) holes) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind-as-raw env meta (BFalse) name site written mult ty rule objid)
  (values (refuse-open env env2 meta holes ty rule) x))

(def-fns _ $ (many bind : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (bind-as env (BFalse) (BFalse) name site written mult ty rule objid))

(def-fns _ $ (many bind-erased : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) (many (Bool) written) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Nat) objid) ->
    (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind-erased-raw env name site written mult ty rule objid)
  (values (refuse-open env env2 (BFalse) (BFalse) ty rule) x))

(def-fns _ $ (many qraw : (many (Syn) r) -> (many (String) s))
  (tick $ show-r r))

(def-fns _ $ (many conformed : (many (Multiplicity) mode) (many (Res) r) -> (many (Res) r2))
  (match many (misuse mode $ res-erasure r) _ ((None _) r) ((Some _ _) (MkRes (res-term r) (res-ty r) mode $ res-place r))))

(def-adts $ (What : -> Type)
  enum
  (many WForm : (many (String) kw) (many (List $ Syn) args) (many (String) rest) -> (What))
  (many WOpened : (many (String) kw) (many (List $ Syn) args) (many (Nat) mid) -> (What))
  (many WCoerce : (many (String) kw) (many (List $ Syn) args) (many (Term) sb) (many (Syn) praw) -> (What))
  (many WReturn : (many (Maybe $ Name) nm) (many (Maybe $ Loc) site) (many (Maybe $ Nat) cid) (many (String) fallback) (many (Multiplicity) mu) -> (What)))

(def-fns _ $ (many what-form : (many (String) kw) (many (List $ Syn) args) -> (many (String) s))
  (tick $ rope-str $ rwrap "(" (rjoin (Cons _ (RStr $ kw-mark kw) $ show-raws args) " ") ")"))

(def-fns _ $ (many what-say : (many (Env) env) (many (What) w) -> (many (List $ Pair (Loc) $ String) notes) (many (String) what))
  (let-match many w (WReturn nm site cid fallback mu)
    ((WForm kw args rest) (values (Nil _) $ str-cat (what-form kw args) rest))
    ((WOpened kw args mid)
      (values (match many (env-entry-at env mid) (((List $ Pair (Loc) $ String) _)) ((None _) (Nil _)) ((Some _ l) (Cons _ (MkPair _ _ l $ say env "the `open-adt` is here") $ Nil _)))
        $ str-cat3 (what-form kw args) ", opened " $ str-cat3 (tick $ kw-mark $ mult-name $ entry-mult-of env mid) " by an " $ tick $ kw-mark "open-adt"))
    ((WCoerce kw args sb praw)
      (values (match many praw (((List $ Pair (Loc) $ String) _)) ((RAtom _ n) (match many (lookup env n) (((List $ Pair (Loc) $ String) _)) ((Some _ y) (declared env "" y)) ((None _) (Nil _)))) (else (Nil _)))
        $ str-cat3 (what-form kw args) ", at " $ str-cat3 (qshow env sb) " by the target side of " $ str-cat (qraw praw) "'s type")))
  (let ((many name)) $ match many nm (((String) _)) ((Some _ n) (str-cat (tick-name n) " ")) ((None _) ""))
  (let ((many callee)) $ match many cid (((String) _)) ((Some _ cx) (qshown env cx)) ((None _) fallback))
  (let ((many notes)) $ match many nm (((List $ Pair (Loc) $ String) _))
    ((None _) (Nil _))
    ((Some _ _) (match many site (((List $ Pair (Loc) $ String) _)) ((None _) (Nil _)) ((Some _ l) (Cons _ (MkPair _ _ l $ str-cat name "is declared here") $ Nil _)))))
  (values notes $ str-cat3 "the return " name $ str-cat3 "of " callee $ str-cat ", declared " $ tick $ mult-name mu))

(def-fns _ $ (many produced : (many (Env) env) (many (What) w) (many (Multiplicity) mode) (many (Res) r) -> (many (Env) env2) (many (Res) r2))
  (let ((many env2)) $ match many (res-term r) (((Env) _))
    ((TErr _) env)
    (else
      (let-match many (env-usage-erased env) (BFalse) ((BTrue) env))
      (let-match many (misuse mode $ res-erasure r) (Some _ how) ((None _) env))
      (let ((many notes) (many what)) $ what-say env w)
      (env-error-with env notes $ str-cat3 (spell-marks env what) ", " $ say env how)))
  (values env2 $ conformed mode r))

(def-fns _ $ (many head-name : (many (Env) env) (many (Res) h) -> (many (String) s))
  (match many (res-term h) _ ((TVar x) (qshown env x)) (else (qshow env $ res-term h))))

(def-fns _ $ (many head-notes : (many (Env) env) (many (Res) h) -> (many (List $ Pair (Loc) $ String) r))
  (match many (res-term h) _ ((TVar x) (declared env (str-cat " " $ tick $ spell env $ mult-name $ entry-mult-of env x) x)) (else (Nil _))))




(def-fns _ $ (many warned-find : (subterm many (List $ Warned) ws) (many (Nat) x) -> (many (Maybe $ Warned) r))
  (let-match many ws (Cons _ w rest) ((Nil _) (None _)))
  (let-match many w (MkWarned y _ _))
  (match many (nat-eq x y) _
    ((BTrue) (Some _ w))
    ((BFalse) (tail $ warned-find rest x))))

(def-fns _ $ (many means-entry : (many (Env) env) (many (String) n) (many (Nat) x) -> (many (Bool) r))
  (let-match many (lookup env $ NSrc n) (Some _ y)
    ((None _) (BFalse)))
  (match many (canon-env env $ TVar y) _ ((TVar z) (nat-eq z x)) (else (BFalse))))

(def-fns _ $ (many suppressing : (many (Env) env) (many (Nat) x) (many (Spot) p) (subterm many (List $ Region) rs) -> (many (List $ Said) hits))
  (let-match many rs (Cons _ r rest) ((Nil _) (Nil _)))
  (let-match many r (MkRegion k n _ _))
  (match many (and (region-covers r p) $ means-entry env n x) _
    ((BTrue) (Cons _ (SaidSilenced k) $ notail $ suppressing env x p rest))
    ((BFalse) (tail $ suppressing env x p rest))))

(def-fns _ $ (many warn-use : (many (Env) env) (many (Loc) l) (many (String) what) (many (Term) t) -> (many (Env) r))
  (let-match many (env-unwarned env) (BFalse) ((BTrue) env))
  (let-match many (canon-env env t) (TVar x) (else env))
  (let-match many (warned-find (env-warned env) x) (Some _ w) ((None _) env))
  (let-match many l (MkLoc cf p))
  (let ((many (Bool) local)) $ match many p _ ((PosSpot q) (match many q _ ((NoPos) (BFalse)) ((MkPos f _ _) (str-eq f cf)))) (else (BTrue)))
  (let ((many hits)) $ suppressing env x p $ match many local _ ((BTrue) (env-regions env)) ((BFalse) (Nil _)))
  (let-match many hits (Nil _) ((Cons _ _ _) (env-set-said env $ list-rev-onto _ hits $ env-said env)))
  (let-match many w (MkWarned _ pl msg))
  (env-back env $ env-warn-with env l (Cons _ (MkPair _ _ pl $ str-cat3 "`;! warn` for " (qshow env t) " is here") $ Nil _) $ str-cat3 what " " $ str-cat3 (qshow env t) ": " msg))

; A message is built only when it is reported: a check takes it as a function at msg-lvl, which may call
; everything above to render terms, and calls it only on failure. A constant message goes through const-msg.
(def-lvl msg-lvl)

(def-fns _ $ (many error-unless-msg : (many (Env) env) (many (Bool) ok) (many (Fn msg-lvl -> (many (String) s)) msg) -> (many (Env) r))
  (match many ok _ ((BTrue) env) ((BFalse) (env-error env $ msg))))

(def-fns _ $ (many error-when-msg : (many (Env) env) (many (Bool) bad) (many (Fn msg-lvl -> (many (String) s)) msg) -> (many (Env) r))
  (error-unless-msg env (not bad) msg))

(def-fns _ $ (many const-msg : (many (String) text) -> (many (Fn msg-lvl -> (many (String) s)) f))
  (def-fns msg-lvl $ (many the-text : -> (many (String) s)) text)
  the-text)

(def-fns _ $ (many error-unless : (many (Env) env) (many (Bool) ok) (many (String) msg) -> (many (Env) r))
  (error-unless-msg env ok $ const-msg msg))

(def-fns _ $ (many error-when : (many (Env) env) (many (Bool) bad) (many (String) msg) -> (many (Env) r))
  (error-unless-msg env (not bad) $ const-msg msg))

(def-fns _ $ (many pos-in : (many (Env) env) (many (List $ Multiplicity) ms) -> (many (Multiplicity) r))
  (let-match many ms (Nil _) ((Cons _ _ _) (pos-mult ms)))
  (match many (env-usage-erased env) _ ((BTrue) (Erased)) ((BFalse) (Many))))

(def-fns _ $ (many run-ids : (many (Env) env) (many (Nat) start) (subterm many (List $ Multiplicity) ms) (many (List $ Res) ress) -> (many (Env) r) (many (List $ Nat) ids))
  (let-match many ms (Cons _ m rest) ((Nil _) (values env $ Nil _)))
  (let ((many (Term) t) (many (List $ Res) more)) $ match many ress (((Term) _) ((List $ Res) _)) ((Cons _ r0 m0) (values (res-term r0) m0)) ((Nil _) (values (TErr "") $ Nil _)))
  (let-match many (mult-is-many m) (BTrue) ((BFalse) (tail $ run-ids env start rest more)))
  (let ((many (Maybe $ Nat) own)) $ match many t _
    ((TVar y) (match many (or (is-settled env y) $ and (nat-lt start y) $ not $ is-meta env y) _ ((BTrue) (Some _ y)) ((BFalse) (None _))))
    (else (None _)))
  (let ((many env2) (many x)) $ match many own (((Env) _) ((Nat) _)) ((Some _ y) (values env y)) ((None _) (env-fresh-id env)))
  (let ((many env3) (many ids)) $ notail $ run-ids env2 start rest more)
  (values env3 $ Cons _ x ids))

(def-fns _ $ (many set-run-states : (erased (Hist Block) hs) (many (Heap hs) h) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) -> (many (Heap hs) r))
  (let-match many ids (Cons _ x rest) ((Nil _) h))
  (let-match many vs (Cons _ v vrest) ((Nil _) h))
  (let ((many (Heap hs) h2)) $ match many (settled-ref _ (heap-entries _ h) x) _ ((None _) (heap-set-settled _ h x v)) ((Some _ _) h))
  (tail $ set-run-states _ h2 rest vrest))

(def-fns _ $ (many sweep-run : (many (Env) env) (many (Nat) start) (subterm many (List $ Nat) ids) -> (many (Env) r))
  (let-match many ids (Cons _ x rest) ((Nil _) env))
  (let-match many (nat-lt start x) (BTrue) ((BFalse) env))
  (let-match many (or (is-settled env x) $ is-meta env x) (BFalse) ((BTrue) (tail $ sweep-run env start rest)))
  (match many (entry-mult-of env x) _
    ((Erased) (tail $ sweep-run (set-state-closed env x $ BToken _) start rest))
    (else (env-error env $ str-cat3 "internal: run-position entry " (qname env x) " has no value"))))

(def-fns _ $ (many const-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Multiplicity) ms) (many (List $ Nat) ids) -> (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let ((many (Nat) x) (many (List $ Nat) more)) $ match many ids (((Nat) _) ((List $ Nat) _)) ((Cons _ x0 r0) (values x0 r0)) ((Nil _) (values 0 $ Nil _)))
  (match many m _
    ((Erased) (let ((many codes) (erased pk)) $ tail $ const-codes ctx rest ids) (values codes (PkErased _ rest codes pk)))
    ((Many) (let ((many codes) (erased pk)) $ notail $ const-codes ctx rest more) (values (Cons _ (CConst _ x) codes) (PkMany _ rest (CConst _ x) codes pk)))
    ((Once) (let ((many codes) (erased pk)) $ notail $ const-codes ctx rest more) (values (Cons _ (CConst _ x) codes) (PkOnce _ rest (CConst _ x) codes pk)))))

(def-fns _ $ (many kept-ids : (subterm many (List $ Multiplicity) ms) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (let-match many ms (Cons _ m rest) ((Nil _) (Nil _)))
  (let-match many ids (Cons _ x more) ((Nil _) (Nil _)))
  (match many m _ ((Erased) (tail $ kept-ids rest more)) (else (Cons _ x $ notail $ kept-ids rest more))))

(def-fns _ $ (many forward-binders : (many (Env) e) (subterm many (List $ Nat) ids) (many (List $ Res) ress) (many (List $ Multiplicity) ms) -> (many (Env) r))
  (let-match many ids (Cons _ x rest) ((Nil _) e))
  (let-match many ress (Cons _ r rrest) ((Nil _) e))
  (let-match many ms (Cons _ m mrest) ((Nil _) e))
  (let ((many e2)) $ match many (res-term r) (((Env) _)) ((TVar y) (forward-binder e x y m)) (else e))
  (tail $ forward-binders e2 rest rrest mrest))

(def-fns _ $ (many run-form : (many (Env) env) (many (Nat) start) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (List $ Res) ress) (many (Hoisted ctx expect) h) -> (many (Env) r) (many (Hoisted ctx expect) h2))
  (let-match many (and (env-run-pos env) $ not $ env-failed env) (BTrue) ((BFalse) (values env h)))
  (let-match many ctx (Nil _) ((Cons _ _ _) (values env h)))
  (let-match many (mult-is-many $ pos-in env expect) (BTrue) ((BFalse) (values (sweep-run env start $ scope-ids $ env-scope env) h)))
  (let ((many env1) (many ids)) $ run-ids env start expect ress)
  (let ((erased _) (many hp)) $ env-heap env1)
  (let ((erased _) (many hp2) (erased _) (many vs) (erased _)) $ run-code (env-fuel env1) _ hp _ $ hoisted-code _ expect h)
  (let ((many env2)) $ env-with-heap env1 _ $ set-run-states _ hp2 ids vs)
  (let ((many codes) (erased cpk)) $ const-codes ctx expect ids)
  (values (sweep-run env2 start $ scope-ids $ env-scope env2) $ hoist-none ctx expect $ CValues _ expect codes cpk))

(def-fns _ $ (many written : (many (Env) env) (many (Multiplicity) pos) (many (Multiplicity) m) (many (String) what) -> (many (Env) r))
  (match many (and (not $ mult-is-many pos) $ mult-is-many m) _
    ((BTrue) (env-error env $ say env $ str-cat3 what " written `" $ str-cat (mult-name m) "` in an erased position; write `erased` here"))
    ((BFalse) env)))

; Whether [ty] applies the prelude's [name] type constructor, found in the prelude's scope however the program
; shadows the name, as lib/elab.ml's nullary finds it.
(def-fns _ $ (many prelude-nullary : (many (Env) env) (many (Term) ty) (many (String) name) -> (many (Bool) b))
  (let-match many (type-head env ty) (Some _ tid) ((None _) (BFalse)))
  (let ((many _) (many x)) $ prelude-id env name)
  (nat-eq tid x))

; The multiplicity a position demands of a value by its type (lib/elab.ml's demanded): a callable head takes
; a Cell or a UniqueFn at unique, and the driver takes a Program at unique.
(def-fns _ $ (many final-demand : (many (Env) env) (many (Term) ty) -> (many (Multiplicity) m))
  (match many (prelude-nullary env ty "Program") _ ((BTrue) (Once)) ((BFalse) (Many))))

(def-fns _ $ (many mode-demand : (many (Env) env) (many (Term) ty) (many (Multiplicity) pos) (many (Bool) final) -> (many (Multiplicity) m))
  (match many final _ ((BTrue) (final-demand env ty)) ((BFalse) (head-demand env ty pos))))

(def-fns _ $ (many demand-mode : (erased (List $ Multiplicity) expect) (many (Env) env) (many (ExprDemand expect) demand) (many (Multiplicity) m) (many (Term) ty) -> (many (Multiplicity) r))
  (match many demand _ ((Fixed _) m) ((CallableHead p) (head-demand env ty p)) ((FinalDemand) (final-demand env ty))))

(def-fns _ $ (many produced-first : (many (List $ Multiplicity) expect) (many (Env) env) (many (ExprDemand expect) demand) (many (What) what) (many (List $ Res) ress) -> (many (Env) env2) (many (List $ Res) ress2))
  (let-match many ress (Cons _ r rest) ((Nil _) (values env ress)))
  (let ((many env2) (many r2)) $ produced env what (demand-mode _ env demand (pos-in env expect) $ res-ty r) r)
  (values env2 $ Cons _ r2 rest))

(def-fns _ $ (many returns-produced : (erased (List $ Multiplicity) e0) (many (Env) env) (many (ExprDemand e0) demand) (many (Maybe $ Nat) cid) (many (String) fallback) (many (List $ Multiplicity) expect) (subterm many (List $ Entry) rets) (many (List $ Res) ress) -> (many (Env) env2) (many (List $ Res) ress2))
  (let-match many rets (Cons _ e erest) ((Nil _) (values env ress)))
  (let-match many expect (Cons _ m mrest) ((Nil _) (values env ress)))
  (let-match many ress (Cons _ r rrest) ((Nil _) (values env ress)))
  (let-match many e (MkEntry nm _ mu _ _ site))
  (let ((many env2) (many r2)) $ produced env (WReturn nm site cid fallback mu) (demand-mode _ env demand m $ res-ty r) r)
  (let ((many env3) (many rest2)) $ notail $ returns-produced _ env2 demand cid fallback mrest erest rrest)
  (values env3 $ Cons _ r2 rest2))

(def-fns _ $ (many intern-raw : (many (Env) env) (many (Syn) raw) -> (many (Env) r))
  (let ((erased _) (many h)) $ env-heap env)
  (let ((many env2) (erased _) (many h2) (erased _)) $ intern-lit env _ h raw)
  (env-with-heap env2 _ h2))

(def-fns _ $ (many lit-node : (many (List $ LitEntry) ls) (many (Nat) x) -> (many (Maybe $ Syn) r))
  (let-match many (lit-of ls x) (Some _ p) ((None _) (None _)))
  (match many p _ ((MkPair _ _ _ n) (Some _ n))))

(def-fns _ $ (many syn-at : (many (Spot) p) (many (Syn) r) -> (many (Syn) r2))
  (match many r _ ((RNat _ n) (RNat p n)) ((RChr _ c) (RChr p c)) ((RString _ s) (RString p s)) (else r)))

(def-fns _ $ (many syn-literal : (many (Env) env) (many (Syn) raw) -> (many (Syn) r))
  (let-match many raw (RAtom p n) (else raw))
  (let-match many n (NHandle x rd m _) (else raw))
  (let-match many (and (reading-eq rd $ MintedIs) $ mult-eq m $ Many) (BTrue) ((BFalse) raw))
  (match many (lit-node (env-lits env) x) _ ((Some _ node) (syn-at p node)) ((None _) raw)))

(def-fns _ $ (many lit-interned : (many (Env) env) (many (Syn) raw) -> (many (Env) r) (many (Syn) r2))
  (let-match many (lit-key raw) (Some _ k) ((None _) (values env raw)))
  (let ((many env2)) $ env-back env $ intern-raw (env-at env $ raw-pos raw) raw)
  (let-match many (lit-lookup env2 k) (Some _ x) ((None _) (values env2 raw)))
  (values env2 $ RAtom (raw-pos raw) $ NHandle x (MintedIs) (Many) $ show-r raw))

(def-fns _
  ((many syn-interned : (many (Env) env) (subterm many (Syn) r) -> (many (Env) e2) (many (Syn) r2))
    (let-match many r (RList p xs) (else (lit-interned env r)))
    (let ((many e2) (many ys)) $ notail $ syns-interned env xs)
    (values e2 $ RList p ys))
  ((many syns-interned : (many (Env) env) (subterm many (List $ Syn) xs) -> (many (Env) e2) (many (List $ Syn) ys))
    (let-match many xs (Cons _ x rest) ((Nil _) (values env $ Nil _)))
    (let ((many e1) (many y)) $ notail $ syn-interned env x)
    (let ((many e2) (many ys)) $ notail $ syns-interned e1 rest)
    (values e2 $ Cons _ y ys)))

(def-fns _ $ (many lit-entry : (many (Env) env) (many (Syn) raw) -> (many (Env) r) (many (Maybe $ Nat) x))
  (let ((many env2)) $ intern-raw env raw)
  (let-match many (lit-key raw) (Some _ k) ((None _) (values env2 $ None _)))
  (values env2 $ lit-lookup env2 k))

(def-fns _ $ (many var-named : (many (Env) env) (many (Name) n) -> (many (Env) r) (many (Maybe $ Nat) x))
  (match many (lookup env n) _
    ((Some _ x) (values (env-refer env (BFalse) x) $ Some _ x))
    ((None _) (values (env-error env $ str-cat3 "unbound name " (tick $ spell-name n) $ hint env n) $ None _))))

(def-fns _ $ (many var-found : (many (Env) env) (many (Name) n) -> (many (Env) r) (many (Maybe $ Nat) x))
  (let-match many n (NHandle _ rd _ _) (else (var-named env n)))
  (let-match many rd (MintedType) ((MintedIs) (var-named env n)))
  (values (env-error env $ str-cat3 "a handle to " (tick $ spell-name n) " is not a name") $ None _))

; The entry an atom names: a literal's, or the newest of that name in scope; id zero, which nothing binds,
; stands for an error already recorded.
(def-fns _ $ (many var : (many (Env) env) (many (Name) n) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many found)) $ var-found env n)
  (values env2 $ match many found _ ((Some _ x) x) ((None _) (Zero))))

(def-fns _ $ (many error-at : (many (Env) env) (many (Spot) pos) (many (String) msg) -> (many (Env) r))
  (env-back env $ env-error (env-at env pos) msg))

(def-fns _ $ (many no-mult : (many (Env) env) (many (Spot) epos) (many (String) what) (many (Multiplicity) m) -> (many (Env) r))
  (error-at env epos $ say env $ str-cat3 what " take no multiplicity; drop `" $ str-cat (mult-name m) "`"))

(def-fns _ $ (many at-place : (many (Env) env) (many (Bool) places) (many (Multiplicity) mult) (many (Spot) epos) (many (Syn) target) -> (many (Env) r) (many (Maybe $ Term) p))
  (let-match many places (BTrue) ((BFalse) (values (error-at env epos $ say env "`at` is allowed only on function telescope and match annotation entries") $ None _)))
  (let ((many tpos)) $ raw-pos target)
  (let-match many (raw-is-literal $ syn-literal env target) (BFalse) ((BTrue) (values (error-at env tpos $ say env "`at` names a variable, not a literal") $ None _)))
  (let ((many envv) (many found)) $ match many target (((Env) _) ((Maybe $ Nat) _))
    ((RAtom _ n) (var-found (env-at env tpos) n))
    (else (values (error-at env tpos $ str-cat "expected a location variable, got " $ qraw target) $ None _)))
  (let-match many found (Some _ x) ((None _) (values (env-back env envv) $ None _)))
  (let-match many (or (mult-is-many $ entry-mult-of env x) $ not $ mult-is-many mult) (BTrue) ((BFalse) (values (error-at env tpos $ say env "`at` needs a variable declared `many` or `unique`") $ None _)))
  (values (env-refer env (and (mult-is-many mult) $ not $ env-usage-erased env) x) $ Some _ $ slot-atom x))

(def-fns _ $ (many not-name : (many (Syn) raw) -> (many (String) s))
  (match many (raw-handle raw) _ ((BTrue) (str-cat3 "a handle to " (qraw raw) " is not a name")) ((BFalse) (str-cat (show-r raw) " is a literal, not a name"))))

(def-fns _ $ (many name-checked : (many (Env) env) (many (Syn) raw0) (many (String) what) -> (many (Env) r) (many (Maybe $ Name) s))
  (let ((many raw)) $ syn-literal env raw0)
  (let-match many (raw-binder raw) (Some _ b)
    ((None _)
      (match many (or (raw-is-literal raw) $ raw-handle raw) _
        ((BTrue) (values (env-error env $ not-name raw) $ None _))
        ((BFalse) (values (env-error env $ str-cat3 "expected " what $ str-cat ", got " $ qraw raw) $ None _)))))
  (values env b))

(def-fns _ $ (many var-of-raw : (many (Env) env) (many (Syn) raw0) (many (String) what) -> (many (Env) r) (many (Nat) x))
  (let ((many raw)) $ syn-literal env raw0)
  (match many raw _
    ((RAtom _ s) (var env s))
    ((RWild _) (values (env-error env "`_` is not a name, and nothing is inferred here") $ Zero))
    ((RList _ _) (values (env-error env $ str-cat3 "expected " what $ str-cat ", got " $ qraw raw) $ Zero))
    (else (let ((many env2) (many x)) $ lit-entry env raw) (values env2 $ match many x _ ((Some _ y) y) ((None _) (Zero))))))

(def-fns _ $ (many type-handle : (many (Syn) raw) -> (many (Maybe $ Nat) x))
  (let-match many raw (RAtom _ n) (else (None _)))
  (let-match many n (NHandle hx rd _ _) (else (None _)))
  (match many rd _ ((MintedType) (Some _ hx)) ((MintedIs) (None _))))

(def-fns _ $ (many atom-var : (many (Env) env) (many (Syn) raw) (many (String) what) -> (many (Env) r) (many (Nat) x))
  (let-match many raw (RAtom _ n) (else (var-of-raw env raw what)))
  (let-match many n (NHandle hx rd _ _) (else (var-of-raw env raw what)))
  (let-match many rd (MintedType) ((MintedIs) (var-of-raw env raw what)))
  (bind (env-refer env (BFalse) hx) (None _) (None _) (BFalse) (Erased) type-term (Some _ $ minted-type env hx) delegate-id))

(def-fns _ $ (many shown-entry : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (let-match many (lit-spelling (env-lits env) x) (None _) ((Some _ k) k))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (match many n _ ((None _) "_") ((Some _ s) (spell-name s))))

(def-fns _ $ (many handle-of : (many (Env) env) (many (Syn) araw) (many (Nat) x) (many (Multiplicity) mode) -> (many (Env) r) (many (Nat) y) (many (Term) ty))
  (let ((many site)) $ raw-pos araw)
  (let ((erased _) (many st)) $ entry-state env x)
  (let ((many env1) (many y)) $ match many st (((Env) _) ((Nat) _)) ((SSettled _ _ m) (values env m)) ((SHypothetical _) (values (error-at env site $ str-cat (qname env x) " is `Hypothetical`, and a handle names a `Settled` entry") x)))
  (let ((many env2)) $ match many (or (mult-eq mode $ Erased) $ mult-eq mode $ made env1 araw x) (((Env) _)) ((BTrue) env1)
    ((BFalse) (error-at env1 site $ str-cat3 (qname env1 x) " is not declared " $ tick $ spell env1 $ mult-name mode)))
  (let-match many (prelude-missing env2 "`settled-of`" "Settled") (None _) ((Some _ msg) (values (env-error env2 msg) y $ TErr "handle")))
  (let ((many env3) (many cid)) $ prelude-id env2 "Settled")
  (let ((many env4) (many mid)) $ prelude-id env3 $ match many mode _ ((Erased) "MErased") ((Many) "MMany") ((Once) "MUnique"))
  (values env4 y $ TApp (TVar cid) $ Cons _ (TApp (TVar mid) $ Nil _) $ Cons _ (minted-type env4 y) $ Cons _ (minted-is y) $ Nil _))

; A name read through its alias (section 8), which must resolve to a variable.
(def-fns _ $ (many named : (many (Env) env) (many (Syn) raw) (many (String) what) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ var-of-raw env raw what)
  (match many (canon-env env2 $ TVar x) _
    ((TVar y) (values env2 y))
    ((TBound _) (values env2 x)) ((TErr _) (values env2 x)) (else (values (env-error env2 $ str-cat3 (qshow env2 $ TVar x) " is not " what) x))))


; ---- Source telescopes (section 3), with erased proofs placing every raw they hold inside the raw list it
; was read from; the elaborator recurses on those raws.

; b is a, or a strict subterm of a.
(def-adts $ (Within : ((List $ Syn) b) ((List $ Syn) a) -> Type)
  enum
  (many WHere : (erased (List $ Syn) a) -> (Within a a))
  (many WIn : (erased (List $ Syn) b) (erased (List $ Syn) a) (erased (Subterm (List $ Syn) b (List $ Syn) a) p) -> (Within b a)))

(def-fns _ $ (erased in-within : (erased Type A) (erased A x) (erased (List $ Syn) b) (erased (List $ Syn) a) (erased (Subterm A x (List $ Syn) b) p) (erased (Within b a) w) -> (erased (Subterm A x (List $ Syn) a) q))
  (match erased w _
    ((WHere _) p)
    ((WIn _ _ s) (subterm-trans p s))))

(def-fns _ $ (erased within-in : (erased (List $ Syn) c) (erased (List $ Syn) b) (erased Type A) (erased A x) (erased (Within c b) w) (erased (Subterm (List $ Syn) b A x) p) -> (erased (Subterm (List $ Syn) c A x) q))
  (match erased w _
    ((WHere _) p)
    ((WIn _ _ s) (subterm-trans s p))))

(def-fns _ $ (erased within-step : (erased (List $ Syn) c) (erased (List $ Syn) b) (erased (List $ Syn) a) (erased (Subterm (List $ Syn) c (List $ Syn) b) p) (erased (Within b a) w) -> (erased (Within c a) q))
  (WIn _ _ $ in-within (List $ Syn) c b a p w))

; A body's final expression, placed in the body's root, or none.
(def-adts $ (Final : ((Nat) fuel) ((List $ Syn) root) -> Type)
  enum
  (many FinalNone : (erased (Nat) fuel) (erased (List $ Syn) root) -> (Final fuel root))
  (many FinalIs : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (Final fuel root))
  (many FinalMade : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Nat) f) (erased (Subterm (Nat) f (Nat) fuel) p) (many (Syn) r) -> (Final fuel root)))

(def-fns _ $ (many final-lift : (erased (Nat) fuel) (many (Nat) f2) (erased (Subterm (Nat) f2 (Nat) fuel) q) (erased (List $ Syn) root) (erased (List $ Syn) all) (many (Final f2 all) fin) -> (many (Final fuel root) r))
  (match many fin _
    ((FinalNone _ _) (FinalNone _ _))
    ((FinalIs _ _ r _) (FinalMade _ _ f2 q r))
    ((FinalMade _ _ f p r) (FinalMade _ _ f (subterm-trans p q) r))))

(def-fns _ $ (many final-raw : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Final fuel root) fin) (many (Syn) none) -> (many (Syn) r))
  (match many fin _ ((FinalNone _ _) none) ((FinalIs _ _ r _) r) ((FinalMade _ _ _ _ r) r)))

; A raw strictly inside the list root.
(def-adts $ (Sub : ((List $ Syn) root) -> Type)
  enum
  (many MkSub : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (Sub root)))

(def-fns _ $ (many subs-of : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) -> (many (List $ Sub root) r))
  (let-match many items (Cons _ t rest) ((Nil _) (Nil _)))
  (Cons _ (MkSub _ t $ in-within (Syn) t items root (prove-subterm t items) w)
    $ notail $ subs-of rest _ $ within-step rest items root (prove-subterm rest items) w))

(def-fns _ $ (many subs-all : (many (List $ Syn) items) -> (many (List $ Sub items) r))
  (subs-of items _ $ WHere items))

; A telescope written in a bracket of its own, and what follows it: the entries are the bracket's items, so
; each is two hops below the root -- inside the bracket, which is inside the root.
; A hop budget: a function that hands its whole raw to another spends one step (see the elaborator block).
(def-adts $ (Steps : ((Nat) n) -> Type)
  enum
  (many SZ : -> (Steps $ Zero))
  (many SS : (erased (Nat) n) (many (Steps n) k) -> (Steps $ Succ n)))
(let ((many one-step)) $ SS _ $ SZ)
(let ((many two-steps)) $ SS _ one-step)

(def-adts
  ((SrcEntry : ((List $ Syn) root) -> Type)
    enum
    (many MkSrcEntry : (erased (List $ Syn) root) (many (Bool) is-sub) (many (Maybe $ Multiplicity) mult) (many (Maybe $ SrcSg root) sg) (many (Maybe $ Name) name) (many (Maybe $ Syn) place) (many (Spot) site) -> (SrcEntry root)))
  ((SrcSg : ((List $ Syn) root) -> Type)
    enum
    (many SrcTy : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (SrcSg root))
    (many SrcIs : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (SrcSg root))))

; Whether every binder carries a type or an is clause, so a let's binders are a telescope (DESIGN.md section 50).
(def-fns _ $ (many all-have-sg : (erased (List $ Syn) root) (subterm many (List $ SrcEntry root) es) -> (many (Bool) r))
  (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
  (let-match many e (MkSrcEntry _ _ _ ssg _ _ _))
  (let-match many ssg (Some _ _)
    ((None _) (BFalse)))
  (match many rest _ ((Nil _) (BTrue)) ((Cons _ _ _) (tail $ all-have-sg _ rest))))

(def-fns _ $ (many at-tail : (many (Env) env) (many (List $ Syn) xs) -> (many (Maybe $ Syn) r))
  (let-match many xs (Cons _ mark rest) ((Nil _) (None _)))
  (let-match many rest (Cons _ target more) ((Nil _) (None _)))
  (match many (and (and (is-mark env mark $ MkAt) $ list-is-empty _ more) $ match many target (((Bool) _)) ((RList _ _) (BFalse)) (else (BTrue))) _
    ((BFalse) (None _))
    ((BTrue) (Some _ target))))

(def-fns _ $ (many names-then-at : (many (Env) env) (subterm many (List $ Syn) rs) -> (many (Bool) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (BTrue)))
  (let-match many (is-some _ $ at-tail env rs) (BFalse) ((BTrue) (BTrue)))
  (match many (raw-binder r) _ ((None _) (BFalse)) ((Some _ _) (tail $ names-then-at env rest))))

(def-fns _ $ (many trailing-at : (many (Env) env) (subterm many (List $ Syn) xs) -> (many (Maybe $ Syn) r))
  (let-match many xs (Cons _ _ rest) ((Nil _) (None _)))
  (match many (at-tail env xs) _ ((Some _ p) (Some _ p)) ((None _) (tail $ trailing-at env rest))))

(def-fns _ $ (many entries-of-names : (subterm many (List $ Syn) names) (many (Env) env) (many (Bool) is-sub) (many (Maybe $ Multiplicity) mult) (many (Spot) site) (erased (List $ Syn) root) (many (Syn) ty) (erased (Subterm (Syn) ty (List $ Syn) root) pty) (many (Maybe $ Syn) place) -> (many (List $ SrcEntry root) r))
  (let-match many (at-tail env names) (None _) ((Some _ _) (Nil _)))
  (let-match many names (Cons _ n rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ entries-of-names rest env is-sub mult site _ ty pty place)
  (Cons _ (MkSrcEntry _ is-sub mult (Some _ $ SrcTy _ ty pty) (raw-name n) place site) more))

(def-fns _ $ (many parse-entry : (many (Env) env) (many (Syn) raw) (erased (List $ Syn) root) (erased (Subterm (Syn) raw (List $ Syn) root) pr) -> (many (List $ SrcEntry root) r))
  (let-match many raw (RList epos items0) (else (Nil $ SrcEntry root)))
  (let ((erased w0)) $ WIn _ _ $ subterm-trans (prove-subterm items0 raw) pr)
  (let ((many (Bool) sub3) (many (List $ Syn) items1) (erased (Within items1 root) w1))
    (match many items0 _
      ((Nil _) (values (BFalse) items0 w0))
      ((Cons _ t rest)
        (match many (is-mark env t $ MkSubterm) (((Bool) _) ((List $ Syn) l) ((Within l root) w))
          ((BTrue) (values (BTrue) rest $ within-step _ _ _ (prove-subterm rest items0) w0))
          ((BFalse) (values (BFalse) items0 w0))))))
  (let ((many (Maybe $ Multiplicity) mult) (many (List $ Syn) items) (erased (Within items root) w2))
    (match many items1 _
      ((Nil _) (values (None _) items1 w1))
      ((Cons _ t rest)
        (match many (mult-of env t) (((Maybe $ Multiplicity) _) ((List $ Syn) l) ((Within l root) w))
          ((None _) (values (None _) items1 w1))
          ((Some _ m) (values (Some _ m) rest $ within-step _ _ _ (prove-subterm rest items1) w1))))))
  (let-match many items (Cons _ first rest) ((Nil _) (Nil _)))
  (let ((erased pf)) $ in-within _ _ _ _ (prove-subterm first items) w2)
  (let-match many (names-then-at env rest) (BTrue) ((BFalse) (Nil _)))
  (let ((many place)) $ trailing-at env items)
  (let-match many (or (list-is-empty _ rest) $ is-some _ $ at-tail env rest) (BFalse)
    ((BTrue) (match many (raw-binder first) _ ((None _) (Nil _)) ((Some _ n) (Cons _ (MkSrcEntry _ sub3 mult (None _) n place epos) $ Nil _)))))
  (let-match many rest (Cons _ second rest2) ((Nil _) (Nil _)))
  (let-match many rest2 (Cons _ third rest3) ((Nil _) (entries-of-names rest env sub3 mult epos _ first pf place)))
  (match many (and (is-mark env second $ MkIs) $ or (list-is-empty _ rest3) $ is-some _ $ at-tail env rest3) _
    ((BTrue) (Cons _ (MkSrcEntry _ sub3 mult (Some _ $ SrcIs _ first pf) (raw-name third) place epos) $ Nil _))
    ((BFalse) (entries-of-names rest env sub3 mult epos _ first pf place))))

; The items before the arrow, and those after it, which sit within the root.
(def-fns _ $ (many split-arrow : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) (many (Env) env) -> (many (Env) r) (many (List $ Sub root) before) (many (List $ Syn) after) (erased (Within after root) wa))
  (let-match many items (Cons _ t rest) ((Nil _) (values (env-error env (say env "missing `->`")) (Nil _) items w)))
  (let ((erased wr)) $ within-step _ _ _ (prove-subterm rest items) w)
  (let-match many (is-mark env t $ MkArrow) (BFalse) ((BTrue) (values env (Nil _) rest wr)))
  (let ((many env2) (many before) (many after) (erased wa)) $ notail $ split-arrow rest _ wr env)
  (values env2 (Cons _ (MkSub _ t $ in-within (Syn) t items root (prove-subterm t items) w) before) after wa))

; Leading annotation tokens from the marks given, in any order; returns the flags for absurd/newtype and extern.
(def-fns _ $ (many take-marks : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) (many (Env) env) (many (MarkK) first) (many (MarkK) second) -> (many (Bool) has-first) (many (Bool) has-second) (many (List $ Syn) rest) (erased (Within rest root) wr))
  (let-match many items (Cons _ t more) ((Nil _) (values (BFalse) (BFalse) items w)))
  (let ((erased wm)) $ within-step _ _ _ (prove-subterm more items) w)
  (match many (is-mark env t first) _
    ((BTrue)
      (let ((many _) (many s) (many rest) (erased wr)) $ notail $ take-marks more _ wm env first second)
      (values (BTrue) s rest wr))
    ((BFalse)
      (let-match many (is-mark env t second) (BTrue) ((BFalse) (values (BFalse) (BFalse) items w)))
      (let ((many f) (many _) (many rest) (erased wr)) $ notail $ take-marks more _ wm env first second)
      (values f (BTrue) rest wr))))

(def-fns _ $ (many trusted-checked : (many (Env) env) (many (String) form) -> (many (Maybe $ Env) r))
  (match many (env-externs env) _
    ((BTrue) (None _))
    ((BFalse) (Some _ $ env-error env $ str-cat3 "only the prelude may write " (tick $ spell env form) "; a program that declares its own runs with `--no-prelude`"))))

(def-fns _ $ (many extern-checked : (many (Env) env) (many (Bool) ext) -> (many (Env) r) (many (Bool) kept))
  (let ((many bad)) $ and ext $ not $ env-externs env)
  (values (refuse-when env bad "only the prelude may mark a definition `extern`; a program that declares its own runs with `--no-prelude`") (and ext $ not bad)))

; A function header's marks, `absurd`, `extern` and `at`, in any order (section 39).
(def-fns _ $ (many take-marks3 : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) (many (Env) env) -> (many (Bool) isabs) (many (Bool) isext) (many (Bool) isat) (many (List $ Syn) rest) (erased (Within rest root) wr))
  (let-match many items (Cons _ t more) ((Nil _) (values (BFalse) (BFalse) (BFalse) items w)))
  (let ((erased wm)) $ within-step _ _ _ (prove-subterm more items) w)
  (let ((many (Bool) a) (many (Bool) e) (many (Bool) f))
    (values (is-mark env t $ MkAbsurd) (is-mark env t $ MkExtern) (is-mark env t $ MkAt)))
  (let-match many (or a $ or e f) (BTrue) ((BFalse) (values (BFalse) (BFalse) (BFalse) items w)))
  (let ((many a2) (many e2) (many f2) (many rest) (erased wr)) $ notail $ take-marks3 more _ wm env)
  (values (or a a2) (or e e2) (or f f2) rest wr))

; ---- Constructors, Matchables and shapes (sections 8, 24, 33)

(def-fns _ $ (many adt-of : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Adt) r))
  (let ((erased _) (many blk)) $ env-block env x)
  (let-match many blk (Some _ b)
    ((None _) (None _)))
  (match many b _ ((BMat _ adt) (Some _ adt)) (else (None $ Adt))))

(def-fns _ $ (many ctor-of : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Ctor) r))
  (let ((erased _) (many blk)) $ env-block env x)
  (let-match many blk (Some _ b)
    ((None _) (None _)))
  (match many b _ ((BCtorFn _ c) (Some _ c)) (else (None $ Ctor))))

(def-fns _ $ (many ctor-named : (many (Env) env) (many (String) name) -> (many (Maybe $ Ctor) r))
  (let-match many (lookup env $ NSrc name) (Some _ x) ((None _) (None _)))
  (ctor-of env x))

(def-fns _ $ (many raw-ext : (many (Env) env) -> (many (Maybe $ ExtType) r))
  (let-match many (ctor-named env "NoPos") (Some _ np) ((None _) (None _)))
  (let-match many (ctor-named env "MkPos") (Some _ mp) ((None _) (None _)))
  (let-match many (ctor-named env "Nil") (Some _ nl) ((None _) (None _)))
  (let-match many (ctor-named env "Cons") (Some _ cs) ((None _) (None _)))
  (let-match many (ctor-named env "SName") (Some _ sn) ((None _) (None _)))
  (let-match many (ctor-named env "SGen") (Some _ sg) ((None _) (None _)))
  (Some _ $ ExtRaw np mp nl cs sn sg))

(def-fns _ $ (many slots-ext : (many (Env) env) -> (many (Maybe $ ExtType) r))
  (let-match many (ctor-named env "Nil") (Some _ nl) ((None _) (None _)))
  (let-match many (ctor-named env "Cons") (Some _ cs) ((None _) (None _)))
  (Some _ $ ExtSlots nl cs))

(def-fns _ $ (many ctor-type : (many (Env) env) (many (Nat) c) -> (many (List $ Entry) tele) (many (Term) ret))
  (match many (type-of env c) _
    ((TValCtor tele ret) (values tele ret)) ((TErr m) (values (Nil _) $ TErr m)) (else (values (Nil $ Entry) $ TErr "not a constructor"))))

(def-fns _ $ (many tid-of : (many (Env) env) (many (Nat) c) -> (many (Nat) tid))
  (let ((many _) (many ret)) $ ctor-type env c)
  (match many (type-head env ret) _ ((None _) (Zero)) ((Some _ t) t)))

(def-adts $ (MatchInfo : -> Type)
  enum
  (many MkMatchInfo : (many (Nat) mid) (many (Disc) disc) (many (List $ MCtor) ctors) (many (Nat) rank) -> (MatchInfo)))

; A match that dispatches at runtime reads its Matchable's value: stamped in where the entry is Settled, else
; read from a non-erased entry still bound (ASSUMPTIONS 139).
(def-fns _ $ (many readable : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (or (is-some _ $ adt-of env x) $ and (mult-is-many $ entry-mult-of env x) $ list-mem-bin (env-objects env) x))

; Of the entries one opened group holds, the record keeps the best-ranked: one whose ADT the elaborator sees,
; then a readable one, then any.
(def-fns _ $ (many matchable-rank : (many (Env) env) (many (Nat) x) -> (many (Nat) r))
  (let-match many (adt-of env x) (None _)
    ((Some _ _) 0))
  (match many (readable env x) _ ((BTrue) 1) ((BFalse) 2)))

(def-fns _ $ (many held-needs-many : (many (Env) env) (many (Nat) tid) (many (Nat) mid) -> (many (Env) r))
  (match many (readable env mid) (((Env) _)) ((BTrue) env) ((BFalse) (env-error env $ str-cat3 (say env "the `Matchable` for ") (qshown env tid) " is erased or out of scope, so a non-erased match cannot take a value of it apart"))))

; The opened Matchable for a type, at most one (merge-opens): among the objects the index names for it, the
; first whose canonical type confirms it.
(def-fns _ $ (many find-matchable-in : (subterm many (List $ Opened) opens) (many (Env) env) (many (Nat) tid) (many (List $ Nat) cands) -> (many (Maybe $ MatchInfo) r))
  (let-match many opens (Cons _ o rest) ((Nil _) (None _)))
  (let ((many x)) $ opened-x o)
  (let-match many (list-mem-bin cands x) (BTrue) ((BFalse) (tail $ find-matchable-in rest env tid cands)))
  (let-match many (type-of env x) (TMatchable d _ _ t cs) (else (tail $ find-matchable-in rest env tid cands)))
  (let-match many t (TVar t2) (else (tail $ find-matchable-in rest env tid cands)))
  (match many (nat-cmp t2 tid) (((Maybe $ MatchInfo) _))
    ((CEq _ _ _) (Some _ $ MkMatchInfo x d cs $ matchable-rank env x))
    (else (tail $ find-matchable-in rest env tid cands))))


; The anonymous Coercible proof def-fns minted for a delegating function g (section 33).
(def-fns _ $ (many find-proof : (subterm many (List $ Nat) objects) (many (Env) env) (many (Nat) ctor) (many (Nat) arity) (many (Nat) index) (many (Nat) g) -> (many (Maybe $ Nat) r))
  (let-match many objects (Cons _ x rest) ((Nil _) (None _)))
  (let ((many hit)) $ match many (proof-target env x ctor arity index) (((Bool) _)) ((Some _ g2) (nat-eq g2 g)) ((None _) (BFalse)))
  (match many hit _
    ((BTrue) (Some _ x))
    ((BFalse) (tail $ find-proof rest env ctor arity index g))))

(def-fns _ $ (many fetched-proof : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) arg) (many (Nat) ctor) (many (Nat) arity) (many (Nat) index) (many (String) kind) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Term) t))
  (let ((many env2) (many g)) $ named env arg "a function name")
  (match many (find-proof (env-objects env2) env2 ctor arity index g) _
    ((None _) (values ew (env-error env2 $ str-cat (qshown env2 g) $ str-cat3 " has no `" kind "` proof in scope") $ None _))
    ((Some _ x) (values ew env2 $ Some _ $ TVar x))))

; A Matchable's constructors, each with its phantom marker, id and number of many fields (section 33).
(def-adts $ (CShape : -> Type)
  enum
  (many MkCShape : (many (Multiplicity) m) (many (Nat) c) (many (Nat) arity) -> (CShape)))

(def-fns _ $ (many shapes : (subterm many (List $ MCtor) ctors) (many (Env) env) -> (many (List $ CShape) r))
  (let-match many ctors (Cons _ mc rest) ((Nil _) (Nil _)))
  (let-match many mc (MkMCtor m t))
  (let ((many c)) $ term-var t)
  (let ((many tele) (many _)) $ ctor-type env c)
  (Cons _ (MkCShape m c $ stored-count tele) $ notail $ shapes rest env))

(def-fns _ $ (many non-phantom : (subterm many (List $ CShape) ss) -> (many (List $ CShape) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (MkCShape m _ _))
  (match many m _ ((Many) (Cons _ s $ notail $ non-phantom rest))
                  ((Once) (Cons _ s $ notail $ non-phantom rest)) ((Erased) (tail $ non-phantom rest))))

(def-fns _ $ (many shape-index : (subterm many (List $ CShape) ss) (many (Nat) c) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (None _)))
  (let-match many s (MkCShape _ c2 _))
  (match many (nat-cmp c c2) _ ((CEq _ _ _) (Some _ i)) (else (tail $ shape-index rest c $ Succ i))))

; A phantom constructor heads no runtime value (section 14 rule 2), so discriminants number the others only.
(def-fns _ $ (many discriminant : (many (List $ CShape) ss) (many (Nat) c) -> (many (Nat) r))
  (match many (shape-index (non-phantom ss) c 0) _ ((None _) 0) ((Some _ i) i)))

(def-fns _ $ (many tagged-of : (many (Disc) disc) (many (List $ CShape) ss) -> (many (Bool) r))
  (match many disc _
    ((DUnion) (BFalse))
    ((DEnum) (nat-lt 1 $ list-length _ $ non-phantom ss))))

(def-fns _ $ (many marker : (subterm many (List $ MCtor) ctors) (many (Nat) c) -> (many (Multiplicity) m))
  (let-match many ctors (Cons _ mc rest) ((Nil _) (Many)))
  (let-match many mc (MkMCtor m t))
  (let-match many t (TVar c2) (else (tail $ marker rest c)))
  (match many (nat-cmp c c2) _ ((CEq _ _ _) m) (else (tail $ marker rest c))))



(def-fns _ $ (many wrappers : (subterm many (List $ CShape) ss) -> (many (List $ Nat) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (MkCShape m c n))
  (match many (and (mult-is-many m) $ nat-eq n 1) _
    ((BTrue) (Cons _ c $ notail $ wrappers rest))
    ((BFalse) (tail $ wrappers rest))))

(def-fns _ $ (many some-not-single : (subterm many (List $ CShape) ss) -> (many (Bool) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (BFalse)))
  (let-match many s (MkCShape m _ n))
  (or (and (mult-is-many m) $ not $ nat-eq n 1) $ notail $ some-not-single rest))

; The wrapping constructors of a type of newtype shape (section 33), none if it is not of that shape.
(def-fns _ $ (many newtype-wrappers : (many (Disc) disc) (many (List $ CShape) ss) -> (many (List $ Nat) r))
  (match many (or (tagged-of disc ss) $ some-not-single ss) _
    ((BTrue) (Nil _))
    ((BFalse) (wrappers ss))))

(def-fns _ $ (many find-newtype-in : (subterm many (List $ Opened) opens) (many (Env) env) (many (Nat) c) (many (List $ Nat) cands) -> (many (Maybe $ Nat) r))
  (let-match many opens (Cons _ o rest) ((Nil _) (None _)))
  (let ((many x)) $ opened-x o)
  (let ((many found))
    (match many (list-mem-bin cands x) (((Bool) _))
      ((BFalse) (BFalse))
      ((BTrue)
        (let-match many (type-of env x) (TMatchable d nt _ _ cs) (else (BFalse)))
        (match many nt (((Bool) _))
          ((BFalse) (BFalse))
          ((BTrue) (list-mem-bin (newtype-wrappers d $ shapes cs env) c))))))
  (match many found _ ((BTrue) (Some _ x)) ((BFalse) (tail $ find-newtype-in rest env c cands))))

(def-fns _ $ (many find-newtype : (many (Env) env) (many (Nat) c) -> (many (Maybe $ Nat) r))
  (find-newtype-in (env-opens env) env c $ index-of c $ env-index env))

(def-fns _
  ((many term-place : (many (Env) env) (subterm many (Term) t) -> (many (Maybe $ Term) p))
    (match many t _
      ((TVar x) (Some _ $ slot-atom x))
      ((TSlotOf s) (match many s (((Maybe $ Term) _)) ((TVar x) (Some _ $ slot-atom x)) (else (None _))))
      ((TApp h args)
        (let-match many (canon-env env h) (TVar c) (else (None _)))
        (let-match many (find-newtype env c) (Some _ _) ((None _) (None _)))
        (let ((many tele) (many _)) $ ctor-type env c)
        (tail $ stored-arg-place env tele args))
      (else (None _))))
  ((many stored-arg-place : (many (Env) env) (many (List $ Entry) tele) (subterm many (List $ Term) args) -> (many (Maybe $ Term) p))
    (let-match many args (Cons _ a rest) ((Nil _) (None _)))
    (let-match many tele (Cons _ e trest) ((Nil _) (None _)))
    (match many (mult-is-many $ entry-mult e) _
      ((BTrue) (tail $ term-place env a))
      ((BFalse) (tail $ stored-arg-place env trest rest)))))

(def-fns _ $ (many at-target : (many (Env) env) (many (List $ Term) acc) (many (Term) p) -> (many (Term) r))
  (let-match many p (TSlotOf b) (else (instantiate acc p)))
  (let-match many b (TBound k) (else (instantiate acc p)))
  (maybe-or _ (term-place env $ list-nth-or _ acc k $ TBound k) $ instantiate acc p))

(def-fns _ $ (many term-res : (many (Term) t) (many (Term) ty) -> (many (Res) r))
  (MkRes t ty (Erased) $ None _))

(def-fns _ $ (many cshape-arities : (subterm many (List $ CShape) ss) -> (many (List $ Nat) r))
  (let-match many ss (Cons _ s rest)
    ((Nil _) (Nil _)))
  (match many s _ ((MkCShape _ _ n) (Cons _ n $ notail $ cshape-arities rest))))

(def-fns _ $ (many hollow-ctor : (many (Env) env) (many (Nat) c) -> (many (Bool) r))
  (let ((many tid)) $ tid-of env c)
  (let-match many (find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env) (Some _ info) ((None _) (BFalse)))
  (let-match many info (MkMatchInfo mid disc cs _))
  (let-match many (type-of env mid) (TMatchable _ _ ext _ _) (else (BFalse)))
  (let ((many ss)) $ shapes cs env)
  (and (not ext) $ and (list-mem-bin (mctor-ids cs) c) $ hollow-shape (tagged-of disc ss) $ cshape-arities $ non-phantom ss))

(def-fns _ $ (many ctor-records : (subterm many (List $ CShape) ss) (many (Env) env) (many (Nat) index) (many (Bool) tagged) (many (Maybe $ ExtType) ext) (many (List $ Nat) shape) (many (Bool) nt) -> (many (List $ Ctor) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (Nil _)))
  (match many s _
    ((MkCShape _ c n) (Cons _ (MkCtor (entry-name-or-id env c) c index n tagged ext shape nt) $ notail $ ctor-records rest env (Succ index) tagged ext shape nt))))

; The ADT a Matchable's type describes (section 24): the non-phantom constructors at their discriminants.
(def-fns _ $ (many mint-adt : (many (Env) env) (many (Nat) tid) (many (Disc) disc) (many (List $ CShape) ss) (many (Maybe $ ExtType) ext) (many (Bool) nt) -> (many (Adt) r))
  (let ((many tagged)) $ tagged-of disc ss)
  (MkAdt (entry-name-or-id env tid) tagged (ctor-records (non-phantom ss) env 0 tagged ext (cshape-arities $ non-phantom ss) nt) ext nt))

(def-fns _ $ (many alias-target : (many (Env) env) (many (Nat) x) -> (many (Nat) r))
  (match many (idmap-get _ x $ env-aliases env) _ ((Hit _ _ _ t _) t) ((Miss _ _ _ _) x)))

; A variable in a non-erased position: a Settled entry's value embedded with its entry (section 29), or a
; Hypothetical entry's place in the frames the code binds.
(def-fns _ $ (many var-code : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) x) -> (many (Code ctx many-one) r))
  (let-match many (is-settled env x) (BFalse) ((BTrue) (CConst _ x)))
  (match many (mem-dec x ctx) _
    ((Some _ p) (CVar _ x p))
    ((None _) (CError _ many-one $ str-cat "internal: not bound at runtime: " $ shown-name env x))))

(def-fns _ $ (many matchable-code : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) pos) (many (Nat) x) -> (many (Code ctx (Cons (Multiplicity) pos (Nil (Multiplicity)))) r))
  (match many pos _
    ((Erased) (CErased _ $ Cons _ pos $ Nil _))
    ((Many) (var-code env ctx x))
    ((Once) (recast _ (Cons _ (Once) $ Nil _) many-one (MsManyOnce _ _ $ MsNil) $ var-code env ctx x))))

; A match on an ADT the elaborator can see reads no Matchable at runtime (section 24); one on a held
; Matchable reads it as the ADT its type describes.
(def-fns _ $ (many match-shape : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) x) (many (Nat) tid) (many (Disc) disc) (many (List $ CShape) ss) -> (many (Shape ctx) r))
  (match many (adt-of env x) _ ((Some _ adt) (ShKnown _ adt)) ((None _) (ShHeld _ (var-code env ctx x) $ mint-adt env tid disc ss (None _) $ match many (type-of env x) (((Bool) _)) ((TMatchable _ nt _ _ _) nt) (else (BFalse))))))

(def-fns _ $ (many mint : (many (Env) env) (many (Term) ty) -> (many (Env) r) (many (Res) res))
  (let ((many env2) (many x)) $ bind env (None _) (None _) (BFalse) (Erased) ty (None _) delegate-id)
  (values env2 $ res-of env2 x))


(def-fns _ $ (many sg-inst : (many (List $ Term) args) (many (Sg) sg) -> (many (Sg) r))
  (match many sg _
    ((SgTy t) (SgTy $ instantiate args t))
    ((SgIs t ty) (SgIs (instantiate args t) $ instantiate args ty))))

(def-fns _ $ (many fact-of : (many (Sg) sg) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (match many sg _
    ((SgTy t) (values t $ None _))
    ((SgIs t ty) (values ty $ Some _ t))))

(def-fns _ $ (many proof-type : (many (Nat) ctor) (many (List $ Term) args) -> (many (Term) t))
  (TApp (TVar ctor) args))

(def-fns _ $ (many nth-term : (many (List $ Term) ts) (many (Nat) i) -> (many (Term) t))
  (match many (list-nth _ ts i) _ ((NthMiss _ _ _ _) (TErr "missing argument")) ((NthHit _ _ _ t _) t)))

; Values for binders, many ones from the list in order, erased ones the token.
(def-fns _ $ (many non-erased : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Nat) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (Nil _)))
  (match many (entry-mult-of env x) _
    ((Many) (Cons _ x $ notail $ non-erased rest env))
    ((Once) (Cons _ x $ notail $ non-erased rest env))
    ((Erased) (tail $ non-erased rest env))))

(def-fns _ $ (many ress-of : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Res) r))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (Cons _ (res-of env x) $ notail $ ress-of rest env))))

(def-fns _ $ (many tvars-rev : (subterm many (List $ Nat) ids) (many (List $ Term) acc) -> (many (List $ Term) r))
  (match many ids _
    ((Nil _) acc)
    ((Cons _ x rest) (tail $ tvars-rev rest $ Cons _ (TVar x) acc))))

(def-fns _ $ (many under-list : (subterm many (List $ Multiplicity) ms) (many (Multiplicity) pos) -> (many (List $ Multiplicity) r))
  (match many ms _
    ((Nil _) (Nil _))
    ((Cons _ m rest) (Cons _ (under pos m) $ notail $ under-list rest pos))))

(def-fns _ $ (many all-erased : (subterm many (List $ Multiplicity) ms) -> (many (List $ Multiplicity) r))
  (match many ms _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (Erased) $ notail $ all-erased rest))))

(def-fns _ $ (many no-code : (erased (List $ List $ Nat) ctx) -> (many (Code ctx many-one) c))
  (CError _ many-one "no value"))

(def-fns _ $ (many codes-missing : (erased (List $ List $ Nat) ctx) (subterm many (List $ Multiplicity) ms) -> (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let ((many codes) (erased pk)) $ notail $ codes-missing ctx rest)
  (let ((many (Code ctx many-one) missing)) $ no-code _)
  (match many m _
    ((Many) (values (Cons _ missing codes) (PkMany _ rest missing codes pk)))
    ((Once) (values (Cons _ missing codes) (PkOnce _ rest missing codes pk)))
    ((Erased) (values codes (PkErased _ rest codes pk)))))

; Binds fresh ids for the many returns and keeps those the position takes many (sections 14, 19): the ids
; first, then each one's place in the frame they form, then the code referring to them there.
(def-fns _ $ (many fresh-bound : (subterm many (List $ Multiplicity) rets) (many (Env) env) -> (many (Env) r) (many (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk))
  (let-match many rets (Cons _ m rest) ((Nil _) (values env (Nil _) (PkNil _))))
  (match many m _
    ((Erased)
      (let ((many env2) (many bound) (erased bpk)) $ tail $ fresh-bound rest env)
      (values env2 bound (PkErased _ rest bound bpk)))
    ((Many)
      (let ((many env2) (many t)) $ env-fresh-id env)
      (let ((many env3) (many bound) (erased bpk)) $ notail $ fresh-bound rest env2)
      (values env3 (Cons _ t bound) (PkMany _ rest t bound bpk)))
    ((Once)
      (let ((many env2) (many t)) $ env-fresh-id env)
      (let ((many env3) (many bound) (erased bpk)) $ notail $ fresh-bound rest env2)
      (values env3 (Cons _ t bound) (PkOnce _ rest t bound bpk)))))

(def-fns _ $ (many kept-of : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) frame) (subterm many (List $ Multiplicity) expect) (many (List $ Multiplicity) rets) (erased (Lockstep (Multiplicity) (Multiplicity) expect rets) lock) (erased (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk) (many (List $ AtIn frame) ats) (erased (Lockstep (Nat) (AtIn frame) bound ats) lk) ->
    (many (List $ Code (Cons (List (Nat)) frame ctx) many-one) kept) (erased (Picked (Code (Cons (List (Nat)) frame ctx) many-one) expect kept) kpk))
  (let-match many expect (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let-match erased lock (LsCons _ _ _ _ _ _ lp))
  (let-match many rets (Cons _ rm rrest))
  (match many rm _
    ((Erased)
      (let-match erased bpk (PkErased _ _ _ bp))
      (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp ats lk)
      (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) missing)) $ no-code _)
      (match many m _
        ((Erased) (values kept (PkErased _ rest kept kpk)))
        ((Many) (values (Cons _ missing kept) (PkMany _ rest missing kept kpk)))
        ((Once) (values (Cons _ missing kept) (PkOnce _ rest missing kept kpk)))))
    ((Many)
      (let-match erased bpk (PkMany _ _ _ _ bp))
      (let-match erased lk (LsCons _ _ _ _ _ _ lq))
      (let-match many ats (Cons _ at3 arest))
      (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp arest lq)
      (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) code)) $ match many at3 _ ((MkAtIn _ z p) (CVar _ z $ MHere _ _ _ p)))
      (match many m _
        ((Many) (values (Cons _ code kept) (PkMany _ rest code kept kpk)))
        ((Once) (values (Cons _ code kept) (PkOnce _ rest code kept kpk)))
        ((Erased) (values kept (PkErased _ rest kept kpk)))))
    ((Once)
      (let-match erased bpk (PkOnce _ _ _ _ bp))
      (let-match erased lk (LsCons _ _ _ _ _ _ lq))
      (let-match many ats (Cons _ at3 arest))
      (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp arest lq)
      (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) code)) $ match many at3 _ ((MkAtIn _ z p) (CVar _ z $ MHere _ _ _ p)))
      (match many m _
        ((Many) (values (Cons _ code kept) (PkMany _ rest code kept kpk)))
        ((Once) (values (Cons _ code kept) (PkOnce _ rest code kept kpk)))
        ((Erased) (values kept (PkErased _ rest kept kpk)))))))

(def-fns _ $ (many projection : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (List $ Multiplicity) rets) (erased (Lockstep (Multiplicity) (Multiplicity) expect rets) lock) (many (Env) env) ->
    (many (Env) r) (many (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk) (many (List $ Code (Cons (List (Nat)) bound ctx) many-one) kept) (erased (Picked (Code (Cons (List (Nat)) bound ctx) many-one) expect kept) kpk))
  (let ((many env2) (many bound) (erased bpk)) $ fresh-bound rets env)
  (let ((many ats) (erased lk)) $ at-ins bound)
  (let ((many kept) (erased kpk)) $ kept-of ctx bound expect rets lock bound bpk ats lk)
  (values env2 bound bpk kept kpk))

(def-fns _ $ (many mark-words : (subterm many (List $ Nat) ids) (many (Env) env) (many (Bool) temporary) -> (many (Env) r))
  (match many ids _ ((Nil _) env) ((Cons _ x xs) (tail $ mark-words xs (mark-word env x temporary) temporary))))

(def-fns _ $ (many at-in-frame : (subterm many (List $ Nat) ids) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (let-match many ids (Cons _ x rest)
    ((Nil _) (None _)))
  (match many (and (mult-is-many $ entry-mult-of env x) $ equal-env env p $ slot-atom x) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ at-in-frame rest env p))))

(def-fns _ $ (many at-in-frames : (subterm many (List $ List $ Nat) ctx) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (let-match many ctx (Cons _ frame rest)
    ((Nil _) (None _)))
  (match many (at-in-frame frame env p) _ ((Some _ x) (Some _ x)) ((None _) (tail $ at-in-frames rest env p))))

(def-fns _ $ (many at-constant : (subterm many (List $ Nat) ids) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (None _)))
  (match many (and (is-settled env x) $ and (mult-is-many $ entry-mult-of env x) $ equal-env env p $ slot-atom x) _
    ((BTrue) (Some _ x)) ((BFalse) (tail $ at-constant rest env p))))

(def-fns _ $ (many at-literal : (subterm many (List $ LitEntry) ls) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (None _)))
  (let-match many l (MkLitEntry x _ _ _ _))
  (match many (equal-env env p $ slot-atom x) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ at-literal rest env p))))

; A variable the code holds physically whose slot is [p], the word an `at` entry is read from (section 36).
(def-fns _ $ (many direct-word : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Term) p0) -> (many (Maybe $ Nat) r))
  (let-match many p0 (TSlotOf c) (else (None _)))
  (let-match many c (TVar x) (else (None _)))
  (match many (and (mult-is-many $ entry-mult-of env x) $ or (is-settled env x) $ is-some _ $ mem-dec x ctx) _ ((BTrue) (Some _ x)) ((BFalse) (None _))))

(def-fns _ $ (many location-var : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Term) p0) -> (many (Env) r) (many (Nat) x))
  (let ((many direct)) $ direct-word env ctx p0)
  (let ((many p)) $ canon-env env p0)
  (let ((many inframe)) $ match many direct (((Maybe $ Nat) _)) ((Some _ _) direct) ((None _) (at-in-frames ctx env p)))
  (let ((many constant)) $ match many inframe (((Maybe $ Nat) _)) ((Some _ _) inframe) ((None _) (at-constant (env-words env) env p)))
  (let ((many found)) $ match many constant (((Maybe $ Nat) _)) ((Some _ _) constant) ((None _) (at-literal (env-lits env) env p)))
  (match many found _ ((Some _ x) (values env x)) ((None _) (values (env-error env $ str-cat (say env "no caller word for `at` ") $ qshow env p) 0))))

; A parameter written `at` is not passed: inside the body it is a rename of the word its target holds
; (section 36), bound over the frame of the runtime parameters [base], the first such parameter outermost;
; [before] holds the parameters bound so far, the place of each entry being written over those alone.
(def-fns _ $ (many at-renames : (subterm many (List $ Entry) params) (many (List $ Nat) pids) (many (List $ Term) before) (many (Env) env) (many (List $ List $ Nat) base) -> (many (Env) r) (many (List $ List $ Nat) ctx) (many (StmtCode base ctx) sc))
  (let-match many params (Cons _ e rest) ((Nil _) (values env base $ SNone _)))
  (let-match many pids (Cons _ y yrest) ((Nil _) (values env base $ SNone _)))
  (let ((many after)) $ Cons _ (TVar y) before)
  (let-match many (entry-place e) (Some _ p) ((None _) (tail $ at-renames rest yrest after env base)))
  (let-match many (mult-is-many $ entry-mult-of env y) (BTrue) ((BFalse) (tail $ at-renames rest yrest after env base)))
  (let ((many env2) (many src)) $ location-var env base $ instantiate before p)
  (let ((many env3) (many ctx) (many more)) $ notail $ at-renames rest yrest after env2 $ Cons _ (Cons _ y $ Nil _) base)
  (values env3 ctx $ SSeq _ _ _ (SLet _ many-one (Cons _ y $ Nil _) (PkMany _ (Nil _) y (Nil _) $ PkNil _) (var-code env2 base src)) more))

(def-fns _ $ (many physical-mults : (subterm many (List $ Entry) tele) -> (many (List $ Multiplicity) ms))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (Cons _ (match many (entry-place e) (((Multiplicity) _)) ((Some _ _) (Erased)) ((None _) (entry-mult e))) $ notail $ physical-mults rest))))

(def-fns _ $ (many project-code : (erased (List $ List $ Nat) ctx) (many (Env) env) (many (List $ Multiplicity) input) (many (List $ Multiplicity) output) (many (Code ctx input) code) -> (many (Env) r) (many (Code ctx output) c))
  (let-match many (lockstep-dec _ _ output input) (LdYes _ _ _ _ lk)
    ((LdNo _ _ _ _) (values (env-error env "internal: return projection size") $ CError _ output "projection")))
  (let ((many env2) (many ids) (erased pk) (many kept) (erased kp)) $ projection ctx output input lk env)
  (values env2 $ CLet _ input _ ids pk code $ CValues _ output kept kp))

(def-fns _ $ (many result-codes : (subterm many (List $ Multiplicity) expect) (many (List $ Entry) tele) (many (List $ Nat) ids) (many (List $ Term) args) (many (Env) env) (many (List $ List $ Nat) ctx) ->
    (many (Env) r) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) expect codes) pk))
  (let-match many expect (Cons _ m rest) ((Nil _) (values env (Nil _) $ PkNil _)))
  (let ((many x) (many more)) $ match many ids (((Nat) _) ((List $ Nat) more)) ((Nil _) (values 0 ids)) ((Cons _ x xs) (values x xs)))
  (let ((many place) (many tail3)) $ match many tele (((Maybe $ Term) _) ((List $ Entry) tail3)) ((Nil _) (values (None _) tele)) ((Cons _ e es) (values (entry-place e) es)))
  (let ((many env2) (many code))
    (match many m (((Env) _) ((Code ctx many-one) code))
      ((Erased) (values env $ CError _ many-one "erased return"))
      (else
        (let-match many place (Some _ p) ((None _) (values env $ var-code env ctx x)))
        (let ((many env2) (many y)) $ location-var env ctx $ instantiate args p)
        (values env2 $ var-code env2 ctx y))))
  (let ((many env3) (many codes) (erased pk)) $ notail $ result-codes rest tail3 more (Cons _ (TVar x) args) env2 ctx)
  (match many m _
    ((Erased) (values env3 codes $ PkErased _ rest codes pk))
    ((Many) (values env3 (Cons _ code codes) $ PkMany _ rest code codes pk))
    ((Once) (values env3 (Cons _ code codes) $ PkOnce _ rest code codes pk))))

; What a signature passes or returns at runtime: its non-erased entries without a written `at` (section 36).
(def-fns _ $ (many runtime-ids : (subterm many (List $ Entry) tele) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many ids (Cons _ x xrest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ runtime-ids rest xrest)
  (match many (entry-stored e) _ ((BTrue) (Cons _ x more)) ((BFalse) more)))

(def-fns _ $ (many has-place : (subterm many (List $ Entry) tele) -> (many (Bool) r))
  (match many tele _ ((Nil _) (BFalse)) ((Cons _ e rest) (or (is-some _ $ entry-place e) $ notail $ has-place rest))))

(def-fns _ $ (many runtime-count : (subterm many (List $ Entry) tele) -> (many (Nat) n))
  (let-match many tele (Cons _ e rest) ((Nil _) 0))
  (let ((many more)) $ notail $ runtime-count rest)
  (match many (entry-stored e) _ ((BTrue) (Succ more)) ((BFalse) more)))

(def-fns _ $ (many slot-named-bound : (many (Term) c) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many c (TBound k) (else acc))
  (let ((many j)) $ nat-sub k d)
  (match many (and (not $ nat-lt k d) $ nat-lt j i) _ ((BTrue) (Cons _ (nat-sub i $ Succ j) acc)) ((BFalse) acc)))
(def-fns _
  ((many slot-named : (subterm many (Term) t) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many t _
      ((TSlotOf c) (tail $ slot-named-bound c i d $ notail $ slot-named c i d acc))
      ((TApp h args) (tail $ slot-named h i d $ notail $ slot-named-list args i d acc))
      ((TCell h args) (tail $ slot-named h i d $ notail $ slot-named-list args i d acc))
      ((TFn _ l ps rs) (tail $ slot-named l i d $ notail $ slot-named-tele ps i d $ notail $ slot-named-tele rs i (nat-add d $ list-length _ ps) acc))
      ((TTyCtor ps) (tail $ slot-named-tele ps i d acc))
      ((TValCtor ps ret) (tail $ slot-named-tele ps i d $ notail $ slot-named ret i (nat-add d $ list-length _ ps) acc))
      ((TMatchable _ _ _ ty cs) (tail $ slot-named ty i d $ notail $ slot-named-mctors cs i d acc))
      (else acc)))
  ((many slot-named-list : (subterm many (List $ Term) ts) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (match many ts _
      ((Nil _) acc)
      ((Cons _ t rest) (tail $ slot-named t i d $ notail $ slot-named-list rest i d acc))))
  ((many slot-named-mctors : (subterm many (List $ MCtor) cs) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (let-match many cs (Cons _ c rest) ((Nil _) acc))
    (match many c _ ((MkMCtor _ t) (tail $ slot-named t i d $ notail $ slot-named-mctors rest i d acc))))
  ((many slot-named-entry : (subterm many (Entry) e) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (let-match many e (MkEntry _ _ _ sg place _))
    (let ((many acc2)) $ match many place (((List $ Nat) _)) ((None _) acc) ((Some _ p) (notail $ slot-named p i d acc)))
    (match many sg _ ((SgTy t) (tail $ slot-named t i d acc2)) ((SgIs t _) (tail $ slot-named t i d acc2))))
  ((many slot-named-tele : (subterm many (List $ Entry) es) (many (Nat) i) (many (Nat) d) (many (List $ Nat) acc) -> (many (List $ Nat) r))
    (let-match many es (Cons _ e rest) ((Nil _) acc))
    (tail $ slot-named-tele rest i (Succ d) $ notail $ slot-named-entry e i d acc)))

(def-fns _ $ (many slot-named-signature : (subterm many (List $ Entry) es) (many (Nat) i) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many es (Cons _ e rest) ((Nil _) acc))
  (tail $ slot-named-signature rest (Succ i) $ slot-named-entry e i 0 acc))
(def-fns _ $ (many slot-named-params : (many (List $ Entry) params) (many (List $ Entry) rets) -> (many (List $ Nat) r))
  (let ((many all) (erased _)) $ list-append _ params rets)
  (slot-named-signature all 0 $ Nil _))

(def-fns _ $ (many has-runtime : (many (List $ Entry) tele) -> (many (Bool) r))
  (not $ nat-is-zero $ runtime-count tele))

; [code] produces the runtime entries of [tele], bound to [rids]; the entries written `at` are read from the
; words the code holds (section 36), as a call's returns are. An at-match [skipped] has no runtime at all.
(def-fns _ $ (many reconstruct : (many (List $ List $ Nat) ctx) (many (Env) env) (many (List $ Multiplicity) expect) (many (List $ Entry) tele) (many (List $ Nat) rids) (many (Bool) skipped) (many (Code ctx expect) code) -> (many (Env) r) (many (Code ctx expect) out))
  (let-match many (and (mult-is-many $ pos-in env expect) $ or skipped $ has-place tele) (BTrue) ((BFalse) (values env code)))
  (let ((many physical)) $ physical-mults tele)
  (let-match many (lockstep-dec _ _ physical rids) (LdYes _ _ _ _ lk)
    ((LdNo _ _ _ _) (values (env-error env "internal: reconstruction size") code)))
  (let ((many bound) (erased bpk)) $ picked-of _ physical rids lk)
  (let ((many env2) (many projected)) $ match many skipped (((Env) _) ((Code ctx physical) _))
    ((BFalse) (project-code ctx env expect physical code))
    ((BTrue) (let ((many missing) (erased pk)) $ codes-missing ctx physical) (values env $ CValues _ physical missing pk)))
  (let ((many env3) (many kept) (erased kpk)) $ result-codes expect tele rids (Nil _) env2 $ Cons _ bound ctx)
  (values env3 $ CLet _ physical _ bound bpk projected $ CValues _ expect kept kpk))

; [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
; their ids in order; names, multiplicities and states override the telescope's own when given.
(def-fns _ $ (many opened-among : (subterm many (List $ Opened) os) (many (List $ Nat) ids) -> (many (List $ Opened) r))
  (let-match many os (Cons _ o rest)
    ((Nil _) (Nil _)))
  (match many (list-mem-bin ids $ opened-x o) _ ((BTrue) (Cons _ o $ notail $ opened-among rest ids)) ((BFalse) (tail $ opened-among rest ids))))

; Two opened objects of one kind naming one thing.
(def-fns _ $ (many opened-share : (many (Opened) x) (many (Opened) y) -> (many (Bool) r))
  (let-match many x (MkOpened _ kx nx))
  (match many y _
    ((MkOpened _ ky ny)
      (and (nat-eq (open-kind-code kx) $ open-kind-code ky) $ and (nat-lt (open-kind-code kx) 2) $ nats-share nx ny))))

; The first of [ys] sharing a name with x; only one older than x, of a smaller id (an object is opened after
; the entries it may share with were bound), when [older-only].
(def-fns _ $ (many first-sharing : (subterm many (List $ Opened) ys) (many (Opened) x) (many (Bool) older-only) -> (many (Maybe $ Nat) r))
  (let-match many ys (Cons _ y rest) ((Nil _) (None _)))
  (match many (and (or (not older-only) $ nat-lt (opened-x y) $ opened-x x) $ opened-share x y) _
    ((BTrue) (Some _ $ opened-x y))
    ((BFalse) (tail $ first-sharing rest x older-only))))

; A newer opened object and an older one naming one thing, if any: the newest such object, and the newest
; older one it shares with; the list holds the newer first. Only a pair with a [touched] object, one whose
; names changed since the invariant last held, can share, the others having been disjoint then, so an
; untouched object is compared with the touched ones [tos] alone.
(def-fns _ $ (many open-pair : (subterm many (List $ Opened) opens) (many (List $ Nat) touched) (many (List $ Opened) tos) -> (many (Maybe $ Pair (Nat) (Nat)) r))
  (let-match many opens (Cons _ x rest) ((Nil _) (None _)))
  (let ((many (Maybe $ Nat) y))
    (match many (list-mem-bin touched $ opened-x x) _
      ((BTrue) (first-sharing rest x $ BFalse))
      ((BFalse) (first-sharing tos x $ BTrue))))
  (match many y _
    ((Some _ yy) (Some _ $ MkPair _ _ (opened-x x) yy))
    ((None _) (tail $ open-pair rest touched tos))))

; At most one opened Matchable names a given type constructor or value constructor, and at most one opened
; Newtype a given constructor (section 8): two that would are unified, forcing, and the better-ranked entry
; kept, the older on a tie, until no two name one thing; [fuel] bounds the merges by the list's length, and
; [touched] holds the objects whose names changed since the invariant last held, the unification adding to
; the environment's own those it changes.
(def-fns _ $ (many merge-opens : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Nat) touched) -> (many (UnifyRes) r))
  (let-match many fuel (Succ f) ((Zero) (UOk env)))
  (let ((many opens)) $ env-opens env)
  (let-match many (open-pair opens touched $ opened-among opens touched) (Some _ pr) ((None _) (UOk env)))
  (let-match many pr (MkPair _ _ newer older))
  (let-match many (unify-force (Forcing env) (type-of env newer) (type-of env older)) (Forcing env2)
    ((Refuted m) (UContra m)))
  (let ((many drop)) $ match many (nat-lt (matchable-rank env2 newer) $ matchable-rank env2 older) (((Nat) _)) ((BTrue) older) ((BFalse) newer))
  (let ((many env3)) $ env-unopen env2 drop)
  (let ((many all) (erased _)) $ list-append _ (env-touched env3) $ nats-remove touched drop)
  (tail $ merge-opens f (env-settled env3) all))

; The invariant restored after a forcing (refine, open-adt, the printers), for the objects it touched.
(def-fns _ $ (many merge-all : (many (Forced) fe) -> (many (UnifyRes) r))
  (let-match many fe (Forcing env) ((Refuted m) (UContra m)))
  (match many (env-touched env) _
    ((Nil _) (UOk env))
    ((Cons _ _ _) (merge-opens (Succ $ list-length _ $ env-opens env) (env-settled env) $ env-touched env))))

(def-lvl place-lvl)
; [x] is at the slot term [p] (section 35): a rule on its automatic slot, minted by forcing, the opened
; objects merged after.
; While the slot is still the fresh atom it was minted as, with no rule, named by no opened object and absent
; from [p], the rule is added outright, which seems to be what forcing it would do; a slot a forcing has
; already ruled is forced as any atom is.
(def-fns _ $ (many slot-forced : (many (Env) env) (many (Nat) s) (many (Term) p) -> (many (UnifyRes) r))
  (def-fns place-lvl $ (many forced : -> (many (UnifyRes) r)) (merge-all $ unify-force (Forcing env) (TVar s) p))
  (let ((erased _) (erased _) (many bnd) (many tb)) $ env-table env)
  (let-match many tb (MkTable _ f0 _ _ _ _ _ _ c1 _ _ _))
  (let-match many (facts-lookup s _ f0 _ _ (WNil s) _ c1) (LFree _ _ _ _ _ _ ps) (else (forced)))
  (let ((many t) (erased _)) $ canon-in _ _ bnd tb p)
  (let-match many (term-eq t $ TVar s) (BFalse) ((BTrue) (UOk env)))
  (let-match many (rule-out-refresh _ _ bnd tb s ps t) (Some _ added) ((None _) (forced)))
  (match many added _ ((MkAdded _ _ _ _ tb2) (UOk $ env-set-table env _ _ bnd tb2))))

(def-fns _ $ (many place-forced : (many (Env) env) (many (Nat) x) (many (Term) p) -> (many (UnifyRes) r))
  (let-match many (env-slot-of env x) (Some _ s) ((None _) (UOk env)))
  (slot-forced env s p))

(def-fns _ $ (many placed-or : (many (Env) env) (many (Nat) x) (many (UnifyRes) o) (many (Term) p) -> (many (Env) r))
  (match many o _
    ((UOk env2) env2)
    ((UContra m) (env-error env $ str-cat3 "internal: " (qshow env $ TVar x) $ str-cat3 " cannot sit at " (qshow env p) $ str-cat3 " (" (clash-str env m) ")"))))

(def-fns _ $ (many env-place-at : (many (Env) env) (many (Nat) x) (many (Term) p) -> (many (Env) r))
  (placed-or env x (place-forced env x p) p))

(def-fns _ $ (many slot-at : (many (Env) env) (many (Nat) x) (many (Nat) s) (many (Term) p) -> (many (Env) r))
  (placed-or env x (slot-forced env s p) p))

(def-fns _ $ (many placed-at : (many (Env) env) (many (Nat) x) (many (Maybe $ Term) p) -> (many (Env) r))
  (match many p _ ((None _) env) ((Some _ q) (env-place-at env x q))))

; ---- Opening telescopes into scope

(def-adts $ (MultsMode : -> Type)
  enum
  (many MMDeclared : -> (MultsMode))
  (many MMErased : -> (MultsMode))
  (many MMExpect : (many (List $ Multiplicity) ms) -> (MultsMode)))

(def-fns _ $ (many open-tele : (subterm many (List $ Entry) tele) (many (Env) env) (many (Maybe $ List $ Maybe $ Name) names) (many (Maybe $ List $ Maybe $ Loc) sites) (many (Maybe $ List $ Multiplicity) mults) (many (List $ Term) ids) (many (Bool) meta) ->
    (many (Env) r) (many (List $ Nat) fresh) (erased (Lockstep (Entry) (Nat) tele fresh) lock))
  (let-match many tele (Cons _ e rest) ((Nil _) (values env (Nil _) (LsNil _ _))))
  (let-match many e (MkEntry ename _ emult esg place esite))
  (let ((many ty) (many rule)) $ fact-of $ sg-inst ids esg)
  (let ((many (Maybe $ Name) name) (many (Maybe $ List $ Maybe $ Name) names2))
    (match many names _
      ((None _) (values ename names))
      ((Some _ ns) (match many ns (((Maybe $ Name) _) ((Maybe $ List $ Maybe $ Name) ns2)) ((Nil _) (values ename names)) ((Cons _ n nrest) (values n $ Some _ nrest))))))
  ; [sites] given means this site is where the source writes the binders -- a pattern's fields --
  ; so they are the ones shadowing warns at; without it the telescope is being read back and each
  ; entry keeps the position its declaration carried (core.sl's bind-as).
  (let ((many (Maybe $ Loc) site) (many (Bool) warns) (many (Maybe $ List $ Maybe $ Loc) sites2))
    (match many sites _
      ((None _) (values esite (BFalse) sites))
      ((Some _ ss) (match many ss (((Maybe $ Loc) _) ((Bool) _) ((Maybe $ List $ Maybe $ Loc) _)) ((Nil _) (values (None _) (BTrue) sites)) ((Cons _ sf srest) (values sf (BTrue) $ Some _ srest))))))
  (let ((many (Multiplicity) mult) (many (Maybe $ List $ Multiplicity) mults2))
    (match many mults _
      ((None _) (values emult mults))
      ((Some _ ms) (match many ms (((Multiplicity) _) ((Maybe $ List $ Multiplicity) ms2)) ((Nil _) (values emult mults)) ((Cons _ m mrest) (values m $ Some _ mrest))))))
  (let ((many env2a) (many x)) $ bind-as env meta (BFalse) name site warns mult ty rule delegate-id)
  (let ((many env2)) $ match many place (((Env) _))
    ((None _) env2a)
    ((Some _ p) (match many meta (((Env) _)) ((BTrue) env2a) ((BFalse) (env-place-at env2a x $ instantiate ids p)))))
  (let ((many env3) (many more) (erased p)) $ notail $ open-tele rest env2 names2 sites2 mults2 (Cons _ (TVar x) ids) meta)
  (values env3 (Cons _ x more) (LsCons _ _ e x rest more p)))

(def-fns _ $ (many anon-names : (subterm many (List $ Entry) tele) -> (many (List $ Maybe $ Name) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (None _) $ notail $ anon-names rest))))

(def-fns _ $ (many finish-mode-tele : (many (Env) env) (many (List $ Entry) tele) (many (Multiplicity) pos) (many (Bool) final) ->
    (many (Env) out) (many (List $ Entry) selected) (many (List $ Multiplicity) inner) (many (DemandBridge many-one inner) bridge))
  (let-match many tele (Cons _ e rest) ((Nil _) (values env tele many-one (HeadDemand (Many)))))
  (let-match many e (MkEntry name sub2 _ sg place site))
  (let ((many ty) (many _)) (fact-of sg))
  (let ((many mode)) (mode-demand env ty pos final))
  (values env (Cons _ (MkEntry name sub2 mode sg place site) rest) (Cons _ mode (Nil _)) (HeadDemand mode)))

(def-fns _ $ (many finish-demand-tele : (many (List $ Multiplicity) expect) (many (ExprDemand expect) demand) (many (Env) env) (many (List $ Entry) tele) ->
    (many (Env) out) (many (List $ Entry) selected) (many (List $ Multiplicity) inner) (many (DemandBridge expect inner) bridge))
  (match many demand _
    ((Fixed _) (values env tele expect (KeepDemand _)))
    ((CallableHead p) (finish-mode-tele env tele p $ BFalse))
    ((FinalDemand) (finish-mode-tele env tele (Many) $ BTrue))))

(def-fns _ $ (many raw-sites : (subterm many (List $ Syn) rs) (many (Env) env) -> (many (List $ Maybe $ Loc) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (Some _ $ loc-in env $ raw-pos r) $ notail $ raw-sites rest env))))

(def-fns _ $ (many anon-sites : (subterm many (List $ Entry) tele) -> (many (List $ Maybe $ Loc) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (None _) $ notail $ anon-sites rest))))

(def-fns _ $ (many raw-names : (subterm many (List $ Syn) rs) -> (many (List $ Maybe $ Name) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (raw-name r) $ notail $ raw-names rest))))

; Entering a branch forces the scrutinee equal to the constructor over its fields (section 7).

(def-fns _ $ (many subterm-params : (subterm many (List $ Entry) tele) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many ids (Cons _ x irest) ((Nil _) (Nil _)))
  (match many (entry-sub e) _
    ((BTrue) (Cons _ x $ notail $ subterm-params rest irest))
    ((BFalse) (tail $ subterm-params rest irest))))

; Per-value multiplicities of the binders of a let or the entries of a signature.
(def-fns _ $ (many src-mults : (erased (List $ Syn) root) (subterm many (List $ SrcEntry root) es) -> (many (List $ Multiplicity) r) (erased (Lockstep (SrcEntry root) (Multiplicity) es r) lock))
  (let-match many es (Cons _ e rest) ((Nil _) (values (Nil _) (LsNil _ _))))
  (let ((many m)) $ match many e (((Multiplicity) _)) ((MkSrcEntry _ _ sm _ _ _ _) (match many sm (((Multiplicity) _)) ((None _) (Many)) ((Some _ mm) mm))))
  (let ((many r) (erased p)) $ notail $ src-mults _ rest)
  (values (Cons _ m r) (LsCons _ _ e m rest r p)))


(def-fns _
  ((many is-strict-subterm : (subterm many (Term) b) (many (Term) a) -> (many (Bool) r))
    (match many b _
      ((TApp _ args) (tail $ subterm-in args a)) (else (BFalse))))
  ((many subterm-in : (subterm many (List $ Term) ts) (many (Term) a) -> (many (Bool) r))
    (match many ts _
      ((Nil _) (BFalse))
      ((Cons _ t rest) (or (term-eq a t) $ or (notail $ is-strict-subterm t a) $ notail $ subterm-in rest a)))))

; A literal is an atom to the unifier (DESIGN.md section 45): checking fails where one meets a Succ shape or another
; literal, and forcing binds one where a contradiction was wanted. The notes name each literal a check or a
; trial turned on, a character standing for its code, with the first of [within] it sits in; numerals come
; first, then characters, each in order of value (lib/elab.ml's literal_notes).
(def-fns _ $ (many lit-value : (many (String) s) -> (many (Nat) n))
  (let-match many (all-digits s) (BFalse) ((BTrue) (parse-nat s 0)))
  (match many (char-lit-code s) _ ((Some _ n) n) ((None _) 0)))

(def-fns _ $ (many lit-before : (many (String) a) (many (String) b) -> (many (Bool) r))
  (match many (all-digits a) _
    ((BTrue) (match many (all-digits b) _ ((BTrue) (nat-lt (lit-value a) (lit-value b))) ((BFalse) (BTrue))))
    ((BFalse) (match many (all-digits b) _ ((BTrue) (BFalse)) ((BFalse) (nat-lt (lit-value a) (lit-value b)))))))

(def-fns _ $ (many hit-spelling : (many (Pair (Term) (LitEntry)) h) -> (many (String) s))
  (let-match many h (MkPair _ _ _ l))
  (match many (lit-entry-spelling l) _ ((Some _ s) s) ((None _) "internal: a minted constant read as a literal")))

(def-fns _ $ (many hit-insert : (many (Pair (Term) (LitEntry)) h) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (List $ Pair (Term) (LitEntry)) r))
  (let-match many hs (Cons _ x rest) ((Nil _) (Cons _ h $ Nil _)))
  (match many (lit-before (hit-spelling h) (hit-spelling x)) _
    ((BTrue) (Cons _ h hs))
    ((BFalse) (Cons _ x $ notail $ hit-insert h rest))))

(def-fns _ $ (many code-of-char : (many (Term) t) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (Bool) r))
  (let-match many hs (Cons _ h rest)
    ((Nil _) (BFalse)))
  (match many h _ ((MkPair _ _ ct _) (or (and (not $ all-digits $ hit-spelling h) $ is-strict-subterm ct t) $ notail $ code-of-char t rest))))

; The hits kept, a numeral that is a hit character's code left out, in order.
(def-fns _ $ (many hits-kept : (subterm many (List $ Pair (Term) (LitEntry)) hs) (many (List $ Pair (Term) (LitEntry)) all) (many (List $ Pair (Term) (LitEntry)) acc) -> (many (List $ Pair (Term) (LitEntry)) r))
  (let-match many hs (Cons _ h rest) ((Nil _) acc))
  (match many h _
    ((MkPair _ _ t _)
      (tail $ hits-kept rest all $ match many (and (all-digits $ hit-spelling h) $ code-of-char t all) (((List $ Pair (Term) (LitEntry)) _)) ((BTrue) acc) ((BFalse) (hit-insert h acc))))))

(def-fns _ $ (many lit-place : (many (Env) env) (many (Term) t) (subterm many (List $ Term) within) -> (many (Maybe $ Term) r))
  (let-match many within (Cons _ c rest)
    ((Nil _) (None _)))
  (match many (is-strict-subterm (canon-env env c) t) _ ((BTrue) (Some _ c)) ((BFalse) (tail $ lit-place env t rest))))

(def-fns _ $ (many literal-notes : (many (Env) env) (many (List $ Term) within) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many hs (Cons _ h rest) ((Nil _) (Nil _)))
  (let-match many h (MkPair _ _ t _))
  (let ((many s)) $ hit-spelling h)
  (let ((many (Bool) numeral)) $ all-digits s)
  (let ((many place)) $ match many (lit-place env t within) (((String) _)) ((None _) "") ((Some _ c) (str-cat " in " $ qshow env c)))
  (let ((many kind)) $ match many numeral (((String) _)) ((BTrue) " is a numeral literal, opaque") ((BFalse) " is a character literal, whose code is opaque"))
  (let ((many msg)) $ str-cat3 s place $ str-cat kind $ say env " to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more")
  (Cons _ (MkPair _ _ (env-loc env) msg) $ notail $ literal-notes env within rest))

; Where two canonical terms part: the pairs of subterms at which they first differ.
(def-fns _
  ((many differ : (subterm many (Term) a) (many (Term) b) -> (many (List $ Pair (Term) (Term)) r))
    (let-match many (term-eq a b) (BFalse) ((BTrue) (Nil _)))
    (let ((many one-pair)) $ Cons _ (MkPair _ _ a b) $ Nil _)
    (let-match many a (TApp h xs) (else one-pair))
    (let-match many b (TApp h2 ys)
      (else one-pair))
    (match many (and (term-eq h h2) $ nat-eq (list-length _ xs) $ list-length _ ys) _ ((BTrue) (tail $ differ-list xs ys)) ((BFalse) one-pair)))
  ((many differ-list : (subterm many (List $ Term) xs) (many (List $ Term) ys) -> (many (List $ Pair (Term) (Term)) r))
    (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
    (let-match many ys (Cons _ y yrest) ((Nil _) (Nil _)))
    (let ((many zs) (erased _)) $ list-append _ (notail $ differ x y) $ notail $ differ-list rest yrest)
    zs))

(def-fns _ $ (many pair-side : (many (Env) env) (many (Term) t) (subterm many (List $ Pair (Term) (Term)) pairs) -> (many (Bool) r))
  (let-match many pairs (Cons _ p rest) ((Nil _) (BFalse)))
  (let-match many p (MkPair _ _ a b))
  (or (and (not $ or (has-meta-env env a) $ has-meta-env env b)
        $ or (term-eq t a) $ or (term-eq t b) $ or (is-strict-subterm t a) $ is-strict-subterm t b)
    $ notail $ pair-side env t rest))

(def-fns _ $ (many check-hits : (many (Env) env) (subterm many (List $ Pair (Term) (LitEntry)) ls) (many (List $ Pair (Term) (Term)) pairs) -> (many (List $ Pair (Term) (LitEntry)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ check-hits env rest pairs)
  (let-match many l (MkPair _ _ t _))
  (match many (pair-side env t pairs) _ ((BTrue) (Cons _ l more)) ((BFalse) more)))

; What a forcing trial bound: each literal's canonical form under the trial, where the trial changed it.
(def-fns _ $ (many trial-bound : (many (Env) trial) (subterm many (List $ Pair (Term) (LitEntry)) ls) -> (many (List $ Term) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ trial-bound trial rest)
  (let-match many l (MkPair _ _ t _))
  (let ((many u)) $ canon-env trial t)
  (match many (term-eq u t) _ ((BTrue) more) ((BFalse) (Cons _ u more))))

(def-fns _ $ (many term-among : (many (Term) t) (subterm many (List $ Term) ts) -> (many (Bool) r))
  (match many ts _ ((Nil _) (BFalse)) ((Cons _ u rest) (or (term-eq t u) $ notail $ term-among t rest))))

(def-fns _ $ (many forced-hits : (many (Env) trial) (subterm many (List $ Pair (Term) (LitEntry)) ls) (many (List $ Term) bound) -> (many (List $ Pair (Term) (LitEntry)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ forced-hits trial rest bound)
  (let-match many l (MkPair _ _ t _))
  (match many (term-among (canon-env trial t) bound) _ ((BTrue) (Cons _ l more)) ((BFalse) more)))

; The notes for a branch a forcing trial left standing, [env] the environment before the trial.
(def-fns _ $ (many forced-notes : (many (Env) env) (many (Env) trial) (many (Res) r) -> (many (List $ Pair (Loc) $ String) e))
  (let ((many ls)) $ lit-terms env $ env-lits env)
  (let ((many hs)) $ forced-hits trial ls $ trial-bound trial ls)
  (literal-notes env (Cons _ (res-ty r) $ Cons _ (res-term r) $ Nil _) $ hits-kept hs hs $ Nil _))

; ---- Checks (section 9's canonicalize-then-compare) and proofs (section 18)

(def-fns _ $ (many ctor-result : (many (Env) env) (many (Term) t) -> (many (Maybe $ Pair (List $ Entry) (Term)) r))
  (match many (canon-env env t) _ ((TTyCtor ps) (Some _ $ MkPair _ _ ps type-term)) ((TValCtor ps ret) (Some _ $ MkPair _ _ ps ret)) (else (None _))))

(def-fns _ $ (many term-head : (many (Term) t) -> (many (Term) h))
  (match many t _ ((TApp h _) h) (else t)))

(def-fns _ $ (many ctor-hint : (many (Env) env) (many (Maybe $ Syn) raw) (many (Term) actual) (many (Term) expected) -> (many (String) s))
  (let-match many raw (Some _ r) ((None _) ""))
  (let-match many (ctor-result env actual) (Some _ pr) ((None _) ""))
  (let-match many pr (MkPair _ _ ps ret))
  (let-match many (equal-env env (term-head ret) $ term-head $ canon-env env expected) (BTrue) ((BFalse) ""))
  (let ((many p)) $ raw-pos r)
  (str-cat3 "\nhint: did you mean " (qraw $ RList p $ Cons _ r $ list-replicate _ (list-length _ ps) $ RWild p) "?"))

; Identity after canonicalization (section 9), solving any metas either side holds (unify-env); a mismatch
; is reported only when asked to.
(def-fns _ $ (many error-at-with : (many (Env) env) (many (Spot) pos) (many (List $ Pair (Loc) $ String) notes) (many (String) msg) -> (many (Env) r))
  (env-back env $ env-error-with (env-at env pos) notes msg))

(def-fns _ $ (many error-at-hinted : (many (Env) env) (many (Spot) pos) (many (List $ Pair (Loc) $ String) notes) (many (String) msg) (many (String) hints) -> (many (Env) r))
  (env-back env $ env-error-hinted (env-at env pos) notes msg hints))

(def-fns msg-lvl $ (many no-about : -> (many (String) p) (many (List $ Pair (Loc) $ String) n))
  (values "" $ Nil _))

(def-fns _ $ (many ill-typed-msg : (many (Env) env) (many (Clash) m) -> (many (Maybe $ String) r))
  (let-match many m (CIllTyped x t) (else (None _)))
  (let-match many (term-type env t) (Some _ tt) ((None _) (None _)))
  (Some _ $ str-cat3 "type mismatch: expected " (qshow env $ type-of env x) $ str-cat3 ", got " (qshow env tt) $ str-cat3 ": " (qshow env $ TVar x) $ str-cat " would be " $ qshow env t))

(def-fns _ $ (many solve-about : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) (many (Bool) report) (many (Maybe $ Syn) raw) (many (Fn msg-lvl -> (many (String) p) (many (List $ Pair (Loc) $ String) n)) about) -> (many (Env) r) (many (Bool) ok))
  (let-match many (unify-solve env actual expected) (UContra m) ((UOk env2) (values env2 $ BTrue)))
  (let-match many report (BTrue) ((BFalse) (values env $ BFalse)))
  (let ((many prefix) (many more)) (about))
  (let-match many (ill-typed-msg env m) (None _) ((Some _ s) (values (env-error-with env more $ str-cat prefix s) $ BFalse)))
  (let ((many ls)) $ lit-terms env $ env-lits env)
  (let ((many hs)) $ check-hits env ls $ differ (canon-env env actual) $ canon-env env expected)
  (let ((many notes) (erased _)) $ list-append _ (literal-notes env (Cons _ expected $ Cons _ actual $ Nil _) $ hits-kept hs hs $ Nil _) more)
  (values (env-error-hinted env notes (str-cat3 prefix what $ str-cat3 " mismatch: expected " (qshow env expected) $ str-cat ", got " $ qshow env actual) $ ctor-hint env raw actual expected) $ BFalse))

(def-fns _ $ (many wild-error : (many (Env) env) (many (Spot) apos) (many (Fn msg-lvl -> (many (String) p) (many (List $ Pair (Loc) $ String) n)) about) (many (String) msg) -> (many (Env) r))
  (let ((many prefix) (many notes)) (about))
  (error-at-with env apos notes $ str-cat prefix msg))

(def-fns _ $ (many solve : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) (many (Bool) report) (many (Maybe $ Syn) raw) -> (many (Env) r) (many (Bool) ok))
  (solve-about env what actual expected report raw no-about))

(def-fns _ $ (many check-raw : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) (many (Maybe $ Syn) raw) -> (many (Env) r))
  (let ((many env2) (many _)) $ solve env what actual expected (BTrue) raw)
  env2)

(def-fns _ $ (many check-slot : (many (Env) env) (many (Term) ty) -> (many (Env) r))
  (let-match many (unify-solve env ty slot-term) (UContra _) ((UOk env2) env2))
  (env-error env $ str-cat "expected a `(Slot)` or `_`, got " $ qshow env ty))

(def-fns _ $ (many check : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) -> (many (Env) r))
  (check-raw env what actual expected $ None _))

(def-fns _ $ (many check-sg-about : (many (Env) env) (many (Sg) sg) (many (Res) r) (many (Maybe $ Syn) raw) (many (Fn msg-lvl -> (many (String) p) (many (List $ Pair (Loc) $ String) n)) about) -> (many (Env) e))
  (let ((many env2) (many _)) $ match many sg (((Env) _) ((Bool) _))
    ((SgTy ty) (solve-about env "type" (res-ty r) ty (BTrue) raw about))
    ((SgIs t ty)
      (let ((many env3) (many _)) $ solve-about env "value" (res-term r) t (BTrue) (None _) about)
      (solve-about env3 "type" (res-ty r) ty (BTrue) (None _) about)))
  env2)

(def-fns _ $ (many check-sg : (many (Env) env) (many (Sg) sg) (many (Res) r) (many (Maybe $ Syn) raw) -> (many (Env) e))
  (check-sg-about env sg r raw no-about))

(def-fns _ $ (many count-error : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r))
  (env-error env $ str-cat3 "expected " (nat-str expected) $ str-cat3 what ", got " $ nat-str got))

(def-fns _ $ (many raw-strs : (subterm many (List $ Syn) rs) -> (many (List $ String) r))
  (match many rs _ ((Nil _) (Nil _)) ((Cons _ r rest) (Cons _ (show-r r) $ notail $ raw-strs rest))))

(def-fns _ $ (many said-notes : (many (Env) env) (subterm many (List $ Pair (Loc) $ String) ns) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many ns (Cons _ n rest) ((Nil _) (Nil _)))
  (let-match many n (MkPair _ _ l m))
  (Cons _ (MkPair _ _ l $ say env m) $ notail $ said-notes env rest))

(def-fns _ $ (many count-values : (many (Env) env) (many (Maybe $ Sink) sink) (many (Nat) n) (many (Nat) m) -> (many (Env) r))
  (let-match many sink (Some _ k) ((None _) (count-error env " values" n m)))
  (let-match many k (MkSink template noun tele wr placed scope function))
  (let ((many senv)) $ env-set-scope env scope)
  (let ((many owner) (many anchors)) $ match many function (((String) _) ((List $ Pair (Loc) $ String) _))
    ((Some _ f) (values (qshown senv f) $ declared-as senv f))
    ((None _) (values (say senv template) $ said-notes senv placed)))
  (env-error-with env anchors $ str-cat3 owner " expects " $ str-cat3 (counted n noun) ", got " $ str-cat (nat-str m) $ expected-str
    $ match many wr (((String) _)) ((Nil _) (show-tele-t senv tele (BTrue))) (else (join-strs (raw-strs wr) " "))))

(def-fns _ $ (many sink-mults : (many (Sink) k) (many (List $ Multiplicity) ms) -> (many (Sink) r))
  (match many k _ ((MkSink owner noun tele wr anchors scope function) (MkSink owner noun (tele-with-mults tele ms) wr anchors scope function))))

(def-fns _ $ (many branch-sink : (many (Sink) k) (many (Bool) remap) (many (List $ Multiplicity) ms) -> (many (Maybe $ Sink) r))
  (Some _ $ match many remap (((Sink) _)) ((BTrue) (sink-mults k ms)) ((BFalse) k)))


; A boundary (DESIGN.md section 50): a term reaching one with a `_` still open is refused.
(def-fns _ $ (many settle : (many (Env) env) (many (Term) t) -> (many (Env) r))
  (match many (has-meta-env env t) _
    ((BTrue) (env-error-hinted env (Nil _) (cannot-infer env t) $ hole-hints env t))
    ((BFalse) env)))

(def-fns _ $ (many settle-res : (many (Env) env) (many (Res) r) -> (many (Env) e))
  (match many (has-meta-env env $ res-term r) _
    ((BTrue) (settle env $ res-term r))
    ((BFalse) (settle env $ res-ty r))))

(def-fns _ $ (many settle-list : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Env) r))
  (match many ts _
    ((Nil _) env)
    ((Cons _ t rest) (tail $ settle-list rest $ settle env t))))

(def-fns _ $ (many metaless-ress : (subterm many (List $ Res) rs) (many (Env) env) -> (many (List $ Res) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (MkRes (metaless env $ res-term r) (metaless env $ res-ty r) (res-erasure r) $ res-place r) $ notail $ metaless-ress rest env))))

(def-fns _ $ (many metaless-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many e (MkEntry n s m sg place site))
  (let ((many g)) $ match many sg (((Sg) _)) ((SgTy t) (SgTy $ metaless env t)) ((SgIs t ty) (SgIs (metaless env t) $ metaless env ty)))
  (let ((many p)) $ match many place (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ t) (Some _ $ metaless env t)))
  (Cons _ (MkEntry n s m g p site) $ notail $ metaless-tele rest env))

(def-fns _ $ (many settle-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (Env) r))
  (match many es _
    ((Nil _) env)
    ((Cons _ e rest) (tail $ settle-tele rest $ settle env $ sg-term $ entry-sg e))))

(def-fns _ $ (many check-result-place : (many (Env) env) (many (Entry) e) (many (List $ Term) ids) (many (Res) r) -> (many (Env) out))
  (let-match many (match many (res-term r) (((Bool) _)) ((TErr _) (BTrue)) (else (BFalse))) (BFalse) ((BTrue) env))
  (let-match many (entry-place e) (Some _ p) ((None _) env))
  (let ((many p2)) $ instantiate ids p)
  (let ((many ok)) $ match many (res-place r) (((Bool) _)) ((None _) (BFalse)) ((Some _ q) (equal-env env p2 q)))
  (def-fns msg-lvl $ (many msg-at : -> (many (String) s)) (str-cat (say env "return does not satisfy `at` ") $ qshow env p2))
  (error-unless-msg env ok msg-at))

; A result that is not a variable is bound to an anonymous one for the entries after it, so that a later
; entry's `at` can name the slot it sits in (DESIGN.md section 15).
(def-fns _ $ (many result-term : (many (Env) env) (many (Res) r) -> (many (Env) r2) (many (Term) t))
  (let-match many (res-term r) (TVar _) (else (values env $ res-term r)))
  (let-match many (res-place r) (Some _ p) ((None _) (values env $ res-term r)))
  (let ((many env2) (many y)) $ bind-as env (BFalse) (BTrue) (None _) (None _) (BFalse) (res-erasure r) (res-ty r) (Some _ $ res-term r) delegate-id)
  (values (env-place-at env2 y p) $ TVar y))

(def-fns _ $ (many next-site : (many (Env) env) (many (List $ Pair (Spot) $ Maybe $ Syn) sites) -> (many (Env) r) (many (Maybe $ Syn) raw) (many (List $ Pair (Spot) $ Maybe $ Syn) more))
  (let-match many sites (Cons _ site ps) ((Nil _) (values env (None _) sites)))
  (let-match many site (MkPair _ _ pos w))
  (values (env-at env pos) w ps))

; Results against a return telescope; [ids] as in open-tele. Each result is checked at [sites], where it is
; written.
(def-fns _ $ (many check-results : (subterm many (List $ Entry) tele) (many (Env) env) (many (List $ Res) ress) (many (List $ Term) ids) (many (List $ Pair (Spot) $ Maybe $ Syn) sites) -> (many (Env) r))
  (let-match many tele (Cons _ e rest)
    ((Nil _) (match many ress _ ((Nil _) env) ((Cons _ _ _) (env-error env "expected fewer values")))))
  (let-match many ress (Cons _ r rrest) ((Nil _) (env-error env "expected more values")))
  (let ((many (Env) at-site) (many (Maybe $ Syn) raw) (many (List $ Pair (Spot) $ Maybe $ Syn) more)) $ next-site env sites)
  (let ((many env2)) $ env-back env $ check-result-place (settle-res (check-sg at-site (sg-inst ids $ entry-sg e) r raw) r) e ids r)
  (let ((many env3) (many t)) $ result-term env2 r)
  (tail $ check-results rest env3 rrest (Cons _ t ids) more))

(def-fns _ $ (many written-sites : (subterm many (List $ Syn) rs) -> (many (List $ Pair (Spot) $ Maybe $ Syn) r))
  (match many rs _ ((Nil _) (Nil _)) ((Cons _ r rest) (Cons _ (MkPair _ _ (raw-pos r) $ Some _ r) $ notail $ written-sites rest))))

; Where each of a body's [n] results is written: the entries of a final values form holding one per result,
; else the final expression (lib/elab.ml's result_sites).
(def-fns _ $ (many result-sites : (many (Env) env) (many (List $ Syn) body) (many (Nat) n) -> (many (List $ Pair (Spot) $ Maybe $ Syn) r))
  (let-match many (list-rev _ body) (Cons _ final _)
    ((Nil _) (match many (env-loc env) _ ((MkLoc _ here) (list-replicate _ n $ MkPair _ _ here $ None _)))))
  (let ((many whole)) $ list-replicate _ n $ MkPair _ _ (raw-pos final) $ match many (nat-eq n 1) (((Maybe $ Syn) _)) ((BTrue) (Some _ final)) ((BFalse) (None _)))
  (let-match many final (RList _ items) (else whole))
  (let-match many items (Cons _ v entries)
    ((Nil _) whole))
  (match many (and (is-special env v $ SpExpr $ ExValues) $ nat-eq (list-length _ entries) n) _ ((BTrue) (written-sites entries)) ((BFalse) whole)))

(def-fns _ $ (many check-results-count : (many (Env) env) (many (List $ Syn) body) (many (List $ Entry) tele) (many (List $ Res) ress) (many (List $ Term) ids) -> (many (Env) r))
  (let ((many n)) $ list-length _ tele)
  (let ((many m)) $ list-length _ ress)
  (match many (nat-cmp n m) _
    ((CEq _ _ _) (check-results tele env ress ids $ result-sites env body n))
    (else (count-error env " values" n m))))

; prove-subterm (section 18): the first, canonicalized, is a strict subtree of the second through constructor
; applications only.
(def-fns _ $ (many provable-subterm : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Bool) r))
  (is-strict-subterm (canon-env env b) $ canon-env env a))

(def-fns _ $ (many mint-subterm : (many (Env) env) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty) -> (many (Env) r) (many (Res) res))
  (def-fns msg-lvl $ (many msg-subterm : -> (many (String) s)) (str-cat3 (qshow env a) " is not a strict subterm of " $ qshow env b))
  (let ((many env2)) $ error-unless-msg env (provable-subterm env a b) msg-subterm)
  (mint env2 $ proof-type subterm-id $ Cons _ aty $ Cons _ a $ Cons _ bty $ Cons _ b $ Nil _))

(def-fns _ $ (many provable-predates : (many (Env) env) (many (Nat) x) (many (Nat) lvl) -> (many (Bool) r))
  (let-match many (entry-introduced env x) (Some _ ix) ((None _) (BFalse)))
  (let-match many (entry-introduced env lvl) (Some _ il) ((None _) (BFalse)))
  (and (entry-minted env lvl) $ nat-lt ix il))

; prove-predates (section 18): the variable was in scope when the level was minted, both read by their
; binders and never canonicalized (ASSUMPTIONS 13); a literal has no introduction order (section 45).
(def-fns _ $ (many mint-predates : (many (Env) env) (many (Nat) x) (many (Nat) lvl) -> (many (Env) r) (many (Res) res))
  (def-fns msg-lvl $ (many who : (many (Nat) y) -> (many (String) s)) (match many (env-entry-name env y) (((String) _)) ((None _) (qshow env $ TVar y)) ((Some _ _) (qshown env y))))
  (let ((many env2)) $ match many (entry-minted env lvl) (((Env) _)) ((BTrue) env) ((BFalse) (env-error env $ str-cat (who lvl) (say env " is not a level minted by `def-lvl`"))))
  (let ((many env3)) $ match many (is-literal env x) (((Env) _)) ((BTrue) (env-error env2 $ str-cat3 (qshown env2 x) (match many (lit-spelling (env-lits env2) x) _ ((Some _ _) " is a literal") ((None _) " is a constant a macro minted")) ", which has no introduction order")) ((BFalse) env2))
  (let ((many env4)) $ match many (or (provable-predates env x lvl) $ or (is-literal env x) $ not $ entry-minted env lvl) (((Env) _)) ((BTrue) env3) ((BFalse) (env-error env3 $ str-cat3 (who x) " was not in scope when level " $ str-cat (who lvl) " was minted")))
  (mint env4 $ proof-type predates-id $ Cons _ (type-of env4 x) $ Cons _ (TVar x) $ Cons _ (TVar lvl) $ Nil _))

; The arguments of a proof of the given kind, with an error where the term is not one.
(def-fns _ $ (many proof-args : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Maybe $ List $ Term) r))
  (let-match many (canon-env env $ res-ty p) (TApp h args) (else (None $ List $ Term)))
  (let-match many h (TVar c) (else (None $ List $ Term)))
  (match many (nat-cmp c ctor) _ ((CEq _ _ _) (Some _ args)) (else (None _))))

(def-fns _ $ (many not-a-proof : (many (Env) env) (many (Nat) ctor) (many (String) alt) (many (Res) p) -> (many (Env) r))
  (env-error env $ str-cat3 "expected a " (qshown env ctor) $ str-cat3 " proof" alt $ str-cat3 ", got " (qshow env $ res-term p) $ str-cat " : " $ qshow env $ res-ty p))

(def-fns _ $ (many proof-errs : (subterm many (Nat) n) -> (many (List $ Term) ts))
  (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ (TErr "proof") $ notail $ proof-errs k))))

; The three arguments of a Predates proof, or the four of a Subterm or Coercible proof (section 18).
(def-fns _ $ (many proof-terms : (many (Env) env) (many (Nat) ctor) (many (String) alt) (many (Res) p) (many (Nat) n) -> (many (Env) r) (many (List $ Term) args))
  (let ((many (Maybe $ List $ Term) args))
    (match many (proof-args env ctor p) _
      ((None _) (None _))
      ((Some _ ts) (match many (nat-cmp (list-length _ ts) n) (((Maybe $ List $ Term) _)) ((CEq _ _ _) (Some _ ts)) (else (None _))))))
  (match many args _
    ((None _) (values (not-a-proof env ctor alt p) $ proof-errs n))
    ((Some _ ts) (values env ts))))

(def-fns _ $ (many expect-proof3 : (many (Env) env) (many (Nat) ctor) (many (String) alt) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2))
  (let ((many env2) (many args)) $ proof-terms env ctor alt p 3)
  (values env2 (nth-term args 0) (nth-term args 1) $ nth-term args 2))

(def-fns _ $ (many expect-proof4 : (many (Env) env) (many (Nat) ctor) (many (String) alt) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3))
  (let ((many env2) (many args)) $ proof-terms env ctor alt p 4)
  (values env2 (nth-term args 0) (nth-term args 1) (nth-term args 2) $ nth-term args 3))

(def-fns _ $ (many expect-proof6 : (many (Env) env) (many (Nat) ctor) (many (String) alt) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3) (many (Term) t4) (many (Term) t5))
  (let ((many env2) (many args)) $ proof-terms env ctor alt p 6)
  (values env2 (nth-term args 0) (nth-term args 1) (nth-term args 2) (nth-term args 3) (nth-term args 4) $ nth-term args 5))

(def-fns _ $ (many expected-proof-type : (many (Env) env) (many (Maybe $ List $ Entry) tele) -> (many (Maybe $ Term) r))
  (let-match many tele (Some _ es) ((None _) (None _)))
  (let-match many es (Cons _ e rest) ((Nil _) (None _)))
  (match many rest _
    ((Cons _ _ _) (None _))
    ((Nil _)
      (Some _ $ canon-env env $ sg-ty $ entry-sg e))))

(def-fns _ $ (many expected-coercible-sides : (many (Env) env) (many (Maybe $ List $ Entry) tele) -> (many (Maybe $ Pair (Term) $ Term) r))
  (let-match many (expected-proof-type env tele) (Some _ ty) ((None _) (None _)))
  (let-match many ty (TApp h args) (else (None $ Pair (Term) $ Term)))
  (match many (and (term-eq h $ TVar coercible-id) $ nat-eq (list-length _ args) 6) _
    ((BTrue) (Some _ $ MkPair _ _ (nth-term args 0) $ nth-term args 3))
    ((BFalse) (None _))))

(def-fns _ $ (many coercible-mint : (many (Env) env) (many (Maybe $ List $ Entry) tele) (many (Term) ty) -> (many (Env) e) (many (Res) r))
  (let ((many env2)) $ match many (expected-proof-type env tele) (((Env) _)) ((None _) env) ((Some _ want) (check env "type" ty want)))
  (mint env2 $ metaless env2 ty))

(def-fns _ $ (many sharing-mult : (many (Env) env) (many (Term) side) -> (many (Env) e) (many (Multiplicity) m))
  (let ((many t)) $ canon-env env side)
  (let-match many (term-eq t unique-term) (BFalse) ((BTrue) (values env $ Once)))
  (match many (term-eq t shared-term) _
    ((BTrue) (values env $ Many))
    ((BFalse) (values (env-error env "expected `(Unique)` or `(Shared)`") $ Many))))

(def-fns _ $ (many sharing-of-fn : (many (Env) env) (many (Term) ty) -> (many (Term) r))
  (let-match many (canon-env env ty) (TFn unique2 _ _ _)
    (else shared-term))
  (match many unique2 _ ((BTrue) unique-term) ((BFalse) shared-term)))

(def-fns _ $ (many wrap-sharing : (subterm many (List $ Entry) tele) (many (Term) side) -> (many (Term) r))
  (let-match many tele (Cons _ e rest)
    ((Nil _) shared-term))
  (match many (entry-mult e) _ ((Erased) (tail $ wrap-sharing rest side)) ((Many) shared-term) ((Once) side)))

(def-fns _ $ (many coercible-code : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Multiplicity) src) (many (Code ctx (Cons (Multiplicity) src (Nil (Multiplicity)))) code) -> (many (Code ctx expect) r))
  (match many (mults-same (Cons _ src $ Nil _) expect) _
    ((Some _ same) (recast _ expect (Cons _ src $ Nil _) same code))
    ((None _) (CErased _ expect))))

(def-fns _ $ (many coercible-proof-tele : (many (Env) env) (many (Nat) ctor) (many (Maybe $ Pair (Term) $ Term) sides) -> (many (Env) e) (many (Maybe $ List $ Entry) tele))
  (let-match many sides (Some _ p) ((None _) (values env $ None _)))
  (let-match many p (MkPair _ _ sa sb))
  (let ((many env1) (many ta)) $ bind-as env (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) type-term (None _) delegate-id)
  (let ((many env2) (many va)) $ bind-as env1 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TVar ta) (None _) delegate-id)
  (let ((many env3) (many tb)) $ bind-as env2 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) type-term (None _) delegate-id)
  (let ((many env4) (many vb)) $ bind-as env3 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TVar tb) (None _) delegate-id)
  (let ((many ty)) $ proof-type ctor $ Cons _ sa $ Cons _ (TVar ta) $ Cons _ (TVar va) $ Cons _ sb $ Cons _ (TVar tb) $ Cons _ (TVar vb) $ Nil _)
  (values env4 $ Some _ $ Cons _ (MkEntry (None _) (BFalse) (Erased) (SgTy ty) (None _) $ None _) $ Nil _))

(def-fns _ $ (many trans-proofs : (many (Env) env) (many (Nat) ctor) (many (Nat) n) (many (Res) p) (many (Res) q) -> (many (Env) r) (many (Res) res))
  (let ((many env2) (many pa)) $ proof-terms env ctor "" p n)
  (let ((many env3) (many qa)) $ proof-terms env2 ctor "" q n)
  (let ((many env4)) $ check env3 "value" (nth-term qa 1) $ nth-term pa $ nat-pred n)
  (mint env4 $ proof-type ctor $ Cons _ (nth-term pa 0) $ Cons _ (nth-term pa 1) $ list-drop _ 2 qa))


(def-fns _ $ (many drop-prefix : (subterm many (String) p) (many (String) s) -> (many (Maybe $ String) r))
  (let-match many p (SCons c prest) ((SNil) (Some _ s)))
  (let-match many s (SCons d srest) ((SNil) (None _)))
  (match many (char-is d $ char-code c) _ ((BTrue) (tail $ drop-prefix prest srest)) ((BFalse) (None _))))

(def-fns _ $ (many help-lines-in : (subterm many (List $ String) ls) (many (String) prefix) -> (many (List $ String) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) (notail $ help-lines-in rest prefix))
  (match many (drop-prefix prefix l) _ ((Some _ t) (Cons _ t more)) ((None _) more)))

(def-fns _ $ (many help-lines : (many (Env) env) (many (String) kind) (many (String) key) -> (many (List $ String) r))
  (help-lines-in (env-help env) (str-cat3 kind " " $ str-cat key ": ")))

(def-fns _ $ (many hint-lines : (many (String) prefix) (subterm many (List $ String) ts) -> (many (String) r))
  (let-match many ts (Cons _ t rest) ((Nil _) ""))
  (str-cat3 "\nhint: " prefix $ str-cat t $ notail $ hint-lines prefix rest))

(def-fns _ $ (many sp-hints : (many (Env) env) (many (String) key) -> (many (String) r))
  (say-code env $ hint-lines "usage: " $ help-lines env "usage" key))

(def-fns _ $ (many sp-misuse : (many (Env) env) (many (Sp) sp) -> (many (String) r))
  (let ((many n)) (sp-name sp))
  (str-cat3 "malformed " (tick $ spell env n) $ str-cat " form" $ sp-hints env n))

(def-fns _ $ (many message-name : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Syn) r))
  (let-match many raw (RList _ items) (else (Some _ raw)))
  (let-match many items (Cons _ h rest) ((Nil _) (None _)))
  (let-match many rest (Cons _ a more) ((Nil _) (None _)))
  (let-match many a (RAtom _ _) (else (None $ Syn)))
  (match many (and (is-special env h $ SpExpr $ ExShare) $ list-is-empty _ more) _ ((BTrue) (Some _ a)) ((BFalse) (None _))))

(def-fns _ $ (many message-of : (many (Env) env) (many (Nat) x) (many (Multiplicity) m0) (many (Term) str-ty) -> (many (Maybe $ String) why) (many (String) text))
  (let-match many (mult-is-many m0) (BTrue) ((BFalse) (values (Some _ "is erased") "")))
  (let ((erased _) (many st)) $ entry-state env x)
  (let-match many st (SSettled _ _ m) ((SHypothetical _) (values (Some _ "is `Hypothetical`") "")))
  (let ((many t)) $ minted-type env m)
  (let-match many (term-eq t str-ty) (BTrue) ((BFalse) (values (Some _ $ str-cat3 "has type " (qshow env t) ", not the prelude's `String`") "")))
  (let ((erased _) (many blk)) $ env-block env x)
  (let-match many blk (Some _ b) ((None _) (values (Some _ "is `Hypothetical`") "")))
  (let-match many b (BExt _ p) (else (values (Some _ "is `Hypothetical`") "")))
  (match many p _ ((PStr s) (values (None _) s)) ((PBytes s) (values (None _) s)) (else (values (Some _ "is `Hypothetical`") ""))))

(def-fns _ $ (many form-in-type : (many (Env) env) (many (Syn) raw) -> (many (Env) r))
  (error-at env (raw-pos raw) "no function is called while a type is elaborated, so a head in a type cannot be a form (section 9)"))

(def-fns _ $ (many compile-say : (many (Env) env) (many (Sp) sp) (many (List $ Syn) args) (many (Multiplicity) pos) -> (many (Env) r))
  (let ((many what)) $ tick $ spell env $ sp-name sp)
  (let-match many args (Cons _ raw more) ((Nil _) (env-error env $ sp-misuse env sp)))
  (let-match many more (Nil _) ((Cons _ _ _) (env-error env $ sp-misuse env sp)))
  (let-match many (message-name env raw) (Some _ nraw) ((None _) (error-at env (raw-pos raw) $ str-cat (qraw raw) " is not a name")))
  (let ((many env1a) (many x)) $ var-of-raw (env-at env $ raw-pos nraw) nraw "a name")
  (let ((many env1)) $ env-back env env1a)
  (let-match many (prelude-missing env1 what "String") (None _) ((Some _ msg) (env-error env1 msg)))
  (let ((many env2) (many str-ty)) $ prelude-type env1 "String")
  (let ((many why) (many text)) $ message-of env2 x (made env2 nraw x) str-ty)
  (let-match many why (None _)
    ((Some _ w) (error-at env2 (raw-pos raw) $ str-cat3 (say env2 "the message of ") what $ str-cat3 (say env2 " must be a `Settled`, non-erased `String`; ") (qname env2 x) $ str-cat " " w)))
  (let ((many env3)) $ env-back env2 $ read-special (env-at env2 $ raw-pos raw) raw (BFalse) pos)
  (match many (sp-eq sp $ SpStmt $ StCompileWarn) _ ((BTrue) (env-warn-at env3 (env-loc env) text)) ((BFalse) (env-error env3 text))))

(def-fns _ $ (many misplaced : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Sp) r))
  (let-match many (raw-items raw) (Cons _ h _) ((Nil _) (None _)))
  (let-match many (special-of env h) (Some _ sp) ((None _) (None _)))
  (match many (help-lines env "role" $ sp-name sp) _ ((Nil _) (None _)) ((Cons _ _ _) (Some _ sp))))

(def-fns _ $ (many brief : (many (Syn) raw) -> (many (String) s))
  (let-match many raw (RList _ items) (else (qraw raw)))
  (let-match many items (Cons _ h args) ((Nil _) (tick "()")))
  (let-match many h (RAtom _ n) (else "this form"))
  (tick $ str-cat3 "(" (spell-name n) $ match many args (((String) _)) ((Nil _) ")") (else " ...)")))

(def-adts $ (Expansion : -> Type)
  enum
  (many Spliced : (many (List $ Syn) out) -> (Expansion))
  (many Refused : (many (String) msg) -> (Expansion)))

(def-fns _ $ (many head-entry : (many (Env) env) (many (Syn) head) -> (many (Maybe $ Nat) r))
  (let ((many (Maybe $ Name) name))
    (match many head _
      ((RAtom _ n) (Some _ n))
      ((RList _ items)
        (let-match many items (Cons _ h more) ((Nil _) (None _)))
        (let-match many more (Cons _ a none) ((Nil _) (None _)))
        (let-match many none (Nil _) ((Cons _ _ _) (None _)))
        (let-match many (special-of env h) (Some _ sp) ((None _) (None _)))
        (let-match many (sp-eq sp $ SpExpr $ ExShare) (BTrue) ((BFalse) (None _)))
        (raw-atom a))
      (else (None _))))
  (let-match many name (Some _ n) ((None _) (None _)))
  (let-match many n (NHandle _ _ m _) (else (lookup env n)))
  (match many (mult-is-many m) _ ((BTrue) (lookup env n)) ((BFalse) (None _))))

(def-fns _ $ (many macro-entry : (many (Env) env) (many (Syn) head) -> (many (Maybe $ Nat) r))
  (let-match many (head-entry env head) (Some _ x) ((None _) (None _)))
  (let-match many (mult-is-many $ entry-mult-of env x) (BTrue) ((BFalse) (None _)))
  (let ((erased _) (many s)) $ entry-state env x)
  (let-match many s (SSettled _ _ m) ((SHypothetical _) (None _)))
  (let ((erased _) (many blk)) $ env-block env x)
  (let-match many blk (Some _ b) ((None _) (None _)))
  (let-match many b (BFn _ _ _ _) (else (None _)))
  (let-match many (and (not $ is-literal env m) $ trusted-former env m) (BFalse) ((BTrue) (None _)))
  (let-match many (lookup (env-set-scope env $ env-prelude env) $ NSrc "Macro") (Some _ mt) ((None _) (None _)))
  (match many (term-eq (minted-type env m) $ TApp (TVar mt) $ Nil _) _
    ((BTrue) (Some _ x))
    ((BFalse) (None _))))

(def-fns _ $ (many raw-ext-of : (many (Env) env) -> (many (Maybe $ ExtType) r))
  (let-match many (lookup (env-set-scope env $ env-prelude env) $ NSrc "RawSymbol") (Some _ x) ((None _) (None _)))
  (let-match many (ctor-of env x) (Some _ c) ((None _) (None _)))
  (let-match many c (MkCtor _ _ _ _ _ ext _ _))
  ext)

(def-fns _ $ (many expand : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) raw) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Expansion) x))
  (let-match many raw (RList p items) (else (values ew env $ None _)))
  (let-match many items (Cons _ head args) ((Nil _) (values ew env $ None _)))
  (let-match many (macro-entry env head) (Some _ m) ((None _) (values ew env $ None _)))
  (let ((many n)) $ env-expansions env)
  (let-match many (nat-lt n expansion-limit) (BTrue) ((BFalse) (values ew env $ Some _ $ Refused "more than 10000 macro expansions")))
  (let-match many (raw-ext-of env) (Some _ ext) ((None _) (values ew env $ Some _ $ Refused "the prelude's `Raw` is not the FFI's")))
  (let-match many (env-loc env) (MkLoc file _))
  (let ((many envr)) $ env-back env $ read-special (env-at env $ raw-pos head) head (BFalse) (Many))
  (let ((unique ew1) (many env2) (many out)) $ env-expand ew (env-set-expansions envr $ Succ n) m ext file p args)
  (match many out _
    ((Ok _ xs) (values ew1 env2 $ Some _ $ Spliced xs))
    ((Fail _ msg) (values ew1 env2 $ Some _ $ Refused $ str-cat3 "macro " (qraw head) $ str-cat " failed: " msg))))

(def-fns _ $ (many handle-raw : (many (Env) env) (many (Spot) pos) (many (Nat) x) -> (many (Syn) r))
  (RAtom pos $ NHandle x (MintedIs) (entry-mult-of env x) (entry-name-or-id env x)))

(def-fns _ $ (many named-share : (many (Env) env) (many (Syn) raw) -> (many (Bool) r))
  (let-match many raw (RList _ items) (else (BFalse)))
  (let-match many items (Cons _ h rest) ((Nil _) (BFalse)))
  (let-match many rest (Cons _ a more) ((Nil _) (BFalse)))
  (let-match many a (RAtom _ _) (else (BFalse)))
  (and (list-is-empty _ more) $ is-special env h $ SpExpr $ ExShare))

(def-fns _ $ (many settled-dispatch : (many (Env) env) (many (Syn) h) -> (many (Bool) r))
  (or (is-some _ $ special-of env h) (is-some _ $ macro-entry env h)))

(def-fns _ $ (many expand-one : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) raw) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Result $ Syn) x))
  (let ((unique ew1) (many env2) (many x)) $ expand ew env raw)
  (let-match many x (Some _ ex) ((None _) (values ew1 env2 $ None _)))
  (let-match many ex (Spliced out) ((Refused m) (values ew1 env2 $ Some _ $ Fail _ m)))
  (let ((many (String) bad)) $ str-cat3 (brief raw) " must expand to one form here, and expanded to " $ nat-str $ list-length _ out)
  (let-match many out (Cons _ r more) ((Nil _) (values ew1 env2 $ Some _ $ Fail _ bad)))
  (match many more _ ((Nil _) (values ew1 env2 $ Some _ $ Ok _ r)) ((Cons _ _ _) (values ew1 env2 $ Some _ $ Fail _ bad))))

(def-fns _ $ (many splice-go : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (many (Env) env) (subterm many (List $ Syn) items) (many (Bool) changed) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Bool) ch) (many (List $ Syn) out) (many (Maybe $ Pair (Syn) (String)) err))
  (let-match many items (Cons _ item rest) ((Nil _) (values ew env changed (Nil _) $ None _)))
  (let ((unique ew1) (many env2) (many x)) $ expand ew env item)
  (let-match many x (Some _ ex)
    ((None _)
      (let ((unique ew2) (many env3) (many ch) (many out) (many err)) $ notail $ splice-go ew1 fuel env2 rest changed)
      (values ew2 env3 ch (Cons _ item out) err)))
  (let-match many ex (Spliced out) ((Refused m) (values ew1 env2 (BTrue) (Nil _) $ Some _ $ MkPair _ _ item m)))
  (let-match many fuel (Succ f2) ((Zero) (values ew1 env2 (BTrue) (Nil _) $ Some _ $ MkPair _ _ item "more than 10000 macro expansions")))
  (let ((many all) (erased _)) $ list-append _ out rest)
  (tail $ splice-go ew1 f2 env2 all $ BTrue))

(def-fns _ $ (many splice : (unique (ElabWorld) ew) (many (Env) env) (many (List $ Syn) items) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Bool) ch) (many (List $ Syn) out) (many (Maybe $ Pair (Syn) (String)) err))
  (splice-go ew expansion-limit env items $ BFalse))

(def-fns _ $ (many splice-items-of : (unique (ElabWorld) ew) (many (Env) env) (subterm many (List $ Syn) entries) (many (Bool) changed) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Bool) ch) (many (List $ Syn) out) (many (Maybe $ Pair (Syn) (String)) err))
  (let-match many entries (Cons _ e rest) ((Nil _) (values ew env changed (Nil _) $ None _)))
  (let ((unique ew1) (many env2) (many ch2) (many e2) (many err2))
    (match many e (((ElabWorld) _ at ew) ((Env) a) ((Bool) b) ((Syn) c) ((Maybe $ Pair (Syn) (String)) d))
      ((RList p items) (let ((unique ew2) (many env3) (many c) (many out) (many er)) $ splice ew env items) (values ew2 env3 c (RList p out) er))
      (else (values ew env (BFalse) e $ None _))))
  (let-match many err2 (None _) ((Some _ x) (values ew1 env2 (BTrue) (Nil _) $ Some _ x)))
  (let ((unique ew3) (many env4) (many ch3) (many out) (many err)) $ notail $ splice-items-of ew1 env2 rest $ or changed ch2)
  (values ew3 env4 ch3 (Cons _ e2 out) err))

(def-fns _ $ (many splice-entries : (unique (ElabWorld) ew) (many (Env) env) (many (List $ Syn) entries) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Bool) ch) (many (List $ Syn) out) (many (Maybe $ Pair (Syn) (String)) err))
  (let ((unique ew1) (many env2) (many ch) (many out) (many err)) $ splice ew env entries)
  (let-match many err (None _) ((Some _ _) (values ew1 env2 ch out err)))
  (splice-items-of ew1 env2 out ch))

(def-fns _ $ (many splice-tail : (unique (ElabWorld) ew) (many (Env) env) (subterm many (Nat) k) (many (List $ Syn) items) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Result $ List $ Syn) x))
  (let-match many k (Succ k2)
    ((Zero)
      (let ((unique ew1) (many env2) (many changed) (many out) (many err)) $ splice ew env items)
      (let-match many changed (BTrue) ((BFalse) (values ew1 env2 $ None _)))
      (let-match many err (None _) ((Some _ e) (match many e _ ((MkPair _ _ item m) (values ew1 (env-at env2 $ raw-pos item) $ Some _ $ Fail _ m)))))
      (values ew1 env2 $ Some _ $ Ok _ out)))
  (let-match many items (Cons _ x rest) ((Nil _) (values ew env $ None _)))
  (let ((unique ew2) (many env2) (many r)) $ notail $ splice-tail ew env k2 rest)
  (let-match many r (Some _ rr) ((None _) (values ew2 env2 $ None _)))
  (match many rr _ ((Fail _ m) (values ew2 env2 $ Some _ $ Fail _ m)) ((Ok _ out) (values ew2 env2 $ Some _ $ Ok _ $ Cons _ x out))))

(def-fns _ $ (many splice-call : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) raw) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Result $ Syn) x))
  (let-match many raw (RList p items) (else (values ew env $ None _)))
  (let-match many items (Cons _ head _) ((Nil _) (values ew env $ None _)))
  (let-match many (match many (special-of env head) (((Bool) _)) ((None _) (BTrue)) ((Some _ sp) (sp-eq sp $ SpExpr $ ExValues))) (BTrue) ((BFalse) (values ew env $ None _)))
  (let ((unique ew1) (many env2) (many r)) $ splice-tail ew env 1 items)
  (let-match many r (Some _ rr) ((None _) (values ew1 env2 $ None _)))
  (match many rr _ ((Fail _ m) (values ew1 env2 $ Some _ $ Fail _ m)) ((Ok _ out) (values ew1 env2 $ Some _ $ Ok _ $ RList p out))))

(def-fns _ $ (many splice-binders : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) head) (many (List $ Syn) args) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Result $ List $ Syn) x))
  (let-match many args (Cons _ bk rhs) ((Nil _) (values ew env $ None _)))
  (let-match many bk (RList bp bs) (else (values ew env $ None _)))
  (let ((unique ew1) (many e0) (many changed) (many out) (many err)) $ splice-entries ew (env-set-usage-erased env $ BTrue) bs)
  (let ((many e2)) $ env-set-usage-erased e0 $ env-usage-erased env)
  (let-match many changed (BTrue) ((BFalse) (values ew1 e2 $ None _)))
  (let-match many err (None _) ((Some _ e) (match many e _ ((MkPair _ _ item m) (values ew1 (env-at e2 $ raw-pos item) $ Some _ $ Fail _ m)))))
  (values ew1 e2 $ Some _ $ Ok _ $ Cons _ head $ Cons _ (RList bp out) rhs))

(def-fns _ $ (many body-head : (unique (ElabWorld) ew) (many (Env) env) (many (Syn) item) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Expansion) x))
  (let ((unique ew1) (many env2) (many x)) $ expand ew env item)
  (let-match many x (None _) ((Some _ _) (values ew1 env2 x)))
  (let-match many item (RList p items) (else (values ew1 env2 $ None _)))
  (let-match many items (Cons _ h _) ((Nil _) (values ew1 env2 $ None _)))
  (let-match many (is-special env2 h $ SpStmt $ StLetMatch) (BTrue) ((BFalse) (values ew1 env2 $ None _)))
  (let ((unique ew2) (many env3) (many r)) $ splice-tail ew1 env2 4 items)
  (let-match many r (Some _ rr) ((None _) (values ew2 env3 $ None _)))
  (match many rr _ ((Fail _ m) (values ew2 env3 $ Some _ $ Refused m)) ((Ok _ out) (values ew2 env3 $ Some _ $ Spliced $ Cons _ (RList p out) $ Nil _))))

(def-fns _ $ (many sub-syns : (erased (List $ Syn) root) (subterm many (List $ Sub root) xs) -> (many (List $ Syn) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let-match many x (MkSub _ r _))
  (Cons _ r $ notail $ sub-syns _ rest))

(def-fns _ $ (many not-a : (many (Env) env) (many (String) what) (many (Syn) raw) -> (many (String) r))
  (str-cat3 (brief raw) " is " $ str-cat what $ match many (misplaced env raw) (((String) _))
    ((Some _ sp) (let ((many n)) (sp-name sp)) (str-cat (say env $ hint-lines (str-cat (tick n) " ") $ help-lines env "role" n) $ sp-hints env n))
    ((None _) "")))

(def-fns _ $ (many not-a-statement : (many (Env) env) (many (String) within) (many (Syn) raw) -> (many (String) r))
  (not-a env (match many (misplaced env raw) (((String) _)) ((Some _ _) "not a statement") ((None _) (str-cat3 "not a statement\nhint: every " (say env within) " but the last must be a statement"))) raw))

(def-fns _ $ (many bracket-parts : (subterm many (List $ Syn) args) (many (Env) env) (many (Sp) sp) ->
    (many (Env) r) (many (List $ Sub args) entries) (many (List $ Syn) after) (erased (Within after args) wa))
  (let-match many args (Cons _ braw after) ((Nil _) (values (env-error env $ sp-misuse env sp) (Nil _) args (WHere args))))
  (let ((erased wa)) $ within-step after args args (prove-subterm after args) (WHere args))
  (let ((many env1) (many entries))
    (match many braw (((Env) _) ((List $ Sub args) es))
      ((RList _ items)
        (values env $ subs-of items _ $ WIn _ _ $ subterm-trans (prove-subterm items braw) (prove-subterm braw args)))
      (else (values (env-error env $ sp-misuse env sp) (Nil _)))))
  (values env1 entries after wa))

(def-lvl misuse-lvl)


(def-fns _ $ (many find-matchable : (many (Env) env) (many (Nat) tid) -> (many (Env) r) (many (Maybe $ MatchInfo) info))
  (values env $ find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env))

(def-fns _ $ (many first-stored : (subterm many (List $ Entry) tele) -> (many (Maybe $ Entry) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (None _)))
  (match many (entry-stored e) _ ((BTrue) (Some _ e)) ((BFalse) (tail $ first-stored rest))))

(def-fns _ $ (many check-ext-shape : (many (Env) env) (many (String) name) (many (Bool) tagged) (many (List $ Nat) ns) (many (List $ Nat) want) -> (many (Env) r))
  (let ((many tagged-want)) $ nat-lt 1 $ list-length _ want)
  (def-fns msg-lvl $ (many msg-shape : -> (many (String) s))
    (let ((many (String) shape)) $ match many tagged-want _ ((BTrue) " has the tagged shape (") ((BFalse) " has the shape ("))
    (let ((many (String) how)) $ match many (and tagged-want $ not tagged) _ ((BTrue) "the untagged (") ((BFalse) "("))
    (str-cat3 "the extern implementation of " (tick name) $ str-cat3 shape (spell-nats want) $ str-cat3 "), its declaration " how $ str-cat (spell-nats ns) ")"))
  (error-unless-msg env (and (or tagged $ nat-lt (list-length _ ns) 2) $ nat-list-eq ns want) msg-shape))

; The constructors an extern function builds its result with, read off its model's return type (section 42):
; the implementation's view and the declaration must agree on the shape, as they must for an extern type.
(def-fns _ $ (many extern-ctors : (many (Env) env) (many (String) name) (many (List $ Entry) rets) (many (List $ Nat) want) -> (many (Env) r) (many (List $ Ctor) cs))
  (let ((many (Maybe $ Nat) head))
    (match many (first-stored rets) _
      ((None _) (None _))
      ((Some _ e)
        (let ((many ty) (many _)) $ fact-of $ entry-sg e)
        (type-head env ty))))
  (let-match many head (Some _ tid)
    ((None _) (values (env-error env $ str-cat3 "the extern implementation of " (tick name) " builds no declared type") (Nil _))))
  (let ((many env2) (many found)) $ find-matchable env tid)
  (let ((many (Maybe $ Adt) got))
    (match many found _
      ((None _) (None _))
      ((Some _ info) (match many info _ ((MkMatchInfo mid _ _ _) (adt-of env2 mid))))))
  (let-match many got (Some _ adt)
    ((None _) (values (env-error env2 $ str-cat3 "the extern implementation of " (tick name) $ str-cat3 " needs " (qshown env2 tid) " declared before it") (Nil _))))
  (let ((many records)) $ adt-ctors adt)
  (let ((many ns)) $ ctor-arities records)
  (values (check-ext-shape env2 name (adt-tagged adt) ns want) records))

; ---- Opening a Matchable or Newtype (section 8, ASSUMPTIONS 139)

; The entries of [os] whose ids are in [ids], in order.
; Opens x (section 8): its constructors must be distinct after canonicalization, and it then merges with
; whatever open names one of them or its type constructor.
(def-fns _ $ (many env-open-adt : (many (Env) env) (many (Nat) x) -> (many (UnifyRes) r))
  (let ((many dup)) $ match many (type-of env x) (((Maybe $ Nat) _)) ((TMatchable _ _ _ _ cs) (nats-dup $ mctor-ids cs)) (else (None _)))
  (match many dup _
    ((Some _ c) (UContra $ CCat (CTerm $ TVar c) $ CText " is listed twice"))
    ((None _) (merge-all $ Forcing $ env-open env x))))

; def-adts opens what it mints; a fresh object relates to nothing open, so the assertion holds.
(def-fns _ $ (many open-minted : (many (Env) env) (many (Nat) x) -> (many (Env) r))
  (match many (env-open-adt env x) _ ((UOk env2) env2) ((UContra m) (env-error env $ str-cat "internal: " $ clash-str env m))))

; Opens an `AtFn` proof (section 39), as a Matchable is opened; naming one function, it seems unable to
; contradict another open, so a contradiction is reported as internal.
(def-fns _ $ (many open-proof : (many (Env) env) (many (Nat) x) -> (many (Env) r))
  (match many (merge-all $ Forcing $ env-open env x) _ ((UOk env2) env2) ((UContra m) (env-error env $ str-cat "internal: " $ clash-str env m))))

; An anonymous let at [mult] of a Matchable or Newtype, elaborated by the caller into [inner]: the entry an
; open records (section 8). Run at once in run position, as a let's right-hand side is.
(def-fns _ $ (many open-bind : (many (List $ List $ Nat) ctx) (many (Env) env) (many (Env) inner) (many (Res) r) (many (Multiplicity) mult) (many (Code ctx (Cons (Multiplicity) mult (Nil (Multiplicity)))) code) ->
    (many (Env) r2) (many (Nat) x) (many (Term) t))
  (let ((many t)) $ res-term r)
  (let ((many inner2)) $ settle-res inner r)
  (let ((many (Env) inner3))
    (match many (canon-env inner2 $ res-ty r) _
      ((TMatchable _ _ _ _ _) inner2)
      (else (env-error inner2 $ str-cat3 (qshow inner2 t) " : " $ str-cat (qshow inner2 $ res-ty r) (say inner2 " is not a `Matchable`")))))
  (let ((many run)) $ env-run-pos env)
  (let ((many env3) (many x)) $ bind (env-hide env inner3) (None _) (Some _ $ env-loc env) (BFalse) mult (res-ty r) (Some _ t) delegate-id)
  (let ((many (Env) env4))
    (match many run _
      ((BFalse) env3)
      ((BTrue)
        (match many mult (((Env) _))
          ((Erased) (env-set-tokens env3 $ Cons _ x $ Nil _))
          (else
            (let-match many ctx (Nil _) ((Cons _ _ _) (env-set-tokens env3 $ Cons _ x $ Nil _)))
            (match many (not $ env-failed inner3) (((Env) _))
              ((BTrue) (env-run-let env3 (Cons _ mult $ Nil _) code $ Cons _ x $ Nil _))
              ((BFalse) (env-set-tokens env3 $ Cons _ x $ Nil _))))))))
  (values (match many t (((Env) _)) ((TVar y) (forward-marks (forward-binder env4 x y mult) x y)) (else env4)) x t))

(def-fns _ $ (many open-contradicts : (many (List $ List $ Nat) ctx) (many (Env) env) (many (Env) inner) (many (Res) r) (many (Code ctx erased-one) code) -> (many (Env) out))
  (let ((many env2) (many x) (many t)) $ open-bind ctx env inner r (Erased) code)
  (let ((erased _) (erased _) (erased obnd) (many otb)) $ env-table env2)
  (let ((many kind) (many _)) $ open-names _ _ obnd otb x)
  (let-match many kind (OKMatchable) ((OKNone) env2) ((OKAtFn) env2))
  (match many (env-open-adt env2 x) _
    ((UOk _) (env-error env2 $ str-cat3 (say env2 "`open-absurd`: opening ") (qshow env2 t) " contradicts nothing"))
    ((UContra _) env2)))

(def-fns _ $ (many mint-level : (many (Env) env) (many (Maybe $ Name) name) (many (Maybe $ Loc) site) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind-erased env name site (BTrue) (Erased) level-term (None _) delegate-id)
  (values (mark-minted env2 x) x))

; Entering a branch forces the scrutinee equal to the constructor over its fields, and its type to the
; constructor's return (section 7).
(def-fns _ $ (many newtype-fields-at : (subterm many (List $ Entry) tele) (many (List $ Nat) fids) (many (Env) env) (many (Res) scrut) -> (many (Env) out))
  (let-match many tele (Cons _ e rest) ((Nil _) env))
  (let-match many fids (Cons _ x tail2) ((Nil _) env))
  (let ((many env1)) (match many (entry-stored e) (((Env) _))
    ((BFalse) env) ((BTrue) (placed-at env x $ res-place scrut))))
  (tail $ newtype-fields-at rest tail2 env1 scrut))

(def-fns _ $ (many refine : (many (Env) env) (many (Res) scrut) (many (Nat) c) (many (List $ Nat) fids) (many (Term) ret) -> (many (UnifyRes) r))
  (let ((many params) (many _)) (ctor-type env c))
  (let ((many env14)) (match many (find-newtype env c) (((Env) _)) ((None _) env) ((Some _ _) (newtype-fields-at params fids env scrut))))
  (let ((many fvars)) $ tvars-rev fids $ Nil _)
  (merge-all $ unify-force (unify-force (Forcing env14) (res-term scrut) $ TApp (TVar c) $ list-rev _ fvars) (res-ty scrut) $ instantiate fvars ret))

(def-fns _ $ (many open-fields : (many (Env) env) (many (List $ Entry) tele) (many (List $ Maybe $ Name) names) (many (List $ Maybe $ Loc) sites) (many (Maybe $ List $ Multiplicity) mults) (many (Res) sres) (many (Nat) c) (many (Term) ret) ->
    (many (Env) r) (many (List $ Nat) fids) (many (UnifyRes) u))
  (let ((many env2) (many fids) (erased _)) $ open-tele tele env (Some _ names) (Some _ sites) mults (Nil _) $ BFalse)
  (let ((many env2d)) $ env-track-all (mark-words fids env2 (BFalse)) (BField) fids)
  (values env2d fids (refine env2d sres c fids ret)))

(def-fns _ $ (many disc-of-checked : (many (Env) env) (many (Syn) d) -> (many (Env) r) (many (Disc) disc))
  (let-match many (is-mark env d $ MkUnion) (BFalse) ((BTrue) (values env $ DUnion)))
  (match many (is-mark env d $ MkEnum) _
    ((BTrue) (values env $ DEnum))
    ((BFalse) (values (env-error env (say env "expected `enum` or `union`")) $ DEnum))))

; A claim on the FFI's fixed table (ASSUMPTIONS 42): each implementation backs one declaration per program.
(def-fns _ $ (many claim-extern : (many (Env) env) (many (String) name) (many (Bool) known) -> (many (Env) r))
  (let-match many known (BTrue) ((BFalse) (env-error env $ str-cat "no extern implementation for " $ tick name)))
  (let-match many (claimed-at (env-claimed env) name) (Some _ l) ((None _) (env-claim env name)))
  (env-error-with env (Cons _ (MkPair _ _ l "the declaration that bound it") $ Nil _) $ str-cat3 "the extern implementation of " (tick name) " is already bound"))


; ---- Small helpers the block's checks use

(def-fns _ $ (many macro-refused : (many (Env) env) (many (Syn) head) -> (many (Env) r))
  (let ((many plain)) $ str-cat (qraw head) " is a macro, expanded only where its head is constant-known")
  (let-match many (head-entry env head) (Some _ x) ((None _) (env-error env plain)))
  (let ((erased _) (many s)) $ entry-state env x)
  (let ((many dyn)) $ match many s (((Bool) _)) ((SHypothetical _) (BTrue)) (else (BFalse)))
  (let ((many gone)) $ match many (entry-mult-of env x) (((Bool) _)) ((Erased) (BTrue)) (else (BFalse)))
  (let-match many (or dyn gone) (BTrue) ((BFalse) (env-error env plain)))
  (let ((many how)) $ match many gone (((String) _)) ((BTrue) " `erased`") ((BFalse) ""))
  (let ((many where)) $ match many dyn (((String) _)) ((BTrue) ", where every binding is `Hypothetical`") ((BFalse) ""))
  (let ((many notes)) $ match many (env-entry-at env x) (((List $ Pair (Loc) $ String) _))
    ((None _) (Nil _))
    ((Some _ l) (Cons _ (MkPair _ _ l $ say env $ str-cat3 (qshown env x) " is bound" $ str-cat3 how " here" where) $ Nil _)))
  (let-match many gone (BTrue) ((BFalse) (env-error-hinted env notes plain $ say env "\nhint: a macro reaches a body through a run-position binding, named directly or forwarded by a `let`")))
  (match many dyn _
    ((BTrue) (env-error-with env notes $ str-cat (qraw head) " is an erased macro, expanded only where its head is constant-known and non-erased"))
    ((BFalse) (env-error-hinted env notes (str-cat (qraw head) " is an erased macro, and only a non-erased one is expanded") $ say env "\nhint: bind it `many` to expand it"))))

(def-fns _ $ (many cannot-apply-in-type : (many (Env) env) (many (Term) h) (many (Term) hty) -> (many (String) s))
  (str-cat3 (qshow env h) " has type " $ str-cat (qshow env hty) " and cannot be applied in a type"))

(def-fns _ $ (many annotation-kind : (many (Env) env) (many (Res) callee) (many (Bool) same) -> (many (String) s))
  (match many same _
    ((BTrue) (str-cat3 "same-level call to " (qshow env $ res-term callee) (say env " takes a `(subterm p)` annotation, not `(predates p)`")))
    ((BFalse) (str-cat3 "lower-level call to " (qshow env $ res-term callee) (say env " takes a `(predates p)` annotation, not `(subterm p)`")))))

(def-fns _ $ (many level-of-error : (many (Env) env) (many (Term) f) (many (Term) ty) -> (many (String) s))
  (str-cat3 (say env "`level-of`: ") (qshow env f) $ str-cat3 " : " (qshow env ty) " is not a function"))

(def-fns _ $ (many expr-error : (unique (ElabWorld) ew) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Env) env) (many (String) msg) (many (String) tag) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (values ew (env-error env msg) (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect tag))

(def-fns _ $ (many not-applicable : (unique (ElabWorld) ew) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Env) env) (many (Syn) head) (many (Res) h) (many (String) tag) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (match many (prelude-nullary env (res-ty h) "Macro") _
    ((BTrue) (values ew (macro-refused env head) (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect tag))
    ((BFalse) (expr-error ew ctx expect env (str-cat3 (qshow env $ res-term h) " : " $ str-cat (qshow env $ res-ty h) " is not applicable") tag))))

(def-lvl refusal-lvl)

(def-fns _ $ (many erased-result : (unique (ElabWorld) ew) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ What) what) (many (Env) env) (many (Res) r) -> (unique (ElabWorld) ewr at ew) (many (Env) r2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (let ((many env2) (many r2)) $ match many what (((Env) _) ((Res) _)) ((None _) (values env $ conformed (pos-in env expect) r)) ((Some _ w) (produced env w (pos-in env expect) r)))
  (values ew env2 (Cons _ r2 $ Nil _) $ hoist-none ctx expect $ CErased _ expect))

; A constructor named in source, read through its alias, which must hold a value constructor.
(def-fns _ $ (many ctor-var : (many (Env) env) (many (Syn) raw) -> (many (Env) r) (many (Nat) c))
  (let ((many env2) (many c)) $ named env raw "a constructor")
  (match many (type-of env2 c) _
    ((TValCtor _ _) (values env2 c))
    ((TErr _) (values env2 c)) (else (values (env-error env2 $ str-cat (qshown env2 c) " is not a value constructor") c))))

(def-fns _ $ (many runtime-one : (erased (List $ List $ Nat) ctx) (many (Multiplicity) pos)
    (many (Code ctx (Cons (Multiplicity) pos (Nil (Multiplicity)))) code) -> (many (Code ctx many-one) out))
  (match many pos _
    ((Erased) (CErased _ many-one))
    ((Many) code)
    (else (match many (mults-same (Cons _ pos (Nil _)) many-one) _
      ((None _) (CError _ many-one "invalid runtime shape"))
      ((Some _ same) (recast _ many-one (Cons _ pos (Nil _)) same code))))))

(def-fns _ $ (many bridge-code : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) outer) (erased (List $ Multiplicity) inner) (many (DemandBridge outer inner) bridge) (many (Code ctx inner) code) -> (many (Code ctx outer) out))
  (match many bridge _ ((KeepDemand _) code) ((HeadDemand mode) (runtime-one _ mode code))))

(def-fns _ $ (many prepare-argument : (many (Env) env) (many (Multiplicity) pos) (many (Res) res) (many (Bool) with-word) ->
    (many (Env) env2) (many (Res) prepared) (many (Nat) id))
  (let ((many env1) (many id)) (bind-as env (BFalse) (BTrue) (None _) (None _) (BFalse) pos (res-ty res) (Some _ (res-term res)) delegate-id))
  (let ((many env2)) (match many with-word (((Env) _)) ((BTrue) (mark-word env1 id (BTrue))) ((BFalse) (env-set-temporary env1 $ insert-desc id $ env-temporary env1))))
  (let ((many env3)) (placed-at env2 id $ res-place res))
  (values env3 (res-of env3 id) id))

(def-fns _ $ (many code-var : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) -> (many (Maybe $ Nat) r))
  (let-match many code (CValues _ _ cs _)
    ((CVar _ z _) (Some _ z))
    ((CConst _ z) (Some _ z))
    (else (None _)))
  (let-match many cs (Cons _ c rest) (else (None _)))
  (match many rest _ ((Nil _) (tail $ code-var _ _ c)) (else (None _))))

(def-fns _ $ (many settled-from : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (Env) env) (many (Code ctx ms) code) (many (Nat) x) -> (many (Env) r))
  (let-match many (env-run-pos env) (BTrue) ((BFalse) env))
  (let-match many (code-var _ _ code) (Some _ z) ((None _) env))
  (let ((erased _) (many h)) $ env-heap env)
  (let-match many (settled-ref _ (heap-entries _ h) z) (Some _ v) ((None _) env))
  (env-with-heap env _ $ heap-set-settled _ h x v))

(def-fns _ $ (many prepare-or-keep : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (Env) env) (many (Multiplicity) pos) (many (Res) res) (many (Code ctx ms) code) ->
    (many (Env) env2) (many (Res) prepared) (many (Nat) id))
  (let ((many (Maybe $ Nat) same))
    (match many (res-term res) _
      ((TVar y) (match many (code-var _ _ code) _ ((Some _ z) (match many (nat-eq y z) _ ((BTrue) (Some _ y)) ((BFalse) (None _)))) ((None _) (match many (mult-is-many pos) _ ((BTrue) (None _)) ((BFalse) (Some _ y))))))
      (else (None _))))
  (match many same _
    ((Some _ y) (values env res y))
    ((None _) (prepare-argument env pos res $ BTrue))))

(def-fns _ $ (many hoist-argument : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) bind-mult) (many (Multiplicity) pos) (many (Res) res) (many (Code ctx (Cons (Multiplicity) pos (Nil (Multiplicity)))) code) ->
    (many (Env) env2) (many (Res) prepared) (many (Nat) id) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
  (let ((many env1) (many r) (many id)) (prepare-or-keep _ _ env bind-mult res code))
  (let ((many physical)) (runtime-one _ pos code))
  (let ((many kept)) $ match many (code-var _ _ physical) (((Bool) _)) ((Some _ z) (nat-eq z id)) ((None _) (BFalse)))
  (let-match many (or kept $ not $ mult-is-many pos) (BFalse)
    ((BTrue) (values env1 r id ctx $ SNone _)))
  (let ((many env2) (many ctx2) (many sc)) (hoist-temp env1 ctx id physical))
  (values env2 r id ctx2 sc))

(def-fns _ $ (many prepare-pack : (erased (List $ List $ Nat) ctx)
    (subterm many (List $ Pair (Nat) $ Code ctx many-one) pairs) ->
    (many (List $ Multiplicity) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) ipk)
    (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk))
  (let-match many pairs (Cons _ pair rest) ((Nil _) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _))))
  (let-match many pair (MkPair _ _ id code))
  (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (notail $ prepare-pack _ rest))
  (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk)
    (Cons _ code codes) (PkMany _ ms code codes cpk)))

(def-fns _ $ (many hoist-unplaced : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) mult) (many (Res) res) (many (Code ctx (Cons (Multiplicity) mult (Nil (Multiplicity)))) code) ->
    (many (Env) env2) (many (Nat) id) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
  (let ((many env1) (many id)) (bind-as env (BFalse) (BTrue) (None _) (None _) (BFalse) mult (res-ty res) (Some _ (res-term res)) delegate-id))
  (let ((many env2) (many ctx2) (many sc)) (hoist-temp (mark-word env1 id (BTrue)) ctx id (runtime-one _ mult code)))
  (values env2 id ctx2 sc))

(def-fns _ $ (many id-codes : (many (Env) env) (many (List $ List $ Nat) ctx) (subterm many (List $ Nat) ids) -> (many (List $ Code ctx many-one) codes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (Cons _ (var-code env ctx id) $ notail $ id-codes env ctx rest))

(def-fns _ $ (many cell-result : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect)
    (many (Env) env) (many (Res) res) (many (Code ctx many-one) code) ->
    (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) out))
  (values env (Cons _ res (Nil _))
    (match many (mult-is-many (pos-in env expect)) (((Code ctx expect) _))
      ((BFalse) (CErased _ expect))
      ((BTrue) (match many (mults-same many-one expect) (((Code ctx expect) _))
        ((None _) (CError _ expect "size")) ((Some _ same) (recast _ expect many-one same code)))))))

(def-fns _ $ (many cell-result-hoisted : (unique (ElabWorld) ew) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Env) env) (many (Res) res) (many (Hoisted ctx many-one) h) -> (unique (ElabWorld) ewr at ew)
    (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) out))
  (let-match many h (MkHoisted _ _ ctx2 pre code))
  (let ((many env2) (many ress) (many out)) (cell-result _ expect env res code))
  (values ew env2 ress $ MkHoisted _ _ ctx2 pre out))

(def-fns _ $ (many same-cells : (many (ExprK) k) -> (many (Bool) r))
  (match many k _ ((ExCellSame) (BTrue)) (else (BFalse))))

(def-fns _ $ (many same-arg : (many (Env) env) (many (ExprK) k) (many (Syn) raw) (many (Res) r) -> (many (Env) env2) (many (Maybe $ Term) place))
  (let ((many ty)) $ canon-env env $ res-ty r)
  (let ((many ok)) $ match many ty (((Bool) _))
    ((TCell _ _) (same-cells k)) ((TFn _ _ _ _) (not $ same-cells k)) ((TErr _) (BTrue)) (else (BFalse)))
  (let ((many env2)) $ match many ok (((Env) _))
    ((BTrue) env)
    ((BFalse) (env-back env $ env-error (env-at env $ raw-pos raw) $ say env $ str-cat3
      (str-cat3 "`" (sp-name $ SpExpr k) "` takes ") (match many (same-cells k) (((String) _)) ((BTrue) "cells, and ") ((BFalse) "functions, and "))
      (str-cat3 (qshow env $ res-term r) " : " $ str-cat (qshow env ty) " is not one"))))
  (values env2 $ match many (res-place r) (((Maybe $ Term) _)) ((None _) (term-place env $ res-term r)) (else (res-place r))))

(def-fns _ $ (many fn-same-typed : (many (Env) env) (many (Res) ra) (many (Res) rb) -> (many (Env) env2))
  (match many (equal-env env (res-ty ra) (res-ty rb)) _
    ((BTrue) env)
    ((BFalse) (env-error env $ say env $ str-cat3 (str-cat3 "`fn-same` takes functions of one type, and " (qshow env $ res-term ra) " : ")
      (str-cat3 (qshow env $ res-ty ra) " and " (qshow env $ res-term rb)) (str-cat3 " : " (qshow env $ res-ty rb) " are not")))))

(def-fns _ $ (many cell-listed : (many (Env) env) (many (Res) r) -> (many (Maybe $ MatchInfo) info) (many (Nat) tid))
  (let-match many (canon-env env $ res-ty r) (TCell h _) (else (values (None _) 0)))
  (let-match many (canon-env env h) (TVar c) (else (values (None _) 0)))
  (let ((many tid)) $ tid-of env c)
  (let ((many _) (many found)) $ find-matchable env tid)
  (let-match many found (Some _ info) ((None _) (values (None _) tid)))
  (let-match many info (MkMatchInfo _ _ cs _))
  (match many (list-mem-bin (mctor-ids cs) c) _ ((BTrue) (values (Some _ info) tid)) ((BFalse) (values (None _) tid))))

(def-fns _ $ (many cell-same-listed : (many (Env) env) (many (Res) ra) (many (Res) rb) -> (many (Env) env2))
  (def-fns msg-lvl $ (many apart : -> (many (Env) r))
    (env-error env $ say env $ str-cat3 (str-cat "`cell-same` takes cells of constructors one opened `Matchable` lists, and " $ qshow env $ res-term ra) " and " $ str-cat (qshow env $ res-term rb) " are not"))
  (let ((many ia) (many ta)) $ cell-listed env ra)
  (let ((many ib) (many _)) $ cell-listed env rb)
  (let-match many ia (Some _ a) ((None _) (apart)))
  (let-match many ib (Some _ b) ((None _) (apart)))
  (let-match many a (MkMatchInfo ma da _ _))
  (let-match many b (MkMatchInfo mb _ _ _))
  (let-match many (nat-eq ma mb) (BTrue) ((BFalse) (apart)))
  (match many da _
    ((DEnum) env)
    ((DUnion) (env-error env $ say env $ str-cat3 "`cell-same` takes cells of an `enum`, and " (qshown env ta) " is a `union`"))))

(def-fns _ $ (many cells-allowed : (many (Env) env) (many (Nat) mid) (many (Bool) phantom) -> (many (Bool) r))
  (match many (type-of env mid) _
    ((TMatchable _ nt ext _ _) (and (or phantom $ not nt) (or (not ext) (env-in-extern env))))
    (else (BFalse))))

(def-fns _ $ (many phantom-cells-allowed : (many (Env) env) (many (Nat) tid) -> (many (Bool) r))
  (let ((many _) (many found)) (find-matchable env tid))
  (let-match many found (Some _ info) ((None _) (BFalse)))
  (let-match many info (MkMatchInfo mid _ _ _))
  (cells-allowed env mid $ BTrue))

(def-fns _ $ (many cell-shape : (many (Env) env) (many (Multiplicity) pos) (many (Nat) c) ->
    (many (Env) env2) (many (Ctor) ctor) (many (List $ Entry) params) (many (Term) ret) (many (Multiplicity) mark))
  (let ((many params) (many ret)) (ctor-type env c))
  (let ((many tid)) (tid-of env c))
  (let ((many env1) (many found)) (find-matchable env tid))
  (let-match many found (Some _ info)
    ((None _)
      (values (env-error env1 (say env1 "cell constructor has no opened `Matchable`"))
        (MkCtor (entry-name-or-id env c) c 0 (stored-count params) (BFalse) (None _) (Nil _) (BFalse)) params ret (Erased))))
  (let-match many info (MkMatchInfo mid disc cs _))
  (let ((many env2)) (match many (type-of env1 mid) (((Env) _))
    ((TMatchable _ nt ext _ _)
      (error-when (error-when env1 (and nt $ mult-is-many $ marker cs c) "newtype constructors have no cells")
        (and ext (not (env-in-extern env1))) "extern constructors have no cells outside an extern model"))
    (else (env-error env1 (say env1 "invalid cell `Matchable`")))))
  (let ((many env2b)) (error-unless env2 (list-mem-bin (mctor-ids cs) c)
    (str-cat3 (shown-name env2 c) " is not a constructor of " (shown-name env2 tid))))
  (let ((many env2d)) (match many (and (mult-is-many pos) $ not $ mult-is-many $ marker cs c) (((Env) _))
    ((BTrue) (env-error env2b $ str-cat (qshown env2b c) $ say env2b " is phantom, so its cell is used only in an erased position"))
    ((BFalse) env2b)))
  (let ((many ss)) (shapes cs env2d))
  (values env2d (MkCtor (entry-name-or-id env2d c) c (discriminant ss c) (stored-count params)
    (tagged-of disc ss) (None _) (cshape-arities (non-phantom ss)) (BFalse)) params ret (marker cs c)))

(def-fns _ $ (many pattern-slots : (subterm many (List $ Entry) params) (many (List $ Nat) ids) -> (many (List $ Term) slots))
  (let-match many params (Cons _ entry2 rest) ((Nil _) (Nil _)))
  (let-match many ids (Cons _ id tail2) ((Nil _) (Nil _)))
  (let ((many slots)) (notail $ pattern-slots rest tail2))
  (match many (entry-stored entry2) _ ((BFalse) slots) ((BTrue) (Cons _ (slot-atom id) slots))))

(def-fns _ $ (many binder-name : (many (Maybe $ Syn) b) -> (many (Maybe $ Name) r))
  (match many b _ ((None _) (None _)) ((Some _ r) (raw-name r))))

(def-fns _ $ (many binder-site : (many (Env) env) (many (Maybe $ Syn) b) -> (many (Maybe $ Loc) r))
  (match many b _ ((None _) (None _)) ((Some _ r) (Some _ $ loc-in env $ raw-pos r))))

(def-fns _ $ (many pattern-cell : (many (Env) env) (many (Multiplicity) mult) (many (Res) scrut)
    (many (Nat) ctor) (many (List $ Nat) fids) (many (Maybe $ Syn) braw) -> (many (Env) env2) (many (Nat) id))
  (let ((many params) (many _)) (ctor-type env ctor))
  (let ((many env1) (many id)) (bind env (binder-name braw) (binder-site env braw) (BTrue) mult (TCell (TVar ctor) (pattern-slots params fids)) (None _) delegate-id))
  (let ((many env2)) $ env-track (mark-word env1 id (BFalse)) (BOptional) id)
  (values (placed-at env2 id $ res-place scrut) id))

(def-fns _ $ (many field-mults : (subterm many (List $ Multiplicity) ms) (many (Multiplicity) mode) -> (many (List $ Multiplicity) r))
  (match many ms _ ((Nil _) ms) ((Cons _ m rest) (Cons _ (field-under mode m) $ notail $ field-mults rest mode))))

(def-fns _ $ (many split-pattern-fields : (subterm many (List $ Entry) tele) (many (List $ Syn) fields) -> (many (List $ Syn) prefix) (many (List $ Syn) suffix))
  (let-match many tele (Cons _ _ rest) ((Nil _) (values (Nil _) fields)))
  (let-match many fields (Cons _ f tail2)
    ((Nil _) (values (Nil _) fields)))
  (let ((many prefix) (many suffix)) (notail $ split-pattern-fields rest tail2))
  (values (Cons _ f prefix) suffix))

(def-fns _ $ (many is-entry : (many (Multiplicity) mult) (many (Term) t) (many (Maybe $ Term) place) -> (many (Entry) e))
  (MkEntry (None _) (BFalse) mult (SgIs t type-term) place (None _)))

(def-fns _ $ (many bound-slots : (subterm many (List $ Entry) tele) -> (many (List $ Term) slots))
  (let-match many tele (Cons _ e rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ bound-slots rest)
  (match many (entry-stored e) _ ((BFalse) more) ((BTrue) (Cons _ (TSlotOf $ TBound $ list-length _ rest) more))))

(def-fns _ $ (many with-cell-entry : (many (Nat) c) (many (List $ Entry) tele) (many (List $ Entry) shown) (many (Multiplicity) mode) (many (Maybe $ Term) place) -> (many (List $ Entry) r))
  (let ((many es) (erased _)) $ list-append _ shown $ Cons _ (MkEntry (None _) (BFalse) mode (SgTy $ TCell (TVar c) $ bound-slots tele) place (None _)) $ Nil _)
  es)

; [extra]: the telescope ends with the cell binder, which is optional (the owner's decision in chat;
; DESIGN.md section 23).
(def-fns _ $ (many binder-count : (many (Env) env) (many (Spot) ppos) (many (String) what) (many (Nat) c) (many (Multiplicity) mode) (many (Bool) extra) (many (Nat) got) (many (List $ Entry) tele) -> (many (Env) r))
  (let ((many n)) $ list-length _ tele)
  (error-at-with env ppos (declared-as env c) $ str-cat3 (say env what) " on " $ str-cat3 (qshown env c) (str-cat3 " under `" (spell env $ mult-name mode) "` expects ")
    $ str-cat3 (match many extra (((String) _)) ((BTrue) (str-cat3 (nat-str $ nat-sub n 1) " or " $ str-cat (nat-str n) " binders")) ((BFalse) (counted n "binder"))) ", got " $ str-cat (nat-str got) $ expected-str $ show-tele-t env tele (BTrue)))

(def-fns _ $ (many field-count : (many (Env) env) (many (Spot) ppos) (many (String) what) (many (String) noun) (many (Nat) c) (many (List $ Entry) params) (many (Nat) needed) (many (Nat) got) (many (String) rule) -> (many (Env) r))
  (let ((many shown)) $ show-tele-t env params (BTrue))
  (error-at-with env ppos (declared-as env c) $ str-cat3 (say env what) " of " $ str-cat3 (qshown env c) " expects " $ str-cat3 (counted needed noun) ", got "
    $ str-cat (nat-str got) $ match many (str-is-empty shown) (((String) _)) ((BTrue) "") ((BFalse) (str-cat3 ": expected " rule $ str-cat " " $ tick shown))))

(def-fns _ $ (many slot-count : (many (Env) env) (many (Spot) ppos) (many (String) what) (many (String) noun) (many (Nat) c) (many (List $ Entry) params) (many (Nat) got) -> (many (Env) r))
  (field-count env ppos what noun c params (stored-count params) got "one for each non-erased field of"))

(def-fns _ $ (many ctor-arg-count : (subterm many (List $ Entry) tele) -> (many (Nat) n))
  (let-match many tele (Cons _ e rest) ((Nil _) (Zero)))
  (let ((many more)) $ notail $ ctor-arg-count rest)
  (match many (entry-mult e) _ ((Erased) (Succ $ Succ more)) (else (Succ more))))

(def-fns _ $ (many slot-entries : (subterm many (List $ Term) slots) -> (many (List $ Entry) r))
  (match many slots _ ((Nil _) (Nil _)) ((Cons _ t rest) (Cons _ (is-entry (Many) t $ None _) $ notail $ slot-entries rest))))

(def-fns _ $ (many pattern-fields : (many (Env) env) (many (Spot) ppos) (many (String) what) (many (Multiplicity) mode) (many (Res) scrut) (many (Nat) c) (many (List $ Entry) tele) (many (List $ Multiplicity) mults) (many (List $ Syn) fields) (many (Bool) extra) ->
    (many (Env) out) (many (List $ Syn) ordinary) (many (Maybe $ Syn) braw))
  (let ((many env14)) (error-unless env (atoms-only fields) "pattern binders must be names or `_`"))
  (let ((many n)) $ list-length _ tele)
  (let ((many got)) $ list-length _ fields)
  (let ((many shown)) $ tele-with-mults tele mults)
  (let ((many has-cell)) $ and extra $ nat-eq got $ Succ n)
  (let-match many (or (nat-eq got n) has-cell) (BTrue)
    ((BFalse) (values (binder-count env14 ppos what c mode extra got $ match many extra (((List $ Entry) _)) ((BTrue) (with-cell-entry c tele shown mode $ res-place scrut)) ((BFalse) shown)) fields (None _))))
  (let-match many has-cell (BTrue) ((BFalse) (values env14 fields (None _))))
  (let ((many ordinary) (many rest)) (split-pattern-fields tele fields))
  (values env14 ordinary (match many rest (((Maybe $ Syn) _)) ((Nil _) (None _)) ((Cons _ r _) (Some _ r)))))

(def-fns _ $ (many pattern-cell-option : (many (Env) env) (many (Multiplicity) mult) (many (Res) scrut) (many (Nat) c) (many (List $ Nat) fids) (many (Bool) extra) (many (Maybe $ Syn) name) -> (many (Env) out) (many (Maybe $ Nat) cell))
  (let-match many extra (BTrue) ((BFalse) (values env (None _))))
  (let ((many env1) (many id)) (pattern-cell env mult scrut c fids name))
  (let ((many env2)) (match many (res-term scrut) (((Env) _)) ((TVar x) (forward-state env1 id x)) (else env1)))
  (values env2 (Some _ id)))


(def-adts $ (ElseBody : ((Syn) raw) -> Type)
  enum
  (many MkElseBody : (erased (Syn) raw) (many (Maybe $ Syn) name) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) raw) p) -> (ElseBody raw)))
; An `else` binds the scrutinee back when its first item is an atom followed by a body; otherwise the body
; starts at once (section 23).
(def-fns _ $ (many else-parts : (many (Syn) raw) (many (Bool) extra) -> (many (Maybe $ ElseBody raw) r))
  (let-match many raw (RList _ items) (else (None _)))
  (let-match many items (Cons _ _ body) ((Nil _) (None _)))
  (let ((many whole)) $ MkElseBody raw (None _) body $ prove-subterm body raw)
  (let-match many extra (BTrue) ((BFalse) (Some _ whole)))
  (let-match many body (Cons _ name rest)
    ((Nil _) (Some _ whole)))
  (let-match many rest (Cons _ _ _) ((Nil _) (Some _ whole)))
  (match many (raw-atom name) _ ((None _) (Some _ whole)) ((Some _ _) (Some _ $ MkElseBody raw (Some _ name) rest $ prove-subterm rest raw))))

(def-fns _ $ (many else-binder : (many (Env) env) (many (Res) scrut) (many (Multiplicity) mult) (many (Bool) extra) (many (Maybe $ Syn) name) -> (many (Env) out) (many (Maybe $ Nat) binder))
  (let-match many extra (BTrue) ((BFalse) (values env (None _))))
  (let ((many env1) (many x)) (bind env (binder-name name) (binder-site env name) (BTrue) mult (res-ty scrut) (Some _ $ res-term scrut) delegate-id))
  (let ((many env2)) $ env-track (mark-word env1 x (BFalse)) (BOptional) x)
  (values (placed-at env2 x $ res-place scrut) (Some _ x)))

; `(slot-of x)`: the automatic slot of x's binder (section 35), a direct variable reference and no use.
(def-fns _ $ (many slot-var : (many (Env) env) (many (Syn) raw) -> (many (Env) env2) (many (Nat) id))
  (let ((many env1) (many id)) (var-of-raw env raw "a direct variable reference"))
  (def-fns msg-lvl $ (many bound-msg : -> (many (String) s)) (str-cat3 (say env1 "`slot-of` in a constructor's telescope cannot name ") (qshown env1 id) ", bound by a telescope still being written"))
  (values (env-back env1 $ error-when-msg (env-at env1 $ raw-pos raw) (list-mem-bin (env-ctor-tele env1) id) bound-msg) id))

(def-fns _ $ (many cell-slot-codes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) -> (many (List $ Code ctx many-one) codes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (Cons _ (match many id (((Code ctx many-one) _))
    ((None _) (CValue _ (BToken _))) ((Some _ x) (var-code env ctx x))) (notail $ cell-slot-codes env ctx rest)))

(def-fns _ $ (many cell-slot-writes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) (many (Nat) index) -> (many (List $ Pair (Nat) $ Code ctx many-one) writes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (let ((many writes)) (notail $ cell-slot-writes env ctx rest (Succ index)))
  (match many id _ ((None _) writes) ((Some _ x) (Cons _ (MkPair _ _ index (var-code env ctx x)) writes))))

(def-fns _ $ (many cell-alloc-result : (unique (ElabWorld) ew) (many (Env) env) (erased (List $ List $ Nat) ctx) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre)
    (many (List $ Multiplicity) expect) (many (Nat) c) (many (Ctor) ct) (many (List $ Term) slots)
    (many (List $ Maybe $ Nat) slotids) -> (unique (ElabWorld) ewr at ew)
    (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (let ((many env1) (many x)) (bind env (None _) (None _) (BFalse) (under (pos-in env expect) (Once)) (TCell (TVar c) slots) (None _) delegate-id))
  (let ((many hollow)) $ hollow-ctor env1 c)
  (let ((many place)) $ match many hollow (((Maybe $ Term) _)) ((BTrue) (Some _ $ slot-atom null-id)) ((BFalse) (None _)))
  (let ((many env2)) $ placed-at env1 x place)
  (cell-result-hoisted ew ctx expect env2 (res-with-place (res-of env2 x) place)
    (MkHoisted _ _ ctx2 pre $ match many hollow (((Code ctx2 many-one) _))
      ((BTrue) (var-code env2 ctx2 null-id))
      ((BFalse) (CCellAlloc _ ct (cell-slot-codes env2 ctx2 slotids))))))

(def-fns _ $ (many cell-mark-token : (many (Env) env) (many (Syn) raw) -> (many (Bool) is-at))
  (let-match many raw (RList _ items)
    (else (BFalse)))
  (match many items _ ((Cons _ m rest) (and (list-is-empty _ rest) (is-mark env m (MkAt)))) ((Nil _) (BFalse))))

(def-fns _ $ (many cell-marks : (erased (List $ Syn) root) (subterm many (List $ Sub root) items)
    (many (Env) env) (many (Bool) pending) -> (many (Env) env2) (many (List $ Sub root) args) (many (List $ Bool) marks))
  (let-match many items (Cons _ item rest)
    ((Nil _) (values (refuse-when env pending "`at` must precede an argument") (Nil _) (Nil _))))
  (let-match many item (MkSub _ raw _))
  (let-match many (cell-mark-token env raw) (BFalse) ((BTrue) (tail $ cell-marks _ rest env (BTrue))))
  (let ((many env2) (many args) (many marks)) (notail $ cell-marks _ rest env (BFalse)))
  (values env2 (Cons _ item args) (Cons _ pending marks)))

(def-fns _ $ (many cell-invoke-writes : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Bool) full)
    (subterm many (List $ Entry) params) (many (List $ Term) terms) (many (List $ Bool) marks)
    (many (List $ Term) slots) (many (Nat) index) -> (many (Env) env2) (many (List $ Pair (Nat) $ Code ctx many-one) writes))
  (let-match many params (Cons _ param rest) ((Nil _) (values env (Nil _))))
  (let ((many term) (many ts)) (match many terms (((Term) _) ((List $ Term) xs))
    ((Nil _) (values (TErr "missing argument") (Nil _))) ((Cons _ x xs) (values x xs))))
  (let ((many skip) (many ms)) (match many marks (((Bool) _) ((List $ Bool) xs))
    ((Nil _) (values (BFalse) (Nil _))) ((Cons _ x xs) (values x xs))))
  (match many (entry-mult param) _
    ((Erased) (tail $ cell-invoke-writes (refuse-when env skip "`at` cannot mark an erased argument") ctx full rest ts ms slots index))
    (else
      (let ((many slot) (many ss)) (match many slots (((Term) _) ((List $ Term) xs))
        ((Nil _) (values (TErr "missing slot") (Nil _))) ((Cons _ x xs) (values x xs))))
      (let ((many same)) (equal-env env slot $ TSlotOf term))
      (let ((many omit)) (or full skip))
      (let ((many env1)) (refuse-when env (and omit (not same))
        (str-cat3 "`at` argument " (nat-str (Succ index)) " is not in its slot's location class")))
      (let ((many env2) (many writes)) (notail $ cell-invoke-writes env1 ctx full rest ts ms ss (Succ index)))
      (values env2 (match many omit (((List $ Pair (Nat) $ Code ctx many-one) _))
        ((BTrue) writes) ((BFalse) (Cons _ (MkPair _ _ index (var-code env2 ctx (term-var term))) writes)))))))

(def-fns _ $ (many cell-read-bindings : (many (Env) env) (many (List $ List $ Nat) ctx)
    (many (Nat) sid) (many (Ctor) k2) (subterm many (Nat) n) (many (List $ Syn) names)
    (many (List $ Term) slots) (many (Multiplicity) pos) (many (Nat) index) ->
    (many (Env) env2) (many (List $ Pair (Nat) $ Code ctx many-one) pairs) (many (List $ Syn) restnames))
  (let-match many n (Succ k) ((Zero) (values env (Nil _) names)))
  (let-match many names (Cons _ name rest) ((Nil _) (values (env-error env (say env "`cell-match` needs more binders")) (Nil _) (Nil _))))
  (let ((many slot) (many ss)) (match many slots (((Term) _) ((List $ Term) ss))
    ((Nil _) (values (TErr "missing slot") (Nil _))) ((Cons _ s ss) (values s ss))))
  (let ((many env0) (many nm)) (name-checked env name "a slot binder"))
  (let ((many env1) (many id)) (bind env0 nm (Some _ $ loc-in env0 $ raw-pos name) (BTrue) (under pos (Many)) slot-term (Some _ slot) delegate-id))
  (let ((many env2)) $ env-track (mark-word env1 id (BFalse)) (BField) id)
  (let ((many env3) (many pairs) (many restnames)) (notail $ cell-read-bindings env2 ctx sid k2 k rest ss pos (Succ index)))
  (values env3 (Cons _ (MkPair _ _ id (CCellRead _ k2 index (var-code env3 ctx sid))) pairs) restnames))

(def-fns _ $ (many malformed-entry : (many (Env) env) (many (Syn) r) -> (many (Env) e))
  (let-match many (list-rev _ $ raw-items r) (Cons _ last _) ((Nil _) (env-error env $ str-cat3 "malformed telescope entry " (qraw r) $ sp-hints env "telescope-entry")))
  (let-match many (or (raw-is-literal last) $ raw-handle last) (BTrue) ((BFalse) (env-error env $ str-cat3 "malformed telescope entry " (qraw r) $ sp-hints env "telescope-entry")))
  (error-at env (raw-pos last) $ not-name $ syn-literal env last))

(def-fns _ $ (many parse-entries-checked : (erased (List $ Syn) root) (subterm many (List $ Sub root) subs) (many (Env) env) -> (many (Env) r) (many (List $ SrcEntry root) es))
  (let-match many subs (Cons _ s rest) ((Nil _) (values env $ Nil _)))
  (let ((many (Env) env1) (many (List $ SrcEntry root) here))
    (match many s _
      ((MkSub _ r p)
        (let-match many (raw-atom r) (None _)
          ((Some _ str) (values (env-error env $ str-cat "expected a telescope entry, got " $ name-text str) $ Nil _)))
        (let ((many es)) $ parse-entry env r _ p)
        (match many es (((Env) _) ((List $ SrcEntry root) l))
          ((Nil _) (values (malformed-entry env r) es))
          ((Cons _ _ _) (values env es))))))
  (let ((many env2) (many more)) $ notail $ parse-entries-checked _ rest env1)
  (let ((many all) (erased _)) $ list-append _ here more)
  (values env2 all))

(def-fns _ $ (many check-binder-mults : (erased (List $ Syn) root) (subterm many (List $ SrcEntry root) es) (many (Multiplicity) spos) (many (Env) env) -> (many (Env) r))
  (let-match many es (Cons _ e rest) ((Nil _) env))
  (let-match many e (MkSrcEntry _ _ m _ _ _ site))
  (match many m _
    ((Some _ mm) (tail $ check-binder-mults _ rest spos $ env-back env $ written (env-at env site) spos mm "a `let` binder"))
    ((None _) (tail $ check-binder-mults _ rest spos $ env-error env (say env "`let` binder needs a multiplicity")))))

(def-fns _ $ (many mult-checked : (many (Env) env) (many (Syn) raw) -> (many (Env) r) (many (Multiplicity) m))
  (match many (mult-of env raw) _
    ((Some _ m) (values env m))
    ((None _) (values (env-error env $ str-cat "expected a multiplicity, got " $ qraw raw) $ Many))))

(def-fns _ $ (many level-var-checked : (many (Env) env) (many (Term) t) (many (String) alt) -> (many (Env) r) (many (Nat) x))
  (def-fns msg-lvl $ (many bad : -> (many (Env) r)) (env-error env $ str-cat3 (qshow env t) " is not a level" alt))
  (let-match many (canon-env env t) (TVar x) (else (values (bad) $ Zero)))
  (match many (equal-env env (type-of env x) level-term) _ ((BTrue) (values env x)) ((BFalse) (values (bad) x))))

(def-fns _ $ (many level-binder : (many (Env) env) (many (Term) t) -> (many (Env) r) (many (Nat) x))
  (match many t _ ((TVar x) (values env x)) (else (values (env-error env $ str-cat (qshow env t) " is not a level") $ Zero))))

(def-fns _ $ (many one-arg : (many (List $ Syn) args) -> (many (Syn) r))
  (match many args _ ((Nil _) (RWild $ MkSpot 0 0)) ((Cons _ r _) r)))

(def-fns _ $ (many comptime-shape : (many (List $ Syn) args) -> (many (Maybe $ Pair (Syn) $ Pair (Syn) $ List $ Syn) r))
  (let-match many args (Cons _ x rest) ((Nil _) (None _)))
  (let-match many rest (Cons _ pat more) ((Nil _) (None _)))
  (let-match many more (Nil _) ((Cons _ _ _) (None _)))
  (let-match many (raw-items pat) (Cons _ craw fields) ((Nil _) (None _)))
  (match many (atoms-only fields) _
    ((BTrue) (Some _ $ MkPair _ _ x $ MkPair _ _ craw fields))
    ((BFalse) (None _))))

; numeral-of (section 45): a numeral or character literal by its own spelling, never an expression.
(def-fns _ $ (many numeral-of-term : (many (Env) env) (many (Syn) arg0) -> (many (Env) r) (many (Maybe $ Term) t))
  (let ((many arg)) $ syn-literal env arg0)
  (let-match many (raw-is-literal arg) (BTrue)
    ((BFalse)
      (match many arg _
        ((RList _ _) (values (env-error env $ str-cat "expected a literal, got " $ qraw arg) $ None _))
        (else (values (env-error env $ str-cat (say env "`numeral-of` takes a literal, not ") $ qraw arg) $ None _)))))
  (let ((many env1) (many found)) $ lit-entry env arg)
  (let-match many found (Some _ x) ((None _) (values env1 $ None _)))
  (match many (lit-proof (env-lits env1) x) _
    ((None _) (values (env-error env1 $ str-cat (show-r arg) " is a string literal, which carries no `Numeral` proof") $ None _))
    ((Some _ p) (values env1 $ Some _ $ TVar p))))

(def-fns _ $ (many is-fetch : (many (ExprK) e) -> (many (Bool) r))
  (match many e _ ((ExLevelOf) (BTrue)) ((ExMatchableOf) (BTrue)) ((ExDelegateOf) (BTrue)) ((ExNumeralOf) (BTrue)) ((ExSlotOf) (BTrue)) ((ExAtFnOf) (BTrue)) (else (BFalse))))

; The number a numeral or character literal spells, if the raw is one (lib/literal.ml's classify).
(def-fns _ $ (many lit-number : (many (Syn) raw) -> (many (Maybe $ Nat) n))
  (match many raw _ ((RNat _ n) (Some _ n)) ((RChr _ c) (Some _ c)) (else (None _))))

; How a numeral or character literal is spelled in a message (lib/literal.ml's spell).
(def-fns _ $ (many literal-spelled : (many (Syn) raw) (many (Nat) z) -> (many (String) s))
  (match many raw _ ((RChr _ _) (rope-str $ lit-char-rope z)) (else (nat-str z))))

; The entry holding the Nat a numeral or character literal stands for, a character's being its code's
; (lib/elab.ml's numeral_entry).
(def-fns _ $ (many numeral-entry : (many (Env) env) (many (Syn) raw0) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ Nat) e))
  (let ((many raw)) $ syn-literal env raw0)
  (let-match many (lit-number raw) (Some _ z)
    ((None _)
      (values (env-error env
                (str-cat (qraw raw) " is not a numeral or character literal"))
              $ None _)))
  (let ((many env1)) $ intern-raw env raw)
  (match many (lit-lookup env1 $ nat-str z) _
    ((None _) (values env1 $ None _))
    ((Some _ x) (values env1 $ Some _ $ MkPair _ _ z x))))

(def-fns _ $ (many literal-lt-entry : (many (Env) env) (many (Syn) raw0) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ Nat) e))
  (let ((many raw)) $ syn-literal env raw0)
  (let ((many (Bool) numeral)) $ match many raw (((Bool) b)) ((RNat _ _) (BTrue)) (else (BFalse)))
  (match many numeral _
    ((BFalse) (values (env-error env $ str-cat (say env "`prove-literal-lt` takes two numerals, got ") $ qraw raw) $ None _))
    ((BTrue) (numeral-entry env raw))))

(def-fns _ $ (many mint-literal-lt : (many (Env) env) (many (List $ Syn) args) -> (many (Env) r) (many (Maybe $ Res) res))
  (let-match many args (Cons _ araw rest) ((Nil _) (values env $ None _)))
  (let-match many rest (Cons _ braw _) ((Nil _) (values env $ None _)))
  (let ((many env1) (many ea)) $ literal-lt-entry env araw)
  (let ((many env2) (many eb)) $ literal-lt-entry env1 braw)
  (let-match many ea (Some _ pa) ((None _) (values env2 $ None _)))
  (let-match many eb (Some _ pb) ((None _) (values env2 $ None _)))
  (let-match many pa (MkPair _ _ za xa))
  (let-match many pb (MkPair _ _ zb xb))
  (let-match many (nat-lt za zb) (BTrue)
    ((BFalse) (values (env-error env2 $ str-cat3 (say env2 "`prove-literal-lt`: ") (nat-str za) $ str-cat " is not below " $ nat-str zb) $ None _)))
  (let ((many env3) (many lt)) $ prelude-id env2 "Lt")
  (let ((many env4) (many r)) $ mint env3 $ proof-type lt $ Cons _ (TVar xa) $ Cons _ (TVar xb) $ Nil _)
  (values env4 $ Some _ r))

; A generated form is elaborated in the prelude's scope, so user shadowing cannot reach it, and the caller's
; scope restored after; the level context stays the caller's throughout (lib/elab.ml's in_prelude).
(def-fns _ $ (many generated-form : (many (Env) env) -> (many (Env) r))
  (env-set-scope env $ env-prelude env))

(def-fns _ $ (many leave-prelude : (many (Env) outer) (many (Env) inner) -> (many (Env) r))
  (env-set-scope inner $ env-scope outer))

(def-fns _ $ (many cc-eq : (many (CC) a) (many (CC) b) -> (many (Bool) r))
  (match many a _
    ((CCPlain) (match many b _ ((CCPlain) (BTrue)) (else (BFalse))))
    ((CCTail) (match many b _ ((CCTail) (BTrue)) (else (BFalse))))
    ((CCDelegate) (match many b _ ((CCDelegate) (BTrue)) (else (BFalse))))
    ((CCCtor) (match many b _ ((CCCtor) (BTrue)) (else (BFalse))))
    ((CCNoTail) (match many b _ ((CCNoTail) (BTrue)) (else (BFalse))))
    ((CCSame _ _) (BFalse))))

; A branch of the raw b: present, refuted automatically with (absurd C), or absurd by proof (section 21).
(def-adts $ (BranchParts : ((Syn) b) -> Type)
  enum
  (many BPresent : (erased (Syn) b) (many (Syn) craw) (many (List $ Syn) fields) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) b) p) -> (BranchParts b))
  (many BRefuted : (erased (Syn) b) (many (Syn) craw) -> (BranchParts b))
  (many BAbsurd : (erased (Syn) b) (many (Syn) craw) (many (List $ Syn) fields) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) b) p) -> (BranchParts b)))

(def-fns _ $ (many pattern-parts : (many (Syn) pat) -> (many (Maybe $ Pair (Syn) $ List $ Syn) r))
  (let-match many pat (RList _ items) ((RAtom _ _) (Some _ $ MkPair _ _ pat $ Nil _)) (else (None _)))
  (let-match many items (Cons _ c fs)
    ((Nil _) (None _)))
  (match many (atoms-only fs) _ ((BTrue) (Some _ $ MkPair _ _ c fs)) ((BFalse) (None _))))

(def-fns _ $ (many branch-parts : (many (Env) env) (many (Syn) braw) -> (many (Maybe $ BranchParts braw) r))
  (let-match many braw (RList _ items) (else (None $ BranchParts braw)))
  (let-match many items (Cons _ first more) ((Nil _) (None _)))
  (match many (is-mark env first $ MkAbsurd) _
    ((BFalse)
      (let-match many (pattern-parts first) (Some _ pp)
        ((None _) (None _)))
      (match many pp _ ((MkPair _ _ c fs) (Some _ $ BPresent _ c fs more $ prove-subterm more braw))))
    ((BTrue)
      (let-match many more (Cons _ pat body) ((Nil _) (None _)))
      (match many body _
        ((Nil _)
          (match many (raw-atom pat) _
            ((Some _ _) (Some _ $ BRefuted _ pat))
            ((None _) (None _))))
        ((Cons _ _ _)
          (let-match many (pattern-parts pat) (Some _ pp)
            ((None _) (None _)))
          (match many pp _ ((MkPair _ _ cc fs) (Some _ $ BAbsurd _ cc fs body $ prove-subterm body braw))))))))

(def-fns _ $ (many pattern-pos : (many (Env) env) (many (Syn) braw) -> (many (Spot) p))
  (let-match many braw (RList bp items)
    (else (raw-pos braw)))
  (let-match many items (Cons _ first more)
    ((Nil _) bp))
  (let-match many (is-mark env first $ MkAbsurd) (BTrue)
    ((BFalse) (raw-pos first)))
  (match many more _ ((Cons _ pat _) (raw-pos pat)) ((Nil _) bp)))

(def-fns _ $ (many marker-checked : (many (Env) env) (many (Nat) tid) (many (List $ MCtor) mctors) (many (Nat) c) -> (many (Env) r) (many (Multiplicity) m))
  (match many (mctors-list mctors c) _
    ((BTrue) (values env $ marker mctors c))
    ((BFalse) (values (env-error env $ str-cat3 (qshown env c) " is not a constructor of " $ qshown env tid) $ Many))))

(def-fns _ $ (many scrutinee-matchable : (many (Env) env) (many (Res) sres) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ MatchInfo) found))
  (let ((many env1)) $ settle-res env sres)
  (let-match many (type-head env1 $ res-ty sres) (Some _ tid)
    ((None _) (values (env-error env1 $ str-cat3 "cannot match on " (qshow env1 $ res-term sres) $ str-cat " : " $ qshow env1 $ res-ty sres) $ None _)))
  (let ((many env2) (many found)) $ find-matchable env1 tid)
  (let-match many found (Some _ info)
    ((None _) (values (env-error env2 $ str-cat (qshown env2 tid) (say env2 " has no `Matchable` open")) $ None _)))
  (values env2 $ Some _ $ MkPair _ _ tid info))

(def-fns _ $ (many warn-match : (many (Env) env) (many (Bool) runs) (many (Nat) tid) -> (many (Env) r))
  (match many runs _ ((BTrue) (warn-use env (env-loc env) "match on" $ TVar tid)) ((BFalse) env)))

(def-fns _ $ (many count-bins : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Nat) n))
  (let-match many xs (Cons _ y rest)
    ((Nil _) 0))
  (match many (nat-cmp x y) _ ((CEq _ _ _) (Succ $ notail $ count-bins rest x)) (else (tail $ count-bins rest x))))

; Every constructor of the Matchable appears exactly once (section 21).
(def-fns _ $ (many is-else-branch : (many (Env) env) (many (Syn) braw) -> (many (Bool) r))
  (let-match many braw (RList _ items) (else (BFalse)))
  (match many items _ ((Nil _) (BFalse)) ((Cons _ first _) (is-mark env first $ MkElse))))

(def-fns _ $ (many has-real-branch : (many (Env) env) (subterm many (List $ Syn) bs) -> (many (Bool) r))
  (let-match many bs (Cons _ b rest) ((Nil _) (BFalse)))
  (let-match many (raw-items b) (Cons _ first _)
    ((Nil _) (BTrue)))
  (match many (is-mark env first $ MkAbsurd) _ ((BTrue) (tail $ has-real-branch env rest)) ((BFalse) (BTrue))))

(def-fns _ $ (many let-else : (many (Env) env) (many (Syn) item) (many (List $ Syn) rest) -> (many (Maybe $ Pair (Syn) $ List $ Syn) r))
  (let-match many (raw-items item) (Cons _ head args) ((Nil _) (None _)))
  (let-match many args (Cons _ m a1) ((Nil _) (None _)))
  (let-match many a1 (Cons _ scrut a2) ((Nil _) (None _)))
  (let-match many a2 (Cons _ pat branches) ((Nil _) (None _)))
  (match many (and (is-special env head $ SpStmt $ StLetMatch) $ has-real-branch env branches) _
    ((BTrue) (Some _ $ MkPair _ _ head $ Cons _ m $ Cons _ scrut $ Cons _ (RWild $ raw-pos pat) $ Cons _ (RList (raw-pos pat) $ Cons _ pat rest) branches))
    ((BFalse) (None _))))

; The unlisted constructors an else stands for: those whose forced unification does not contradict; the first of
; them, and whether any could run (section 21).
; The forcing trial for constructor [c], [m] its multiplicity marker: the environment it opens its fields in, and
; whether forcing contradicts. covered-of and the error path's ctor-trial both run it.
(def-fns _ $ (many run-trial : (many (Multiplicity) m) (many (Nat) c) (many (Env) env) (many (Res) sres) (many (Multiplicity) smult) -> (many (Env) envb) (many (UnifyRes) u))
  (let ((many ctele) (many ret)) $ ctor-type env c)
  (let ((many (List $ Multiplicity) mults)) $ match many (mult-is-many m) _ ((BFalse) (all-erased $ tele-mults ctele)) ((BTrue) (field-mults (tele-mults ctele) smult)))
  (let ((many envb) (many _) (many u)) $ open-fields (env-set-run-pos env $ BFalse) ctele (anon-names ctele) (anon-sites ctele) (Some _ mults) sres c ret)
  (values envb u))

(def-fns _ $ (many covered-of : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Nat) seen) (many (Res) sres) (many (Multiplicity) smult) (many (Maybe $ Nat) first) (many (Bool) reachable) (many (List $ Nat) covered) -> (many (Env) r) (many (Maybe $ Nat) first2) (many (Bool) reachable2) (many (List $ Nat) covered2))
  (let-match many mctors (Cons _ mc rest) ((Nil _) (values env first reachable covered)))
  (let-match many mc (MkMCtor m t))
  (let ((many c)) $ term-var t)
  (let-match many (nat-cmp (count-bins seen c) 0) (CEq _ _ _)
    (else (tail $ covered-of rest env seen sres smult first reachable covered)))
  (let ((many phantom)) $ not $ mult-is-many m)
  (let ((many envb) (many u)) $ run-trial m c env sres smult)
  (let-match many u (UOk envb2)
    ((UContra _) (tail $ covered-of rest (env-discard env envb) seen sres smult first reachable covered)))
  (tail $ covered-of rest (env-discard env envb2) seen sres smult
    (match many first (((Maybe $ Nat) _)) ((None _) (Some _ c)) ((Some _ _) first))
    (or reachable $ not $ and phantom $ mult-is-many smult)
    $ match many phantom (((List $ Nat) _)) ((BTrue) covered) ((BFalse) (Cons _ c covered))))

; The environment the forcing trial for constructor [c] leaves, as covered-of runs it, where it does not
; refute the constructor.
(def-fns _ $ (many ctor-trial : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Multiplicity) smult) (many (Nat) c) -> (many (Maybe $ Env) r))
  (let-match many mctors (Cons _ mc rest) ((Nil _) (None _)))
  (let-match many mc (MkMCtor m t))
  (let-match many (nat-eq (term-var t) c) (BTrue) ((BFalse) (tail $ ctor-trial rest env sres smult c)))
  (let ((many _) (many u)) $ run-trial m c env sres smult)
  (match many u _ ((UContra _) (None _)) ((UOk envb2) (Some _ envb2))))

; An error about branches forcing left standing, with the notes each trial's literals earn.
(def-fns _ $ (many forced-error : (many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Multiplicity) smult) (subterm many (List $ Nat) cs) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ forced-error mctors env sres smult rest)
  (let-match many (ctor-trial mctors env sres smult c) (Some _ trial) ((None _) more))
  (let ((many joined) (erased _)) $ list-append _ (forced-notes env trial sres) more)
  joined)

(def-fns _ $ (many unrefuted : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Nat) seen) (many (Res) sres) (many (Multiplicity) smult) -> (many (List $ Nat) r))
  (let-match many mctors (Cons _ mc rest) ((Nil _) (Nil _)))
  (let-match many mc (MkMCtor m t))
  (let ((many c)) $ term-var t)
  (let ((many more)) $ notail $ unrefuted rest env seen sres smult)
  (let-match many (nat-cmp (count-bins seen c) 0) (CEq _ _ _) (else more))
  (let ((many _) (many u)) $ run-trial m c env sres smult)
  (match many u _ ((UContra _) more) ((UOk _) (Cons _ c more))))

(def-fns _ $ (many missing-notes : (many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Multiplicity) smult) (subterm many (List $ Nat) cs) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ missing-notes mctors env sres smult rest)
  (let ((many what)) $ str-cat "value constructor " $ qshown env c)
  (let ((many head)) $ match many (env-entry-at env c) (((Pair (Loc) $ String) _))
    ((Some _ l) (MkPair _ _ l $ str-cat what ", which is declared here"))
    ((None _) (MkPair _ _ (env-loc env) $ str-cat what ", which is built in")))
  (let ((many joined) (erased _)) $ list-append _ (Cons _ head $ forced-error mctors env sres smult $ Cons _ c $ Nil _) more)
  joined)

(def-fns _ $ (many missing-branches : (many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Multiplicity) smult) (many (List $ Nat) seen) (many (String) form) -> (many (Env) r))
  (let ((many cs)) $ unrefuted mctors env seen sres smult)
  (env-error-with env (missing-notes mctors env sres smult cs)
    $ str-cat3 (say env $ str-cat3 "this " form " is missing a branch for the following unrefuted constructor") (match many (nat-eq (list-length _ cs) 1) (((String) _)) ((BTrue) "") ((BFalse) "s")) ":"))

(def-adts $ (RefuteForm : ((Syn) raw) -> Type)
  enum
  (many RefuteMatch : (erased (Syn) raw) (many (Syn) head) (many (List $ Syn) args) (erased (Subterm (List $ Syn) args (Syn) raw) p) -> (RefuteForm raw))
  (many RefuteOpen : (erased (Syn) raw) (many (Syn) head) (many (Syn) e) (erased (Subterm (Syn) e (Syn) raw) p) -> (RefuteForm raw))
  (many RefuteValue : (erased (Syn) raw) -> (RefuteForm raw)))

(def-fns _ $ (many refute-form : (many (Env) env) (many (Syn) raw) -> (many (RefuteForm raw) r))
  (let-match many raw (RList _ items) (else (RefuteValue _)))
  (let-match many items (Cons _ head args) ((Nil _) (RefuteValue _)))
  (let-match many (and (is-special env head $ SpExpr $ ExMatch) $ is-underscore $ list-nth-or _ args 2 raw) (BFalse)
    ((BTrue) (RefuteMatch _ head args $ prove-subterm args raw)))
  (let-match many args (Cons _ e more) ((Nil _) (RefuteValue _)))
  (match many (and (is-special env head $ SpExpr $ ExOpenAbsurd) $ and (nat-eq (list-length _ more) 1) $ is-underscore $ list-nth-or _ more 0 raw) _
    ((BTrue) (RefuteOpen _ head e $ prove-subterm e raw))
    ((BFalse) (RefuteValue _))))

(def-fns _ $ (many refuted-value : (many (Env) env) (many (Res) r) -> (many (Env) out))
  (let ((many env1) (many found)) $ scrutinee-matchable env r)
  (let-match many found (Some _ pr) ((None _) env1))
  (let-match many pr (MkPair _ _ _ info))
  (let-match many info (MkMatchInfo _ _ mctors _))
  (let ((many env2) (many first) (many _) (many _)) $ covered-of mctors env1 (Nil _) r (Erased) (None _) (BFalse) $ Nil _)
  (match many first _
    ((None _) env2)
    ((Some _ c) (env-error-with env2 (forced-error mctors env2 r (Erased) (Cons _ c $ Nil _)) $ str-cat3 (qshow env2 $ res-term r) " : " $ str-cat3 (qshow env2 $ res-ty r) " is not refuted: it may be headed by " $ qshown env2 c))))

(def-fns _ $ (many discs-of : (subterm many (List $ Nat) cs) (many (List $ CShape) ss) -> (many (List $ Nat) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest) (Cons _ (discriminant ss c) $ notail $ discs-of rest ss))))

(def-fns _ $ (many check-coverage : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Nat) seen) -> (many (Env) r))
  (let-match many mctors (Cons _ mc rest) ((Nil _) env))
  (let-match many mc (MkMCtor _ t))
  (let ((many c)) $ term-var t)
  (let ((many n)) $ count-bins seen c)
  (match many (nat-lt 1 n) _
    ((BFalse) (tail $ check-coverage rest env seen))
    ((BTrue) (tail $ check-coverage rest (env-error env $ str-cat3 "constructor " (qshown env c) $ str-cat3 " has " (nat-str n) " branches") seen))))


; The ids at the many positions of a list of multiplicities, in step, as the frame a binder list makes.
(def-fns _ $ (many many-of : (subterm many (List $ Multiplicity) ms) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (let-match many ms (Cons _ m rest) ((Nil _) (Nil _)))
  (let-match many ids (Cons _ x xrest) ((Nil _) (Nil _)))
  (match many m _ ((Many) (Cons _ x $ notail $ many-of rest xrest))
                  ((Once) (Cons _ x $ notail $ many-of rest xrest)) ((Erased) (tail $ many-of rest xrest))))

; Whether a def-fns group binds a many function; a group of erased ones leaves nothing behind (ASSUMPTIONS 77).
; ---- The elaborator proper: one block recursing on the raws it elaborates (self/README.md)

; What the statements read from their raws, holding the parts they elaborate later inside those raws.
(def-adts
  ((Header : ((Syn) f) -> Type)
    enum
    (many MkHeader : (erased (Syn) f) (many (Spot) site) (many (Maybe $ Name) name) (many (Multiplicity) mult) (many (Bool) is-unique) (many (Bool) is-absurd) (many (Bool) is-extern) (many (Bool) is-at) (many (Maybe $ Nat) delegates) (many (Maybe $ Impl) impl) (many (List $ Entry) params) (many (List $ Entry) rets) (many (List $ Nat) sig-ids) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) f) p) -> (Header f)))
  ((Headers : ((List $ Syn) fns) -> Type)
    enum
    (many HStop : (erased (List $ Syn) fns) -> (Headers fns))
    (many HCons : (erased (Syn) f) (erased (List $ Syn) rest) (many (Header f) h) (many (Headers rest) hs) -> (Headers $ Cons (Syn) f rest)))
  ; [gids]: the frame the group binds, its many functions' ids; an erased function is checked and leaves nothing
  ; behind (ASSUMPTIONS 77).
  ((Bound : ((List $ Syn) fns) ((Headers fns) hs) ((List $ Nat) gids) -> Type)
    enum
    (many BStop : (erased (List $ Syn) fns) -> (Bound fns (HStop fns) (Nil (Nat))))
    (many BMany : (erased (Syn) f) (erased (List $ Syn) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Nat) gids) (many (Nat) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Syn) f rest) (HCons f rest h hs) (Cons (Nat) x gids)))
    (many BErased : (erased (Syn) f) (erased (List $ Syn) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Nat) gids) (many (Nat) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Syn) f rest) (HCons f rest h hs) gids)))
  ((AdtHeader : ((Syn) f) -> Type)
    enum
    (many MkAdtHeader : (erased (Syn) f) (many (String) name) (many (Disc) disc) (many (Bool) is-newtype) (many (Bool) is-extern) (many (List $ Syn) ctors) (erased (Subterm (List $ Syn) ctors (Syn) f) p) -> (AdtHeader f)))
  ((AdtHeaders : ((List $ Syn) adts) -> Type)
    enum
    (many AStop : (erased (List $ Syn) adts) -> (AdtHeaders adts))
    (many AHCons : (erased (Syn) f) (erased (List $ Syn) rest) (many (AdtHeader f) h) (many (AdtHeaders rest) hs) -> (AdtHeaders $ Cons (Syn) f rest)))
  ((Tids : ((List $ Syn) adts) ((AdtHeaders adts) hs) -> Type)
    enum
    (many TStop : (erased (List $ Syn) adts) -> (Tids adts $ AStop adts))
    (many TCons : (erased (Syn) f) (erased (List $ Syn) rest) (erased (AdtHeader f) h) (erased (AdtHeaders rest) hs) (many (Nat) x) (many (Tids rest hs) more) -> (Tids (Cons (Syn) f rest) $ AHCons f rest h hs)))
  ((LetParts : ((List $ Syn) args) -> Type)
    enum
    (many MkLetParts : (erased (List $ Syn) args) (many (List $ SrcEntry args) binders) (many (List $ Syn) rhs) (erased (Within rhs args) wr) -> (LetParts args)))
  ((CtorParts : ((Syn) c) -> Type)
    enum
    (many MkCtorParts : (erased (Syn) c) (many (Multiplicity) mult) (many (Maybe $ Name) name) (many (List $ Syn) sg) (erased (Subterm (List $ Syn) sg (Syn) c) p) -> (CtorParts c))))

(def-adts $ (RealBranch : ((List $ List $ Nat) ctx) ((List $ Multiplicity) ns) -> Type)
  enum
  (many MkRealBranch : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (many (Nat) c) (many (List $ Nat) fids) (many (Code (Cons (List (Nat)) fids ctx) ns) code) -> (RealBranch ctx ns)))

(def-fns _ $ (many real-ctors : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ RealBranch ctx ns) bs) -> (many (List $ Nat) r))
  (let-match many bs (Cons _ b rest)
    ((Nil _) (Nil _)))
  (match many b _ ((MkRealBranch _ _ c _ _) (Cons _ c $ notail $ real-ctors _ _ rest))))

(def-fns _ $ (many real-branches-code : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ RealBranch ctx ns) bs) (many (List $ CShape) ss) -> (many (List $ Branch ctx ns) r))
  (let-match many bs (Cons _ b rest) ((Nil _) (Nil _)))
  (match many b _
    ((MkRealBranch _ _ c fids code) (Cons _ (MkBranch _ _ (discriminant ss c) fids code) $ notail $ real-branches-code _ _ rest ss))))

; A header's function bound as soon as the header is read, so a later header of the block sees it (section 53),
; with the `AtFn` proof of a header marked `at`, so a call within the block to the function is skipped (section
; 39), and the `Delegate` proof and placement of its delegate annotation (section 41).
(def-fns _ $ (many bind-header : (erased (Syn) f) (many (Header f) h) (many (Env) env) (many (Nat) lvl) -> (many (Env) r) (many (Nat) x))
  (let-match many h (MkHeader _ hpos name mult uq _ _ isat delegates _ params rets _ _ _))
  (let ((many ty)) $ TFn uq (TVar lvl) params rets)
  (let ((many env1) (many x)) $ bind env name (Some _ $ loc-in env hpos) (BTrue) mult ty (None _) delegate-id)
  (let ((many env2)) $ mark-word env1 x $ BFalse)
  (let ((many env3))
    (match many delegates (((Env) _))
      ((None _) env2)
      ((Some _ df)
        (let ((many env2p)) $ env-place-at env2 x $ slot-atom df)
        (let ((many fty)) $ type-of env2p df)
        (let ((many env2d) (many _)) $ bind-erased env2p (None _) (None _) (BFalse) (Erased) (proof-type delegate-id $ Cons _ (sharing-of-fn env2p ty) $ Cons _ ty $ Cons _ (TVar x) $ Cons _ (sharing-of-fn env2p fty) $ Cons _ fty $ Cons _ (TVar df) $ Nil _) (None _) delegate-id)
        env2d)))
  (let-match many isat (BTrue) ((BFalse) (values env3 x)))
  (let ((many env4) (many p)) $ bind-erased env3 (None _) (None _) (BFalse) (Erased) (proof-type atfn-id $ Cons _ ty $ Cons _ (TVar x) $ Nil _) (None _) delegate-id)
  (values (open-proof env4 p) x))

(def-fns _ $ (many bound-erased : (erased (List $ Syn) fns) (erased (Headers fns) hs) (erased (List $ Nat) gids) (subterm many (Bound fns hs gids) ids) -> (many (List $ Nat) r))
  (match many ids _
    ((BStop _) (Nil _))
    ((BMany _ _ _ _ _ _ more) (tail $ bound-erased _ _ _ more))
    ((BErased _ _ _ _ _ x more) (Cons _ x $ notail $ bound-erased _ _ _ more))))

(def-fns _ $ (many set-settled-states : (subterm many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) cs) (many (Env) env) -> (many (Env) r))
  (let-match many cs (Cons _ p rest) ((Nil _) env))
  (match many p _
    ((MkPair _ _ id v) (tail $ set-settled-states rest $ set-state-closed env id v))))

(def-fns _ $ (many ctor-values : (subterm many (List $ Ctor) cs) -> (many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest) (Cons _ (MkPair _ _ (ctor-id c) $ BCtorFn _ c) $ notail $ ctor-values rest))))

(def-fns _ $ (many mctors-of : (subterm many (List $ Pair (Multiplicity) $ Nat) cs) -> (many (List $ MCtor) r))
  (let-match many cs (Cons _ p rest)
    ((Nil _) (Nil _)))
  (match many p _ ((MkPair _ _ m c) (Cons _ (MkMCtor m $ TVar c) $ notail $ mctors-of rest))))


(def-fns _ $ (many slot-term-of : (many (Env) env) (many (Nat) x) -> (many (Term) t))
  (let-match many (env-slot-of env x) (Some _ s) ((None _) (slot-atom x)))
  (TVar s))

(def-fns _ $ (many slot-pairs : (many (Env) env) (subterm many (List $ Nat) ids) -> (many (List $ Nat) xs) (many (List $ Nat) ss))
  (let-match many ids (Cons _ x rest) ((Nil _) (values (Nil _) (Nil _))))
  (let ((many xs) (many ss)) $ notail $ slot-pairs env rest)
  (let-match many (env-slot-of env x) (Some _ s) ((None _) (values xs ss)))
  (match many (nat-eq s x) (((List $ Nat) _) ((List $ Nat) _)) ((BTrue) (values xs ss)) ((BFalse) (values (Cons _ x xs) (Cons _ s ss)))))

(def-fns _ $ (many abstract-slots : (many (Env) env) (many (List $ Nat) ids) (many (Term) t) -> (many (Term) r))
  (let ((many xs) (many ss)) $ slot-pairs env ids)
  (abstract ids $ mapv t (OpSlots xs ss) 0))

(def-fns _ $ (many abstract-slots-sg : (many (Env) env) (many (List $ Nat) ids) (many (Sg) sg) -> (many (Sg) r))
  (match many sg _
    ((SgTy t) (SgTy $ abstract-slots env ids t))
    ((SgIs t ty) (SgIs (abstract-slots env ids t) $ abstract-slots env ids ty))))

(def-fns _ $ (many bin-ids-of : (subterm many (List $ Term) ts) -> (many (List $ Nat) r))
  (let-match many ts (Cons _ t rest) ((Nil _) (Nil _)))
  (match many t _
    ((TVar x) (Cons _ x $ notail $ bin-ids-of rest)) (else (tail $ bin-ids-of rest))))

; Post-erasure normalization (ASSUMPTIONS 72, 74, 88; lib/elab.ml's check_marks): a let whose right-hand
; side is variables and constants is substituted away, and one whose body returns exactly what it binds is
; replaced by its right-hand side, so a marked call stands in tail position in the code that runs. A
; substitution maps every variable of the code's frames to a variable or a constant of the frames it is
; rewritten into.

(def-adts
  ((Atom : ((List $ List $ Nat) ctx) -> Type)
    enum
    (many AVar : (erased (List $ List $ Nat) ctx) (many (Nat) x) (many (Mem x ctx) p) -> (Atom ctx))
    (many AConst : (erased (List $ List $ Nat) ctx) (many (Nat) x) -> (Atom ctx)))
  ((Ren : ((List $ List $ Nat) from) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many RId : (erased (List $ List $ Nat) ctx) -> (Ren ctx ctx))
    (many RWeak : (erased (List $ Nat) f) (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (Ren from ctx) r) -> (Ren from (Cons (List (Nat)) f ctx)))
    (many RFrame : (erased (List $ Nat) f) (erased (List $ List $ Nat) rest) (erased (List $ List $ Nat) ctx) (many (List $ Atom ctx) atoms) (erased (Lockstep (Nat) (Atom ctx) f atoms) lk) (many (Ren rest ctx) r) -> (Ren (Cons (List (Nat)) f rest) ctx))))

(def-fns _ $ (many atom-code : (erased (List $ List $ Nat) ctx) (many (Atom ctx) a) -> (many (Code ctx many-one) r))
  (match many a _ ((AVar _ x p) (CVar _ x p)) ((AConst _ x) (CConst _ x))))

(def-fns _ $ (many atom-there : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (many (Atom ctx) a) -> (many (Atom (Cons (List (Nat)) f ctx)) r))
  (match many a _ ((AVar _ x p) (AVar _ x $ MThere _ _ _ p)) ((AConst _ x) (AConst _ x))))

(def-fns _ $ (many self-atoms : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (subterm many (List $ AtIn f) ats) -> (many (List $ Atom (Cons (List (Nat)) f ctx)) r) (erased (Lockstep (AtIn f) (Atom (Cons (List (Nat)) f ctx)) ats r) lk))
  (let-match many ats (Cons _ at2 rest) ((Nil _) (values (Nil _) (LsNil _ _))))
  (let ((many r) (erased lk)) $ notail $ self-atoms ctx f rest)
  (let ((many (Atom (Cons (List (Nat)) f ctx)) atom)) $ match many at2 _ ((MkAtIn _ x p) (AVar _ x $ MHere _ _ _ p)))
  (values (Cons _ atom r) (LsCons _ _ at2 atom rest r lk)))

(def-fns _ $ (many ren-weaken : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (Ren from ctx) ren) -> (many (Ren (Cons (List (Nat)) f from) (Cons (List (Nat)) f ctx)) r))
  (let ((many ats) (erased lk)) $ at-ins f)
  (let ((many atoms) (erased lk2)) $ self-atoms ctx _ ats)
  (RFrame _ _ _ atoms (lockstep-trans _ _ _ _ _ _ lk lk2) $ RWeak _ _ _ ren))

(def-fns _ $ (many ren-get : (many (Nat) x) (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (Mem x from) p) (subterm many (Ren from ctx) ren) -> (many (Atom ctx) r))
  (let-match many ren (RFrame _ _ _ atoms lk r)
    ((RId _) (AVar _ x p))
    ((RWeak _ _ _ r) (atom-there _ _ $ notail $ ren-get x _ _ p r)))
  (let-match many p (MHere _ _ _ q)
    ((MThere _ _ _ q) (tail $ ren-get x _ _ q r)))
  (let ((many a) (erased _)) $ at-get _ _ _ q atoms lk)
  a)

; The atoms a let binds, if its right-hand side is nothing but variables and constants.
(def-fns _ $ (many atoms-of : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Atom ctx) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Some _ $ Nil _)))
  (let-match many (notail $ atoms-of _ rest) (Some _ more) ((None _) (None _)))
  (match many c _
    ((CVar _ x p) (Some _ $ Cons _ (AVar _ x p) more))
    ((CConst _ x) (Some _ $ Cons _ (AConst _ x) more)) (else (None $ List $ Atom ctx))))

(def-fns _ $ (many rhs-atoms : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (Code ctx ms) c) -> (many (Maybe $ List $ Atom ctx) r))
  (match many c _
    ((CVar _ x p) (Some _ $ Cons _ (AVar _ x p) $ Nil _))
    ((CConst _ x) (Some _ $ Cons _ (AConst _ x) $ Nil _))
    ((CErased _ _) (Some _ $ Nil _))
    ((CValues _ _ cs _) (atoms-of _ cs)) (else (None $ List $ Atom ctx))))

(def-fns _ $ (many vars-of : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Nat) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Some _ $ Nil _)))
  (let-match many c (CVar _ x _) (else (None $ List $ Nat)))
  (match many (notail $ vars-of _ rest) _
    ((None _) (None _))
    ((Some _ xs) (Some _ $ Cons _ x xs))))

(def-fns _ $ (many bins-eq : (subterm many (List $ Nat) as) (many (List $ Nat) bs) -> (many (Bool) r))
  (let-match many as (Cons _ x rest)
    ((Nil _) (list-is-empty _ bs)))
  (match many bs _ ((Nil _) (BFalse)) ((Cons _ y brest) (and (nat-eq x y) $ notail $ bins-eq rest brest))))

; Whether a body returns exactly the let's ids, in order, with the two erasure lists then agreeing on their many entries.
(def-fns _ $ (many returns-same : (erased (List $ List $ Nat) ctx) (subterm many (List $ Multiplicity) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) _pk) (subterm many (List $ Multiplicity) ns) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ns cs) _qk) -> (many (Maybe $ ManySame ms ns) r))
  (let-match many (vars-of _ cs) (Some _ vars) ((None _) (None _)))
  (match many (bins-eq ids vars) _
    ((BTrue) (mults-same ms ns))
    ((BFalse) (None _))))

; Dropping a frame nothing mentions (lib/elab.ml's constant let): the code rebuilt one frame shorter, or None
; where some variable sits in that frame.
(def-adts
  ((Drop : ((List $ List $ Nat) from) ((List $ List $ Nat) ctx) -> Type)
    enum
    (many DHere : (erased (List $ Nat) f) (erased (List $ List $ Nat) ctx) -> (Drop (Cons (List (Nat)) f ctx) ctx))
    (many DUnder : (erased (List $ Nat) g) (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (Drop from ctx) d) -> (Drop (Cons (List (Nat)) g from) (Cons (List (Nat)) g ctx))))
  ((Kept : (Type A) (Type B) ((List A) xs) -> Type)
    enum
    (many KNo : (erased Type A) (erased Type B) (erased (List A) xs) -> (Kept A B xs))
    (many KYes : (erased Type A) (erased Type B) (erased (List A) xs) (many (List B) ys) (erased (Lockstep A B xs ys) lk) -> (Kept A B xs))))

(def-fns _ $ (many mem-drop : (erased (Nat) x) (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (Mem x from) p) (many (Drop from ctx) d) -> (many (Maybe $ Mem x ctx) r))
  (let-match many d (DUnder _ _ _ d2) ((DHere _ _) (match many p _ ((MHere _ _ _ _) (None _)) ((MThere _ _ _ q) (Some _ q)))))
  (let-match many p (MThere _ _ _ q)
    ((MHere _ _ _ at2) (Some _ $ MHere _ _ _ at2)))
  (match many (notail $ mem-drop _ _ _ q d2) _ ((Some _ q2) (Some _ $ MThere _ _ _ q2)) ((None _) (None _))))

(def-fns _
  ((many strengthen : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code from ms) c) (many (Drop from ctx) d) -> (many (Maybe $ Code ctx ms) r))
    (match many c _
      ((CVar _ x p) (match many (mem-drop _ _ _ p d) _ ((Some _ q) (Some _ $ CVar _ x q)) ((None _) (None _))))
      ((CConst _ x) (Some _ $ CConst _ x))
      ((CValue _ v) (Some _ $ CValue _ v))
      ((CErased _ ms2) (Some _ $ CErased _ ms2))
      ((CValues _ ms2 cs pk)
        (match many (notail $ strengthen-list _ _ cs d) _
          ((KNo _ _ _) (None _))
          ((KYes _ _ _ cs2 lk) (Some _ $ CValues _ ms2 cs2 $ picked-along _ _ _ _ _ pk lk))))
      ((CApp _ ms2 f args cc)
        (let-match many (notail $ strengthen _ _ _ f d) (Some _ f2) ((None _) (None _)))
        (match many (notail $ strengthen-list _ _ args d) _
          ((KNo _ _ _) (None _))
          ((KYes _ _ _ args2 _) (Some _ $ CApp _ ms2 f2 args2 cc))))
      ((CLet _ ms2 _ ids pk rhs rest)
        (let-match many (notail $ strengthen _ _ _ rhs d) (Some _ rhs2) ((None _) (None _)))
        (match many (notail $ strengthen _ _ _ rest $ DUnder _ _ _ d) _
          ((None _) (None _))
          ((Some _ rest2) (Some _ $ CLet _ ms2 _ ids pk rhs2 rest2))))
      ((CLetRec _ _ _ g rest)
        (let-match many g (MkGroup _ ids fns lk))
        (let-match many (notail $ strengthen-fns _ _ ids fns d) (KYes _ _ _ fns2 lk2) ((KNo _ _ _) (None _)))
        (match many (notail $ strengthen _ _ _ rest $ DUnder _ _ _ d) _
          ((None _) (None _))
          ((Some _ rest2) (Some _ $ CLetRec _ _ _ (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2) rest2))))
      ((CMatch _ ns scrut shape bs dfl live)
        (let-match many (notail $ strengthen _ _ _ scrut d) (Some _ scrut2) ((None _) (None _)))
        (let ((many (Maybe $ Shape ctx) shape2))
          (match many shape _
            ((ShKnown _ adt) (Some _ $ ShKnown _ adt))
            ((ShNone _) (Some _ $ ShNone _))
            ((ShHeld _ mc tags) (match many (notail $ strengthen _ _ _ mc d) _ ((None _) (None _)) ((Some _ mc2) (Some _ $ ShHeld _ mc2 tags))))))
        (let-match many shape2 (Some _ sh) ((None _) (None _)))
        (let-match many (notail $ strengthen-branches _ _ ns bs d) (Some _ bs2) ((None _) (None _)))
        (let-match many dfl (Some _ dd) ((None _) (Some _ $ CMatch _ ns scrut2 sh bs2 (None _) live)))
        (match many (notail $ strengthen _ _ _ dd $ DUnder _ _ _ d) _
          ((None _) (None _))
          ((Some _ dd2) (Some _ $ CMatch _ ns scrut2 sh bs2 (Some _ dd2) live))))

      ((CCellAlloc _ ctor slots)
        (match many (notail $ strengthen-list _ _ slots d) _ ((KNo _ _ _) (None _)) ((KYes _ _ _ slots2 _) (Some _ $ CCellAlloc _ ctor slots2))))
      ((CCellWrite _ k2 cell slots)
        (let-match many (notail $ strengthen _ _ _ cell d) (Some _ cell2)
          ((None _) (None _)))
        (match many (notail $ strengthen-slots _ _ slots d) _ ((None _) (None _)) ((Some _ slots2) (Some _ $ CCellWrite _ k2 cell2 slots2))))
      ((CCellCopy _ k2 cell slots)
        (let-match many (notail $ strengthen _ _ _ cell d) (Some _ cell2)
          ((None _) (None _)))
        (match many (notail $ strengthen-slots _ _ slots d) _ ((None _) (None _)) ((Some _ slots2) (Some _ $ CCellCopy _ k2 cell2 slots2))))
      ((CCellRead _ k2 index cell)
        (match many (notail $ strengthen _ _ _ cell d) _ ((None _) (None _)) ((Some _ cell2) (Some _ $ CCellRead _ k2 index cell2))))
      ((CWorldDo _ req)
        (match many (notail $ strengthen _ _ _ req d) _ ((None _) (None _)) ((Some _ req2) (Some _ $ CWorldDo _ req2))))
      ((CPrim _ ms2 p args)
        (match many (notail $ strengthen-list _ _ args d) _
          ((KNo _ _ _) (None _))
          ((KYes _ _ _ args2 _) (Some _ $ CPrim _ ms2 p args2))))
      ((CAbsurd _ ms2) (Some _ $ CAbsurd _ ms2))
      ((CError _ ms2 m) (Some _ $ CError _ ms2 m))))
  ((many strengthen-list : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code from many-one) cs) (many (Drop from ctx) d) -> (many (Kept (Code from many-one) (Code ctx many-one) cs) r))
    (let-match many cs (Cons _ c rest) ((Nil _) (KYes _ _ _ (Nil _) (LsNil _ _))))
    (let-match many (notail $ strengthen _ _ _ c d) (Some _ c2) ((None _) (KNo _ _ _)))
    (match many (notail $ strengthen-list _ _ rest d) _
      ((KNo _ _ _) (KNo _ _ _))
      ((KYes _ _ _ r lk) (KYes _ _ _ (Cons _ c2 r) (LsCons _ _ c c2 rest r lk)))))

  ((many strengthen-slots : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code from many-one) slots) (many (Drop from ctx) d) -> (many (Maybe $ List $ Pair (Nat) $ Code ctx many-one) r))
    (let-match many slots (Cons _ slot rest) ((Nil _) (Some _ $ Nil _)))
    (let-match many slot (MkPair _ _ index code))
    (let-match many (notail $ strengthen _ _ _ code d) (Some _ code2)
      ((None _) (None _)))
    (match many (notail $ strengthen-slots _ _ rest d) _ ((None _) (None _)) ((Some _ rest2) (Some _ $ Cons _ (MkPair _ _ index code2) rest2))))

  ((many strengthen-fns : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids from) fns) (many (Drop from ctx) d) -> (many (Kept (Pair (Nat) $ Func gids from) (Pair (Nat) $ Func gids ctx) fns) r))
    (let-match many fns (Cons _ p rest) ((Nil _) (KYes _ _ _ (Nil _) (LsNil _ _))))
    (let-match many p (MkPair _ _ id fn))
    (let ((many (Maybe $ Func gids ctx) fn2))
      (match many fn _
        ((MkFunc _ _ rets n i ps body impl top)
          (match many (notail $ strengthen _ _ _ body $ DUnder _ _ _ $ DUnder _ _ _ d) _ ((None _) (None _)) ((Some _ body2) (Some _ $ MkFunc _ _ rets n i ps body2 impl top))))
        ((MkAlias _ _ n i target)
          (match many (notail $ strengthen _ _ _ target $ DUnder _ _ _ d) _ ((None _) (None _)) ((Some _ t2) (Some _ $ MkAlias _ _ n i t2))))))
    (let-match many fn2 (Some _ f2) ((None _) (KNo _ _ _)))
    (let-match many (notail $ strengthen-fns _ _ gids rest d) (KYes _ _ _ r lk) ((KNo _ _ _) (KNo _ _ _)))
    (let ((many p2)) $ MkPair _ _ id f2)
    (KYes _ _ _ (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))
  ((many strengthen-branches : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (subterm many (List $ Branch from ns) bs) (many (Drop from ctx) d) -> (many (Maybe $ List $ Branch ctx ns) r))
    (let-match many bs (Cons _ b rest) ((Nil _) (Some _ $ Nil _)))
    (let-match many b (MkBranch _ _ dsc ids body))
    (let-match many (notail $ strengthen _ _ _ body $ DUnder _ _ _ d) (Some _ body2) ((None _) (None _)))
    (match many (notail $ strengthen-branches _ _ ns rest d) _
      ((None _) (None _))
      ((Some _ r) (Some _ $ Cons _ (MkBranch _ _ dsc ids body2) r)))))

; A let's right-hand side of values embedded by elaboration alone, as lib/elab.ml's constant.
(def-fns _ $ (many all-values : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r))
  (let-match many cs (Cons _ c rest)
    ((Nil _) (BTrue)))
  (match many c _ ((CValue _ _) (tail $ all-values _ rest)) (else (BFalse))))

(def-fns _ $ (many constant-rhs : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (many (Code ctx ms) c) -> (many (Bool) r))
  (match many c _ ((CErased _ _) (BTrue)) ((CValue _ _) (BTrue)) ((CValues _ _ cs _) (all-values _ cs)) (else (BFalse))))

(def-fns _ $ (many normal-values : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ms cs) pk) -> (many (Code ctx ms) r))
  (let-match many ms (Cons _ m rest) (else (CValues _ ms cs pk)))
  (let-match many m (Many) (else (CValues _ ms cs pk)))
  (let-match many rest (Nil _) (else (CValues _ ms cs pk)))
  (let-match many cs (Cons _ code more)
    (else (CValues _ ms cs pk)))
  (match many more _ ((Nil _) code) (else (CValues _ ms cs pk))))

(def-fns _
  ((many norm : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (subterm many (Code from ms) c) (many (Ren from ctx) ren) -> (many (Code ctx ms) r))
    (match many c _
      ((CVar _ x p) (atom-code _ $ ren-get x _ _ p ren))
      ((CConst _ x) (CConst _ x))
      ((CValue _ v) (CValue _ v))
      ((CErased _ ms2) (CErased _ ms2))
      ((CValues _ ms2 cs pk)
        (let ((many cs2) (erased lk)) $ notail $ norm-list _ _ cs ren)
        (normal-values _ ms2 cs2 $ picked-along _ _ _ _ _ pk lk))
      ((CApp _ ms2 f as cc)
        (let ((many as2) (erased _)) $ notail $ norm-list _ _ as ren)
        (CApp _ ms2 (notail $ norm _ _ many-one f ren) as2 cc))
      ((CLet _ ms2 _ ids pk rhs rest)
        (let ((many rhs2)) $ notail $ norm _ _ ms2 rhs ren)
        (let ((many (Maybe $ Ren (Cons (List (Nat)) ids from) ctx) dropped))
          (match many (rhs-atoms _ _ rhs2) _
            ((None _) (None _))
            ((Some _ atoms)
              (match many (lockstep-dec _ _ ids atoms) _
                ((LdYes _ _ _ _ lk) (Some _ $ RFrame _ _ _ atoms lk ren))
                ((LdNo _ _ _ _) (None _))))))
        (let-match many dropped (None _) ((Some _ ren2) (tail $ norm _ _ ms rest ren2)))
        (let ((many rest2)) $ notail $ norm _ _ ms rest $ ren-weaken _ _ ids ren)
        (let ((many (Maybe $ ManySame ms2 ms) same))
          (match many rest2 _
            ((CVar _ y p) (returns-same _ ms2 ids pk many-one (Cons _ (CVar _ y p) $ Nil _) $ PkMany _ (Nil _) (CVar _ y p) (Nil _) $ PkNil _))
            ((CValues _ ns3 cs pk3) (returns-same _ ms2 ids pk ns3 cs pk3))
            (else (None _))))
        (let-match many same (None _) ((Some _ p) (recast _ ms ms2 p rhs2)))
        (let ((many (Maybe $ Code ctx ms) gone)) $ match many (constant-rhs _ _ rhs2) _ ((BTrue) (strengthen _ _ _ rest2 $ DHere _ _)) ((BFalse) (None _)))
        (match many gone _
          ((Some _ r) r)
          ((None _) (CLet _ ms2 _ ids pk rhs2 rest2))))
      ((CLetRec _ _ _ g rest) (match many g _ ((MkGroup _ ids _ _) (CLetRec _ _ _ (notail $ norm-group _ _ _ g ren) $ notail $ norm _ _ ms rest $ ren-weaken _ _ ids ren))))
      ((CMatch _ ns scrut shape bs dfl live)
        (let ((many (Maybe $ Code ctx ns) dropped))
          (match many shape _
            ((ShNone _)
              (let-match many bs (Cons _ b rest)
                ((Nil _) (match many dfl _ ((Some _ d) (Some _ $ notail $ norm _ _ ns d $ RFrame _ _ _ (Nil _) (LsNil _ _) ren)) ((None _) (None _)))))
              (let-match many rest (Nil _) ((Cons _ _ _) (None _)))
              (let-match many b (MkBranch _ _ _ ids body))
              (match many ids _
                ((Nil _) (Some _ $ notail $ norm _ _ ns body $ RFrame _ _ _ (Nil _) (LsNil _ _) ren))
                ((Cons _ _ _) (None _))))
            (else (None _))))
        (let-match many dropped (None _) ((Some _ d) d))
        (CMatch _ ns (notail $ norm _ _ many-one scrut ren)
                (match many shape (((Shape ctx) _)) ((ShKnown _ adt) (ShKnown _ adt)) ((ShNone _) (ShNone _)) ((ShHeld _ mc tags) (ShHeld _ (notail $ norm _ _ many-one mc ren) tags)))
                (notail $ norm-branches _ _ ns bs ren)
                (match many dfl (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _)) ((Some _ d) (Some _ $ notail $ norm _ _ ns d $ ren-weaken _ _ (Nil _) ren)) ((None _) (None _)))
                live))

      ((CCellAlloc _ ctor slots)
        (let ((many slots2) (erased _)) $ notail $ norm-list _ _ slots ren)
        (CCellAlloc _ ctor slots2))
      ((CCellWrite _ k2 cell slots) (CCellWrite _ k2 (notail $ norm _ _ many-one cell ren) $ notail $ norm-slots _ _ slots ren))
      ((CCellCopy _ k2 cell slots) (CCellCopy _ k2 (notail $ norm _ _ many-one cell ren) $ notail $ norm-slots _ _ slots ren))
      ((CCellRead _ k2 index cell) (CCellRead _ k2 index $ notail $ norm _ _ many-one cell ren))
      ((CWorldDo _ req) (CWorldDo _ $ notail $ norm _ _ many-one req ren))
      ((CPrim _ ms2 p as)
        (let ((many as2) (erased _)) $ notail $ norm-list _ _ as ren)
        (CPrim _ ms2 p as2))
      ((CAbsurd _ ms2) (CAbsurd _ ms2))
      ((CError _ ms2 m) (CError _ ms2 m))))
  ((many norm-list : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code from many-one) cs) (many (Ren from ctx) ren) -> (many (List $ Code ctx many-one) r) (erased (Lockstep (Code from many-one) (Code ctx many-one) cs r) lock))
    (let-match many cs (Cons _ c rest) ((Nil _) (values (Nil _) (LsNil _ _))))
    (let ((many r) (erased p)) $ notail $ norm-list _ _ rest ren)
    (let ((many c2)) $ notail $ norm _ _ many-one c ren)
    (values (Cons _ c2 r) (LsCons _ _ c c2 rest r p)))

  ((many norm-slots : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code from many-one) slots) (many (Ren from ctx) ren) -> (many (List $ Pair (Nat) $ Code ctx many-one) r))
    (let-match many slots (Cons _ slot rest)
      ((Nil _) (Nil _)))
    (match many slot _ ((MkPair _ _ index code) (Cons _ (MkPair _ _ index $ notail $ norm _ _ many-one code ren) $ notail $ norm-slots _ _ rest ren))))

  ((many norm-group : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (erased (List $ Nat) gids) (subterm many (Group gids from) g) (many (Ren from ctx) ren) -> (many (Group gids ctx) r))
    (let-match many g (MkGroup _ ids fns lk))
    (let ((many fns2) (erased lk2)) $ notail $ norm-fns _ _ ids fns ren)
    (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2))
  ((many norm-fns : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids from) fns) (many (Ren from ctx) ren) -> (many (List $ Pair (Nat) $ Func gids ctx) r) (erased (Lockstep (Pair (Nat) $ Func gids from) (Pair (Nat) $ Func gids ctx) fns r) lk))
    (let-match many fns (Cons _ p rest) ((Nil _) (values (Nil _) (LsNil _ _))))
    (let ((many r) (erased lk)) $ notail $ norm-fns _ _ gids rest ren)
    (let-match many p (MkPair _ _ id fn))
    (let ((many (Func gids ctx) fn2))
      (match many fn _
        ((MkFunc _ _ rets n i ps body impl top) (MkFunc _ _ rets n i ps (notail $ norm _ _ rets body $ ren-weaken _ _ ps $ ren-weaken _ _ gids ren) impl top))
        ((MkAlias _ _ n i target) (MkAlias _ _ n i $ notail $ norm _ _ many-one target $ ren-weaken _ _ gids ren))))
    (let ((many p2)) $ MkPair _ _ id fn2)
    (values (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))
  ((many norm-branches : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (subterm many (List $ Branch from ns) bs) (many (Ren from ctx) ren) -> (many (List $ Branch ctx ns) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (Nil _)))
    (match many b _ ((MkBranch _ _ d ids body) (Cons _ (MkBranch _ _ d ids $ notail $ norm _ _ ns body $ ren-weaken _ _ ids ren) $ notail $ norm-branches _ _ ns rest ren)))))

(def-fns _ $ (many chain-ren : (erased (List $ List $ Nat) c0) (erased (List $ List $ Nat) c1) (erased (List $ List $ Nat) c2) (subterm many (StmtCode c1 c2) sc) (many (Ren c0 c1) r) -> (many (Ren c0 c2) r2))
  (match many sc _
    ((SNone _) r)
    ((SLet _ _ _ _ _) (RWeak _ _ _ r))
    ((SLetRec _ _ _) (RWeak _ _ _ r))
    ((SMatch _ _ _ _ _) (RWeak _ _ _ r))
    ((SSeq _ _ _ a b) (tail $ chain-ren _ _ _ b $ notail $ chain-ren _ _ _ a r))))

(def-fns _ $ (many weaken-along : (erased (List $ List $ Nat) c1) (erased (List $ List $ Nat) c2) (many (List $ Multiplicity) ms) (many (StmtCode c1 c2) sc) (many (Code c1 ms) code) -> (many (Code c2 ms) r))
  (norm _ _ ms code $ chain-ren _ _ _ sc $ RId _))

(def-fns _ $ (many bind-lift : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) ns) (many (List $ Nat) ids) (erased (List $ Nat) frame)
    (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (Code (Cons (List (Nat)) ids (Cons (List (Nat)) frame ctx)) ns) r))
  (norm _ _ ns rest $ ren-weaken _ _ ids $ RWeak _ _ _ $ RId ctx))

(def-fns _
  ((many bind-through : (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Multiplicity) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk)
      (subterm many (Code ctx ms) rhs) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (Code ctx ns) r))
    (match many rhs _
      ((CLet _ first _ frame fpk value body)
        (CLet _ first _ frame fpk value $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest))
      ((CLetRec _ _ _ group body)
        (match many group _ ((MkGroup _ frame _ _)
          (CLetRec _ _ _ group $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest))))
      ((CMatch _ _ scrut shape branches dflt live)
        (let-match many (rhs-atoms _ _ rest) (Some _ _) ((None _) (CLet _ ms _ ids pk rhs rest)))
        (CMatch _ ns scrut shape (notail $ bind-through-branches ctx ms ns ids pk branches rest)
          (match many dflt (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _))
            ((None _) (None _))
            ((Some _ body) (Some _ $ notail $ bind-through (Cons _ (Nil _) ctx) ms ns ids pk body $ bind-lift ctx ns ids (Nil _) rest))) live))
      (else (CLet _ ms _ ids pk rhs rest))))
  ((many bind-through-branches : (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (List $ Multiplicity) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk)
      (subterm many (List $ Branch ctx ms) branches) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (List $ Branch ctx ns) r))
    (let-match many branches (Cons _ branch more) ((Nil _) (Nil _)))
    (match many branch _ ((MkBranch _ _ disc frame body)
      (Cons _ (MkBranch _ _ disc frame $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest)
        $ notail $ bind-through-branches ctx ms ns ids pk more rest)))))

(def-fns _
  ((many distribute : (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) -> (many (Code ctx ms) r))
    (match many code _
      ((CLet _ first _ ids pk rhs rest)
        (bind-through ctx first ms ids pk (notail $ distribute ctx first rhs) $ notail $ distribute (Cons _ ids ctx) ms rest))
      ((CLetRec _ _ _ group rest)
        (let-match many group (MkGroup _ ids fns lk))
        (let ((many fs) (erased lk2)) $ notail $ distribute-fns ctx ids fns)
        (CLetRec _ _ _ (MkGroup _ ids fs $ lockstep-trans _ _ _ _ _ _ lk lk2) $ notail $ distribute (Cons _ ids ctx) ms rest))
      ((CMatch _ _ scrut shape branches dflt live)
        (CMatch _ ms (notail $ distribute ctx many-one scrut)
          (match many shape (((Shape ctx) _)) ((ShKnown _ _) shape) ((ShNone _) shape) ((ShHeld _ mc adt) (ShHeld _ (notail $ distribute ctx many-one mc) adt)))
          (notail $ distribute-branches ctx ms branches)
          (match many dflt (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ms) _)) ((None _) (None _)) ((Some _ body) (Some _ $ notail $ distribute (Cons _ (Nil _) ctx) ms body))) live))
      ((CValues _ _ values2 pk)
        (let ((many vs) (erased lk)) $ notail $ distribute-list ctx values2)
        (CValues _ ms vs $ picked-along _ _ _ _ _ pk lk))
      ((CApp _ _ fn args cc)
        (let ((many as) (erased _)) $ notail $ distribute-list ctx args)
        (CApp _ ms (notail $ distribute ctx many-one fn) as cc))
      ((CCellAlloc _ ctor slots)
        (let ((many ss) (erased _)) $ notail $ distribute-list ctx slots)
        (CCellAlloc _ ctor ss))
      ((CCellWrite _ k2 cell slots) (CCellWrite _ k2 (notail $ distribute ctx many-one cell) $ notail $ distribute-slots ctx slots))
      ((CCellCopy _ k2 cell slots) (CCellCopy _ k2 (notail $ distribute ctx many-one cell) $ notail $ distribute-slots ctx slots))
      ((CCellRead _ k2 index cell) (CCellRead _ k2 index $ notail $ distribute ctx many-one cell))
      ((CWorldDo _ req) (CWorldDo _ $ notail $ distribute ctx many-one req))
      ((CPrim _ _ p args)
        (let ((many as) (erased _)) $ notail $ distribute-list ctx args)
        (CPrim _ ms p as))
      (else code)))
  ((many distribute-list : (many (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) codes) ->
      (many (List $ Code ctx many-one) r) (erased (Lockstep (Code ctx many-one) (Code ctx many-one) codes r) lk))
    (let-match many codes (Cons _ code rest) ((Nil _) (values (Nil _) $ LsNil _ _)))
    (let ((many c)) $ notail $ distribute ctx many-one code)
    (let ((many cs) (erased lk)) $ notail $ distribute-list ctx rest)
    (values (Cons _ c cs) $ LsCons _ _ code c rest cs lk))
  ((many distribute-slots : (many (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (many (List $ Pair (Nat) $ Code ctx many-one) r))
    (let-match many slots (Cons _ slot rest) ((Nil _) (Nil _)))
    (match many slot _ ((MkPair _ _ index code)
      (Cons _ (MkPair _ _ index $ notail $ distribute ctx many-one code) $ notail $ distribute-slots ctx rest))))
  ((many distribute-branches : (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (subterm many (List $ Branch ctx ms) branches) -> (many (List $ Branch ctx ms) r))
    (let-match many branches (Cons _ branch rest) ((Nil _) (Nil _)))
    (match many branch _ ((MkBranch _ _ disc ids body)
      (Cons _ (MkBranch _ _ disc ids $ notail $ distribute (Cons _ ids ctx) ms body) $ notail $ distribute-branches ctx ms rest))))
  ((many distribute-fns : (many (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) ->
      (many (List $ Pair (Nat) $ Func gids ctx) r) (erased (Lockstep (Pair (Nat) $ Func gids ctx) (Pair (Nat) $ Func gids ctx) fns r) lk))
    (let-match many fns (Cons _ pair rest) ((Nil _) (values (Nil _) $ LsNil _ _)))
    (let-match many pair (MkPair _ _ id fn))
    (let ((many (Func gids ctx) fn2))
      (match many fn _
        ((MkFunc _ _ ms name fid ps body impl top) (MkFunc _ _ ms name fid ps (notail $ distribute (Cons _ ps $ Cons _ gids ctx) ms body) impl top))
        ((MkAlias _ _ _ _ _) fn)))
    (let ((many p)) $ MkPair _ _ id fn2)
    (let ((many more) (erased lk)) $ notail $ distribute-fns ctx gids rest)
    (values (Cons _ p more) $ LsCons _ _ pair p rest more lk)))

(def-fns _ $ (many normalize : (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) ms) (many (Code ctx ms) code) -> (many (Code ctx ms) r))
  (norm _ _ ms (distribute ctx ms $ norm _ _ ms code $ RId ctx) $ RId ctx))

; Normalized code that erases to nothing, or to a reordering of variables (sections 39, 40; ASSUMPTIONS
; 207): renames, loads and a match whose every branch erases to nothing, dispatch included; never a store,
; an allocation, a copy or a call that was not skipped.
(def-fns _
  ((many erases-to-nothing : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ _ _ _) (BFalse))
      ((CCellAlloc _ _ _) (BFalse))
      ((CCellWrite _ _ _ _) (BFalse))
      ((CCellCopy _ _ _ _) (BFalse))
      ((CCellRead _ _ _ cell) (tail $ erases-to-nothing _ _ cell))
      ((CWorldDo _ _) (BFalse))
      ((CPrim _ _ _ _) (BFalse))
      ((CValues _ _ cs _) (tail $ erases-list _ cs))
      ((CLet _ _ _ _ _ rhs rest) (and (notail $ erases-to-nothing _ _ rhs) $ notail $ erases-to-nothing _ _ rest))
      ((CLetRec _ _ _ _ rest) (tail $ erases-to-nothing _ _ rest))
      ((CMatch _ _ scrut shape bs dfl _)
        (and (notail $ erases-to-nothing _ _ scrut)
          $ and (match many shape (((Bool) _)) ((ShHeld _ mc _) (notail $ erases-to-nothing _ _ mc)) (else (BTrue)))
          $ and (notail $ erases-branches _ _ bs) $ match many dfl (((Bool) _)) ((Some _ d) (notail $ erases-to-nothing _ _ d)) ((None _) (BTrue))))
      (else (BTrue))))
  ((many erases-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BTrue))
      ((Cons _ c rest) (and (notail $ erases-to-nothing _ _ c) $ notail $ erases-list _ rest))))
  ((many erases-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BTrue)))
    (match many b _ ((MkBranch _ _ _ _ body) (and (notail $ erases-to-nothing _ _ body) $ notail $ erases-branches _ _ rest)))))


; ---- tail and delegate (section 19): judged on the normalized post-erasure code, per
; function, so a nested def-fns's marks are its own.

(def-fns _ $ (many cc-marked : (many (CC) cc) (many (Bool) only-delegate) -> (many (Bool) r))
  (match many cc _ ((CCTail) (not only-delegate)) ((CCDelegate) (BTrue)) (else (BFalse))))

(def-fns _ $ (many marked-call : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) (many (CC) cc) -> (many (Bool) r))
  (match many code _
    ((CApp _ _ _ _ cc2) (cc-eq cc cc2))
    ((CLet _ _ _ _ _ rhs rest) (or (notail $ marked-call _ _ rhs cc) $ notail $ marked-call _ _ rest cc))
    (else (BFalse))))

(def-fns _
  ((many has-marked : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) (many (Bool) only) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ f args cc) (or (cc-marked cc only) $ or (notail $ has-marked _ _ f only) $ notail $ has-marked-list _ args only))

      ((CCellAlloc _ _ slots) (tail $ has-marked-list _ slots only))
      ((CCellWrite _ _ cell slots) (or (notail $ has-marked _ _ cell only) $ notail $ has-marked-slots _ slots only))
      ((CCellCopy _ _ cell slots) (or (notail $ has-marked _ _ cell only) $ notail $ has-marked-slots _ slots only))
      ((CCellRead _ _ _ cell) (tail $ has-marked _ _ cell only))
      ((CWorldDo _ req) (tail $ has-marked _ _ req only))
      ((CPrim _ _ _ args) (tail $ has-marked-list _ args only))
      ((CValues _ _ cs _) (tail $ has-marked-list _ cs only))
      ((CLet _ _ _ _ _ rhs rest) (or (notail $ has-marked _ _ rhs only) $ notail $ has-marked _ _ rest only))
      ((CLetRec _ _ _ _ rest) (tail $ has-marked _ _ rest only))
      ((CMatch _ _ scrut shape bs dfl _) (or (notail $ has-marked _ _ scrut only) $ or (match many shape (((Bool) _)) ((ShKnown _ _) (BFalse)) ((ShNone _) (BFalse)) ((ShHeld _ mc _) (notail $ has-marked _ _ mc only))) $ or (notail $ has-marked-branches _ _ bs only) $ match many dfl (((Bool) _)) ((Some _ d) (notail $ has-marked _ _ d only)) ((None _) (BFalse)))) (else (BFalse))))
  ((many has-marked-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Bool) only) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BFalse))
      ((Cons _ c rest) (or (notail $ has-marked _ _ c only) $ notail $ has-marked-list _ rest only))))

  ((many has-marked-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Bool) only) -> (many (Bool) r))
    (let-match many slots (Cons _ slot rest)
      ((Nil _) (BFalse)))
    (match many slot _ ((MkPair _ _ _ code) (or (notail $ has-marked _ _ code only) $ notail $ has-marked-slots _ rest only))))

  ((many has-marked-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) only) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BFalse)))
    (match many b _ ((MkBranch _ _ _ _ body) (or (notail $ has-marked _ _ body only) $ notail $ has-marked-branches _ _ rest only)))))

; Every marked call sits in tail position: the body's final call, through lets, let recs and match branches
; for tail, directly for delegate.
(def-fns _
  ((many tails-ok : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) (many (Bool) direct) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ f args _) (and (not $ has-marked _ _ f $ BFalse) $ not $ has-marked-list _ args $ BFalse))
      ((CLet _ _ _ _ _ rhs rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ c $ BFalse))
          ((BFalse) (and (not $ has-marked _ _ rhs $ BFalse) $ notail $ tails-ok _ _ rest direct))))
      ((CLetRec _ _ _ _ rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ rest $ BFalse))
          ((BFalse) (tail $ tails-ok _ _ rest direct))))
      ((CMatch _ _ scrut shape bs dfl _)
        (let-match many direct (BFalse) ((BTrue) (not $ has-marked _ _ c $ BFalse)))
        (and (not $ has-marked _ _ scrut $ BFalse)
          (and (match many shape (((Bool) _)) ((ShKnown _ _) (BTrue)) ((ShNone _) (BTrue)) ((ShHeld _ mc _) (not $ has-marked _ _ mc $ BFalse)))
            (and (notail $ tails-ok-branches _ _ bs direct)
              $ match many dfl (((Bool) _)) ((Some _ d) (notail $ tails-ok _ _ d direct)) ((None _) (BTrue))))))

      ((CCellAlloc _ _ slots) (not $ has-marked-list _ slots $ BFalse))
      ((CCellWrite _ _ cell slots) (and (not $ has-marked _ _ cell $ BFalse) $ not $ has-marked-slots _ slots $ BFalse))
      ((CCellCopy _ _ cell slots) (and (not $ has-marked _ _ cell $ BFalse) $ not $ has-marked-slots _ slots $ BFalse))
      ((CCellRead _ _ _ cell) (not $ has-marked _ _ cell $ BFalse))
      ((CWorldDo _ req) (not $ has-marked _ _ req $ BFalse))
      ((CPrim _ _ _ args) (not $ has-marked-list _ args $ BFalse))
      ((CValues _ _ cs _) (not $ has-marked-list _ cs $ BFalse)) (else (BTrue))))
  ((many tails-ok-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) direct) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BTrue)))
    (match many b _ ((MkBranch _ _ _ _ body) (and (notail $ tails-ok _ _ body direct) $ notail $ tails-ok-branches _ _ rest direct)))))

; Every call with whether it sits in tail position, as tails-ok reads it: a notail call there is refused, and
; an unmarked same-level call warns, naming the mark that fits.
(def-fns _ $ (many report-call : (many (CC) cc) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
  (let-match many cc (CCSame l callee)
    ((CCNoTail) (refuse-when env in-tail "a `notail`-marked call is in tail position"))
    (else env))
  (env-warn-at env l $ str-cat3 "same-level call to " callee $ str-cat " is unmarked; mark it "
    $ tick $ spell env $ match many in-tail (((String) _)) ((BTrue) "tail") ((BFalse) "notail")))

(def-fns _
  ((many call-report : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
    (match many c _
      ((CApp _ _ f args cc)
        (let ((many env1)) $ report-call cc in-tail env)
        (let ((many env2)) $ notail $ call-report _ _ f (BFalse) env1)
        (tail $ call-report-list _ args env2))
      ((CCellAlloc _ _ slots) (tail $ call-report-list _ slots env))
      ((CCellWrite _ _ cell slots)
        (let ((many env1)) $ notail $ call-report _ _ cell (BFalse) env)
        (tail $ call-report-slots _ slots env1))
      ((CCellCopy _ _ cell slots)
        (let ((many env1)) $ notail $ call-report _ _ cell (BFalse) env)
        (tail $ call-report-slots _ slots env1))
      ((CCellRead _ _ _ cell) (tail $ call-report _ _ cell (BFalse) env))
      ((CWorldDo _ req) (tail $ call-report _ _ req (BFalse) env))
      ((CPrim _ _ _ args) (tail $ call-report-list _ args env))
      ((CValues _ _ cs _) (tail $ call-report-list _ cs env))
      ((CLet _ _ _ _ _ rhs rest)
        (let ((many env1)) $ notail $ call-report _ _ rhs (BFalse) env)
        (tail $ call-report _ _ rest in-tail env1))
      ((CLetRec _ _ _ _ rest) (tail $ call-report _ _ rest in-tail env))
      ((CMatch _ _ scrut shape bs dfl _)
        (let ((many env1)) $ match many shape (((Env) _)) ((ShHeld _ mc _) (notail $ call-report _ _ mc (BFalse) env)) (else env))
        (let ((many env2)) $ notail $ call-report _ _ scrut (BFalse) env1)
        (let ((many env3)) $ notail $ call-report-branches _ _ bs in-tail env2)
        (match many dfl _ ((Some _ d) (tail $ call-report _ _ d in-tail env3)) ((None _) env3)))
      (else env)))
  ((many call-report-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) -> (many (Env) r))
    (let-match many cs (Cons _ c rest)
      ((Nil _) env))
    (let ((many env1)) $ notail $ call-report _ _ c (BFalse) env)
    (tail $ call-report-list _ rest env1))
  ((many call-report-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Env) env) -> (many (Env) r))
    (let-match many slots (Cons _ slot rest) ((Nil _) env))
    (let-match many slot (MkPair _ _ _ code))
    (let ((many env1)) $ notail $ call-report _ _ code (BFalse) env)
    (tail $ call-report-slots _ rest env1))
  ((many call-report-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
    (let-match many bs (Cons _ b rest) ((Nil _) env))
    (let-match many b (MkBranch _ _ _ _ body))
    (let ((many env1)) $ notail $ call-report _ _ body in-tail env)
    (tail $ call-report-branches _ _ rest in-tail env1)))

; Validates the marks in a body and returns the normalized code and, for a delegate, the callee (section 19).
(def-fns _ $ (many check-marks : (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) pids) (many (List $ Multiplicity) ms) (many (Code ctx ms) code) -> (many (Env) r) (many (Code ctx ms) code2) (many (Maybe $ Nat) delegated))
  (let ((many code2)) $ normalize ctx ms code)
  (let ((many delegate2)) $ has-marked _ _ code2 $ BTrue)
  (let ((many (String) kind)) $ match many delegate2 _ ((BTrue) "delegate") ((BFalse) "tail"))
  (let ((many env0)) $ call-report _ _ code2 (BTrue) env)
  (let ((many env1)) $ error-unless env0 (tails-ok _ _ code2 delegate2) $ str-cat3 "a " (tick kind) "-marked call is not in tail position")
  (let-match many delegate2 (BTrue) ((BFalse) (values env1 code2 $ None _)))
  (let ((many (Maybe $ Pair (Nat) $ List $ Code ctx many-one) call))
    (match many code2 _
      ((CApp _ _ f args _) (match many f _ ((CVar _ g _) (Some _ $ MkPair _ _ g args)) ((CConst _ g) (Some _ $ MkPair _ _ g args)) (else (None _)))) (else (None _))))
  (let-match many call (Some _ pr)
    ((None _) (values (env-error env1 (say env1 "`delegate` needs exactly one call to a named function")) code2 $ None _)))
  (let-match many pr (MkPair _ _ g args))
  (let ((many straight)) $ match many (vars-of _ args) (((Bool) _)) ((None _) (BFalse)) ((Some _ ids) (bins-eq ids pids)))
  (match many straight _
    ((BTrue) (values env1 code2 $ Some _ g))
    ((BFalse) (values (env-error env1 (say env1 "a `delegate` call must pass the function's non-erased parameters straight through")) code2 $ None _))))


; A call's decrease annotation (section 19): (predates p) right after the callee, or (subterm p) right before
; the decreasing argument, whose position it carries; a written proof p sits inside the call's arguments
; root, and _ or no annotation at all leaves the proof to the elaborator (DESIGN.md section 48).
(def-adts $ (Given : ((List $ Syn) root) -> Type)
  enum
  (many Inferred : (erased (List $ Syn) root) -> (Given root))
  (many Written : (erased (List $ Syn) root) (many (Syn) p) (erased (Subterm (Syn) p (List $ Syn) root) q) -> (Given root)))

(def-adts $ (Ann : ((List $ Syn) root) -> Type)
  enum
  (many AnnNone : (erased (List $ Syn) root) -> (Ann root))
  (many AnnPredates : (erased (List $ Syn) root) (many (Spot) ap) (many (Given root) g) -> (Ann root))
  (many AnnSubterm : (erased (List $ Syn) root) (many (Spot) ap) (many (Nat) i) (many (Given root) g) -> (Ann root)))

(def-fns _ $ (many given-of : (erased (List $ Syn) root) (many (Syn) p) (erased (Subterm (Syn) p (List $ Syn) root) q) -> (many (Given root) g))
  (match many (is-underscore p) _ ((BTrue) (Inferred _)) ((BFalse) (Written _ p q))))

(def-fns _ $ (many ann-of : (many (Env) env) (many (Syn) arg) (many (Nat) i) (erased (List $ Syn) root) (erased (Subterm (Syn) arg (List $ Syn) root) pa) -> (many (Ann root) r))
  (let-match many arg (RList _ items) (else (AnnNone root)))
  (let-match many items (Cons _ k krest) ((Nil _) (AnnNone _)))
  (let-match many krest (Cons _ p prest) ((Nil _) (AnnNone _)))
  (let-match many prest (Nil _) ((Cons _ _ _) (AnnNone _)))
  (let ((erased pp)) $ subterm-trans (prove-subterm p arg) pa)
  (let-match many (is-mark env k $ MkPredates) (BFalse)
    ((BTrue) (AnnPredates _ (raw-pos arg) $ given-of _ p pp)))
  (match many (is-mark env k $ MkSubterm) _ ((BTrue) (AnnSubterm _ (raw-pos arg) i $ given-of _ p pp)) ((BFalse) (AnnNone _))))

; The annotation and the arguments without it.
(def-fns _ $ (many split-annotation : (subterm many (List $ Syn) args) (erased (List $ Syn) root) (erased (Within args root) w) (many (Env) env) (many (Nat) i) -> (many (Env) env2) (many (Ann root) ann) (many (List $ Sub root) rest))
  (let-match many args (Cons _ arg more) ((Nil _) (values env (AnnNone _) $ Nil _)))
  (let ((erased pa)) $ in-within _ _ _ _ (prove-subterm arg args) w)
  (let ((erased wm)) $ within-step _ _ _ (prove-subterm more args) w)
  (let ((many ann)) $ ann-of env arg i _ pa)
  (let-match many ann (AnnNone _)
    (else
      (let ((many env1) (many later) (many rest)) $ notail $ split-annotation more _ wm env i)
      (let ((many env2)) $ match many ann (((Env) _))
        ((AnnPredates _ ap _) (match many (nat-is-zero i) _ ((BTrue) env1) ((BFalse) (error-at env1 ap $ say env "`predates` is written immediately after the callee"))))
        (else env1))
      (let ((many (String) twice)) "a call carries at most one decrease annotation")
      (values (match many later (((Env) _)) ((AnnNone _) env2) ((AnnPredates _ ap _) (error-at env2 ap twice)) ((AnnSubterm _ ap _ _) (error-at env2 ap twice))) ann rest)))
  (let ((many env1) (many ann2) (many rest)) $ notail $ split-annotation more _ wm env $ Succ i)
  (values env1 ann2 $ Cons _ (MkSub _ arg pa) rest))

(def-fns _ $ (many subterm-indices : (subterm many (List $ Entry) tele) (many (Nat) i) -> (many (List $ Nat) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (Nil _)))
  (match many (entry-sub e) _
    ((BTrue) (Cons _ i $ notail $ subterm-indices rest $ Succ i))
    ((BFalse) (tail $ subterm-indices rest $ Succ i))))

; A bare call's annotation (DESIGN.md section 48): where the levels differ, otherwise at the
; first subterm argument that differs from its counterpart; a written annotation stays as it is.
(def-fns _ $ (many first-differing : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) -> (many (Maybe $ Nat) r))
  (let-match many positions (Cons _ pi rest) ((Nil _) (None _)))
  (let-match many (list-nth _ (env-subterms env) j) (NthHit _ _ _ counterpart _) ((NthMiss _ _ _ _) (None _)))
  (match many (equal-env env (nth-term args pi) $ TVar counterpart) _
    ((BFalse) (Some _ pi))
    ((BTrue) (tail $ first-differing rest env args $ Succ j))))

(def-fns _ $ (many here-pos : (many (Env) env) -> (many (Spot) p))
  (match many (env-loc env) _ ((MkLoc _ p) p)))

(def-fns _ $ (many lower-level-hint : (many (Env) env) (many (Res) callee) -> (many (String) s))
  (let-match many (env-enclosing env) (Some _ g) ((None _) ""))
  (match many (equal-env env (res-term callee) $ TVar g) _
    ((BTrue) "")
    ((BFalse) (str-cat3 "\nhint: a call to a strictly lower level needs no decreasing argument; consider defining " (qshow env $ res-term callee) $ str-cat3 " at a lower level, or " (qshow env $ TVar g) " at a higher one"))))

(def-fns _ $ (many resolve-ann : (many (Env) env) (erased (List $ Syn) root) (many (Ann root) ann) (many (Res) callee) (many (Bool) same) (many (List $ Nat) positions) (many (List $ Term) args) -> (many (Env) r) (many (Ann root) a))
  (let-match many ann (AnnNone _) (else (values env ann)))
  (let-match many same (BTrue) ((BFalse) (values env $ AnnPredates _ (here-pos env) $ Inferred _)))
  (match many (first-differing positions env args 0) _
    ((Some _ i) (values env $ AnnSubterm _ (here-pos env) i $ Inferred _))
    ((None _) (values (env-error env $ str-cat3 "same-level call to " (qshow env $ res-term callee) $ str-cat " decreases no subterm argument" $ lower-level-hint env callee) $ AnnNone _))))

(def-fns _ $ (many index-of-nat : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many xs (Cons _ y rest)
    ((Nil _) (None _)))
  (match many (nat-cmp x y) _ ((CEq _ _ _) (Some _ i)) (else (tail $ index-of-nat rest x $ Succ i))))

; Earlier subterm arguments must equal their counterparts (section 19's lexicographic discipline).
(def-fns _ $ (many param-label : (many (Callee) c) (many (List $ Entry) params) (many (Nat) i) -> (many (String) s))
  (argument-label c (Succ i) $ match many (list-nth _ params i) (((Maybe $ Name) _)) ((NthHit _ _ _ e _) (entry-name e)) ((NthMiss _ _ _ _) (None _))))

(def-fns _ $ (many no-counterpart : (many (Env) env) (many (Spot) ap) (many (Callee) desc) (many (List $ Entry) params) (many (Nat) i) (many (Nat) k) -> (many (Env) r))
  (let ((many g) (many gnotes)) $ match many (env-enclosing env) (((String) _) ((List $ Pair (Loc) $ String) _))
    ((Some _ f) (values (str-cat3 " " (kind-name env $ type-of env f) $ str-cat " " $ qshown env f) (declared-as env f)))
    ((None _) (values "" (Nil _))))
  (let ((many notes) (erased _)) $ list-append _ (callee-notes desc) gnotes)
  (error-at-with env ap notes $ str-cat3 (param-label desc params i) (say env " is its `subterm` parameter ")
    $ str-cat3 (nat-str $ Succ k) (str-cat ", but the enclosing" g) $ str-cat " has " $ match many k (((String) _)) ((Zero) "none") (else (str-cat "only " $ nat-str k))))

(def-fns _ $ (many subterm-notes : (many (Env) env) (many (Callee) desc) (many (List $ Entry) params) (many (List $ Spot) sites) (subterm many (List $ Nat) positions) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many positions (Cons _ pi rest) ((Nil _) (Nil _)))
  (let ((many p)) $ match many (list-nth _ sites pi) (((Spot) _)) ((NthHit _ _ _ x _) x) ((NthMiss _ _ _ _) (here-pos env)))
  (Cons _ (MkPair _ _ (loc-in env p) $ str-cat (param-label desc params pi) $ say env " is a `subterm` parameter") $ notail $ subterm-notes env desc params sites rest))

(def-fns _ $ (many not-subterm-param : (many (Env) env) (many (Spot) ap) (many (Callee) desc) (many (List $ Entry) params) (many (List $ Spot) sites) (many (List $ Nat) positions) (many (Nat) i) -> (many (Env) r))
  (let ((many notes) (erased _)) $ list-append _ (subterm-notes env desc params sites positions) $ callee-notes desc)
  (error-at-with env ap notes $ str-cat (param-label desc params i) $ say env " is not a `subterm` parameter"))

(def-fns _ $ (many sub-raws : (erased (List $ Syn) root) (subterm many (List $ Sub root) subs) -> (many (List $ Syn) r))
  (let-match many subs (Cons _ s rest) ((Nil _) (Nil _)))
  (match many s _ ((MkSub _ arg _) (Cons _ arg $ notail $ sub-raws _ rest))))

(def-fns _ $ (many sub-positions : (erased (List $ Syn) root) (subterm many (List $ Sub root) subs) -> (many (List $ Spot) r))
  (let-match many subs (Cons _ s rest) ((Nil _) (Nil _)))
  (match many s _ ((MkSub _ arg _) (Cons _ (raw-pos arg) $ notail $ sub-positions _ rest))))

(def-fns _ $ (many subterm-provable-at : (many (Env) env) (many (List $ Entry) params) (many (List $ Term) args) (many (Nat) i) -> (many (Bool) r))
  (let-match many (index-of-nat (subterm-indices params 0) i 0) (Some _ k) ((None _) (BFalse)))
  (let-match many (list-nth _ (env-subterms env) k) (NthHit _ _ _ counterpart _) ((NthMiss _ _ _ _) (BFalse)))
  (provable-subterm env (nth-term args i) $ TVar counterpart))

(def-fns _ $ (many unneeded : (erased (List $ Syn) root) (many (Ann root) ann) (many (Env) env) (many (Env) checked) (many (Term) lv) (many (List $ Entry) params) (many (List $ Term) args) -> (many (Env) r))
  (let-match many (env-failed checked) (BFalse) ((BTrue) checked))
  (let-match many (env-level env) (Some _ cur) ((None _) checked))
  (let ((many (Spot) ap) (many (String) kw) (many (Bool) drop))
    (match many ann (((Spot) p) ((String) k) ((Bool) d))
      ((AnnNone _) (values (here-pos env) "" (BFalse)))
      ((AnnPredates _ p0 _) (values p0 "predates" $ match many (canon-env env lv) (((Bool) _)) ((TVar m) (provable-predates env m cur)) (else (BFalse))))
      ((AnnSubterm _ p0 i _) (values p0 "subterm" $ subterm-provable-at env params args i))))
  (match many drop (((Env) _))
    ((BFalse) checked)
    ((BTrue) (env-warn-at checked (loc-in checked ap) $ say checked $ str-cat3 "unnecessary `(" kw " _)`; drop it"))))

(def-fns _ $ (many check-earlier : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) (many (Nat) k) (many (Spot) ap) (many (Callee) desc) (many (List $ Entry) params) -> (many (Env) r))
  (let-match many positions (Cons _ pi rest) ((Nil _) env))
  (let-match many (nat-lt j k) (BTrue) ((BFalse) env))
  (let ((many (Env) env2))
    (match many (list-nth _ (env-subterms env) j) _
      ((NthMiss _ _ _ _) (no-counterpart env ap desc params pi j))
      ((NthHit _ _ _ counterpart _) (check env "value" (nth-term args pi) $ TVar counterpart))))
  (tail $ check-earlier rest env2 args (Succ j) k ap desc params))

(def-fns _ $ (many erased-in-many : (subterm many (List $ Multiplicity) expect) (many (List $ Res) ress) (erased (Lockstep (Multiplicity) (Res) expect ress) lock) (many (Env) env) -> (many (Env) r))
  (let-match many expect (Cons _ m rest) ((Nil _) env))
  (let-match erased lock (LsCons _ _ _ _ _ _ p))
  (let-match many ress (Cons _ r rrest))
  (let ((many placeholder)) $ match many (res-term r) (((Bool) _)) ((TErr _) (BTrue)) (else (BFalse)))
  (let ((many env2)) $ match many (and (not $ env-usage-erased env) $ and (mult-is-many m) $ not placeholder) (((Env) _))
    ((BFalse) env)
    ((BTrue) (match many (misuse m $ res-erasure r) (((Env) _)) ((None _) env) ((Some _ how) (env-error env $ str-cat "internal: an unchecked result " how)))))
  (tail $ erased-in-many rest rrest p env2))

(def-fns _ $ (many mode-result-check : (many (Env) env) (many (List $ Res) ress) (many (Multiplicity) pos) (many (Bool) final) -> (many (Env) out))
  (let-match many ress (Cons _ r _) ((Nil _) env))
  (let ((many mode)) (mode-demand env (res-ty r) pos final))
  (erased-in-many (Cons _ mode (Nil _)) (Cons _ r (Nil _)) (LsCons _ _ mode r (Nil _) (Nil _) (LsNil _ _)) env))

; A call's or application's argument count against its telescope (lib/elab.ml's check_args).
(def-fns _ $ (many count-check : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r))
  (match many (nat-cmp expected got) _
    ((CEq _ _ _) env)
    (else (count-error env what expected got))))

(def-fns _ $ (many malformed : (unique (ElabWorld) ew) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Env) env) (many (Sp) sp) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (expr-error ew ctx expect env (sp-misuse env sp) "malformed"))

; The field at a wrapping constructor's one many position, given the arguments in order.
(def-fns _ $ (many wrap-field : (subterm many (List $ Entry) tele) (many (List $ Term) args) (many (List $ Term) tys) -> (many (Maybe $ Pair (Term) (Term)) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (None _)))
  (let-match many args (Cons _ t trest) ((Nil _) (None _)))
  (let-match many tys (Cons _ ty tyrest) ((Nil _) (None _)))
  (match many (entry-mult e) _
    ((Many) (match many (many-count rest) _ ((Zero) (Some _ $ MkPair _ _ t ty)) ((Succ _) (None _))))
    ((Once) (match many (many-count rest) _ ((Zero) (Some _ $ MkPair _ _ t ty)) ((Succ _) (None _))))
    ((Erased) (tail $ wrap-field rest trest tyrest))))

(def-fns _ $ (many missing-arg : (many (Env) env) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ var (env-at env $ MkSpot 0 0) $ NSrc "_")
  (values (env-back env env2) x))

(def-fns _ $ (many erased-res : (many (List $ Res) ress) (erased (Lockstep (Multiplicity) (Res) erased-one ress) lock) -> (many (Res) r))
  (first-res _ _ ress lock))

(def-fns _ $ (many erased-term : (many (List $ Res) ress) (erased (Lockstep (Multiplicity) (Res) erased-one ress) lock) -> (many (Term) t))
  (res-term $ erased-res ress lock))

(let ((many no-tele)) $ None $ List $ Entry)

; ---- `_` arguments (DESIGN.md section 50): what an application's result looks like over its parameters' metas, and
; the solving of that against the telescope the application is expected to produce.

(def-adts $ (AppResult : -> Type)
  enum
  (many ARApp : (many (Term) h) (many (Term) ret) -> (AppResult))
  (many ARCall : (many (List $ Entry) rets) -> (AppResult)))

(def-fns _ $ (many app-result-tele : (many (AppResult) r) (many (List $ Term) mvars) -> (many (List $ Entry) tele))
  (match many r _
    ((ARApp h ret) (Cons _ (MkEntry (None _) (BFalse) (Erased) (SgIs (TApp h $ list-rev _ mvars) $ instantiate mvars ret) (None _) (None _)) $ Nil _))
    ((ARCall rets) (instantiate-tele mvars rets))))

(def-fns _ $ (many entry-with-sg : (many (Entry) e) (many (Sg) sg) -> (many (Entry) r))
  (match many e _ ((MkEntry n s m _ place site) (MkEntry n s m sg place site))))

; An entry's type: as given, or inferred from its value where no binder of the telescope is mentioned.
(def-fns _ $ (many sg-type : (many (Sg) sg) -> (many (Maybe $ Term) r))
  (let-match many sg (SgIs t ty)
    ((SgTy t) (Some _ t)))
  (match many (dangling t 0) _ ((BTrue) (None _)) ((BFalse) (Some _ ty))))

; A result entry against an expected one: values where both are is-entries, types always.
(def-fns _ $ (many solve-pair : (many (Env) env) (many (Sg) e) (many (Sg) r) (many (Bool) strict) -> (many (Env) r2) (many (Bool) ok))
  (let ((many (Env) env1) (many (Bool) ok1))
    (match many e _
      ((SgIs a _) (match many r (((Env) _) ((Bool) b)) ((SgIs b2 _) (solve env "value" b2 a strict $ None _)) ((SgTy _) (values env $ BTrue))))
      ((SgTy _) (values env $ BTrue))))
  (let-match many ok1 (BTrue) ((BFalse) (values env1 $ BFalse)))
  (let-match many (sg-type r) (Some _ rt) ((None _) (values env1 $ BTrue)))
  (match many (sg-type e) _
    ((None _) (values env1 $ BTrue))
    ((Some _ et) (solve env1 "type" rt et strict $ None _))))

(def-fns _ $ (many solve-tele : (subterm many (List $ Entry) expect) (many (List $ Entry) result) (many (Env) env) (many (Bool) strict) -> (many (Env) r) (many (Bool) ok))
  (let-match many expect (Cons _ e rest) ((Nil _) (values env $ BTrue)))
  (let-match many result (Cons _ r rrest) ((Nil _) (values env $ BTrue)))
  (let ((many env1) (many ok1)) $ solve-pair env (entry-sg e) (entry-sg r) strict)
  (match many ok1 _
    ((BFalse) (values env1 $ BFalse))
    ((BTrue) (tail $ solve-tele rest rrest env1 strict))))

; [result] over [mvars] against the expectation, where an application has a `_`: not [strict], a failure
; leaves the environment as it was; strict, the mismatch is reported.
(def-fns _ $ (many solve-against : (many (Env) env) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (List $ Term) mvars) (many (Bool) wilds) (many (Bool) strict) -> (many (Env) r))
  (let-match many expect (Some _ tele) ((None _) env))
  (let-match many wilds (BTrue) ((BFalse) env))
  (let ((many res)) $ app-result-tele result mvars)
  (let ((many n)) $ list-length _ tele)
  (let ((many m)) $ list-length _ res)
  (let-match many (nat-cmp n m) (CEq _ _ _) (else (match many strict _ ((BTrue) (count-error env " values" n m)) ((BFalse) env))))
  (let ((many env2) (many ok)) $ solve-tele tele res env strict)
  (match many (or ok strict) _ ((BTrue) env2) ((BFalse) env)))

(def-fns _ $ (many tele-has-meta : (subterm many (List $ Entry) es) (many (Env) env) -> (many (Bool) r))
  (match many es _
    ((Nil _) (BFalse))
    ((Cons _ e rest) (or (has-meta-env env $ sg-term $ entry-sg e) $ notail $ tele-has-meta rest env))))

(def-fns _ $ (many terms-have-meta : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Bool) r))
  (match many ts _
    ((Nil _) (BFalse))
    ((Cons _ t rest) (or (has-meta-env env t) $ notail $ terms-have-meta rest env))))

(def-fns _ $ (many metaless-list : (subterm many (List $ Term) ts) (many (Env) env) -> (many (List $ Term) r))
  (match many ts _
    ((Nil _) (Nil _))
    ((Cons _ t rest) (Cons _ (metaless env t) $ notail $ metaless-list rest env))))

; The first argument, in order, still holding a `_` no unification solved.
(def-fns _ $ (many report-unsolved : (subterm many (List $ Term) args) (many (List $ Syn) raws) (many (List $ Entry) tele) (many (Callee) c) (many (Env) env) (many (Nat) i) -> (many (Env) r))
  (let-match many args (Cons _ t rest) ((Nil _) env))
  (let ((many name) (many more)) $ match many tele (((Maybe $ Name) _) ((List $ Entry) _)) ((Cons _ e es) (values (entry-name e) es)) ((Nil _) (values (None _) (Nil _))))
  (let ((many raw) (many rraws)) $ match many raws (((Maybe $ Syn) _) ((List $ Syn) _)) ((Cons _ r rs) (values (Some _ r) rs)) ((Nil _) (values (None _) (Nil _))))
  (let-match many (has-meta-env env t) (BTrue) ((BFalse) (tail $ report-unsolved rest rraws more c env $ Succ i)))
  (let ((many what)) $ argument-label c i name)
  (let ((many apos)) $ match many raw (((Spot) _)) ((Some _ r) (raw-pos r)) ((None _) (here-pos env)))
  (match many (match many raw (((Bool) _)) ((Some _ r) (is-underscore r)) ((None _) (BTrue))) _
    ((BTrue) (error-at-hinted env apos (callee-notes c) (str-cat what " is `_` and cannot be inferred") $ hole-hints env t))
    ((BFalse) (error-at-hinted env apos (callee-notes c) (str-cat3 what ": " $ cannot-infer env t) $ hole-hints env t))))

(def-fns _ $ (many any-wild : (erased (List $ Syn) root) (subterm many (List $ Sub root) args) -> (many (Bool) r))
  (let-match many args (Cons _ s rest)
    ((Nil _) (BFalse)))
  (match many s _ ((MkSub _ arg _) (or (is-underscore arg) $ notail $ any-wild _ rest))))

; Where each `_` among [args] is written, for the meta that stands for it; nothing for any other argument.
(def-fns _ $ (many wild-sites : (erased (List $ Syn) root) (many (Env) env) (subterm many (List $ Sub root) args) -> (many (List $ Maybe $ Loc) r))
  (let-match many args (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (MkSub _ arg _))
  (Cons _ (match many (is-underscore arg) (((Maybe $ Loc) _)) ((BTrue) (Some _ $ loc-in env $ raw-pos arg)) ((BFalse) (None _)))
    $ notail $ wild-sites _ env rest))

; comptime-match (section 28): a Settled, non-erased scrutinee with a non-erased discriminant, verified
; against the named constructor; the fields are bound Settled and the facts refined as a branch would.
; ---- A Settled's value printed through its type, for section 28's mismatch message (ASSUMPTIONS 66): a
; block carries no names, so the type's Matchable supplies them and an untagged type is read through its one
; constructor's field; an extern value prints through its model. The descent into a block's fields is
; bounded by the address, which each field's smaller number refines.

(def-fns _ $ (many show-nat : (subterm many (Nat) n) -> (many (Rope) r))
  (match many n _
    ((Zero) (RStr "(Zero)"))
    ((Succ k) (rwrap "(Succ " (notail $ show-nat k) ")"))))

(def-fns _ $ (many show-half : (many (Nat) n) -> (many (Rope) r))
  (match many (nat-halve n) _
    ((HZ) (RStr "(HZ)"))
    ((H1 m _ _) (rwrap "(H1 " (show-nat m) ")"))
    ((H2 m _ _) (rwrap "(H2 " (show-nat m) ")"))))

(def-fns _ $ (many show-str : (subterm many (String) s) -> (many (Rope) r))
  (match many s _
    ((SNil) (RStr "(SNil)"))
    ((SCons c rest) (rwrap "(SCons " (rcat3 (show-nat $ char-code c) (RStr " ") $ notail $ show-str rest) ")"))))

; The literal a value of one of the three literal types spells as, read off the block: a Char and a U8 are their
; Nat (section 33), so neither is unwrapped first. None where the type is not one of the three, or the block does
; not carry the payload it would need.
(def-fns _ $ (many lit-rope : (erased (Hist Block) hs) (many (Env) env) (many (Term) ty) (many (Block (Ref Block hs)) blk) -> (many (Maybe $ Rope) r))
  (let-match many blk (BExt _ p) (else (None $ Rope)))
  (match many p (((Maybe $ Rope) _))
    ((PNat n)
      (let-match many (prelude-nullary env ty "Nat") (BFalse) ((BTrue) (Some _ $ RStr $ nat-str n)))
      (match many (prelude-nullary env ty "Char") (((Maybe $ Rope) _))
        ((BTrue) (Some _ $ lit-char-rope n))
        ((BFalse) (None $ Rope))))
    ((PStr st)
      (match many (prelude-nullary env ty "String") (((Maybe $ Rope) _))
        ((BTrue) (Some _ $ lit-string-rope st))
        ((BFalse) (None $ Rope))))
    ((PHalf _) (None $ Rope))
    ((PBytes _) (None $ Rope))
    ((PRaw _ _) (None $ Rope))
    ((PHandle _ _ _ _) (None $ Rope))))

(def-fns _ $ (many show-plain : (erased (Hist Block) a) (many (Block (Ref Block a)) b) -> (many (Rope) r))
  (let-match many b (BExt _ p)
    ((BCtorFn _ c) (rwrap "<constructor " (RStr $ ctor-name c) ">"))
    ((BMat _ adt) (rwrap "<matchable " (RStr $ adt-name adt) ">"))
    ((BToken _) (RStr "_"))
    ((BError _ m) (rwrap "<error: " (RStr m) ">"))
    (else (RStr "?")))
  (match many p _ ((PNat n) (show-nat n)) ((PHalf x) (show-half x)) ((PStr x) (show-str x)) ((PBytes x) (show-str x)) ((PRaw _ _) (RStr "_")) ((PHandle _ _ _ _) (RStr "_"))))

; A Half at its own type. Its field is a Nat, so it spells in decimal, as the reference's typed printer reaches
; it; show-plain above keeps the unary spelling, which is what the untyped fallback prints.
(def-fns _ $ (many show-half-typed : (many (Nat) n) -> (many (Rope) r))
  (match many (nat-halve n) _
    ((HZ) (RStr "(HZ)"))
    ((H1 m _ _) (rwrap "(H1 " (RStr $ nat-str m) ")"))
    ((H2 m _ _) (rwrap "(H2 " (RStr $ nat-str m) ")"))))

; An extern value at its own type, which the reference's printer reaches through the FFI's destruct whatever the
; type. Here there is one case per extern implementation and no else, so a fourth extern type stops the compiler
; at this line rather than silently falling back to the untyped spelling. ExtHalf is the only arm that runs:
; a second extern declaration of an already bound name is refused (ASSUMPTIONS 42), so ExtNat and ExtString
; tag the prelude's own types alone, which lit-rope spells before this is reached.
(def-fns _ $ (many show-ext-typed : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (ExtType) e) -> (many (Rope) r))
  (let-match many e (ExtHalf) ((ExtArray) (show-plain _ b)) ((ExtNat) (show-plain _ b)) ((ExtString) (show-plain _ b)) ((ExtBytes) (show-plain _ b)) ((ExtRaw _ _ _ _ _ _) (show-plain _ b)) ((ExtSlots _ _) (show-plain _ b)))
  (let-match many b (BExt _ p)
    (else (show-plain _ b)))
  (match many p (((Rope) _)) ((PHalf n) (show-half-typed n)) (else (show-plain _ b))))

(def-fns _ $ (many types-of : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Term) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (Cons _ (type-of env x) $ notail $ types-of env rest))))

; The many fields' types of a constructor at an instance of its type, as entering its branch reads them.
; One entry per field in declaration order, None where the field is erased: it has no word, so it takes none
; from the destructure and prints `_` (section 45).
(def-fns _ $ (many field-slots : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Maybe $ Term) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (match many (entry-mult-of env x) (((Maybe $ Term) _))
            ((Erased) (None _))
            (else (Some _ $ type-of env x)))
    $ notail $ field-slots env rest))

; The fields' types in the environment the unification refined, which a nested field's own printing reads
; them in (lib/elab.ml's show_value passes its env' down).
(def-fns _ $ (many field-types : (many (Env) env) (many (Term) ty) (many (Ctor) c) -> (many (Env) e) (many (List $ Maybe $ Term) tys))
  (let ((many ctele) (many ret)) $ ctor-type env $ ctor-id c)
  (let ((many envb) (many fids) (erased _)) $ open-tele ctele env (None _) (None _) (None _) (Nil _) $ BFalse)
  (match many (merge-all $ unify-force (Forcing envb) (instantiate (tvars-rev fids $ Nil _) ret) ty) _
    ((UOk e2) (values e2 (field-slots e2 fids)))
    ((UContra _) (values env (Nil _)))))

(def-fns _ $ (many type-adt : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Adt) r))
  (let-match many (type-head env ty) (Some _ tid) ((None _) (None _)))
  (let ((many _) (many found)) $ find-matchable env tid)
  (let-match many found (Some _ info)
    ((None _) (None _)))
  (match many info _ ((MkMatchInfo mid _ _ _) (adt-of env mid))))

(def-fns _ $ (many listed-in-ctors : (many (Env) env) (subterm many (List $ MCtor) cs) (many (Nat) cid) -> (many (Nat) r))
  (let-match many cs (Cons _ mc rest) ((Nil _) cid))
  (let-match many mc (MkMCtor _ c))
  (let ((many (Bool) hit)) $ match many c _
    ((TVar z) (match many (ctor-of env z) _ ((Some _ ct) (nat-eq (ctor-id ct) cid)) ((None _) (BFalse))))
    (else (BFalse)))
  (let-match many hit (BFalse) ((BTrue) (match many c (((Nat) _)) ((TVar z) z) (else cid))))
  (tail $ listed-in-ctors env rest cid))

(def-fns _ $ (many listed-entry : (many (Env) env) (many (Term) ty) (many (Nat) cid) -> (many (Nat) r))
  (let-match many (type-head env ty) (Some _ tid) ((None _) cid))
  (let ((many _) (many found)) $ find-matchable env tid)
  (let-match many found (Some _ info) ((None _) cid))
  (match many info _ ((MkMatchInfo _ _ cs _) (listed-in-ctors env cs cid))))

; The constructor's name over its fields, without the outer parens: show-at hands those to its caller as the
; Bool beside the rope, so a last argument that is an application takes `$` instead of its own pair (DESIGN 2).
(def-fns _ $ (many ctor-body : (many (Ctor) ct) (many (List $ Rope) fields) -> (many (Rope) r))
  (rjoin (Cons _ (RStr $ ctor-name ct) fields) " "))

; The sole non-phantom constructor, where a type has exactly one and so needs no tag (section 45).
(def-fns _ $ (many lone-ctor : (many (Adt) adt) -> (many (Maybe $ Ctor) c))
  (let-match many (adt-ctors adt) (Cons _ c more)
    ((Nil _) (None _)))
  (match many more (((Maybe $ Ctor) _)) ((Nil _) (Some _ c)) ((Cons _ _ _) (None _))))

(def-fns _
  ; The rope is the rendering, and the Bool says it is an application body still missing its parens, which is
  ; what lets a caller write `$` before a last one instead (section 45).
  ((many show-at : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) r) (subterm many (Nat) depth)
      (many (Env) env) (many (Term) ty0) -> (many (Rope) rope) (many (Bool) app))
    (let-match many depth (Succ dd) ((Zero) (values (RStr "_") (BFalse))))
    (let ((many ty)) $ canon-env env ty0)
    (let-match many (term-eq ty slot-term) (BFalse) ((BTrue) (values (RStr "_") (BFalse))))
    (match many ty (((Rope) _) ((Bool) b2))
      ((TCell _ _) (values (RStr "_") (BFalse)))
      (else
        (let ((erased _) (many blk) (erased _)) $ hread hs hp r)
        (let-match many (lit-rope _ env ty blk) (None _) ((Some _ text) (values text (BFalse))))
        (let-match many (type-adt env ty) (Some _ adt) ((None _) (values (RStr "_") (BFalse))))
        (let ((erased _) (many hp2) (erased _) (many read)) $ dispatch _ hp (adt-ext adt) (adt-tagged adt) r)
        (match many read (((Rope) _) ((Bool) b5))
          ((Some _ pair)
            (let-match many pair (MkPair _ _ index fields))
            (let-match many (ctor-at adt index) (Some _ ct) ((None _) (values (RStr "_") (BFalse))))
            (let ((many e2) (many tys)) (field-types env ty ct))
            (values (ctor-body ct $ notail $ show-fields _ hp2 dd tys fields e2) (BTrue)))
          ((None _)
            (let-match many (lone-ctor adt) (Some _ ct) ((None _) (values (RStr "_") (BFalse))))
            (let ((many e2) (many tys)) (field-types env ty ct))
            (values (ctor-body ct $ notail $ show-fields _ hp dd tys
                      (ctor-fields _ hp (adt-newtype adt) (ctor-arity ct) r) e2) (BTrue)))))))

  ; Walks the declared fields, an erased one taking no word from the destructure; a field that is an application
  ; takes its own parens, or `$` where it is the last (DESIGN 2, 45).
  ((many show-fields : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (Nat) depth)
      (subterm many (List $ Maybe $ Term) tys) (many (List $ Ref Block hs) fs) (many (Env) env) -> (many (List $ Rope) rs))
    (let-match many tys (Cons _ mt rest) ((Nil _) (Nil _)))
    (let ((many fw) (many more)) $ match many mt (((Maybe $ Ref Block hs) _) ((List $ Ref Block hs) l))
      ((None _) (values (None _) fs))
      ((Some _ _) (match many fs (((Maybe $ Ref Block hs) _) ((List $ Ref Block hs) l)) ((Nil _) (values (None _) fs)) ((Cons _ f rst) (values (Some _ f) rst)))))
    (let ((many shown)) $ notail $ shown-field _ hp depth rest mt fw env)
    (Cons _ shown $ notail $ show-fields _ hp depth rest more env))

  ((many shown-field : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (Nat) depth) (subterm many (List $ Maybe $ Term) rest) (many (Maybe $ Term) mt) (many (Maybe $ Ref Block hs) fw) (many (Env) env) -> (many (Rope) r))
    (let-match many mt (Some _ t) ((None _) (RStr "_")))
    (let-match many depth (Succ dd) ((Zero) (RStr "_")))
    (let ((many (Rope) body) (many (Bool) app))
      (match many fw _
        ((Some _ f) (notail $ show-at _ hp f dd env t))
        ((None _) (values (RStr "_") (BFalse)))))
    (let-match many app (BTrue) ((BFalse) body))
    (match many rest _
      ((Nil _) (RCat (RStr "$ ") body))
      ((Cons _ _ _) (rwrap "(" body ")")))))

(def-fns _ $ (many show-typed : (many (Env) env) (many (Term) ty) (many (Nat) x) -> (many (Rope) r))
  (let ((erased _) (many hp)) $ env-heap env)
  (let-match many (settled-ref _ (heap-entries _ hp) x) (Some _ v) ((None _) (RStr "?")))
  (let ((many body) (many app)) $ show-at _ hp v 100000 env ty)
  (match many app (((Rope) _)) ((BTrue) (rwrap "(" body ")")) ((BFalse) body)))

(def-fns _ $ (many elab-comptime-match : (erased (List $ List $ Nat) ctx) (many (Env) env) (many (List $ Syn) args) (many (Maybe $ Nat) pre) -> (many (Env) r) (many (StmtCode ctx ctx) sc))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env $ sp-misuse env $ SpStmt $ StComptimeMatch))
    (let-match many args (Cons _ mraw rest) ((Nil _) (values (bad) $ SNone _)))
    (let-match many (comptime-shape rest) (Some _ triple) ((None _) (values (bad) $ SNone _)))
    (let ((many envm) (many mode)) (mult-checked env mraw))
    (let ((many env14)) $ refuse-unless envm (mult-is-many mode) "`comptime-match` takes `many` or `unique`, not `erased`")
    (let-match many triple (MkPair _ _ xraw cpat))
    (let-match many cpat (MkPair _ _ craw fields))
    (let ((many env1)) $ refuse-unless env14 (env-run-pos env14) "`comptime-match` is a run-position statement (section 28)")
    (let ((many env2) (many x) (many sharing))
      (match many (match many pre (((Maybe $ Syn) _)) ((Some _ _) (None _)) ((None _) (share-arg env1 xraw))) (((Env) _) ((Nat) i) ((Bool) b))
        ((None _)
          (let-match many pre (None _) ((Some _ y) (values env1 y (BFalse))))
          (let ((many envb) (many z)) $ var-of-raw env1 xraw "a variable")
          (values envb z (BFalse)))
        ((Some _ arg)
          (let ((many envb) (many y)) $ var-of-raw env1 arg "a variable")
          (let ((many envc)) $ refuse-when envb (not $ mult-is-once $ made envb arg y) "`share` needs a unique value")
          (let ((many envd)) $ match many (mult-is-once mode) (((Env) _)) ((BFalse) envc) ((BTrue) (env-error envc $ str-cat3 "many value " (qshown envc y) " used at unique")))
          (values envd y (BTrue)))))
    (let ((many (Syn) xr)) $ match many (share-arg env1 xraw) _ ((None _) xraw) ((Some _ a) a))
    (let ((many env2d)) (use-entry-as env2 mode x sharing $ raw-atom xr))
    (let ((many (Env) env3))
      (match many (and (is-settled env2d x) $ mult-is-many $ made env2d xr x) _
        ((BTrue) env2d)
        ((BFalse) (env-error env2d (say env2d "`comptime-match` needs a Settled scrutinee that is `many` or `unique`")))))
    (let ((many env4) (many c)) $ ctor-var env3 craw)
    (let ((many tele) (many ret)) $ ctor-type env4 c)
    (let ((many head)) $ type-head env4 $ type-of env4 x)
    (let ((many (Nat) tid)) $ match many head _ ((None _) (Zero)) ((Some _ t2) t2))
    (let ((many (Env) env5) (many (Maybe $ MatchInfo) found))
      (match many head _
        ((None _) (values (env-error env4 "scrutinee is not a datatype value") $ None _))
        ((Some _ t3) (find-matchable env4 t3))))
    (let ((many (Env) env6))
      (match many found _
        ((None _) env5)
        ((Some _ info)
          (let-match many info (MkMatchInfo mid disc mctors _))
          (let ((many env5a)) $ match many (is-some _ $ adt-of env5 mid) (((Env) _)) ((BTrue) env5) ((BFalse) (env-error env5 $ str-cat3 (say env5 "the `Matchable` for ") (qshown env5 tid) (say env5 " is not Settled, so `comptime-match` cannot consult it"))))
          (let ((many env5b)) $ use-entry (warn-use env5a (env-loc env5a) "match on" $ TVar tid) (Many) mid (BFalse))
          (let ((many env6a)) $ match many disc (((Env) _)) ((DUnion) (env-error env5b (say env5b "`comptime-match` needs an `enum`, not a `union`"))) ((DEnum) env5b))
          (let ((many env6b) (many mk)) $ marker-checked env6a tid mctors c)
          (match many (mult-is-many mk) (((Env) _)) ((BTrue) env6b) ((BFalse) (env-error env6b $ str-cat3 (say env6b "`comptime-match`: ") (qshown env6b c) " is phantom, so no non-erased value is headed by it"))))))
    (let ((many (Env) env7))
      (match many (ctor-of env6 c) _
        ((None _) (env-error env6 $ str-cat (qshown env6 c) " is not a run-position constructor"))
        ((Some _ ct)
          (let ((many env6b) (many mi)) $ env-destruct env6 x ct)
          (let-match many mi (Some _ i) ((None _) env6b))
          (match many (nat-cmp i $ ctor-index ct) (((Env) _))
            ((CEq _ _ _) env6b)
            (else (env-error env6b $ str-cat3 (say env6b "`comptime-match`: expected ") (qshown env6b c) $ str-cat ", got " $ tick $ rope-str $ show-typed env6b (type-of env6b x) x))))))
    (let ((many extra)) (match many found (((Bool) _)) ((None _) (BFalse)) ((Some _ info) (match many info _ ((MkMatchInfo mid _ cs _) (and (mult-is-many $ marker cs c) $ cells-allowed env7 mid $ BFalse))))))
    (let ((many mults)) (field-mults (tele-mults tele) mode))
    (let ((many ppos)) $ match many (list-nth _ rest 1) (((Spot) _)) ((NthHit _ _ _ pr _) (raw-pos pr)) ((NthMiss _ _ _ _) (here-pos env7)))
    (let ((many env8) (many ordinary) (many cellname)) (pattern-fields env7 ppos "a `comptime-match` pattern" mode (res-of env7 x) c tele mults fields extra))
    (let ((many env10) (many fids) (many u)) $ open-fields env8 tele (raw-names ordinary) (raw-sites ordinary env8) (Some _ mults) (res-of env8 x) c ret)
    (let-match many u (UOk env11)
      ((UContra msg) (values (match many (env-failed env10) (((Env) _)) ((BTrue) env10) ((BFalse) (env-error env10 $ str-cat3 "internal: the verified value contradicts the facts in force (" (clash-str env10 msg) ")"))) $ SNone _)))
    (let ((many env12)) (match many (ctor-of env11 c) (((Env) _)) ((None _) env11) ((Some _ ct) (env-set-fields env11 x ct fids mults))))
    (let ((many env13) (many _)) (pattern-cell-option env12 mode (res-of env12 x) c fids extra cellname))
    (values env13 $ SNone _))

; Every function recurses on a raw it elaborates: the first subterm parameter is that raw or list, a later
; one a structure parsed from it (its entries prove they sit inside it) or a Steps budget spent when a
; function hands its whole raw to another.
; ---- Sugar (DESIGN.md section 49): unary stands for calls on the prelude's Numeral lemmas, written
; down as the reference writes them and elaborated where the form is met. The elaborator's group takes a
; budget of such expansions as its first subterm parameter, spent when a generated form is elaborated,
; which is what lets that raw be of the elaborator's own making (ASSUMPTIONS 111).

(def-fns _
  ((many raw-size : (subterm many (Syn) raw) -> (many (Nat) n))
    (match many raw _
      ((RList _ items) (Succ $ notail $ raws-size items))
      (else 1)))
  ((many raws-size : (subterm many (List $ Syn) rs) -> (many (Nat) n))
    (match many rs _
      ((Nil _) 0)
      ((Cons _ r rest) (nat-add (notail $ raw-size r) $ notail $ raws-size rest)))))

(def-fns _ $ (many gen-atom : (many (String) s) -> (many (Syn) r))
  (RAtom (MkSpot 1 1) $ NSrc s))

(def-fns _ $ (many gen-nat : (many (Nat) n) -> (many (Syn) r))
  (RNat (MkSpot 1 1) n))

(def-fns _ $ (many gen-of : (many (String) head) (many (List $ Syn) args) -> (many (Syn) r))
  (RList (MkSpot 1 1) $ Cons _ (gen-atom head) args))

(def-fns _ $ (many gen-numeral-of : (many (Nat) n) -> (many (Syn) r))
  (gen-of "numeral-of" $ Cons _ (gen-nat n) $ Nil _))

(def-fns _ $ (many bin-raw : (subterm many (Bin) b) -> (many (Syn) r))
  (gen-of (bin-ctor b) $ match many b (((List $ Syn) _)) ((BZ) (Nil _)) ((B1 x) (Cons _ (notail $ bin-raw x) $ Nil _)) ((B2 x) (Cons _ (notail $ bin-raw x) $ Nil _))))

(def-fns _ $ (many bin-text : (many (Nat) n) -> (many (Syn) r))
  (bin-raw $ bin-of-nat n))

(def-fns _ $ (many bin-succ : (subterm many (Bin) b) -> (many (Bin) c))
  (match many b _ ((BZ) (B1 $ BZ)) ((B1 b1) (B2 b1)) ((B2 b1) (B1 $ notail $ bin-succ b1))))

; The witness that n's spelling steps to (n+1)'s: (B1 x) steps to (B2 x), and (B2 x) to (B1 (succ x)).
(def-fns _ $ (many bin-succ-witness : (subterm many (Bin) b) -> (many (Syn) r))
  (match many b _
    ((BZ) (gen-of "BSZ" $ Nil _))
    ((B1 x) (gen-of "BS1" $ Cons _ (bin-raw x) $ Nil _))
    ((B2 x) (gen-of "BS2" $ Cons _ (bin-raw x) $ Cons _ (bin-raw $ bin-succ x) $ Cons _ (notail $ bin-succ-witness x) $ Nil _))))

(def-fns _ $ (many succs : (subterm many (Nat) k) (many (Syn) base) -> (many (Syn) r))
  (match many k _
    ((Zero) base)
    ((Succ j) (tail $ succs j $ gen-of "Succ" $ Cons _ base $ Nil _))))

(def-fns _ $ (many unary-fold : (subterm many (Nat) k) (many (Nat) z) (many (Nat) lo) (many (Syn) floor) (many (Syn) acc) -> (many (Syn) r))
  (let-match many k (Succ j) ((Zero) acc))
  (let ((many n)) $ Succ z)
  (let ((many below)) $ succs (nat-sub z lo) floor)
  (let ((many stp)) $ gen-of "numeral-succ" $ Cons _ (bin-text z) $ Cons _ (bin-text n) $ Cons _ (gen-nat z) $ Cons _ (gen-nat n)
                      $ Cons _ (bin-succ-witness $ bin-of-nat z) $ Cons _ (gen-numeral-of z) $ Cons _ (gen-numeral-of n) $ Nil _)
  (let ((many congd)) $ gen-of "eq-cong-succ" $ Cons _ (gen-nat z) $ Cons _ below $ Cons _ acc $ Nil _)
  (let ((many acc2)) $ gen-of "eq-trans" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat n) $ Cons _ (gen-of "Succ" $ Cons _ (gen-nat z) $ Nil _)
                      $ Cons _ (gen-of "Succ" $ Cons _ below $ Nil _) $ Cons _ stp $ Cons _ congd $ Nil _)
  (tail $ unary-fold j n lo floor acc2))

(def-fns _ $ (many unary-source : (many (Nat) za) (many (Nat) lo) (many (Bool) floored) -> (many (Syn) r))
  (let ((many (Syn) floor) (many (Syn) acc))
    (match many floored _
      ((BFalse) (values (gen-of "Zero" $ Nil _) $ gen-of "numeral-zero" $ Cons _ (gen-nat 0) $ Cons _ (gen-numeral-of 0) $ Nil _))
      ((BTrue) (values (gen-nat lo) $ gen-of "Refl" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat lo) $ Nil _))))
  (gen-of "let-match" $ Cons _ (gen-atom "erased") $ Cons _ (unary-fold (nat-sub za lo) lo lo floor acc)
    $ Cons _ (gen-of "Refl" $ Cons _ (RWild $ MkSpot 1 1) $ Cons _ (RWild $ MkSpot 1 1) $ Nil _) $ Nil _))


; ---- dump-context (ASSUMPTIONS 196, lib/dump.ml)

(def-adts
  ((Goal : -> Type)
    enum
    (many GoalStatement : -> (Goal))
    (many GoalType : -> (Goal))
    (many GoalValues : (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) -> (Goal)))
  ((Focus : -> Type)
    enum
    (many MkFocus : (many (String) source) (many (Term) t) (many (Term) ty) -> (Focus))))

(def-fns _ $ (many cat-strs : (subterm many (List $ String) xs) (many (List $ String) ys) -> (many (List $ String) r))
  (match many xs _ ((Nil _) ys) ((Cons _ x rest) (Cons _ x $ notail $ cat-strs rest ys))))

(def-fns _ $ (many prefix-all : (many (String) p) (subterm many (List $ String) xs) -> (many (List $ String) r))
  (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (str-cat p x) $ notail $ prefix-all p rest))))

(def-fns _ $ (many when-str : (many (Bool) b) (many (String) x) (many (List $ String) rest) -> (many (List $ String) r))
  (match many b _ ((BTrue) (Cons _ x rest)) ((BFalse) rest)))

(def-fns _ $ (many mult-names : (subterm many (List $ Multiplicity) ms) -> (many (List $ String) r))
  (match many ms _ ((Nil _) (Nil _)) ((Cons _ m rest) (Cons _ (mult-name m) $ notail $ mult-names rest))))

(def-fns _ $ (many qnames : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (qshown env x) $ notail $ qnames env rest))))

(def-fns _ $ (many bound-here : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (and (list-mem-bin (scope-ids $ env-scope env) x) $ not $ is-prelude env x))

(let ((many proof-ids)) (Cons _ predates-id $ Cons _ subterm-id $ Cons _ coercible-id $ Cons _ delegate-id $ Cons _ atfn-id $ Nil _))

(def-fns _ $ (many entry-kind : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (let-match many (canon-env env $ type-of env x) (TApp h _)
    ((TFn uq _ _ _) (match many uq _ ((BTrue) "unique function") ((BFalse) "function")))
    ((TTyCtor _) "type constructor")
    ((TValCtor _ _) "constructor")
    ((TMatchable _ _ _ _ _) "Matchable")
    ((TCell _ _) "cell")
    (else "value"))
  (let-match many h (TVar hd) (else "value"))
  (let-match many (nat-eq hd level-id) (BFalse)
    ((BTrue) (match many (entry-minted env x) _ ((BTrue) (say env "level minted by `def-lvl`")) ((BFalse) "level"))))
  (let-match many (nat-eq hd univ-id) (BFalse) ((BTrue) "type"))
  (let-match many (nat-eq hd special-id) (BFalse)
    ((BTrue) "special form"))
  (match many (list-mem-bin proof-ids hd) _ ((BTrue) "proof") ((BFalse) "value")))

(def-fns _ $ (many entry-flags : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ name mult state _ _ _ site))
  (let ((many (Bool) shadowed)) $ match many name _ ((None _) (BFalse)) ((Some _ n) (match many (lookup env n) _ ((Some _ y) (not $ nat-eq y x)) ((None _) (BTrue)))))
  (let ((many where)) $ loc-str site)
  (let ((many (String) placed))
    (match many (str-is-empty where) _
      ((BFalse) (str-cat "bound at " where))
      ((BTrue) (match many (is-prelude env x) _ ((BTrue) "built in") ((BFalse) "minted by the elaborator")))))
  (let ((many (List $ String) rest))
    (when-str (match many name (((Bool) _)) ((None _) (BTrue)) ((Some _ _) (BFalse))) "anonymous"
      $ when-str (list-mem-bin (env-temporary env) x) "the elaborator's own binder for a head or an argument"
      $ when-str shadowed "shadowed by a newer binder of the same name" $ list1 _ placed))
  (let ((many (List $ String) rest2))
    (match many (index-of-bin (env-subterms env) x 0) _
      ((Some _ i) (Cons _ (str-cat3 "subterm parameter " (nat-str $ Succ i) " of the enclosing function") rest))
      ((None _) rest)))
  (join-strs (Cons _ (mult-name mult) $ Cons _ (match many state (((String) _)) ((SSettled _ _ _) "Settled") ((SHypothetical _) "Hypothetical")) $ Cons _ (entry-kind env x) rest2) ", "))

(def-fns _ $ (many unique-status : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let-match many (mult-is-once $ entry-mult-of env x) (BTrue) ((BFalse) (Nil _)))
  (let ((many (String) status))
    (match many (idmap-get _ x $ uses-map $ env-uses env) _
      ((Miss _ _ _ _) "unique: live, neither consumed nor shared on this path")
      ((Hit _ _ _ u _)
        (match many u _
          ((UseConsumed l) (str-cat3 "unique: consumed at " (loc-str $ Some _ l) ", so usable only erased from here on"))
          ((UseShared l) (str-cat3 "unique: shared at " (loc-str $ Some _ l) $ str-cat3 (say env ", so usable at many, written `(share ") (shown-name env x) ")`, and never again at unique"))))))
  (Cons _ status $ when-str (list-mem-bin (env-captures env) x) (say env "unique: closed over by the enclosing `def-fns`, so usable here only erased or through `share`") $ Nil _))

(def-fns _ $ (many entry-value : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let-match many (and (is-settled env x) $ mult-is-many $ entry-mult-of env x) (BTrue) ((BFalse) (Nil _)))
  (let ((many shown)) $ rope-str $ show-typed env (type-of env x) x)
  (match many (str-eq shown "_") _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "= " shown))))

(def-fns _ $ (many entry-lines : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let ((many _) (many rule)) $ fact-at env x)
  (let ((many (List $ String) is-line))
    (match many rule _
      ((None _) (Nil _))
      ((Some _ r0)
        (let ((many r)) $ canon-env env r0)
        (let ((many (Bool) anonymous)) $ match many r _ ((TVar y) (match many (env-entry-name env y) _ ((None _) (BTrue)) ((Some _ _) (BFalse)))) (else (BFalse)))
        (match many anonymous _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "is " $ show-t-except env r $ Some _ x))))))
  (Cons _ (str-cat3 (shown-name env x) " : " $ str-cat3 (show-t env $ type-of env x) "  [" $ str-cat (entry-flags env x) "]")
    $ prefix-all "    " $ cat-strs is-line $ cat-strs (entry-value env x) $ unique-status env x))

(def-fns _ $ (many ctor-strs : (many (Env) env) (subterm many (List $ MCtor) cs) -> (many (List $ String) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let-match many c (MkMCtor _ t))
  (let ((many ty)) $ match many t (((Term) _)) ((TVar cid) (type-of env cid)) (else t))
  (Cons _ (str-cat3 (show-t env t) " : " $ show-t env ty) $ notail $ ctor-strs env rest))

(def-fns _ $ (many ctor-lines : (many (Env) env) (many (Term) ty) -> (many (List $ String) r))
  (let-match many (type-head env ty) (Some _ tid) ((None _) (Nil _)))
  (let ((many _) (many found)) $ find-matchable env tid)
  (let-match many found (Some _ info) ((None _) (Nil _)))
  (match many info _
    ((MkMatchInfo _ _ cs _) (list1 _ $ str-cat3 "constructors of `" (shown-name env tid) $ str-cat "`: " $ join-strs (ctor-strs env cs) "; "))))

(def-fns _ $ (many ctor-lines-tele : (many (Env) env) (subterm many (List $ Entry) es) -> (many (List $ String) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ ctor-lines-tele env rest)
  (let-match many (entry-sg e) (SgTy t)
    ((SgIs _ _) more))
  (match many (dangling t 0) _ ((BTrue) more) ((BFalse) (cat-strs (ctor-lines env t) more))))

(def-fns _ $ (many with-mults : (subterm many (List $ Multiplicity) ms) (many (List $ Entry) es) -> (many (List $ Entry) r))
  (let-match many ms (Cons _ m mrest) ((Nil _) es))
  (let-match many es (Cons _ e erest)
    ((Nil _) es))
  (match many e _ ((MkEntry n s _ sg pl site) (Cons _ (MkEntry n s m sg pl site) $ notail $ with-mults mrest erest))))

(def-fns _ $ (many goal-lines : (many (Env) env) (many (Goal) wanted) -> (many (List $ String) r))
  (let-match many wanted (GoalValues expect tele)
    ((GoalStatement) (list1 _ $ say env "goal: none; `dump-context` stands as a statement here, so nothing is expected of it"))
    ((GoalType) (list1 _ "goal: a type, in an erased position")))
  (match many tele _
    ((None _)
      (let ((many n)) $ list-length _ expect)
      (let ((many (String) plural)) $ match many n _ ((Succ p) (match many p _ ((Zero) " value") (else " values"))) ((Zero) " values"))
      (list1 _ $ str-cat3 "goal: " (nat-str n) $ str-cat3 plural " at " $ str-cat (join-strs (mult-names expect) ", ") "; the position fixes no type"))
    ((Some _ es)
      (let ((many (List $ Entry) es2)) $ match many (nat-eq (list-length _ es) $ list-length _ expect) _ ((BTrue) (with-mults expect es)) ((BFalse) es))
      (Cons _ (str-cat "goal: " $ show-tele-t env es2 $ BTrue) $ ctor-lines-tele env es2))))

(def-fns _ $ (many position-lines : (many (Env) env) (many (Goal) wanted) -> (many (List $ String) r))
  (let ((many (List $ String) pos))
    (match many wanted _
      ((GoalStatement) (Nil _))
      ((GoalType) (list1 _ "position: erased"))
      ((GoalValues expect _) (list1 _ $ str-cat "position: " $ mult-name $ pos-in env expect))))
  (let ((many (String) level))
    (match many (env-level env) _
      ((None _) "level: the top level, above every function's level")
      ((Some _ lvl)
        (str-cat3 "level: " (qshown env lvl)
          (match many (env-subterms env) (((String) _))
            ((Nil _) "; the enclosing function has no subterm parameter")
            ((Cons _ _ _) (str-cat "; its subterm arguments, in order: " $ join-strs (qnames env $ env-subterms env) ", ")))))))
  (cat-strs pos
    $ when-str (env-usage-erased env) "erased context: nothing here counts as a use, so no unique binder is consumed or shared by this code"
    $ Cons _ (match many (env-run-pos env) (((String) _)) ((BTrue) "run position: a statement here runs at once and its binders are Settled") ((BFalse) "inside a function body or a match branch: binders here are Hypothetical and calls need their proofs"))
    $ Cons _ level
    $ when-str (env-in-extern env) "inside an extern function's model, so extern types' constructors have cells" $ Nil _))

(def-fns _ $ (many insert-asc : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (list1 _ x)))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ _) (Cons _ x xs))
    ((CEq _ _ _) xs)
    (else (Cons _ y $ notail $ insert-asc x rest))))

(def-fns _ $ (many sort-asc : (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (insert-asc x $ notail $ sort-asc rest))))

(def-fns _ $ (many class-add : (many (Nat) root) (many (Nat) x) (subterm many (List $ Pair (Nat) $ List $ Nat) cs) -> (many (List $ Pair (Nat) $ List $ Nat) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (list1 _ $ MkPair _ _ root $ list1 _ x)))
  (let-match many c (MkPair _ _ r members))
  (match many (nat-cmp root r) _
    ((CEq _ _ _) (Cons _ (MkPair _ _ r $ list-rev _ $ Cons _ x $ list-rev _ members) rest))
    (else (Cons _ c $ notail $ class-add root x rest))))

; The slotted entries grouped by the canonical atom of their slot, each class in order of first mention.
(def-fns _ $ (many at-classes : (many (Env) env) (subterm many (List $ Nat) ids) (many (List $ Pair (Nat) $ List $ Nat) acc) -> (many (List $ Pair (Nat) $ List $ Nat) r))
  (let-match many ids (Cons _ x rest) ((Nil _) acc))
  (let-match many (canon-env env $ slot-atom x) (TVar a) (else (tail $ at-classes env rest acc)))
  (tail $ at-classes env rest $ class-add a x acc))

(def-fns _ $ (many at-member : (many (Env) env) (many (Nat) x) -> (many (Maybe $ String) r))
  (let-match many (lit-spelling (env-lits env) x) (None _)
    ((Some _ s) (Some _ s)))
  (match many (or (bound-here env x) $ nat-eq x null-id) _ ((BTrue) (Some _ $ shown-name env x)) ((BFalse) (None _))))

(def-fns _ $ (many at-members : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) shown) (many (Bool) bound))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil _) (BFalse))))
  (let ((many shown) (many bound)) $ notail $ at-members env rest)
  (let ((many bound2)) $ or bound $ bound-here env x)
  (match many (at-member env x) _
    ((None _) (values shown bound2))
    ((Some _ s) (values (Cons _ s shown) bound2))))

(def-fns _ $ (many at-shown : (many (Env) env) (subterm many (List $ Pair (Nat) $ List $ Nat) cs) -> (many (List $ String) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ at-shown env rest)
  (let-match many c (MkPair _ _ _ members))
  (let ((many shown) (many bound)) $ at-members env $ sort-asc members)
  (match many (and bound $ nat-lt 1 $ list-length _ shown) _
    ((BTrue) (Cons _ (str-cat3 "{" (join-strs shown ", ") "}") more))
    ((BFalse) more)))

(def-fns _ $ (many lit-ids : (subterm many (List $ LitEntry) ls) -> (many (List $ Nat) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (match many l _ ((MkLitEntry x _ _ _ _) (Cons _ x $ notail $ lit-ids rest))))

(def-fns _ $ (many at-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many ids) (erased _)) $ list-append _ (Cons _ null-id $ lit-ids $ env-lits env) $ scope-ids $ env-scope env)
  (match many (at-shown env $ at-classes env ids $ Nil _) _
    ((Nil _) (list1 _ "slots: every entry is at a slot of its own"))
    ((Cons _ c cs) (list1 _ $ str-cat "slots, the entries at one slot: " $ join-strs (Cons _ c cs) " "))))

(def-fns _ $ (many not-prelude : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) (Nil _)))
  (match many (is-prelude env x) _ ((BTrue) (tail $ not-prelude env rest)) ((BFalse) (Cons _ x $ notail $ not-prelude env rest))))

(def-fns _ $ (many opened-split : (many (Env) env) (many (Bool) all) (subterm many (List $ Opened) os) -> (many (List $ String) shown) (many (Nat) prelude))
  (let-match many os (Cons _ o rest) ((Nil _) (values (Nil _) 0)))
  (let ((many shown) (many n)) $ notail $ opened-split env all rest)
  (let ((many s)) $ Cons _ (show-t env $ type-of env $ opened-x o) shown)
  (match many (is-prelude env $ opened-x o) _
    ((BTrue) (values (match many all (((List $ String) _)) ((BTrue) s) ((BFalse) shown)) $ Succ n))
    ((BFalse) (values s n))))

(def-fns _ $ (many opened-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many none)) $ match many (not-prelude env $ scope-ids $ env-scope env) (((Bool) _)) ((Nil _) (BTrue)) (else (BFalse)))
  (let ((many shown) (many n)) $ opened-split env none $ env-opens env)
  (let ((many header)) $ match many none (((String) _))
    ((BTrue) (str-cat3 "opened (the program has bound nothing, so the prelude's " (nat-str n) " are listed)"))
    ((BFalse) (str-cat "opened, beyond the prelude's " $ nat-str n)))
  (list1 _ $ str-cat3 header ": " $ match many shown (((String) _)) ((Nil _) "none") ((Cons _ _ _) (join-strs shown " "))))

(def-fns _ $ (many numeral-rules : (many (Env) env) (subterm many (List $ LitEntry) ls) -> (many (List $ String) r))
  (let-match many ls (Cons _ l rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ numeral-rules env rest)
  (let-match many l (MkLitEntry x _ _ _ _))
  (let-match many (lit-entry-spelling l) (Some _ s) ((None _) more))
  (let-match many (all-digits s) (BTrue) ((BFalse) more))
  (let ((many c)) $ canon-env env $ TVar x)
  (match many c _ ((TApp _ _) (Cons _ (str-cat3 s " is " $ show-t env c) more)) (else more)))

(def-fns _ $ (many literal-lines : (many (Env) env) -> (many (List $ String) r))
  (match many (numeral-rules env $ env-lits env) _
    ((Nil _) (Nil _))
    ((Cons _ r rs) (list1 _ $ str-cat "numerals with rules: " $ join-strs (Cons _ r rs) "; "))))

(def-fns _ $ (many entries-lines : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (cat-strs (prefix-all "  " $ entry-lines env x) $ notail $ entries-lines env rest))))

(def-fns _ $ (many scope-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many mine)) $ not-prelude env $ scope-ids $ env-scope env)
  (let ((many n)) $ nat-str $ list-length _ $ scope-ids $ env-prelude env)
  (match many mine _
    ((Nil _) (Cons _ (str-cat3 "in scope, newest first (the program has bound nothing, so the prelude's " n " are listed):") $ entries-lines env $ scope-ids $ env-scope env))
    (else (Cons _ (str-cat3 "in scope, newest first (" (nat-str $ list-length _ mine) $ str-cat3 " entries; the prelude's " n $ say env " are not listed, and `(dump-context x)` shows any one):")
      $ entries-lines env mine))))

(def-fns _ $ (many focus-lines : (many (Env) env) (subterm many (List $ Focus) fs) -> (many (List $ String) r))
  (let-match many fs (Cons _ f rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ focus-lines env rest)
  (let-match many f (MkFocus source t ty))
  (let ((many (Maybe $ Nat) variable)) $ match many t _ ((TVar x) (match many (is-meta env x) _ ((BTrue) (None _)) ((BFalse) (Some _ x)))) (else (None _)))
  (let-match many variable (None _) ((Some _ x) (cat-strs (entry-lines env x) more)))
  (let ((many (String) typed)) $ match many ty _ ((TErr _) "") (else (str-cat " : " $ qshow env ty)))
  (Cons _ (str-cat3 (tick source) " canonicalizes to " $ str-cat (qshow env t) typed) more))

(def-fns _ $ (many dump-report : (many (Env) env) (many (Goal) wanted) (many (List $ Focus) focus) -> (many (Env) r))
  (let ((many (List $ String) shown)) $ match many focus _ ((Nil _) (scope-lines env)) ((Cons _ _ _) (focus-lines env focus)))
  (let ((many body)) $ cat-strs (goal-lines env wanted) $ cat-strs (position-lines env wanted) $ cat-strs shown $ cat-strs (at-lines env) $ cat-strs (opened-lines env) $ literal-lines env)
  (env-error env $ join-strs (Cons _ (say env "`dump-context` stops elaboration here and reports what the checker knows") $ prefix-all "  " body) "\n"))

(def-fns _ $ (many deep-body : (many (Env) env) (many (List $ Syn) body) -> (many (Bool) r))
  (let-match many body (Cons _ item rest) ((Nil _) (BFalse)))
  (let-match many rest (Nil _) ((Cons _ _ _) (BTrue)))
  (let-match many item (RList _ items) (else (BFalse)))
  (let-match many items (Cons _ head _) ((Nil _) (BFalse)))
  (or (is-special env head $ SpExpr $ ExMatch) $ is-special env head $ SpExpr $ ExCellMatch))

(def-fns _ $ (many deepen : (many (Env) env) (many (List $ Syn) body) (many (Maybe $ Nat) flat) (many (List $ Maybe $ Nat) deep) -> (many (List $ Maybe $ Nat) r))
  (match many (deep-body env body) _ ((BTrue) (Cons _ flat deep)) ((BFalse) deep)))

(def-fns _ $ (many warn-lopsided : (many (Env) env) (many (Maybe $ Loc) final) (many (List $ Maybe $ Nat) deep) -> (many (Env) r))
  (let-match many final (Some _ l) ((None _) env))
  (let-match many deep (Cons _ d rest) ((Nil _) env))
  (let-match many rest (Nil _) (else env))
  (let-match many d (Some _ c) ((None _) env))
  (let-match many (env-run-pos env) (BFalse) ((BTrue) env))
  (env-warn-at env l $ str-cat (say env "lopsided `match`; flatten it with a `let-match` on ") $ qshown env c))

(def-fns _ $ (many call-returns : (unique (ElabWorld) ew) (many (Env) env3) (many (List $ List $ Nat) ctx) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre) (many (List $ Multiplicity) expect) (many (List $ Entry) rets) (many (List $ Term) acc) (many (Multiplicity) pos) (many (ExprDemand expect) demand) (many (Maybe $ Nat) cid) (many (String) fallback) (many (Invoke ctx2) inv) -> (unique (ElabWorld) ewr at ew)
    (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (let ((many rmults)) $ physical-mults rets)
  (let ((many env4) (many ids) (erased _)) $ open-tele rets env3 (Some _ $ anon-names rets) (Some _ $ list-replicate _ (list-length _ rets) $ Some _ $ env-loc env3) (Some _ $ under-list (tele-mults rets) pos) acc $ BFalse)
  (let ((many (Env) env5) (many (Hoisted ctx expect) code))
    (match many (mult-is-many pos) _
      ((BFalse) (values env4 $ hoist-none ctx expect $ CErased _ expect))
      ((BTrue)
        (let ((many (Code ctx2 rmults) call))
          (match many inv _
            ((InvApp _ hid actuals cc2 skipped)
              (let-match many skipped (BFalse) ((BTrue) (let ((many missing) (erased pk)) $ codes-missing ctx2 rmults) (CValues _ rmults missing pk)))
              (CApp ctx2 rmults (var-code env4 ctx2 hid) actuals cc2))
            ((InvWorld _ actuals)
              (let-match many actuals (Cons _ _ more) ((Nil _) (CError _ rmults "world-do arity")))
              (let-match many more (Cons _ req _) ((Nil _) (CError _ rmults "world-do arity")))
              (match many (mults-same many-one rmults) _
                ((Some _ same) (recast _ rmults many-one same $ CWorldDo _ req))
                ((None _) (CError _ rmults "world-do returns"))))
            ((InvPrim _ p actuals)
              (let-match many (is-some _ $ prim-named implemented $ sp-name p) (BTrue) ((BFalse) (let ((many missing) (erased pk)) $ codes-missing ctx2 rmults) (CValues _ rmults missing pk)))
              (CPrim ctx2 rmults p actuals))))
        (let-match many (lockstep-dec _ _ rmults ids) (LdYes _ _ _ _ lk)
          ((LdNo _ _ _ _) (values (env-error env4 "internal: call return count") $ hoist-none ctx expect $ CError _ expect "size")))
        (let ((many bound) (erased bpk)) $ picked-of _ rmults ids lk)
        (let ((many env5) (many kept) (erased kpk)) $ result-codes expect rets ids acc env4 $ Cons _ bound ctx2)
        (let ((many (Code ctx2 expect) code)) $ CLet _ rmults _ bound bpk call $ CValues _ expect kept kpk)
        (let-match many (and (env-run-pos env5) $ not $ env-failed env5) (BTrue) ((BFalse) (values env5 $ MkHoisted _ _ ctx2 pre code)))
        (let-match many ctx2 (Nil _) ((Cons _ _ _) (values env5 $ MkHoisted _ _ ctx2 pre code)))
        (let ((many all)) $ under-list (tele-mults rets) pos)
        (let ((many env6) (many every) (erased epk)) $ result-codes all rets ids acc env5 $ Cons _ bound ctx2)
        (let ((erased _) (many hp)) $ env-heap env6)
        (let ((erased _) (many hp2) (erased _) (many vs) (erased _)) $ run-code (env-fuel env6) _ hp _ $ CLet _ rmults _ bound bpk call $ CValues _ all every epk)
        (let ((many env7)) $ env-with-heap env6 _ $ set-run-states _ hp2 (kept-ids all ids) vs)
        (let ((many codes) (erased cpk)) $ const-codes ctx2 expect $ kept-ids expect ids)
        (values env7 $ MkHoisted _ _ ctx2 pre $ CValues _ expect codes cpk))))
  (let ((many env6) (many ress)) $ returns-produced _ env5 demand cid fallback expect rets $ ress-of ids env5)
  (values ew env6 ress code))


(def-fns _ $ (many at-taken : (many (Env) env) (many (Multiplicity) m) (many (Multiplicity) want) (many (Res) h) -> (many (Env) r))
  (match many (mult-eq m want) _
    ((BTrue) env)
    ((BFalse) (env-error env $ str-cat3 (say env "the head ") (qshow env $ res-term h) $ str-cat3 " : " (qshow env $ canon-env env $ res-ty h) $ str-cat3 " is taken at " (tick $ spell env $ mult-name want) $ str-cat " here; write " $ tick $ str-cat3 "(" (spell env "at") $ str-cat3 " " (spell env $ mult-name want) " (...))"))))
(def-fns _
  ; An expression of the given size and erasures (sections 14, 27); [tele] is the telescope a bare _ reuses.
  ((many elab-expr-demand : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (Syn) raw) (many (Env) env-in) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) (many (ExprDemand expect) demand) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code) (erased (Lockstep (Multiplicity) (Res) expect ress) lock))
    (let ((unique ew1) (many env-x) (many mx)) $ expand-one ew env-in raw)
    (let-match many mx (None _)
      ((Some _ er)
        (let ((many envx)) $ env-at env-x $ raw-pos raw)
        (match many er _
          ((Fail _ m)
            (let ((unique ew2) (many env2) (many ress) (many h)) $ expr-error ew1 ctx expect envx m "macro")
            (let ((many ress2) (erased lock)) $ list-fit _ _ expect ress no-res)
            (values ew2 env2 ress2 h lock))
          ((Ok _ out)
            (let-match many fuel (Succ f2)
              ((Zero)
                (let ((unique ew3) (many env2) (many ress) (many h)) $ expr-error ew1 ctx expect envx "more than 10000 macro expansions" "macro")
                (let ((many ress2) (erased lock)) $ list-fit _ _ expect ress no-res)
                (values ew3 env2 ress2 h lock)))
            (tail $ elab-expr-demand ew1 f2 (raw-size out) out env-x ctx expect tele cc demand)))))
    (let ((unique ew4) (many env-y) (many sy)) $ splice-call ew1 env-x raw)
    (let-match many sy (None _)
      ((Some _ ry)
        (let-match many ry (Ok _ raw2)
          ((Fail _ m)
            (let ((unique ew5) (many env2) (many ress) (many h)) $ expr-error ew4 ctx expect env-y m "macro")
            (let ((many ress2) (erased lock)) $ list-fit _ _ expect ress no-res)
            (values ew5 env2 ress2 h lock)))
        (let-match many fuel (Succ f2)
          ((Zero)
            (let ((unique ew6) (many env2) (many ress) (many h)) $ expr-error ew4 ctx expect env-y "more than 10000 macro expansions" "macro")
            (let ((many ress2) (erased lock)) $ list-fit _ _ expect ress no-res)
            (values ew6 env2 ress2 h lock)))
        (tail $ elab-expr-demand ew4 f2 (raw-size raw2) raw2 env-y ctx expect tele cc demand)))
    (let ((many env) (many sink) (many final)) $ env-take-sink env-y)
    (let ((many start)) $ env-fresh-bound env)
    (let ((many envl0)) $ env-at env $ raw-pos raw)
    (let ((many envl)) $ env-set-usage-erased envl0 $ or (env-usage-erased env) $ not $ mult-is-many $ pos-mult expect)
    (let ((many pos0) (erased pf)) $ pos-of expect)
    (let ((many pos)) $ pos-in envl expect)
    (let ((unique ew7) (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
      (match many raw (((ElabWorld) _ at ew4) ((Env) env2) ((List $ Res) ress) ((Hoisted ctx expect) code))
        (else
          (let ((many env1) (many x)) $ atom-var envl raw "a name")
          (let ((many mode)) (demand-mode _ env1 demand (pos-in env1 expect) (type-of env1 x)))
          (let ((many env2)) $ use-entry-as env1 mode x (BFalse) $ raw-atom raw)
          (let ((many r)) $ res-of env2 x)
          (values ew4 env2 (Cons _ (conformed mode r) $ Nil _) $ hoist-none ctx expect $ coercible-code _ expect (Many) $ var-code env2 ctx x))
        ((RList _ items)
          (let-match many items (Cons _ head args) ((Nil _) (expr-error ew4 ctx expect envl "empty form" "empty form")))
          (match many (special-of envl head) (((ElabWorld) _ at ew4) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
            ((Some _ sp)
              (let-match many (misplaced envl raw) (None _) ((Some _ _) (expr-error ew4 ctx expect envl (not-a envl "not an expression" raw) "misplaced")))
              (let ((many envl2)) $ read-special envl head (BFalse) pos)
              (let ((many multi)) $ or (sp-eq sp $ SpExpr $ ExWorldDo) $ or (sp-eq sp $ SpExpr $ ExGensym) $ or (sp-eq sp $ SpExpr $ ExInternNat) $ or (sp-eq sp $ SpExpr $ ExInternChar) $ or (sp-eq sp $ SpExpr $ ExInternString) $ or (sp-eq sp $ SpExpr $ ExMintSettled) $ or (sp-eq sp $ SpExpr $ ExMintSettledErased) $ or (sp-eq sp $ SpExpr $ ExSettledEq) $ or (sp-eq sp $ SpExpr $ ExResolve) $ or (sp-eq sp $ SpExpr $ ExReadFile) $ or (sp-eq sp $ SpExpr $ ExGensymUnique) $ or (sp-eq sp $ SpExpr $ ExPlaceAt) $ or (sp-eq sp $ SpExpr $ ExPlaceAtMany) $ or (sp-eq sp $ SpExpr $ ExUnplaceAt) $ or (sp-eq sp $ SpExpr $ ExUnplaceAtMany) $ or (sp-eq sp $ SpExpr $ ExPlacedSlot) $ or (sp-eq sp $ SpExpr $ ExPlacedEq) $ or (sp-eq sp $ SpExpr $ ExCellMatch) $ or (sp-eq sp $ SpExpr $ ExValues) $ or (sp-eq sp $ SpExpr $ ExMatch) $ or (sp-eq sp $ SpExpr $ ExOpenAbsurd) $ or (sp-eq sp $ SpMark $ MkTail) $ or (sp-eq sp $ SpMark $ MkNoTail) $ or (sp-eq sp $ SpMark $ MkDelegate) $ or (sp-eq sp $ SpMark $ MkAt) $ or (sp-eq sp $ SpStmt $ StCompileError) $ sp-eq sp $ SpStmt $ StDumpContext)
              (let ((many (Env) env0))
                (match many multi _
                  ((BTrue) envl2)
                  ((BFalse)
                    (let-match many expect (Cons _ _ rest)
                      ((Nil _) (env-error envl2 $ str-cat (tick $ spell envl2 $ sp-name sp) " produces one value")))
                    (match many rest (((Env) _)) ((Nil _) envl2) ((Cons _ _ _) (env-error envl2 $ str-cat (tick $ spell envl2 $ sp-name sp) " produces one value"))))))
              (let-match many (match many (sp-arity sp) (((Bool) _)) ((None _) (BTrue)) ((Some _ n) (nat-eq n $ list-length _ args))) (BTrue) ((BFalse) (malformed ew4 ctx expect env0 sp)))
              (let ((many kw)) $ sp-name sp)
              (let ((many proof-what)) $ Some _ $ WForm kw args ", a proof and so erased")
              (match many sp (((ElabWorld) _ at ew4) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                ((SpFormer _)
                  (let ((many env1)) $ error-when env0 (mult-is-many pos) "a type in a non-erased position")
                  (let ((unique ew8) (many env2) (many t)) $ notail $ elab-type-form ew4 fuel sugar args two-steps env1 sp)
                  (erased-result ew8 ctx expect (None _) env2 $ term-res t type-term))
                ((SpStmt sk)
                  (let-match many sk (StDumpContext)
                    ((StCompileError) (let ((unique ew9) (many envm) (many margs)) $ notail $ settle-message ew4 fuel sugar args env0) (values ew9 (compile-say envm sp margs pos) (Nil _) $ hoist-none ctx expect $ CError _ expect "compile-error"))
                    (else (expr-error ew4 ctx expect env0 (str-cat3 (spell-marks env0 $ tick $ str-cat3 "(" (kw-mark kw) $ match many args (((String) _)) ((Nil _) ")") (else " ...)")) " is a statement, not an expression" $ sp-hints env0 $ sp-name sp) "statement as expression")))
                  (let ((unique ew10) (many env1) (many focus)) $ notail $ elab-focus ew4 fuel sugar args _ two-steps env0)
                  (values ew10 (dump-report env1 (GoalValues expect tele) focus) (Nil _) $ hoist-none ctx expect $ CError _ expect "dump-context"))
                ((SpMark mk)
                  (match many mk (((ElabWorld) _ at ew4) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                    ((MkAt) (notail $ elab-cell-at ew4 fuel sugar args env0 ctx expect tele))
                    ((MkTail) (notail $ elab-marked ew4 fuel sugar args (env-set-sink env0 sink) ctx expect tele (CCTail) sp demand))
                    ((MkNoTail) (notail $ elab-marked ew4 fuel sugar args (env-set-sink env0 sink) ctx expect tele (CCNoTail) sp demand))
                    ((MkDelegate) (notail $ elab-marked ew4 fuel sugar args (env-set-sink env0 sink) ctx expect tele (CCDelegate) sp demand))
                    (else (malformed ew4 ctx expect env0 sp))))
                ((SpExpr ex)
                  (match many ex (((ElabWorld) _ at ew4) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                    ((ExSlotOf)
                      (let ((many env1r) (many id)) (slot-var env0 (one-arg args)))
                      (let ((many env1)) $ env-refer env1r (and (mult-is-many pos) $ not $ env-usage-erased env1r) id)
                      (let ((many env1b)) $ match many (and (mult-is-many pos) $ not $ mult-is-many $ entry-mult-of env1 id) (((Env) _))
                        ((BTrue) (env-error env1 $ say env1 $ str-cat3 (qshow env1 $ slot-atom id) " is erased, as " $ str-cat (qname env1 id) " is, and stands in a non-erased position"))
                        ((BFalse) env1))
                      (cell-result-hoisted ew4 ctx expect env1b (MkRes (slot-term-of env1b id) slot-term (pos-in env1b expect) $ Some _ $ slot-atom id) (hoist-none ctx many-one $ var-code env1b ctx id)))
                    ((ExAtFnOf)
                      (let ((unique ew11) (many env2) (many found)) $ notail $ fetched ew4 fuel sugar args one-step env0 ex)
                      (match many found (((ElabWorld) _ at ew11) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                        ((None _) (values ew11 env2 (Nil _) $ hoist-none ctx expect $ CError _ expect "no AtFn proof"))
                        ((Some _ x) (erased-result ew11 ctx expect proof-what env2 $ res-of env2 $ term-var x))))
                    ((ExCellAlloc)
                      (let ((unique ew12) (many env1) (many rs) (many c)) $ notail $ elab-cell-alloc ew4 fuel sugar args env0 ctx expect)
                      (let ((many env2) (many rs2)) $ produced-first expect env1 demand (WForm kw args ", a fresh cell and so unique") rs)
                      (values ew12 env2 rs2 c))
                    ((ExCellWrite)
                      (let ((unique ew13) (many env1) (many rs) (many c)) $ notail $ elab-cell-write ew4 fuel sugar args env0 ctx expect)
                      (let ((many env2) (many rs2)) $ produced-first expect env1 demand (WForm kw args ", a cell and so unique") rs)
                      (values ew13 env2 rs2 c))
                    ((ExCellMatch) (notail $ elab-cell-match ew4 fuel sugar args env0 ctx expect tele demand))
                    ((ExCellSame) (notail $ elab-same ew4 fuel sugar ex kw args env0 ctx expect demand))
                    ((ExFnSame) (notail $ elab-same ew4 fuel sugar ex kw args env0 ctx expect demand))
                    ((ExShare)
                      (let-match many args (Cons _ arg rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((many env1)) $ refuse-unless env0 (list-is-empty _ rest) "`share` takes one value")
                      (let ((many env1c)) $ refuse-when env1 (not $ mult-is-many pos) "`share` in an erased position")
                      (let ((many mode)) $ under pos $ Once)
                      (let ((unique ew14) (many env2) (many r) (many physical))
                        (match many arg (((ElabWorld) _ at ew4) ((Env) _) ((Res) r) ((Hoisted ctx many-one) c))
                          ((RAtom _ n)
                            (let ((many env2) (many x)) $ var (env-at env1c $ raw-pos arg) n)
                            (let ((many env3)) $ refuse-when env2 (and (mult-is-many pos) $ not $ mult-is-once $ made env2 arg x) "`share` needs a unique value")
                            (let ((many env4)) $ use-entry env3 (under pos $ Many) x $ BTrue)
                            (values ew4 (env-back env1c env4) (res-of env4 x) $ hoist-none ctx many-one $ var-code env4 ctx x))
                          (else
                            (let ((unique ew15) (many env2) (many rs) (many h) (erased lock)) $ notail $ elab-expr-demand ew4 fuel sugar arg env1c ctx (Cons _ mode $ Nil _) no-tele (CCPlain) (Fixed _))
                            (let-match many h (MkHoisted _ _ c2 pre code))
                            (values ew15 env2 (first-res _ _ rs lock) $ MkHoisted _ _ c2 pre $ runtime-one _ mode code))))
                      (let ((many env2s) (many rs)) $ produced env2 (WForm kw args ", shared and so many") (demand-mode _ env2 demand (pos-in env2 expect) $ res-ty r) $ MkRes (res-term r) (res-ty r) (under pos $ Many) $ res-place r)
                      (cell-result-hoisted ew14 ctx expect env2s rs physical))
                    ((ExValues)
                      (let-match many demand (Fixed _)
                        ((CallableHead p) (notail $ elab-values-one ew4 fuel sugar args env0 ctx tele (CallableHead p)))
                        ((FinalDemand) (notail $ elab-values-one ew4 fuel sugar args env0 ctx tele (FinalDemand))))
                      (let ((many n)) $ list-length _ expect)
                      (let ((many na)) $ list-length _ args)
                      (let ((many env1)) $ match many (nat-eq n na) (((Env) _)) ((BTrue) env0) ((BFalse) (count-values env0 sink n na)))
                      (let ((unique ew16) (many env2) (many ress) (many ctx2) (many pre) (many codes) (erased pk)) $ notail $ elab-values ew4 fuel sugar args env1 ctx expect tele $ Nil _)
                      (values ew16 env2 ress $ MkHoisted _ _ ctx2 pre $ CValues _ expect codes pk))
                    ((ExMatch)
                      (let ((unique ew17) (many env2) (many ress) (many code)) $ notail $ elab-match ew4 fuel sugar args env0 ctx expect tele demand (BFalse) "`match`" $ match many final (((Maybe $ Loc) _)) ((BTrue) (Some _ $ loc-in envl $ raw-pos head)) ((BFalse) (None _)))
                      (values ew17 env2 ress code))
                    ((ExMatchableOf)
                      (let ((unique ew18) (many env3) (many found)) $ notail $ fetched ew4 fuel sugar args one-step env0 ex)
                      (let-match many found (Some _ mt)
                        ((None _) (values ew18 env3 (Nil _) $ hoist-none ctx expect $ CError _ expect "no Matchable")))
                      (let ((many mid)) (term-var mt))
                      (let ((many env4) (many r)) $ produced env3 (WOpened kw args mid) (demand-mode _ env3 demand (pos-in env3 expect) $ type-of env3 mid) $ res-of env3 mid)
                      (let ((many env5)) $ match many (misuse (under pos $ Many) $ entry-mult-of env3 mid) (((Env) _)) ((None _) (use-entry env4 (under pos $ Many) mid $ BFalse)) ((Some _ _) env4))
                      (values ew18 env5 (Cons _ r $ Nil _) $ hoist-none ctx expect $ single _ expect pos0 pf $ matchable-code env3 ctx pos0 mid))

                    ((ExNumeralOf)
                      (let ((unique ew19) (many env2) (many found)) $ notail $ fetched ew4 fuel sugar args one-step env0 ex)
                      (match many found (((ElabWorld) _ at ew19) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                        ((None _) (values ew19 env2 (Nil _) $ hoist-none ctx expect $ CError _ expect "numeral-of"))
                        ((Some _ p) (erased-result ew19 ctx expect proof-what env2 $ res-of env2 $ term-var p))))
                    ((ExProveLiteralLt)
                      (let ((many env2) (many found)) $ mint-literal-lt env0 args)
                      (match many found (((ElabWorld) _ at ew4) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                        ((None _) (values ew4 env2 (Nil _) $ hoist-none ctx expect $ CError _ expect "prove-literal-lt"))
                        ((Some _ r) (erased-result ew4 ctx expect proof-what env2 r))))
                    ((ExOpenAbsurd)
                      (let-match many args (Cons _ eraw more) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let-match many more (Cons _ ann more2) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let-match many more2 (Nil _) ((Cons _ _ _) (malformed ew4 ctx expect env0 sp)))
                      (let ((unique ew20) (many env1) (many ress) (many h0) (erased lock)) $ notail $ elab-expr-demand ew4 fuel sugar eraw env0 ctx erased-one no-tele (CCPlain) (Fixed _))
                      (let-match many h0 (MkHoisted _ _ c0 _ code0))
                      (let ((many env3)) $ open-contradicts c0 env0 env1 (first-res _ _ ress lock) code0)
                      (let ((unique ew21) (many env4) (many ann-tele) (many _) (many _) (many _)) $ notail $ result-tele ew20 fuel sugar ann env3 expect tele demand)
                      (let ((many env5) (many rids) (erased _)) $ open-tele ann-tele env4 (Some _ $ anon-names ann-tele) (None _) (None _) (Nil _) $ BFalse)
                      (values ew21 env5 (ress-of rids env5) $ hoist-none ctx expect $ match many pos (((Code ctx expect) _)) ((Erased) (CErased _ expect)) (else (CAbsurd _ expect))))
                    ((ExLevelOf)
                      (let ((unique ew22) (many env2) (many found)) $ notail $ fetched ew4 fuel sugar args one-step env0 ex)
                      (match many found (((ElabWorld) _ at ew22) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                        ((None _) (values ew22 env2 (Nil _) $ hoist-none ctx expect $ CError _ expect "level-of"))
                        ((Some _ lv) (erased-result ew22 ctx expect (Some _ $ WForm kw args ", a `Level` and so erased") env2 $ MkRes lv level-term (Erased) $ None _))))
                    ((ExProveSubterm)
                      (let ((unique ew23) (many env2) (many a2) (many aty) (many b2) (many bty)) $ notail $ elab-two-terms ew4 fuel sugar args env0)
                      (let ((many env3) (many r)) $ mint-subterm env2 a2 aty b2 bty)
                      (erased-result ew23 ctx expect proof-what env3 r))
                    ((ExProvePredates)
                      (let-match many args (Cons _ xraw rest)
                        ((Nil _) (expr-error ew4 ctx expect env0 (sp-misuse env0 $ SpExpr $ ExProvePredates) "prove-predates")))
                      (let ((unique ew24) (many env2) (many x)) $ match many xraw (((ElabWorld) _ at ew4) ((Env) _) ((Nat) _))
                        ((RList _ _)
                          (let ((unique ew25) (many env1) (many xt) (many _)) $ notail $ elab-one-term ew4 fuel sugar args env0)
                          (match many xt _ ((TVar y) (values ew25 env1 y)) (else (values ew25 (env-error env1 $ str-cat "expected a variable or a fetch form, got " $ tick $ rope-str $ show-raw xraw) $ Zero))))
                        (else (let ((many ewt1) (many ewt2)) (var-of-raw env0 xraw "a variable")) (values ew4 ewt1 ewt2)))
                      (let ((unique ew26) (many env3) (many lt) (many _)) $ notail $ elab-one-term ew24 fuel sugar rest env2)
                      (let ((many env4) (many lvl)) $ level-binder env3 lt)
                      (let ((many env5) (many r)) $ mint-predates env4 x lvl)
                      (erased-result ew26 ctx expect proof-what env5 r))
                    ((ExPredatesTrans)
                      (let ((unique ew27) (many env1) (many p) (many q)) $ notail $ two-proofs ew4 fuel sugar args env0 ctx)
                      (let ((many env2) (many r)) $ trans-proofs env1 predates-id 3 p q)
                      (erased-result ew27 ctx expect proof-what env2 r))
                    ((ExSubtermTrans)
                      (let ((unique ew28) (many env1) (many p) (many q)) $ notail $ two-proofs ew4 fuel sugar args env0 ctx)
                      (let ((many env2) (many r)) $ trans-proofs env1 subterm-id 4 p q)
                      (erased-result ew28 ctx expect proof-what env2 r))
                    ((ExCoercibleTrans)
                      (let-match many args (Cons _ _ rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((many env1) (many mid)) $ bind-as env0 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) sharing-term (None _) delegate-id)
                      (let ((many first)) $ match many (expected-coercible-sides env1 tele) (((Maybe $ Pair (Term) $ Term) _)) ((None _) (None _)) ((Some _ sides) (match many sides (((Maybe $ Pair (Term) $ Term) _)) ((MkPair _ _ sa _) (Some _ $ MkPair _ _ sa $ TVar mid)))))
                      (let ((unique ew29) (many env2) (many p)) $ notail $ elab-coercible-proof ew4 fuel sugar args env1 ctx coercible-id first)
                      (let ((many env3) (many sa) (many ta) (many va) (many sm) (many tb) (many vb)) $ expect-proof6 env2 coercible-id "" p)
                      (let ((many target)) $ match many (expected-coercible-sides env3 tele) (((Term) _)) ((None _) (TVar mid)) ((Some _ sides) (match many sides (((Term) _)) ((MkPair _ _ _ s2) s2))))
                      (let ((unique ew30) (many env4) (many q)) $ notail $ elab-coercible-proof ew29 fuel sugar rest env3 ctx coercible-id $ Some _ $ MkPair _ _ sm target)
                      (let ((many env5) (many sm2) (many tb2) (many vb2) (many sb) (many tc) (many vc)) $ expect-proof6 env4 coercible-id "" q)
                      (let ((many env6)) $ check (check (check env5 "sharing" sm sm2) "type" tb tb2) "value" vb vb2)
                      (let ((many env7) (many r)) $ coercible-mint env6 tele $ proof-type coercible-id $ Cons _ sa $ Cons _ ta $ Cons _ va $ Cons _ sb $ Cons _ tc $ Cons _ vc $ Nil _)
                      (erased-result ew30 ctx expect proof-what env7 r))
                    ((ExPredatesSubterm)
                      (let ((unique ew31) (many env1) (many p) (many q)) $ notail $ two-proofs ew4 fuel sugar args env0 ctx)
                      (let ((many env2a) (many _) (many p1) (many p2)) $ expect-proof3 env1 predates-id "" p)
                      (let ((many env2) (many q0) (many q1) (many _) (many q3)) $ expect-proof4 env2a subterm-id "" q)
                      (let ((many env3)) $ check env2 "value" q3 p1)
                      (let ((many env4) (many r)) $ mint env3 $ proof-type predates-id $ Cons _ q0 $ Cons _ q1 $ Cons _ p2 $ Nil _)
                      (erased-result ew31 ctx expect proof-what env4 r))
                    ((ExCoerce)
                      (let-match many args (Cons _ araw rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((unique ew32) (many env1) (many p)) $ notail $ elab-coercible-proof ew4 fuel sugar rest env0 ctx coercible-id $ None _)
                      (let ((many env2) (many sa) (many _) (many va) (many sb) (many tb) (many vb)) $ expect-proof6 env1 coercible-id "" p)
                      (let ((many env3) (many src) (many dst))
                        (match many pos (((Env) _) ((Multiplicity) src) ((Multiplicity) dst))
                          ((Erased) (values env2 (Erased) $ Erased))
                          (else
                            (let ((many env2a) (many src)) $ sharing-mult env2 sa)
                            (let ((many env2b) (many dst)) $ sharing-mult env2a sb)
                            (values env2b src dst))))
                      (let ((unique ew33) (many env4) (many ars) (many h) (erased lock)) $ notail $ elab-expr-demand ew32 fuel sugar araw env3 ctx (Cons _ src $ Nil _) no-tele (CCPlain) (Fixed _))
                      (let-match many h (MkHoisted _ _ c2 pre code))
                      (let ((many ar)) $ first-res _ _ ars lock)
                      (let ((many env5)) $ check (settle-res env4 ar) "value" (res-term ar) va)
                      (let ((many env6) (many x)) $ bind env5 (None _) (None _) (BFalse) dst tb (Some _ vb) delegate-id)
                      (let ((many env7)) $ placed-at env6 x $ res-place ar)
                      (let-match many rest (Cons _ praw _) ((Nil _) (malformed ew33 ctx expect env7 sp)))
                      (let ((many env8) (many r)) $ produced env7 (WCoerce kw args sb praw) (demand-mode _ env7 demand (pos-in env7 expect) tb) $ res-with-place (res-of env7 x) $ res-place ar)
                      (values ew33 env8 (Cons _ r $ Nil _) $ MkHoisted _ _ c2 pre $ coercible-code _ expect src code))
                    ((ExCoercibleRefl)
                      (let-match many args (Cons _ _ rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((unique ew34) (many env1) (many s)) $ notail $ elab-sharing-side ew4 fuel sugar args env0)
                      (let ((unique ew35) (many env2) (many e) (many ty)) $ notail $ elab-one-term ew34 fuel sugar rest env1)
                      (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ s $ Cons _ ty $ Cons _ e $ Cons _ s $ Cons _ ty $ Cons _ e $ Nil _)
                      (erased-result ew35 ctx expect proof-what env3 r))
                    ((ExCoercibleSym)
                      (let ((many sides)) $ match many (expected-coercible-sides env0 tele) (((Maybe $ Pair (Term) $ Term) _)) ((None _) (None _)) ((Some _ p) (match many p (((Maybe $ Pair (Term) $ Term) _)) ((MkPair _ _ sa sb) (Some _ $ MkPair _ _ sb sa)))))
                      (let ((unique ew36) (many env1) (many p)) $ notail $ elab-coercible-proof ew4 fuel sugar args env0 ctx coercible-id sides)
                      (let ((many env2) (many sa) (many ta) (many va) (many sb) (many tb) (many vb)) $ expect-proof6 env1 coercible-id "" p)
                      (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ sb $ Cons _ tb $ Cons _ vb $ Cons _ sa $ Cons _ ta $ Cons _ va $ Nil _)
                      (erased-result ew36 ctx expect proof-what env3 r))
                    ((ExCoercibleShare)
                      (let ((unique ew37) (many env1) (many p)) $ notail $ elab-coercible-proof ew4 fuel sugar args env0 ctx coercible-id $ None _)
                      (let ((many env2) (many _) (many ta) (many va) (many _) (many tb) (many vb)) $ expect-proof6 env1 coercible-id "" p)
                      (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ shared-term $ Cons _ ta $ Cons _ va $ Cons _ shared-term $ Cons _ tb $ Cons _ vb $ Nil _)
                      (erased-result ew37 ctx expect proof-what env3 r))
                    ((ExCoercibleWrap)
                      (let-match many args (Cons _ _ rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((unique ew38) (many env1) (many s)) $ notail $ elab-sharing-side ew4 fuel sugar args env0)
                      (let-match many rest (Cons _ craw wargs) ((Nil _) (malformed ew38 ctx expect env1 sp)))
                      (let ((many env2) (many cid)) $ ctor-var env1 craw)
                      (let ((many ctele) (many ret)) $ ctor-type env2 cid)
                      (let ((many env3)) $ match many (find-newtype env2 cid) (((Env) _)) ((None _) (env-error env2 $ str-cat (qshown env2 cid) (say env2 " has no opened newtype `Matchable` for its wrapping constructor"))) ((Some _ _) env2))
                      (let ((unique ew39) (many env4a) (many acc) (many tys) (many _) (many _) (many _)) $ notail $ check-args ew38 fuel sugar wargs (subs-all wargs) one-step env3 (CalleeWrap env3 cid) ctx ctele (Erased) no-tele (ARApp (TVar cid) ret) (BTrue) (BFalse) (BFalse))
                      (let ((many env4)) $ settle-list acc env4a)
                      (let ((many env5) (many f) (many fty))
                        (match many (wrap-field ctele (list-rev _ acc) $ list-rev _ tys) (((Env) _) ((Term) f) ((Term) fty))
                          ((Some _ pr) (match many pr (((Env) _) ((Term) f) ((Term) fty)) ((MkPair _ _ g gty) (values env4 g gty))))
                          ((None _) (values (env-error env4 "not the wrapping constructor") (TErr "wrapper") $ TErr "wrapper"))))
                      (let ((many env6) (many r)) $ coercible-mint env5 tele $ proof-type coercible-id $ Cons _ (wrap-sharing ctele s) $ Cons _ fty $ Cons _ f $ Cons _ s $ Cons _ (instantiate acc ret) $ Cons _ (TApp (TVar cid) $ list-rev _ acc) $ Nil _)
                      (erased-result ew39 ctx expect proof-what env6 r))
                    ((ExCoercibleCtor)
                      (let-match many args (Cons _ _ rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((unique ew40) (many env1) (many s)) $ notail $ elab-sharing-side ew4 fuel sugar args env0)
                      (let ((many env2)) $ match many (expected-coercible-sides env1 tele) (((Env) _)) ((None _) env1) ((Some _ p) (match many p (((Env) _)) ((MkPair _ _ sa _) (check env1 "sharing" s sa)))))
                      (let-match many rest (Cons _ craw cargs) ((Nil _) (malformed ew40 ctx expect env2 sp)))
                      (let ((many env3) (many cid)) $ ctor-var env2 craw)
                      (let ((many ctele) (many ret)) $ ctor-type env3 cid)
                      (let ((many needed)) $ ctor-arg-count ctele)
                      (let-match many (nat-eq needed $ list-length _ cargs) (BTrue)
                        ((BFalse) (values ew40 (field-count env3 (here-pos env3) "`coercible-ctor`" "more argument" cid ctele needed (list-length _ cargs) "a source and a target for each erased field and a `Coercible` proof for each other field, in the order of") (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "coercible-ctor")))
                      (let ((unique ew41) (many env4) (many src) (many tgt)) $ notail $ coercible-ctor-args ew40 fuel sugar cargs env3 ctx ctele (Nil _) (Nil _) cid s)
                      (let ((many env5) (many r)) $ coercible-mint env4 tele $ proof-type coercible-id $ Cons _ s $ Cons _ (instantiate src ret) $ Cons _ (TApp (TVar cid) $ list-rev _ src) $ Cons _ s $ Cons _ (instantiate tgt ret) $ Cons _ (TApp (TVar cid) $ list-rev _ tgt) $ Nil _)
                      (erased-result ew41 ctx expect proof-what env5 r))
                    ((ExCoercibleOf)
                      (let ((unique ew42) (many env1) (many p)) $ notail $ elab-coercible-proof ew4 fuel sugar args env0 ctx delegate-id $ expected-coercible-sides env0 tele)
                      (let ((many env2) (many sg) (many tg) (many vg) (many sf) (many tf) (many vf)) $ expect-proof6 env1 delegate-id "" p)
                      (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ sg $ Cons _ tg $ Cons _ vg $ Cons _ sf $ Cons _ tf $ Cons _ vf $ Nil _)
                      (erased-result ew42 ctx expect proof-what env3 r))
                    ((ExGensym) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExGensymUnique) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExPlaceAt) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExPlaceAtMany) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExUnplaceAt) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExUnplaceAtMany) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExPlacedSlot) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExPlacedEq) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSlotEq) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledType) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledErase) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExResolve) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExReadFile) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledEq) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledMult) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledValue) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExInternNat) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExInternChar) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExInternString) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExMintSettled) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExMintSettledErased) (notail $ elab-prim-call ew4 fuel sugar items env0 ctx expect tele demand pos sp))
                    ((ExSettledOf)
                      (let-match many args (Cons _ mraw rest) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let-match many rest (Cons _ araw _) ((Nil _) (malformed ew4 ctx expect env0 sp)))
                      (let ((many env1) (many mode)) $ mult-checked env0 mraw)
                      (let ((many env2a) (many x)) $ var-of-raw (env-at env1 $ raw-pos araw) araw "a name")
                      (let ((many env2b)) $ env-refer env2a (and (not $ mult-eq mode $ Erased) $ not $ env-usage-erased env2a) x)
                      (let ((many env3) (many y) (many ty)) $ handle-of (env-back env1 env2b) araw x mode)
                      (let ((many env4) (many h)) $ bind env3 (None _) (None _) (BFalse) (under pos $ Many) ty (None _) delegate-id)
                      (let ((many env5) (many r)) $ produced env4 (WForm kw args ", a handle and so many") (demand-mode _ env4 demand (pos-in env4 expect) ty) $ res-of env4 h)
                      (values ew4 env5 (Cons _ r $ Nil _) $ hoist-none ctx expect $ coercible-code _ expect (Many) $ CValue _ $ BExt _ $ PHandle y (MintedIs) mode $ shown-entry env5 y))
                    ((ExWorldDo)
                      (let ((many request)) $ lookup (env-set-scope env0 $ env-prelude env0) $ NSrc "Request")
                      (let-match many request (Some _ rq) ((None _) (values ew4 (env-error env0 "`world-do` needs the prelude's `Request`") (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "world-do")))
                      (let ((many params)) $ Cons _ (ty-entry "A" type-term) $ Cons _ (MkEntry (Some _ $ NSrc "w") (BFalse) (Once) (SgTy world-term) (None _) (None _))
                        $ Cons _ (MkEntry (Some _ $ NSrc "req") (BFalse) (Once) (SgTy $ TApp (TVar rq) $ Cons _ (TBound 1) $ Nil _) (None _) (None _)) $ Nil _)
                      (let ((many rets)) $ Cons _ (MkEntry (Some _ $ NSrc "w2") (BFalse) (Once) (SgTy world-term) (Some _ $ TSlotOf $ TBound 1) (None _))
                        $ Cons _ (MkEntry (Some _ $ NSrc "r") (BFalse) (Many) (SgTy $ TBound 3) (None _) (None _)) $ Nil _)
                      (let ((unique ew43) (many env2) (many acc) (many _) (many ctx2) (many apre) (many actuals)) $ notail $ check-args ew4 fuel sugar args (subs-all args) one-step env0 (CalleeForm env0 "world-do") ctx params pos tele (ARCall rets) (BFalse) (BTrue) $ BTrue)
                      (call-returns ew43 env2 ctx ctx2 apre expect rets acc pos demand (None _) (tick $ kw-mark "world-do") $ InvWorld _ actuals))
                    ((ExDelegateOf)
                      (let ((unique ew44) (many env2) (many found)) $ notail $ fetched ew4 fuel sugar args one-step env0 ex)
                      (match many found (((ElabWorld) _ at ew44) ((Env) _) ((List $ Res) rs) ((Hoisted ctx expect) c))
                        ((None _) (values ew44 env2 (Nil _) $ hoist-none ctx expect $ CError _ expect "no delegate proof"))
                        ((Some _ x) (erased-result ew44 ctx expect proof-what env2 $ res-of env2 $ term-var x))))))))
            ((None _)
              (let ((unique ew45) (many (Env) env2) (many (Res) h) (many (List $ List $ Nat) ctxh) (many (StmtCode ctx ctxh) hpre) (many (Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hcode))
                (match many head (((ElabWorld) _ at ew4) ((Env) env2) ((Res) h) ((List $ List $ Nat) ctxh) ((StmtCode ctx ctxh) hpre) ((Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hcode))
                  (else (let ((many env2) (many x)) $ var-of-raw envl head "a name") (values ew4 env2 (res-of env2 x) ctx (SNone _) $ coercible-code _ (Cons _ pos $ Nil _) (Many) $ var-code env2 ctx x))
                  ((RList _ _) (notail $ compute-head ew4 fuel sugar items envl ctx pos))))
              (let ((many (Maybe $ Syn) redo)) $ match many head _
                ((RList _ _)
                  (let-match many (res-term h) (TVar y) (else (None _)))
                  (let ((many hraw)) $ handle-raw env2 (raw-pos head) y)
                  (match many (settled-dispatch env2 hraw) _ ((BTrue) (Some _ hraw)) ((BFalse) (None _))))
                (else (None _)))
              (let-match many redo (None _)
                ((Some _ hraw)
                  (let-match many fuel (Succ f2) ((Zero) (expr-error ew45 ctx expect env2 "more than 10000 macro expansions" "macro")))
                  (let ((many raw2)) $ RList (raw-pos raw) $ Cons _ hraw args)
                  (let ((unique ew46) (many env3) (many rs) (many hh) (erased _)) $ notail $ elab-expr-demand ew45 f2 (raw-size raw2) raw2 env2 ctxh expect tele cc demand)
                  (values ew46 env3 rs $ hoist-after _ _ _ hpre hh)))
              (let ((unique ew47) (many env5) (many ress5) (many hc5)) (match many (canon-env env2 $ res-ty h) (((ElabWorld) _ at ew45) ((Env) _) ((List $ Res) rs) ((Hoisted ctxh expect) c))
                ((TCell ctor slots)
                  (let ((many envm) (many rawargs) (many marks)) (cell-marks _ (subs-all args) env2 (BFalse)))
                  (notail $ elab-cell-invoke ew45 fuel sugar args rawargs two-steps envm ctxh expect tele h (describe env2 head (res-term h) (res-ty h)) (runtime-one _ pos hcode) ctor slots (BFalse) marks))
                ((TTyCtor ttele)
                  (let ((many tc)) $ describe env2 head (res-term h) (res-ty h))
                  (let ((many env3)) $ match many (mult-is-many pos) (((Env) _))
                    ((BFalse) env2)
                    ((BTrue) (env-error-with env2 (callee-notes tc) $ str-cat (match many head (((String) _)) ((RAtom _ _) (str-cat "type constructor " $ callee-subject tc)) (else (callee-subject tc))) " applied in a non-erased position")))
                  (let ((unique ew48) (many env4) (many acc) (many _) (many _) (many _) (many _)) $ notail $ check-args ew45 fuel sugar args (subs-all args) one-step env3 tc ctxh ttele (Erased) tele (ARApp (res-term h) type-term) (BTrue) (BFalse) (BFalse))
                  (erased-result ew48 ctxh expect (None _) env4 $ MkRes (TApp (res-term h) $ list-rev _ acc) type-term (Erased) $ None _))
                ((TValCtor ctele ret)
                  (let ((many mode)) (match many demand (((Multiplicity) _)) ((Fixed _) (pos-in env2 expect)) ((CallableHead p) (head-demand env2 ret p)) ((FinalDemand) (final-demand env2 ret))))
                  (let ((many bad-head)) $ and (mult-is-many pos) $ not $ mult-is-many $ res-erasure h)
                  (let ((many env2d)) $ match many bad-head (((Env) _)) ((BTrue) (env-error-with env2 (head-notes env2 h) $ str-cat3 "erased constructor " (head-name env2 h) " in a non-erased position")) ((BFalse) env2))
                  (let ((many env2e)) $ match many (mult-is-many mode) (((Env) _)) ((BTrue) (warn-use env2d (loc-in env2d $ raw-pos head) "application of" $ res-term h)) ((BFalse) env2d))
                  (let ((many env3)) $ match many (res-term h) (((Env) _)) ((TVar x) (match many bad-head (((Env) _)) ((BTrue) env2e) ((BFalse) (use-entry env2e (under pos $ Many) x $ BFalse)))) (else env2e))
                  (let ((many env3a) (many _) (many hid) (many ctx1) (many hsc)) $ hoist-argument env3 ctxh (under pos $ Many) pos h hcode)
                  (let ((unique ew49) (many env4) (many acc) (many _) (many ctx2) (many apre) (many actuals)) $ notail $ check-args ew45 fuel sugar args (subs-all args) one-step env3a (describe env3a head (res-term h) (res-ty h)) ctx1 ctele mode tele (ARApp (res-term h) ret) (BFalse) (BFalse) $ BTrue)
                  (let ((many wrapped)) $ match many (canon-env env4 $ res-term h) (((Bool) _)) ((TVar c) (is-some _ $ find-newtype env4 c)) (else (BFalse)))
                  (let ((many hollow)) $ match many (canon-env env4 $ res-term h) (((Bool) _)) ((TVar c) (hollow-ctor env4 c)) (else (BFalse)))
                  (let ((many place)) $ match many hollow (((Maybe $ Term) _)) ((BTrue) (Some _ $ slot-atom null-id)) ((BFalse) (term-place env4 $ TApp (res-term h) $ list-rev _ acc)))
                  (let ((many result)) $ MkRes (TApp (res-term h) $ list-rev _ acc) (instantiate acc ret) mode place)
                  (let ((many built)) $ match many wrapped (((Code ctx2 many-one) _))
                    ((BFalse) (CApp _ many-one (var-code env4 ctx2 hid) actuals $ CCCtor))
                    ((BTrue) (match many actuals (((Code ctx2 many-one) _)) ((Nil _) (CError _ many-one "no newtype field")) ((Cons _ first _) first))))
                  (let ((many code)) $ match many hollow (((Code ctx2 many-one) _)) ((BTrue) (var-code env4 ctx2 null-id)) ((BFalse) built))
                  (cell-result-hoisted ew49 ctxh expect env4 result $ MkHoisted _ _ ctx2 (SSeq _ _ _ hsc apre) code))
                ((TFn uq lv params rets)
                  (let ((many env2a) (many ann) (many args2)) $ split-annotation args _ (WHere args) env2 0)
                  (notail $ elab-call ew45 fuel sugar args (MkPair _ _ args2 ann) env2a ctxh expect tele h (describe env2 head (res-term h) (res-ty h)) (raw-pos head) pos hcode uq lv params rets cc demand $ BFalse))
                ((TErr m) (not-applicable ew45 ctxh expect env2 head h m)) (else (not-applicable ew45 ctxh expect env2 head h "not applicable"))))
              (values ew47 env5 ress5 $ hoist-after _ _ _ hpre hc5))))))
    (let ((many n)) $ list-length _ expect)
    (let ((many m)) $ list-length _ ress)
    (let ((many ress2) (erased lock)) $ list-fit _ _ expect (metaless-ress ress env2) no-res)
    (let-match many (nat-cmp n m) (CEq _ _ _) (else (values ew7 (env-back env $ count-values env2 sink n m) ress2 code lock)))
    (let ((many env3) (many code3)) $ run-form (env-set-usage-erased (env-back env $ match many demand (((Env) _))
      ((Fixed _) (erased-in-many expect ress2 lock env2))
      ((CallableHead p) (mode-result-check env2 ress2 p $ BFalse))
      ((FinalDemand) (mode-result-check env2 ress2 (Many) $ BTrue))) $ env-usage-erased env) start ctx expect ress2 code)
    (values ew7 env3 ress2 code3 lock))
  ; A values of one entry under a head or driver demand: the entry is elaborated under the same demand.
  ((many elab-values-one : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Maybe $ List $ Entry) tele) (many (ExprDemand many-one) demand) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx many-one) code))
    (let-match many args (Cons _ item _) ((Nil _) (expr-error ew ctx many-one env "a callable head needs one value" "values")))
    (let ((many env1)) (count-check env " values" 1 (list-length _ args)))
    (let ((unique ew1) (many env2) (many rs) (many code) (erased _)) (tail $ elab-expr-demand ew fuel sugar item env1 ctx many-one tele (CCPlain) demand))
    (values ew1 env2 rs code))
  ((many elab-one-term : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Term) t) (many (Term) ty))
    (match many args _
      ((Nil _) (let ((many env2) (many x)) $ missing-arg env) (values ew env2 (TVar x) $ type-of env2 x))
      ((Cons _ araw _) (let ((unique ew1) (many env2) (many t) (many ty)) $ notail $ elab-term ew fuel sugar araw env (BFalse) no-tele) (values ew1 (settle env2 t) t ty))))

  ((many comptime-scrutinee : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Nat) pre))
    (let-match many args (Cons _ mraw rest) ((Nil _) (values ew env $ None _)))
    (let-match many rest (Cons _ xraw _) ((Nil _) (values ew env $ None _)))
    (let-match many (mult-of env mraw) (Some _ mode) ((None _) (values ew env $ None _)))
    (let-match many (and (env-run-pos env) $ mult-is-many mode) (BTrue) ((BFalse) (values ew env $ None _)))
    (let-match many xraw (RList _ _) (else (values ew env $ None _)))
    (let ((many by-name)) $ match many (share-arg env xraw) (((Bool) _)) ((Some _ a) (match many a (((Bool) _)) ((RList _ _) (BFalse)) (else (BTrue)))) ((None _) (BFalse)))
    (let-match many by-name (BFalse) ((BTrue) (values ew env $ None _)))
    (let ((unique ew1) (many env2) (many ress) (many h) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar xraw env ctx (Cons _ mode $ Nil _) no-tele (CCPlain) (Fixed _))
    (let ((many env3) (many _) (many y)) $ prepare-argument env2 mode (first-res _ _ ress lock) $ BTrue)
    (values ew1 (settled-from _ _ env3 (hoisted-code _ (Cons _ mode $ Nil _) h) y) $ Some _ y))

  ((many compute-head : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) items) (many (Env) envl) (many (List $ List $ Nat) ctx) (many (Multiplicity) pos) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (Res) h) (many (List $ List $ Nat) ctxh) (many (StmtCode ctx ctxh) hpre) (many (Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hc))
    (let-match many items (Cons _ head _) ((Nil _) (values ew envl no-res ctx (SNone _) $ CError _ (Cons _ pos $ Nil _) "no head")))
    (let ((unique ew1) (many (Env) env2) (many (Res) hr) (many (List $ List $ Nat) ctxh) (many (StmtCode ctx ctxh) hpre) (many (Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hc))
      (match many pos (((ElabWorld) _ at ew) ((Env) env2) ((Res) hr) ((List $ List $ Nat) ctxh) ((StmtCode ctx ctxh) hpre) ((Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hc))
        ((Erased)
          (let ((unique ew2) (many env2) (many rs) (many hh) (erased lock)) (notail $ elab-expr-demand ew fuel sugar head envl ctx erased-one no-tele (CCPlain) (Fixed _)))
          (let-match many hh (MkHoisted _ _ c p hc))
          (values ew2 env2 (first-res _ _ rs lock) c p hc))
        (else
          (let ((unique ew3) (many env2) (many rs) (many hh) (erased lock)) (notail $ elab-expr-demand ew fuel sugar head envl ctx many-one no-tele (CCPlain) (CallableHead pos)))
          (let-match many hh (MkHoisted _ _ c p hc))
          (values ew3 env2 (first-res _ _ rs lock) c p (coercible-code _ (Cons _ pos (Nil _)) (Many) hc)))))
    (let ((many env3) (many hr2) (many hid)) (prepare-argument env2 (res-erasure hr) hr $ BTrue))
    (let ((many env4)) $ match many (res-term hr) (((Env) _)) ((TVar y) (match many (env-run-pos env3) (((Env) _)) ((BTrue) env3) ((BFalse) (forward-binder env3 hid y $ res-erasure hr)))) (else env3))
    (values ew1 (settled-from _ _ env4 hc hid) hr2 ctxh hpre hc))

  ((many settle-item : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (Syn) item) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) pos) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (Maybe $ Syn) item2) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre))
    (let-match many item (RList p its) (else (values ew env (None _) ctx $ SNone _)))
    (let-match many its (Cons _ head args) ((Nil _) (values ew env (None _) ctx $ SNone _)))
    (let-match many head (RList hp _) (else (values ew env (None _) ctx $ SNone _)))
    (let-match many (named-share env head) (BFalse) ((BTrue) (values ew env (None _) ctx $ SNone _)))
    (let ((unique ew1) (many env1) (many hr) (many c) (many pr) (many hc)) $ notail $ compute-head ew fuel sugar its env ctx pos)
    (let ((many hid)) $ match many (res-term hr) (((Nat) _)) ((TVar y) y) (else 0))
    (let ((many env2) (many c2) (many sc))
      (match many (mult-is-many pos) (((Env) _) ((List $ List $ Nat) c3) ((StmtCode c c3) s3))
        ((BTrue) (hoist-temp env1 c hid $ runtime-one _ pos hc))
        ((BFalse) (values env1 c $ SNone _))))
    (values ew1 env2 (Some _ $ RList p $ Cons _ (handle-raw env2 hp hid) args) c2 $ SSeq _ _ _ pr sc))

  ((many settle-message : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Syn) args2))
    (let-match many args (Cons _ m more) ((Nil _) (values ew env args)))
    (let-match many m (RList mp _) (else (values ew env args)))
    (let-match many (named-share env m) (BFalse) ((BTrue) (values ew env args)))
    (let ((unique ew1) (many env1) (many rs) (many hh) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar m env (Nil _) many-one no-tele (CCPlain) (CallableHead (Many)))
    (let-match many hh (MkHoisted _ _ _ _ hc))
    (let ((many hr)) $ first-res _ _ rs lock)
    (let ((many env2) (many _) (many hid)) (prepare-argument env1 (res-erasure hr) hr $ BTrue))
    (values ew1 (settled-from _ _ env2 hc hid) $ Cons _ (handle-raw env2 mp hid) more))

  ((many elab-one-erased : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Res) p))
    (let-match many args (Cons _ araw _) ((Nil _) (let ((many env2) (many x)) $ missing-arg env) (values ew env2 $ res-of env2 x)))
    (let ((unique ew1) (many env2) (many ress) (many _) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar araw env ctx erased-one no-tele (CCPlain) (Fixed _))
    (values ew1 (settle env2 $ erased-term ress lock) $ erased-res ress lock))

  ((many elab-focus : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (erased (Nat) n) (subterm many (Steps n) st) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Focus) fs))
    (let-match many args (Cons _ raw rest) ((Nil _) (values ew env $ Nil _)))
    (let ((unique ew1) (many env1) (many t) (many ty)) $ notail $ elab-term ew fuel sugar raw env (BFalse) no-tele)
    (let ((unique ew2) (many env2) (many more)) $ notail $ elab-focus ew1 fuel sugar rest _ st env1)
    (values ew2 env2 $ Cons _ (MkFocus (show-r raw) t ty) more))

  ; Grammar expressions (section 9): variables, constructor applications and type formers; [as-type] also
  ; checks the result is a type.
  ((many elab-term : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (Syn) raw) (many (Env) env) (many (Bool) as-type) (many (Maybe $ List $ Entry) tele) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Term) t) (many (Term) ty))
    (let ((unique ew1) (many env-x0) (many mx)) $ expand-one ew (env-set-usage-erased env $ BTrue) raw)
    (let ((many env-x)) $ env-set-usage-erased env-x0 $ env-usage-erased env)
    (let-match many mx (None _)
      ((Some _ er)
        (let ((many envx)) $ env-at env-x $ raw-pos raw)
        (let-match many er (Ok _ out) ((Fail _ m) (values ew1 (env-error envx m) (TErr "macro") $ TErr "macro")))
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envx "more than 10000 macro expansions") (TErr "macro") $ TErr "macro")))
        (tail $ elab-term ew1 f2 (raw-size out) out env-x as-type tele)))
    (let ((unique ew2) (many env-y0) (many sy)) $ splice-call ew1 (env-set-usage-erased env-x $ BTrue) raw)
    (let ((many env-y)) $ env-set-usage-erased env-y0 $ env-usage-erased env)
    (let-match many sy (None _)
      ((Some _ ry)
        (let-match many ry (Ok _ raw2) ((Fail _ m) (values ew2 (env-error env-y m) (TErr "macro") $ TErr "macro")))
        (let-match many fuel (Succ f2) ((Zero) (values ew2 (env-error env-y "more than 10000 macro expansions") (TErr "macro") $ TErr "macro")))
        (tail $ elab-term ew2 f2 (raw-size raw2) raw2 env-y as-type tele)))
    (let ((many envl)) $ env-at env-y $ raw-pos raw)
    (let ((unique ew3) (many (Env) env2) (many (Term) t) (many (Term) ty))
      (match many raw (((ElabWorld) _ at ew2) ((Env) env2) ((Term) t) ((Term) ty))
        (else
          (match many (is-underscore raw) (((ElabWorld) _ at ew2) ((Env) _) ((Term) t0) ((Term) ty0))
            ((BTrue) (let ((many env2) (many x)) $ bind-as envl (BTrue) (BFalse) (None _) (Some _ $ loc-in env $ raw-pos raw) (BFalse) (Erased) type-term (None _) delegate-id) (values ew2 env2 (TVar x) type-term))
            ((BFalse)
              (let-match many (type-handle raw) (Some _ hx)
                ((None _) (let ((many env2) (many x)) $ atom-var envl raw "a name") (values ew2 env2 (TVar x) $ type-of env2 x)))
              (values ew2 (env-refer envl (BFalse) hx) (minted-type envl hx) type-term))))
        ((RList _ items)
          (let-match many items (Cons _ head args)
            ((Nil _) (values ew2 (env-error envl "empty form") (TErr "empty form") $ TErr "empty form")))
          (let-match many (match many head (((Bool) _)) ((RList _ _) (BTrue)) (else (BFalse))) (BFalse)
            ((BTrue) (values ew2 (form-in-type envl head) (TErr "head") $ TErr "head")))
          (match many (special-of envl head) (((ElabWorld) _ at ew2) ((Env) _) ((Term) t0) ((Term) ty0))
            ((Some _ sp)
              (let ((unique ew5) (many env2) (many t)) $ notail $ elab-type-form ew2 fuel sugar args two-steps envl sp)
              (values ew5 env2 t (match many t (((Term) _)) ((TSlotOf _) slot-term) ((TVar x) (type-of env2 x)) (else type-term))))
            ((None _)
              (let ((many env2) (many x)) $ var-of-raw envl head "a constructor")
              (let ((many h)) $ TVar x)
              (let ((many hty)) $ canon-env env2 $ type-of env2 x)
              (match many hty (((ElabWorld) _ at ew2) ((Env) _) ((Term) t0) ((Term) ty0))
                ((TTyCtor ttele)
                  (let ((unique ew6) (many env3) (many acc) (many _) (many _) (many _) (many _)) $ notail $ check-args ew2 fuel sugar args (subs-all args) one-step env2 (describe env2 head h hty) (Nil _) ttele (Erased) tele (ARApp h type-term) (BTrue) (BFalse) (BFalse))
                  (values ew6 env3 (TApp h $ list-rev _ acc) type-term))
                ((TValCtor ctele ret)
                  (let ((unique ew7) (many env3) (many acc) (many _) (many _) (many _) (many _)) $ notail $ check-args ew2 fuel sugar args (subs-all args) one-step env2 (describe env2 head h hty) (Nil _) ctele (Erased) tele (ARApp h ret) (BTrue) (BFalse) (BTrue))
                  (values ew7 env3 (TApp h $ list-rev _ acc) $ instantiate acc ret))
                ((TFn _ _ _ _) (values ew2 (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "function in type") $ TErr "function in type"))
                ((TErr m) (values ew2 (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr m) $ TErr m)) (else (values ew2 (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "not applicable") $ TErr "not applicable"))))))))
    (let ((many (Env) env3)) $ match many as-type _ ((BFalse) env2) ((BTrue) (check-raw env2 "type" ty type-term $ Some _ raw)))
    (values ew3 (env-back env env3) t ty))

  ((many fetched : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (subterm many (Steps $ Succ $ Zero) _st) (many (Env) env) (many (ExprK) e) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Maybe $ Term) t))
    (let-match many args (Cons _ arg _) ((Nil _) (values ew (env-error env $ sp-misuse env $ SpExpr e) $ None _)))
    (match many e _
      ((ExLevelOf)
        (let ((unique ew1) (many env2) (many f) (many fty0)) $ notail $ elab-term ew fuel sugar arg env (BFalse) no-tele)
        (let ((many env3)) $ settle env2 f)
        (let ((many fty)) $ canon-env env3 fty0)
        (match many fty (((ElabWorld) _ at ew1) ((Env) _) ((Maybe $ Term) _))
          ((TFn _ lv _ _) (values ew1 env3 $ Some _ lv))
          (else (values ew1 (env-error env3 $ level-of-error env3 f fty) $ None _))))
      ((ExMatchableOf)
        (let ((many env2) (many tid)) $ named env arg "a type constructor")
        (let ((many env3) (many info)) $ find-matchable env2 tid)
        (let-match many info (Some _ i)
          ((None _) (values ew (env-error env3 $ str-cat (qshown env3 tid) (say env3 " has no `Matchable` open")) $ None _)))
        (match many i _ ((MkMatchInfo mid _ _ _) (values ew env3 $ Some _ $ TVar mid))))
      ((ExNumeralOf) (let ((many ewt1) (many ewt2)) (numeral-of-term env arg)) (values ew ewt1 ewt2))
      ((ExSlotOf) (let ((many env2) (many id)) (slot-var env arg)) (values ew env2 $ Some _ $ slot-term-of env2 id))
      ((ExDelegateOf) (fetched-proof ew env arg delegate-id 6 2 "Delegate"))
      ((ExAtFnOf) (fetched-proof ew env arg atfn-id 2 1 "AtFn"))
      (else (values ew (env-error env $ sp-misuse env $ SpExpr e) $ None _))))

  ((many elab-type-form : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (subterm many (Steps $ Succ $ Succ $ Zero) st) (many (Env) env) (many (Sp) sp) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Term) t))
    (let-match many st (SS _ k))
    (match many sp _
      ((SpFormer fo)
        (match many fo _
          ((FoCell)
            (let-match many args (Cons _ craw rest)
              ((Nil _) (values ew (env-error env $ sp-misuse env $ SpFormer $ FoCell) (TErr "malformed `Cell`"))))
            (let ((many env1) (many c)) (ctor-var env craw))
            (let ((many env2) (many ct) (many params) (many _) (many _)) (cell-shape env1 (Erased) c))
            (let ((unique ew1) (many env3) (many slots)) (notail $ elab-slot-terms ew fuel sugar rest env2))
            (values ew1 (match many (nat-eq (ctor-arity ct) $ list-length _ slots) (((Env) _)) ((BTrue) env3) ((BFalse) (slot-count env3 (here-pos env3) "the type former `Cell`" "slot" c params $ list-length _ slots))) (TCell (TVar c) slots)))
          ((FoFn)
            (let-match many args (Cons _ lvraw rest) ((Nil _) (values ew (env-error env $ sp-misuse env $ SpFormer $ FoFn) $ TErr "malformed `Fn`")))
            (let ((unique ew2) (many env2) (many lv) (many lvty)) $ notail $ elab-term ew fuel sugar lvraw env (BFalse) no-tele)
            (let ((many env3)) $ check env2 "type" lvty level-term)
            (let ((many env3a) (many ps) (many after) (erased wa)) $ split-arrow rest _ (WHere rest) env3)
            (let ((unique ew3) (many env4) (many params) (many rets) (many _)) $ notail $ elab-fn-type ew2 fuel sugar rest one-step (MkPair _ _ ps $ subs-of after _ wa) env3a)
            (values ew3 env4 $ TFn (BFalse) lv params rets))
          ((FoUniqueFn)
            (let-match many args (Cons _ lvraw rest) ((Nil _) (values ew (env-error env $ sp-misuse env $ SpFormer $ FoUniqueFn) $ TErr "malformed `Fn`")))
            (let ((unique ew4) (many env2) (many lv) (many lvty)) $ notail $ elab-term ew fuel sugar lvraw env (BFalse) no-tele)
            (let ((many env3)) $ check env2 "type" lvty level-term)
            (let ((many env3a) (many ps) (many after) (erased wa)) $ split-arrow rest _ (WHere rest) env3)
            (let ((unique ew5) (many env4) (many params) (many rets) (many _)) $ notail $ elab-fn-type ew4 fuel sugar rest one-step (MkPair _ _ ps $ subs-of after _ wa) env3a)
            (values ew5 env4 $ TFn (BTrue) lv params rets))
          ((FoTyCtor)
            (let ((many env2) (many ps) (many after) (erased wa)) $ split-arrow args _ (WHere args) env)
            (tail $ elab-tyctor ew fuel sugar args k (MkPair _ _ ps $ subs-of after _ wa) env2))
          ((FoValCtor)
            (let ((many env1) (many ps) (many after) (erased wa)) $ split-arrow args _ (WHere args) env)
            (let ((unique ew6) (many env2) (many _) (many _) (many t)) $ notail $ elab-valctor ew fuel sugar args k (MkPair _ _ ps $ subs-of after _ wa) env1)
            (values ew6 (env-discard env1 env2) t))
          ((FoMatchable)
            (let-match many args (Cons _ d rest)
              ((Nil _) (values ew (env-error env $ sp-misuse env $ SpFormer $ FoMatchable) $ TErr "malformed Matchable")))
            (let ((many nt) (many ext) (many marked) (erased wm)) $ take-marks rest _ (WHere rest) env (MkNewtypeMark) $ MkExtern)
            (let-match many marked (Cons _ t cs)
              ((Nil _) (values ew (env-error env $ sp-misuse env $ SpFormer $ FoMatchable) $ TErr "malformed Matchable")))
            (let ((many env2) (many disc)) $ disc-of-checked env d)
            (let ((many env3) (many tid)) $ named env2 t "a type constructor")
            (let ((many env4) (many mcs)) $ notail $ elab-mctors fuel sugar (subterm (within-in cs rest (List (Syn)) args (within-step cs marked rest (prove-subterm cs marked) wm) (prove-subterm rest args))) cs env3)
            (values ew env4 $ TMatchable disc nt ext (TVar tid) mcs))
          ))
      ((SpStmt sk)
        (let-match many sk (StDumpContext)
          ((StCompileError)
            (let-match many args (Cons _ m _) ((Nil _) (values ew (compile-say env sp args $ Erased) $ TErr "compile-error")))
            (values ew (match many m (((Env) _)) ((RList _ _) (form-in-type env m)) (else (compile-say env sp args $ Erased))) $ TErr "compile-error"))
          (else (values ew (env-error env $ str-cat (tick $ spell env $ sp-name sp) " cannot appear in a type") $ TErr "statement in type")))
        (let ((unique ew8) (many env1) (many focus)) $ notail $ elab-focus ew fuel sugar args _ k env)
        (values ew8 (dump-report env1 (GoalType) focus) $ TErr "dump-context"))
      ((SpExpr e)
        (let-match many (is-fetch e) (BTrue)
          ((BFalse) (values ew (env-error env (str-cat (tick $ spell env $ sp-name sp) " cannot appear in a type")) (TErr "expression in type"))))
        (let-match many (sp-arity sp) (Some _ n) ((None _) (values ew (env-error env $ sp-misuse env sp) $ TErr "malformed fetch")))
        (let-match many (nat-eq n $ list-length _ args) (BTrue) ((BFalse) (values ew (env-error env $ sp-misuse env sp) $ TErr "malformed fetch")))
        (let ((unique ew9) (many env1) (many found)) $ notail $ fetched ew fuel sugar args k env e)
        (values ew9 env1 $ match many found (((Term) _)) ((None _) (TErr "fetch")) ((Some _ t) t)))
      ((SpMark _) (values ew (env-error env $ str-cat (tick $ spell env $ sp-name sp) " cannot appear in a type") $ TErr "mark in type"))))

  ((many elab-cell-items : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) items)
      (many (List $ Term) slots) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) pos) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Term) slots2) (many (List $ Maybe $ Nat) ids)
      (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre))
    (let-match many items (Cons _ item rest) ((Nil _) (values ew env slots (repeat-field _ (list-length _ slots) (None _)) ctx (SNone _))))
    (let ((many old) (many tail3)) (match many slots (((Term) _) ((List $ Term) xs))
      ((Nil _) (values (TVar null-id) (Nil _))) ((Cons _ x xs) (values x xs))))
    (match many (is-underscore item) _
      ((BTrue)
        (let ((unique ew1) (many env2) (many slots2) (many ids) (many ctx2) (many pre)) (notail $ elab-cell-items ew fuel sugar rest tail3 env ctx pos))
        (values ew1 env2 (Cons _ old slots2) (Cons _ (None _) ids) ctx2 pre))
      ((BFalse)
        (let ((many mult)) (under pos (Many)))
        (let ((unique ew2) (many env1) (many rs) (many h) (erased lk)) (notail $ elab-expr-demand ew fuel sugar item env ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
        (let-match many h (MkHoisted _ _ ctxa prea code))
        (let ((many res)) (first-res _ _ rs lk))
        (let ((many env2)) (settle-res (check-slot env1 (res-ty res)) res))
        (let ((many env3) (many id) (many ctxb) (many scb)) (hoist-unplaced env2 ctxa mult res code))
        (let ((unique ew3) (many env4) (many slots2) (many ids) (many ctx2) (many pre)) (notail $ elab-cell-items ew2 fuel sugar rest tail3 env3 ctxb pos))
        (values ew3 env4 (Cons _ (res-term res) slots2) (Cons _ (Some _ id) ids) ctx2 (SSeq _ _ _ prea (SSeq _ _ _ scb pre))))))

  ((many elab-cell-at : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many args (Cons _ mraw more0) ((Nil _) (malformed ew ctx expect env $ SpMark $ MkAt)))
    (let-match many more0 (Cons _ raw more)
      ((Nil _) (match many mraw _
        ((RList _ _) (expr-error ew ctx expect env (say env "`at` around a call or a `Cell` invocation names the multiplicity its head is taken at: `(at erased (f ...))` for an `Fn`, `(at unique (k ...))` for a `UniqueFn`, and the position's for a `Cell`") "at"))
        (else (malformed ew ctx expect env $ SpMark $ MkAt)))))
    (let-match many more (Nil _) (else (malformed ew ctx expect env $ SpMark $ MkAt)))
    (let-match many raw (RList _ items) (else (malformed ew ctx expect env $ SpMark $ MkAt)))
    (let-match many items (Cons _ hraw actuals) ((Nil _) (malformed ew ctx expect env $ SpMark $ MkAt)))
    (let ((many envm0) (many mode)) (mult-checked env mraw))
    (let ((many pos)) $ pos-in env expect)
    (let ((unique ew1) (many (Env) env1) (many (Res) h) (many (List $ List $ Nat) ctxh) (many (StmtCode ctx ctxh) hpre) (many (Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hcode))
      (match many hraw (((ElabWorld) _ at ew) ((Env) env1) ((Res) h) ((List $ List $ Nat) ctxh) ((StmtCode ctx ctxh) hpre) ((Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hcode))
        ((RList _ _)
          (let ((unique ew2) (many (Env) env1) (many (Res) hr) (many (List $ List $ Nat) ctxh) (many (StmtCode ctx ctxh) hpre) (many (Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hc))
            (match many pos (((ElabWorld) _ at ew) ((Env) env1) ((Res) hr) ((List $ List $ Nat) ctxh) ((StmtCode ctx ctxh) hpre) ((Code ctxh (Cons (Multiplicity) pos (Nil (Multiplicity)))) hc))
              ((Erased)
                (let ((unique ew3) (many env1) (many rs) (many hh) (erased lk)) (notail $ elab-expr-demand ew fuel sugar hraw envm0 ctx erased-one no-tele (CCPlain) (Fixed _)))
                (let-match many hh (MkHoisted _ _ c p hc))
                (values ew3 env1 (first-res _ _ rs lk) c p hc))
              (else (match many mode _
                ((Erased)
                  (let ((unique ew4) (many env1) (many rs) (many hh) (erased lk)) (notail $ elab-expr-demand ew fuel sugar hraw envm0 ctx erased-one no-tele (CCPlain) (Fixed _)))
                  (let-match many hh (MkHoisted _ _ c p _))
                  (values ew4 env1 (first-res _ _ rs lk) c p (CErased _ $ Cons _ pos $ Nil _)))
                (else
                  (let ((unique ew4) (many env1) (many rs) (many hh) (erased lk)) (notail $ elab-expr-demand ew fuel sugar hraw envm0 ctx many-one no-tele (CCPlain) (CallableHead pos)))
                  (let-match many hh (MkHoisted _ _ c p hc))
                  (values ew4 env1 (first-res _ _ rs lk) c p (coercible-code _ (Cons _ pos (Nil _)) (Many) hc)))))))
          (let ((many env2) (many hr2) (many hid)) (prepare-argument env1 (res-erasure hr) hr $ BTrue))
          (values ew2 (settled-from _ _ env2 hc hid) hr2 ctxh hpre hc))
        (else
          (let ((many env1) (many id)) (var-of-raw envm0 hraw "a name"))
          (values ew env1 (res-of env1 id) ctx (SNone _) $ match many mode _
            ((Erased) (CErased _ $ Cons _ pos $ Nil _))
            (else (coercible-code _ (Cons _ pos $ Nil _) (Many) $ var-code env1 ctx id))))))
    (let ((many desc)) $ describe env1 hraw (res-term h) (res-ty h))
    (let ((unique ew5) (many env5) (many ress5) (many hc5)) (match many (canon-env env1 (res-ty h)) (((ElabWorld) _ at ew1) ((Env) _) ((List $ Res) rs) ((Hoisted ctxh expect) c))
      ((TCell c slots)
        (let ((many env1t)) (at-taken env1 mode pos h))
        (let ((many envm) (many rawargs) (many marks)) (cell-marks _ (subs-all actuals) env1t (BFalse)))
        (notail $ elab-cell-invoke ew1 fuel sugar actuals rawargs two-steps envm ctxh expect tele h desc (runtime-one _ pos hcode) c slots (BTrue) marks))
      ((TFn uq lv params rets)
        (let ((many env1t)) (at-taken env1 mode (match many uq _ ((BTrue) (Once)) ((BFalse) (Erased))) h))
        (let ((many env1a) (many ann) (many args2)) $ split-annotation actuals _ (WHere actuals) env1t 0)
        (notail $ elab-call ew1 fuel sugar actuals (MkPair _ _ args2 ann) env1a ctxh expect tele h desc (raw-pos hraw) pos hcode uq lv params rets (CCPlain) (Fixed _) $ BTrue))
      (else (expr-error ew1 ctxh expect env1 (str-cat (say env1 "`at` wraps a `Cell` invocation or a call, and ") $ str-cat3 (qshow env1 $ res-term h) " : " $ str-cat (qshow env1 $ res-ty h) $ say env1 " is neither") "at"))))
    (values ew5 env5 ress5 $ hoist-after _ _ _ hpre hc5))

  ((many elab-cell-alloc : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many args (Cons _ raw _) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellAlloc) "cell-alloc")))
    (let ((many env0)) (count-check env " arguments" 1 (list-length _ args)))
    (match many raw _
      ((RList _ items)
        (let-match many items (Cons _ craw rest) ((Nil _) (expr-error ew ctx expect env0 (sp-misuse env0 $ SpExpr $ ExCellAlloc) "cell-alloc")))
        (let ((many env1) (many c)) (ctor-var env0 craw))
        (let ((many env2) (many ct) (many params) (many _) (many _)) (cell-shape env1 (pos-in env1 expect) c))
        (let ((many n)) (ctor-arity ct))
        (let-match many (nat-eq n $ list-length _ rest) (BTrue)
          ((BFalse) (values ew (slot-count env2 (raw-pos raw) "`cell-alloc`" "slot item" c params $ list-length _ rest) (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "cell-alloc")))
        (let ((many env3)) env2)
        (let ((unique ew1) (many env4) (many slots) (many ids) (many ctx2) (many pre))
          (notail $ elab-cell-items ew fuel sugar rest (repeat-field _ n (TVar null-id)) env3 ctx (pos-in env3 expect)))
        (cell-alloc-result ew1 env4 ctx ctx2 pre expect c ct slots ids))
      (else
        (let ((many env1) (many c)) (ctor-var env0 raw))
        (let ((many env2) (many ct) (many _) (many _) (many _)) (cell-shape env1 (pos-in env1 expect) c))
        (let ((many n)) (ctor-arity ct))
        (cell-alloc-result ew env2 ctx ctx (SNone _) expect c ct (repeat-field _ n (TVar null-id))
          (repeat-field _ n (None _))))))

  ((many elab-cell-write : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many args (Cons _ mraw rest0) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellWrite) "cell-write")))
    (let-match many rest0 (Cons _ input rest) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellWrite) "cell-write")))
    (let-match many rest (Cons _ spec _) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellWrite) "cell-write")))
    (let ((many env0c)) (count-check env " arguments" 3 (list-length _ args)))
    (let ((many env0a) (many mode)) (mult-checked env0c mraw))
    (let ((many env0b)) $ written env0a (pos-in env0a expect) mode "a `cell-write`")
    (let ((many env0)) (refuse-when env0b (and (mult-is-many $ pos-in env0b expect) $ not $ mult-is-many mode) "`cell-write` takes its cell at `many` or `unique` in a non-erased position"))
    (let ((many shared)) $ mult-eq mode $ Many)
    (let ((many mult)) (under (pos-in env0 expect) mode))
    (let ((unique ew1) (many env1) (many rs) (many ih) (erased lk)) (notail $ elab-expr-demand ew fuel sugar input env0 ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
    (let-match many ih (MkHoisted _ _ ictx ipre inputcode))
    (let ((many res)) (first-res _ _ rs lk))
    (let ((many env2) (many sid) (many hctx) (many ssc)) (hoist-unplaced env1 ictx mult res inputcode))
    (let-match many spec (RList _ items) (else (expr-error ew1 ctx expect env2 (sp-misuse env2 $ SpExpr $ ExCellWrite) "cell-write")))
    (let-match many items (Cons _ craw items4) ((Nil _) (expr-error ew1 ctx expect env2 (sp-misuse env2 $ SpExpr $ ExCellWrite) "cell-write")))
    (let ((many env3) (many c)) (ctor-var env2 craw))
    (let ((many env4) (many ct) (many params) (many _) (many _)) (cell-shape env3 (pos-in env3 expect) c))
    (let-match many (canon-env env4 (res-ty res)) (TCell existing slots)
      (else (expr-error ew1 ctx expect env4 (say env4 "`cell-write` needs a `Cell`") "cell-write")))
    (let ((many env4c) (many same)) $ solve env4 "value" (TVar c) existing (BTrue) (None _))
    (let-match many same (BTrue)
      ((BFalse) (values ew1 env4c (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "cell-write")))
    (let-match many (nat-eq (list-length _ slots) $ list-length _ items4) (BTrue)
      ((BFalse) (values ew1 (slot-count env4c (raw-pos spec) "`cell-write`" "slot item" c params $ list-length _ items4) (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "cell-write")))
    (let ((many env5)) env4c)
    (let ((unique ew2) (many env6) (many slots2) (many ids2) (many bctx) (many ipre2)) (notail $ elab-cell-items ew1 fuel sugar items4 slots env5 hctx (pos-in env5 expect)))
    (let ((many env7) (many x)) (bind env6 (None _) (None _) (BFalse) (under (pos-in env6 expect) (Once)) (TCell (TVar c) slots2) (None _) delegate-id))
    (let ((many place)) $ match many shared (((Maybe $ Term) _)) ((BTrue) (None _)) ((BFalse) (res-place res)))
    (let ((many env8)) (placed-at env7 x place))
    (let ((many writes)) (cell-slot-writes env8 bctx ids2 0))
    (cell-result-hoisted ew2 ctx expect env8 (res-with-place (res-of env8 x) place)
      (MkHoisted _ _ bctx (SSeq _ _ _ ipre $ SSeq _ _ _ ssc ipre2)
        (match many shared (((Code bctx many-one) _))
          ((BTrue) (CCellCopy _ ct (var-code env8 bctx sid) writes))
          ((BFalse) (CCellWrite _ ct (var-code env8 bctx sid) writes))))))

  ((many elab-same : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (many (ExprK) k) (many (String) kw) (subterm many (List $ Syn) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (ExprDemand expect) demand) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many args (Cons _ araw rest) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr k) (sp-name $ SpExpr k))))
    (let-match many rest (Cons _ braw _) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr k) (sp-name $ SpExpr k))))
    (let-match many (or (same-cells k) (env-fn-same env)) (BTrue)
      ((BFalse) (expr-error ew ctx expect env "`fn-same` needs `--fn-same` (OPEN.md 36)" (sp-name $ SpExpr k))))
    (let ((many env0)) $ match many (mult-is-many (pos-in env expect)) (((Env) _))
      ((BTrue) env) ((BFalse) (env-error env $ str-cat3 "`" (sp-name $ SpExpr k) "` in an erased position")))
    (let ((many pscope)) $ env-set-scope env0 $ env-prelude env0)
    (let ((many eqname)) $ match many (same-cells k) (((String) _)) ((BTrue) "JMEq") ((BFalse) "Eq"))
    (let-match many (lookup pscope $ NSrc "ErasedOr") (Some _ eo)
      ((None _) (expr-error ew ctx expect env0 (str-cat3 "`" (sp-name $ SpExpr k) "` needs the prelude's `ErasedOr`, which `--no-prelude` leaves out") (sp-name $ SpExpr k))))
    (let-match many (lookup pscope $ NSrc eqname) (Some _ jm)
      ((None _) (expr-error ew ctx expect env0 (str-cat3 (str-cat3 "`" (sp-name $ SpExpr k) "` needs the prelude's `") eqname "`, which `--no-prelude` leaves out") (sp-name $ SpExpr k))))
    (let ((unique ew1) (many env1) (many rsa) (many ha) (erased lka)) (notail $ elab-expr-demand ew fuel sugar araw env0 ctx (Cons _ (Many) (Nil _)) no-tele (CCPlain) (Fixed _)))
    (let-match many ha (MkHoisted _ _ actx apre acode))
    (let ((many ra)) (first-res _ _ rsa lka))
    (let ((many env2) (many _) (many hctx) (many asc)) (hoist-unplaced env1 actx (Many) ra acode))
    (let ((unique ew2) (many env3) (many rsb) (many hb) (erased lkb)) (notail $ elab-expr-demand ew1 fuel sugar braw env2 hctx (Cons _ (Many) (Nil _)) no-tele (CCPlain) (Fixed _)))
    (let-match many hb (MkHoisted _ _ bctx bpre bcode))
    (let ((many rb)) (first-res _ _ rsb lkb))
    (let ((many env4) (many _) (many hctx2) (many bsc)) (hoist-unplaced env3 bctx (Many) rb bcode))
    (let ((many env5) (many pa)) (same-arg env4 k araw ra))
    (let ((many env6) (many pb)) (same-arg env5 k braw rb))
    (let ((many env6l)) $ match many (same-cells k) (((Env) _)) ((BTrue) (cell-same-listed env6 ra rb)) ((BFalse) (fn-same-typed env6 ra rb)))
    (let ((many same)) $ match many pa (((Bool) _)) ((None _) (BFalse)) ((Some _ p) (match many pb (((Bool) _)) ((None _) (BFalse)) ((Some _ q) (equal-env env6 p q)))))
    (let ((many env7)) $ match many same (((Env) _))
      ((BTrue) env6l)
      ((BFalse) (env-error env6l $ say env6l $ str-cat3 (qshow env6l $ res-term ra)  " and " $ str-cat (qshow env6l $ res-term rb) " are not at one slot")))
    (let ((many eqargs)) $ match many (same-cells k) (((List $ Term) _))
      ((BTrue) (Cons _ (res-ty ra) $ Cons _ (res-term ra) $ Cons _ (res-ty rb) $ Cons _ (res-term rb) $ Nil _))
      ((BFalse) (Cons _ (res-ty ra) $ Cons _ (res-term ra) $ Cons _ (res-term rb) $ Nil _)))
    (let ((many ty)) $ TApp (TVar eo) $ Cons _ (TApp (TVar jm) eqargs) $ Nil _)
    (let ((many env8) (many x)) (bind env7 (None _) (None _) (BFalse) (Many) ty (None _) delegate-id))
    (let ((many place)) $ Some _ $ slot-atom null-id)
    (let ((many env9)) (placed-at env8 x place))
    (let ((unique ew3) (many env10) (many rs) (many c)) $ cell-result-hoisted ew2 ctx expect env9 (res-with-place (res-of env9 x) place)
      (MkHoisted _ _ hctx2 (SSeq _ _ _ apre $ SSeq _ _ _ asc $ SSeq _ _ _ bpre bsc) (var-code env9 hctx2 null-id)))
    (let ((many env11) (many rs2)) $ produced-first expect env10 demand
      (WForm kw args $ match many (same-cells k) (((String) _)) ((BTrue) ", a cell comparison and so many") ((BFalse) ", a function comparison and so many")) rs)
    (values ew3 env11 rs2 c))

  ((many elab-cell-match : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many args (Cons _ mraw rest) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellMatch) "cell-match")))
    (let-match many rest (Cons _ input rest2) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellMatch) "cell-match")))
    (let-match many rest2 (Cons _ ann rest3) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellMatch) "cell-match")))
    (let-match many rest3 (Cons _ pattern body) ((Nil _) (expr-error ew ctx expect env (sp-misuse env $ SpExpr $ ExCellMatch) "cell-match")))
    (let ((many pos)) (pos-in env expect))
    (let ((many env14)) (refuse-when env (not $ mult-is-many pos) "`cell-match` in an erased position"))
    (let ((many env0a) (many mode)) (mult-checked env14 mraw))
    (let ((many env0)) (refuse-when env0a (not $ mult-is-many mode) "`cell-match` takes its cell at `many` or `unique`"))
    (let ((many mult)) (under pos mode))
    (let ((unique ew1) (many env1) (many rs) (many ih) (erased lk)) (notail $ elab-expr-demand ew fuel sugar input env0 ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
    (let-match many ih (MkHoisted _ _ ictx ipre inputcode))
    (let ((many res)) (first-res _ _ rs lk))
    (let ((many env2p) (many _) (many sid)) (prepare-argument env1 mult res $ BTrue))
    (let ((many env2)) $ settled-from _ _ env2p inputcode sid)
    (let ((many hctx)) (Cons _ (Cons _ sid (Nil _)) ictx))
    (let-match many pattern (RList _ items) (else (expr-error ew1 ctx expect env2 (sp-misuse env2 $ SpExpr $ ExCellMatch) "cell-match")))
    (let-match many items (Cons _ craw names) ((Nil _) (expr-error ew1 ctx expect env2 (sp-misuse env2 $ SpExpr $ ExCellMatch) "cell-match")))
    (let ((many env3) (many c)) (ctor-var env2 craw))
    (let ((many env4) (many ct) (many _) (many _) (many _)) (cell-shape env3 mode c))
    (let-match many (canon-env env4 (res-ty res)) (TCell existing slots)
      (else (expr-error ew1 ctx expect env4 (say env4 "`cell-match` needs a `Cell`") "cell-match")))
    (let ((many n)) (ctor-arity ct))
    (let ((many given)) (list-length _ names))
    (let ((many env4c)) $ check env4 "value" (TVar c) existing)
    (let ((many given-back)) $ match many (mult-is-once mode) (((List $ Entry) _)) ((BTrue) (Cons _ (is-entry mode (res-term res) $ res-place res) $ Nil _)) ((BFalse) (Nil _)))
    (let ((many shown) (erased _)) $ list-append _ (slot-entries slots) given-back)
    (let-match many (or (nat-eq n given) $ and (mult-is-once mode) $ nat-eq (Succ n) given) (BTrue)
      ((BFalse) (values ew1 (binder-count env4c (raw-pos pattern) "`cell-match`" c mode (mult-is-once mode) given shown) (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "cell-match")))
    (let ((many env5)) env4c)
    (let ((erased outer-expect)) expect)
    (let ((unique ew2) (many env6) (many anntele) (many inner-expect) (many bridge) (many atmatch)) (notail $ result-tele ew1 fuel sugar ann env5 expect tele demand))
    (let ((many expect2)) inner-expect)
    (let ((many env7) (many pairs) (many restnames)) (cell-read-bindings env6 hctx sid ct n names slots pos 0))
    (let ((many env8) (many pairs2))
      (match many (mult-is-once mode) (((Env) _) ((List $ Pair (Nat) $ Code hctx many-one) ps))
        ((BFalse) (values env7 pairs))
        ((BTrue)
          (let ((many env7n) (many name) (many site)) (match many restnames (((Env) _) ((Maybe $ Name) _) ((Maybe $ Loc) _))
            ((Nil _) (values env7 (None _) $ None _)) ((Cons _ raw _) (let ((many e) (many nm)) (name-checked env7 raw "a cell binder")) (values e nm $ Some _ $ loc-in e $ raw-pos raw))))
          (let ((many envb) (many back)) (bind env7n name site (BTrue) (under pos (Once)) (res-ty res) (Some _ (res-term res)) delegate-id))
          (let ((many envb2)) (env-place-at (env-track (mark-word envb back (BFalse)) (BField) back) back (slot-atom sid)))
          (let ((many pairs2) (erased _)) (list-append _ pairs (Cons _ (MkPair _ _ back (var-code envb2 hctx sid)) (Nil _))))
          (values envb2 pairs2))))
    (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (prepare-pack _ pairs2))
    (let ((many bctx)) (Cons _ ids hctx))
    (let ((unique ew3) (many env9) (many ress) (many bcode) (erased _))
      (notail $ elab-body ew2 fuel sugar body body (WHere _) (env-set-unwarned (env-set-run-pos env8 (BFalse)) $ or (env-unwarned env8) atmatch) bctx expect2 (Some _ anntele) $ Some _ $ MkSink "the enclosing `cell-match`" "return value" (tele-with-mults anntele expect2) (Nil _) (Cons _ (MkPair _ _ (loc-in env8 $ raw-pos ann) "the return annotation of the enclosing `cell-match` is here") $ Nil _) (env-scope env6) $ None _))
    (let ((many env10a)) (check-results-count env9 body anntele ress (Nil _)))
    (let ((many env10)) (refuse-when (env-back env env10a) (match many atmatch (((Bool) _)) ((BTrue) (not $ erases-to-nothing _ _ $ normalize bctx expect2 bcode)) ((BFalse) (BFalse)))
      "the body of an at-`cell-match` must erase to nothing, or to a reordering of variables; this one stores, allocates or calls"))
    (let ((many env11) (many resultids) (erased _))
      (open-tele anntele (env-discard env6 env10) (Some _ (anon-names anntele)) (None _) (None _) (Nil _) (BFalse)))
    (let ((many body-code)) (CLet _ ms _ ids ipk (CValues _ ms codes cpk) bcode))
    (let ((many env12) (many code)) (match many atmatch (((Env) _) ((Code ictx expect2) _))
      ((BFalse) (reconstruct ictx env11 expect2 anntele resultids (BFalse) $ CLet _ many-one _ (Cons _ sid (Nil _)) (PkMany _ _ _ _ (PkNil _)) (runtime-one _ mult inputcode) body-code))
      ((BTrue)
        (let ((many env12s) (many skipped)) (reconstruct hctx env11 expect2 anntele resultids (BTrue) body-code))
        (values env12s $ CLet _ many-one _ (Cons _ sid (Nil _)) (PkMany _ _ _ _ (PkNil _)) (runtime-one _ mult inputcode) skipped))))
    (values ew3 env12 (ress-of resultids env12) $ MkHoisted _ _ ictx ipre
      (bridge-code _ outer-expect expect2 bridge (match many (mult-is-many pos) (((Code ictx expect2) _))
        ((BFalse) (CErased _ expect2))
        ((BTrue) code)))))

  ((many elab-cell-invoke : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args)
      (subterm many (List $ Sub args) rawargs) (subterm many (Steps $ Succ $ Succ $ Zero) st) (many (Env) env) (many (List $ List $ Nat) ctx)
      (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (Res) head) (many (Callee) callee)
      (many (Code ctx many-one) hcode) (many (Term) ctor) (many (List $ Term) slots) (many (Bool) full) (many (List $ Bool) marks) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many st (SS _ step))
    (let ((many pos)) (pos-in env expect))
    (let ((many shared)) $ mult-eq pos $ Many)
    (let ((many mult)) pos)
    (let ((many env1)) (match many (res-term head) (((Env) _))
      ((TVar x) (use-entry env mult x (BFalse))) (else env)))
    (let-match many (canon-env env1 ctor) (TVar c)
      (else (expr-error ew ctx expect env1 (say env1 "`Cell` constructor is not a variable") "cell invocation")))
    (let ((many env3) (many ct) (many params) (many ret) (many _)) (cell-shape env1 pos c))
    (let ((many env4) (many hres) (many sid)) (prepare-argument env3 mult head $ BTrue))
    (let ((many env5) (many hctx) (many hsc)) (hoist-temp env4 ctx sid hcode))
    (let ((unique ew1) (many env6) (many acc) (many _) (many bctx) (many apre) (many _))
      (notail $ check-args ew fuel sugar args rawargs step env5 callee hctx params pos tele (ARApp (TVar c) ret) (BFalse) (BFalse) (BTrue)))
    (let ((many env7) (many writes)) (cell-invoke-writes env6 bctx full params (list-rev _ acc) marks slots 0))
    (let ((many copies)) $ and shared $ not $ list-is-empty _ writes)
    (cell-result-hoisted ew1 ctx expect env7 (MkRes (TApp (TVar c) (list-rev _ acc)) (instantiate acc ret) pos $ match many copies (((Maybe $ Term) _)) ((BTrue) (None _)) ((BFalse) (res-place hres)))
      (MkHoisted _ _ bctx (SSeq _ _ _ hsc apre)
        (match many copies (((Code bctx many-one) _))
          ((BTrue) (CCellCopy _ ct (var-code env7 bctx sid) writes))
          ((BFalse)
            (match many writes (((Code bctx many-one) _))
              ((Nil _) (var-code env7 bctx sid))
              ((Cons _ _ _) (CCellWrite _ ct (var-code env7 bctx sid) writes))))))))

  ((many elab-slot-terms : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) items) (many (Env) env) -> (unique (ElabWorld) ewr at ew)
      (many (Env) env2) (many (List $ Term) slots))
    (let-match many items (Cons _ item rest) ((Nil _) (values ew env (Nil _))))
    (let ((unique ew1) (many env1) (many term) (many ty)) (notail $ elab-term ew fuel sugar item env (BFalse) no-tele))
    (let ((unique ew2) (many env2) (many slots)) (notail $ elab-slot-terms ew1 fuel sugar rest (check env1 "type" ty slot-term)))
    (values ew2 env2 (Cons _ term slots)))

  ((many elab-mctors : (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) cs) (many (Env) env) -> (many (Env) r) (many (List $ MCtor) mcs))
    (let-match many cs (Cons _ c rest) ((Nil _) (values env $ Nil _)))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env "expected (multiplicity Constructor)"))
    (let ((many (Env) env1) (many (Multiplicity) m) (many (Syn) craw))
      (match many (raw-items c) _
        ((Nil _) (values (bad) (Many) c))
        ((Cons _ mraw more)
          (let-match many more (Cons _ cr more2) ((Nil _) (values (bad) (Many) c)))
          (let-match many more2 (Nil _) ((Cons _ _ _) (values (bad) (Many) cr)))
          (match many (mult-of env mraw) (((Env) _) ((Multiplicity) m0) ((Syn) r0))
            ((None _) (values (env-error env $ str-cat "expected a multiplicity, got " $ qraw mraw) (Many) cr))
            ((Some _ mm) (values env mm cr))))))
    (let ((many env2) (many cid)) $ named env1 craw "a constructor")
    (let ((many env3) (many mcs)) $ notail $ elab-mctors fuel sugar rest env2)
    (values env3 $ Cons _ (MkMCtor m $ TVar cid) mcs))

  ; The signature pieces [piece] were read from [root]; [st] pays for the parse of each telescope.
  ((many elab-fn-type : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Entry) params) (many (List $ Entry) rets) (many (List $ Nat) param-ids))
    (let-match many piece (MkPair _ _ ps rs))
    (let ((unique ew1) (many env2) (many ids) (many params)) $ notail $ elab-tele ew fuel sugar root st ps env (MMDeclared) (Nil _) (BTrue) (BFalse) (BTrue) $ BFalse)
    (let ((unique ew2) (many env3) (many _) (many rets)) $ notail $ elab-tele ew1 fuel sugar root st rs env2 (MMDeclared) (tvars-rev ids $ Nil _) (BFalse) (BFalse) (BTrue) $ BFalse)
    (values ew2 (env-discard env env3) params rets ids))

  ((many elab-tyctor : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Term) t))
    (let-match many piece (MkPair _ _ ps ret))
    (let ((unique ew1) (many env2) (many _) (many tele)) $ notail $ elab-tele ew fuel sugar root st ps (env-set-ctor-tele env $ env-signature env) (MMErased) (Nil _) (BFalse) (BFalse) (BFalse) $ BTrue)
    (let ((unique ew2) (many (Env) env3))
      (match many ret (((ElabWorld) _ at ew1) ((Env) env3))
        ((Cons _ s more)
          (let-match many more (Nil _)
            ((Cons _ _ _) (values ew1 (env-error env2 (say env2 "`TyCtor` returns `Type`")))))
          (let-match many s (MkSub _ r p))
          (let ((unique ew3) (many env3) (many t) (many _)) $ notail $ elab-term ew1 fuel sugar (subterm p) r env2 (BFalse) no-tele)
          (values ew3 (check env3 "value" t type-term)))
        ((Nil _) (values ew1 (env-error env2 (say env2 "`TyCtor` returns `Type`"))))))
    (values ew2 (env-discard env env3) $ TTyCtor tele))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type; the return is an application of a type constructor in scope (section 11).
  ((many elab-valctor : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Entry) tele) (many (Term) ret) (many (Term) t))
    (let-match many piece (MkPair _ _ ps rets))
    (let ((unique ew1) (many env2) (many ids) (many tele)) $ notail $ elab-tele ew fuel sugar root st ps (env-set-ctor-tele env $ env-signature env) (MMDeclared) (Nil _) (BFalse) (BFalse) (BFalse) $ BTrue)
    (let ((unique ew2) (many (Env) env3a) (many (Term) ret))
      (match many rets (((ElabWorld) _ at ew1) ((Env) env3a) ((Term) ret))
        ((Nil _) (values ew1 (env-error env2 "a constructor returns one type") $ TErr "no return"))
        ((Cons _ s more)
          (let-match many more (Nil _)
            ((Cons _ _ _) (values ew1 (env-error env2 "a constructor returns one type") $ TErr "no return")))
          (let-match many s (MkSub _ r p))
          (let ((unique ew3) (many env3) (many t) (many _)) $ notail $ elab-term ew1 fuel sugar (subterm p) r env2 (BTrue) no-tele)
          (values ew3 env3 t))))
    (let ((many env3)) $ settle env3a ret)
    (let ((many (Bool) ok))
      (match many (canon-env env3 ret) _
        ((TApp h _)
          (match many h (((Bool) _))
            ((TVar t) (and (not $ list-mem-bin ids t)
                         $ match many (type-of env3 t) (((Bool) _)) ((TTyCtor _) (BTrue)) (else (BFalse)))) (else (BFalse)))) (else (BFalse))))
    (def-fns msg-lvl $ (many msg-return : -> (many (String) s)) (str-cat "a constructor returns an application of a type constructor in scope, not " $ qshow env3 ret))
    (let ((many env4)) $ error-unless-msg env3 ok msg-return)
    (values ew2 (env-set-ctor-tele (env-set-signature env4 $ env-signature env) $ env-ctor-tele env) tele ret $ TValCtor tele $ abstract-slots env4 (list-rev _ ids) ret))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 3).
  ; [ids]: binders already in force, innermost first.
  ((many elab-tele : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (List $ Sub root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (Bool) subterm-ok) (many (Bool) holes) (many (Bool) places) (many (Bool) ctor) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Nat) bound) (many (List $ Entry) tele))
    (let-match many st (SS _ k))
    (let ((unique ew1) (many envm0) (many changed) (many out) (many err)) $ splice-entries ew (env-set-usage-erased env $ BTrue) $ sub-syns _ entries)
    (let ((many envm)) $ env-set-usage-erased envm0 $ env-usage-erased env)
    (let-match many changed (BFalse)
      ((BTrue)
        (let-match many err (None _) ((Some _ e) (match many e _ ((MkPair _ _ item m) (values ew1 (env-error (env-at envm $ raw-pos item) m) (Nil _) $ Nil _)))))
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envm "more than 10000 macro expansions") (Nil _) $ Nil _)))
        (tail $ elab-tele ew1 f2 (raws-size out) out st (subs-all out) envm mode ids subterm-ok holes places ctor)))
    (let ((many env2) (many entries2)) $ parse-entries-checked _ entries env)
    (tail $ elab-src-entries ew1 fuel sugar root k entries2 env2 mode ids (Nil _) (scope-ids $ env-scope env) subterm-ok holes places ctor $ BTrue))

  ((many elab-src-entries : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (Steps $ Zero) st) (subterm many (List $ SrcEntry root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (List $ Nat) bound) (many (List $ Nat) outer) (many (Bool) subterm-ok) (many (Bool) holes) (many (Bool) places) (many (Bool) ctor) (many (Bool) warns) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Nat) bound2) (many (List $ Entry) tele))
    (let-match many entries (Cons _ e rest) ((Nil _) (values ew env (list-rev _ bound) $ Nil _)))
    (let-match many e (MkSrcEntry _ sub2 smult ssg name place epos))
    (let ((many env0)) $ env-back env $ refuse-when (env-at env epos) (and sub2 $ not subterm-ok) "`subterm` is not allowed here")
    (let ((many (Env) env1) (many (Multiplicity) mult) (many (MultsMode) mode2))
      (match many mode _
        ((MMDeclared) (match many smult (((Env) _) ((Multiplicity) m0) ((MultsMode) md0)) ((None _) (values (env-error env0 $ str-cat3 "entry " (tick $ spell-binder name) " needs a multiplicity") (Many) mode)) ((Some _ m) (values env0 m mode))))
        ((MMErased) (match many smult (((Env) _) ((Multiplicity) m0) ((MultsMode) md0)) ((None _) (values env0 (Erased) mode)) ((Some _ m) (values (no-mult env0 epos "a type constructor's parameters" m) (Erased) mode))))
        ((MMExpect ms)
          (let ((many env0b)) $ match many smult (((Env) _)) ((None _) env0) ((Some _ m) (no-mult env0 epos "a match annotation's entries" m)))
          (match many ms (((Env) _) ((Multiplicity) m0) ((MultsMode) md0)) ((Nil _) (values env0b (Erased) mode)) ((Cons _ m more) (values env0b m $ MMExpect more))))))
    (let ((unique ew1) (many (Env) env2) (many (Sg) sg))
      (match many ssg (((ElabWorld) _ at ew) ((Env) env2) ((Sg) sg))
        ((None _) (values ew (env-error env1 $ str-cat3 "entry " (tick $ spell-binder name) (say env1 " needs a type or an `is` clause")) $ SgTy $ TErr "no type"))
        ((Some _ s)
          (match many s (((ElabWorld) _ at ew) ((Env) _) ((Sg) s0))
            ((SrcTy _ r p) (let ((unique ew2) (many env2) (many t) (many _)) $ notail $ elab-term ew fuel sugar (subterm p) r env1 (BTrue) no-tele) (values ew2 env2 $ SgTy t))
            ((SrcIs _ r p) (let ((unique ew3) (many env2) (many t) (many ty)) $ notail $ elab-term ew fuel sugar (subterm p) r env1 (BFalse) no-tele) (values ew3 env2 $ SgIs t ty))))))
    (let ((many ty) (many rule)) $ fact-of sg)
    (let ((many nm)) name)
    (let ((many env2a) (many atplace))
      (match many place (((Env) _) ((Maybe $ Term) p0))
        ((None _) (values env2 $ None _))
        ((Some _ target) (at-place env2 places mult epos target))))
    (let ((many env3p) (many x)) $ bind-as env2a (BFalse) holes nm (Some _ $ loc-in env2a epos) warns mult ty rule delegate-id)
    (let ((many env3b)) $ env-pend env3p x)
    (let ((many env3)) (placed-at env3b x atplace))
    (let ((many env3s)) (env-set-signature env3 (Cons _ x (env-signature env3))))
    (let ((many env3e)) $ match many ctor (((Env) _)) ((BTrue) (env-set-ctor-tele env3s (Cons _ x $ env-ctor-tele env3s))) ((BFalse) env3s))
    (let ((many ap)) $ match many atplace (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ p) (Some _ $ abstract-slots env2a (bin-ids-of ids) p)))
    (let ((many entry3)) $ MkEntry nm sub2 mult (abstract-slots-sg env2a (bin-ids-of ids) sg) ap (Some _ $ loc-in env2a epos))
    (let ((unique ew4) (many env4) (many bound2) (many tele)) $ notail $ elab-src-entries ew1 fuel sugar root st rest env3e mode2 (Cons _ (TVar x) ids) (Cons _ x bound) outer subterm-ok holes places ctor warns)
    (values ew4 env4 bound2 $ Cons _ entry3 tele))
  ; A body: statements then the final expression (section 27); [items] sits within [root].
  ((many elab-body : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ Syn) items) (erased (Within items root) w) (many (Env) env0) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (Maybe $ Sink) sink) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Multiplicity) (Res) expect ress) lock))
    (let ((many env)) $ report-shadows env0 $ BTrue)
    (match many items _
      ((Nil _)
        (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res)
        (values ew (env-error env "a body needs a final expression") ress (CError _ expect "empty body") lock))
      ((Cons _ item rest)
        (let ((erased pi0)) $ in-within _ _ _ _ (prove-subterm item items) w)
        (let ((unique ew1) (many envs) (many settled) (many ctxs) (many spre)) $ notail $ settle-item ew fuel sugar (subterm pi0) item env ctx (pos-in env expect))
        (let-match many settled (None _)
          ((Some _ item2)
            (let-match many fuel (Succ f2)
              ((Zero) (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res) (values ew1 (env-error envs "more than 10000 macro expansions") ress (CError _ expect "macro") lock)))
            (let ((many all)) $ Cons _ item2 rest)
            (let ((unique ew2) (many env3) (many ress) (many code) (erased lock)) $ notail $ elab-body ew1 f2 (raws-size all) all all (WHere _) envs ctxs expect tele sink)
            (values ew2 env3 ress (wrap-stmt _ _ expect spre code) lock)))
        (let ((unique ew3) (many envm) (many mx)) $ body-head ew1 env item)
        (let-match many mx (None _)
          ((Some _ me)
            (let ((many envx)) $ env-at envm $ raw-pos item)
            (let ((many (String) m) (many (List $ Syn) out)) $ match many me _ ((Refused m) (values m $ Nil _)) ((Spliced o) (values "more than 10000 macro expansions" o)))
            (let-match many fuel (Succ f2)
              ((Zero) (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res) (values ew3 (env-error envx m) ress (CError _ expect "macro") lock)))
            (let-match many me (Spliced _)
              ((Refused _) (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res) (values ew3 (env-error envx m) ress (CError _ expect "macro") lock)))
            (let ((many all) (erased _)) $ list-append _ out rest)
            (tail $ elab-body ew3 f2 (raws-size all) all all (WHere _) envm ctx expect tele sink)))
        (let ((erased pi)) $ in-within _ _ _ _ (prove-subterm item items) w)
        (let-match many rest (Cons _ _ _)
          ((Nil _)
            (let ((unique ew4) (many envf) (many ress) (many h) (erased lock)) $ notail $ elab-expr-demand ew3 fuel sugar (subterm pi) item (env-set-final $ env-set-sink env sink) ctx expect tele (CCPlain) (Fixed _))
            (values ew4 envf ress (hoisted-code _ expect h) lock)))
        (match many (let-else env item rest) _
          ((Some _ pr)
            (let-match many pr (MkPair _ _ head gen))
            (match many sugar _
              ((Zero)
                (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res)
                (values ew3 (env-error env "internal: the sugar budget is spent") ress (CError _ expect "sugar") lock))
              ((Succ k)
                (let ((many envl)) $ env-at env $ raw-pos item)
                (let ((unique ew5) (many env2) (many ress) (many h)) $ notail $ elab-match ew3 fuel k gen (env-set-sink (read-special envl head (BFalse) $ pos-in envl expect) sink) ctx expect tele (Fixed _) (BFalse) "`let-match`" $ None _)
                (let ((many ress2) (erased lock)) $ list-fit _ _ expect ress no-res)
                (values ew5 env2 ress2 (hoisted-code _ expect h) lock))))
          ((None _)
            (let ((unique ew6) (many env2) (many ctx2) (many sc)) $ notail $ elab-stmt ew3 fuel sugar (subterm pi) item env ctx (pos-in env expect) "item of a body")
            (let ((unique ew7) (many env3) (many ress) (many code) (erased lock)) $ notail $ elab-body ew6 fuel sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2 expect tele sink)
            (values ew7 env3 ress (wrap-stmt _ _ expect sc code) lock))))))

  ((many elab-refute : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ Syn) items) (erased (Within items root) w) (many (Env) env) (many (List $ List $ Nat) ctx) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r))
    (let ((many env0)) $ env-set-usage-erased env $ BTrue)
    (let-match many items (Cons _ item rest) ((Nil _) (values ew (env-error env0 "a body needs a final expression"))))
    (let ((unique ew1) (many envm) (many mx)) $ expand ew env0 item)
    (let-match many mx (None _)
      ((Some _ me)
        (let ((many envx)) $ env-at envm $ raw-pos item)
        (let-match many me (Spliced out) ((Refused m) (values ew1 (env-error envx m))))
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envx "more than 10000 macro expansions"))))
        (let ((many all) (erased _)) $ list-append _ out rest)
        (tail $ elab-refute ew1 f2 (raws-size all) all all (WHere _) envm ctx)))
    (let ((erased pi)) $ in-within _ _ _ _ (prove-subterm item items) w)
    (match many rest _
      ((Cons _ _ _)
        (let ((unique ew2) (many env2) (many ctx2) (many _)) $ notail $ elab-stmt ew1 fuel sugar (subterm pi) item env0 ctx (Erased) "item of a body")
        (tail $ elab-refute ew2 fuel sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2))
      ((Nil _)
        (let ((many envl)) $ env-at env0 $ raw-pos item)
        (match many (refute-form envl item) _
          ((RefuteMatch _ head args p)
            (let ((unique ew3) (many env2) (many _) (many _)) $ notail $ elab-match ew1 fuel sugar (subterm $ subterm-trans p pi) args (read-special envl head (BFalse) $ Erased) ctx erased-one no-tele (Fixed _) (BTrue) "`match`" $ None _)
            (values ew3 env2))
          ((RefuteOpen _ head e p)
            (let ((many env1)) $ read-special envl head (BFalse) $ Erased)
            (let ((unique ew4) (many env2) (many ress) (many h) (erased lock)) $ notail $ elab-expr-demand ew1 fuel sugar (subterm $ subterm-trans p pi) e env1 ctx erased-one no-tele (CCPlain) (Fixed _))
            (let-match many h (MkHoisted _ _ c2 _ code))
            (values ew4 (open-contradicts c2 env1 env2 (first-res _ _ ress lock) code)))
          ((RefuteValue _)
            (let ((unique ew5) (many env2) (many ress) (many _) (erased lock)) $ notail $ elab-expr-demand ew1 fuel sugar (subterm pi) item envl ctx erased-one no-tele (CCPlain) (Fixed _))
            (values ew5 (refuted-value env2 $ first-res _ _ ress lock)))))))

  ; The statements before a body's final expression and the code they wrap around what follows them
  ; (lib/elab.ml's elab_stmts), then the final expression with its place in [root].
  ((many elab-stmts : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ Syn) items) (erased (Within items root) w) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) spos) (many (String) within) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc) (many (Final fuel root) final))
    (let-match many items (Cons _ item rest) ((Nil _) (values ew env ctx (SNone _) $ FinalNone _ _)))
    (let ((erased pi0)) $ in-within _ _ _ _ (prove-subterm item items) w)
    (let ((unique ew1) (many envs) (many settled) (many ctxs) (many spre)) $ notail $ settle-item ew fuel sugar (subterm pi0) item env ctx spos)
    (let-match many settled (None _)
      ((Some _ item2)
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envs "more than 10000 macro expansions") ctx (SNone _) $ FinalNone _ _)))
        (let ((many all)) $ Cons _ item2 rest)
        (let ((unique ew2) (many env2) (many ctx2) (many sc) (many fin)) $ notail $ elab-stmts ew1 f2 (raws-size all) all all (WHere _) envs ctxs spos within)
        (values ew2 env2 ctx2 (SSeq _ _ _ spre sc) $ final-lift _ f2 (prove-subterm f2 fuel) _ _ fin)))
    (let ((unique ew3) (many envm) (many mx)) $ expand ew1 env item)
    (let-match many mx (None _)
      ((Some _ me)
        (let ((many envx)) $ env-at envm $ raw-pos item)
        (let-match many me (Spliced out) ((Refused m) (values ew3 (env-error envx m) ctx (SNone _) $ FinalNone _ _)))
        (let-match many fuel (Succ f2) ((Zero) (values ew3 (env-error envx "more than 10000 macro expansions") ctx (SNone _) $ FinalNone _ _)))
        (let ((many all) (erased _)) $ list-append _ out rest)
        (let ((unique ew4) (many env2) (many ctx2) (many sc) (many fin)) $ notail $ elab-stmts ew3 f2 (raws-size all) all all (WHere _) envm ctx spos within)
        (values ew4 env2 ctx2 sc $ final-lift _ f2 (prove-subterm f2 fuel) _ _ fin)))
    (let ((erased pi)) $ in-within _ _ _ _ (prove-subterm item items) w)
    (let-match many rest (Cons _ _ _) ((Nil _) (values ew3 env ctx (SNone _) $ FinalIs _ _ item pi)))
    (let ((unique ew5) (many env2) (many ctx2) (many sc)) $ notail $ elab-stmt ew3 fuel sugar (subterm pi) item env ctx spos within)
    (let ((unique ew6) (many env3) (many ctx3) (many sc2) (many final)) $ notail $ elab-stmts ew5 fuel sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2 spos within)
    (values ew6 env3 ctx3 (SSeq _ _ _ sc sc2) final))

  ((many elab-stmt : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (Syn) raw) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) spos) (many (String) within) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many envl)) $ env-at env $ raw-pos raw)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ not-a-statement envl within raw))
    (let ((unique ew1) (many (Env) env2) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
      (match many raw (((ElabWorld) _ at ew) ((Env) env2) ((List $ List $ Nat) ctx2) ((StmtCode ctx ctx2) sc))
        ((RList _ items)
          (let-match many items (Cons _ head args) ((Nil _) (values ew (bad) ctx $ SNone _)))
          (let-match many (special-of envl head) (Some _ sp) ((None _) (values ew (bad) ctx $ SNone _)))
          (let ((many envl2)) $ read-special envl head (BFalse) spos)
          (let-match many sp (SpStmt st) (else (values ew (bad) ctx $ SNone _)))
          (match many st (((ElabWorld) _ at ew) ((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
            ((StLet)
              (let ((unique ew2) (many envs) (many sx)) $ splice-binders ew envl2 head args)
              (let-match many sx (None _)
                ((Some _ rr)
                  (let-match many rr (Ok _ items2) ((Fail _ m) (values ew2 (env-error envs m) ctx $ SNone _)))
                  (let-match many fuel (Succ f2) ((Zero) (values ew2 (env-error envs "more than 10000 macro expansions") ctx $ SNone _)))
                  (let ((many raw2)) $ RList (raw-pos raw) items2)
                  (notail $ elab-stmt ew2 f2 (raw-size raw2) raw2 envs ctx spos within)))
              (let ((many envb) (many braws) (many rhs) (erased wr)) $ bracket-parts args envl2 sp)
              (let ((many env0) (many binders)) $ parse-entries-checked _ braws envb)
              (let ((unique ew3) (many env0b) (many tele) (many tele-ids))
                (match many (all-have-sg _ binders) (((ElabWorld) _ at ew2) ((Env) _) ((Maybe $ List $ Entry) t) ((List $ Nat) ts))
                  ((BFalse) (values ew2 env0 no-tele $ Nil _))
                  ((BTrue)
                    (let ((unique ew4) (many env1) (many bound) (many t)) $ notail $ elab-src-entries ew2 fuel sugar args (SZ) binders env0 (MMDeclared) (Nil _) (Nil _) (Nil _) (BFalse) (BTrue) (BFalse) (BFalse) $ BFalse)
                    (values ew4 (env-restore env0 env1) (Some _ t) bound))))
              (notail $ elab-let ew3 fuel sugar args (MkLetParts _ binders rhs wr) env0b ctx tele tele-ids spos))
            ((StDefLvl)
              (let-match many args (Cons _ n more) ((Nil _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let-match many more (Nil _) ((Cons _ _ _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let ((many envn) (many nm)) $ name-checked envl2 n "a name")
              (let ((many env2) (many x)) $ mint-level envn nm (Some _ $ loc-in envl2 $ raw-pos n))
              (values ew (env-track env2 (BDefinition) x) ctx $ SNone _))
            ((StDefFns) (notail $ elab-def-fns ew fuel sugar args envl2 ctx $ BFalse))
            ((StDefUnique) (notail $ elab-def-fns ew fuel sugar args envl2 ctx $ BTrue))
            ((StDefAdts)
              (let ((unique ew5) (many env3) (many headers) (many tids)) $ notail $ elab-adt-headers ew fuel sugar args envl2)
              (let ((unique ew6) (many env4) (many consts)) $ notail $ define-adts ew5 fuel sugar args headers env3 tids)
              (let-match many (env-run-pos env4) (BFalse) ((BTrue) (values ew6 (set-settled-states consts env4) ctx $ SNone _)))
              (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) $ consts-codes ctx consts)
              (values ew6 env4 (Cons _ ids ctx) $ SLet _ ms ids ipk $ CValues _ ms codes cpk))
            ((StComptimeMatch)
              (let ((unique ew7) (many env1) (many pre)) $ notail $ comptime-scrutinee ew fuel sugar args envl2 ctx)
              (let ((many env2) (many sc)) $ elab-comptime-match ctx env1 args pre)
              (values ew7 env2 ctx sc))
            ((StLetMatch) (notail $ elab-let-match ew fuel sugar args envl2 ctx spos))
            ((StUnary) (notail $ elab-unary ew fuel sugar args envl2 ctx spos))
            ((StOpenAdt) (notail $ elab-open-adt ew fuel sugar args envl2 ctx spos))
            ((StSlotSelf)
              (let-match many args (Cons _ a more) ((Nil _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let-match many more (Nil _) ((Cons _ _ _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let ((many env1) (many x)) $ var-of-raw envl2 a "a variable")
              (let ((many env3)) $ env-back env1 $ check (env-at env1 $ raw-pos a) "type" (type-of env1 x) slot-term)
              (match many (place-forced env3 x $ TVar x) (((ElabWorld) _ at ew) ((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                ((UOk env4) (values ew env4 ctx $ SNone _))
                ((UContra m) (values ew (env-error env3 $ str-cat3 (say env3 "`slot-self`: ") (qshown env3 x) $ str-cat3 (say env3 " contradicts the facts in force (") (clash-str env3 m) ")") ctx $ SNone _))))
            ((StOpenAtFn)
              (let-match many args (Cons _ _ more) ((Nil _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let-match many more (Nil _) ((Cons _ _ _) (values ew (env-error envl2 $ sp-misuse envl2 sp) ctx $ SNone _)))
              (let ((unique ew8) (many env1) (many p)) $ notail $ elab-one-erased ew fuel sugar args envl2 ctx)
              (let ((many env2)) $ match many (canon-env env1 $ res-ty p) (((Env) _))
                ((TApp h as) (match many (and (term-eq h $ TVar atfn-id) $ nat-eq (list-length _ as) 2) (((Env) _)) ((BTrue) env1) ((BFalse) (env-error env1 $ str-cat3 (qshow env1 $ res-term p) " : " $ str-cat (qshow env1 $ res-ty p) $ say env1 " is not an `AtFn` proof"))))
                (else (env-error env1 $ str-cat3 (qshow env1 $ res-term p) " : " $ str-cat (qshow env1 $ res-ty p) $ say env1 " is not an `AtFn` proof")))
              (let ((many env3) (many x)) $ bind-erased env2 (None _) (Some _ $ env-loc env2) (BFalse) (Erased) (res-ty p) (Some _ $ res-term p) delegate-id)
              (values ew8 (open-proof env3 x) ctx $ SNone _))
            ((StDumpContext)
              (let ((unique ew9) (many env1) (many focus)) $ notail $ elab-focus ew fuel sugar args _ two-steps envl2)
              (values ew9 (dump-report env1 (GoalStatement) focus) ctx $ SNone _))
            ((StCompileError) (let ((unique ew10) (many envm) (many margs)) $ notail $ settle-message ew fuel sugar args envl2) (values ew10 (compile-say envm sp margs spos) ctx $ SNone _))
            ((StCompileWarn) (let ((unique ew11) (many envm) (many margs)) $ notail $ settle-message ew fuel sugar args envl2) (values ew11 (compile-say envm sp margs spos) ctx $ SNone _))
            ((StDefOpaque)
              (let-match many (trusted-checked envl2 "def-opaque") (None _) ((Some _ e) (values ew e ctx $ SNone _)))
              (let ((unique ew12) (many e)) $ notail $ elab-opaques ew fuel sugar args envl2)
              (values ew12 e ctx $ SNone _))
            ((StDefPrim)
              (let-match many (trusted-checked envl2 "def-prim") (None _) ((Some _ e) (values ew e ctx $ SNone _)))
              (let ((unique ew13) (many e)) $ notail $ elab-prims ew fuel sugar args envl2)
              (values ew13 e ctx $ SNone _))
            ((StGoal) (let ((unique ew14) (many e)) $ notail $ elab-goal ew fuel sugar args envl2 within) (values ew14 e ctx $ SNone _)))) (else (values ew (bad) ctx $ SNone _))))
    (values ew1 (report-shadows (env-back env env2) $ BTrue) ctx2 sc))

  ((many elab-goal : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (String) within) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env $ sp-misuse env $ SpStmt $ StGoal))
    (let-match many (str-eq within "top-level form") (BTrue) ((BFalse) (values ew (env-error env $ say env "`goal` is allowed only as a top-level form of a file"))))
    (let-match many (env-goals env) (MkGoals mode prior _ _ _ _))
    (let-match many prior (None _) ((Some _ pl) (values ew (env-error-with env (Cons _ (MkPair _ _ pl "the goal is set here") $ Nil _) $ say env "a unit sets at most one `goal`"))))
    (let-match many args (Cons _ mraw rest) ((Nil _) (values ew (bad))))
    (let-match many rest (Cons _ traw rest2) ((Nil _) (values ew (bad))))
    (let-match many rest2 (Nil _) ((Cons _ _ _) (values ew (bad))))
    (let ((many env1) (many mult)) $ mult-checked (env-at env $ raw-pos mraw) mraw)
    (let ((unique ew1) (many env2) (many t) (many _)) $ notail $ elab-term ew fuel sugar traw (env-back env env1) (BTrue) (None _))
    (let ((many report)) $ match many mode (((String) _))
      ((GoalProved) (diagnostic env ": note: " (Nil _) $ str-cat3 (say env2 "proved `(goal ") (spell env2 $ mult-name mult) $ str-cat3 " " (show-t env2 t) ")`"))
      (else ""))
    (values ew1 (env-set-goals env2 $ MkGoals mode (Some _ $ env-loc env) mult t report $ BFalse)))

  ; open-adt (section 8, ASSUMPTIONS 139): an anonymous let at the written multiplicity, then the open of that
  ; binder; the entry is bound by the code where the let would be.
  ((many elab-open-adt : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) spos) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env $ sp-misuse env $ SpStmt $ StOpenAdt))
    (let-match many args (Cons _ mraw rest) ((Nil _) (values ew (bad) ctx $ SNone _)))
    (let-match many rest (Cons _ eraw rest2) ((Nil _) (values ew (bad) ctx $ SNone _)))
    (let-match many rest2 (Nil _) ((Cons _ _ _) (values ew (bad) ctx $ SNone _)))
    (let ((many env0a) (many mult)) $ mult-checked env mraw)
    (let ((many env0)) $ written env0a spos mult "an `open-adt`")
    (let ((unique ew1) (many env1) (many ress) (many h) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar eraw env0 ctx (Cons _ mult $ Nil _) no-tele (CCPlain) (Fixed _))
    (let-match many h (MkHoisted _ _ c2 pre code))
    (let ((many env2) (many x) (many t)) $ open-bind c2 env0 env1 (first-res _ _ ress lock) mult code)
    (let-match many (env-open-adt env2 x) (UOk env3)
      ((UContra m) (values ew1 (env-error env2 $ str-cat3 (say env2 "`open-adt`: ") (qshow env2 t) $ str-cat3 " contradicts what is open (" (clash-str env2 m) ")") ctx $ SNone _)))
    (match many mult _
      ((Erased) (values ew1 env3 ctx $ SNone _))
      (else
        (match many (env-run-pos env0) _
          ((BTrue) (values ew1 env3 ctx $ SNone _))
          ((BFalse) (values ew1 env3 (Cons _ (Cons _ x $ Nil _) c2) $ SSeq _ _ _ pre $ SLet _ (Cons _ (Many) $ Nil _) (Cons _ x $ Nil _) (PkMany _ (Nil _) x (Nil _) $ PkNil _) $ runtime-one _ mult code))))))

  ; let-match (section 27, ASSUMPTIONS 99-100): the sole unrefuted constructor binds outward, its fields at the
  ; scrutinee's own erasure; erased or run at once it leaves no code, else one branch wraps the rest.
  ((many elab-let-match : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) spos) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((unique ew1) (many envs) (many sx)) $ splice-tail ew env 3 args)
    (let-match many sx (None _)
      ((Some _ rr)
        (let-match many rr (Ok _ args2) ((Fail _ m) (values ew1 (env-error envs m) ctx $ SNone _)))
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envs "more than 10000 macro expansions") ctx $ SNone _)))
        (tail $ elab-let-match ew1 f2 (raws-size args2) args2 envs ctx spos)))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env $ sp-misuse env $ SpStmt $ StLetMatch))
    (let-match many args (Cons _ mraw more) ((Nil _) (values ew1 (bad) ctx $ SNone _)))
    (let-match many more (Cons _ scrut more2) ((Nil _) (values ew1 (bad) ctx $ SNone _)))
    (let-match many more2 (Cons _ pat branches) ((Nil _) (values ew1 (bad) ctx $ SNone _)))
    (let-match many (has-real-branch env branches) (BFalse)
      ((BTrue) (values ew1 (env-error env (say env "a `let-match` with a real branch besides its pattern must be a statement of a function, match branch or cell-match body")) ctx $ SNone _)))
    (let-match many (raw-items pat) (Cons _ craw fields) ((Nil _) (values ew1 (bad) ctx $ SNone _)))
    (let ((many env0) (many smult)) $ mult-checked env mraw)
    (let ((many env0d)) $ written env0 spos smult "a `let-match`")
    (let ((unique ew2) (many env1a) (many srs) (many sh) (erased lock)) $ notail $ elab-expr-demand ew1 fuel sugar scrut env0d ctx (Cons _ smult $ Nil _) no-tele (CCPlain) (Fixed _))
    (let-match many sh (MkHoisted _ _ sctx spre scode))
    (let ((many original)) $ first-res _ _ srs lock)
    (let ((many source-code)) (runtime-one _ smult scode))
    (let ((many env1a1) (many sres) (many saved)) (prepare-argument env1a smult original $ BTrue))
    (let ((many env1a2)) $ settled-from _ _ env1a1 source-code saved)
    (let ((many env2w) (many found)) $ scrutinee-matchable env1a2 sres)
    (let-match many found (Some _ pr) ((None _) (values ew2 env2w ctx $ SNone _)))
    (let-match many pr (MkPair _ _ tid info))
    (let ((many env2)) $ warn-match env2w (mult-is-many smult) tid)
    (let-match many info (MkMatchInfo mid disc mctors _))
    (let ((many (Env) env2h))
      (match many (mult-is-many smult) _
        ((BTrue) (use-entry (held-needs-many env2 tid mid) (Many) mid (BFalse)))
        ((BFalse) env2)))
    (let ((many env4) (many c3)) $ ctor-var env2h craw)
    (let ((many env5) (many mk)) $ marker-checked env4 tid mctors c3)
    (let ((many env6)) $ match many (or (not $ mult-is-many smult) $ mult-is-many mk) (((Env) _)) ((BTrue) env5) ((BFalse) (env-error env5 $ str-cat (qshown env5 c3) " is phantom")))
    ; covered-of tests each alternative in an independent branch environment;
    ; phantom alternatives count too, even when they cannot run.
    (let ((unique ew3) (many env6r) (many _) (many seen) (many _)) $ notail $ elab-branches ew2 fuel sugar branches env6 ctx tid sres smult mctors (Nil _) erased-one (Nil _) (Cons _ c3 $ Nil _) (cells-allowed env6 mid $ BFalse) saved (env-uses env6) (env-uses env6) (BTrue) "`let-match`" (MkSink "" "" (Nil _) (Nil _) (Nil _) (env-scope env6) $ None _) (BFalse) (BFalse) $ Nil _)
    (let ((many env6a) (many other) (many _) (many _))
      $ covered-of mctors (check-coverage mctors env6r seen) seen sres smult (None _) (BFalse) $ Nil _)
    (let ((many (Env) env6b))
      (match many other _
        ((None _) env6a)
        ((Some _ _) (missing-branches mctors env6a sres smult seen "`let-match`"))))
    (let ((many ctele) (many ret)) $ ctor-type env6b c3)
    (let ((many extra)) (cells-allowed env6b mid $ not $ mult-is-many mk))
    (let ((many mults)) $ field-mults (tele-mults ctele) smult)
    (let ((many env7) (many ordinary) (many cellname)) (pattern-fields env6b (raw-pos pat) "a `let-match` pattern" smult sres c3 ctele mults fields extra))
    (let ((many ss)) $ shapes mctors env7)
    (let ((many run)) $ and (env-run-pos env7) $ and (mult-is-many smult) $ not $ env-failed env7)
    (let ((many env9) (many fids) (many u)) $ open-fields env7 ctele (raw-names ordinary) (raw-sites ordinary env7) (Some _ mults) sres c3 ret)
    (let-match many u (UOk env10)
      ((UContra msg) (values ew3 (env-error env9 $ str-cat3 "the scrutinee contradicts the facts in force (" (clash-str env9 msg) ")") ctx $ SNone _)))
    (let ((many env10b) (many alias)) (pattern-cell-option env10 smult sres c3 fids extra cellname))
    (match many smult _
      ((Erased) (values ew3 env10b ctx $ SNone _))
      (else
        (match many run _
          ((BTrue)
            (let-match many sctx (Nil _) ((Cons _ _ _) (values ew3 env10b ctx $ SNone _)))
            (let-match many (ctor-of env10b c3) (Some _ ct) ((None _) (values ew3 env10b ctx $ SNone _)))
            (let ((many env11)) (env-run-let env10b many-one source-code (Cons _ saved (Nil _))))
            (let ((many env12)) (env-set-fields env11 saved ct fids mults))
            (let ((many env13)) (match many alias (((Env) _)) ((None _) env12) ((Some _ x) (forward-state env12 x saved))))
            (values ew3 env13 ctx $ SNone _))
          ((BFalse)
            (let ((many mfids)) $ many-of mults fids)
            (let ((many savedctx)) (Cons _ (Cons _ saved (Nil _)) sctx))
            (let ((many fieldctx)) (Cons _ mfids savedctx))
            (let ((many save)) (SSeq _ _ _ spre (SLet sctx many-one (Cons _ saved (Nil _)) (PkMany _ (Nil _) saved (Nil _) (PkNil _)) source-code)))
            (let ((many destruct2)) (SMatch savedctx (var-code env10b savedctx saved) (match-shape env10b savedctx mid tid disc ss) (discriminant ss c3) mfids))
            (let ((many envr) (many rctx) (many renames)) $ at-renames ctele fids (Nil _) env10b fieldctx)
            (let ((many bound)) $ SSeq _ _ _ save $ SSeq _ _ _ destruct2 renames)
            (let-match many alias (Some _ x) ((None _) (values ew3 envr rctx bound)))
            (let ((many bindcell)) (SLet rctx many-one (Cons _ x (Nil _)) (PkMany _ (Nil _) x (Nil _) (PkNil _)) (var-code envr rctx saved)))
            (values ew3 envr (Cons _ (Cons _ x (Nil _)) rctx) (SSeq _ _ _ bound bindcell)))))))

  ; unary (DESIGN.md section 49): the literals checked in the reference's order, then the let-match the form stands
  ; for, written out as there.
  ((many elab-unary : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Multiplicity) spos) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many arity-error)) $ env-error env (say env "`unary` takes one or two literals"))
    (let-match many args (Cons _ araw rest) ((Nil _) (values ew arity-error ctx $ SNone _)))
    (let ((many env1) (many ea)) $ numeral-entry env araw)
    (let-match many ea (Some _ pa) ((None _) (values ew env1 ctx $ SNone _)))
    (let-match many pa (MkPair _ _ za _))
    (let ((many (Env) env2) (many (Maybe $ Nat) lo))
      (match many rest _
        ((Nil _) (values env1 $ Some _ 0))
        ((Cons _ braw rest2)
          (let-match many rest2 (Nil _) ((Cons _ _ _) (values arity-error $ None _)))
          (let ((many env2) (many eb)) $ numeral-entry env1 braw)
          (let-match many eb (Some _ pb) ((None _) (values env2 $ None _)))
          (let-match many pb (MkPair _ _ zb _))
          (match many (nat-lt zb za) (((Env) _) ((Maybe $ Nat) l0))
            ((BTrue) (values env2 $ Some _ zb))
            ((BFalse) (values (env-error env2 $ str-cat3 (say env2 "`unary`: ") (literal-spelled araw za) $ str-cat " does not exceed " $ literal-spelled braw zb) $ None _))))))
    (let-match many lo (Some _ l) ((None _) (values ew env2 ctx $ SNone _)))
    (let ((many k)) $ nat-sub za l)
    (let-match many (nat-lt 4096 k) (BFalse)
      ((BTrue) (values ew (env-error env2 $ str-cat3 (say env2 "`unary`: ") (nat-str k) " successors is beyond the limit") ctx $ SNone _)))
    (let ((many (Bool) floored)) $ match many rest _ ((Nil _) (BFalse)) ((Cons _ _ _) (BTrue)))
    (let-match many sugar (Succ k2)
      ((Zero) (values ew (env-error env2 "internal: a generated form contains sugar") ctx $ SNone _)))
    (let ((many gen)) $ unary-source za l floored)
    (let ((unique ew1) (many env3) (many ctx2) (many sc)) $ notail $ elab-stmt ew fuel k2 gen (generated-form env2) ctx spos "item of a body")
    (values ew1 (leave-prelude env2 env3) ctx2 sc))

  ; let (section 19): binders, then the right-hand side; run at once in run position (section 29); an
  ; annotation is a checked redundancy.
  ; Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
  ; produce (DESIGN.md section 50); the check of each binder against its value stays as it was.
  ((many elab-let : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (subterm many (LetParts args) parts) (many (Env) env0) (many (List $ List $ Nat) ctx) (many (Maybe $ List $ Entry) tele) (many (List $ Nat) tele-ids) (many (Multiplicity) spos) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let-match many parts (MkLetParts _ binders rhs wr))
    (let ((many env1)) $ check-binder-mults _ binders spos env0)
    (let ((many expect) (erased lbe)) $ src-mults _ binders)
    (let ((unique ew1) (many env1b) (many ctx2) (many sc) (many final)) $ notail $ elab-stmts ew fuel sugar args rhs wr env1 ctx spos "item of a `let`'s right-hand side")
    (let ((many (Bool) none)) $ match many final _ ((FinalNone _ _) (BTrue)) (else (BFalse)))
    (let-match many none (BFalse) ((BTrue) (values ew1 (env-error env1b "a body needs a final expression") ctx2 sc)))
    (let ((many fin)) $ final-raw _ _ final $ RWild $ here-pos env0)
    (let ((many bracket)) $ match many args (((Syn) _)) ((Cons _ b _) b) ((Nil _) (RList (here-pos env0) $ Nil _)))
    (let ((many lsink)) $ MkSink "the enclosing `let`" "value" (Nil _) (raw-items bracket) (Cons _ (MkPair _ _ (loc-in env0 $ raw-pos bracket) "the binders of the enclosing `let` are here") $ Nil _) (env-scope env0) $ None _)
    (let ((many env1s)) $ env-set-sink env1b $ Some _ lsink)
    (let ((unique ew2) (many inner) (many ress) (many h) (erased lock))
      (match many final (((ElabWorld) _ at ew1) ((Env) e0) ((List $ Res) rs0) ((Hoisted ctx2 expect) h0) ((Lockstep (Multiplicity) (Res) expect rs0) l0))
        ((FinalIs _ _ r pf) (notail $ elab-expr-demand ew1 fuel sugar (subterm pf) r env1s ctx2 expect tele (CCPlain) (Fixed _)))
        ((FinalMade _ _ f p r) (notail $ elab-expr-demand ew1 (subterm p) f (raw-size r) r env1s ctx2 expect tele (CCPlain) (Fixed _)))
        ((FinalNone _ _)
          (let ((unique ew3) (many e2) (many rs) (many h2)) $ expr-error ew1 ctx2 expect env1s "a body needs a final expression" "empty body")
          (let ((many rs2) (erased l2)) $ list-fit _ _ expect rs no-res)
          (values ew3 e2 rs2 h2 l2))))
    (let-match many h (MkHoisted _ _ ctx3 pre code))
    (let ((many run)) $ env-run-pos env1)
    (let ((unique ew4) (many env2u) (many ids) (erased lids)) $ notail $ bind-let ew2 fuel sugar args binders (env-hide env1 inner) ress (lockstep-trans _ _ _ _ _ _ lbe lock) run tele (Nil _) $ result-sites env1b (Cons _ fin $ Nil _) $ list-length _ expect)
    (let ((many env2)) $ env-stand-for (match many ids (((Env) _)) ((Cons _ g _) (env-track-all env2u (BLet g $ nat-eq (list-length _ rhs) 1) ids)) ((Nil _) env2u)) tele-ids ids)
    (let ((many many-ids) (erased pk)) $ picked-of _ expect ids $ lockstep-trans _ _ _ _ _ _ (lockstep-sym _ _ _ _ lbe) lids)
    (let ((many (Env) env3))
      (match many ctx3 _
        ((Cons _ _ _) env2)
        ((Nil _)
          (let-match many run (BTrue) ((BFalse) env2))
          (forward-binders (match many (and (mult-is-many $ pos-in env1 expect) $ not $ env-failed inner) (((Env) _))
            ((BTrue) (env-run-let env2 expect code ids))
            ((BFalse) (env-set-tokens env2 ids))) ids ress expect))))
    (match many (or run $ not $ mult-is-many $ pos-in env1 expect) _
      ((BTrue) (values ew4 env3 ctx2 sc))
      ((BFalse) (values ew4 env3 (Cons _ many-ids ctx3) $ SSeq _ _ _ sc $ SSeq _ _ _ pre $ SLet _ expect many-ids pk code))))

  ((many bind-let : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ SrcEntry root) binders) (many (Env) env) (many (List $ Res) ress) (erased (Lockstep (SrcEntry root) (Res) binders ress) lr) (many (Bool) run) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) (many (List $ Pair (Spot) $ Maybe $ Syn) sites) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Nat) ids) (erased (Lockstep (SrcEntry root) (Nat) binders ids) lids))
    (let-match many binders (Cons _ b brest) ((Nil _) (values ew env (Nil _) (LsNil _ _))))
    (let-match many b (MkSrcEntry _ _ smult ssg name place epos))
    (let ((many (Res) r) (many (List $ Res) rrest) (erased (Lockstep (SrcEntry root) (Res) brest rrest) lr2))
      (let-match erased lr (LsCons _ _ _ _ _ _ p))
      (let-match many ress (Cons _ r rs))
      (values r rs p))
    (let ((many (Multiplicity) mult)) $ match many smult _ ((None _) (Many)) ((Some _ m) m))
    (let ((erased (Env) _) (many (Maybe $ Syn) raw) (many (List $ Pair (Spot) $ Maybe $ Syn) srest)) $ next-site env sites)
    (let ((unique ew1) (many (Env) env1a) (many (Maybe $ List $ Entry) trest))
      (match many tele (((ElabWorld) _ at ew) ((Env) env1a) ((Maybe $ List $ Entry) trest))
        ((Some _ es)
          (match many es (((ElabWorld) _ at ew) ((Env) _) ((Maybe $ List $ Entry) t0))
            ((Nil _) (values ew env no-tele))
            ((Cons _ e erest) (values ew (check-sg env (sg-inst done $ entry-sg e) r raw) $ Some _ erest))))
        ((None _)
          (let-match many ssg (Some _ s) ((None _) (values ew env no-tele)))
          (match many s (((ElabWorld) _ at ew) ((Env) _) ((Maybe $ List $ Entry) t0))
            ((SrcTy _ t p) (let ((unique ew2) (many env1) (many ty) (many _)) $ notail $ elab-term ew fuel sugar (subterm p) t env (BTrue) no-tele) (values ew2 (check-sg env1 (SgTy ty) r raw) no-tele))
            ((SrcIs _ t p) (let ((unique ew3) (many env1) (many ty) (many tyty)) $ notail $ elab-term ew fuel sugar (subterm p) t env (BFalse) no-tele) (values ew3 (check-sg env1 (SgIs ty tyty) r raw) no-tele))))))
    (let ((many env1s)) $ settle-res env1a r)
    (let ((many env1)) $ match many (and (is-some _ place) $ not $ is-some _ tele) (((Env) _)) ((BFalse) env1s) ((BTrue) (error-at env1s epos $ say env1s "`at` is allowed only on function telescope and match annotation entries")))
    (let ((many env2a) (many x)) $ bind env1 name (Some _ $ loc-in env1 epos) (BTrue) mult (res-ty r) (Some _ $ res-term r) delegate-id)
    (let ((many env2b)) $ mark-word env2a x $ BFalse)
    (let ((many env2)) $ placed-at env2b x $ res-place r)
    (let ((many (Env) env2m)) (match many (res-term r) (((Env) _)) ((TVar y) (forward-marks env2 x y)) (else env2)))
    (let ((many (Env) env3))
      (match many run _
        ((BTrue) env2m)
        ((BFalse) (match many (res-term r) (((Env) _)) ((TVar y) (forward-binder env2m x y mult)) (else env2m)))))
    (let ((unique ew4) (many env4) (many ids) (erased lk)) $ notail $ bind-let ew1 fuel sugar root brest env3 rrest lr2 run trest (Cons _ (res-term r) done) srest)
    (values ew4 env4 (Cons _ x ids) (LsCons _ _ b x brest ids lk)))

  ; def-fns (sections 17, 54): headers bound Hypothetical, each body elaborated at the block's level under its own
  ; subterm parameters and checked against its return telescope; closures minted Settled in run position.
  ((many elab-def-fns : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Bool) uq) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let-match many args (Cons _ lvraw fns) ((Nil _) (values ew (env-error env (say env "`def-fns` needs a level")) ctx $ SNone _)))
    (let ((unique ew1) (many (Env) env2) (many (Nat) lvl))
      (match many (is-underscore lvraw) (((ElabWorld) _ at ew) ((Env) env2) ((Nat) lvl))
        ((BTrue) (let ((many ewt1) (many ewt2)) (mint-level env (None _) (Some _ $ loc-in env $ raw-pos lvraw))) (values ew ewt1 ewt2))
        ((BFalse) (let ((unique ew2) (many env2) (many t) (many _)) $ notail $ elab-term ew fuel sugar lvraw env (BFalse) no-tele) (let ((many ewt3) (many ewt4)) (level-var-checked env2 t " or `_`")) (values ew2 ewt3 ewt4))))
    (let ((many env2a)) $ refuse-when env2 (and uq $ not $ nat-eq (list-length _ fns) 1) "`def-unique` defines exactly one function")
    (let ((unique ew3) (many env4) (many headers) (many gids) (many fids)) $ notail $ elab-headers ew1 fuel sugar fns env2a lvl uq)
    (let ((unique ew4) (many env5a) (many fns2) (erased lk)) $ notail $ define-fns ew3 fuel sugar fns headers env4 ctx gids gids fids lvl $ env-run-pos env4)
    (let ((many (Env) env5)) $ match many (env-run-pos env4) _ ((BTrue) (env-set-tokens env5a $ bound-erased fns headers gids fids)) ((BFalse) env5a))
    (let ((many group)) $ MkGroup _ gids fns2 lk)
    (let-match many gids (Cons _ _ _) ((Nil _) (values ew4 env5 ctx $ SNone _)))
    (match many ctx _
      ((Nil _) (values ew4 (env-close-group env5 _ group) ctx $ SNone _))
      ((Cons _ _ _) (values ew4 env5 (Cons _ gids ctx) $ SLetRec _ _ group))))

  ((many elab-headers : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) fns) (many (Env) env) (many (Nat) lvl) (many (Bool) uq) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Headers fns) hs) (many (List $ Nat) gids) (many (Bound fns hs gids) ids))
    (let-match many fns (Cons _ f rest) ((Nil _) (values ew env (HStop _) (Nil _) (BStop _))))
    (let ((many envl)) $ env-at env $ raw-pos f)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ str-cat "malformed function definition" $ sp-hints envl "function-definition"))
    (let-match many f (RList _ items) (else (values ew (bad) (HStop fns) (Nil _) (BStop _))))
    (let-match many items (Cons _ sigraw body) ((Nil _) (values ew (bad) (HStop _) (Nil _) (BStop _))))
    (let-match many sigraw (RList _ sitems) (else (values ew (bad) (HStop _) (Nil _) (BStop _))))
    (let-match many sitems (Cons _ mraw items1) ((Nil _) (values ew (bad) (HStop _) (Nil _) (BStop _))))
    (let ((many env0a) (many mult)) $ mult-checked envl mraw)
    (let ((many env0b)) $ match many uq (((Env) _))
      ((BTrue) (refuse-when env0a (and (mult-is-many mult) $ not $ mult-is-once mult) "`def-unique` requires `unique` or `erased`"))
      ((BFalse) (refuse-when env0a (mult-is-once mult) "use `def-unique` to define a unique function")))
    (let ((many isabs) (many isext0) (many isat) (many items2) (erased w2)) $ take-marks3 items1 _ (WIn items1 sitems $ prove-subterm items1 sitems) env0b)
    (let ((many env0x) (many isext)) $ extern-checked (env-at env0b $ raw-pos sigraw) isext0)
    (let ((many env0)) $ env-back env0b env0x)
    (def-fns misuse-lvl $ (many bad0 : -> (many (Env) r)) (env-error env0 $ str-cat "malformed function header" $ sp-hints env0 "function-header"))
    (let-match many items2 (Cons _ nraw items3a) ((Nil _) (values ew (bad0) (HStop _) (Nil _) (BStop _))))
    (let ((many env0e)) $ env-back env0 $ refuse-when (env-at env0 $ raw-pos sigraw) (and isat $ not $ mult-is-many mult) "an `erased` function cannot be an at-function: it is called only where nothing runs")
    (let ((many env0n) (many name)) $ name-checked env0e nraw "a function name")
    ; `at f` after the name annotates a delegate to f (section 41)
    (let ((many (Maybe $ Syn) delegates) (many (List $ Syn) items3) (erased (Subterm (List $ Syn) items3 (List $ Syn) items2) p3))
      (match many items3a (((Maybe $ Syn) d) ((List $ Syn) items3) ((Subterm (List $ Syn) items3 (List $ Syn) items2) p3))
        ((Cons _ a more)
          (let-match many more (Cons _ fraw after-at) ((Nil _) (values (None _) items3a $ prove-subterm items3a items2)))
          (match many (is-mark env0n a $ MkAt) _
            ((BTrue) (values (Some _ fraw) after-at $ prove-subterm after-at items2))
            ((BFalse) (values (None _) items3a $ prove-subterm items3a items2))))
        ((Nil _) (values (None _) items3a $ prove-subterm items3a items2))))
    (let ((many env0d) (many (Maybe $ Nat) dfn))
      (match many delegates (((Env) _) ((Maybe $ Nat) _))
        ((None _) (values env0n (None _)))
        ((Some _ fraw)
          (let ((many env0f) (many df)) $ named (env-at env0n $ raw-pos fraw) fraw "a function name")
          (values (env-back env0n env0f) (Some _ df)))))
    (let-match many items3 (Cons _ colon sg) ((Nil _) (values ew (bad0) (HStop _) (Nil _) (BStop _))))
    (let ((many env1)) $ match many (is-mark env0d colon $ MkColon) (((Env) _)) ((BTrue) env0d) ((BFalse) (bad0)))
    (let ((erased psg)) $ subterm-trans (prove-subterm sg items3) $ subterm-trans p3 $ within-in _ _ _ _ w2 $ subterm-trans (prove-subterm sitems sigraw) $ subterm-trans (prove-subterm sigraw items) $ prove-subterm items f)
    (let ((many env1a) (many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env1)
    (let ((many rs)) $ subs-of after _ wa)
    (let ((unique ew1) (many env2a) (many params) (many rets) (many sig-ids)) $ notail $ elab-fn-type ew fuel sugar (subterm (subterm-trans psg $ prove-subterm f fns)) sg one-step (MkPair _ _ ps rs) env1a)
    (let ((many env2)) $ match many (and isat $ has-runtime rets) (((Env) _)) ((BTrue) (error-at env2a (raw-pos sigraw) $ say env2a "an at-function's returns are erased or `at`")) ((BFalse) env2a))
    ; a function marked `extern` and `at` has no implementation, its marks being a promise (section 39)
    (let ((many claims)) $ and isext $ not isat)
    (let ((many found)) $ extern-of $ spell-binder name)
    (let ((many (Env) env2b))
      (match many found _
        ((None _) env2)
        ((Some _ se)
          (match many se _
            ((MkSomeExtern _ e)
              (error-when env2 (and claims $ not $ nat-eq (runtime-count params) $ ext-arity _ e) $ str-cat3 "the extern implementation of " (tick $ spell-binder name) $ str-cat3 " takes " (nat-str $ ext-arity _ e) $ str-cat3 " arguments, its model " (nat-str $ runtime-count params) ""))))))
    (let ((many (Env) env3)) $ match many claims _ ((BTrue) (claim-extern env2b (spell-binder name) $ is-some _ found)) ((BFalse) env2b))
    (let ((many (Maybe $ SomeExtern) se)) $ match many claims _ ((BTrue) found) ((BFalse) (None _)))
    (let ((many (Env) env3b) (many (Maybe $ Impl) impl))
      (match many se _
        ((None _) (values env3 (None _)))
        ((Some _ e2)
          (let-match many e2 (MkSomeExtern _ e))
          (let-match many (ext-result-shape _ e) (Some _ want) ((None _) (values env3 (Some _ $ MkImpl e2 $ Nil _))))
          (let ((many env3a) (many cs)) $ extern-ctors env3 (spell-binder name) rets want)
          (values env3a (Some _ $ MkImpl e2 cs)))))
    (let ((many h)) $ MkHeader _ (raw-pos sigraw) name mult uq isabs isext isat dfn impl params rets sig-ids body $ subterm-trans (prove-subterm body items) $ prove-subterm items f)
    (let ((many env5t) (many x)) $ bind-header _ h (env-back env env3b) lvl)
    (let ((many env5)) $ env-track env5t (BDefinition) x)
    (let ((unique ew2) (many env6) (many hs) (many gids) (many ids)) $ notail $ elab-headers ew1 fuel sugar rest env5 lvl uq)
    (match many mult _
      ((Erased) (values ew2 env6 (HCons _ _ h hs) gids (BErased _ _ _ _ _ x ids)))
      (else (values ew2 env6 (HCons _ _ h hs) (Cons _ x gids) (BMany _ _ _ _ _ x ids)))))

  ((many define-fns : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) fns) (subterm many (Headers fns) headers) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) gall) (many (List $ Nat) gids) (many (Bound fns headers gids) fids) (many (Nat) lvl) (many (Bool) top) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Pair (Nat) $ Func gall ctx) fns2) (erased (Lockstep (Nat) (Pair (Nat) $ Func gall ctx) gids fns2) lk))
    (match many fns _
      ((Nil _)
        (let-match many fids (BStop _))
        (values ew env (Nil _) (LsNil _ _)))
      ((Cons _ f rest)
        (match many headers _
          ((HStop _)
            (let-match many fids (BStop _))
            (values ew env (Nil _) (LsNil _ _)))
          ((HCons _ _ h hrest)
            (match many fids _
              ((BMany _ _ _ _ _ x xrest)
                (let-match many gids (Cons _ _ grest))
                (let ((unique ew1) (many env3) (many fn)) $ notail $ define-fn ew fuel sugar f h env ctx gall x lvl top)
                (let ((unique ew2) (many env4) (many more) (erased lk)) $ notail $ define-fns ew1 fuel sugar rest hrest env3 ctx gall grest xrest lvl top)
                (values ew2 env4 (Cons _ (MkPair _ _ x fn) more) (LsCons _ _ x (MkPair _ _ x fn) grest more lk)))
              ((BErased _ _ _ _ _ x xrest)
                (let ((unique ew3) (many env3) (many _)) $ notail $ define-fn ew fuel sugar f h env ctx gall x lvl top)
                (tail $ define-fns ew3 fuel sugar rest hrest env3 ctx gall gids xrest lvl top))))))))

  ; One function's body checked at its level under its parameters, the group's frame and the defining scope,
  ; its marks validated, and its delegate proof bound where it has one.
  ((many define-fn : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm erased (Syn) f) (many (Header f) h) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) gall) (many (Nat) x) (many (Nat) lvl) (many (Bool) top) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (Func gall ctx) fn))
    (let-match many h (MkHeader _ hpos name mult uq isabs isext isat delegates impl params rets sig-ids body pb))
    (let ((many env0)) $ match many uq (((Env) _)) ((BTrue) (set-entry-mult env x $ Erased)) ((BFalse) env))
    (let ((many body-erased)) $ or (env-usage-erased env) $ or isabs $ not $ mult-is-many mult)
    (let ((many envb0t) (many pids) (erased _)) $ open-tele params (env-set-usage-erased (env-set-run-pos env0 $ BFalse) body-erased) (None _) (None _) (None _) (Nil _) $ BFalse)
    (let ((many envb0)) $ env-stand-for (env-track-all envb0t (BParam) pids) sig-ids pids)
    (let ((many envb1)) $ env-enter-body (mark-words pids envb0 $ BFalse) x lvl $ subterm-params params pids)
    (let ((many captures)) $ match many uq (((List $ Nat) _)) ((BTrue) (env-captures env)) ((BFalse) (env-words env)))
    (let ((many envb)) $ env-set-uses (env-set-captures (env-set-usage-erased (env-set-unwarned (env-set-in-extern envb1 (or (env-in-extern env) isext)) $ or (env-unwarned env) $ or isext isat) body-erased) captures) $ uses-fork $ env-uses envb1)
    (let ((many rms)) $ under-list (tele-mults rets) mult)
    (let ((many pvars)) $ tvars-rev pids $ Nil _)
    ; the frame holds the runtime parameters; a parameter written `at` is a rename of its target's word,
    ; bound by a let around the body (section 36)
    (let ((many rt)) $ runtime-ids params pids)
    (let ((many base)) $ Cons _ rt $ Cons _ gall ctx)
    (let ((many envr) (many bctx) (many renames)) $ at-renames params pids (Nil _) envb base)
    (let ((unique ew1) (many (Env) envb2) (many (Code bctx rms) code))
      (match many isabs (((ElabWorld) _ at ew) ((Env) envb2) ((Code bctx rms) code))
        ((BTrue)
          (let ((unique ew2) (many envb2)) $ notail $ elab-refute ew fuel sugar (subterm pb) body body (WHere _) envr bctx)
          (values ew2 envb2 $ CAbsurd _ rms))
        ((BFalse)
          (let ((many tele)) $ instantiate-tele pvars rets)
          (let ((unique ew3) (many envb1b) (many ress) (many code) (erased _)) $ notail $ elab-body ew fuel sugar (subterm pb) body body (WHere _) envr bctx rms (Some _ tele) $ Some _ $ MkSink "" "return value" (tele-with-mults tele rms) (Nil _) (Nil _) (env-scope envr) $ Some _ x)
          (let ((many envb2)) $ check-results-count envb1b body rets ress pvars)
          (values ew3 envb2 $ match many mult (((Code bctx rms) _)) ((Erased) (CErased _ rms)) (else code)))))
    (let ((many physical)) $ under-list (physical-mults rets) mult)
    (let ((many envb2a) (many projected)) $ project-code bctx envb2 rms physical code)
    (let ((many envb3m) (many code2) (many delegated)) $ check-marks (env-at envb2a hpos) base rt physical $ wrap-stmt _ _ physical renames projected)
    (let ((many envb3)) $ env-back envb2a envb3m)
    (let ((many env2)) $ set-entry-mult (env-set-uses (env-discard env envb3) $ uses-join (env-uses env) $ env-uses envb3) x mult)
    (let ((many (Env) env3))
      (match many delegated _
        ((None _) env2)
        ((Some _ callee)
          (let ((many env2b))
            (match many isext (((Env) _))
              ((BTrue) (env-error (env-at env2 hpos) (say env2 "a function marked `extern` cannot have a `delegate` body: its implementation is promised only under its own signature, and a `Delegate` proof would let a `coerce` run it under the callee's; mark the call `tail`")))
              ((BFalse) env2)))
          (env-set-aliases env2b $ idmap-set _ x (alias-target env2b $ maybe-or _ delegates callee) $ env-aliases env2b))))
    ; the delegate annotation names the function the one `delegate` call names (section 41)
    (let ((many (Env) env3d))
      (match many delegates _
        ((None _)
          (match many delegated (((Env) _))
            ((None _) env3)
            ((Some _ callee) (error-at env3 hpos $ str-cat3 (tick $ spell-binder name) (say env3 " delegates to ") $ str-cat3 (qshow envb3 $ TVar callee) (say env3 ", so its header must name the callee: write `at` and the callee after the name") ""))))
        ((Some _ df)
          (let ((many env3a)) $ env-at env3 hpos)
          (env-back env3 $ match many delegated (((Env) _))
            ((None _) (env-error env3a $ str-cat3 (tick $ spell-binder name) (say env3a " is declared `at` ") $ str-cat3 (qshown env3a df) (say env3a " but its body is not a `delegate` call") ""))
            ((Some _ callee)
              (match many (equal-env envb3 (TVar callee) $ TVar df) (((Env) _))
                ((BTrue) env3a)
                ((BFalse) (env-error env3a $ str-cat3 (tick $ spell-binder name) (say env3a " is declared `at` ") $ str-cat3 (qshown env3a df) (say env3a " but delegates to ") $ qshow envb3 $ TVar callee))))))))
    ; an at-function's body erases to nothing and is never run through the proof; what remains is the dummy a
    ; first-class call without the proof reaches (section 39)
    (let ((many env3e)) $ match many (and isat $ and (not isabs) $ not $ erases-to-nothing _ _ code2) (((Env) _))
      ((BTrue) (error-at env3d hpos $ str-cat3 (say env3d "the body of at-function ") (tick $ spell-binder name) $ say env3d " does not erase to nothing, or to a reordering of variables: it stores, allocates or calls"))
      ((BFalse) env3d))
    (let ((many (Code base physical) code3)) $ match many isat _
      ((BTrue) (let ((many missing) (erased pk)) $ codes-missing base physical) (CValues _ physical missing pk))
      ((BFalse) code2))
    (values ew1 env3e $ match many delegated (((Func gall ctx) _))
      ((None _) (MkFunc _ _ physical (spell-binder name) x rt code3 impl top))
      ((Some _ callee) (MkAlias _ _ (spell-binder name) x $ var-code env3e (Cons _ gall ctx) $ alias-target env3e $ maybe-or _ delegates callee))))

  ; def-adts (sections 8, 21, 54): type constructors bound first, each as soon as its header is read so a
  ; later header may mention it, then each type's constructors, Matchable and Newtype; every constructor
  ; returns its own type.
  ((many elab-opaques : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) es) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
    (let-match many es (Cons _ e rest) ((Nil _) (values ew env)))
    (let ((many envl)) $ env-at env $ raw-pos e)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ str-cat (say envl "malformed `def-opaque` entry") $ sp-hints envl "def-opaque"))
    (let-match many e (RList _ items) (else (values ew (bad))))
    (let-match many items (Cons _ sigraw more) ((Nil _) (values ew (bad))))
    (let-match many more (Nil _) ((Cons _ _ _) (values ew (bad))))
    (let-match many sigraw (RList _ sitems) (else (values ew (bad))))
    (let-match many sitems (Cons _ nraw items1) ((Nil _) (values ew (bad))))
    (let-match many items1 (Cons _ colon sg) ((Nil _) (values ew (bad))))
    (let-match many (is-mark envl colon $ MkColon) (BTrue) ((BFalse) (values ew (bad))))
    (let ((many env0) (many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) envl)
    (let ((unique ew1) (many env2) (many ty)) $ notail $ elab-tyctor ew fuel sugar sg one-step (MkPair _ _ ps $ subs-of after _ wa) env0)
    (let ((many envn) (many bname)) $ name-checked env2 nraw "a type constructor name")
    (let ((many env3) (many _)) $ bind-erased envn bname (Some _ $ loc-in envn $ raw-head-pos e) (BTrue) (Erased) ty (None _) delegate-id)
    (tail $ elab-opaques ew1 fuel sugar rest $ env-back env env3))

  ((many elab-prims : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) es) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
    (let-match many es (Cons _ e rest) ((Nil _) (values ew env)))
    (let ((many envl)) $ env-at env $ raw-pos e)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ str-cat (say envl "malformed `def-prim` entry") $ sp-hints envl "def-prim"))
    (let-match many e (RList _ items) (else (values ew (bad))))
    (let-match many items (Cons _ sigraw more) ((Nil _) (values ew (bad))))
    (let-match many more (Nil _) ((Cons _ _ _) (values ew (bad))))
    (let-match many sigraw (RList _ sitems) (else (values ew (bad))))
    (let-match many sitems (Cons _ mraw items0) ((Nil _) (values ew (bad))))
    (let-match many items0 (Cons _ nraw items1) ((Nil _) (values ew (bad))))
    (let-match many items1 (Cons _ colon sg) ((Nil _) (values ew (bad))))
    (let-match many (is-mark envl colon $ MkColon) (BTrue) ((BFalse) (values ew (bad))))
    (let ((many envs)) $ env-at env $ raw-pos sigraw)
    (let ((many envm) (many mult)) $ mult-checked envs mraw)
    (let-match many (mult-is-once mult) (BFalse) ((BTrue) (values ew (env-back env $ env-error envm $ say envm "a primitive is declared `many` or `erased`"))))
    (let ((many found)) $ match many nraw (((Maybe $ Sp) _)) ((RAtom _ n) (match many n (((Maybe $ Sp) _)) ((NSrc s) (prim-named primitives s)) (else (None _)))) (else (None _)))
    (let-match many found (Some _ sp) ((None _) (values ew (env-back env $ env-error (env-at envm $ raw-pos nraw) $ str-cat (qraw nraw) " names no primitive the compilers implement"))))
    (let-match many (prim-sig envm sp) (None _) ((Some _ _) (values ew (env-back env $ env-error envm $ str-cat "a second `def-prim` for " $ tick $ sp-name sp))))
    (let ((many env0) (many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) envm)
    (let ((unique ew1) (many env2) (many ids) (many params)) $ notail $ elab-tele ew fuel sugar sg one-step ps env0 (MMDeclared) (Nil _) (BFalse) (BFalse) (BTrue) $ BFalse)
    (let ((unique ew2) (many env3) (many _) (many rets)) $ notail $ elab-tele ew1 fuel sugar sg one-step (subs-of after _ wa) env2 (MMDeclared) (tvars-rev ids $ Nil _) (BFalse) (BFalse) (BTrue) $ BFalse)
    (let ((many env4)) $ env-discard envm env3)
    (let-match many (and (mult-is-many mult) $ and (not $ is-some _ $ prim-named implemented $ sp-name sp) $ any-stored rets) (BFalse)
      ((BTrue) (values ew2 (env-back env $ env-error env4 $ str-cat3 "the compilers have no implementation of " (tick $ sp-name sp) ", so its returns must be erased or written `at`"))))
    (tail $ elab-prims ew2 fuel sugar rest $ env-back env $ env-add-prim env4 $ MkPrimSig sp mult params rets))

  ((many elab-prim-call : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) items) (many (Env) env0) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) (many (Multiplicity) pos) (many (Sp) sp) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many items (Cons _ _ args) ((Nil _) (values ew env0 (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "prim")))
    (let-match many (prim-sig env0 sp) (Some _ psig)
      ((None _) (values ew (env-error env0 $ str-cat (tick $ spell env0 $ sp-name sp) " has no signature until `def-prim` declares it") (list-replicate _ (list-length _ expect) no-res) $ hoist-none ctx expect $ CError _ expect "prim")))
    (let-match many psig (MkPrimSig _ m params rets0))
    (let ((many rets)) $ match many (not $ mult-is-many m) (((List $ Entry) _)) ((BTrue) (entries-erased rets0)) ((BFalse) rets0))
    (let ((unique ew1) (many env2) (many acc) (many _) (many ctx2) (many apre) (many actuals)) $ notail $ check-args ew fuel sugar args (subs-all args) one-step env0 (CalleeForm env0 $ sp-name sp) ctx params pos tele (ARCall rets) (BFalse) (BTrue) $ BTrue)
    (let ((many env3) (many hidden)) $ match many (sp-eq sp $ SpExpr $ ExSettledMult) (((Env) _) ((List $ Code ctx2 many-one) _))
      ((BTrue)
        (let ((many env3a) (many ce)) $ prelude-id env2 "MErased")
        (let ((many env3b) (many cm)) $ prelude-id env3a "MMany")
        (let ((many env3c) (many cu)) $ prelude-id env3b "MUnique")
        (values env3c $ Cons _ (nullary-ctor-code _ ce) $ Cons _ (nullary-ctor-code _ cm) $ Cons _ (nullary-ctor-code _ cu) $ Nil _))
      ((BFalse)
        (let-match many (or (sp-eq sp $ SpExpr $ ExSettledEq) $ sp-eq sp $ SpExpr $ ExSlotEq) (BTrue)
          ((BFalse)
            (let-match many (sp-eq sp $ SpExpr $ ExResolve) (BTrue)
              ((BFalse)
                (let-match many (sp-eq sp $ SpExpr $ ExReadFile) (BTrue) ((BFalse) (values env2 $ Nil _)))
                (let ((many env3a) (many co)) $ prelude-id env2 "Ok")
                (let ((many env3b) (many cf)) $ prelude-id env3a "Fail")
                (values env3b $ Cons _ (CConst _ co) $ Cons _ (CConst _ cf) $ Nil _)))
            (let ((many env3a) (many cs)) $ prelude-id env2 "RSettled")
            (let ((many env3b) (many ch)) $ prelude-id env3a "RHypothetical")
            (let ((many env3c) (many cu)) $ prelude-id env3b "RUnbound")
            (values env3c $ Cons _ (CConst _ cs) $ Cons _ (nullary-ctor-code _ ch) $ Cons _ (nullary-ctor-code _ cu) $ Nil _)))
        (let ((many env3a) (many cn)) $ prelude-id env2 "None")
        (let ((many env3b) (many cs)) $ prelude-id env3a "Some")
        (let ((many env3c) (many cr)) $ prelude-id env3b $ match many (sp-eq sp $ SpExpr $ ExSlotEq) _ ((BTrue) "Refl") ((BFalse) "JMRefl"))
        (values env3c $ Cons _ (nullary-ctor-code _ cn) $ Cons _ (CApp _ many-one (CConst _ cs) (Cons _ (nullary-ctor-code _ cr) $ Nil _) (CCCtor)) $ Nil _)))
    (let ((many all) (erased _)) $ list-append _ actuals hidden)
    (call-returns ew1 env3 ctx ctx2 apre expect rets acc pos demand (None _) (tick $ kw-mark $ sp-name sp) $ InvPrim _ sp all))

  ((many elab-adt-headers : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) adts) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (AdtHeaders adts) hs) (many (Tids adts hs) tids))
    (let-match many adts (Cons _ adt rest) ((Nil _) (values ew env (AStop _) $ TStop _)))
    (let ((many envl)) $ env-at env $ raw-pos adt)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ str-cat (say envl "malformed `def-adts` entry") $ sp-hints envl "def-adts-entry"))
    (let-match many adt (RList _ items) (else (values ew (bad) (AStop adts) $ TStop adts)))
    (let-match many items (Cons _ sigraw rest2) ((Nil _) (values ew (bad) (AStop _) $ TStop _)))
    (let-match many sigraw (RList _ sitems) (else (values ew (bad) (AStop _) $ TStop _)))
    (let-match many sitems (Cons _ nraw items1) ((Nil _) (values ew (bad) (AStop _) $ TStop _)))
    (let ((many envn) (many bname)) $ name-checked envl nraw "a type constructor name")
    (let ((many name)) $ spell-binder bname)
    (let-match many items1 (Cons _ colon sg) ((Nil _) (values ew (bad) (AStop _) $ TStop _)))
    (let ((many env0)) $ match many (is-mark envn colon $ MkColon) (((Env) _)) ((BTrue) envn) ((BFalse) (bad)))
    (def-fns misuse-lvl $ (many bad0 : -> (many (Env) r)) (env-error env0 $ str-cat (say env0 "malformed `def-adts` entry") $ sp-hints env0 "def-adts-entry"))
    (let ((many env0a) (many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env0)
    (let-match many after (Cons _ tyraw after2) ((Nil _) (values ew (bad0) (AStop _) $ TStop _)))
    (let-match many rest2 (Cons _ draw after3) ((Nil _) (values ew (bad0) (AStop _) $ TStop _)))
    (let ((many stray)) $ match many after2 (((Bool) _)) ((Nil _) (BFalse)) ((Cons _ _ _) (BTrue)))
    (let ((many env0c)) $ error-when env0a stray "a type constructor declares one return")
    (let ((many env1a) (many disc)) $ disc-of-checked env0c draw)
    (let ((many nt) (many ext0) (many cs) (erased wc)) $ take-marks after3 _ (within-step after3 rest2 items (prove-subterm after3 rest2) $ WIn rest2 items $ prove-subterm rest2 items) env1a (MkNewtypeMark) $ MkExtern)
    (let ((many env1x) (many ext)) $ extern-checked (env-at env1a $ raw-pos sigraw) ext0)
    (let ((many env1)) $ env-back env1a env1x)
    (let ((many tyraws)) $ Cons _ (MkSub _ tyraw $ in-within (Syn) tyraw after sg (prove-subterm tyraw after) wa) $ Nil _)
    (let ((unique ew1) (many env2) (many ty)) $ notail $ elab-tyctor ew fuel sugar sg one-step (MkPair _ _ ps tyraws) env1)
    (let ((many env2b) (many x)) $ bind-erased env2 bname (Some _ $ loc-in env2 $ raw-head-pos adt) (BTrue) (Erased) ty (None _) delegate-id)
    (let ((unique ew2) (many env3) (many hs) (many tids)) $ notail $ elab-adt-headers ew1 fuel sugar rest $ env-back env env2b)
    (let ((many h)) $ MkAdtHeader _ name disc nt ext cs $ within-in cs items (Syn) adt wc $ prove-subterm items adt)
    (values ew2 env3 (AHCons _ _ h hs) $ TCons _ _ _ _ x tids))

  ((many define-adts : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) adts) (subterm many (AdtHeaders adts) headers) (many (Env) env) (many (Tids adts headers) tids) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) consts))
    (let-match many adts (Cons _ adt rest) ((Nil _) (values ew env $ Nil _)))
    (let-match many headers (AHCons _ _ h hrest) ((AStop _) (values ew env $ Nil _)))
    (let-match many tids (TCons _ _ _ _ tid trest))
    (let-match many h (MkAdtHeader _ name disc nt ext ctors pc))
    (let ((many envh)) $ env-at env $ raw-head-pos adt)
    (let ((unique ew1) (many env2) (many mcpairs)) $ notail $ elab-ctors ew fuel sugar (subterm (subterm-trans pc $ prove-subterm adt adts)) ctors envh tid nt)
    (let ((many mctors)) $ mctors-of mcpairs)
    (let ((many ss)) $ shapes mctors env2)
    (let ((many tagged)) $ tagged-of disc ss)
    (let ((many found)) $ match many (str-eq name "Raw") (((Maybe $ ExtType) _)) ((BTrue) (raw-ext env2)) ((BFalse) (match many (str-eq name "Slots") _ ((BTrue) (slots-ext env2)) ((BFalse) (ext-type-of name)))))
    (let ((many (Env) env2b)) $ match many ext _ ((BTrue) (claim-extern env2 name $ is-some _ found)) ((BFalse) env2))
    (let ((many (Maybe $ ExtType) extname)) $ match many ext _ ((BTrue) found) ((BFalse) (None _)))
    (let ((many (Env) env2c))
      (match many extname _
        ((None _) env2b)
        ((Some _ et)
          (let ((many ns)) $ cshape-arities $ non-phantom ss)
          (let ((many want)) $ ext-type-shape et)
          (check-ext-shape env2b name tagged ns want))))
    (let ((many adt2)) $ mint-adt env2c tid disc ss extname nt)
    (let ((many records)) $ adt-ctors adt2)
    (let ((many cvals)) $ ctor-values records)
    (let ((many env3) (many mid)) $ bind-closed env2c (None _) (None _) (BFalse) (Many) (BMat _ adt2) (TMatchable disc nt ext (TVar tid) mctors) (None _) delegate-id)
    (let ((many env3b)) $ open-minted env3 mid)
    (let ((many (Env) env4))
      (match many nt _
        ((BFalse) env3b)
        ((BTrue)
          (match many (newtype-wrappers disc ss) (((Env) _))
            ((Nil _) (env-error env3b $ str-cat (tick name) " is not of newtype shape (section 33)"))
            ((Cons _ _ _) env3b)))))
    (let ((unique ew2) (many env5) (many more)) $ notail $ define-adts ew1 fuel sugar rest hrest env4 trest)
    (let ((many all) (erased _)) $ list-append _ cvals $ Cons _ (MkPair _ _ mid $ BMat _ adt2) more)
    (values ew2 env5 all))

  ((many elab-ctors : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) ctors) (many (Env) env) (many (Nat) tid) (many (Bool) nt) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Pair (Multiplicity) $ Nat) cs))
    (let ((unique ew1) (many envs0) (many sx)) $ splice-tail ew (env-set-usage-erased env $ BTrue) 0 ctors)
    (let ((many envs)) $ env-set-usage-erased envs0 $ env-usage-erased env)
    (let-match many sx (None _)
      ((Some _ rr)
        (let-match many rr (Ok _ c2) ((Fail _ m) (values ew1 (env-error envs m) $ Nil _)))
        (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envs "more than 10000 macro expansions") $ Nil _)))
        (tail $ elab-ctors ew1 f2 (raws-size c2) c2 envs tid nt)))
    (let-match many ctors (Cons _ craw rest) ((Nil _) (values ew1 env $ Nil _)))
    (let ((many envl)) $ env-at env $ raw-pos craw)
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error envl $ str-cat "malformed constructor" $ sp-hints envl "constructor"))
    (let ((many (Env) env0) (many (Maybe $ CtorParts craw) parsed))
      (match many craw _
        ((RList _ items)
          (let-match many items (Cons _ mraw items1) ((Nil _) (values (bad) $ None _)))
          (let ((many env0) (many mult)) $ mult-checked envl mraw)
          (def-fns misuse-lvl $ (many bad0 : -> (many (Env) r)) (env-error env0 $ str-cat "malformed constructor" $ sp-hints env0 "constructor"))
          (let-match many items1 (Cons _ nraw more) ((Nil _) (values (bad0) $ None _)))
          (let-match many more (Cons _ colon sg) ((Nil _) (values (bad0) $ None _)))
          (let ((many env1)) $ match many (is-mark env0 colon $ MkColon) (((Env) _)) ((BTrue) env0) ((BFalse) (bad0)))
          (let ((many env1n) (many name)) $ name-checked env1 nraw "a constructor name")
          (values env1n $ Some _ $ MkCtorParts _ mult name sg $ prove-subterm sg craw)) (else (values (bad) $ None $ CtorParts craw))))
    (let-match many parsed (Some _ cp) ((None _) (tail $ elab-ctors ew1 fuel sugar rest (env-back env env0) tid nt)))
    (let-match many cp (MkCtorParts _ mult name sg psg))
    (let ((many env0a) (many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env0)
    (let ((unique ew2) (many env2) (many tele) (many ret) (many ty)) $ notail $ elab-valctor ew1 fuel sugar (subterm (subterm-trans psg $ prove-subterm craw ctors)) sg one-step (MkPair _ _ ps $ subs-of after _ wa) env0a)
    (let ((many (Env) env2b))
      (match many (type-head env2 ret) _
        ((None _) (env-error env2 $ str-cat3 (tick $ spell-binder name) " must return an application of " $ qshown env2 tid))
        ((Some _ t) (match many (nat-cmp t tid) (((Env) _)) ((CEq _ _ _) env2) (else (env-error env2 $ str-cat3 (tick $ spell-binder name) " must return an application of " $ qshown env2 tid))))))
    (let ((many (Env) env2c))
      (match many (and (not $ mult-is-many mult) $ not $ nat-is-zero $ many-count tele) _
        ((BTrue) (env-warn env2b $ located env2b ": warning: " $ str-cat3 "phantom constructor " (tick $ spell-binder name) " has a non-erased field"))
        ((BFalse) env2b)))
    (let ((many env3)) $ env-discard env0 env2c)
    (let ((many (Env) env4) (many (Nat) c)) $ match many mult _ ((Erased) (bind-erased env3 name (Some _ $ loc-in env3 $ raw-pos craw) (BTrue) mult ty (None _) delegate-id)) (else (bind env3 name (Some _ $ loc-in env3 $ raw-pos craw) (BTrue) mult ty (None _) delegate-id)))
    (let ((unique ew3) (many env5) (many cs)) $ notail $ elab-ctors ew2 fuel sugar rest (env-back env env4) tid nt)
    (values ew3 env5 $ Cons _ (MkPair _ _ mult c) cs))
  ; tail and delegate wrap a call (section 19); the compiled code must be that call.
  ((many elab-marked : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) (many (Sp) sp) (many (ExprDemand expect) demand) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let ((many env1)) $ refuse-unless env (mult-is-many $ pos-in env expect) $ str-cat (tick $ sp-name sp) " in an erased position")
    (let-match many args (Cons _ call _)
      ((Nil _) (expr-error ew ctx expect env1 (str-cat (tick $ spell env1 $ sp-name sp) " marks a function call, not nothing") "mark")))
    (let ((unique ew1) (many env2) (many ress) (many h) (erased _)) $ notail $ elab-expr-demand ew fuel sugar call env1 ctx expect tele cc demand)
    (let-match many h (MkHoisted _ _ _ _ code))
    (let ((many ok)) $ marked-call _ _ code cc)
    (match many ok _
      ((BTrue) (values ew1 env2 ress h))
      ((BFalse) (values ew1 (env-error env2 $ str-cat3 (tick $ spell env2 $ sp-name sp) " marks a function call, not " $ qraw call) ress h))))

  ; Each entry of a values against its entry of the telescope expected, instantiated with the entries before it.
  ((many elab-values : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Res) ress) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre) (many (List $ Code ctx2 many-one) codes) (erased (Picked (Code ctx2 many-one) expect codes) pk))
    (let-match many expect (Cons _ m mrest) ((Nil _) (values ew env (Nil _) ctx (SNone _) (Nil _) (PkNil _))))
    (match many args _
      ((Nil _)
        (let ((many codes) (erased pk)) $ codes-missing ctx expect)
        (values ew env (Nil _) ctx (SNone _) codes pk))
      ((Cons _ arg arest)
        (let ((many (Maybe $ List $ Entry) here) (many (Maybe $ List $ Entry) trest))
          (match many tele _
            ((None _) (values no-tele no-tele))
            ((Some _ es)
              (match many es (((Maybe $ List $ Entry) _) ((Maybe $ List $ Entry) t))
                ((Nil _) (values no-tele no-tele))
                ((Cons _ e erest) (values (Some _ $ Cons _ (entry-with-sg e $ sg-inst done $ entry-sg e) $ Nil _) $ Some _ erest))))))
        (let ((unique ew1) (many env2) (many rs) (many h) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar arg env ctx (Cons _ m $ Nil _) here (CCPlain) (Fixed _))
        (let-match many h (MkHoisted _ _ c1 pre1 code))
        (let ((unique ew2) (many env3) (many ress) (many c2) (many pre2) (many codes) (erased pk)) $ notail $ elab-values ew1 fuel sugar arest env2 c1 mrest trest $ Cons _ (res-term $ first-res _ _ rs lock) done)
        (let ((many codes2) (erased pk2))
          (match many m (((List $ Code c2 many-one) cs) ((Picked (Code c2 many-one) expect cs) p))
            ((Many) (let ((many one)) $ weaken-along _ _ many-one pre2 code) (values (Cons _ one codes) (PkMany _ mrest one codes pk)))
            ((Once) (let ((many one)) $ weaken-along _ _ many-one pre2 $ runtime-one _ m code) (values (Cons _ one codes) (PkOnce _ mrest one codes pk)))
            ((Erased) (values codes (PkErased _ mrest codes pk)))))
        (values ew2 env3 (Cons _ (first-res _ _ rs lock) ress) c2 (SSeq _ _ _ pre1 pre2) codes2 pk2))))

  ((many elab-two-terms : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty))
    (let ((many bad) (many m)) $ values (env-error env "two arguments expected") $ TErr "missing")
    (let-match many args (Cons _ araw rest) ((Nil _) (values ew bad m m m m)))
    (let-match many rest (Cons _ braw _) ((Nil _) (values ew bad m m m m)))
    (let ((unique ew1) (many env2) (many a) (many aty)) $ notail $ elab-term ew fuel sugar araw env (BFalse) no-tele)
    (let ((unique ew2) (many env3) (many b) (many bty)) $ notail $ elab-term ew1 fuel sugar braw env2 (BFalse) no-tele)
    (values ew2 (settle (settle env3 a) b) a aty b bty))

  ; Two proofs of the given kinds, elaborated erased (section 14).
  ((many two-proofs : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Res) p) (many (Res) q))
    (def-fns misuse-lvl $ (many bad : -> (many (Env) r)) (env-error env "two proofs expected"))
    (let-match many args (Cons _ araw rest) ((Nil _) (values ew (bad) no-res no-res)))
    (let-match many rest (Cons _ braw _) ((Nil _) (values ew (bad) no-res no-res)))
    (let ((unique ew1) (many env2) (many prs) (many _) (erased lockp)) $ notail $ elab-expr-demand ew fuel sugar araw env ctx erased-one no-tele (CCPlain) (Fixed _))
    (let ((unique ew2) (many env3) (many qrs) (many _) (erased lockq)) $ notail $ elab-expr-demand ew1 fuel sugar braw env2 ctx erased-one no-tele (CCPlain) (Fixed _))
    (values ew2 (settle (settle env3 $ erased-term prs lockp) $ erased-term qrs lockq) (erased-res prs lockp) $ erased-res qrs lockq))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field, each checked against
  ; the field's type on its side (section 33).
  ((many elab-sharing-side : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) -> (unique (ElabWorld) ewr at ew) (many (Env) e) (many (Term) side))
    (let-match many args (Cons _ raw _) ((Nil _) (values ew (env-error env "a `Sharing` argument is required") $ TErr "Sharing")))
    (match many (is-underscore raw) _
      ((BTrue)
        (let ((many env2) (many x)) $ bind-as env (BTrue) (BFalse) (None _) (Some _ $ loc-in env $ raw-pos raw) (BFalse) (Erased) sharing-term (None _) delegate-id)
        (values ew env2 $ TVar x))
      ((BFalse)
        (let ((unique ew1) (many env2) (many t) (many ty)) $ notail $ elab-term ew fuel sugar raw env (BFalse) no-tele)
        (values ew1 (check env2 "type" ty sharing-term) t))))

  ((many elab-coercible-proof : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) ctor) (many (Maybe $ Pair (Term) $ Term) sides) -> (unique (ElabWorld) ewr at ew) (many (Env) e) (many (Res) r))
    (let-match many args (Cons _ raw _)
      ((Nil _) (values ew (env-error env $ str-cat "a " $ str-cat (qshown env ctor) " proof is required") no-res)))
    (let ((many env1) (many tele)) $ coercible-proof-tele env ctor sides)
    (let ((unique ew1) (many env2) (many ress) (many _) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar raw env1 ctx erased-one tele (CCPlain) (Fixed _))
    (let ((many r)) $ erased-res ress lock)
    (values ew1 (settle-res env2 r) r))

  ((many coercible-ctor-args : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) tele) (many (List $ Term) src) (many (List $ Term) tgt) (many (Nat) c) (many (Term) side) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Term) src2) (many (List $ Term) tgt2))
    (def-fns refusal-lvl $ (many wrong : -> (many (Env) r)) (env-error env "internal: `coercible-ctor` argument count"))
    (let-match many tele (Cons _ e rest)
      ((Nil _) (match many args _ ((Nil _) (values ew env src tgt)) ((Cons _ _ _) (values ew (wrong) src tgt)))))
    (match many (entry-mult e) _
      ((Erased)
        (let-match many args (Cons _ sraw more) ((Nil _) (values ew (wrong) src tgt)))
        (let-match many more (Cons _ traw args2) ((Nil _) (values ew (wrong) src tgt)))
        (let ((unique ew1) (many env2) (many s) (many sty)) $ notail $ elab-term ew fuel sugar sraw env (BFalse) no-tele)
        (let ((unique ew2) (many env3) (many t) (many tty)) $ notail $ elab-term ew1 fuel sugar traw env2 (BFalse) no-tele)
        (let ((many env4)) $ check-sg (settle (settle env3 s) t) (sg-inst src $ entry-sg e) (term-res s sty) $ None _)
        (let ((many env5)) $ check-sg env4 (sg-inst tgt $ entry-sg e) (term-res t tty) $ None _)
        (tail $ coercible-ctor-args ew2 fuel sugar args2 env5 ctx rest (Cons _ s src) (Cons _ t tgt) c side))
      (else
        (let-match many args (Cons _ praw more) ((Nil _) (values ew (wrong) src tgt)))
        (let ((many fs)) $ match many (entry-mult e) (((Term) _)) ((Once) side) (else shared-term))
        (let ((many env0) (many ptele)) $ coercible-proof-tele env coercible-id $ Some _ $ MkPair _ _ fs fs)
        (let ((unique ew3) (many env1a) (many prs) (many _) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar praw env0 ctx erased-one ptele (CCPlain) (Fixed _))
        (let ((many p)) $ erased-res prs lock)
        (let ((many env1)) $ settle-res env1a p)
        (let ((many env2) (many sa) (many sty) (many s) (many sb) (many tty) (many t)) $ expect-proof6 env1 coercible-id "" p)
        (let ((many env3)) $ check (check env2 "sharing" sa fs) "sharing" sb fs)
        (let ((many env4)) $ check-sg env3 (sg-inst src $ entry-sg e) (term-res s sty) $ None _)
        (let ((many env5)) $ check-sg env4 (sg-inst tgt $ entry-sg e) (term-res t tty) $ None _)
        (tail $ coercible-ctor-args ew3 fuel sugar more env5 ctx rest (Cons _ s src) (Cons _ t tgt) c side))))

  ; match (sections 7, 21, 26): the scrutinee, its Matchable, the annotation, then one branch per
  ; constructor, each refined by its forced facts or refuted by them.
  ((many elab-match : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) args) (many (Env) env-in) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) (many (Bool) refute) (many (String) form) (many (Maybe $ Loc) final) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let ((unique ew1) (many envs) (many sx)) $ splice-tail ew env-in 3 args)
    (let-match many sx (None _)
      ((Some _ rr)
        (let-match many rr (Ok _ args2) ((Fail _ m) (expr-error ew1 ctx expect envs m "macro")))
        (let-match many fuel (Succ f2) ((Zero) (expr-error ew1 ctx expect envs "more than 10000 macro expansions" "macro")))
        (tail $ elab-match ew1 f2 (raws-size args2) args2 envs ctx expect tele demand refute form final)))
    (let ((many override)) $ env-sink env-in)
    (let ((many env)) $ match many override (((Env) _)) ((None _) env-in) ((Some _ _) (env-set-sink env-in $ None _)))
    (def-fns refusal-lvl $ (many bad : (unique (ElabWorld) ewb) -> (unique (ElabWorld) ewc at ewb) (many (Env) r) (many (List $ Res) rs) (many (Hoisted ctx expect) c))
      (expr-error ewb ctx expect env (sp-misuse env $ SpExpr $ ExMatch) "match"))
    (let-match many args (Cons _ mraw more) ((Nil _) (bad ew1)))
    (let-match many more (Cons _ scrut more2) ((Nil _) (bad ew1)))
    (let-match many more2 (Cons _ ann branches) ((Nil _) (bad ew1)))
    (let ((many pos)) $ pos-in env expect)
    (let ((many mloc)) $ env-loc env)
    (let ((many env0) (many sm)) $ mult-checked env mraw)
    (let ((many env0d)) $ written env0 pos sm "a `match`")
    (let ((many smult)) $ under pos sm)
    (let ((unique ew2) (many env2a) (many srs) (many sh) (erased lock)) $ notail $ elab-expr-demand ew1 fuel sugar scrut env0d ctx (Cons _ smult $ Nil _) no-tele (CCPlain) (Fixed _))
    (let-match many sh (MkHoisted _ _ sctx spre scode))
    (let ((many original)) $ first-res _ _ srs lock)
    (let ((many source-ctx)) sctx)
    (let ((many source-code)) (runtime-one _ smult scode))
    (let ((many env2a1) (many sres) (many saved)) (prepare-argument env2a smult original $ BTrue))
    (let ((many env2a2)) $ settled-from _ _ env2a1 source-code saved)
    (let ((many ctx4)) (Cons _ (Cons _ saved (Nil _)) source-ctx))
    (let ((many scode2)) (var-code env2a2 ctx4 saved))
    (let ((many env2b) (many found)) $ scrutinee-matchable env2a2 sres)
    (let-match many found (Some _ pr) ((None _) (values ew2 env2b (Nil _) $ hoist-none ctx expect $ CError _ expect "no head")))
    (let-match many pr (MkPair _ _ tid info))
    (let-match many info (MkMatchInfo mid disc mctors _))
    (let ((many ss)) $ shapes mctors env2b)
    (let ((many tagged)) $ tagged-of disc ss)
    (let ((many (Env) env2c))
      (match many (and (mult-is-many pos) $ mult-is-many smult) _
        ((BTrue) (use-entry (held-needs-many env2b tid mid) (Many) mid (BFalse)))
        ((BFalse) env2b)))
    (let ((erased outer-expect)) expect)
    (let ((unique ew3) (many env3w) (many ann-tele) (many inner-expect) (many bridge) (many atmatch))
      (match many refute (((ElabWorld) _ at ew2) ((Env) _) ((List $ Entry) _) ((List $ Multiplicity) i) ((DemandBridge expect i) _) ((Bool) _))
        ((BTrue) (values ew2 env2c (Nil _) expect (KeepDemand _) $ BFalse))
        ((BFalse) (notail $ result-tele ew2 fuel sugar ann env2c expect tele demand))))
    (let ((many env3b)) $ warn-match env3w (and (mult-is-many smult) $ not atmatch) tid)
    (let ((many expect2)) inner-expect)
    (let ((many extra)) (cells-allowed env3b mid $ BFalse))
    (let ((many incoming)) (env-uses env3b))
    (let ((many bsink)) $ match many override (((Sink) _))
      ((Some _ k) k)
      ((None _) (MkSink (str-cat "the enclosing " form) "return value" ann-tele (Nil _) (Cons _ (MkPair _ _ (loc-in env $ raw-pos ann) $ str-cat3 "the return annotation of the enclosing " form " is here") $ Nil _) (env-scope env3b) $ None _)))
    (let ((many remap)) $ not $ is-some _ override)
    (let ((unique ew4) (many env5) (many real) (many seen) (many deep)) $ notail $ elab-branches ew3 fuel sugar branches env3b ctx4 tid sres smult mctors ann-tele expect2 (Nil _) (Nil _) extra saved incoming incoming refute form bsink remap atmatch (Nil _))
    (let ((many env6)) $ check-coverage mctors env5 seen)
    (let ((many env6b) (many first) (many reachable) (many covered)) $ covered-of mctors env6 seen sres smult (None _) (BFalse) $ Nil _)
    (let ((unique ew5) (many env6l) (many dflt) (many deep2)) $ notail $ elab-else ew4 fuel sugar branches env6b ctx4 ann-tele expect2 first reachable (None _) (None _) sres smult extra saved incoming mctors refute form bsink remap atmatch seen deep)
    (let ((many env6c)) $ warn-lopsided env6l final deep2)
    (let ((many nreal)) $ nat-add (list-length _ real) $ match many dflt (((Nat) _)) ((None _) 0) ((Some _ _) 1))
    (let ((many env7)) $ match many (and (mult-is-many pos) $ and (not $ and atmatch $ mult-is-many smult) $ and (or (not tagged) $ not $ mult-is-many smult) $ nat-lt 1 nreal) (((Env) _))
      ((BTrue) (env-error-with env6c (forced-error mctors env6c sres smult (real-ctors _ _ real)) "a match without a runtime discriminant can have only one real branch"))
      ((BFalse) env6c))
    (let ((many live) (erased _)) $ list-append _ (discs-of (real-ctors _ _ real) ss) $ discs-of covered ss)
    (let ((many (Env) env7w))
      (match many (and (mult-is-many pos) $ and (not atmatch) $ and (not $ env-usage-erased env) $ and (nat-is-zero $ list-length _ real) $ not $ is-some _ dflt) _
        ((BTrue) (env-warn-at env7 mloc (say env7 "a non-erased `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function `absurd` instead")))
        ((BFalse) env7)))
    (let ((many (Code ctx4 expect2) code))
      (match many pos _
        ((Erased) (CErased _ expect2))
        (else
          (match many real (((Code ctx4 expect2) _))
            ((Nil _)
              (let-match many dflt (Some _ _) ((None _) (CAbsurd _ expect2)))
              (match many smult (((Code ctx4 expect2) _))
                ((Erased) (CMatch _ expect2 (CErased _ many-one) (ShNone _) (Nil _) dflt live))
                (else
                  (match many tagged (((Code ctx4 expect2) _))
                    ((BFalse) (CMatch _ expect2 scode2 (ShNone _) (Nil _) dflt live))
                    ((BTrue) (CMatch _ expect2 scode2 (match-shape env7 ctx4 mid tid disc ss) (Nil _) dflt live))))))
            ((Cons _ _ more3)
              (let-match many smult (Erased)
                (else (CMatch _ expect2 scode2 (match-shape env7 ctx4 mid tid disc ss) (real-branches-code _ _ real ss) dflt live)))
              (match many more3 (((Code ctx4 expect2) _))
                ((Nil _) (CMatch _ expect2 (CErased _ many-one) (ShNone _) (real-branches-code _ _ real ss) dflt live))
                ((Cons _ _ _) (CError _ expect2 "one real branch"))))))))
    (let ((many env8) (many rids) (erased _)) $ open-tele ann-tele env7w (Some _ $ anon-names ann-tele) (None _) (None _) (Nil _) $ BFalse)
    (let ((many env9) (many code2)) $ reconstruct ctx4 env8 expect2 ann-tele rids atmatch code)
    (values ew5 env9 (ress-of rids env9) $ MkHoisted _ _ sctx spre $ bridge-code _ outer-expect expect2 bridge (match many pos _ ((Erased) (CErased _ expect2)) (else (CLet source-ctx many-one expect2 (Cons _ saved (Nil _)) (PkMany _ (Nil _) saved (Nil _) (PkNil _)) source-code code2)))))

  ; A match's or open-absurd's return annotation: a telescope of the position's size, or _ for the enclosing one.
  ((many result-tele : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (Syn) ann) (many (Env) env) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (List $ Entry) t) (many (List $ Multiplicity) inner) (many (DemandBridge expect inner) bridge) (many (Bool) atmatch))
    (let ((unique ew1) (many (Env) env3) (many (List $ Entry) ann-tele) (many (Bool) atmatch))
      (match many (is-underscore ann) (((ElabWorld) _ at ew) ((Env) env3) ((List $ Entry) ann-tele) ((Bool) atmatch))
        ((BTrue)
          (let-match many tele (Some _ t) ((None _) (values ew (env-error env "no telescope to reuse for `_`") (Nil _) $ BFalse)))
          (match many (tele-has-meta t env) (((ElabWorld) _ at ew) ((Env) _) ((List $ Entry) t0) ((Bool) _))
            ((BTrue) (values ew (env-error env "the telescope `_` would reuse still has a `_` to infer") t $ BFalse))
            ((BFalse) (values ew env t $ BFalse))))
        ((BFalse)
          (let-match many (at-hole env ann) (None _)
            ((Some _ h) (values ew (error-at env (raw-pos h) "an at-match's annotation is written out; `_` cannot stand for it") (Nil $ Entry) $ BFalse)))
          (let-match many ann (RList _ items0) (else (values ew (env-error env $ str-cat "malformed match annotation" $ sp-hints env "annotation") (Nil $ Entry) $ BFalse)))
          ; an at-match's annotation is wrapped `(at <telescope>)` (section 40)
          (let ((many (List $ Syn) aitems) (erased (Subterm (List $ Syn) aitems (Syn) ann) pa) (many (Bool) atmatch))
            (match many items0 (((List $ Syn) aitems) ((Subterm (List $ Syn) aitems (Syn) ann) pa) ((Bool) atmatch))
              ((Cons _ a more)
                (let-match many more (Cons _ inner last) ((Nil _) (values items0 (prove-subterm items0 ann) $ BFalse)))
                (let-match many last (Nil _) ((Cons _ _ _) (values items0 (prove-subterm items0 ann) $ BFalse)))
                (let-match many inner (RList _ iitems) (else (values items0 (prove-subterm items0 ann) $ BFalse)))
                (match many (is-special env a $ SpMark $ MkAt) _
                  ((BTrue) (values iitems (prove-subterm iitems ann) $ BTrue))
                  ((BFalse) (values items0 (prove-subterm items0 ann) $ BFalse))))
              ((Nil _) (values items0 (prove-subterm items0 ann) $ BFalse))))
          (let-match many (first-atom aitems) (None _)
            ((Some _ a) (values ew (error-at env (raw-pos a) $ str-cat "expected a telescope or `_`, got " $ qraw a) (Nil $ Entry) $ BFalse)))
          (let ((unique ew2) (many env3) (many _) (many t)) $ notail $ elab-tele ew fuel sugar (subterm pa) aitems one-step (subs-all aitems) env (MMExpect expect) (Nil _) (BFalse) (BTrue) (BTrue) $ BFalse)
          (let ((many env3b)) $ env-restore env env3)
          (let ((many (Env) env3c))
            (match many tele _
              ((None _) env3b)
              ((Some _ et)
                (let-match many (nat-cmp (list-length _ et) $ list-length _ t) (CEq _ _ _)
                  (else env3b))
                (let ((many env3c) (many _)) $ solve-tele et t env3b $ BTrue)
                env3c)))
          (let ((many env3d)) $ settle-tele t env3c)
          (values ew2 env3d (metaless-tele t env3d) atmatch))))
    (let ((many (Env) env4) (many (List $ Entry) t) (many (List $ Multiplicity) inner) (many (DemandBridge expect inner) bridge))
      (match many (nat-cmp (list-length _ ann-tele) $ list-length _ expect) _
        ((CEq _ _ _) (finish-demand-tele expect demand env3 ann-tele))
        (else (finish-demand-tele expect demand (env-error env3 $ str-cat3 "match annotation has " (nat-str $ list-length _ ann-tele) $ str-cat " entries, position needs " $ nat-str $ list-length _ expect) ann-tele))))
    (let ((many env5)) $ refuse-when env4 (and atmatch $ has-runtime t) "an at-match's annotation entries are erased or `at`")
    (values ew1 env5 t inner bridge atmatch))

  ((many elab-branch-body : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm erased (Syn) braw) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) braw) p) (many (Env) env) (many (List $ List $ Nat) bctx) (many (List $ Multiplicity) ex) (many (List $ Entry) ann-tele) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (Code bctx ex) code))
    (let ((unique ew1) (many envb) (many ress) (many code) (erased _)) $ notail $ elab-body ew fuel sugar (subterm p) body body (WHere _) env bctx ex (Some _ ann-tele) $ None _)
    (values ew1 (check-results-count envb body ann-tele ress $ Nil _) code))

  ; [atmatch]: the branch of an at-match must erase to nothing, dispatch and loads included (section 40).
  ((many elab-pattern-body : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm erased (Syn) braw) (many (List $ Syn) body) (erased (Subterm (List $ Syn) body (Syn) braw) p) (many (Env) env) (many (List $ List $ Nat) bctx) (many (List $ Multiplicity) ex) (many (List $ Entry) ann-tele) (many (Nat) saved) (many (Maybe $ Nat) alias) (many (Maybe $ Sink) sink) (many (Bool) atmatch) (many (Spot) bpos) -> (unique (ElabWorld) ewr at ew) (many (Env) r) (many (Code bctx ex) code))
    (let ((many envs)) $ env-set-unwarned env $ or (env-unwarned env) atmatch)
    (let ((unique ew1) (many env3s) (many code))
      (match many alias (((ElabWorld) _ at ew) ((Env) _) ((Code bctx ex) _))
        ((None _)
          (let ((unique ew2) (many env2) (many ress) (many code) (erased _)) (notail $ elab-body ew fuel sugar (subterm p) body body (WHere _) envs bctx ex (Some _ ann-tele) sink))
          (values ew2 (check-results-count env2 body ann-tele ress (Nil _)) code))
        ((Some _ x)
          (let ((unique ew3) (many env2) (many ress) (many code) (erased _)) (notail $ elab-body ew fuel sugar (subterm p) body body (WHere _) envs (Cons _ (Cons _ x (Nil _)) bctx) ex (Some _ ann-tele) sink))
          (values ew3 (check-results-count env2 body ann-tele ress (Nil _)) (CLet _ many-one ex (Cons _ x (Nil _)) (PkMany _ (Nil _) x (Nil _) (PkNil _)) (var-code env bctx saved) code)))))
    (let ((many env3)) $ env-set-unwarned env3s $ env-unwarned env)
    (let ((many bad)) $ match many (and atmatch $ mult-is-many $ pos-in env ex) (((Bool) _)) ((BTrue) (not $ erases-to-nothing _ _ $ normalize bctx ex code)) ((BFalse) (BFalse)))
    (values ew1 (match many bad (((Env) _)) ((BFalse) env3) ((BTrue) (error-at env3 bpos $ say env3 "a branch of an at-match must erase to nothing, or to a reordering of variables; this one stores, allocates or calls"))) code))

  ; Each branch: present, refuted automatically with (absurd C), or absurd by proof (section 21).
  ((many elab-branches : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) branches) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) tid) (many (Res) sres) (many (Multiplicity) smult) (many (List $ MCtor) mctors) (many (List $ Entry) ann-tele) (many (List $ Multiplicity) expect) (many (List $ RealBranch ctx expect) acc) (many (List $ Nat) seen) (many (Bool) extra) (many (Nat) saved) (many (Uses) incoming) (many (Uses) joined) (many (Bool) refute) (many (String) form) (many (Sink) bsink) (many (Bool) remap) (many (Bool) atmatch) (many (List $ Maybe $ Nat) deep) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ RealBranch ctx expect) real) (many (List $ Nat) seen2) (many (List $ Maybe $ Nat) deep2))
    (let-match many branches (Cons _ braw brest) ((Nil _) (values ew (env-set-uses env joined) (list-rev _ acc) seen deep)))
    (let ((many envl)) (env-at (env-set-uses env $ uses-fork incoming) (raw-pos braw)))
    (let-match many (is-else-branch envl braw) (BFalse)
      ((BTrue) (tail $ elab-branches ew fuel sugar brest env ctx tid sres smult mctors ann-tele expect acc seen extra saved incoming joined refute form bsink remap atmatch deep)))
    (let-match many (branch-parts envl braw) (Some _ bp)
      ((None _) (tail $ elab-branches ew fuel sugar brest (env-back env $ env-error envl $ str-cat "malformed branch" $ sp-hints envl "branch") ctx tid sres smult mctors ann-tele expect acc seen extra saved incoming joined refute form bsink remap atmatch deep)))
    (let ((many (Syn) craw) (many (List $ Syn) fields) (many (Bool) refuted))
      (match many bp _
        ((BPresent _ c fs _ _) (values c fs (BFalse)))
        ((BRefuted _ c) (values c (Nil _) (BTrue)))
        ((BAbsurd _ c fs _ _) (values c fs (BFalse)))))
    (let ((many ppos)) $ pattern-pos envl braw)
    (let ((many env1) (many c)) (ctor-var (env-at envl ppos) craw))
    (let-match many (mctors-list mctors c) (BTrue)
      ((BFalse) (tail $ elab-branches ew fuel sugar brest (env-back env $ env-error-with env1 (declared-as env1 tid) $ str-cat3 (qshown env1 c) " is not a constructor of " $ qshown env1 tid) ctx tid sres smult mctors ann-tele expect acc seen extra saved incoming joined refute form bsink remap atmatch deep)))
    (let ((many env2)) $ env-back envl env1)
    (let ((many mk)) $ marker mctors c)
    (let ((many phantom)) (not $ mult-is-many mk))
    (let ((many cell-extra)) (or extra $ and phantom $ phantom-cells-allowed env2 tid))
    (let ((many ctele) (many ret)) (ctor-type env2 c))
    (let ((many mults)) (field-mults (tele-mults ctele) (match many phantom _ ((BTrue) (Erased)) ((BFalse) smult))))
    (let ((many (Env) env3) (many (List $ Syn) ordinary) (many (Maybe $ Syn) cellname))
      (match many refuted _ ((BTrue) (values env2 fields (None _))) ((BFalse) (pattern-fields env2 ppos (str-cat3 "a " form " branch") smult sres c ctele mults fields cell-extra))))
    (let ((many unreachable)) (and phantom $ mult-is-many smult))
    (let ((many ghost)) (or unreachable $ not $ mult-is-many $ pos-in env expect))
    (let ((many names)) (match many refuted (((List $ Maybe $ Name) _)) ((BTrue) (anon-names ctele)) ((BFalse) (raw-names ordinary))))
    (let ((many sites)) (match many refuted (((List $ Maybe $ Loc) _)) ((BTrue) (anon-sites ctele)) ((BFalse) (raw-sites ordinary env3))))
    (let ((many envb) (many fids) (many u)) (open-fields (env-set-run-pos env3 (BFalse)) ctele names sites (Some _ mults) sres c ret))
    (let ((many mfids)) (many-of mults fids))
    (let ((many bctx)) (Cons _ mfids ctx))
    (let ((unique ew1) (many (Env) env4) (many (List $ RealBranch ctx expect) acc2) (many (List $ Maybe $ Nat) deep2))
      (match many u (((ElabWorld) _ at ew) ((Env) env4) ((List $ RealBranch ctx expect) acc2) ((List $ Maybe $ Nat) deep2))
        ((UContra _)
          (match many refuted _
            ((BTrue) (values ew (env-discard env3 envb) acc deep))
            ((BFalse) (values ew (env-error (env-discard env3 envb) $ str-cat3 "branch " (qshown env3 c) (say envb " is refuted; omit it or write `absurd`")) acc deep))))
        ((UOk envb2)
          (let ((many envb2a) (many alias)) (pattern-cell-option envb2 (match many ghost _ ((BTrue) (Erased)) ((BFalse) smult)) sres c fids (and cell-extra $ not refuted) cellname))
          (let ((many envb2b)) (env-set-usage-erased envb2a (or ghost $ env-usage-erased envb2a)))
          (match many bp _
            ((BPresent _ _ _ body p)
              (let-match many refute (BFalse)
                ((BTrue) (values ew (env-error (env-discard env3 envb2b) (say envb2b "a branch of a refuting match is written `absurd`")) acc deep)))
              (let ((many deep3)) $ deepen envb2b body (match many unreachable _ ((BTrue) (None _)) ((BFalse) (Some _ c))) deep)
              (let ((many envb2r) (many bctx2) (many renames)) $ at-renames ctele fids (Nil _) envb2b bctx)
              (match many unreachable _
                ((BTrue)
                  (let ((unique ew2) (many envb3) (many _)) (notail $ elab-pattern-body ew fuel sugar braw body p envb2r bctx2 (all-erased expect) ann-tele saved alias (branch-sink bsink remap $ all-erased expect) atmatch ppos))
                  (values ew2 (env-discard env3 envb3) acc deep3))
                ((BFalse)
                  (let ((unique ew3) (many envb3) (many code)) (notail $ elab-pattern-body ew fuel sugar braw body p envb2r bctx2 expect ann-tele saved alias (branch-sink bsink remap expect) atmatch ppos))
                  (let ((many outer)) (env-discard env3 envb3))
                  (values ew3 (match many ghost _ ((BTrue) outer) ((BFalse) (env-set-uses outer $ env-uses envb3))) (Cons _ (MkRealBranch _ _ c mfids $ wrap-stmt _ _ expect renames code) acc) deep3))))
            ((BRefuted _ _) (values ew (env-error-with (env-discard env3 envb2b) (forced-notes env3 envb2 sres) $ str-cat3 "branch " (qshown env3 c) " is not refuted") acc deep))
            ((BAbsurd _ _ _ body p)
              (let ((erased q)) (subterm-trans p $ prove-subterm braw branches))
              (let ((many actx)) (match many alias (((List $ List $ Nat) _)) ((None _) bctx) ((Some _ x) (Cons _ (Cons _ x (Nil _)) bctx))))
              (let ((unique ew4) (many envb3)) (notail $ elab-refute ew fuel sugar (subterm q) body body (WHere _) envb2b actx))
              (values ew4 (env-discard env3 envb3) acc $ deepen envb2b body (None _) deep))))))
    (tail $ elab-branches ew1 fuel sugar brest (env-back env env4) ctx tid sres smult mctors ann-tele expect acc2 (Cons _ c seen) extra saved incoming (uses-join joined $ env-uses env4) refute form bsink remap atmatch deep2))

  ; The else branch (section 21): at most one, standing for at least one constructor, its body under no forced
  ; facts and erased throughout when none of them could run.
  ((many elab-else : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) branches) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) ann-tele) (many (List $ Multiplicity) expect) (many (Maybe $ Nat) first) (many (Bool) reachable) (many (Maybe $ Loc) seen-else) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) found) (many (Res) sres) (many (Multiplicity) smult) (many (Bool) extra) (many (Nat) saved) (many (Uses) incoming) (many (List $ MCtor) mctors) (many (Bool) refute) (many (String) form) (many (Sink) bsink) (many (Bool) remap) (many (Bool) atmatch) (many (List $ Nat) seen) (many (List $ Maybe $ Nat) deep) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) code) (many (List $ Maybe $ Nat) deep2))
    (match many branches _
      ((Nil _)
        (let-match many seen-else (None _)
          ((Some _ _) (values ew env found deep)))
        (match many first _ ((None _) (values ew env found deep)) ((Some _ _) (values ew (missing-branches mctors env sres smult seen form) found deep))))
      ((Cons _ braw brest)
        (let-match many (is-else-branch env braw) (BTrue)
          ((BFalse) (tail $ elab-else ew fuel sugar brest env ctx ann-tele expect first reachable seen-else found sres smult extra saved incoming mctors refute form bsink remap atmatch seen deep)))
        (let ((many envl)) (env-at (env-set-uses env $ uses-fork incoming) (raw-pos braw)))
        (let ((unique ew1) (many (Env) env2) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) found2) (many (List $ Maybe $ Nat) deep2))
          (match many refute (((ElabWorld) _ at ew) ((Env) env2) ((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) found2) ((List $ Maybe $ Nat) deep2))
            ((BTrue) (values ew (env-error envl (say envl "a refuting match has no `else`")) found deep))
            ((BFalse)
              (let-match many seen-else (None _)
                ((Some _ l)
                  (values ew (env-error-with envl (Cons _ (MkPair _ _ l (say envl "the first `else` branch")) $ Nil _) (say envl "a match has at most one `else` branch")) found deep)))
              (let-match many first (Some _ _) ((None _) (values ew (env-error envl (say envl "`else` covers no constructor")) found deep)))
              (let-match many (else-parts braw extra) (Some _ parts)
                ((None _) (values ew (env-error envl $ say envl "malformed `else` branch") found deep)))
              (let-match many parts (MkElseBody _ name body p))
              (let ((many live)) (and reachable $ mult-is-many $ pos-in env expect))
              (let ((many envb) (many alias)) (else-binder (env-set-run-pos envl (BFalse)) sres (match many live _ ((BTrue) smult) ((BFalse) (Erased))) extra name))
              (let ((many envb1)) (env-set-usage-erased envb (or (not live) $ env-usage-erased envb)))
              (let ((many deep3)) $ deepen envb1 body (None _) deep)
              (match many reachable _
                ((BTrue)
                  (let ((unique ew2) (many envb2) (many code)) (notail $ elab-pattern-body ew fuel sugar braw body p envb1 (Cons _ (Nil _) ctx) expect ann-tele saved alias (branch-sink bsink remap expect) atmatch $ raw-pos braw))
                  (let ((many outer)) (env-discard envl envb2))
                  (values ew2 (match many live _ ((BTrue) (env-set-uses outer $ env-uses envb2)) ((BFalse) outer)) (Some _ code) deep3))
                ((BFalse)
                  (let ((unique ew3) (many envb2) (many _)) (notail $ elab-pattern-body ew fuel sugar braw body p envb1 (Cons _ (Nil _) ctx) (all-erased expect) ann-tele saved alias (branch-sink bsink remap $ all-erased expect) atmatch $ raw-pos braw))
                  (values ew3 (env-discard envl envb2) (None _) deep3))))))
        (tail $ elab-else ew1 fuel sugar brest (env-set-uses (env-back env env2) (uses-join (env-uses env) (env-uses env2))) ctx ann-tele expect first reachable (Some _ $ env-loc envl) found2 sres smult extra saved incoming mctors refute form bsink remap atmatch seen deep2))))

  ; Arguments against a telescope, each at the position's multiplicity and checked against its entry
  ; (section 14); returns the terms innermost first and the code of the many ones in order.
  ; The arguments of an application against [tele] (DESIGN.md section 50): a meta stands for each parameter; an
  ; argument written `_` is left to it, and is an error unless erased where it stands; any other is checked
  ; against its parameter and bound to its meta, as a term where [as-term] (section 9's grammar) and as an
  ; expression otherwise. [result], over the metas, is solved against [expect] eagerly, where a `_` is present,
  ; before any argument is read, and again, reporting the mismatch, when a `_` would otherwise stay unsolved
  ; at the closing paren; every `_` is solved by then or refused. Returns the argument terms innermost first.
  ((many check-args : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Succ $ Zero) st) (many (Env) env) (many (Callee) callee) (many (List $ List $ Nat) ctx) (many (List $ Entry) tele) (many (Multiplicity) pos) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (Bool) as-term) (many (Bool) boundary) (many (Bool) prepare) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre) (many (List $ Code ctx2 many-one) codes))
    (let-match many st (SS _ k))
    (let ((many env1) (many metas) (erased lock)) $ open-tele tele env (Some _ $ anon-names tele) (Some _ $ wild-sites _ env args) (Some _ $ all-erased $ tele-mults tele) (Nil _) $ BTrue)
    (let ((many mvars)) $ tvars-rev metas $ Nil _)
    (let ((many wilds)) $ any-wild _ args)
    (let ((many env2)) $ solve-against env1 expect result mvars wilds $ BFalse)
    (let ((many fields)) (match many result (((Bool) _)) ((ARApp _ _) (BTrue)) ((ARCall _) (BFalse))))
    (let-match many (nat-eq (list-length _ tele) $ list-length _ args) (BTrue)
      ((BFalse) (let ((many errs)) $ count-errs tele) (values ew (count-mismatch env2 callee tele pos $ list-length _ args) errs errs ctx (SNone _) (Nil _))))
    (let ((many slotted)) $ match many result (((List $ Nat) _)) ((ARCall rets) (slot-named-params tele rets)) ((ARApp _ _) (Nil _)))
    (let ((unique ew1) (many env3) (many acc) (many tys) (many ctx2) (many pre) (many codes) (many ats)) $ notail $ check-args-go ew fuel sugar root args k env2 callee ctx ctx (SNone _) tele metas lock pos as-term prepare fields slotted (Nil _) (Nil _) (Nil _) (Nil _))
    (let ((many (Env) env4)) $ match many (and boundary $ terms-have-meta acc env3) _ ((BTrue) (solve-against env3 expect result mvars wilds $ BTrue)) ((BFalse) env3))
    (let ((many (Env) env5)) $ match many boundary _ ((BTrue) (report-unsolved (list-rev _ acc) (sub-raws _ args) tele callee env4 1)) ((BFalse) env4))
    (let ((many (Env) env6)) $ report-ats (list-rev _ ats) callee env5)
    (values ew1 env6 (metaless-list acc env6) (metaless-list tys env6) ctx2 pre codes))

  ((many check-args-go : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Zero) st) (many (Env) env) (many (Callee) callee) (many (List $ List $ Nat) ctx0) (many (List $ List $ Nat) ctx) (many (StmtCode ctx0 ctx) chain) (many (List $ Entry) tele) (many (List $ Nat) metas) (erased (Lockstep (Entry) (Nat) tele metas) lock) (many (Multiplicity) pos) (many (Bool) as-term) (many (Bool) prepare) (many (Bool) fields) (many (List $ Nat) slotted) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ Nat) ids) (many (List $ AtCheck) ats) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Term) acc2) (many (List $ Term) tys2) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx0 ctx2) pre2) (many (List $ Code ctx2 many-one) codes2) (many (List $ AtCheck) ats2))
    (match many tele _
      ((Nil _)
        (match many args _
          ((Nil _) (values ew env acc tys ctx chain (id-codes env ctx $ list-rev _ ids) ats))
          ((Cons _ _ _) (values ew (env-error env $ str-cat "expected fewer arguments, got " $ nat-str $ list-length _ args) acc tys ctx chain (id-codes env ctx $ list-rev _ ids) ats))))
      ((Cons _ e rest)
        (let-match many args (Cons _ s arest)
          ((Nil _) (values ew (env-error env $ str-cat "expected " $ str-cat (nat-str $ list-length _ tele) " more arguments, got 0") acc tys ctx chain (id-codes env ctx $ list-rev _ ids) ats)))
        (let-match erased lock (LsCons _ _ _ _ _ _ lp))
        (let-match many metas (Cons _ m mrest))
        (let-match many s (MkSub _ arg p))
        (let ((many mult)) (match many fields (((Multiplicity) _)) ((BTrue) (field-under pos (entry-mult e))) ((BFalse) (under pos (entry-mult e)))))
        (let ((many sg)) $ sg-inst acc $ entry-sg e)
        (def-fns msg-lvl $ (many arg-about : -> (many (String) pre) (many (List $ Pair (Loc) $ String) ns))
          (values (str-cat (argument-label callee (Succ $ list-length _ acc) $ entry-name e) ": ") $ callee-notes callee))
        (let ((many apos)) $ raw-pos arg)
        (match many (is-underscore arg) _
          ((BTrue)
            (let ((many (Env) env2) (many (Term) t))
              (match many (mult-is-many mult) _
                ((BTrue) (values (wild-error env apos arg-about "`_` stands only for an erased argument, and this one is not erased") $ TErr "wild"))
                ((BFalse) (match many (entry-place e) (((Env) _) ((Term) _))
                  ((None _) (values env $ TVar m))
                  ((Some _ _) (values (wild-error env apos arg-about "`_` cannot stand for an argument written `at`") $ TErr "wild"))))))
            (tail $ check-args-go ew fuel sugar root arest st env2 callee ctx0 ctx chain rest mrest lp pos as-term prepare fields slotted (Cons _ t acc) (Cons _ (type-of env2 m) tys) ids ats))
          ((BFalse)
            (let ((unique ew1) (many (Env) env2) (many (Res) rarg) (many (List $ List $ Nat) ctxa) (many (StmtCode ctx ctxa) prea) (many (Code ctxa (Cons (Multiplicity) mult (Nil (Multiplicity)))) code))
              (match many as-term (((ElabWorld) _ at ew) ((Env) env2) ((Res) rarg) ((List $ List $ Nat) ctxa) ((StmtCode ctx ctxa) prea) ((Code ctxa (Cons (Multiplicity) mult (Nil (Multiplicity)))) code))
                ((BTrue)
                  (let ((unique ew2) (many env2) (many t) (many ty)) $ notail $ elab-term ew fuel sugar (subterm p) arg env (BFalse) $ Some _ $ Cons _ (entry-with-sg e sg) $ Nil _)
                  (values ew2 env2 (term-res t ty) ctx (SNone _) $ CErased _ $ Cons _ mult $ Nil _))
                ((BFalse)
                  (let ((unique ew3) (many env2) (many rs) (many h) (erased lock3)) $ notail $ elab-expr-demand ew fuel sugar (subterm p) arg env ctx (Cons _ mult $ Nil _) (Some _ $ Cons _ (entry-with-sg e sg) $ Nil _) (CCPlain) (Fixed _))
                  (let-match many h (MkHoisted _ _ ctxa prea code))
                  (values ew3 env2 (first-res _ _ rs lock3) ctxa prea code))))
            (let ((many (Res) r)) $ match many (and (not $ is-some _ $ res-place rarg) $ or (is-some _ $ entry-place e) $ list-mem-bin slotted $ list-length _ acc) _
              ((BTrue) (MkRes (res-term rarg) (res-ty rarg) (res-erasure rarg) $ term-place env2 $ res-term rarg))
              ((BFalse) rarg))
            (let ((many env3)) $ env-back env2 $ check-sg-about (env-at env2 apos) sg r (Some _ arg) arg-about)
            (let ((many env4a) (many _)) $ solve-about (env-at env3 apos) "value" (res-term r) (TVar m) (BTrue) (None _) arg-about)
            (let ((many env4b)) $ match many (res-term r) (((Env) _))
              ((TVar y) (match many (is-meta env4a y) _ ((BTrue) env4a) ((BFalse) (slot-at env4a m (Succ m) (TSlotOf $ TVar y)))))
              (else env4a))
            (let ((many env4)) $ env-back env3 env4b)
            (let ((many env5a) (many r2) (many id) (many ctxb) (many scb))
              (match many (and prepare (mult-is-many mult)) (((Env) _) ((Res) r0) ((Nat) x0) ((List $ List $ Nat) cb) ((StmtCode ctxa cb) _))
                ((BTrue) (hoist-argument env4 ctxa mult mult r code))
                ((BFalse)
                  (let ((many is-var)) $ match many (res-term r) (((Bool) _)) ((TVar _) (BTrue)) (else (BFalse)))
                  (let-match many (and prepare $ and (not fields) $ and (not is-var) $ list-mem-bin slotted $ list-length _ acc) (BTrue)
                    ((BFalse) (values env4 r 0 ctxa $ SNone _)))
                  (let ((many env5) (many r3) (many x3)) (prepare-argument env4 (res-erasure r) r $ BFalse))
                  (values env5 r3 x3 ctxa $ SNone _))))
            ; an argument for a parameter written `at` must sit where its target does, in an erased position
            ; too, and is not passed (section 36)
            (let ((many (List $ AtCheck) ats2) (many (Bool) omitted))
              (match many (entry-place e) _
                ((None _) (values ats $ BFalse))
                ((Some _ pl) (values (Cons _ (MkAtCheck apos (Succ $ list-length _ acc) (entry-name e) (at-target env5a acc pl) $ res-place r2) ats) $ BTrue))))
            (let ((many ids2)) $ match many (or omitted $ not $ mult-is-many mult) (((List $ Nat) _)) ((BTrue) ids) ((BFalse) (Cons _ id ids)))
            (tail $ check-args-go ew1 fuel sugar root arest st env5a callee ctx0 ctxb (SSeq _ _ _ chain $ SSeq _ _ _ prea scb) rest mrest lp pos as-term prepare fields slotted
              (Cons _ (res-term r2) acc) (Cons _ (res-ty r2) tys) ids2 ats2))))))

  ; A function call (section 19): a lower-level call carries a Predates proof about the callee's level, a
  ; same-level call a Subterm proof for its decreasing argument; the top level carries neither (section 20).
  ((many elab-call : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm many (List $ Syn) rawargs) (subterm many (Pair (List $ Sub rawargs) $ Ann rawargs) parts) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (Res) callee) (many (Callee) desc) (many (Spot) hpos) (many (Multiplicity) pos) (many (Code ctx (Cons (Multiplicity) pos (Nil (Multiplicity)))) hcode) (many (Bool) uq) (many (Term) lv) (many (List $ Entry) params) (many (List $ Entry) rets) (many (CC) cc) (many (ExprDemand expect) demand) (many (Bool) assert-at) -> (unique (ElabWorld) ewr at ew)
      (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
    (let-match many parts (MkPair _ _ args ann))
    (let ((many mode)) $ under pos $ match many uq (((Multiplicity) _)) ((BTrue) (Once)) ((BFalse) (Many)))
    (let ((many env11)) $ match many (and assert-at $ not $ mult-is-many pos) (((Env) _))
      ((BTrue) (env-error env $ say env $ str-cat (tick $ spell env $ sp-name $ SpMark $ MkAt) " in an erased position"))
      ((BFalse) env))
    ; a call of an at-function is skipped (section 39): the proof opened for the callee is what licenses it
    (let ((many skipped)) $ and (mult-is-many pos) $ atfn-open env11 $ res-term callee)
    (let ((many env12)) $ match many (and assert-at $ not skipped) (((Env) _)) ((BTrue) (env-error-with env11 (head-notes env11 callee) $ str-cat (head-name env11 callee) $ say env11 " is not an at-function here: no `AtFn` proof for it is open")) ((BFalse) env11))
    (let ((many env13)) $ match many (and skipped $ not $ cc-eq cc $ CCPlain) (((Env) _)) ((BTrue) (env-error env12 $ str-cat3 (tick $ spell env12 $ match many cc (((String) _)) ((CCTail) "tail") ((CCNoTail) "notail") (else "delegate")) (say env12 " marks a call that compiles to one, and a call of at-function ") $ str-cat (head-name env12 callee) " is skipped")) ((BFalse) env12))
    (let ((many env13w)) $ match many (and (mult-is-many pos) $ not skipped) (((Env) _)) ((BTrue) (warn-use env13 (loc-in env13 hpos) "call of" $ res-term callee)) ((BFalse) env13))
    (let ((many erased-head)) $ and assert-at $ not uq)
    (let ((many bad-fn)) $ and (not erased-head) $ and (mult-is-many pos) $ not $ mult-is-many $ res-erasure callee)
    (let ((many bad-share)) $ and (not bad-fn) $ and uq $ and (mult-is-many pos) $ not $ mult-is-once $ res-erasure callee)
    (let ((many env14)) $ match many bad-fn (((Env) _)) ((BTrue) (env-error-with env13w (head-notes env13w callee) $ str-cat3 "erased function " (head-name env13w callee) " called in a non-erased position")) ((BFalse) env13w))
    (let ((many env0)) $ match many bad-share (((Env) _)) ((BTrue) (env-error-with env14 (head-notes env14 callee) $ str-cat3 (say env14 "a shared `UniqueFn` ") (head-name env14 callee) " is callable only erased")) ((BFalse) env14))
    (let ((many env1)) $ match many (res-term callee) (((Env) _)) ((TVar x2) (match many (or erased-head $ or bad-fn bad-share) (((Env) _)) ((BTrue) env0) ((BFalse) (use-entry env0 mode x2 $ BFalse)))) (else env0))
    (let ((many env1a) (many _) (many hid) (many ctx1) (many hsc)) $ match many erased-head (((Env) _) ((Res) _) ((Nat) _) ((List $ List $ Nat) c1) ((StmtCode ctx c1) _))
      ((BTrue) (hoist-argument env1 ctx (Erased) (Erased) callee $ CErased _ $ Cons _ (Erased) $ Nil _))
      ((BFalse) (hoist-argument env1 ctx mode pos callee hcode)))
    (let ((unique ew1) (many env2) (many acc) (many tys) (many ctx2) (many apre) (many actuals)) $ notail $ check-args ew fuel sugar rawargs args one-step env1a desc ctx1 params pos tele (ARCall rets) (BFalse) (BTrue) $ BTrue)
    (let ((many pre)) $ SSeq _ _ _ hsc apre)
    (let ((many arg-terms)) $ list-rev _ acc)
    (let ((unique ew2) (many envp)) $ notail $ check-call-proof ew1 fuel sugar rawargs ann env2 ctx callee desc (sub-positions _ args) lv params arg-terms $ list-rev _ tys)
    (let ((many env3)) $ unneeded _ ann env2 envp lv params arg-terms)
    (let ((many (CC) cc2))
      (match many (and (mult-is-many pos) $ and (cc-eq cc $ CCPlain) $ match many (env-level env3) (((Bool) _)) ((None _) (BFalse)) ((Some _ cur) (equal-env env3 lv $ TVar cur))) _
        ((BTrue) (CCSame (env-loc env) $ qshow env $ res-term callee))
        ((BFalse) cc)))
    (let ((many cid)) $ match many (res-term callee) (((Maybe $ Nat) _)) ((TVar cx) (Some _ cx)) (else (None _)))
    (call-returns ew2 env3 ctx ctx2 pre expect rets acc pos demand cid "this call" $ InvApp _ hid actuals cc2 skipped))

  ; The call-site proof (section 19), read against the current level and enclosing subterm parameters; a bare
  ; call gets its annotation from resolve-ann first.
  ((many check-call-proof : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (Nat) sugar) (subterm erased (List $ Syn) rawargs) (subterm many (Ann rawargs) ann) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Res) callee) (many (Callee) desc) (many (List $ Spot) sites) (many (Term) lv) (many (List $ Entry) params) (many (List $ Term) args) (many (List $ Term) arg-tys) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
    (match many (env-level env) _
      ((None _)
        (match many ann _
          ((AnnNone _) (values ew env)) (else (values ew (env-error env "the top level calls without proofs; drop the decrease annotation (section 20)")))))
      ((Some _ cur)
        (let ((many same)) $ equal-env env lv $ TVar cur)
        (let ((many positions)) $ subterm-indices params 0)
        (let ((many env1) (many ann2)) $ resolve-ann env _ ann callee same positions args)
        (match many ann2 _
          ((AnnNone _) (values ew env1))
          ((AnnSubterm _ ap i g)
            (let-match many same (BTrue) ((BFalse) (values ew (env-error env1 $ annotation-kind env1 callee same))))
            (let-match many (index-of-nat positions i 0) (Some _ kk)
              ((None _) (values ew (not-subterm-param env1 ap desc params sites positions i))))
            (let ((many env2)) $ check-earlier positions env1 args 0 kk ap desc params)
            (let-match many (list-nth _ (env-subterms env2) kk) (NthHit _ _ _ counterpart _)
              ((NthMiss _ _ _ _) (values ew (no-counterpart env2 ap desc params i kk))))
            (let ((many arg)) $ nth-term args i)
            (let ((unique ew1) (many (Env) env3) (many (Res) pres))
              (match many g (((ElabWorld) _ at ew) ((Env) env3) ((Res) pres))
                ((Inferred _) (let ((many ewt1) (many ewt2)) (mint-subterm env2 arg (nth-term arg-tys i) (TVar counterpart) $ type-of env2 counterpart)) (values ew ewt1 ewt2))
                ((Written _ p pp)
                  (let ((unique ew2) (many env3) (many prs) (many _) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar (subterm pp) p env2 ctx erased-one no-tele (CCPlain) (Fixed _))
                  (values ew2 env3 $ erased-res prs lock))))
            (let ((many env4) (many _) (many s1) (many _) (many s3)) $ expect-proof4 env3 subterm-id " or `_`" pres)
            (let ((many env5)) $ check env4 "value" s1 arg)
            (values ew1 (check env5 "value" s3 $ TVar counterpart)))
          ((AnnPredates _ _ g)
            (let-match many same (BFalse) ((BTrue) (values ew (env-error env1 $ annotation-kind env1 callee same))))
            (let ((unique ew3) (many (Env) env2) (many (Res) pres))
              (match many g (((ElabWorld) _ at ew) ((Env) env2) ((Res) pres))
                ((Inferred _)
                  (def-fns msg-lvl $ (many not-variable : -> (many (Env) e) (many (Res) r))
                    (values (env-error env1 $ str-cat (qshow env1 lv) " is not a variable") $ MkRes (TErr "level") (TErr "level") (Erased) $ None _))
                  (match many (canon-env env1 lv) (((ElabWorld) _ at ew) ((Env) _) ((Res) r0))
                    ((TVar m) (let ((many ewt3) (many ewt4)) (mint-predates env1 m cur)) (values ew ewt3 ewt4))
                    ((TErr m) (values ew (env-error env1 m) $ MkRes (TErr m) (TErr m) (Erased) $ None _)) (else (let ((many ewt5) (many ewt6)) (not-variable)) (values ew ewt5 ewt6))))
                ((Written _ p pp)
                  (let ((unique ew4) (many env2) (many prs) (many _) (erased lock)) $ notail $ elab-expr-demand ew fuel sugar (subterm pp) p env1 ctx erased-one no-tele (CCPlain) (Fixed _))
                  (values ew4 env2 $ erased-res prs lock))))
            (let ((many env3) (many _) (many p1) (many p2)) $ expect-proof3 env2 predates-id " or `_`" pres)
            (let ((many env4)) $ check env3 "value" p2 $ TVar cur)
            (def-fns msg-lvl $ (many msg-level : -> (many (String) s)) (str-cat3 (qshow env4 $ res-term pres) " : " $ str-cat3 (qshow env4 $ res-ty pres) " does not relate the callee's level " $ qshow env4 lv))
            (values ew3 (error-unless-msg env4 (equal-env env4 p1 lv) msg-level))))))))

(def-fns _ $ (many elab-expr : (unique (ElabWorld) ew) (many (Nat) fuel) (many (Nat) sugar) (many (Syn) raw) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) -> (unique (ElabWorld) ewr at ew)
    (many (Env) r) (many (List $ Res) ress) (many (Hoisted ctx expect) code) (erased (Lockstep (Multiplicity) (Res) expect ress) lock))
  (elab-expr-demand ew fuel sugar raw env ctx expect tele cc (Fixed _)))

; ---- The top level (section 27): statements run as they are elaborated, the final expression consumed;
; every form but the last must be a statement.

(def-fns _ $ (many pragma-of : (many (Syn) raw) -> (many (Maybe $ List $ Syn) r))
  (let-match many raw (RList _ items) (else (None _)))
  (let-match many items (Cons _ h rest)
    ((Nil _) (None _)))
  (let-match many h (RAtom _ hn) (else (None _)))
  (let-match many hn (NSrc w) (else (None _)))
  (match many (str-eq w ";!") _ ((BTrue) (Some _ rest)) ((BFalse) (None _))))

(def-fns _ $ (many pragma-warn : (many (Env) env) (many (Spot) l) (many (Syn) nraw) (many (Syn) mraw) -> (many (Env) r))
  (let-match many nraw (RAtom nl n) (else env))
  (let-match many mraw (RAtom _ mname) (else env))
  (let-match many mname (NSrc msg) (else env))
  (let-match many (lookup env n) (Some _ x)
    ((None _) (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick $ spell-name n) $ str-cat ", which is not in scope" $ hint env n)))
  (let-match many (canon-env env $ TVar x) (TVar c)
    (else (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick $ spell-name n) ", which is neither a constructor nor a function")))
  (let-match many (match many (canon-env env $ type-of env x) (((Bool) _)) ((TTyCtor _) (BTrue)) ((TValCtor _ _) (BTrue)) ((TFn _ _ _ _) (BTrue)) (else (BFalse))) (BTrue)
    ((BFalse) (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick $ spell-name n) ", which is neither a constructor nor a function")))
  (let-match many (warned-find (env-warned env) c) (Some _ w)
    ((None _) (env-set-warned env $ Cons _ (MkWarned c (loc-in env l) msg) $ env-warned env)))
  (match many w _ ((MkWarned _ pl _) (env-error-with env (Cons _ (MkPair _ _ pl "the first is here") $ Nil _) $ str-cat "second `;! warn` for " $ tick $ spell-name n))))

(def-fns _ $ (many pragma : (many (Env) env) (many (Spot) l) (many (List $ Syn) words) -> (many (Env) r))
  (let-match many (match many words (((List $ Syn) _)) ((Cons _ _ rest) rest) ((Nil _) words)) (Cons _ nraw more)
    ((Nil _) (env-error env "`;! warn` needs a name and a message")))
  (match many more _
    ((Nil _) (env-error env "`;! warn` needs a message after the name"))
    ((Cons _ mraw _) (pragma-warn env l nraw mraw))))

(def-fns _ $ (many sweep-regions : (many (Env) env) (subterm many (List $ Region) rs) (many (List $ Nat) used) -> (many (Env) r))
  (let-match many rs (Cons _ r rest) ((Nil _) env))
  (match many r _ ((MkRegion k n from _)
    (tail $ sweep-regions
      (match many (list-mem-bin used k) (((Env) _))
        ((BTrue) env)
        ((BFalse) (env-back env $ env-warn-at env (loc-in env from) $ str-cat3 "`;! suppress warn` for " (tick-name $ NSrc n) " silenced nothing")))
      rest used))))

(def-fns _ $ (many end-file : (many (Env) env0) -> (many (Env) r))
  (let ((many env)) $ report-shadows env0 $ BFalse)
  (let ((many swept)) $ match many (env-failed env) (((Env) _))
    ((BFalse) (sweep-regions env (env-regions env) $ env-silenced env))
    ((BTrue) env))
  (env-set-regions (env-set-said swept $ said-without-silenced $ env-said swept) $ Nil _))

; ---- Finals (lib/elab.ml's final_form): what the driver does with a file's final value

(def-adts $ (FinalKind : -> Type)
  enum
  (many FMain : -> (FinalKind))
  (many FProgram : -> (FinalKind))
  (many FThunk : (many (Term) ty) -> (FinalKind))
  (many FPlain : -> (FinalKind)))

(def-fns _ $ (many bare-final-entry : (many (Env) env) (many (Bool) string) (many (Entry) e) -> (many (Bool) b))
  (let-match many e (MkEntry _ st m sg place _))
  (let-match many st (BFalse) ((BTrue) (BFalse)))
  (let-match many place (None _) ((Some _ _) (BFalse)))
  (let-match many sg (SgTy t) ((SgIs _ _) (BFalse)))
  (let-match many m (Many) (else (BFalse)))
  (match many string _ ((BTrue) (prelude-nullary env t "String")) ((BFalse) (BTrue))))

(def-fns _ $ (many final-form : (many (Env) env) (many (Term) ty) -> (many (Maybe $ FinalKind) f))
  (let-match many (canon-env env ty) (TFn uq _ ps rs)
    (else (Some _ $ match many (prelude-nullary env ty "Program") _ ((BTrue) (FProgram)) ((BFalse) (FPlain)))))
  (let-match many uq (BFalse) ((BTrue) (None _)))
  (let-match many rs (Cons _ r more) ((Nil _) (None _)))
  (let-match many more (Nil _) ((Cons _ _ _) (None _)))
  (match many ps _
    ((Nil _) (match many (bare-final-entry env (BFalse) r) _ ((BTrue) (Some _ $ FThunk $ sg-term $ entry-sg r)) ((BFalse) (None _))))
    ((Cons _ p more2)
      (match many (and (list-is-empty _ more2) $ and (bare-final-entry env (BTrue) p) $ bare-final-entry env (BTrue) r) _
        ((BTrue) (Some _ $ FMain))
        ((BFalse) (None _))))))

(def-fns _ $ (many classify-final : (many (Env) env) (many (Term) ty) -> (many (FinalKind) f))
  (match many (final-form env ty) _ ((Some _ k) k) ((None _) (FPlain))))

(def-lvl BINDER-CMP)

(def-fns BINDER-CMP $ (many binder-le : (many (Pair (Nat) $ Tracked) a) (many (Pair (Nat) $ Tracked) b) -> (many (Bool) r))
  (let-match many a (MkPair _ _ x ta))
  (let-match many b (MkPair _ _ y tb))
  (let-match many ta (MkTracked la _ _ _ _))
  (let-match many tb (MkTracked lb _ _ _ _))
  (let-match many (loc-place la) (Some _ pa) ((None _) (BTrue)))
  (let-match many (loc-place lb) (Some _ pb) ((None _) (BTrue)))
  (let-match many pa (MkPair _ _ fa ca))
  (let-match many pb (MkPair _ _ fb cb))
  (let-match many ca (MkPair _ _ linea cola))
  (let-match many cb (MkPair _ _ lineb colb))
  (match many (str-cmp fa fb) _
    ((CLt _ _ _ _ _) (BTrue))
    ((CGt _ _ _ _ _) (BFalse))
    (else (or (nat-lt linea lineb) $ and (nat-eq linea lineb) $ or (nat-lt cola colb) $ and (nat-eq cola colb) $ not $ nat-lt y x))))

(let ((erased BINDER-SORT-L) (many binder-sort)) (sort-factory BINDER-CMP))

(def-fns _ $ (many let-deletable : (many (Nat) g) (subterm many (List $ Pair (Nat) $ Tracked) bs) (many (IdMap $ RefState) rf) -> (many (Bool) r))
  (let-match many bs (Cons _ b rest) ((Nil _) (BTrue)))
  (let-match many b (MkPair _ _ x t))
  (let-match many t (MkTracked _ _ kind _ _))
  (let-match many kind (BLet g2 _) (else (tail $ let-deletable g rest rf)))
  (let-match many (nat-eq g g2) (BTrue) ((BFalse) (tail $ let-deletable g rest rf)))
  (match many (nat-eq (ref-level rf x) 0) _ ((BFalse) (BFalse)) ((BTrue) (tail $ let-deletable g rest rf))))

(def-fns _ $ (many unused-text : (many (Env) env) (many (Nat) x) (many (Tracked) t) (many (List $ Pair (Nat) $ Tracked) all) (many (IdMap $ RefState) rf) -> (many (Maybe $ String) r))
  (let-match many t (MkTracked _ n kind m scope-erased))
  (let-match many n (NSrc s) (else (None _)))
  (let-match many (str-starts "_" s) (BFalse) ((BTrue) (None _)))
  (let ((many name)) $ tick-name n)
  (let ((many renamed)) $ tick-name $ NSrc $ str-cat "_" s)
  (let ((many level)) $ ref-level rf x)
  (let-match many (nat-eq level 0) (BFalse)
    ((BTrue)
      (Some _ $ str-cat3 "unused " name $ match many kind (((String) _))
        ((BLet g one-form) (match many (and one-form $ let-deletable g all rf) (((String) _)) ((BTrue) (say env "; delete its `let`")) ((BFalse) (say env "; write `_` in its place"))))
        ((BField) (say env "; write `_` in its place"))
        ((BParam) (str-cat "; rename it " renamed))
        (else "; delete it"))))
  (let-match many (or (nat-eq level 2) $ or scope-erased $ not $ mult-is-many m) (BFalse) ((BTrue) (None _)))
  (match many kind _
    ((BLet _ _) (Some _ $ str-cat name $ say env " is referenced only in erased positions; declare it `erased`"))
    ((BParam) (Some _ $ str-cat3 name (say env " is referenced only in erased positions; declare it `erased`, or rename it ") renamed))
    (else (None _))))

(def-fns _ $ (many warn-unused : (many (Env) env) (subterm many (List $ Pair (Nat) $ Tracked) bs) (many (List $ Pair (Nat) $ Tracked) all) (many (IdMap $ RefState) rf) -> (many (Env) r))
  (let-match many bs (Cons _ b rest) ((Nil _) env))
  (let-match many b (MkPair _ _ x t))
  (let-match many t (MkTracked l n _ _ _))
  (let ((many top)) $ match many (lookup env n) (((Bool) _)) ((Some _ y) (nat-eq x y)) ((None _) (BFalse)))
  (let ((many text)) $ match many top (((Maybe $ String) _)) ((BTrue) (None _)) ((BFalse) (unused-text env x t all rf)))
  (tail $ warn-unused (match many text (((Env) _)) ((Some _ s) (env-warn-at env l s)) ((None _) env)) rest all rf))

(def-fns _ $ (many report-unused : (many (Env) env) -> (many (Env) r))
  (let-match many (env-tracking env) (MkTracking on bs rf))
  (let-match many on (BTrue) ((BFalse) env))
  (let ((many env1)) $ env-set-warn-unused env (BTrue))
  (let-match many (env-failed env1) (BFalse) ((BTrue) env1))
  (let ((many all)) $ idmap-pairs _ bs 1 0 $ Nil _)
  (warn-unused env1 (binder-sort (Pair (Nat) $ Tracked) binder-le all) all rf))

(def-fns _ $ (many discharge : (unique (ElabWorld) ew) (many (Syn) item) (many (Env) env) (many (Bool) last) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
  (let-match many (env-goals env) (MkGoals mode gat m t report _))
  (let-match many mode (GoalProved) (else (values ew (env-error env $ say env "under `--goal open` no file ends in an expression"))))
  (let-match many last (BTrue) ((BFalse) (values ew (env-error env $ say env "under `--goal proved` only the last file ends in an expression"))))
  (let-match many gat (Some _ site) ((None _) (values ew (env-error env $ say env "under `--goal proved` the final expression discharges a `goal`, and none is set"))))
  (let ((many tele)) $ Cons _ (MkEntry (None _) (BFalse) m (SgTy t) (None _) (Some _ site)) $ Nil _)
  (let ((many sink)) $ MkSink "the goal" "value" tele (Nil _) (Cons _ (MkPair _ _ site "the goal is set here") $ Nil _) (env-scope env) $ None _)
  (let ((unique ew1) (many env1) (many ress) (many _) (erased _)) $ elab-expr-demand ew expansion-limit (raw-size item) item (env-set-final $ env-set-sink env $ Some _ sink) (Nil _) (Cons _ m $ Nil _) (Some _ tele) (CCPlain) (Fixed _))
  (let ((many env2)) $ check-results-count env1 (Cons _ item $ Nil _) tele ress (Nil _))
  (values ew1 (report-unused $ env-set-goals env2 $ MkGoals mode gat m t report $ BTrue)))

(def-fns _ $ (many close-goal : (many (Env) env) (many (String) path) -> (many (Env) r))
  (let-match many (env-goals env) (MkGoals mode gat _ _ report discharged))
  (let ((many flag)) $ match many mode (((String) _)) ((GoalProved) "`--goal proved`") (else "`--goal open`"))
  (let-match many mode (GoalUnrequired) (else
    (let-match many gat (Some _ site) ((None _) (env-fail env $ str-cat3 path ": error: under " $ str-cat flag " a file sets a `goal`, and none does")))
    (let-match many mode (GoalProved) (else env))
    (let-match many discharged (BTrue) ((BFalse) (env-error (env-at-loc env site) $ say env "the goal is not discharged: under `--goal proved` the last file ends in an expression that proves it")))
    (env-set-said env $ Cons _ (SaidNote site report) $ env-said env)))
  env)

(def-fns _ $ (many run-toplevel : (unique (ElabWorld) ew) (subterm many (Nat) fuel) (subterm many (List $ Syn) items) (many (Nat) expanded) (many (Bool) loading) (many (Bool) last) (many (Env) envi) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
  (let ((many env0)) $ match many loading (((Env) _)) ((BTrue) (env-set-prelude envi $ env-scope envi)) ((BFalse) envi))
  (let-match many items (Cons _ item0 rest) ((Nil _) (values ew env0)))
  (let ((many after)) $ match many expanded (((Nat) _)) ((Zero) (Zero)) ((Succ k) k))
  (let-match many (pragma-of item0) (None _)
    ((Some _ words) (tail $ run-toplevel ew fuel rest after loading last $ pragma (env-at env0 $ raw-pos item0) (raw-pos item0) words)))
  (let ((many env) (many item)) $ match many expanded (((Env) _) ((Syn) _)) ((Zero) (syn-interned env0 item0)) ((Succ _) (values env0 item0)))
  (let ((unique ew1) (many envm) (many mx)) $ expand ew (env-at env $ raw-pos item) item)
  (let-match many mx (None _)
    ((Some _ me)
      (let-match many me (Spliced out) ((Refused m) (values ew1 (env-error envm m))))
      (let-match many fuel (Succ f2) ((Zero) (values ew1 (env-error envm "more than 10000 macro expansions"))))
      (let ((many all) (erased _)) $ list-append _ out rest)
      (tail $ run-toplevel ew1 f2 all (nat-add (list-length _ out) after) loading last envm)))
  (let ((unique ew2) (many envs) (many settled) (many _) (many _)) $ settle-item ew1 expansion-limit (raw-size item) item (env-at env $ raw-pos item) (Nil _) (Many))
  (let-match many settled (None _)
    ((Some _ item2)
      (let-match many fuel (Succ f2) ((Zero) (values ew2 (env-error envs "more than 10000 macro expansions"))))
      (tail $ run-toplevel ew2 f2 (Cons _ item2 rest) expanded loading last envs)))
  (let ((many env2)) $ env-set-warn-unused (env-at env $ raw-pos item) $ env-warn-unused env)
  (match many (or (is-statement env2 item) $ not $ list-is-empty _ rest) _
    ((BTrue)
      (let ((unique ew3) (many env3) (many _) (many _)) $ elab-stmt ew2 expansion-limit (raw-size item) item env2 (Nil _) (Many) "top-level form")
      (tail $ run-toplevel ew3 fuel rest after loading last $ report-unused env3))
    ((BFalse)
      (let-match many (misplaced env2 item) (None _) ((Some _ _) (values ew2 (env-error env2 $ not-a env2 "neither a statement nor an expression" item))))
      (let-match many (env-goals env2) (MkGoals gmode _ _ _ _ _))
      (let-match many gmode (GoalUnrequired) (else (tail $ discharge ew2 item env2 last)))
      (let ((unique ew4) (many env3a) (many ress) (many h) (erased lock)) $ elab-expr-demand ew2 expansion-limit (raw-size item) item env2 (Nil _) many-one no-tele (CCPlain) (FinalDemand))
      (let ((many env3)) $ settle-res env3a $ first-res _ _ ress lock)
      (let-match many (env-failed env3) (BFalse) ((BTrue) (values ew4 env3)))
      (let ((many ty)) $ res-ty $ first-res _ _ ress lock)
      (match many (final-form env3 ty) _
        ((None _) (values ew4 (env-error env3 $ str-cat "a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`; this one is " $ qshow env3 ty)))
        ((Some _ _) (values ew4 (env-run-final (report-unused env3) (hoisted-code _ many-one h) ty)))))))
