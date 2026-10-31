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
      (let-match erased pf (PoErased _ _ q))
      (let-match erased q (PoNil))
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
  (let ((many index)) $ match many b2 (((Maybe $ Nat) _)) ((BTag _ ct _) (Some _ $ ctor-index ct)) (else (word-of-block _ b2)))
  (let-match many index (Some _ i) ((None _) (None $ Sp)))
  (let ((erased _) (many s)) $ entry-state env x)
  (let-match many s (SSettled _ _ m) ((SHypothetical _) (None _)))
  (let-match many (and (mult-is-many $ entry-mult-of env x) $ term-eq (minted-type env m) special-term) (BTrue)
    ((BFalse) (None _)))
  (sp-of-index i))

(def-fns _ $ (many special-of-atom : (many (Env) env) (many (Syn) raw) -> (many (Maybe $ Sp) r))
  (let-match many (raw-atom raw) (Some _ n) ((None _) (None _)))
  (let-match many (lookup env n) (Some _ x) ((None _) (None _)))
  (let-match many n (NHandle _ _ m _) (else (special-of-entry env x)))
  (match many (mult-is-many m) _ ((BTrue) (special-of-entry env x)) ((BFalse) (None _))))

(def-fns _ $ (many held-key : (many (Env) env) (many (Maybe $ Nat) except) (many (Nat) x) -> (many (Maybe $ String) r))
  (let-match many (special-of-entry env x) (None _) ((Some _ sp) (Some _ $ sp-name sp)))
  (let-match many (match many except (((Bool) _)) ((None _) (BTrue)) ((Some _ e) (not $ nat-eqb e x))) (BTrue) ((BFalse) (None _)))
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
  (let-match many (or (char-eqb c #\`) $ or (char-eqb c #\space) $ or (char-eqb c #\x28) $ or (char-eqb c #\x29) $ char-eqb c #\newline) (BTrue)
    ((BFalse) (tail $ respell-scan kws code rest quoted (rcat tok $ RChar c) out)))
  (let ((many q2)) $ match many (and (char-eqb c #\`) $ not code) (((Bool) _)) ((BTrue) (not quoted)) ((BFalse) quoted))
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
  (let-match many l (MkLitEntry x _ lit _ _))
  (let-match many lit (Some _ r) ((None _) more))
  (match many r _
    ((RString _ _) more)
    (else (Cons _ (MkPair _ _ (canon-env env $ TVar x) l) more))))

; An atom is shown by the best of the entries equal to it that a reader can name where the message is: a
; numeral or string literal, by its spelling, else the newest binding the scope still names, else its id. What
; canonicalization picks to represent a class is an accident of minting order, so it does not decide the name
; (lib/env.ml's show). A candidate is the atom it would name, its entry, and the name.
(def-fns _ $ (many cand-of : (many (Env) env) (many (List $ Nat) atoms) (many (Nat) x) (many (Shown) n) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let ((many (Maybe $ Nat) canonical)) $ match many (canon-env env $ TVar x) _ ((TVar a) (match many (list-mem-bin atoms a) _ ((BTrue) (Some _ a)) ((BFalse) (None _)))) (else (None _)))
  (let-match many canonical (None _)
    ((Some _ a) (Cons _ (MkPair _ _ a $ MkPair _ _ x $ shown-text n) acc)))
  (match many (list-mem-bin atoms x) _ ((BTrue) (Cons _ (MkPair _ _ x $ MkPair _ _ x $ shown-text n) acc)) ((BFalse) acc)))

(def-fns _ $ (many name-cands : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) (subterm many (List $ Pair (Name) (Nat)) ns) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ns (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ n x))
  (let ((many (Bool) skip)) $ match many except _ ((None _) (BFalse)) ((Some _ e) (nat-eqb e x)))
  (tail $ name-cands env atoms except rest $ match many skip (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) acc) ((BFalse) (cand-of env atoms x (ShText $ spell-name n) acc))))

(def-fns _ $ (many names-lit : (many (Syn) r) -> (many (Bool) b))
  (match many r _ ((RChr _ _) (BFalse)) (else (BTrue))))

(def-fns _ $ (many lit-cands : (many (Env) env) (many (List $ Nat) atoms) (subterm many (List $ LitEntry) ls) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) acc))
  (let-match many l (MkLitEntry x _ lit _ _))
  (let-match many lit (Some _ r) ((None _) (tail $ lit-cands env atoms rest acc)))
  (tail $ lit-cands env atoms rest $ match many (names-lit r) (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) (cand-of env atoms x (syn-shown r) acc)) ((BFalse) acc)))

(def-fns _ $ (many best-cand : (many (Nat) a) (subterm many (List $ Pair (Nat) $ Pair (Nat) (String)) cs) (many (Maybe $ Pair (Nat) (String)) best) -> (many (Maybe $ Pair (Nat) (String)) r))
  (let-match many cs (Cons _ c rest) ((Nil _) best))
  (let-match many c (MkPair _ _ a2 xn))
  (let-match many xn (MkPair _ _ x _))
  (let ((many (Bool) newer)) $ match many best (((Bool) _)) ((None _) (BTrue)) ((Some _ b) (match many b _ ((MkPair _ _ y _) (nat-lt y x)))))
  (tail $ best-cand a rest $ match many (and (nat-eqb a a2) newer) (((Maybe $ Pair (Nat) (String)) _)) ((BTrue) (Some _ xn)) ((BFalse) best)))

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
  (let ((many (Bool) skip)) $ match many except _ ((None _) (BFalse)) ((Some _ e) (nat-eqb e x)))
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
  (let-match many (and (term-eq h $ TVar ctor) $ nat-eqb (list-length _ args) arity) (BTrue) ((BFalse) (None _)))
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
  (let ((many (Bool) skip)) $ match many except (((Bool) _)) ((None _) (BFalse)) ((Some _ e) (nat-eqb e x)))
  (let-match many skip (BFalse) ((BTrue) (tail $ slot-cands env kws except rest acc)))
  (tail $ slot-cands env kws except rest $ match many (canon-env env $ slot-atom x) (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((TVar a) (Cons _ (MkPair _ _ a $ MkPair _ _ x $ fetch-form kws "slot-of" $ spell-name n) acc))
    (else acc)))

(def-fns _ $ (many lit-fetch-cand : (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Nat) atoms) (many (Maybe $ Nat) canonical) (many (Nat) x) (many (String) head) (many (Syn) r) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) out))
  (let-match many canonical (Some _ a) ((None _) acc))
  (match many (list-mem-bin atoms a) _ ((BTrue) (Cons _ (MkPair _ _ a $ MkPair _ _ x $ fetch-form kws head $ shown-text $ syn-shown r) acc)) ((BFalse) acc)))

(def-fns _ $ (many lit-fetch-cands : (many (Env) env) (many (List $ Pair (String) $ Pair (Nat) (String)) kws) (many (List $ Nat) atoms) (subterm many (List $ LitEntry) ls) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let-match many ls (Cons _ l rest) ((Nil _) acc))
  (let-match many l (MkLitEntry x proof lit _ _))
  (let-match many lit (Some _ r) ((None _) (tail $ lit-fetch-cands env kws atoms rest acc)))
  (let ((many acc2)) $ lit-fetch-cand kws atoms (match many (canon-env env $ slot-atom x) (((Maybe $ Nat) _)) ((TVar a) (Some _ a)) (else (None _))) x "slot-of" r acc)
  (tail $ lit-fetch-cands env kws atoms rest $ match many proof (((List $ Pair (Nat) $ Pair (Nat) (String)) _))
    ((Some _ p) (lit-fetch-cand kws atoms (canon-id env p) p "numeral-of" r acc2))
    ((None _) acc2)))

(def-fns _ $ (many fetch-cands : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let ((many kws)) $ kws-of env)
  (let ((many named)) $ named-cands env except (name-index-entries _ $ scope-names $ env-scope env) $ Nil _)
  (level-cands env kws named $ slot-cands env kws except (name-index-entries _ $ scope-names $ env-scope env) $ matchable-cands env kws named (env-opens env) $ proof-cands env kws named delegate-id 6 2 "delegate-of" (env-objects env) (Nil _) $ proof-cands env kws named atfn-id 2 1 "at-fn-of" (env-objects env) (Nil _) $ lit-fetch-cands env kws atoms (env-lits env) $ Nil _))

(def-fns _ $ (many plain-atoms : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) (Nil _)))
  (match many (is-meta env x) _ ((BTrue) (tail $ plain-atoms env rest)) ((BFalse) (Cons _ x $ notail $ plain-atoms env rest))))

(def-fns _ $ (many naming : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) -> (many (Env) r))
  (let-match many atoms (Cons _ _ _) ((Nil _) env))
  (let ((many lits)) $ lit-cands env atoms (env-lits env) $ Nil _)
  (let ((many names)) $ name-cands env atoms except (name-index-entries _ $ scope-names $ env-scope env) $ Nil _)
  (name-atoms env atoms lits names $ match many (all-named atoms lits names) _ ((BTrue) (Nil _)) ((BFalse) (fetch-cands env atoms except))))

(def-fns _ $ (many lit-name : (many (Env) env) (many (Nat) x) -> (many (Maybe $ String) r))
  (let-match many (lit-of (env-lits env) x) (Some _ r) ((None _) (None _)))
  (match many (names-lit r) _ ((BTrue) (Some _ $ shown-text $ syn-shown r)) ((BFalse) (None _))))

; An entry by its own name, else by the numeral or string literal it is, else, where [aliases], by a name in scope
; equal to it, else by a fetch form yielding it, else as an anonymous marker (Env.name_of).
(def-fns _ $ (many entry-shown-name : (many (Env) env) (many (Bool) aliases) (many (Nat) x) -> (many (String) r))
  (let-match many (env-entry-name env x) (None _) ((Some _ n) (name-text n)))
  (let-match many (lit-name env x) (None _) ((Some _ s) s))
  (let-match many (is-meta env x) (BFalse) ((BTrue) (anon-mark env x)))
  (let-match many (match many aliases (((Maybe $ Pair (Nat) (String)) _))
      ((BTrue) (best-cand x (name-cands env (list1 _ x) (None _) (name-index-entries _ $ scope-names $ env-scope env) $ Nil _) $ None _))
      ((BFalse) (None _)))
    (None _)
    ((Some _ p) (match many p _ ((MkPair _ _ _ nm) nm))))
  (let-match many (best-cand x (fetch-cands env (list1 _ x) $ None _) $ None _) (Some _ p)
    ((None _) (anon-mark env x)))
  (match many p _ ((MkPair _ _ _ fm) fm)))

(def-fns _ $ (many shown-name : (many (Env) env) (many (Nat) x) -> (many (String) r))
  (entry-shown-name env (BTrue) x))

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
  (match many (char-eqb c #\x05) _
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
    ((Some _ hm) (match many (mult-eq hm $ Many) (((Bool) _)) ((BTrue) (is-some _ $ lit-of (env-lits env) x)) ((BFalse) (BFalse))))
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
  (many CalleeWrap : (many (Env) env) (many (String) form) (many (Nat) c) -> (Callee))
  (many CalleeForm : (many (Env) env) (many (String) name) -> (Callee)))

(def-adts $ (Invoke : ((List $ List $ Nat) ctx) -> Type)
  enum
  (many InvApp : (erased (List $ List $ Nat) ctx) (many (Nat) hid) (many (List $ Code ctx many-one) actuals) (many (CC) cc) (many (Bool) skipped) -> (Invoke ctx))
  (many InvWorld : (erased (List $ List $ Nat) ctx) (many (List $ Code ctx many-one) actuals) -> (Invoke ctx))
  (many InvPrim : (erased (List $ List $ Nat) ctx) (many (Sp) prim) (many (List $ Code ctx many-one) actuals) -> (Invoke ctx))
  (many InvNative : (erased (List $ List $ Nat) ctx) (many (Nat) cid) -> (Invoke ctx)))

(def-fns _ $ (many prim-sig-in : (subterm many (List $ PrimSig) ps) (many (Sp) sp) -> (many (Maybe $ PrimSig) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPrimSig q _ _ _))
  (match many (sp-eq q sp) _ ((BTrue) (Some _ p)) ((BFalse) (tail $ prim-sig-in rest sp))))

(def-fns _ $ (many prim-sig : (many (Env) env) (many (Sp) sp) -> (many (Maybe $ PrimSig) r))
  (prim-sig-in (env-prims env) sp))

(let ((many implemented)) $ Cons _ (SpExpr $ ExGensym) $ Cons _ (SpExpr $ ExSettledType) $ Cons _ (SpExpr $ ExSettledErase) $ Cons _ (SpExpr $ ExSettledEq) $ Cons _ (SpExpr $ ExResolve) $ Cons _ (SpExpr $ ExReadFile) $ Cons _ (SpExpr $ ExSettledMult) $ Cons _ (SpExpr $ ExSettledValue) $ Cons _ (SpExpr $ ExInternNat) $ Cons _ (SpExpr $ ExInternChar) $ Cons _ (SpExpr $ ExInternString) $ Cons _ (SpExpr $ ExMintSettled) $ Cons _ (SpExpr $ ExMintSettledErased) $ Cons _ (SpExpr $ ExSettledTyApply) $ Cons _ (SpExpr $ ExSettledValApply) $ Cons _ (SpExpr $ ExSlotEq) $ Nil _)
(let ((many primitives)) $ Cons _ (SpExpr $ ExGensymUnique) $ Cons _ (SpExpr $ ExPlaceAt) $ Cons _ (SpExpr $ ExPlaceAtMany) $ Cons _ (SpExpr $ ExUnplaceAt) $ Cons _ (SpExpr $ ExUnplaceAtMany) $ Cons _ (SpExpr $ ExPlacedSlot) $ Cons _ (SpExpr $ ExPlacedEq) implemented)

(def-fns _ $ (many nullary-ctor-code : (erased (List $ List $ Nat) ctx) (many (Nat) c) -> (many (Code ctx many-one) r))
  (CApp _ many-one (CConst _ c) (Nil _) (CCCtor)))

(def-fns _ $ (many prim-named : (subterm many (List $ Sp) ps) (many (String) s) -> (many (Maybe $ Sp) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (None _)))
  (match many (str-eqb (sp-name p) s) _ ((BTrue) (Some _ p)) ((BFalse) (tail $ prim-named rest s))))

(def-fns _ $ (many entries-erased : (subterm many (List $ Entry) es) -> (many (List $ Entry) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many e (MkEntry n s _ sg p site))
  (Cons _ (MkEntry n s (Erased) sg p site) $ notail $ entries-erased rest))

(def-fns _ $ (many any-stored : (subterm many (List $ Entry) es) -> (many (Bool) r))
  (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
  (or (entry-stored e) $ tail $ any-stored rest))

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

(def-fns _ $ (many callee-written : (many (Callee) c) -> (many (Maybe $ Name) w))
  (match many c _ ((CalleeHead _ head _ _) (raw-atom head)) (else (None _))))

(def-fns _ $ (many describe : (many (Env) env) (many (Syn) head) (many (Term) h) (many (Term) hty) -> (many (Callee) c))
  (CalleeHead env (match many (computed-raw env head) (((Syn) _)) ((BTrue) (RList (raw-pos head) $ Nil _)) ((BFalse) head)) h hty))

(def-fns _ $ (many callee-view : (many (Callee) c) ->
    (many (String) subject) (many (Bool) apposed) (many (List $ Pair (Loc) $ String) notes) (many (Bool) marked) (many (Bool) fields) (many (String) noun))
  (let-match many c (CalleeHead env head h hty)
    ((CalleeWrap env form cid) (values (str-cat (say env $ str-cat3 "`" form "` of ") $ qshown env cid) (BFalse) (declared-as env cid) (BTrue) (BTrue) "more argument"))
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
  (str-cat3 (nat-str n) (str-cat " " what) $ match many (nat-eqb n 1) (((String) _)) ((BTrue) "") ((BFalse) "s")))

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

(def-fns _ $ (many count-mismatch : (many (Env) env) (many (Callee) c) (many (List $ Entry) tele) (many (Multiplicity) pos) (many (Nat) got) (many (List $ Pair (Loc) $ String) spliced) -> (many (Env) r))
  (let ((many subject) (many apposed) (many notes) (many marked) (many fields) (many noun)) $ callee-view c)
  (let ((many all) (erased _)) $ list-append _ notes spliced)
  (env-error-with env all $ str-cat3 subject (match many apposed (((String) _)) ((BTrue) ",") ((BFalse) ""))
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
  (or (equal-env env (TVar x) (TVar y)) $ tail $ same-value env x rest))

(def-fns _ $ (many typed-entries : (many (Env) env) (many (Term) ty) (subterm many (List $ Nat) xs) (many (List $ Pair (Nat) (Name)) found) -> (many (List $ Pair (Nat) (Name)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) found))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (let-match many n (Some _ name) ((None _) (tail $ typed-entries env ty rest found)))
  (let ((many visible)) $ match many (lookup env name) (((Bool) _)) ((Some _ y) (nat-eqb x y)) ((None _) (BFalse)))
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
  (str-cat (hint-at env (entry-site env x) $ str-cat3 (qshow env $ TVar x) " has type " $ str-cat3 (qshow env ty) ", as " $ match many (nat-eqb k 1) (((String) _)) ((BTrue) "does:") ((BFalse) "do:"))
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

(def-fns _ $ (many owners-dropped : (subterm many (List $ Nat) fs) -> (many (List $ Nat) r))
  (let-match many fs (Cons _ f rest) ((Nil _) fs))
  (match many (nat-is-zero f) _ ((BTrue) (tail $ owners-dropped rest)) ((BFalse) fs)))

(def-fns _ $ (many nats-have : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (BFalse)))
  (or (nat-eqb x y) $ tail $ nats-have rest x))

(def-fns _ $ (many frame-chain : (many (Env) e) (subterm many (Nat) fuel) (many (Nat) x) (many (List $ Nat) shown) -> (many (List $ String) r) (many (List $ Nat) shown2))
  (let-match many fuel (Succ f) ((Zero) (values (Nil _) shown)))
  (let-match many (nat-is-zero x) (BFalse) ((BTrue) (values (Nil _) shown)))
  (let-match many (nats-have shown x) (BFalse) ((BTrue) (values (Nil _) shown)))
  (let-match many (env-frame e x) (Some _ fr) ((None _) (values (Nil _) shown)))
  (let-match many fr (MkPair _ _ head call))
  (let-match many call (MkLoc _ cp))
  (let ((many more) (many shown3)) $ notail $ frame-chain e f (spot-frame cp) $ Cons _ x shown)
  (values (Cons _ (located (env-at-loc e call) ": note: " $ str-cat3 "in the expansion of " (qraw head) " here") more) shown3))

(def-fns _ $ (many chains : (many (Env) e) (subterm many (List $ Nat) xs) (many (List $ Nat) shown) -> (many (List $ String) r) (many (List $ Nat) shown2))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil _) shown)))
  (let ((many ls) (many shown2)) $ frame-chain e x x shown)
  (let ((many more) (many shown3)) $ notail $ chains e rest shown2)
  (let ((many all) (erased _)) $ list-append _ ls more)
  (values all shown3))

(def-fns _ $ (many unmarked : (subterm many (List $ String) ps) -> (many (String) text) (many (List $ Nat) xs))
  (let-match many ps (Cons _ t rest) ((Nil _) (values "" $ Nil _)))
  (let-match many rest (Cons _ m more) ((Nil _) (values t $ Nil _)))
  (let ((many t2) (many xs)) $ notail $ unmarked more)
  (values (str-cat t t2) $ Cons _ (parse-nat m) xs))

(def-fns _ $ (many frame-lines : (many (Env) e) (subterm many (List $ String) lines) (many (List $ Nat) shown) -> (many (List $ String) r))
  (let-match many lines (Cons _ line rest) ((Nil _) (Nil _)))
  (let ((many text) (many xs)) $ unmarked $ split-on line #\x03)
  (let ((many ls) (many shown2)) $ chains e xs shown)
  (let ((many after) (erased _)) $ list-append _ ls $ notail $ frame-lines e rest shown2)
  (Cons _ text after))

(def-fns _ $ (many expand-frames : (many (Env) e) (many (String) x) -> (many (String) r))
  (join-strs (frame-lines e (split-on x #\newline) $ Nil _) "\n"))

(def-fns _ $ (many splice-notes : (many (Env) e) (subterm many (List $ Pair (Nat) (Nat)) splices) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many splices (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (MkPair _ _ x k))
  (let-match many (env-frame e x) (Some _ fr) ((None _) (tail $ splice-notes e rest)))
  (let-match many fr (MkPair _ _ head call))
  (let ((many gave)) $ match many k (((String) _)) ((Zero) "no forms") ((Succ k1) (match many k1 (((String) _)) ((Zero) "1 form") ((Succ _) (str-cat (nat-str k) " forms")))))
  (Cons _ (MkPair _ _ call $ str-cat3 "the expansion of " (qraw head) $ str-cat " here gave " gave) $ notail $ splice-notes e rest))

(def-fns _ $ (many spliced-here : (many (Env) e) -> (many (List $ Pair (Loc) $ String) r))
  (let-match many (env-loc e) (MkLoc _ p))
  (splice-notes e $ spot-splices p))

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
  (match many (nat-eqb x y) _
    ((BTrue) (Some _ w))
    ((BFalse) (tail $ warned-find rest x))))

(def-fns _ $ (many means-entry : (many (Env) env) (many (String) n) (many (Nat) x) -> (many (Bool) r))
  (let-match many (lookup env $ NSrc n) (Some _ y)
    ((None _) (BFalse)))
  (match many (canon-env env $ TVar y) _ ((TVar z) (nat-eqb z x)) (else (BFalse))))

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
  (let ((many (Bool) local)) $ match many (spot-bare p) _ ((PosSpot q) (match many q _ ((NoPos) (BFalse)) ((MkPos f _ _) (str-eqb f cf)))) (else (BTrue)))
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

(def-fns _ $ (many written : (many (Env) env) (many (Multiplicity) pos) (many (Multiplicity) m) (many (String) what) -> (many (Env) r))
  (match many (and (not $ mult-is-many pos) $ mult-is-many m) _
    ((BTrue) (env-error env $ say env $ str-cat3 what " written `" $ str-cat (mult-name m) "` in an erased position; write `erased` here"))
    ((BFalse) env)))

; Whether [ty] applies the prelude's [name] type constructor, found in the prelude's scope however the program
; shadows the name, as lib/elab.ml's nullary finds it.
(def-fns _ $ (many prelude-nullary : (many (Env) env) (many (Term) ty) (many (String) name) -> (many (Bool) b))
  (let-match many (type-head env ty) (Some _ tid) ((None _) (BFalse)))
  (let ((many _) (many x)) $ prelude-id env name)
  (nat-eqb tid x))

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
  (let ((many env2) (many r2)) $ produced env what (demand-mode _ env demand (pos-mult expect) $ res-ty r) r)
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

(def-fns _ $ (many syn-at : (many (Spot) p) (many (Syn) r) -> (many (Syn) r2))
  (match many r _ ((RNat _ n) (RNat p n)) ((RChr _ c) (RChr p c)) ((RString _ s) (RString p s)) (else r)))

(def-fns _ $ (many syn-literal : (many (Env) env) (many (Syn) raw) -> (many (Syn) r))
  (let-match many raw (RAtom p n) (else raw))
  (let-match many n (NHandle x rd m _) (else raw))
  (let-match many (and (reading-eq rd $ MintedIs) $ mult-eq m $ Many) (BTrue) ((BFalse) raw))
  (match many (lit-of (env-lits env) x) _ ((Some _ node) (syn-at p node)) ((None _) raw)))

(def-fns _ $ (many lit-interned : (many (Env) env) (many (Syn) raw) -> (many (Env) r) (many (Syn) r2))
  (let-match many (lit-key raw) (Some _ k) ((None _) (values env raw)))
  (let ((many env2)) $ env-back env $ intern-raw (env-at env $ raw-pos raw) raw)
  (let-match many (lit-lookup env2 k) (Some _ x) ((None _) (values env2 raw)))
  (values env2 $ RAtom (raw-pos raw) $ NHandle x (MintedIs) (Many) $ syn-shown raw))

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

(def-fns _ $ (many unwritten : (many (Env) env) (many (Spot) pos) (many (String) form) (many (Nat) id) -> (many (Env) r))
  (def-fns msg-lvl $ (many bound-msg : -> (many (String) s)) (str-cat3 (say env $ str-cat form " cannot name ") (qshown env id) (say env ", an entry of a constructor's telescope still being written")))
  (env-back env $ error-when-msg (env-at env pos) (list-mem-bin (env-ctor-tele env) id) bound-msg))

(def-fns _ $ (many at-place : (many (Env) env) (many (Bool) places) (many (Multiplicity) mult) (many (Spot) epos) (many (Syn) target) -> (many (Env) r) (many (Maybe $ Term) p))
  (let-match many places (BTrue) ((BFalse) (values (error-at env epos $ say env "`at` is allowed only on function telescope and match annotation entries") $ None _)))
  (let ((many tpos)) $ raw-pos target)
  (let-match many (raw-is-literal $ syn-literal env target) (BFalse) ((BTrue) (values (error-at env tpos $ say env "`at` names a variable, not a literal") $ None _)))
  (let ((many envv) (many found)) $ match many target (((Env) _) ((Maybe $ Nat) _))
    ((RAtom _ n) (var-found (env-at env tpos) n))
    (else (values (error-at env tpos $ str-cat "expected a location variable, got " $ qraw target) $ None _)))
  (let-match many found (Some _ x) ((None _) (values (env-back env envv) $ None _)))
  (let ((many envu)) $ unwritten env tpos "`at`" x)
  (let-match many (or (mult-is-many $ entry-mult-of envu x) $ not $ mult-is-many mult) (BTrue) ((BFalse) (values (error-at envu tpos $ say envu "`at` needs a variable declared `many` or `unique`") $ None _)))
  (values (env-refer envu (and (mult-is-many mult) $ not $ env-usage-erased envu) x) $ Some _ $ slot-atom x))

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

(def-fns _ $ (many shown-entry : (many (Env) env) (many (Nat) x) -> (many (Shown) s))
  (let-match many (lit-shown (env-lits env) x) (None _) ((Some _ k) k))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ n _ _ _ _ _ _))
  (ShText $ match many n _ ((None _) "_") ((Some _ s) (spell-name s))))

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
  (many FinalIs : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) (many (Nat) frame) -> (Final fuel root))
  (many FinalMade : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Nat) f) (erased (Subterm (Nat) f (Nat) fuel) p) (many (Syn) r) (many (Nat) frame) -> (Final fuel root)))

(def-fns _ $ (many final-lift : (erased (Nat) fuel) (many (Nat) f2) (erased (Subterm (Nat) f2 (Nat) fuel) q) (erased (List $ Syn) root) (erased (List $ Syn) all) (many (Final f2 all) fin) -> (many (Final fuel root) r))
  (match many fin _
    ((FinalNone _ _) (FinalNone _ _))
    ((FinalIs _ _ r _ x) (FinalMade _ _ f2 q r x))
    ((FinalMade _ _ f p r x) (FinalMade _ _ f (subterm-trans p q) r x))))

(def-fns _ $ (many final-raw : (erased (Nat) fuel) (erased (List $ Syn) root) (many (Final fuel root) fin) (many (Syn) none) -> (many (Syn) r))
  (match many fin _ ((FinalNone _ _) none) ((FinalIs _ _ r _ _) r) ((FinalMade _ _ _ _ r _) r)))

; A raw strictly inside the list root.
(def-adts $ (Sub : ((List $ Syn) root) -> Type)
  enum
  (many MkSub : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) (many (Nat) frame) (many (List $ Nat) pieces) -> (Sub root)))

(def-fns _ $ (many subs-framed : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) (many (List $ Nat) frames) (many (List $ List $ Nat) pieces) -> (many (List $ Sub root) r))
  (let-match many items (Cons _ t rest) ((Nil _) (Nil _)))
  (let ((many f) (many fs)) $ list-pop _ frames 0)
  (let ((many ps) (many pss)) $ list-pop _ pieces $ Nil _)
  (Cons _ (MkSub _ t (in-within (Syn) t items root (prove-subterm t items) w) f ps)
    $ notail $ subs-framed rest _ (within-step rest items root (prove-subterm rest items) w) fs pss))

(def-fns _ $ (many subs-of : (many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) -> (many (List $ Sub root) r))
  (subs-framed items _ w (Nil _) $ Nil _))

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
    (many MkSrcEntry : (erased (List $ Syn) root) (many (Bool) is-sub) (many (Maybe $ Multiplicity) mult) (many (Maybe $ SrcSg root) sg) (many (Maybe $ Name) name) (many (Maybe $ Syn) place) (many (Spot) site) (many (Nat) frame) (many (Nat) sg-frame) (many (Nat) place-frame) -> (SrcEntry root)))
  ((SrcSg : ((List $ Syn) root) -> Type)
    enum
    (many SrcTy : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (SrcSg root))
    (many SrcIs : (erased (List $ Syn) root) (many (Syn) r) (erased (Subterm (Syn) r (List $ Syn) root) p) -> (SrcSg root))))

; Whether every binder carries a type or an is clause, so a let's binders are a telescope (DESIGN.md section 50).
(def-fns _ $ (many all-have-sg : (erased (List $ Syn) root) (subterm many (List $ SrcEntry root) es) -> (many (Bool) r))
  (let-match many es (Cons _ e rest) ((Nil _) (BFalse)))
  (let-match many e (MkSrcEntry _ _ _ ssg _ _ _ _ _ _))
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

(def-fns _ $ (many entries-of-names : (subterm many (List $ Syn) names) (many (Env) env) (many (Bool) is-sub) (many (Maybe $ Multiplicity) mult) (many (Spot) site) (erased (List $ Syn) root) (many (Syn) ty) (erased (Subterm (Syn) ty (List $ Syn) root) pty) (many (Maybe $ Syn) place) (many (Nat) frame) (many (Nat) sgf) (many (Nat) placef) -> (many (List $ SrcEntry root) r))
  (let-match many (at-tail env names) (None _) ((Some _ _) (Nil _)))
  (let-match many names (Cons _ n rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ entries-of-names rest env is-sub mult site _ ty pty place frame sgf placef)
  (Cons _ (MkSrcEntry _ is-sub mult (Some _ $ SrcTy _ ty pty) (raw-name n) place site frame sgf placef) more))

(def-fns _ $ (many parse-entry : (many (Env) env) (many (Syn) raw) (erased (List $ Syn) root) (erased (Subterm (Syn) raw (List $ Syn) root) pr) (many (Nat) frame) (many (List $ Nat) pieces) -> (many (List $ SrcEntry root) r))
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
  (let ((many sgf)) $ list-nth-or _ pieces (nat-sub (list-length _ items0) (list-length _ items)) 0)
  (let ((many placef)) $ list-nth-or _ pieces (nat-pred $ list-length _ items0) 0)
  (let-match many (or (list-is-empty _ rest) $ is-some _ $ at-tail env rest) (BFalse)
    ((BTrue) (match many (raw-binder first) _ ((None _) (Nil _)) ((Some _ n) (Cons _ (MkSrcEntry _ sub3 mult (None _) n place epos frame 0 placef) $ Nil _)))))
  (let-match many rest (Cons _ second rest2) ((Nil _) (Nil _)))
  (let-match many rest2 (Cons _ third rest3) ((Nil _) (entries-of-names rest env sub3 mult epos _ first pf place frame sgf placef)))
  (match many (and (is-mark env second $ MkIs) $ or (list-is-empty _ rest3) $ is-some _ $ at-tail env rest3) _
    ((BTrue) (Cons _ (MkSrcEntry _ sub3 mult (Some _ $ SrcIs _ first pf) (raw-name third) place epos frame sgf placef) $ Nil _))
    ((BFalse) (entries-of-names rest env sub3 mult epos _ first pf place frame sgf placef))))

; The items before the arrow, and those after it, which sit within the root.
(def-fns _ $ (many split-arrow : (subterm many (List $ Syn) items) (erased (List $ Syn) root) (erased (Within items root) w) (many (Env) env) -> (many (Env) r) (many (List $ Sub root) before) (many (List $ Syn) after) (erased (Within after root) wa))
  (let-match many items (Cons _ t rest) ((Nil _) (values (env-error env (say env "missing `->`")) (Nil _) items w)))
  (let ((erased wr)) $ within-step _ _ _ (prove-subterm rest items) w)
  (let-match many (is-mark env t $ MkArrow) (BFalse) ((BTrue) (values env (Nil _) rest wr)))
  (let ((many env2) (many before) (many after) (erased wa)) $ notail $ split-arrow rest _ wr env)
  (values env2 (Cons _ (MkSub _ t (in-within (Syn) t items root (prove-subterm t items) w) 0 $ Nil _) before) after wa))

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
  (let ((many hit)) $ match many (proof-target env x ctor arity index) (((Bool) _)) ((Some _ g2) (nat-eqb g2 g)) ((None _) (BFalse)))
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
  (match many (and (mult-is-many m) $ nat-eqb n 1) _
    ((BTrue) (Cons _ c $ notail $ wrappers rest))
    ((BFalse) (tail $ wrappers rest))))

(def-fns _ $ (many some-not-single : (subterm many (List $ CShape) ss) -> (many (Bool) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (BFalse)))
  (let-match many s (MkCShape m _ n))
  (or (and (mult-is-many m) $ not $ nat-eqb n 1) $ tail $ some-not-single rest))

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

(def-fns _ $ (many phantom-ctor : (many (Env) env) (many (Nat) c) -> (many (Bool) r))
  (let ((many tid)) $ tid-of env c)
  (let-match many (find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env) (Some _ info) ((None _) (BFalse)))
  (let-match many info (MkMatchInfo _ _ cs _))
  (mult-eq (marker cs c) $ Erased))

(def-fns _ $ (many fieldless-pos : (subterm many (List $ CShape) ss) (many (Nat) c) (many (Nat) i) -> (many (Nat) r))
  (let-match many ss (Cons _ s rest) ((Nil _) i))
  (let-match many s (MkCShape _ c2 n))
  (match many (nat-cmp c c2) _ ((CEq _ _ _) i) (else (tail $ fieldless-pos rest c $ match many n (((Nat) _)) ((Zero) (Succ i)) (else i)))))

(def-fns _ $ (many tag-refused : (many (Env) env) (many (Nat) c) (many (String) why) -> (many (Env) r) (many (Nat) pos))
  (values (env-error env $ str-cat (qshown env c) $ say env why) 0))

(def-fns _ $ (many tag-checks : (many (Env) env) (many (Nat) c) (many (List $ Entry) tele) -> (many (Env) r) (many (Nat) pos))
  (let ((many tid)) $ tid-of env c)
  (let-match many (find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env) (Some _ info)
    ((None _) (tag-refused env c " has no opened `Matchable` that lists it")))
  (let-match many info (MkMatchInfo mid disc cs _))
  (let-match many (list-mem-bin (mctor-ids cs) c) (BTrue) ((BFalse) (tag-refused env c " has no opened `Matchable` that lists it")))
  (let-match many (mult-eq (marker cs c) $ Erased) (BFalse) ((BTrue) (tag-refused env c " is phantom, so it has no tag")))
  (let-match many (stored-count tele) (Zero) (else (tag-refused env c " has a non-erased field, so its value is not a tag")))
  (let-match many disc (DEnum) ((DUnion) (tag-refused env c " is a constructor of a union, which carries no tag")))
  (let-match many (type-of env mid) (TMatchable _ _ ext _ _) (else (values env 0)))
  (let-match many ext (BFalse) ((BTrue) (tag-refused env c " is a constructor of an extern type, whose representation is the FFI's")))
  (values env $ fieldless-pos (non-phantom $ shapes cs env) c 0))

(def-fns _ $ (many tag-of : (many (Env) env) (many (Nat) c) -> (many (Maybe $ Nat) r))
  (let ((many tid)) $ tid-of env c)
  (let-match many (find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env) (Some _ info) ((None _) (None _)))
  (let-match many info (MkMatchInfo mid disc cs _))
  (let-match many (list-mem-bin (mctor-ids cs) c) (BTrue) ((BFalse) (None _)))
  (let-match many (type-of env mid) (TMatchable _ nt ext _ _) (else (None _)))
  (let-match many (or nt ext) (BFalse) ((BTrue) (None _)))
  (let ((many ss)) $ shapes cs env)
  (let ((many tagged)) $ tagged-of disc ss)
  (let-match many (hollow-shape tagged $ cshape-arities $ non-phantom ss) (BFalse) ((BTrue) (Some _ 0)))
  (let-match many tagged (BTrue) ((BFalse) (None _)))
  (let-match many (mult-eq (marker cs c) $ Erased) (BFalse) ((BTrue) (None _)))
  (let ((many tele) (many _)) $ ctor-type env c)
  (let-match many (stored-count tele) (Zero) (else (None _)))
  (Some _ $ fieldless-pos (non-phantom ss) c 0))

(def-fns _ $ (many tag-slot-entry : (many (Env) env) (many (Nat) k) -> (many (Env) r) (many (Nat) t))
  (let ((erased _) (many h)) $ env-heap env)
  (let ((many env2) (erased _) (many h2) (erased _) (many t)) $ tag-slot env _ h k)
  (values (env-with-heap env2 _ h2) t))

(def-fns _ $ (many tag-place : (many (Env) env) (many (Nat) c) -> (many (Env) r) (many (Maybe $ Term) p))
  (let-match many (tag-of env c) (Some _ k) ((None _) (values env $ None _)))
  (let ((many env2) (many t)) $ tag-slot-entry env k)
  (values env2 $ Some _ $ slot-atom t))

(def-fns _ $ (many slot-tag-refused : (many (Env) env) (many (String) msg) -> (many (Env) r) (many (Maybe $ Nat) k))
  (values (env-error env $ str-cat (say env "`slot-tag`: ") msg) $ None _))

(def-fns _ $ (many slot-tag-of : (many (Env) env) (many (Nat) x) -> (many (Env) r) (many (Maybe $ Nat) k))
  (let ((many ty)) $ type-of env x)
  (let ((many (Bool) cell) (many (Maybe $ Nat) ctor)) $ match many ty _
    ((TCell h _) (values (BTrue) $ match many (canon-env env h) (((Maybe $ Nat) _)) ((TVar c) (Some _ c)) (else (None _))))
    (else (values (BFalse) $ match many (canon-env env $ TVar x) (((Maybe $ Nat) _)) ((TApp h _) (match many h (((Maybe $ Nat) _)) ((TVar c) (Some _ c)) (else (None _)))) (else (None _)))))
  (let ((many mtid)) $ match many cell (((Maybe $ Nat) _)) ((BTrue) (match many ctor (((Maybe $ Nat) _)) ((Some _ c) (Some _ $ tid-of env c)) ((None _) (None _)))) ((BFalse) (type-head env ty)))
  (let-match many mtid (Some _ tid) ((None _) (slot-tag-refused env $ str-cat3 (qshown env x) " : " $ str-cat (qshow env ty) " is neither a value of a data type nor a cell")))
  (let-match many (find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env) (Some _ info) ((None _) (slot-tag-refused env $ str-cat (qshown env tid) $ say env " has no `Matchable` open")))
  (let-match many info (MkMatchInfo mid disc cs _))
  (let-match many (type-of env mid) (TMatchable _ nt ext _ _) (else (slot-tag-refused env "internal: not a `Matchable`")))
  (let-match many ext (BFalse) ((BTrue) (slot-tag-refused env $ str-cat (qshown env tid) " is an extern type, whose representation is the FFI's")))
  (let-match many nt (BFalse) ((BTrue) (slot-tag-refused env $ str-cat (qshown env tid) " is a newtype, which has no tag slot")))
  (let ((many ss)) $ shapes cs env)
  (let-match many (and (not cell) $ hollow-shape (tagged-of disc ss) $ cshape-arities $ non-phantom ss) (BFalse) ((BTrue) (values env $ Some _ 0)))
  (let-match many ctor (Some _ c) ((None _) (slot-tag-refused env $ str-cat3 "the constructor of " (qshown env x) " is not known here")))
  (let-match many (list-mem-bin (mctor-ids cs) c) (BTrue) ((BFalse) (slot-tag-refused env $ str-cat3 (qshown env c) (say env " is not listed by the `Matchable` open for ") (qshown env tid))))
  (let-match many (mult-eq (marker cs c) $ Erased) (BFalse) ((BTrue) (slot-tag-refused env $ str-cat (qshown env c) " is phantom, so it has no tag slot")))
  (let ((many tele) (many _)) $ ctor-type env c)
  (let-match many (stored-count tele) (Zero) (else (slot-tag-refused env $ str-cat (qshown env c) " has a non-erased field, so it has no tag slot")))
  (let-match many (tag-of env c) (Some _ k) ((None _) (slot-tag-refused env $ str-cat3 (qshown env tid) " is neither tagged nor hollow, so the word of " $ str-cat (qshown env c) " is unspecified")))
  (values env $ Some _ k))

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
    ((None _) (CError _ many-one $ str-cat "internal: not bound at runtime: " $ entry-shown-name env (BFalse) x))))

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
  (match many tele _ ((Nil _) (BFalse)) ((Cons _ e rest) (or (is-some _ $ entry-place e) $ tail $ has-place rest))))

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
  (let-match many (and (mult-is-many $ pos-mult expect) $ or skipped $ has-place tele) (BTrue) ((BFalse) (values env code)))
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
      (and (nat-eqb (open-kind-code kx) $ open-kind-code ky) $ and (nat-lt (open-kind-code kx) 2) $ nats-share nx ny))))

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

; A form's results are opened with open-results, and only after everything the form elaborates: `delegate-of`
; and `at-fn-of` fetch an anonymous entry in scope by its type (ASSUMPTIONS 114), so a result entry opened
; earlier could, it seems, be fetched as the proof of itself.
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

(def-fns _ $ (many open-results : (many (List $ Entry) tele) (many (Env) env) (many (Maybe $ List $ Maybe $ Loc) sites) (many (Maybe $ List $ Multiplicity) mults) (many (List $ Term) ids) ->
    (many (Env) r) (many (List $ Nat) fresh) (erased (Lockstep (Entry) (Nat) tele fresh) lock))
  (open-tele tele env (Some _ $ anon-names tele) sites mults ids $ BFalse))

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
  (let ((many m)) $ match many e (((Multiplicity) _)) ((MkSrcEntry _ _ sm _ _ _ _ _ _ _) (match many sm (((Multiplicity) _)) ((None _) (Many)) ((Some _ mm) mm))))
  (let ((many r) (erased p)) $ notail $ src-mults _ rest)
  (values (Cons _ m r) (LsCons _ _ e m rest r p)))


(def-fns _
  ((many is-strict-subterm : (subterm many (Term) b) (many (Term) a) -> (many (Bool) r))
    (match many b _
      ((TApp _ args) (tail $ subterm-in args a)) (else (BFalse))))
  ((many subterm-in : (subterm many (List $ Term) ts) (many (Term) a) -> (many (Bool) r))
    (match many ts _
      ((Nil _) (BFalse))
      ((Cons _ t rest) (or (term-eq a t) $ or (notail $ is-strict-subterm t a) $ tail $ subterm-in rest a)))))

; A literal is an atom to the unifier (DESIGN.md section 45): checking fails where one meets a Succ shape or another
; literal, and forcing binds one where a contradiction was wanted. The notes name each literal a check or a
; trial turned on, a character standing for its code, with the first of [within] it sits in; numerals come
; first, then characters, each in order of value (lib/elab.ml's literal_notes).
(def-fns _ $ (many lit-value : (many (String) s) -> (many (Nat) n))
  (let-match many (all-digits s) (BFalse) ((BTrue) (parse-nat s)))
  (match many (char-lit-code s) _ ((Some _ c) (char-code c)) ((None _) 0)))

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
  (match many h _ ((MkPair _ _ ct _) (or (and (not $ all-digits $ hit-spelling h) $ is-strict-subterm ct t) $ tail $ code-of-char t rest))))

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
    (match many (and (term-eq h h2) $ nat-eqb (list-length _ xs) $ list-length _ ys) _ ((BTrue) (tail $ differ-list xs ys)) ((BFalse) one-pair)))
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
    $ tail $ pair-side env t rest))

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
  (match many ts _ ((Nil _) (BFalse)) ((Cons _ u rest) (or (term-eq t u) $ tail $ term-among t rest))))

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
  (env-error-with env (spliced-here env) $ str-cat3 "expected " (nat-str expected) $ str-cat3 what ", got " $ nat-str got))

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
  (let ((many notes) (erased _)) $ list-append _ anchors $ spliced-here env)
  (env-error-with env notes $ str-cat3 owner " expects " $ str-cat3 (counted n noun) ", got " $ str-cat (nat-str m) $ expected-str
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
  (let-match many (match many (res-term r) (((Bool) _)) ((TVar _) (BTrue)) (else (BFalse))) (BFalse) ((BTrue) (values env $ res-term r)))
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
  (let ((many whole)) $ list-replicate _ n $ MkPair _ _ (raw-pos final) $ match many (nat-eqb n 1) (((Maybe $ Syn) _)) ((BTrue) (Some _ final)) ((BFalse) (None _)))
  (let-match many final (RList _ items) (else whole))
  (let-match many items (Cons _ v entries)
    ((Nil _) whole))
  (match many (and (is-special env v $ SpExpr $ ExValues) $ nat-eqb (list-length _ entries) n) _ ((BTrue) (written-sites entries)) ((BFalse) whole)))

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
  (let ((many env3)) $ match many (is-literal env x) (((Env) _)) ((BTrue) (env-error env2 $ str-cat3 (qshown env2 x) (match many (lit-of (env-lits env2) x) _ ((Some _ _) " is a literal") ((None _) " is a constant a macro minted")) ", which has no introduction order")) ((BFalse) env2))
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
  (match many (and (term-eq h $ TVar coercible-id) $ nat-eqb (list-length _ args) 6) _
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
  (match many (char-eqb d c) _ ((BTrue) (tail $ drop-prefix prest srest)) ((BFalse) (None _))))

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

(def-fns _ $ (many handle-raw : (many (Env) env) (many (Spot) pos) (many (Nat) x) -> (many (Syn) r))
  (RAtom pos $ NHandle x (MintedIs) (entry-mult-of env x) $ ShText $ entry-name-or-id env x))

(def-fns _ $ (many named-share : (many (Env) env) (many (Syn) raw) -> (many (Bool) r))
  (let-match many raw (RList _ items) (else (BFalse)))
  (let-match many items (Cons _ h rest) ((Nil _) (BFalse)))
  (let-match many rest (Cons _ a more) ((Nil _) (BFalse)))
  (let-match many a (RAtom _ _) (else (BFalse)))
  (and (list-is-empty _ more) $ is-special env h $ SpExpr $ ExShare))

(def-fns _ $ (many settled-dispatch : (many (Env) env) (many (Syn) h) -> (many (Bool) r))
  (or (is-some _ $ special-of env h) (is-some _ $ macro-entry env h)))

(def-fns _ $ (many sub-syns : (erased (List $ Syn) root) (subterm many (List $ Sub root) xs) -> (many (List $ Syn) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let-match many x (MkSub _ r _ _ _))
  (Cons _ r $ notail $ sub-syns _ rest))

(def-fns _ $ (many not-a : (many (Env) env) (many (String) what) (many (Syn) raw) -> (many (String) r))
  (str-cat3 (brief raw) " is " $ str-cat what $ match many (misplaced env raw) (((String) _))
    ((Some _ sp) (let ((many n)) (sp-name sp)) (str-cat (say env $ hint-lines (str-cat (tick n) " ") $ help-lines env "role" n) $ sp-hints env n))
    ((None _) "")))

(def-fns _ $ (many not-a-statement : (many (Env) env) (many (String) within) (many (Syn) raw) -> (many (String) r))
  (not-a env (match many (misplaced env raw) (((String) _)) ((Some _ _) "not a statement") ((None _) (str-cat3 "not a statement\nhint: every " (say env within) " but the last must be a statement"))) raw))

(def-fns _ $ (many bracket-parts : (subterm many (List $ Syn) args) (many (Env) env) (many (Sp) sp) (many (Held) held) ->
    (many (Env) r) (many (List $ Sub args) entries) (many (List $ Syn) after) (erased (Within after args) wa))
  (let-match many args (Cons _ braw after) ((Nil _) (values (env-error env $ sp-misuse env sp) (Nil _) args (WHere args))))
  (let ((erased wa)) $ within-step after args args (prove-subterm after args) (WHere args))
  (let ((many env1) (many entries))
    (match many braw (((Env) _) ((List $ Sub args) es))
      ((RList _ items)
        (let-match many held (MkHeld fs pss _))
        (values env $ subs-framed items _ (WIn _ _ $ subterm-trans (prove-subterm items braw) (prove-subterm braw args)) fs pss))
      (else (values (env-error env $ sp-misuse env sp) (Nil _)))))
  (values env1 entries after wa))

(def-lvl misuse-lvl)


(def-fns _ $ (many find-matchable : (many (Env) env) (many (Nat) tid) -> (many (Env) r) (many (Maybe $ MatchInfo) info))
  (let ((many found)) $ find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env)
  (match many found _
    ((Some _ _) (values env found))
    ((None _) (values (env-error env $ str-cat (qshown env tid) (say env " has no `Matchable` open")) found))))

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
  (let ((many env2) (many r2)) $ match many what (((Env) _) ((Res) _)) ((None _) (values env $ conformed (pos-mult expect) r)) ((Some _ w) (produced env w (pos-mult expect) r)))
  (values ew env2 (Cons _ r2 $ Nil _) $ hoist-none ctx expect $ CErased _ expect))

(def-fns _ $ (many returns-own : (many (Env) env) (many (Nat) tid) (many (Term) ret) -> (many (Bool) r))
  (match many (type-head env ret) _ ((Some _ t) (nat-eqb t tid)) ((None _) (BFalse))))

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
      ((TVar y) (match many (code-var _ _ code) _ ((Some _ z) (match many (nat-eqb y z) _ ((BTrue) (Some _ y)) ((BFalse) (None _)))) ((None _) (match many (mult-is-many pos) _ ((BTrue) (None _)) ((BFalse) (Some _ y))))))
      (else (None _))))
  (match many same _
    ((Some _ y) (values env res y))
    ((None _) (prepare-argument env pos res $ BTrue))))

(def-fns _ $ (many prepare-pack : (erased (List $ List $ Nat) ctx)
    (subterm many (List $ Pair (Nat) $ Code ctx many-one) pairs) ->
    (many (List $ Multiplicity) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) ipk)
    (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk))
  (let-match many pairs (Cons _ pair rest) ((Nil _) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _))))
  (let-match many pair (MkPair _ _ id code))
  (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (notail $ prepare-pack _ rest))
  (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk)
    (Cons _ code codes) (PkMany _ ms code codes cpk)))

(def-fns _ $ (many id-codes : (many (Env) env) (many (List $ List $ Nat) ctx) (subterm many (List $ Nat) ids) -> (many (List $ Code ctx many-one) codes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (Cons _ (var-code env ctx id) $ notail $ id-codes env ctx rest))

(def-fns _ $ (many cell-result : (erased (List $ List $ Nat) ctx) (many (List $ Multiplicity) expect)
    (many (Env) env) (many (Res) res) (many (Code ctx many-one) code) ->
    (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) out))
  (values env (Cons _ res (Nil _))
    (match many (mult-is-many (pos-mult expect)) (((Code ctx expect) _))
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
  (let-match many (nat-eqb ma mb) (BTrue) ((BFalse) (apart)))
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
      (values env1
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

(def-fns _ $ (many binder-at : (many (Env) env) (many (Spot) pos) (many (Syn) raw) (many (String) what) -> (many (Env) r))
  (let-match many (raw-binder raw) (None _) ((Some _ _) env))
  (let ((many env2) (many _)) $ name-checked (env-at env pos) raw what)
  (env-back env env2))

(def-fns _ $ (many field-names-checked : (many (Env) env) (subterm many (List $ Syn) rs) -> (many (Env) r))
  (let-match many rs (Cons _ r rest) ((Nil _) env))
  (match many (raw-binder r) _
    ((Some _ _) (tail $ field-names-checked env rest))
    ((None _) (binder-at env (raw-pos r) r "a field name"))))

(def-fns _ $ (many pattern-fields : (many (Env) env) (many (Spot) ppos) (many (String) what) (many (Multiplicity) mode) (many (Res) scrut) (many (Nat) c) (many (List $ Entry) tele) (many (List $ Multiplicity) mults) (many (List $ Syn) fields) (many (Bool) extra) ->
    (many (Env) out) (many (List $ Syn) ordinary) (many (Maybe $ Syn) braw))
  (let ((many n)) $ list-length _ tele)
  (let ((many got)) $ list-length _ fields)
  (let ((many shown)) $ tele-with-mults tele mults)
  (let ((many has-cell)) $ and extra $ nat-eqb got $ Succ n)
  (let-match many (or (nat-eqb got n) has-cell) (BTrue)
    ((BFalse) (values (binder-count env ppos what c mode extra got $ match many extra (((List $ Entry) _)) ((BTrue) (with-cell-entry c tele shown mode $ res-place scrut)) ((BFalse) shown)) fields (None _))))
  (let-match many has-cell (BTrue) ((BFalse) (values (field-names-checked env fields) fields (None _))))
  (let ((many ordinary) (many rest)) (split-pattern-fields tele fields))
  (let ((many env2)) $ match many rest (((Env) _)) ((Nil _) env) ((Cons _ r _) (binder-at env ppos r "a cell binder")))
  (values (field-names-checked env2 ordinary) ordinary (match many rest (((Maybe $ Syn) _)) ((Nil _) (None _)) ((Cons _ r _) (Some _ r)))))

(def-fns _ $ (many pattern-cell-option : (many (Env) env) (many (Multiplicity) mult) (many (Res) scrut) (many (Nat) c) (many (List $ Nat) fids) (many (Bool) extra) (many (Maybe $ Syn) name) -> (many (Env) out) (many (Maybe $ Nat) cell))
  (let-match many extra (BTrue) ((BFalse) (values env (None _))))
  (let-match many name (Some _ _) ((None _) (values env (None _))))
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
  (values (unwritten env1 (raw-pos raw) "`slot-of`" id) id))

(def-fns _ $ (many cell-slot-codes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) -> (many (List $ Code ctx many-one) codes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (Cons _ (match many id (((Code ctx many-one) _))
    ((None _) (var-code env ctx null-id)) ((Some _ x) (var-code env ctx x))) (notail $ cell-slot-codes env ctx rest)))

(def-fns _ $ (many cell-slot-writes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) (many (Nat) index) -> (many (List $ Pair (Nat) $ Code ctx many-one) writes))
  (let-match many ids (Cons _ id rest) ((Nil _) (Nil _)))
  (let ((many writes)) (notail $ cell-slot-writes env ctx rest (Succ index)))
  (match many id _ ((None _) writes) ((Some _ x) (Cons _ (MkPair _ _ index (var-code env ctx x)) writes))))

(def-fns _ $ (many cell-alloc-result : (unique (ElabWorld) ew) (many (Env) env) (erased (List $ List $ Nat) ctx) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) pre)
    (many (List $ Multiplicity) expect) (many (Nat) c) (many (Ctor) ct) (many (List $ Term) slots)
    (many (List $ Maybe $ Nat) slotids) -> (unique (ElabWorld) ewr at ew)
    (many (Env) env2) (many (List $ Res) ress) (many (Hoisted ctx expect) code))
  (let ((many env1) (many x)) (bind env (None _) (None _) (BFalse) (under (pos-mult expect) (Once)) (TCell (TVar c) slots) (None _) delegate-id))
  (let ((many hollow)) $ hollow-ctor env1 c)
  (let ((many env1b) (many place)) $ tag-place env1 c)
  (let ((many env2)) $ placed-at env1b x place)
  (cell-result-hoisted ew ctx expect env2 (res-with-place (res-of env2 x) place)
    (MkHoisted _ _ ctx2 pre $ match many hollow (((Code ctx2 many-one) _))
      ((BTrue) (var-code env2 ctx2 null-id))
      ((BFalse) (match many place (((Code ctx2 many-one) _))
        ((Some _ _) (CApp _ many-one (var-code env2 ctx2 c) (Nil _) (CCTag)))
        ((None _) (CCellAlloc _ ct (cell-slot-codes env2 ctx2 slotids))))))))

(def-adts $ (CellMark : -> Type)
  enum
  (many CMStore : -> (CellMark))
  (many CMSkip : -> (CellMark))
  (many CMImm : (many (Syn) old) (many (Syn) new) -> (CellMark)))

(def-fns _ $ (many cell-mark-name : (many (CellMark) m) -> (many (String) s))
  (match many m _ ((CMImm _ _) "`imm`") (else "`at`")))

(def-fns _ $ (many refuse-mark : (many (Env) env) (many (Bool) bad) (many (CellMark) m) (many (String) msg) -> (many (Env) r))
  (match many bad _ ((BTrue) (env-error env $ say env $ str-cat (cell-mark-name m) msg)) ((BFalse) env)))

(def-fns _ $ (many cell-mark-token : (many (Env) env) (many (Bool) skip) (many (Syn) raw) -> (many (Env) env2) (many (Maybe $ CellMark) mark))
  (let-match many raw (RList _ items) (else (values env $ None _)))
  (let-match many items (Cons _ m rest) ((Nil _) (values env $ None _)))
  (let-match many (is-mark env m (MkImm)) (BFalse)
    ((BTrue)
      (values (match many (nat-eqb (list-length _ rest) 2) (((Env) _)) ((BTrue) env) ((BFalse) (env-error env $ sp-misuse env $ SpMark $ MkImm)))
        (Some _ $ CMImm (list-nth-or _ rest 0 m) $ list-nth-or _ rest 1 m))))
  (values env $ match many (and skip $ and (list-is-empty _ rest) $ is-mark env m (MkAt)) (((Maybe $ CellMark) _))
    ((BTrue) (Some _ $ CMSkip)) ((BFalse) (None _))))

(def-fns _ $ (many cell-marks : (erased (List $ Syn) root) (subterm many (List $ Sub root) items)
    (many (Env) env) (many (Bool) skip) (many (Maybe $ CellMark) pending) -> (many (Env) env2) (many (List $ Sub root) args) (many (List $ CellMark) marks))
  (let ((many mark)) $ match many pending (((CellMark) _)) ((None _) (CMStore)) ((Some _ m) m))
  (let ((many marked)) $ match many pending (((Bool) _)) ((None _) (BFalse)) ((Some _ _) (BTrue)))
  (let-match many items (Cons _ item rest)
    ((Nil _) (values (refuse-mark env marked mark " must precede an argument") (Nil _) (Nil _))))
  (let-match many item (MkSub _ raw _ _ _))
  (let ((many env1) (many found)) $ cell-mark-token env skip raw)
  (let-match many found (None _)
    ((Some _ _) (tail $ cell-marks _ rest (refuse-mark env1 marked mark " must precede an argument, not another mark") skip found)))
  (let ((many env2) (many args) (many marks)) (notail $ cell-marks _ rest env1 skip (None _)))
  (values env2 (Cons _ item args) (Cons _ mark marks)))

(def-fns _ $ (many cell-invoke-writes : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Bool) full)
    (subterm many (List $ Entry) params) (many (List $ Term) terms) (many (List $ CellMark) marks)
    (many (List $ Term) slots) (many (Nat) index) -> (many (Env) env2) (many (List $ Pair (Nat) $ Code ctx many-one) writes)
    (many (List $ Nat) imms) (many (List $ Pair (Syn) (Term)) dues))
  (let-match many params (Cons _ param rest) ((Nil _) (values env (Nil _) (Nil _) (Nil _))))
  (let ((many term) (many ts)) (match many terms (((Term) _) ((List $ Term) xs))
    ((Nil _) (values (TErr "missing argument") (Nil _))) ((Cons _ x xs) (values x xs))))
  (let ((many mark) (many ms)) (match many marks (((CellMark) _) ((List $ CellMark) xs))
    ((Nil _) (values (CMStore) (Nil _))) ((Cons _ x xs) (values x xs))))
  (let ((many marked)) $ match many mark (((Bool) _)) ((CMStore) (BFalse)) (else (BTrue)))
  (match many (entry-mult param) _
    ((Erased) (tail $ cell-invoke-writes (refuse-mark env marked mark " cannot mark an erased argument") ctx full rest ts ms slots index))
    (else
      (let ((many slot) (many ss)) (match many slots (((Term) _) ((List $ Term) xs))
        ((Nil _) (values (TErr "missing slot") (Nil _))) ((Cons _ x xs) (values x xs))))
      (let ((many same)) (equal-env env slot $ TSlotOf term))
      (let ((many omit)) $ or full $ match many mark (((Bool) _)) ((CMSkip) (BTrue)) (else (BFalse)))
      (let ((many env1)) (refuse-when env (and omit (not same))
        (str-cat3 "`at` argument " (nat-str (Succ index)) " is not in its slot's location class")))
      (let ((many env2) (many immediate) (many due)) $ match many mark (((Env) _) ((Bool) _) ((List $ Pair (Syn) (Term)) _))
        ((CMImm o n) (values (refuse-mark env1 full mark " marks a store, and an `at`-wrapped invocation performs none") (BTrue)
          (Cons _ (MkPair _ _ o slot) $ Cons _ (MkPair _ _ n $ TSlotOf term) $ Nil _)))
        (else (values env1 (BFalse) (Nil _))))
      (let ((many env3) (many writes) (many imms) (many dues)) (notail $ cell-invoke-writes env2 ctx full rest ts ms ss (Succ index)))
      (let ((many dues2) (erased _)) $ list-append _ due dues)
      (values env3
        (match many omit (((List $ Pair (Nat) $ Code ctx many-one) _))
          ((BTrue) writes) ((BFalse) (Cons _ (MkPair _ _ index (var-code env3 ctx (term-var term))) writes)))
        (match many immediate (((List $ Nat) _)) ((BTrue) (Cons _ index imms)) ((BFalse) imms)) dues2))))

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
      ((MkSub _ r p f ps)
        (let ((many envf)) $ env-entering env f)
        (let-match many (raw-atom r) (None _)
          ((Some _ str) (values (env-error envf $ str-cat "expected a telescope entry, got " $ name-text str) $ Nil _)))
        (let ((many es)) $ parse-entry envf r _ p f ps)
        (match many es (((Env) _) ((List $ SrcEntry root) l))
          ((Nil _) (values (malformed-entry envf r) es))
          ((Cons _ _ _) (values envf es))))))
  (let ((many env2) (many more)) $ notail $ parse-entries-checked _ rest $ env-in-expansion env1 $ env-expansion env)
  (let ((many all) (erased _)) $ list-append _ here more)
  (values env2 all))

(def-fns _ $ (many check-binder-mults : (erased (List $ Syn) root) (subterm many (List $ SrcEntry root) es) (many (Multiplicity) spos) (many (Env) env) -> (many (Env) r))
  (let-match many es (Cons _ e rest) ((Nil _) env))
  (let-match many e (MkSrcEntry _ _ m _ _ _ site f _ _))
  (let ((many envf)) $ env-entering env f)
  (match many m _
    ((Some _ mm) (tail $ check-binder-mults _ rest spos $ env-back env $ written (env-at envf site) spos mm "a `let` binder"))
    ((None _) (tail $ check-binder-mults _ rest spos $ env-back env $ env-error envf (say env "`let` binder needs a multiplicity")))))

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
  (Some _ $ MkPair _ _ x $ MkPair _ _ craw fields))

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
  (match many raw _ ((RNat _ n) (Some _ n)) ((RChr _ c) (Some _ $ char-code c)) (else (None _))))

(def-fns _ $ (many cc-eq : (many (CC) a) (many (CC) b) -> (many (Bool) r))
  (match many a _
    ((CCPlain) (match many b _ ((CCPlain) (BTrue)) (else (BFalse))))
    ((CCTail) (match many b _ ((CCTail) (BTrue)) (else (BFalse))))
    ((CCDelegate) (match many b _ ((CCDelegate) (BTrue)) (else (BFalse))))
    ((CCCtor) (match many b _ ((CCCtor) (BTrue)) (else (BFalse))))
    ((CCTag) (match many b _ ((CCTag) (BTrue)) (else (BFalse))))
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
  (Some _ $ MkPair _ _ c fs))

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
    ((None _) (values env2 $ None _)))
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
  (let-match many (nat-eqb (term-var t) c) (BTrue) ((BFalse) (tail $ ctor-trial rest env sres smult c)))
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
  (let ((many notes) (erased _)) $ list-append _ (missing-notes mctors env sres smult cs) $ spliced-here env)
  (env-error-with env notes
    $ str-cat3 (say env $ str-cat3 "this " form " is missing a branch for the following unrefuted constructor") (match many (nat-eqb (list-length _ cs) 1) (((String) _)) ((BTrue) "") ((BFalse) "s")) ":"))

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
  (match many (and (is-special env head $ SpExpr $ ExOpenAbsurd) $ and (nat-eqb (list-length _ more) 1) $ is-underscore $ list-nth-or _ more 0 raw) _
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
        (let ((many env2f)) $ match many (canon-env env2p fty) (((Env) _))
          ((TFn _ _ _ _) env2p)
          (else (error-at env2p hpos $ str-cat3 (tick $ spell-binder name) (say env2p " is declared `at` ") $ str-cat3 (qshown env2p df) (say env2p ", which is not a function: it has type ") $ qshow env2p $ canon-env env2p fty)))
        (let ((many env2d) (many _)) $ bind-erased env2f (None _) (None _) (BFalse) (Erased) (proof-type delegate-id $ Cons _ (sharing-of-fn env2p ty) $ Cons _ ty $ Cons _ (TVar x) $ Cons _ (sharing-of-fn env2p fty) $ Cons _ fty $ Cons _ (TVar df) $ Nil _) (None _) delegate-id)
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
  (match many (nat-eqb s x) (((List $ Nat) _) ((List $ Nat) _)) ((BTrue) (values xs ss)) ((BFalse) (values (Cons _ x xs) (Cons _ s ss)))))

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
  (match many bs _ ((Nil _) (BFalse)) ((Cons _ y brest) (and (nat-eqb x y) $ tail $ bins-eq rest brest))))

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
      ((CCellWrite _ k2 cell slots imms)
        (let-match many (notail $ strengthen _ _ _ cell d) (Some _ cell2)
          ((None _) (None _)))
        (match many (notail $ strengthen-slots _ _ slots d) _ ((None _) (None _)) ((Some _ slots2) (Some _ $ CCellWrite _ k2 cell2 slots2 imms))))
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
      ((CCellWrite _ k2 cell slots imms) (CCellWrite _ k2 (notail $ norm _ _ many-one cell ren) (notail $ norm-slots _ _ slots ren) imms))
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
        (let ((many rest2)) $ notail $ distribute (Cons _ ids ctx) ms rest)
        (let-match many (rhs-atoms _ _ rest2) (None _) ((Some _ _) (bind-through ctx first ms ids pk (notail $ distribute ctx first rhs) rest2)))
        (let-match many rhs (CLet _ inner _ frame fpk value body) (else (bind-through ctx first ms ids pk (notail $ distribute ctx first rhs) rest2)))
        (CLet _ inner _ frame fpk (notail $ distribute ctx inner value) $ bind-through (Cons _ frame ctx) first ms ids pk (notail $ distribute (Cons _ frame ctx) first body) $ bind-lift ctx ms ids frame rest2))
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
      ((CCellWrite _ k2 cell slots imms) (CCellWrite _ k2 (notail $ distribute ctx many-one cell) (notail $ distribute-slots ctx slots) imms))
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
      ((CApp _ _ _ _ cc) (cc-eq cc $ CCTag))
      ((CCellAlloc _ _ _) (BFalse))
      ((CCellWrite _ _ _ _ _) (BFalse))
      ((CCellCopy _ _ _ _) (BFalse))
      ((CCellRead _ _ _ cell) (tail $ erases-to-nothing _ _ cell))
      ((CWorldDo _ _) (BFalse))
      ((CPrim _ _ _ _) (BFalse))
      ((CValues _ _ cs _) (tail $ erases-list _ cs))
      ((CLet _ _ _ _ _ rhs rest) (and (notail $ erases-to-nothing _ _ rhs) $ tail $ erases-to-nothing _ _ rest))
      ((CLetRec _ _ _ _ rest) (tail $ erases-to-nothing _ _ rest))
      ((CMatch _ _ scrut shape bs dfl _)
        (and (notail $ erases-to-nothing _ _ scrut)
          $ and (match many shape (((Bool) _)) ((ShHeld _ mc _) (notail $ erases-to-nothing _ _ mc)) (else (BTrue)))
          $ and (notail $ erases-branches _ _ bs) $ match many dfl (((Bool) _)) ((Some _ d) (tail $ erases-to-nothing _ _ d)) ((None _) (BTrue))))
      (else (BTrue))))
  ((many erases-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BTrue))
      ((Cons _ c rest) (and (notail $ erases-to-nothing _ _ c) $ tail $ erases-list _ rest))))
  ((many erases-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BTrue)))
    (match many b _ ((MkBranch _ _ _ _ body) (and (notail $ erases-to-nothing _ _ body) $ tail $ erases-branches _ _ rest)))))


; ---- tail and delegate (section 19): judged on the normalized post-erasure code, per
; function, so a nested def-fns's marks are its own.

(def-fns _ $ (many cc-marked : (many (CC) cc) (many (Bool) only-delegate) -> (many (Bool) r))
  (match many cc _ ((CCTail) (not only-delegate)) ((CCDelegate) (BTrue)) (else (BFalse))))

(def-fns _ $ (many marked-call : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) (many (CC) cc) -> (many (Bool) r))
  (match many code _
    ((CApp _ _ _ _ cc2) (cc-eq cc cc2))
    ((CLet _ _ _ _ _ rhs rest) (or (notail $ marked-call _ _ rhs cc) $ tail $ marked-call _ _ rest cc))
    (else (BFalse))))

(def-fns _
  ((many has-marked : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) (many (Bool) only) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ f args cc) (or (cc-marked cc only) $ or (notail $ has-marked _ _ f only) $ tail $ has-marked-list _ args only))

      ((CCellAlloc _ _ slots) (tail $ has-marked-list _ slots only))
      ((CCellWrite _ _ cell slots _) (or (notail $ has-marked _ _ cell only) $ tail $ has-marked-slots _ slots only))
      ((CCellCopy _ _ cell slots) (or (notail $ has-marked _ _ cell only) $ tail $ has-marked-slots _ slots only))
      ((CCellRead _ _ _ cell) (tail $ has-marked _ _ cell only))
      ((CWorldDo _ req) (tail $ has-marked _ _ req only))
      ((CPrim _ _ _ args) (tail $ has-marked-list _ args only))
      ((CValues _ _ cs _) (tail $ has-marked-list _ cs only))
      ((CLet _ _ _ _ _ rhs rest) (or (notail $ has-marked _ _ rhs only) $ tail $ has-marked _ _ rest only))
      ((CLetRec _ _ _ _ rest) (tail $ has-marked _ _ rest only))
      ((CMatch _ _ scrut shape bs dfl _) (or (notail $ has-marked _ _ scrut only) $ or (match many shape (((Bool) _)) ((ShKnown _ _) (BFalse)) ((ShNone _) (BFalse)) ((ShHeld _ mc _) (notail $ has-marked _ _ mc only))) $ or (notail $ has-marked-branches _ _ bs only) $ match many dfl (((Bool) _)) ((Some _ d) (tail $ has-marked _ _ d only)) ((None _) (BFalse)))) (else (BFalse))))
  ((many has-marked-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Bool) only) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BFalse))
      ((Cons _ c rest) (or (notail $ has-marked _ _ c only) $ tail $ has-marked-list _ rest only))))

  ((many has-marked-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Bool) only) -> (many (Bool) r))
    (let-match many slots (Cons _ slot rest)
      ((Nil _) (BFalse)))
    (match many slot _ ((MkPair _ _ _ code) (or (notail $ has-marked _ _ code only) $ tail $ has-marked-slots _ rest only))))

  ((many has-marked-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) only) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BFalse)))
    (match many b _ ((MkBranch _ _ _ _ body) (or (notail $ has-marked _ _ body only) $ tail $ has-marked-branches _ _ rest only)))))

; Every marked call sits in tail position: the body's final call, through lets, let recs and match branches
; for tail, directly for delegate.
(def-fns _
  ((many tails-ok : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) c) (many (Bool) direct) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ f args _) (and (not $ has-marked _ _ f $ BFalse) $ not $ has-marked-list _ args $ BFalse))
      ((CLet _ _ _ _ _ rhs rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ c $ BFalse))
          ((BFalse) (and (not $ has-marked _ _ rhs $ BFalse) $ tail $ tails-ok _ _ rest direct))))
      ((CLetRec _ _ _ _ rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ rest $ BFalse))
          ((BFalse) (tail $ tails-ok _ _ rest direct))))
      ((CMatch _ _ scrut shape bs dfl _)
        (let-match many direct (BFalse) ((BTrue) (not $ has-marked _ _ c $ BFalse)))
        (and (not $ has-marked _ _ scrut $ BFalse)
          (and (match many shape (((Bool) _)) ((ShKnown _ _) (BTrue)) ((ShNone _) (BTrue)) ((ShHeld _ mc _) (not $ has-marked _ _ mc $ BFalse)))
            (and (notail $ tails-ok-branches _ _ bs direct)
              $ match many dfl (((Bool) _)) ((Some _ d) (tail $ tails-ok _ _ d direct)) ((None _) (BTrue))))))

      ((CCellAlloc _ _ slots) (not $ has-marked-list _ slots $ BFalse))
      ((CCellWrite _ _ cell slots _) (and (not $ has-marked _ _ cell $ BFalse) $ not $ has-marked-slots _ slots $ BFalse))
      ((CCellCopy _ _ cell slots) (and (not $ has-marked _ _ cell $ BFalse) $ not $ has-marked-slots _ slots $ BFalse))
      ((CCellRead _ _ _ cell) (not $ has-marked _ _ cell $ BFalse))
      ((CWorldDo _ req) (not $ has-marked _ _ req $ BFalse))
      ((CPrim _ _ _ args) (not $ has-marked-list _ args $ BFalse))
      ((CValues _ _ cs _) (not $ has-marked-list _ cs $ BFalse)) (else (BTrue))))
  ((many tails-ok-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) direct) -> (many (Bool) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) (BTrue)))
    (match many b _ ((MkBranch _ _ _ _ body) (and (notail $ tails-ok _ _ body direct) $ tail $ tails-ok-branches _ _ rest direct)))))

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
      ((CCellWrite _ _ cell slots _)
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
  (many AnnPredates : (erased (List $ Syn) root) (many (Spot) ap) (many (Bool) via-handle) (many (Given root) g) -> (Ann root))
  (many AnnSubterm : (erased (List $ Syn) root) (many (Spot) ap) (many (Bool) via-handle) (many (Nat) i) (many (Given root) g) -> (Ann root)))

(def-fns _ $ (many given-of : (erased (List $ Syn) root) (many (Syn) p) (erased (Subterm (Syn) p (List $ Syn) root) q) -> (many (Given root) g))
  (match many (is-underscore p) _ ((BTrue) (Inferred _)) ((BFalse) (Written _ p q))))

(def-fns _ $ (many ann-of : (many (Env) env) (many (Syn) arg) (many (Nat) i) (erased (List $ Syn) root) (erased (Subterm (Syn) arg (List $ Syn) root) pa) -> (many (Ann root) r))
  (let-match many arg (RList _ items) (else (AnnNone root)))
  (let-match many items (Cons _ k krest) ((Nil _) (AnnNone _)))
  (let-match many krest (Cons _ p prest) ((Nil _) (AnnNone _)))
  (let-match many prest (Nil _) ((Cons _ _ _) (AnnNone _)))
  (let ((erased pp)) $ subterm-trans (prove-subterm p arg) pa)
  (let-match many (loc-in env $ raw-pos arg) (MkLoc _ ap))
  (let-match many (is-mark env k $ MkPredates) (BFalse)
    ((BTrue) (AnnPredates _ ap (raw-handle k) $ given-of _ p pp)))
  (match many (is-mark env k $ MkSubterm) _ ((BTrue) (AnnSubterm _ ap (raw-handle k) i $ given-of _ p pp)) ((BFalse) (AnnNone _))))

(def-fns _ $ (many ann-env : (many (Env) env) (erased (List $ Syn) root) (many (Ann root) ann) -> (many (Env) r))
  (match many ann _ ((AnnNone _) env) ((AnnPredates _ ap _ _) (env-in-expansion env $ spot-frame ap)) ((AnnSubterm _ ap _ _ _) (env-in-expansion env $ spot-frame ap))))

(def-fns _ $ (many ann-twice : (erased (List $ Syn) root) (many (Env) env) (many (Spot) ap) (many (Ann root) found) -> (many (Env) r))
  (match many found _ ((AnnNone _) env) (else (error-at env ap "a call carries at most one decrease annotation"))))

; The annotation and the arguments without it.
(def-fns _ $ (many split-annotation : (subterm many (List $ Syn) args) (erased (List $ Syn) root) (erased (Within args root) w) (many (Env) env) (many (Nat) i) (many (List $ Nat) frames) (many (Ann root) found) (many (List $ Sub root) acc) -> (many (Env) env2) (many (Ann root) ann) (many (List $ Sub root) rest))
  (let-match many args (Cons _ arg more) ((Nil _) (values env found $ list-rev _ acc)))
  (let ((erased pa)) $ in-within _ _ _ _ (prove-subterm arg args) w)
  (let ((erased wm)) $ within-step _ _ _ (prove-subterm more args) w)
  (let ((many f) (many fs)) $ list-pop _ frames 0)
  (let ((many ann)) $ ann-of (env-entering env f) arg i _ pa)
  (let ((many first)) $ match many found (((Ann root) _)) ((AnnNone _) ann) (else found))
  (let-match many ann (AnnPredates _ ap _ _)
    ((AnnNone _) (tail $ split-annotation more _ wm env (Succ i) fs found $ Cons _ (MkSub _ arg pa f $ Nil _) acc))
    ((AnnSubterm _ ap _ _ _) (tail $ split-annotation more _ wm (ann-twice _ env ap found) i fs first acc)))
  (let ((many env1)) $ ann-twice _ env ap found)
  (let ((many env2)) $ match many (nat-is-zero i) (((Env) _)) ((BTrue) env1) ((BFalse) (error-at env1 ap $ say env "`predates` is written immediately after the callee")))
  (tail $ split-annotation more _ wm env2 i fs first acc))

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
  (let-match many same (BTrue) ((BFalse) (values env $ AnnPredates _ (here-pos env) (BFalse) $ Inferred _)))
  (match many (first-differing positions env args 0) _
    ((Some _ i) (values env $ AnnSubterm _ (here-pos env) (BFalse) i $ Inferred _))
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
  (match many s _ ((MkSub _ arg _ _ _) (Cons _ arg $ notail $ sub-raws _ rest))))

(def-fns _ $ (many sub-positions : (erased (List $ Syn) root) (subterm many (List $ Sub root) subs) -> (many (List $ Spot) r))
  (let-match many subs (Cons _ s rest) ((Nil _) (Nil _)))
  (match many s _ ((MkSub _ arg _ _ _) (Cons _ (raw-pos arg) $ notail $ sub-positions _ rest))))

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
      ((AnnPredates _ p0 h _) (values p0 "predates" $ and (not h) $ match many (canon-env env lv) (((Bool) _)) ((TVar m) (provable-predates env m cur)) (else (BFalse))))
      ((AnnSubterm _ p0 h i _) (values p0 "subterm" $ and (not h) $ subterm-provable-at env params args i))))
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

(def-fns _ $ (many apply-metas : (many (Env) env) (many (Nat) mult-id) (subterm many (List $ Syn) hs) -> (many (Env) r) (many (List $ Pair (Nat) $ Pair (Nat) (Nat)) ms))
  (let-match many hs (Cons _ _ more) ((Nil _) (values env $ Nil _)))
  (let ((many env1) (many m)) $ bind-as env (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TApp (TVar mult-id) $ Nil _) (None _) delegate-id)
  (let ((many env2) (many ty)) $ bind-as env1 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) type-term (None _) delegate-id)
  (let ((many env3) (many t)) $ bind-as env2 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TVar ty) (None _) delegate-id)
  (let ((many env4) (many rest)) $ notail $ apply-metas env3 mult-id more)
  (values env4 $ Cons _ (MkPair _ _ m $ MkPair _ _ ty t) rest))

(def-fns _ $ (many apply-params : (many (Nat) settled-id) (many (Nat) i) (subterm many (List $ Pair (Nat) $ Pair (Nat) (Nat)) ms) -> (many (List $ Entry) r))
  (let-match many ms (Cons _ mtt more) ((Nil _) (Nil _)))
  (let-match many mtt (MkPair _ _ m tt))
  (let-match many tt (MkPair _ _ ty t))
  (let ((many (String) name)) $ match many i _ ((Zero) "c") (else (str-cat "a" $ nat-str i)))
  (Cons _ (MkEntry (Some _ $ NSrc name) (BFalse) (Many) (SgTy $ TApp (TVar settled-id) $ Cons _ (TVar m) $ Cons _ (TVar ty) $ Cons _ (TVar t) $ Nil _) (None _) (None _)) $ notail $ apply-params settled-id (Succ i) more))

(def-fns _ $ (many apply-indices : (many (Env) env) (subterm many (List $ Pair (Nat) $ Pair (Nat) (Nat)) ms) -> (many (List $ Pair (Term) $ Pair (Term) (Term)) r))
  (let-match many ms (Cons _ mtt more) ((Nil _) (Nil _)))
  (let-match many mtt (MkPair _ _ m tt))
  (let-match many tt (MkPair _ _ ty t))
  (Cons _ (MkPair _ _ (canon-env env $ metaless env $ TVar m) $ MkPair _ _ (metaless env $ TVar ty) $ metaless env $ TVar t) $ notail $ apply-indices env more))

(def-fns _ $ (many mult-refused : (many (Env) env) (many (Sp) sp) (many (Syn) raw) (many (Term) m) (many (String) want) -> (many (Env) r))
  (env-error (env-at env $ raw-pos raw) $ str-cat (tick $ sp-name sp) $ str-cat " takes this handle at " $ str-cat want $ str-cat ", and its `Mult` is " $ qshow env m))

(def-fns _ $ (many handles-at : (many (Env) env) (many (Sp) sp) (many (Term) none-mult) (many (Term) mc) (subterm many (List $ Syn) raws) (many (List $ Pair (Term) $ Pair (Term) (Term)) idx) (many (Maybe $ List $ Entry) tele) -> (many (Env) r))
  (let-match many raws (Cons _ raw more) ((Nil _) env))
  (let-match many idx (Cons _ mtt rest) ((Nil _) env))
  (let-match many mtt (MkPair _ _ m _))
  (let-match many (match many tele (((Bool) _)) ((Some _ es) (match many es _ ((Nil _) (BTrue)) (else (BFalse)))) ((None _) (BFalse))) (BFalse) ((BTrue) env))
  (let ((many (Maybe $ List $ Entry) later) (many (Term) want)) $ match many tele _
    ((Some _ es) (match many es _
      ((Cons _ e es2) (values (Some _ es2) $ match many (mult-eq (entry-mult e) $ Erased) _ ((BTrue) none-mult) ((BFalse) mc)))
      ((Nil _) (values (None _) none-mult))))
    ((None _) (values (None _) none-mult)))
  (let-match many (term-eq m want) (BTrue) ((BFalse) (mult-refused env sp raw m $ qshow env want)))
  (tail $ handles-at env sp none-mult mc more rest later))

(def-fns _ $ (many index-raws : (many (Env) env) (many (Spot) l) (subterm many (List $ Pair (Term) $ Pair (Term) (Term)) idx) -> (many (Env) r) (many (List $ Syn) raws))
  (let-match many idx (Cons _ mtt more) ((Nil _) (values env $ Nil _)))
  (let-match many mtt (MkPair _ _ _ tt))
  (let-match many tt (MkPair _ _ ty t))
  (let ((many env1) (many x)) $ match many t (((Env) _) ((Nat) _)) ((TVar y) (values env y)) (else (bind env (None _) (None _) (BFalse) (Erased) ty (Some _ t) delegate-id)))
  (let ((many env2) (many rest)) $ notail $ index-raws env1 l more)
  (values env2 $ Cons _ (RAtom l $ NHandle x (MintedIs) (Erased) $ ShText $ show-t env1 $ TVar x) rest))

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
    ((Cons _ e rest) (or (has-meta-env env $ sg-term $ entry-sg e) $ tail $ tele-has-meta rest env))))

(def-fns _ $ (many terms-have-meta : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Bool) r))
  (match many ts _
    ((Nil _) (BFalse))
    ((Cons _ t rest) (or (has-meta-env env t) $ tail $ terms-have-meta rest env))))

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
  (match many s _ ((MkSub _ arg _ _ _) (or (is-underscore arg) $ tail $ any-wild _ rest))))

; Where each `_` among [args] is written, for the meta that stands for it; nothing for any other argument.
(def-fns _ $ (many wild-sites : (erased (List $ Syn) root) (many (Env) env) (subterm many (List $ Sub root) args) -> (many (List $ Maybe $ Loc) r))
  (let-match many args (Cons _ s rest) ((Nil _) (Nil _)))
  (let-match many s (MkSub _ arg _ f _))
  (Cons _ (match many (is-underscore arg) (((Maybe $ Loc) _)) ((BTrue) (Some _ $ loc-in (env-entering env f) $ raw-pos arg)) ((BFalse) (None _)))
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
  (let ((many payload)) $ match many blk (((Maybe $ Payload) _)) ((BExt _ p) (Some _ p)) (else (match many (word-of-block _ blk) (((Maybe $ Payload) _)) ((Some _ w) (Some _ $ PNat w)) ((None _) (None _)))))
  (let-match many payload (Some _ p) ((None _) (None $ Rope)))
  (match many p (((Maybe $ Rope) _))
    ((PNat n)
      (let-match many (prelude-nullary env ty "Nat") (BFalse) ((BTrue) (Some _ $ RStr $ nat-str n)))
      (let-match many (prelude-nullary env ty "Char") (BTrue) ((BFalse) (None $ Rope)))
      (match many (char-of-nat n) (((Maybe $ Rope) _)) ((Some _ c) (Some _ $ lit-char-rope c)) ((None _) (None $ Rope))))
    ((PStr st)
      (match many (prelude-nullary env ty "String") (((Maybe $ Rope) _))
        ((BTrue) (Some _ $ RStr $ lit-string st))
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
    ((TVar z) (match many (ctor-of env z) _ ((Some _ ct) (nat-eqb (ctor-id ct) cid)) ((None _) (BFalse))))
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
        (let ((erased _) (many hp2) (erased _) (many read)) $ dispatch _ hp (adt-ext adt) (adt-tagged adt) (ctor-arities $ adt-ctors adt) r)
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
          (let ((many env5a)) $ match many (is-some _ $ adt-of env5 mid) (((Env) _)) ((BTrue) env5) ((BFalse) (env-error env5 $ str-cat3 (say env5 "the `Matchable` for ") (qshown env5 tid) (say env5 $ match many (entry-mult-of env5 mid) (((String) _)) ((Erased) " is erased, so `comptime-match` cannot consult it") (else " is not Settled, so `comptime-match` cannot consult it")))))
          (let ((many env5b)) $ use-entry (warn-use env5a (env-loc env5a) "match on" $ TVar tid) (Many) mid (BFalse))
          (let ((many env6a)) $ match many disc (((Env) _)) ((DUnion) (env-error env5b (say env5b "`comptime-match` needs an `enum`, not a `union`"))) ((DEnum) env5b))
          (let ((many env6b) (many mk)) $ marker-checked env6a tid mctors c)
          (match many (mult-is-many mk) (((Env) _)) ((BTrue) env6b) ((BFalse) (env-error env6b $ str-cat3 (say env6b "`comptime-match`: ") (qshown env6b c) " is phantom, so no non-erased value is headed by it"))))))
    (let ((many (Env) env7))
      (match many (ctor-of env6 c) _
        ((None _) (env-error env6 $ str-cat (qshown env6 c) " is not a run-position constructor"))
        ((Some _ ct)
          (let ((many env6b) (many mi)) $ env-destruct env6 x ct)
          (match many (headed-by mi ct) (((Env) _))
            ((BTrue) env6b)
            ((BFalse) (env-error env6b $ str-cat3 (say env6b "`comptime-match`: expected ") (qshown env6b c) $ str-cat ", got " $ tick $ rope-str $ show-typed env6b (type-of env6b x) x))))))
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
(def-fns _
  ((many raw-size : (subterm many (Syn) raw) -> (many (Nat) n))
    (match many raw _
      ((RList _ items) (Succ $ notail $ raws-size items))
      (else 1)))
  ((many raws-size : (subterm many (List $ Syn) rs) -> (many (Nat) n))
    (match many rs _
      ((Nil _) 0)
      ((Cons _ r rest) (nat-add (notail $ raw-size r) $ notail $ raws-size rest)))))


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
  (let-match many (nat-eqb hd level-id) (BFalse)
    ((BTrue) (match many (entry-minted env x) _ ((BTrue) (say env "level minted by `def-lvl`")) ((BFalse) "level"))))
  (let-match many (nat-eqb hd univ-id) (BFalse) ((BTrue) "type"))
  (let-match many (nat-eqb hd special-id) (BFalse)
    ((BTrue) "special form"))
  (match many (list-mem-bin proof-ids hd) _ ((BTrue) "proof") ((BFalse) "value")))

(def-fns _ $ (many entry-flags : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (let ((erased _) (many e)) $ entry env x)
  (let-match many e (MkEInfo _ name mult state _ _ _ site))
  (let ((many (Bool) shadowed)) $ match many name _ ((None _) (BFalse)) ((Some _ n) (match many (lookup env n) _ ((Some _ y) (not $ nat-eqb y x)) ((None _) (BTrue)))))
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
          ((UseShared l) (str-cat3 "unique: shared at " (loc-str $ Some _ l) $ str-cat3 (say env ", so usable at many, written `(share ") (entry-shown-name env (BFalse) x) ")`, and never again at unique"))))))
  (Cons _ status $ when-str (list-mem-bin (env-captures env) x) (say env "unique: closed over by the enclosing `def-fns`, so usable here only erased or through `share`") $ Nil _))

(def-fns _ $ (many entry-value : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let-match many (and (is-settled env x) $ mult-is-many $ entry-mult-of env x) (BTrue) ((BFalse) (Nil _)))
  (let ((many shown)) $ rope-str $ show-typed env (type-of env x) x)
  (match many (str-eqb shown "_") _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "= " shown))))

(def-fns _ $ (many entry-lines : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let ((many _) (many rule)) $ fact-at env x)
  (let ((many (List $ String) is-line))
    (match many rule _
      ((None _) (Nil _))
      ((Some _ r0)
        (let ((many r)) $ canon-env env r0)
        (let ((many (Bool) anonymous)) $ match many r _ ((TVar y) (match many (env-entry-name env y) _ ((None _) (BTrue)) ((Some _ _) (BFalse)))) (else (BFalse)))
        (match many anonymous _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "is " $ show-t-except env r $ Some _ x))))))
  (Cons _ (str-cat3 (entry-shown-name env (BFalse) x) " : " $ str-cat3 (show-t env $ type-of env x) "  [" $ str-cat (entry-flags env x) "]")
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
    ((MkMatchInfo _ _ cs _) (list1 _ $ str-cat3 "constructors of `" (entry-shown-name env (BFalse) tid) $ str-cat "`: " $ join-strs (ctor-strs env cs) "; "))))

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
      (let ((many (List $ Entry) es2)) $ match many (nat-eqb (list-length _ es) $ list-length _ expect) _ ((BTrue) (with-mults expect es)) ((BFalse) es))
      (Cons _ (str-cat "goal: " $ show-tele-t env es2 $ BTrue) $ ctor-lines-tele env es2))))

(def-fns _ $ (many position-lines : (many (Env) env) (many (Goal) wanted) -> (many (List $ String) r))
  (let ((many (List $ String) pos))
    (match many wanted _
      ((GoalStatement) (Nil _))
      ((GoalType) (list1 _ "position: erased"))
      ((GoalValues expect _) (list1 _ $ str-cat "position: " $ mult-name $ pos-mult expect))))
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
  (match many (or (bound-here env x) $ nat-eqb x null-id) _ ((BTrue) (Some _ $ entry-shown-name env (BFalse) x)) ((BFalse) (None _))))

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
  (let-match many l (MkLitEntry x _ lit _ _))
  (let-match many lit (Some _ r) ((None _) more))
  (let-match many r (RNat _ n) (else more))
  (let ((many s)) $ nat-str n)
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


(def-fns _ $ (many at-taken : (many (Env) env) (many (Multiplicity) m) (many (Multiplicity) want) (many (Res) h) -> (many (Env) r))
  (match many (mult-eq m want) _
    ((BTrue) env)
    ((BFalse) (env-error env $ str-cat3 (say env "the head ") (qshow env $ res-term h) $ str-cat3 " : " (qshow env $ canon-env env $ res-ty h) $ str-cat3 " is taken at " (tick $ spell env $ mult-name want) $ str-cat " here; write " $ tick $ str-cat3 "(" (spell env "at") $ str-cat3 " " (spell env $ mult-name want) " (...))"))))

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
