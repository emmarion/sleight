; self/elab.sl -- the elaborator and checker (self/README.md): head dispatch (DESIGN.md section 4), erasure
; by position (section 20), calls with their proofs, matches with refutation and else (sections 12, 17, 38),
; the seven statements with run-position statements run at once (sections 16, 34), literals, and the sugar
; expansions. It mirrors lib/elab.ml with every check ported (ASSUMPTIONS 91); an error is recorded as a
; value and elaboration goes on, so a program may be refused with more than one message.

(def-adts $ (Res : -> Type)
  enum
  (many MkRes : (many (Term) term) (many (Term) ty) (many (Mult) erasure) (many (Maybe $ Term) place) -> (Res)))

(def-fns _ $ (many res-term : (many (Res) r) -> (many (Term) t)) (match many r _ ((MkRes t _ _ _) t)))
(def-fns _ $ (many res-ty : (many (Res) r) -> (many (Term) t)) (match many r _ ((MkRes _ ty _ _) ty)))
(def-fns _ $ (many res-erasure : (many (Res) r) -> (many (Mult) t)) (match many r _ ((MkRes _ _ e _) e)))

(def-fns _ $ (many res-place : (many (Res) r) -> (many (Maybe $ Term) p))
  (match many r _ ((MkRes _ _ _ p) p)))

(def-fns _ $ (many res-with-place : (many (Res) r) (many (Maybe $ Term) p) -> (many (Res) r2))
  (match many r _ ((MkRes t ty m _) (MkRes t ty m p))))

(def-fns _ $ (many res-of : (many (Env) env) (many (Nat) x) -> (many (Res) r))
  (MkRes (TVar x) (type-of env x) (entry-mult-of env x) $ Some _ $ TVar x))

(def-fns _ $ (many term-res : (many (Env) env) (many (Term) t) (many (Term) ty) -> (many (Res) r))
  (MkRes t ty (Erased) $ None _))

(let ((many no-res)) $ MkRes (TErr "no value") (TErr "no value") (Erased) $ None _)
(let ((many erased-one)) $ Cons _ (Erased) $ Nil _)

; One value's code at the shape the position expects, that position read from the shape; a shape of another
; count has its count reported at the expression's end.
(def-fns _ $ (many single : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (erased (Mult) pos) (erased (PosOf expect pos) pf) (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) c) -> (many (Code ctx expect) r))
  (match many expect _
    ((Nil _) (CError _ expect "size"))
    ((Cons _ m rest)
      (match many rest _
        ((Cons _ _ _) (CError _ expect "size"))
        ((Nil _)
          (match many m _
            ((Many)
              (let-match erased pf (PoMany r0))
              c)
            ((Once)
              (let-match erased pf (PoOnce r0))
              (recast _ expect many-one (MsManyOnce _ _ $ MsNil) c))
            ((Erased)
              (let-match erased pf (PoOnly))
              c)))))))

(def-fns _ $ (many first-res : (erased (Mult) m) (erased (List $ Mult) ms) (many (List $ Res) rs) (erased (Lockstep (Mult) (Res) (Cons (Mult) m ms) rs) lock) -> (many (Res) r))
  (let-match erased lock (LsCons a b x y xs ys p))
  (let-match many rs (Cons c r rest))
  r)

; What a statement leaves in the code after it (lib/elab.ml's wrap functions), and the frame it binds.
(def-adts $ (StmtCode : ((List $ List $ Nat) ctx) ((List $ List $ Nat) ctx2) -> Type)
  enum
  (many SNone : (erased (List $ List $ Nat) ctx) -> (StmtCode ctx ctx))
  (many SLet : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (many (Code ctx ms) rhs) -> (StmtCode ctx (Cons (List (Nat)) ids ctx)))
  (many SLetRec : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) gids) (many (Group gids ctx) g) -> (StmtCode ctx (Cons (List (Nat)) gids ctx)))
  (many SMatch : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (Nat) disc) (many (List $ Nat) ids) -> (StmtCode ctx (Cons (List (Nat)) ids ctx)))
  (many SSeq : (erased (List $ List $ Nat) ctx) (erased (List $ List $ Nat) ctx1) (erased (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx1) first) (many (StmtCode ctx1 ctx2) then) -> (StmtCode ctx ctx2)))

(def-fns _ $ (many consts-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) cs) ->
    (many (List $ Mult) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) ipk) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk))
  (match many cs _
    ((Nil _) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _)))
    ((Cons _ p rest)
      (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) $ notail $ consts-codes ctx rest)
      (match many p _
        ((MkPair _ _ id v) (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk) (Cons _ (CValue _ v) codes) (PkMany _ ms (CValue _ v) codes cpk)))))))

(def-fns _ $ (many wrap-stmt : (erased (List $ List $ Nat) ctx) (erased (List $ List $ Nat) ctx2) (many (List $ Mult) ns) (subterm many (StmtCode ctx ctx2) sc) (many (Code ctx2 ns) rest) -> (many (Code ctx ns) r))
  (match many sc _
    ((SNone _) rest)
    ((SLet _ ms ids pk rhs) (CLet _ ms _ ids pk rhs rest))
    ((SLetRec _ _ g) (CLetRec _ _ _ g rest))
    ((SMatch _ scrut shape disc ids) (CMatch _ ns scrut shape (Cons _ (MkBranch _ _ disc ids rest) $ Nil _) (None _) $ Cons _ disc $ Nil _))
    ((SSeq _ _ _ first then) (tail $ wrap-stmt _ _ ns first $ notail $ wrap-stmt _ _ ns then rest))))

; ---- Raw helpers and the special-form head test

(def-fns _ $ (many raw-atom : (many (Raw) r) -> (many (Maybe $ String) s))
  (match many r _ ((RAtom _ s) (Some _ s)) (else (None $ String))))

(def-fns _ $ (many raw-items : (many (Raw) r) -> (many (List $ Raw) items))
  (match many r _ ((RList _ items) items) (else (Nil $ Raw))))

(def-fns _ $ (many raw-name : (many (Raw) r) -> (many (String) s))
  (match many r _ ((RAtom _ s) s) (else "_")))

(def-fns _ $ (many atoms-only : (subterm many (List $ Raw) rs) -> (many (Bool) r))
  (match many rs _
    ((Nil _) (BTrue))
    ((Cons _ r rest) (match many (raw-atom r) _ ((None _) (BFalse)) ((Some _ _) (tail $ atoms-only rest))))))

(def-fns _ $ (many is-underscore : (many (Raw) r) -> (many (Bool) b))
  (match many (raw-atom r) _ ((None _) (BFalse)) ((Some _ s) (str-eq s "_"))))

(def-fns _ $ (many term-var : (many (Term) t) -> (many (Nat) x))
  (match many t _ ((TVar x) x) (else (Zero))))

(def-fns _ $ (many name-or-anon : (many (String) n) -> (many (Maybe $ String) r))
  (match many (str-cmp n "_") _ ((CEq _ _ _) (None _)) (else (Some _ n))))

; A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4).
(def-fns _ $ (many special-of-atom : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ Sp) r))
  (match many (raw-atom raw) _
    ((None _) (None _))
    ((Some a n)
      (match many (lookup env n) _
        ((None _) (None _))
        ((Some b x)
          (match many (and (mult-is-many $ entry-mult-of env x) $ equal-env env (type-of env x) special-term) _
            ((BFalse) (None _))
            ((BTrue)
              (let ((erased a2) (many blk)) $ env-block env x)
              (match many blk _
                ((None _) (None _))
                ((Some _ b2) (match many b2 _ ((BTag _ ct _) (sp-of-index $ ctor-index ct)) (else (None $ Sp))))))))))))

(def-fns _ $ (many special-of : (many (Env) env) (subterm many (Raw) raw) -> (many (Maybe $ Sp) r))
  (match many raw _
    ((RList _ items)
      (match many items _
        ((Nil _) (None _))
        ((Cons _ h tail2)
          (match many tail2 _
            ((Nil _) (None _))
            ((Cons _ arg more)
              (match many (notail $ special-of env h) _
                ((None _) (None _))
                ((Some _ sp)
                  (match many (and (sp-eq sp $ SpExpr $ ExShare) $ list-is-empty _ more) _
                    ((BFalse) (None _))
                    ((BTrue) (tail $ special-of env arg))))))))))
    (else (special-of-atom env raw))))

(def-fns _ $ (many read-special : (many (Env) env) (subterm many (Raw) raw) (many (Bool) sharing) (many (Mult) pos) -> (many (Env) r))
  (match many raw _
    ((RAtom _ n) (match many (lookup env n) _ ((None _) env) ((Some _ x) (use-entry env (Many) x sharing))))
    ((RList _ items)
      (match many items _
        ((Nil _) env)
        ((Cons _ h rest)
          (match many rest _
            ((Nil _) env)
            ((Cons _ arg _)
              (let ((many env14)) (match many (mult-is-many pos) (((Env) _))
                ((BTrue) env)
                ((BFalse) (env-error env "`share` in an erased position"))))
              (tail $ read-special (notail $ read-special env14 h (BFalse) pos) arg (BTrue) pos))))))
    (else env)))

(def-adts $ (ExprDemand : ((List $ Mult) expect) -> Type)
  enum
  (many Fixed : (erased (List $ Mult) expect) -> (ExprDemand expect))
  (many CallableHead : -> (ExprDemand many-one))
  (many FinalDemand : -> (ExprDemand many-one)))

(def-adts $ (DemandBridge : ((List $ Mult) outer) ((List $ Mult) inner) -> Type)
  enum
  (many KeepDemand : (erased (List $ Mult) ms) -> (DemandBridge ms ms))
  (many HeadDemand : (many (Mult) mode) -> (DemandBridge many-one (Cons (Mult) mode (Nil (Mult))))))

(def-fns _ $ (many head-demand : (many (Env) env) (many (Term) ty) -> (many (Mult) m))
  (match many (canon-env env ty) _
    ((TCell _ _) (Once))
    ((TFn uq _ _ _) (match many uq _ ((BTrue) (Once)) ((BFalse) (Many))))
    (else (Many))))

(def-fns _ $ (many is-special : (many (Env) env) (many (Raw) raw) (many (Sp) sp) -> (many (Bool) r))
  (match many (special-of env raw) _
    ((None _) (BFalse))
    ((Some _ s) (sp-eq s sp))))

(def-fns _ $ (many is-mark : (many (Env) env) (many (Raw) raw) (many (MarkK) k) -> (many (Bool) r))
  (is-special env raw $ SpMark k))

(def-fns _ $ (many mult-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ Mult) r))
  (match many (special-of env raw) _
    ((None _) (None _))
    ((Some _ s)
      (match many (sp-eq s $ SpMark $ MkErased) _
        ((BTrue) (Some _ $ Erased))
        ((BFalse) (match many (sp-eq s $ SpMark $ MkMany) _ ((BTrue) (Some _ $ Many)) ((BFalse) (match many (sp-eq s $ SpMark $ MkUnique) _ ((BTrue) (Some _ $ Once)) ((BFalse) (None _))))))))))

(def-fns _ $ (many stmt-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ StmtK) r))
  (match many (raw-items raw) _
    ((Nil _) (None _))
    ((Cons _ h _)
      (match many (special-of env h) _
        ((None _) (None _))
        ((Some _ sp)
          (match many sp _
            ((SpStmt k) (Some _ k)) (else (None $ StmtK))))))))

(def-fns _ $ (many is-statement : (many (Env) env) (many (Raw) raw) -> (many (Bool) r))
  (match many (stmt-of env raw) _ ((None _) (BFalse)) ((Some _ _) (BTrue))))

(def-fns _ $ (many share-arg : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ Raw) r))
  (match many (raw-items raw) _
    ((Nil _) (None _))
    ((Cons _ h rest)
      (match many rest _
        ((Nil _) (None _))
        ((Cons _ arg more)
          (match many (and (list-is-empty _ more) $ is-special env h $ SpExpr $ ExShare) _
            ((BTrue) (Some _ arg))
            ((BFalse) (None _))))))))


; The numeral and character literals, each with its canonical form.
(def-fns _ $ (many lit-terms : (many (Env) env) (subterm many (List $ LitEntry) lits) -> (many (List $ Pair (Term) (LitEntry)) r))
  (match many lits _
    ((Nil _) (Nil _))
    ((Cons _ l rest)
      (let ((many more)) $ notail $ lit-terms env rest)
      (match many l _
        ((MkLitEntry x _ s)
          (match many (is-literal-name s) _
            ((BTrue) (Cons _ (MkPair _ _ (canon-env env $ TVar x) l) more))
            ((BFalse) more)))))))

; An atom is shown by the best of the entries equal to it that a reader can name where the message is: a
; numeral or string literal, by its spelling, else the newest binding the scope still names, else its id. What
; canonicalization picks to represent a class is an accident of minting order, so it does not decide the name
; (lib/env.ml's show). A candidate is the atom it would name, its entry, and the name.
(def-fns _ $ (many cand-of : (many (Env) env) (many (List $ Nat) atoms) (many (Nat) x) (many (String) n) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (let ((many (Maybe $ Nat) canonical)) $ match many (canon-env env $ TVar x) _ ((TVar a) (match many (list-mem-bin atoms a) _ ((BTrue) (Some _ a)) ((BFalse) (None _)))) (else (None _)))
  (match many canonical _
    ((Some _ a) (Cons _ (MkPair _ _ a $ MkPair _ _ x n) acc))
    ((None _) (match many (list-mem-bin atoms x) _ ((BTrue) (Cons _ (MkPair _ _ x $ MkPair _ _ x n) acc)) ((BFalse) acc)))))

(def-fns _ $ (many name-cands : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) (subterm many (List $ Pair (String) (Nat)) ns) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (match many ns _
    ((Nil _) acc)
    ((Cons _ p rest)
      (match many p _
        ((MkPair _ _ n x)
          (let ((many (Bool) skip)) $ match many except _ ((None _) (BFalse)) ((Some _ e) (nat-eq e x)))
          (tail $ name-cands env atoms except rest $ match many skip (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) acc) ((BFalse) (cand-of env atoms x n acc))))))))

(def-fns _ $ (many lit-cands : (many (Env) env) (many (List $ Nat) atoms) (subterm many (List $ LitEntry) ls) (many (List $ Pair (Nat) $ Pair (Nat) (String)) acc) -> (many (List $ Pair (Nat) $ Pair (Nat) (String)) r))
  (match many ls _
    ((Nil _) acc)
    ((Cons _ l rest)
      (match many l _
        ((MkLitEntry x _ s)
          (let ((many (Bool) string)) $ match many s (((Bool) _)) ((SCons c _) (char-is c 34)) ((SNil) (BFalse)))
          (tail $ lit-cands env atoms rest $ match many (or (all-digits s) string) (((List $ Pair (Nat) $ Pair (Nat) (String)) _)) ((BTrue) (cand-of env atoms x s acc)) ((BFalse) acc)))))))

(def-fns _ $ (many best-cand : (many (Nat) a) (subterm many (List $ Pair (Nat) $ Pair (Nat) (String)) cs) (many (Maybe $ Pair (Nat) (String)) best) -> (many (Maybe $ Pair (Nat) (String)) r))
  (match many cs _
    ((Nil _) best)
    ((Cons _ c rest)
      (match many c _
        ((MkPair _ _ a2 xn)
          (match many xn _
            ((MkPair _ _ x _)
              (let ((many (Bool) newer)) $ match many best (((Bool) _)) ((None _) (BTrue)) ((Some _ b) (match many b _ ((MkPair _ _ y _) (nat-lt y x)))))
              (tail $ best-cand a rest $ match many (and (nat-eq a a2) newer) (((Maybe $ Pair (Nat) (String)) _)) ((BTrue) (Some _ xn)) ((BFalse) best)))))))))

(def-fns _ $ (many name-atoms : (many (Env) env) (subterm many (List $ Nat) atoms) (many (List $ Pair (Nat) $ Pair (Nat) (String)) lits) (many (List $ Pair (Nat) $ Pair (Nat) (String)) names) -> (many (Env) r))
  (match many atoms _
    ((Nil _) env)
    ((Cons _ a rest)
      (let ((many (String) fallback)) $ match many (best-cand a names $ None _) (((String) _)) ((Some _ p) (match many p _ ((MkPair _ _ _ nm) nm))) ((None _) (str-cat "_" $ nat-str a)))
      (let ((many (String) n)) $ match many (best-cand a lits $ None _) (((String) _)) ((Some _ p) (match many p _ ((MkPair _ _ _ sp) sp))) ((None _) fallback))
      (tail $ name-atoms (env-name-entry env a n) rest lits names))))

(def-fns _ $ (many plain-atoms : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (match many (is-meta env x) _ ((BTrue) (tail $ plain-atoms env rest)) ((BFalse) (Cons _ x $ notail $ plain-atoms env rest))))))

(def-fns _ $ (many naming : (many (Env) env) (many (List $ Nat) atoms) (many (Maybe $ Nat) except) -> (many (Env) r))
  (match many atoms _
    ((Nil _) env)
    ((Cons _ _ _)
      (let ((many lits)) $ lit-cands env atoms (env-lits env) $ Nil _)
      (let ((many names)) $ name-cands env atoms except (nm-entries _ (scope-names $ env-scope env) (REmpty) $ Nil _) $ Nil _)
      (name-atoms env atoms lits names))))

(def-fns _ $ (many show-t-except : (many (Env) env) (many (Term) t) (many (Maybe $ Nat) except) -> (many (String) s))
  (let ((many c)) $ canon-env env t)
  (rope-str $ show-term c (naming env (plain-atoms env $ term-vars c $ Nil _) except) $ Nil _))

(def-fns _ $ (many show-t : (many (Env) env) (many (Term) t) -> (many (String) s))
  (show-t-except env t $ None _))

(def-fns _ $ (many show-tele-t : (many (Env) env) (many (List $ Entry) es) -> (many (String) s))
  (let ((many ces)) $ canon-env-tele env es)
  (let ((many r) (many bound)) $ show-tele ces (naming env (plain-atoms env $ term-vars-tele ces $ Nil _) $ None _) (Nil _) (BTrue))
  (rope-str r))

(def-fns _ $ (many clash-str : (many (Env) env) (subterm many (Clash) c) -> (many (String) s))
  (match many c _
    ((CText s) s)
    ((CTerm t) (tick $ show-t env t))
    ((CName x) (qname env x))
    ((CCat a b) (str-cat (notail $ clash-str env a) $ notail $ clash-str env b))))

(def-fns _ $ (many show-r : (many (Raw) r) -> (many (String) s))
  (rope-str $ show-raw r))

(def-fns _ $ (many qshow : (many (Env) env) (many (Term) t) -> (many (String) s))
  (tick $ show-t env t))

(def-fns _ $ (many qraw : (many (Raw) r) -> (many (String) s))
  (tick $ show-r r))

(def-fns _ $ (many warned-find : (subterm many (List $ Warned) ws) (many (Nat) x) -> (many (Maybe $ Warned) r))
  (match many ws _
    ((Nil _) (None _))
    ((Cons _ w rest)
      (match many w _
        ((MkWarned y _ _)
          (match many (nat-eq x y) _
            ((BTrue) (Some _ w))
            ((BFalse) (tail $ warned-find rest x))))))))

(def-fns _ $ (many means-entry : (many (Env) env) (many (String) n) (many (Nat) x) -> (many (Bool) r))
  (match many (lookup env n) _
    ((None _) (BFalse))
    ((Some _ y) (match many (canon-env env $ TVar y) _ ((TVar z) (nat-eq z x)) (else (BFalse))))))

(def-fns _ $ (many suppressing : (many (Env) env) (many (Nat) x) (many (Pos) p) (subterm many (List $ Region) rs) -> (many (List $ Said) hits))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest)
      (match many r _ ((MkRegion k n _ _)
        (match many (and (region-covers r p) $ means-entry env n x) _
          ((BTrue) (Cons _ (SaidSilenced k) $ notail $ suppressing env x p rest))
          ((BFalse) (tail $ suppressing env x p rest))))))))

(def-fns _ $ (many warn-use : (many (Env) env) (many (Loc) l) (many (String) what) (many (Term) t) -> (many (Env) r))
  (match many (env-in-extern env) _
    ((BTrue) env)
    ((BFalse)
      (match many (canon-env env t) _
        ((TVar x)
          (match many (warned-find (env-warned env) x) _
            ((None _) env)
            ((Some _ w)
              (let ((many hits)) $ suppressing env x (match many l (((Pos) _)) ((MkLoc _ p) p)) $ env-regions env)
              (match many hits _
                ((Cons _ _ _) (env-set-said env $ list-rev-onto _ hits $ env-said env))
                ((Nil _)
                  (match many w _
                    ((MkWarned _ pl msg)
                      (env-back env $ env-warn-note-at (env-warn-at env l $ str-cat3 what " " $ str-cat3 (qshow env t) ": " msg)
                        pl $ str-cat3 "`;! warn` for " (qshow env t) " is here"))))))))
        (else env)))))

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

(def-fns _ $ (many written : (many (Env) env) (many (Mult) pos) (many (Mult) m) (many (String) what) -> (many (Env) r))
  (error-when env (and (not $ mult-is-many pos) $ mult-is-many m) $ str-cat3 "a " (tick what) " in an erased position is written `erased`"))

; ---- Literals (ASSUMPTIONS 51-53, 60): numerals, characters and strings, interned per program

(def-adts $ (LitKind : -> Type)
  enum
  (many LName : -> (LitKind))
  (many LNumeral : -> (LitKind))
  (many LChar : -> (LitKind)))

(def-fns _ $ (many classify : (many (String) s) -> (many (LitKind) k))
  (match many s _
    ((SNil) (LName))
    ((SCons c rest)
      (match many (all-digits s) _
        ((BTrue) (LNumeral))
        ((BFalse)
          (match many (and (char-is c 35) $ match many rest (((Bool) _)) ((SNil) (BFalse)) ((SCons c2 _) (char-is c2 92))) _
            ((BTrue) (LChar))
            ((BFalse) (LName))))))))

(def-fns _ $ (many parse-nat : (subterm many (String) s) (many (Nat) acc) -> (many (Nat) n))
  (match many s _
    ((SNil) acc)
    ((SCons c rest) (tail $ parse-nat rest $ nat-add (nat-mul 10 acc) $ nat-sub (char-code c) 48))))

(def-fns _ $ (many is-hex : (many (Char) c) -> (many (Bool) r))
  (or (char-between c 48 57) $ or (char-between c 97 102) $ char-between c 65 70))

(def-fns _ $ (many hex-digit : (many (Char) c) -> (many (Nat) d))
  (let ((many n)) $ char-code c)
  (match many (char-between c 48 57) _
    ((BTrue) (nat-sub n 48))
    ((BFalse)
      (match many (char-between c 97 102) _
        ((BTrue) (nat-sub n 87))
        ((BFalse) (nat-sub n 55))))))

(def-fns _ $ (many char-lit-body : (many (String) s) -> (many (String) body))
  (match many s _ ((SNil) (SNil)) ((SCons _ rest) (match many rest _ ((SNil) (SNil)) ((SCons _ rest2) rest2)))))

; The code of #\c, #\space, #\newline, #\tab or #\xHH, or None where the literal is malformed.
(def-fns _ $ (many char-lit-code : (many (String) s) -> (many (Maybe $ Nat) n))
  (let ((many body)) $ char-lit-body s)
  (match many (str-cmp body "space") _
    ((CEq _ _ _) (Some _ 32))
    (else
      (match many (str-cmp body "newline") _
        ((CEq _ _ _) (Some _ 10))
        (else
          (match many (str-cmp body "tab") _
            ((CEq _ _ _) (Some _ 9))
            (else
              (match many body _
                ((SNil) (None _))
                ((SCons c rest)
                  (match many rest _
                    ((SNil) (Some _ $ char-code c))
                    ((SCons h1 rest2)
                      (match many rest2 _
                        ((SNil) (None _))
                        ((SCons h2 rest3)
                          (match many (and (char-is c 120) $ and (is-hex h1) $ and (is-hex h2) $ str-is-empty rest3) _
                            ((BTrue) (Some _ $ nat-add (nat-mul 16 $ hex-digit h1) $ hex-digit h2))
                            ((BFalse) (None _))))))))))))))))

; What is wrong with a literal's spelling, if anything (lib/literal.ml's classify).
(def-fns _ $ (many literal-error : (many (String) s) -> (many (Maybe $ String) r))
  (match many (classify s) _
    ((LName) (None _))
    ((LNumeral)
      (match many s _
        ((SNil) (None _))
        ((SCons c rest)
          (match many (and (char-is c 48) $ not $ str-is-empty rest) _
            ((BTrue) (Some _ $ str-cat s " has a leading zero"))
            ((BFalse) (None _))))))
    ((LChar)
      (match many (char-lit-code s) _
        ((Some _ _) (None _))
        ((None _) (Some _ $ str-cat "malformed character literal " s))))))

(def-fns _ $ (many prelude-id : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Nat) x))
  (match many (lookup env name) _
    ((None _) (values (env-error env $ str-cat "unbound name " $ tick name) $ Zero))
    ((Some _ x) (values env x))))

(def-fns _ $ (many prelude-type : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Term) t))
  (let ((many env2) (many x)) $ prelude-id env name)
  (values env2 $ TApp (TVar x) $ Nil _))

; Whether [ty] applies the prelude's [name] type constructor, found in the prelude's scope however the program
; shadows the name, as lib/elab.ml's nullary finds it.
(def-fns _ $ (many prelude-nullary : (many (Env) env) (many (Term) ty) (many (String) name) -> (many (Bool) b))
  (match many (type-head env ty) _
    ((None _) (BFalse))
    ((Some _ tid)
      (let ((many env2) (many x)) $ prelude-id (env-set-scope env $ env-prelude env) name)
      (nat-eq tid x))))

; The multiplicity a position demands of a value by its type (lib/elab.ml's demanded): a callable head takes
; a Cell or a UniqueFn at unique, and the driver takes an IO value at unique.
(def-fns _ $ (many final-demand : (many (Env) env) (many (Term) ty) -> (many (Mult) m))
  (match many (prelude-nullary env ty "IO") _ ((BTrue) (Once)) ((BFalse) (Many))))

(def-fns _ $ (many mode-demand : (many (Env) env) (many (Term) ty) (many (Bool) final) -> (many (Mult) m))
  (match many final _ ((BTrue) (final-demand env ty)) ((BFalse) (head-demand env ty))))

(let ((many two-dec)) (lt-dec (Zero) 2))
(comptime-match many two-dec (Yes tda2 tdb2 two-positive))
(let ((many two-dec2)) (lt-dec (Succ (Zero)) 2))
(comptime-match many two-dec2 (Yes tea2 teb2 two-above-one))

; The bijective spelling by halving: n is B1 of the spelling of q when n - 1 is 2q, B2 of it when 2q + 1.
(def-fns _ $ (many bin-of-nat : (subterm many (Nat) n) -> (many (Bin) b))
  (match many n _
    ((Zero) (BZ))
    ((Succ n1)
      (match many n1 _
        ((Zero) (B1 $ BZ))
        ((Succ n2)
          (let ((many q) (many r) (erased m) (erased mm) (erased a) (erased p)) (divmod n1 2 two-positive))
          (let ((erased lt)) (lt-weaken q n1 $ divmod-lt n2 2 q r m mm a two-above-one))
          (let ((many b)) (notail $ bin-of-nat (subterm (lt-subterm q n lt)) q))
          (match many r _ ((Zero) (B1 b)) ((Succ _) (B2 b))))))))

(def-fns _ $ (many bin-ctor : (many (Bin) b) -> (many (String) name))
  (match many b _ ((BZ) "BZ") ((B1 _) "B1") ((B2 _) "B2")))

(def-fns _ $ (many bin-term : (subterm many (Bin) b) (many (Env) env) -> (many (Env) r) (many (Term) t))
  (let ((many env2) (many c)) $ prelude-id env $ bin-ctor b)
  (let ((many (Env) env3) (many (List $ Term) args))
    (match many b _
      ((BZ) (values env2 $ Nil _))
      ((B1 b1) (let ((many env3) (many t)) $ notail $ bin-term b1 env2) (values env3 $ Cons _ t $ Nil _))
      ((B2 b1) (let ((many env3) (many t)) $ notail $ bin-term b1 env2) (values env3 $ Cons _ t $ Nil _))))
  (values env3 $ TApp (TVar c) args))

; The bijective base-2 spelling of a number as a term over the prelude's Bin (ASSUMPTIONS 50).
(def-fns _ $ (many nat-bin-term : (many (Nat) n) (many (Env) env) -> (many (Env) r) (many (Term) t))
  (bin-term (bin-of-nat n) env))

; ---- The source spelling of a literal, which a printed Nat, Char or String reads back from
; (lib/ffi_core.ml's lit_char and lit_string, lib/literal.ml's spell). The compile-time printer below spells in
; the language; an emitted printer calls Ffi_core (emit.sl).

(let ((many sixteen-dec)) (lt-dec (Zero) 16))
(comptime-match many sixteen-dec (Yes sda sdb sixteen-positive))

(def-fns _ $ (many hex-rope : (many (Nat) n) -> (many (Rope) r))
  (RChar $ char-of-code $ match many (nat-lt n 10) (((Nat) _)) ((BTrue) (nat-add 48 n)) ((BFalse) (nat-add 87 n))))

; Bare where the reader's word syntax admits the character, hexadecimal otherwise.
(def-fns _ $ (many lit-char-rope : (many (Nat) c) -> (many (Rope) r))
  (match many (nat-eq c 32) _
    ((BTrue) (RStr "#\\space"))
    ((BFalse)
      (match many (nat-eq c 10) _
        ((BTrue) (RStr "#\\newline"))
        ((BFalse)
          (match many (nat-eq c 9) _
            ((BTrue) (RStr "#\\tab"))
            ((BFalse)
              (match many (and (and (nat-lt 32 c) (nat-lt c 127)) $ not $ or (nat-eq c 40) $ or (nat-eq c 41) $ nat-eq c 59) _
                ((BTrue) (rcat (RStr "#\\") $ RChar $ char-of-code c))
                ((BFalse)
                  (let ((many hi) (many lo) (erased dm) (erased dmm) (erased da) (erased dp)) (divmod c 16 sixteen-positive))
                  (rcat3 (RStr "#\\x") (hex-rope hi) $ hex-rope lo))))))))))

; The four escapes the reader unescapes; every other byte stands as itself.
(def-fns _ $ (many escape-char : (many (Char) c) -> (many (Rope) r))
  (let ((many k)) $ char-code c)
  (match many (nat-eq k 34) _
    ((BTrue) (RStr "\\\""))
    ((BFalse)
      (match many (nat-eq k 92) _
        ((BTrue) (RStr "\\\\"))
        ((BFalse)
          (match many (nat-eq k 10) _
            ((BTrue) (RStr "\\n"))
            ((BFalse)
              (match many (nat-eq k 9) _
                ((BTrue) (RStr "\\t"))
                ((BFalse) (RChar c))))))))))

(def-fns _ $ (many str-escape : (subterm many (String) s) -> (many (Rope) r))
  (match many s _
    ((SNil) (REmpty))
    ((SCons c rest) (rcat (escape-char c) $ notail $ str-escape rest))))

(def-fns _ $ (many lit-string-rope : (many (String) s) -> (many (Rope) r))
  (rwrap "\"" (str-escape s) "\""))

(def-fns _ $ (many record-literal : (many (Env) env) (many (String) key) (many (Nat) x) (many (Maybe $ Nat) proof) (many (String) spelling) -> (many (Env) r))
  (let ((many env2)) $ env-set-literals env $ nm-set _ key x $ env-literals env)
  (env-push-lit env2 x proof spelling))

(def-fns _ $ (many lit-lookup : (many (Env) env) (many (String) key) -> (many (Maybe $ Nat) r))
  (match many (nm-get _ key $ env-literals env) _ ((NHit _ _ _ x _) (Some _ x)) ((NMiss _ _ _ _) (None _))))

; Interns a numeral: a Const Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
(def-fns _ $ (many intern-numeral : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Nat) x) (many (Nat) proof))
  (let ((many n)) $ parse-nat key 0)
  (let ((many env1) (many nat-ty)) $ prelude-type env "Nat")
  (let ((many env2) (many x)) $ bind-closed env1 (None _) (None _) (BFalse) (Many) (BExt _ $ PNat n) nat-ty (None _) delegate-id)
  (let ((many env2b) (many numeral)) $ prelude-id env2 "Numeral")
  (let ((many env2c) (many spelled)) $ nat-bin-term n env2b)
  (let ((many pty)) $ TApp (TVar numeral) $ Cons _ spelled $ Cons _ (TVar x) $ Nil _)
  (let ((many env3) (many p)) $ bind-token env2c (None _) (None _) (BFalse) (Erased) pty (None _) delegate-id)
  (values (record-literal env3 key x (Some _ p) key) x p))

(def-fns _ $ (many lit-proof : (subterm many (List $ LitEntry) lits) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (match many lits _
    ((Nil _) (None _))
    ((Cons _ p rest)
      (match many p _
        ((MkLitEntry y proof _) (match many (nat-cmp x y) _ ((CEq _ _ _) proof) (else (tail $ lit-proof rest x))))))))

(def-fns _ $ (many intern-numeral-once : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Nat) x) (many (Nat) proof))
  (match many (lit-lookup env key) _
    ((Some _ x)
      (match many (lit-proof (env-lits env) x) _
        ((Some _ p) (values env x p))
        ((None _) (values env x $ Zero))))
    ((None _) (intern-numeral env key))))

; Interns a numeral or character literal (ASSUMPTIONS 51, 52): a character is (MkChar (MkU8 n p)) over its
; code's numeral, transparent down to the opaque n.
(def-fns _ $ (many intern : (many (Env) env) (many (String) key) (many (LitKind) kind) -> (many (Env) r))
  (match many (lit-lookup env key) _
    ((Some _ _) env)
    ((None _)
      (match many (literal-error key) _
        ((Some _ msg) (env-error env msg))
        ((None _)
          (match many kind _
            ((LNumeral) (let ((many env2) (many x) (many p)) $ intern-numeral env key) env2)
            ((LChar)
              (let ((many (Nat) code)) $ match many (char-lit-code key) _ ((None _) 0) ((Some _ n) n))
              (let ((many env2) (many num) (many np)) $ intern-numeral-once env $ nat-str code)
              (let ((many env2b) (many lt-id)) $ prelude-id env2 "Lt")
              (let ((many env2c) (many modulus)) $ prelude-id env2b "u8-modulus")
              (let ((many env3) (many lt)) (bind-token env2c (None _) (None _) (BFalse) (Erased)
                                          (TApp (TVar lt-id) $ Cons _ (TVar num) $ Cons _ (TVar modulus) $ Nil _) (None _) delegate-id))
              (let ((many env3b) (many mk-char)) $ prelude-id env3 "MkChar")
              (let ((many env3c) (many mk-u8)) $ prelude-id env3b "MkU8")
              (let ((many rule)) $ TApp (TVar mk-char) $ Cons _ (TApp (TVar mk-u8) $ Cons _ (TVar num) $ Cons _ (TVar lt) $ Nil _) $ Nil _)
              (let ((many env3d) (many char-ty)) $ prelude-type env3c "Char")
              (let ((many env4) (many x)) $ bind-closed env3d (None _) (None _) (BFalse) (Many) (BExt _ $ PNat code) char-ty (Some _ rule) delegate-id)
              (record-literal env4 key x (Some _ np) $ rope-str $ lit-char-rope code))
            ((LName) env)))))))

; Interns a string (ASSUMPTIONS 60): its characters, holding no proof.
(def-fns _ $ (many string-key : (many (String) s) -> (many (String) key))
  (rope-str $ RCat (RChar #\x22) $ RStr s))

(def-fns _ $ (many intern-string : (many (Env) env) (many (String) key) -> (many (Env) r))
  (match many (lit-lookup env key) _
    ((Some _ _) env)
    ((None _)
      (let ((many body)) $ match many key (((String) _)) ((SNil) (SNil)) ((SCons _ rest) rest))
      (let ((many env1) (many str-ty)) $ prelude-type env "String")
      (let ((many env2) (many x)) $ bind-closed env1 (None _) (None _) (BFalse) (Many) (BExt _ $ PStr body) str-ty (None _) delegate-id)
      (record-literal env2 key x (None _) $ rope-str $ lit-string-rope body))))

(def-fns _
  ((many intern-literals : (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r))
    (match many raw _
      ((RAtom _ s) (env-set-scope (intern env s $ classify s) $ env-scope env))
      ((RString _ s) (env-set-scope (intern-string env $ string-key s) $ env-scope env))
      ((RList _ items) (tail $ intern-literals-list items env))))
  ((many intern-literals-list : (subterm many (List $ Raw) rs) (many (Env) env) -> (many (Env) r))
    (match many rs _
      ((Nil _) env)
      ((Cons _ r rest) (tail $ intern-literals-list rest $ notail $ intern-literals r env)))))

; The entry an atom names: a literal's, or the newest of that name in scope; id zero, which nothing binds,
; stands for an error already recorded.
(def-fns _ $ (many var : (many (Env) env) (many (String) n) -> (many (Env) r) (many (Nat) x))
  (match many (literal-error n) _
    ((Some _ msg) (values (env-error env msg) $ Zero))
    ((None _)
      (match many (classify n) _
        ((LName)
          (match many (lookup env n) _
            ((Some _ x) (values env x))
            ((None _) (values (env-error env $ str-cat "unbound name " $ tick n) $ Zero)))) (else (match many (lit-lookup env n) _ ((Some _ x) (values env x)) ((None _) (values (env-error env $ str-cat3 "literal " n " outside a top-level form") $ Zero))))))))

(def-fns _ $ (many var-of-raw : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Nat) x))
  (match many raw _
    ((RAtom _ s) (var env s))
    ((RString _ s)
      (match many (lit-lookup env $ string-key s) _
        ((Some _ x) (values env x))
        ((None _) (values (env-error env "string literal outside a top-level form") $ Zero))))
    ((RList _ _) (values (env-error env $ str-cat3 "expected " what $ str-cat ", got " $ tick $ rope-str $ show-raw raw) $ Zero))))

; A name read through its alias (ASSUMPTIONS 78), which must resolve to a variable.
(def-fns _ $ (many named : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ var-of-raw env raw what)
  (match many (canon-env env2 $ TVar x) _
    ((TVar y) (values env2 y))
    ((TBound _) (values env2 x)) ((TErr _) (values env2 x)) (else (values (env-error env2 $ str-cat3 (qshow env2 $ TVar x) " is not " what) x))))


; ---- Source telescopes (section 30), with erased proofs placing every raw they hold inside the raw list it
; was read from; the elaborator recurses on those raws.

; b is a, or a strict subterm of a.
(def-adts $ (Within : ((List $ Raw) b) ((List $ Raw) a) -> Type)
  enum
  (many WHere : (erased (List $ Raw) a) -> (Within a a))
  (many WIn : (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm (List $ Raw) b (List $ Raw) a) p) -> (Within b a)))

(def-fns _ $ (erased in-within : (erased Type A) (erased A x) (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm A x (List $ Raw) b) p) (erased (Within b a) w) -> (erased (Subterm A x (List $ Raw) a) q))
  (match erased w _
    ((WHere _) p)
    ((WIn _ _ s) (subterm-trans p s))))

(def-fns _ $ (erased within-in : (erased (List $ Raw) c) (erased (List $ Raw) b) (erased Type A) (erased A x) (erased (Within c b) w) (erased (Subterm (List $ Raw) b A x) p) -> (erased (Subterm (List $ Raw) c A x) q))
  (match erased w _
    ((WHere _) p)
    ((WIn _ _ s) (subterm-trans s p))))

(def-fns _ $ (erased within-step : (erased (List $ Raw) c) (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm (List $ Raw) c (List $ Raw) b) p) (erased (Within b a) w) -> (erased (Within c a) q))
  (WIn _ _ $ in-within (List $ Raw) c b a p w))

; A body's final expression, placed in the body's root, or none.
(def-adts $ (Final : ((List $ Raw) root) -> Type)
  enum
  (many FinalNone : (erased (List $ Raw) root) -> (Final root))
  (many FinalIs : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (Final root)))

; A raw strictly inside the list root.
(def-adts $ (Sub : ((List $ Raw) root) -> Type)
  enum
  (many MkSub : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (Sub root)))

(def-fns _ $ (many subs-of : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) -> (many (List $ Sub root) r))
  (match many items _
    ((Nil _) (Nil _))
    ((Cons _ t rest)
      (Cons _ (MkSub _ t $ in-within (Raw) t items root (prove-subterm t items) w)
        $ notail $ subs-of rest _ $ within-step rest items root (prove-subterm rest items) w))))

(def-fns _ $ (many subs-all : (many (List $ Raw) items) -> (many (List $ Sub items) r))
  (subs-of items _ $ WHere items))

; A telescope written in a bracket of its own, and what follows it: the entries are the bracket's items, so
; each is two hops below the root -- inside the bracket, which is inside the root.
(def-fns _ $ (many bracket-parts : (subterm many (List $ Raw) args) (many (Env) env) (many (String) what) ->
    (many (Env) r) (many (List $ Sub args) entries) (many (List $ Raw) after) (erased (Within after args) wa))
  (match many args _
    ((Nil _) (values (env-error env what) (Nil _) args (WHere args)))
    ((Cons _ braw after)
      (let ((erased wa)) $ within-step after args args (prove-subterm after args) (WHere args))
      (let ((many env1) (many entries))
        (match many braw (((Env) _) ((List $ Sub args) es))
          ((RList _ items)
            (values env $ subs-of items _ $ WIn _ _ $ subterm-trans (prove-subterm items braw) (prove-subterm braw args)))
          (else (values (env-error env what) (Nil _)))))
      (values env1 entries after wa))))

; A hop budget: a function that hands its whole raw to another spends one step (see the elaborator block).
(def-adts $ (Steps : ((Nat) n) -> Type)
  enum
  (many SZ : -> (Steps $ Zero))
  (many SS : (erased (Nat) n) (many (Steps n) k) -> (Steps $ Succ n)))
(let ((many one-step)) $ SS _ $ SZ)
(let ((many two-steps)) $ SS _ one-step)

(def-adts
  ((SrcEntry : ((List $ Raw) root) -> Type)
    enum
    (many MkSrcEntry : (erased (List $ Raw) root) (many (Bool) is-sub) (many (Maybe $ Mult) mult) (many (Maybe $ SrcSg root) sg) (many (String) name) (many (Maybe $ String) place) (many (Pos) site) -> (SrcEntry root)))
  ((SrcSg : ((List $ Raw) root) -> Type)
    enum
    (many SrcTy : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (SrcSg root))
    (many SrcIs : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (SrcSg root))))

; Whether every binder carries a type or an is clause, so a let's binders are a telescope (SUGAR.md 6).
(def-fns _ $ (many all-have-sg : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) -> (many (Bool) r))
  (match many es _
    ((Nil _) (BFalse))
    ((Cons _ e rest)
      (match many e _
        ((MkSrcEntry _ _ _ ssg _ _ _)
          (match many ssg _
            ((None _) (BFalse))
            ((Some _ _) (match many rest _ ((Nil _) (BTrue)) ((Cons _ _ _) (tail $ all-have-sg _ rest))))))))))

(def-fns _ $ (many at-tail : (many (Env) env) (many (List $ Raw) xs) -> (many (Maybe $ String) r))
  (match many xs _
    ((Nil _) (None _))
    ((Cons _ mark rest)
      (match many rest _
        ((Nil _) (None _))
        ((Cons _ target more)
          (match many (and (is-mark env mark $ MkAt) $ list-is-empty _ more) _
            ((BFalse) (None _))
            ((BTrue) (raw-atom target))))))))

(def-fns _ $ (many entries-of-names : (subterm many (List $ Raw) names) (many (Env) env) (many (Bool) is-sub) (many (Maybe $ Mult) mult) (many (Pos) site) (erased (List $ Raw) root) (many (Raw) ty) (erased (Subterm (Raw) ty (List $ Raw) root) pty) -> (many (List $ SrcEntry root) r))
  (match many names _
    ((Nil _) (Nil _))
    ((Cons _ n rest)
      (let ((many place)) $ at-tail env rest)
      (let ((many more)) $ match many place (((List $ SrcEntry root) _))
        ((Some _ _) (Nil _))
        ((None _) (notail $ entries-of-names rest env is-sub mult site _ ty pty)))
      (Cons _ (MkSrcEntry _ is-sub mult (Some _ $ SrcTy _ ty pty) (raw-name n) place site) more))))

(def-fns _ $ (many parse-entry : (many (Env) env) (many (Raw) raw) (erased (List $ Raw) root) (erased (Subterm (Raw) raw (List $ Raw) root) pr) -> (many (List $ SrcEntry root) r))
  (match many raw _
    ((RList epos items0)
      (let ((erased w0)) $ WIn _ _ $ subterm-trans (prove-subterm items0 raw) pr)
      (let ((many (Bool) sub3) (many (List $ Raw) items1) (erased (Within items1 root) w1))
        (match many items0 _
          ((Nil _) (values (BFalse) items0 w0))
          ((Cons _ t rest)
            (match many (is-mark env t $ MkSubterm) (((Bool) _) ((List $ Raw) l) ((Within l root) w))
              ((BTrue) (values (BTrue) rest $ within-step _ _ _ (prove-subterm rest items0) w0))
              ((BFalse) (values (BFalse) items0 w0))))))
      (let ((many (Maybe $ Mult) mult) (many (List $ Raw) items) (erased (Within items root) w2))
        (match many items1 _
          ((Nil _) (values (None _) items1 w1))
          ((Cons _ t rest)
            (match many (mult-of env t) (((Maybe $ Mult) _) ((List $ Raw) l) ((Within l root) w))
              ((None _) (values (None _) items1 w1))
              ((Some _ m) (values (Some _ m) rest $ within-step _ _ _ (prove-subterm rest items1) w1))))))
      (match many items _
        ((Nil _) (Nil _))
        ((Cons _ first rest)
          (let ((erased pf)) $ in-within _ _ _ _ (prove-subterm first items) w2)
          (match many rest _
            ((Nil _) (Cons _ (MkSrcEntry _ sub3 mult (None _) (raw-name first) (None _) epos) $ Nil _))
            ((Cons _ second rest2)
              (match many rest2 _
                ((Cons _ third rest3)
                  (match many (and (is-mark env second $ MkIs) $ or (list-is-empty _ rest3) $ is-some _ $ at-tail env rest3) _
                    ((BTrue) (Cons _ (MkSrcEntry _ sub3 mult (Some _ $ SrcIs _ first pf) (raw-name third) (at-tail env rest3) epos) $ Nil _))
                    ((BFalse) (entries-of-names rest env sub3 mult epos _ first pf))))
                ((Nil _) (entries-of-names rest env sub3 mult epos _ first pf)))))))) (else (Nil $ SrcEntry root))))

; The items before the arrow, and those after it, which sit within the root.
(def-fns _ $ (many split-arrow : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) (many (Env) env) -> (many (List $ Sub root) before) (many (List $ Raw) after) (erased (Within after root) wa))
  (match many items _
    ((Nil _) (values (Nil _) items w))
    ((Cons _ t rest)
      (let ((erased wr)) $ within-step _ _ _ (prove-subterm rest items) w)
      (match many (is-mark env t $ MkArrow) _
        ((BTrue) (values (Nil _) rest wr))
        ((BFalse)
          (let ((many before) (many after) (erased wa)) $ notail $ split-arrow rest _ wr env)
          (values (Cons _ (MkSub _ t $ in-within (Raw) t items root (prove-subterm t items) w) before) after wa))))))

; Leading annotation tokens from the marks given, in any order; returns the flags for absurd/newtype and extern.
(def-fns _ $ (many take-marks : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) (many (Env) env) (many (MarkK) first) (many (MarkK) second) -> (many (Bool) has-first) (many (Bool) has-second) (many (List $ Raw) rest) (erased (Within rest root) wr))
  (match many items _
    ((Nil _) (values (BFalse) (BFalse) items w))
    ((Cons _ t more)
      (let ((erased wm)) $ within-step _ _ _ (prove-subterm more items) w)
      (match many (is-mark env t first) _
        ((BTrue)
          (let ((many f) (many s) (many rest) (erased wr)) $ notail $ take-marks more _ wm env first second)
          (values (BTrue) s rest wr))
        ((BFalse)
          (match many (is-mark env t second) _
            ((BTrue)
              (let ((many f) (many s) (many rest) (erased wr)) $ notail $ take-marks more _ wm env first second)
              (values f (BTrue) rest wr))
            ((BFalse) (values (BFalse) (BFalse) items w))))))))

; ---- Constructors, Matchables and shapes (sections 17, 19, 38)

(def-fns _ $ (many adt-of : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Adt) r))
  (let ((erased a) (many blk)) $ env-block env x)
  (match many blk _
    ((None _) (None _))
    ((Some _ b) (match many b _ ((BMat _ adt) (Some _ adt)) (else (None $ Adt))))))

(def-fns _ $ (many ctor-of : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Ctor) r))
  (let ((erased a) (many blk)) $ env-block env x)
  (match many blk _
    ((None _) (None _))
    ((Some _ b) (match many b _ ((BCtorFn _ c) (Some _ c)) (else (None $ Ctor))))))

(def-fns _ $ (many ctor-type : (many (Env) env) (many (Nat) c) -> (many (List $ Entry) tele) (many (Term) ret))
  (match many (type-of env c) _
    ((TValCtor tele ret) (values tele ret)) ((TErr m) (values (Nil _) $ TErr m)) (else (values (Nil $ Entry) $ TErr "not a constructor"))))

(def-fns _ $ (many tid-of : (many (Env) env) (many (Nat) c) -> (many (Nat) tid))
  (let ((many tele) (many ret)) $ ctor-type env c)
  (match many (type-head env ret) _ ((None _) (Zero)) ((Some _ t) t)))

(def-adts $ (MatchInfo : -> Type)
  enum
  (many MkMatchInfo : (many (Nat) mid) (many (Disc) disc) (many (List $ MCtor) ctors) (many (Nat) rank) -> (MatchInfo)))

; A match that dispatches at runtime reads its Matchable's value: stamped in where the entry is Const, else
; read from a non-erased entry still bound (ASSUMPTIONS 139).
(def-fns _ $ (many readable : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (or (is-some _ $ adt-of env x) $ and (mult-is-many $ entry-mult-of env x) $ list-mem-bin (env-objects env) x))

; Of the entries one opened group holds, the record keeps the best-ranked: one whose ADT the elaborator sees,
; then a readable one, then any.
(def-fns _ $ (many matchable-rank : (many (Env) env) (many (Nat) x) -> (many (Nat) r))
  (match many (adt-of env x) _
    ((Some _ _) 0)
    ((None _) (match many (readable env x) _ ((BTrue) 1) ((BFalse) 2)))))

(def-fns _ $ (many held-needs-many : (many (Env) env) (many (Nat) tid) (many (Nat) mid) -> (many (Env) r))
  (error-unless env (readable env mid) $ str-cat3 "the `Matchable` for " (qname env tid) " is erased or out of scope, so a non-erased match cannot take a value of it apart"))

; The opened Matchable for a type, at most one (merge-opens): among the objects the index names for it, the
; first whose canonical type confirms it.
(def-fns _ $ (many find-matchable-in : (subterm many (List $ Opened) opens) (many (Env) env) (many (Nat) tid) (many (List $ Nat) cands) -> (many (Maybe $ MatchInfo) r))
  (match many opens _
    ((Nil _) (None _))
    ((Cons _ o rest)
      (let ((many x)) $ opened-x o)
      (match many (list-mem-bin cands x) _
        ((BFalse) (tail $ find-matchable-in rest env tid cands))
        ((BTrue)
          (match many (type-of env x) _
            ((TMatchable d _ _ t cs)
              (match many t (((Maybe $ MatchInfo) _))
                ((TVar t2)
                  (match many (nat-cmp t2 tid) (((Maybe $ MatchInfo) _))
                    ((CEq _ _ _) (Some _ $ MkMatchInfo x d cs $ matchable-rank env x))
                    (else (tail $ find-matchable-in rest env tid cands))))
                (else (tail $ find-matchable-in rest env tid cands))))
            (else (tail $ find-matchable-in rest env tid cands))))))))


; The anonymous Coercible proof def-fns minted for a delegating function g (section 38).
(def-fns _ $ (many find-delegate : (subterm many (List $ Nat) objects) (many (Env) env) (many (Nat) g) -> (many (Maybe $ Nat) r))
  (match many objects _
    ((Nil _) (None _))
    ((Cons _ x rest)
      (let ((many (Bool) hit))
        (match many (type-of env x) _
          ((TApp h args)
            (match many (list-nth _ args 2) (((Bool) _))
              ((NthMiss _ _ _ _) (BFalse))
              ((NthHit _ _ _ t _)
                (match many t (((Bool) _))
                  ((TVar g2) (and (and (term-eq h $ TVar delegate-id) $ nat-eq (list-length _ args) 6) $ and (nat-eq g2 g) $ match many (env-entry-name env x) (((Bool) _)) ((None _) (BTrue)) ((Some _ _) (BFalse)))) (else (BFalse)))))) (else (BFalse))))
      (match many hit _
        ((BTrue) (Some _ x))
        ((BFalse) (tail $ find-delegate rest env g))))))

; A Matchable's constructors, each with its phantom marker, id and number of many fields (section 38).
(def-adts $ (CShape : -> Type)
  enum
  (many MkCShape : (many (Mult) m) (many (Nat) c) (many (Nat) arity) -> (CShape)))

(def-fns _ $ (many shapes : (subterm many (List $ MCtor) ctors) (many (Env) env) -> (many (List $ CShape) r))
  (match many ctors _
    ((Nil _) (Nil _))
    ((Cons _ mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let ((many c)) $ term-var t)
          (let ((many tele) (many ret)) $ ctor-type env c)
          (Cons _ (MkCShape m c $ many-count tele) $ notail $ shapes rest env))))))

(def-fns _ $ (many non-phantom : (subterm many (List $ CShape) ss) -> (many (List $ CShape) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ s rest)
      (match many s _
        ((MkCShape m _ _) (match many m _ ((Many) (Cons _ s $ notail $ non-phantom rest))
                                          ((Once) (Cons _ s $ notail $ non-phantom rest)) ((Erased) (tail $ non-phantom rest))))))))

(def-fns _ $ (many shape-index : (subterm many (List $ CShape) ss) (many (Nat) c) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (match many ss _
    ((Nil _) (None _))
    ((Cons _ s rest)
      (match many s _
        ((MkCShape _ c2 _) (match many (nat-cmp c c2) _ ((CEq _ _ _) (Some _ i)) (else (tail $ shape-index rest c $ Succ i))))))))

; A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only.
(def-fns _ $ (many discriminant : (many (List $ CShape) ss) (many (Nat) c) -> (many (Nat) r))
  (match many (shape-index (non-phantom ss) c 0) _ ((None _) 0) ((Some _ i) i)))

(def-fns _ $ (many tagged-of : (many (Disc) disc) (many (List $ CShape) ss) -> (many (Bool) r))
  (match many disc _
    ((DUnion) (BFalse))
    ((DEnum) (nat-lt 1 $ list-length _ $ non-phantom ss))))

(def-fns _ $ (many marker : (subterm many (List $ MCtor) ctors) (many (Nat) c) -> (many (Mult) m))
  (match many ctors _
    ((Nil _) (Many))
    ((Cons _ mc rest)
      (match many mc _
        ((MkMCtor m t)
          (match many t _
            ((TVar c2) (match many (nat-cmp c c2) _ ((CEq _ _ _) m) (else (tail $ marker rest c)))) (else (tail $ marker rest c))))))))



; The wrapping constructor of a type of newtype shape (section 38), if any.
(def-fns _ $ (many wrappers : (subterm many (List $ CShape) ss) -> (many (List $ Nat) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ s rest)
      (match many s _
        ((MkCShape m c n)
          (match many (and (mult-is-many m) $ nat-eq n 1) _
            ((BTrue) (Cons _ c $ notail $ wrappers rest))
            ((BFalse) (tail $ wrappers rest))))))))

(def-fns _ $ (many others-bare : (subterm many (List $ CShape) ss) (many (Nat) w) -> (many (Bool) r))
  (match many ss _
    ((Nil _) (BTrue))
    ((Cons _ s rest)
      (match many s _
        ((MkCShape m c n)
          (and (or (not $ mult-is-many m) $ or (nat-eq c w) $ nat-is-zero n)
            $ notail $ others-bare rest w))))))

(def-fns _ $ (many wrapper : (many (Disc) disc) (many (List $ CShape) ss) -> (many (Maybe $ Nat) r))
  (match many (wrappers ss) _
    ((Nil _) (None _))
    ((Cons _ w rest)
      (match many rest _
        ((Cons _ _ _) (None _))
        ((Nil _)
          (match many (and (not $ tagged-of disc ss) $ others-bare ss w) _
            ((BTrue) (Some _ w))
            ((BFalse) (None _))))))))

(def-fns _ $ (many find-newtype-in : (subterm many (List $ Opened) opens) (many (Env) env) (many (Nat) c) (many (List $ Nat) cands) -> (many (Maybe $ Nat) r))
  (match many opens _
    ((Nil _) (None _))
    ((Cons _ o rest)
      (let ((many x)) $ opened-x o)
      (let ((many found))
        (match many (list-mem-bin cands x) (((Bool) _))
          ((BFalse) (BFalse))
          ((BTrue)
            (match many (type-of env x) (((Bool) _))
              ((TMatchable d nt _ _ cs)
                (match many nt (((Bool) _))
                  ((BFalse) (BFalse))
                  ((BTrue) (match many (wrapper d $ shapes cs env) (((Bool) _)) ((None _) (BFalse)) ((Some _ w) (nat-eq w c))))))
              (else (BFalse))))))
      (match many found _ ((BTrue) (Some _ x)) ((BFalse) (tail $ find-newtype-in rest env c cands))))))

(def-fns _ $ (many find-newtype : (many (Env) env) (many (Nat) c) -> (many (Maybe $ Nat) r))
  (find-newtype-in (env-opens env) env c $ index-of c $ env-index env))

(def-fns _ $ (many cshape-arities : (subterm many (List $ CShape) ss) -> (many (List $ Nat) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ s rest) (match many s _ ((MkCShape _ _ n) (Cons _ n $ notail $ cshape-arities rest))))))

(def-fns _ $ (many ctor-records : (subterm many (List $ CShape) ss) (many (Env) env) (many (Nat) index) (many (Bool) tagged) (many (Maybe $ ExtType) ext) (many (List $ Nat) shape) (many (Bool) nt) -> (many (List $ Ctor) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ s rest)
      (match many s _
        ((MkCShape _ c n) (Cons _ (MkCtor (name-of env c) c index n tagged ext shape nt) $ notail $ ctor-records rest env (Succ index) tagged ext shape nt))))))

; The ADT a Matchable's type describes (section 17): the non-phantom constructors at their discriminants.
(def-fns _ $ (many mint-adt : (many (Env) env) (many (Nat) tid) (many (Disc) disc) (many (List $ CShape) ss) (many (Maybe $ ExtType) ext) (many (Bool) nt) -> (many (Adt) r))
  (let ((many tagged)) $ tagged-of disc ss)
  (MkAdt (name-of env tid) tagged (ctor-records (non-phantom ss) env 0 tagged ext (cshape-arities $ non-phantom ss) nt) ext nt))

(def-fns _ $ (many alias-target : (many (Env) env) (many (Nat) x) -> (many (Nat) r))
  (match many (idmap-get _ x $ env-aliases env) _ ((Hit _ _ _ t _) t) ((Miss _ _ _ _) x)))

; A variable in a non-erased position: a Const entry's value embedded with its entry (section 34), or a
; Dyn entry's place in the frames the code binds.
(def-fns _ $ (many var-code : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) x) -> (many (Code ctx many-one) r))
  (match many (is-const env x) _
    ((BTrue) (CConst _ x))
    ((BFalse)
      (match many (mem-dec x ctx) _
        ((Some _ p) (CVar _ x p))
        ((None _) (CError _ many-one $ str-cat "internal: not bound at runtime: " $ name-of env x))))))

(def-fns _ $ (many matchable-code : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) pos) (many (Nat) x) -> (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) r))
  (match many pos _
    ((Erased) (CErased _ $ Cons _ pos $ Nil _))
    ((Many) (var-code env ctx x))
    ((Once) (recast _ (Cons _ (Once) $ Nil _) many-one (MsManyOnce _ _ $ MsNil) $ var-code env ctx x))))

; A match on an ADT the elaborator can see reads no Matchable at runtime (section 17); one on a held
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

(def-fns _ $ (many fact-of : (many (Env) env) (many (Sg) sg) -> (many (Term) ty) (many (Maybe $ Term) rule))
  (match many sg _
    ((SgTy t) (values t $ None _))
    ((SgIs t ty) (values ty $ Some _ t))))

(def-fns _ $ (many proof-type : (many (Nat) ctor) (many (List $ Term) args) -> (many (Term) t))
  (TApp (TVar ctor) args))

(def-fns _ $ (many nth-term : (many (List $ Term) ts) (many (Nat) i) -> (many (Term) t))
  (match many (list-nth _ ts i) _ ((NthMiss _ _ _ _) (TErr "missing argument")) ((NthHit _ _ _ t _) t)))

; Values for binders, many ones from the list in order, erased ones the token.
(def-fns _ $ (many non-erased : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Nat) r))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ x rest)
      (match many (entry-mult-of env x) _
        ((Many) (Cons _ x $ notail $ non-erased rest env))
        ((Once) (Cons _ x $ notail $ non-erased rest env))
        ((Erased) (tail $ non-erased rest env))))))

(def-fns _ $ (many ress-of : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Res) r))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (Cons _ (res-of env x) $ notail $ ress-of rest env))))

(def-fns _ $ (many tvars-rev : (subterm many (List $ Nat) ids) (many (List $ Term) acc) -> (many (List $ Term) r))
  (match many ids _
    ((Nil _) acc)
    ((Cons _ x rest) (tail $ tvars-rev rest $ Cons _ (TVar x) acc))))

(def-fns _ $ (many under-list : (subterm many (List $ Mult) ms) (many (Mult) pos) -> (many (List $ Mult) r))
  (match many ms _
    ((Nil _) (Nil _))
    ((Cons _ m rest) (Cons _ (under pos m) $ notail $ under-list rest pos))))

(def-fns _ $ (many all-erased : (subterm many (List $ Mult) ms) -> (many (List $ Mult) r))
  (match many ms _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (Erased) $ notail $ all-erased rest))))

(def-fns _ $ (many no-code : (erased (List $ List $ Nat) ctx) -> (many (Code ctx many-one) c))
  (CError _ many-one "no value"))

; Binds fresh ids for the many returns and keeps those the position takes many (ASSUMPTIONS 39): the ids
; first, then each one's place in the frame they form, then the code referring to them there.
(def-fns _ $ (many fresh-bound : (subterm many (List $ Mult) rets) (many (Env) env) -> (many (Env) r) (many (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk))
  (match many rets _
    ((Nil _) (values env (Nil _) (PkNil _)))
    ((Cons _ m rest)
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
          (values env3 (Cons _ t bound) (PkOnce _ rest t bound bpk)))))))

(def-fns _ $ (many kept-of : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) frame) (subterm many (List $ Mult) expect) (many (List $ Mult) rets) (erased (Lockstep (Mult) (Mult) expect rets) lock) (erased (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk) (many (List $ AtIn frame) ats) (erased (Lockstep (Nat) (AtIn frame) bound ats) lk) ->
    (many (List $ Code (Cons (List (Nat)) frame ctx) many-one) kept) (erased (Picked (Code (Cons (List (Nat)) frame ctx) many-one) expect kept) kpk))
  (match many expect _
    ((Nil _) (values (Nil _) (PkNil _)))
    ((Cons _ m rest)
      (let-match erased lock (LsCons x y m0 rm0 rest0 rrest0 lp))
      (let-match many rets (Cons b rm rrest))
      (match many rm _
        ((Erased)
          (let-match erased bpk (PkErased tb rr bb bp))
          (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp ats lk)
          (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) missing)) $ no-code _)
          (match many m _
            ((Erased) (values kept (PkErased _ rest kept kpk)))
            ((Many) (values (Cons _ missing kept) (PkMany _ rest missing kept kpk)))
            ((Once) (values (Cons _ missing kept) (PkOnce _ rest missing kept kpk)))))
        ((Many)
          (let-match erased bpk (PkMany tb rr t bb bp))
          (let-match erased lk (LsCons tc td t0 a0 bb0 arest0 lq))
          (let-match many ats (Cons c at3 arest))
          (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp arest lq)
          (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) code)) $ match many at3 _ ((MkAtIn _ z p) (CVar _ z $ MHere _ _ _ p)))
          (match many m _
            ((Many) (values (Cons _ code kept) (PkMany _ rest code kept kpk)))
            ((Once) (values (Cons _ code kept) (PkOnce _ rest code kept kpk)))
            ((Erased) (values kept (PkErased _ rest kept kpk)))))
        ((Once)
          (let-match erased bpk (PkOnce tb rr t bb bp))
          (let-match erased lk (LsCons tc td t0 a0 bb0 arest0 lq))
          (let-match many ats (Cons c at3 arest))
          (let ((many kept) (erased kpk)) $ notail $ kept-of ctx frame rest rrest lp _ bp arest lq)
          (let ((many (Code (Cons (List (Nat)) frame ctx) many-one) code)) $ match many at3 _ ((MkAtIn _ z p) (CVar _ z $ MHere _ _ _ p)))
          (match many m _
            ((Many) (values (Cons _ code kept) (PkMany _ rest code kept kpk)))
            ((Once) (values (Cons _ code kept) (PkOnce _ rest code kept kpk)))
            ((Erased) (values kept (PkErased _ rest kept kpk)))))))))

(def-fns _ $ (many projection : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (List $ Mult) rets) (erased (Lockstep (Mult) (Mult) expect rets) lock) (many (Env) env) ->
    (many (Env) r) (many (List $ Nat) bound) (erased (Picked (Nat) rets bound) bpk) (many (List $ Code (Cons (List (Nat)) bound ctx) many-one) kept) (erased (Picked (Code (Cons (List (Nat)) bound ctx) many-one) expect kept) kpk))
  (let ((many env2) (many bound) (erased bpk)) $ fresh-bound rets env)
  (let ((many ats) (erased lk)) $ at-ins bound)
  (let ((many kept) (erased kpk)) $ kept-of ctx bound expect rets lock bound bpk ats lk)
  (values env2 bound bpk kept kpk))

(def-fns _ $ (many mark-words : (subterm many (List $ Nat) ids) (many (Env) env) (many (Bool) temporary) -> (many (Env) r))
  (match many ids _ ((Nil _) env) ((Cons _ x xs) (tail $ mark-words xs (mark-word env x temporary) temporary))))

(def-fns _ $ (many at-in-frame : (subterm many (List $ Nat) ids) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (match many ids _
    ((Nil _) (None _))
    ((Cons _ x rest) (match many (at-equal env p $ TVar x) _ ((BTrue) (Some _ x)) ((BFalse) (tail $ at-in-frame rest env p))))))

(def-fns _ $ (many at-in-frames : (subterm many (List $ List $ Nat) ctx) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (match many ctx _
    ((Nil _) (None _))
    ((Cons _ frame rest) (match many (at-in-frame frame env p) _ ((Some _ x) (Some _ x)) ((None _) (tail $ at-in-frames rest env p))))))

(def-fns _ $ (many at-constant : (subterm many (List $ Nat) ids) (many (Env) env) (many (Term) p) -> (many (Maybe $ Nat) r))
  (match many ids _
    ((Nil _) (None _))
    ((Cons _ x rest)
      (match many (and (is-const env x) $ and (mult-is-many $ entry-mult-of env x) $ at-equal env p $ TVar x) _
        ((BTrue) (Some _ x)) ((BFalse) (tail $ at-constant rest env p))))))

(def-fns _ $ (many location-var : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Term) p) -> (many (Env) r) (many (Nat) x))
  (let ((many direct)) $ match many p (((Maybe $ Nat) _))
    ((TVar x) (match many (and (mult-is-many $ entry-mult-of env x) $ or (is-const env x) $ is-some _ $ mem-dec x ctx) _ ((BTrue) (Some _ x)) ((BFalse) (None _))))
    (else (None _)))
  (let ((many inframe)) $ match many direct (((Maybe $ Nat) _)) ((Some _ _) direct) ((None _) (at-in-frames ctx env p)))
  (let ((many found)) $ match many inframe (((Maybe $ Nat) _)) ((Some _ _) inframe) ((None _) (at-constant (env-words env) env p)))
  (match many found _ ((Some _ x) (values env x)) ((None _) (values (env-error env $ str-cat "no caller word for `at` " $ qshow env p) 0))))

(def-fns _ $ (many physical-mults : (subterm many (List $ Entry) tele) -> (many (List $ Mult) ms))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (Cons _ (match many (entry-place e) (((Mult) _)) ((Some _ _) (Erased)) ((None _) (entry-mult e))) $ notail $ physical-mults rest))))

(def-fns _ $ (many project-code : (many (List $ List $ Nat) ctx) (many (Env) env) (many (List $ Mult) input) (many (List $ Mult) output) (many (Code ctx input) code) -> (many (Env) r) (many (Code ctx output) c))
  (match many (lockstep-dec _ _ output input) _
    ((LdNo _ _ _ _) (values (env-error env "internal: return projection size") $ CError _ output "projection"))
    ((LdYes _ _ _ _ lk)
      (let ((many env2) (many ids) (erased pk) (many kept) (erased kp)) $ projection ctx output input lk env)
      (values env2 $ CLet _ input _ ids pk code $ CValues _ output kept kp))))

(def-fns _ $ (many result-codes : (subterm many (List $ Mult) expect) (many (List $ Entry) tele) (many (List $ Nat) ids) (many (List $ Term) args) (many (Env) env) (many (List $ List $ Nat) ctx) ->
    (many (Env) r) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) expect codes) pk))
  (match many expect _
    ((Nil _) (values env (Nil _) $ PkNil _))
    ((Cons _ m rest)
      (let ((many x) (many more)) $ match many ids (((Nat) _) ((List $ Nat) more)) ((Nil _) (values 0 ids)) ((Cons _ x xs) (values x xs)))
      (let ((many place) (many tail3)) $ match many tele (((Maybe $ Term) _) ((List $ Entry) tail3)) ((Nil _) (values (None _) tele)) ((Cons _ e es) (values (entry-place e) es)))
      (let ((many env2) (many code))
        (match many m (((Env) _) ((Code ctx many-one) code))
          ((Erased) (values env $ CError _ many-one "erased return"))
          (else
            (match many place (((Env) _) ((Code ctx many-one) code))
              ((None _) (values env $ var-code env ctx x))
              ((Some _ p)
                (match many (instantiate args p) (((Env) _) ((Code ctx many-one) code))
                  ((TSlotHolds p2) (let ((many env2) (many y)) $ location-var env ctx p2) (values env2 $ var-code env2 ctx y))
                  (else (values (env-error env "internal: malformed return location") $ CError _ many-one "location"))))))))
      (let ((many env3) (many codes) (erased pk)) $ notail $ result-codes rest tail3 more (Cons _ (TVar x) args) env2 ctx)
      (match many m _
        ((Erased) (values env3 codes $ PkErased _ rest codes pk))
        ((Many) (values env3 (Cons _ code codes) $ PkMany _ rest code codes pk))
        ((Once) (values env3 (Cons _ code codes) $ PkOnce _ rest code codes pk))))))

; [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
; their ids in order; names, multiplicities and states override the telescope's own when given.
; ---- Opening telescopes into scope

(def-adts $ (MultsMode : -> Type)
  enum
  (many MMDeclared : -> (MultsMode))
  (many MMErased : -> (MultsMode))
  (many MMExpect : (many (List $ Mult) ms) -> (MultsMode)))

(def-fns _ $ (many open-tele : (subterm many (List $ Entry) tele) (many (Env) env) (many (Maybe $ List $ Maybe $ String) names) (many (Maybe $ List $ Maybe $ Loc) sites) (many (Maybe $ List $ Mult) mults) (many (List $ Term) ids) (many (Bool) meta) ->
    (many (Env) r) (many (List $ Nat) fresh) (erased (Lockstep (Entry) (Nat) tele fresh) lock))
  (match many tele _
    ((Nil _) (values env (Nil _) (LsNil _ _)))
    ((Cons _ e rest)
      (match many e _
        ((MkEntry ename _ emult esg place esite)
          (let ((many ty) (many rule)) $ fact-of env $ sg-inst ids esg)
          (let ((many (Maybe $ String) name) (many (Maybe $ List $ Maybe $ String) names2))
            (match many names _
              ((None _) (values ename names))
              ((Some _ ns) (match many ns (((Maybe $ String) _) ((Maybe $ List $ Maybe $ String) ns2)) ((Nil _) (values ename names)) ((Cons _ n nrest) (values n $ Some _ nrest))))))
          ; [sites] given means this site is where the source writes the binders -- a pattern's fields --
          ; so they are the ones shadowing warns at; without it the telescope is being read back and each
          ; entry keeps the position its declaration carried (core.sl's bind-as).
          (let ((many (Maybe $ Loc) site) (many (Bool) warns) (many (Maybe $ List $ Maybe $ Loc) sites2))
            (match many sites _
              ((None _) (values esite (BFalse) sites))
              ((Some _ ss) (match many ss (((Maybe $ Loc) _) ((Bool) _) ((Maybe $ List $ Maybe $ Loc) _)) ((Nil _) (values (None _) (BTrue) sites)) ((Cons _ sf srest) (values sf (BTrue) $ Some _ srest))))))
          (let ((many (Mult) mult) (many (Maybe $ List $ Mult) mults2))
            (match many mults _
              ((None _) (values emult mults))
              ((Some _ ms) (match many ms (((Mult) _) ((Maybe $ List $ Mult) ms2)) ((Nil _) (values emult mults)) ((Cons _ m mrest) (values m $ Some _ mrest))))))
          (let ((many env2a) (many x)) $ bind-as env meta (BFalse) name site warns mult ty rule delegate-id)
          (let ((many env2)) $ match many place (((Env) _))
            ((None _) env2a)
            ((Some _ p) (match many (instantiate ids p) (((Env) _)) ((TSlotHolds p2) (at-merge env2a (TVar x) p2)) (else (env-error env2a "internal: malformed location")))))
          (let ((many env3) (many more) (erased p)) $ notail $ open-tele rest env2 names2 sites2 mults2 (Cons _ (TVar x) ids) meta)
          (values env3 (Cons _ x more) (LsCons _ _ e x rest more p)))))))

(def-fns _ $ (many anon-names : (subterm many (List $ Entry) tele) -> (many (List $ Maybe $ String) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (None _) $ notail $ anon-names rest))))

(def-fns _ $ (many finish-mode-tele : (many (Env) env) (many (List $ Entry) tele) (many (Bool) final) ->
    (many (Env) out) (many (List $ Entry) selected) (many (List $ Mult) inner) (many (DemandBridge many-one inner) bridge))
  (match many tele _
    ((Nil _) (values env tele many-one (HeadDemand (Many))))
    ((Cons _ e rest)
      (match many e _
        ((MkEntry name sub2 _ sg place site)
          (let ((many ty) (many rule)) (fact-of env sg))
          (let ((many mode)) (mode-demand env ty final))
          (values env (Cons _ (MkEntry name sub2 mode sg place site) rest) (Cons _ mode (Nil _)) (HeadDemand mode)))))))

(def-fns _ $ (many finish-demand-tele : (many (List $ Mult) expect) (many (ExprDemand expect) demand) (many (Env) env) (many (List $ Entry) tele) ->
    (many (Env) out) (many (List $ Entry) selected) (many (List $ Mult) inner) (many (DemandBridge expect inner) bridge))
  (match many demand _
    ((Fixed _) (values env tele expect (KeepDemand _)))
    ((CallableHead) (finish-mode-tele env tele $ BFalse))
    ((FinalDemand) (finish-mode-tele env tele $ BTrue))))

(def-fns _ $ (many raw-sites : (subterm many (List $ Raw) rs) (many (Env) env) -> (many (List $ Maybe $ Loc) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (Some _ $ loc-in env $ raw-pos r) $ notail $ raw-sites rest env))))

(def-fns _ $ (many anon-sites : (subterm many (List $ Entry) tele) -> (many (List $ Maybe $ Loc) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ _ rest) (Cons _ (None _) $ notail $ anon-sites rest))))

(def-fns _ $ (many raw-names : (subterm many (List $ Raw) rs) -> (many (List $ Maybe $ String) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (name-or-anon $ raw-name r) $ notail $ raw-names rest))))

; Entering a branch forces the scrutinee equal to the constructor over its fields (section 18).

(def-fns _ $ (many subterm-params : (subterm many (List $ Entry) tele) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (match many ids _
        ((Nil _) (Nil _))
        ((Cons _ x irest)
          (match many (entry-sub e) _
            ((BTrue) (Cons _ x $ notail $ subterm-params rest irest))
            ((BFalse) (tail $ subterm-params rest irest))))))))

; Per-value multiplicities of the binders of a let or the entries of a signature.
(def-fns _ $ (many src-mults : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) -> (many (List $ Mult) r) (erased (Lockstep (SrcEntry root) (Mult) es r) lock))
  (match many es _
    ((Nil _) (values (Nil _) (LsNil _ _)))
    ((Cons _ e rest)
      (let ((many m)) $ match many e (((Mult) _)) ((MkSrcEntry _ _ sm _ _ _ _) (match many sm (((Mult) _)) ((None _) (Many)) ((Some _ mm) mm))))
      (let ((many r) (erased p)) $ notail $ src-mults _ rest)
      (values (Cons _ m r) (LsCons _ _ e m rest r p)))))


(def-fns _
  ((many is-strict-subterm : (subterm many (Term) b) (many (Term) a) -> (many (Bool) r))
    (match many b _
      ((TApp _ args) (tail $ subterm-in args a)) (else (BFalse))))
  ((many subterm-in : (subterm many (List $ Term) ts) (many (Term) a) -> (many (Bool) r))
    (match many ts _
      ((Nil _) (BFalse))
      ((Cons _ t rest) (or (term-eq a t) $ or (notail $ is-strict-subterm t a) $ notail $ subterm-in rest a)))))

; A literal is an atom to the unifier (LITERALS.md): checking fails where one meets a Succ shape or another
; literal, and forcing binds one where a contradiction was wanted. The notes name each literal a check or a
; trial turned on, a character standing for its code, with the first of [within] it sits in; numerals come
; first, then characters, each in order of value (lib/elab.ml's literal_notes).
(def-fns _ $ (many lit-value : (many (String) s) -> (many (Nat) n))
  (match many (all-digits s) _ ((BTrue) (parse-nat s 0)) ((BFalse) (match many (char-lit-code s) _ ((Some _ n) n) ((None _) 0)))))

(def-fns _ $ (many lit-before : (many (String) a) (many (String) b) -> (many (Bool) r))
  (match many (all-digits a) _
    ((BTrue) (match many (all-digits b) _ ((BTrue) (nat-lt (lit-value a) (lit-value b))) ((BFalse) (BTrue))))
    ((BFalse) (match many (all-digits b) _ ((BTrue) (BFalse)) ((BFalse) (nat-lt (lit-value a) (lit-value b)))))))

(def-fns _ $ (many hit-spelling : (many (Pair (Term) (LitEntry)) h) -> (many (String) s))
  (match many h _ ((MkPair _ _ _ l) (match many l _ ((MkLitEntry _ _ s) s)))))

(def-fns _ $ (many hit-insert : (many (Pair (Term) (LitEntry)) h) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (List $ Pair (Term) (LitEntry)) r))
  (match many hs _
    ((Nil _) (Cons _ h $ Nil _))
    ((Cons _ x rest)
      (match many (lit-before (hit-spelling h) (hit-spelling x)) _
        ((BTrue) (Cons _ h hs))
        ((BFalse) (Cons _ x $ notail $ hit-insert h rest))))))

(def-fns _ $ (many code-of-char : (many (Term) t) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (Bool) r))
  (match many hs _
    ((Nil _) (BFalse))
    ((Cons _ h rest)
      (match many h _ ((MkPair _ _ ct _) (or (and (not $ all-digits $ hit-spelling h) $ is-strict-subterm ct t) $ notail $ code-of-char t rest))))))

; The hits kept, a numeral that is a hit character's code left out, in order.
(def-fns _ $ (many hits-kept : (subterm many (List $ Pair (Term) (LitEntry)) hs) (many (List $ Pair (Term) (LitEntry)) all) (many (List $ Pair (Term) (LitEntry)) acc) -> (many (List $ Pair (Term) (LitEntry)) r))
  (match many hs _
    ((Nil _) acc)
    ((Cons _ h rest)
      (match many h _
        ((MkPair _ _ t _)
          (tail $ hits-kept rest all $ match many (and (all-digits $ hit-spelling h) $ code-of-char t all) (((List $ Pair (Term) (LitEntry)) _)) ((BTrue) acc) ((BFalse) (hit-insert h acc))))))))

(def-fns _ $ (many lit-place : (many (Env) env) (many (Term) t) (subterm many (List $ Term) within) -> (many (Maybe $ Term) r))
  (match many within _
    ((Nil _) (None _))
    ((Cons _ c rest) (match many (is-strict-subterm (canon-env env c) t) _ ((BTrue) (Some _ c)) ((BFalse) (tail $ lit-place env t rest))))))

(def-fns _ $ (many literal-notes : (many (Env) env) (many (Env) out) (many (List $ Term) within) (subterm many (List $ Pair (Term) (LitEntry)) hs) -> (many (Env) r))
  (match many hs _
    ((Nil _) out)
    ((Cons _ h rest)
      (match many h _
        ((MkPair _ _ t _)
          (let ((many s)) $ hit-spelling h)
          (let ((many (Bool) numeral)) $ all-digits s)
          (let ((many place)) $ match many (lit-place env t within) (((String) _)) ((None _) "") ((Some _ c) (str-cat " in " $ qshow env c)))
          (let ((many kind)) $ match many numeral (((String) _)) ((BTrue) " is a numeral literal, usually opaque") ((BFalse) " is a character literal, whose code is usually opaque"))
          (let ((many msg)) $ str-cat3 s place $ str-cat kind " to the checker; consider `unary`, `distinct`, or `numeral-of`")
          (tail $ literal-notes env (env-note-at out (env-loc out) msg) within rest))))))

; Where two canonical terms part: the pairs of subterms at which they first differ.
(def-fns _
  ((many differ : (subterm many (Term) a) (many (Term) b) -> (many (List $ Pair (Term) (Term)) r))
    (match many (term-eq a b) _
      ((BTrue) (Nil _))
      ((BFalse)
        (let ((many one-pair)) $ Cons _ (MkPair _ _ a b) $ Nil _)
        (match many a _
          ((TApp h xs)
            (match many b _
              ((TApp h2 ys) (match many (and (term-eq h h2) $ nat-eq (list-length _ xs) $ list-length _ ys) _ ((BTrue) (tail $ differ-list xs ys)) ((BFalse) one-pair)))
              (else one-pair)))
          (else one-pair)))))
  ((many differ-list : (subterm many (List $ Term) xs) (many (List $ Term) ys) -> (many (List $ Pair (Term) (Term)) r))
    (match many xs _
      ((Nil _) (Nil _))
      ((Cons _ x rest)
        (match many ys _
          ((Nil _) (Nil _))
          ((Cons _ y yrest)
            (let ((many zs) (erased _)) $ list-append _ (notail $ differ x y) $ notail $ differ-list rest yrest)
            zs))))))

(def-fns _ $ (many pair-side : (many (Env) env) (many (Term) t) (subterm many (List $ Pair (Term) (Term)) pairs) -> (many (Bool) r))
  (match many pairs _
    ((Nil _) (BFalse))
    ((Cons _ p rest)
      (match many p _
        ((MkPair _ _ a b)
          (or (and (not $ or (has-meta-env env a) $ has-meta-env env b)
                $ or (term-eq t a) $ or (term-eq t b) $ or (is-strict-subterm t a) $ is-strict-subterm t b)
            $ notail $ pair-side env t rest))))))

(def-fns _ $ (many check-hits : (many (Env) env) (subterm many (List $ Pair (Term) (LitEntry)) ls) (many (List $ Pair (Term) (Term)) pairs) -> (many (List $ Pair (Term) (LitEntry)) r))
  (match many ls _
    ((Nil _) (Nil _))
    ((Cons _ l rest)
      (let ((many more)) $ notail $ check-hits env rest pairs)
      (match many l _ ((MkPair _ _ t _) (match many (pair-side env t pairs) _ ((BTrue) (Cons _ l more)) ((BFalse) more)))))))

; What a forcing trial bound: each literal's canonical form under the trial, where the trial changed it.
(def-fns _ $ (many trial-bound : (many (Env) trial) (subterm many (List $ Pair (Term) (LitEntry)) ls) -> (many (List $ Term) r))
  (match many ls _
    ((Nil _) (Nil _))
    ((Cons _ l rest)
      (let ((many more)) $ notail $ trial-bound trial rest)
      (match many l _
        ((MkPair _ _ t _)
          (let ((many u)) $ canon-env trial t)
          (match many (term-eq u t) _ ((BTrue) more) ((BFalse) (Cons _ u more))))))))

(def-fns _ $ (many term-among : (many (Term) t) (subterm many (List $ Term) ts) -> (many (Bool) r))
  (match many ts _ ((Nil _) (BFalse)) ((Cons _ u rest) (or (term-eq t u) $ notail $ term-among t rest))))

(def-fns _ $ (many forced-hits : (many (Env) trial) (subterm many (List $ Pair (Term) (LitEntry)) ls) (many (List $ Term) bound) -> (many (List $ Pair (Term) (LitEntry)) r))
  (match many ls _
    ((Nil _) (Nil _))
    ((Cons _ l rest)
      (let ((many more)) $ notail $ forced-hits trial rest bound)
      (match many l _ ((MkPair _ _ t _) (match many (term-among (canon-env trial t) bound) _ ((BTrue) (Cons _ l more)) ((BFalse) more)))))))

; The notes for a branch a forcing trial left standing, [env] the environment before the trial.
(def-fns _ $ (many forced-notes : (many (Env) env) (many (Env) trial) (many (Res) r) (many (Env) out) -> (many (Env) e))
  (let ((many ls)) $ lit-terms env $ env-lits env)
  (let ((many hs)) $ forced-hits trial ls $ trial-bound trial ls)
  (literal-notes env out (Cons _ (res-ty r) $ Cons _ (res-term r) $ Nil _) $ hits-kept hs hs $ Nil _))

; ---- Checks (section 5's canonicalize-then-compare) and proofs (section 8)

; Identity after canonicalization (section 5), solving any metas either side holds (unify-env); a mismatch
; is reported only when asked to.
(def-fns _ $ (many solve : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) (many (Bool) report) -> (many (Env) r) (many (Bool) ok))
  (match many (unify-solve env actual expected) _
    ((UOk env2) (values env2 $ BTrue))
    ((UContra _)
      (match many report _
        ((BTrue)
          (let ((many ls)) $ lit-terms env $ env-lits env)
          (let ((many hs)) $ check-hits env ls $ differ (canon-env env actual) $ canon-env env expected)
          (let ((many out)) $ env-error env $ str-cat3 what " mismatch: expected " $ str-cat3 (qshow env expected) ", got " $ qshow env actual)
          (values (literal-notes env out (Cons _ expected $ Cons _ actual $ Nil _) $ hits-kept hs hs $ Nil _) $ BFalse))
        ((BFalse) (values env $ BFalse))))))

(def-fns _ $ (many check : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) -> (many (Env) r))
  (let ((many env2) (many ok)) $ solve env what actual expected $ BTrue)
  env2)

(def-fns _ $ (many check-sg : (many (Env) env) (many (Sg) sg) (many (Res) r) -> (many (Env) e))
  (match many sg _
    ((SgTy ty) (check env "type" (res-ty r) ty))
    ((SgIs t _) (check env "value" (res-term r) t))))

(def-fns _ $ (many count-error : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r))
  (env-error env $ str-cat3 "expected " (nat-str expected) $ str-cat3 what ", got " $ nat-str got))

; A boundary (SUGAR.md 6): a term reaching one with a `_` still open is refused.
(def-fns _ $ (many settle : (many (Env) env) (many (Term) t) -> (many (Env) r))
  (def-fns msg-lvl $ (many msg-settle : -> (many (String) s)) (str-cat "cannot infer the `_` in " $ qshow env t))
  (error-when-msg env (has-meta-env env t) msg-settle))

(def-fns _ $ (many settle-res : (many (Env) env) (many (Res) r) -> (many (Env) e))
  (settle (settle env $ res-term r) $ res-ty r))

(def-fns _ $ (many settle-list : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Env) r))
  (match many ts _
    ((Nil _) env)
    ((Cons _ t rest) (tail $ settle-list rest $ settle env t))))

(def-fns _ $ (many metaless-ress : (subterm many (List $ Res) rs) (many (Env) env) -> (many (List $ Res) r))
  (match many rs _
    ((Nil _) (Nil _))
    ((Cons _ r rest) (Cons _ (MkRes (metaless env $ res-term r) (metaless env $ res-ty r) (res-erasure r) $ res-place r) $ notail $ metaless-ress rest env))))

(def-fns _ $ (many metaless-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (List $ Entry) r))
  (match many es _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (match many e _
        ((MkEntry n s m sg place site)
          (let ((many g)) $ match many sg (((Sg) _)) ((SgTy t) (SgTy $ metaless env t)) ((SgIs t ty) (SgIs (metaless env t) $ metaless env ty)))
          (let ((many p)) $ match many place (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ t) (Some _ $ metaless env t)))
          (Cons _ (MkEntry n s m g p site) $ notail $ metaless-tele rest env))))))

(def-fns _ $ (many settle-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (Env) r))
  (match many es _
    ((Nil _) env)
    ((Cons _ e rest) (tail $ settle-tele rest $ settle env $ sg-term $ entry-sg e))))

(def-fns _ $ (many check-result-place : (many (Env) env) (many (Entry) e) (many (List $ Term) ids) (many (Res) r) -> (many (Env) out))
  (match many (env-usage-erased env) _
    ((BTrue) env)
    ((BFalse)
      (match many (entry-place e) _
        ((None _) env)
        ((Some _ p)
          (match many (instantiate ids p) _
            ((TSlotHolds p2)
              (let ((many ok)) $ match many (res-place r) (((Bool) _)) ((None _) (BFalse)) ((Some _ q) (at-equal env p2 q)))
              (def-fns msg-lvl $ (many msg-at : -> (many (String) s)) (str-cat "return does not satisfy `at` " $ qshow env p2))
              (error-unless-msg env ok msg-at))
            (else (env-error env "internal: malformed location"))))))))

; Results against a return telescope; [ids] as in open-tele. Each result is checked at [sites], where it is
; written.
(def-fns _ $ (many check-results : (subterm many (List $ Entry) tele) (many (Env) env) (many (List $ Res) ress) (many (List $ Term) ids) (many (List $ Pos) sites) -> (many (Env) r))
  (match many tele _
    ((Nil _) (match many ress _ ((Nil _) env) ((Cons _ _ _) (env-error env "expected fewer values"))))
    ((Cons _ e rest)
      (match many ress _
        ((Nil _) (env-error env "expected more values"))
        ((Cons _ r rrest)
          (let ((many (Env) at-site) (many (List $ Pos) more)) $ match many sites (((Env) _) ((List $ Pos) _)) ((Nil _) (values env sites)) ((Cons _ pos ps) (values (env-at env pos) ps)))
          (let ((many env2)) $ env-back env $ check-result-place (settle-res (check-sg at-site (sg-inst ids $ entry-sg e) r) r) e ids r)
          (tail $ check-results rest env2 rrest (Cons _ (res-term r) ids) more))))))

(def-fns _ $ (many raw-positions : (subterm many (List $ Raw) rs) -> (many (List $ Pos) r))
  (match many rs _ ((Nil _) (Nil _)) ((Cons _ r rest) (Cons _ (raw-pos r) $ notail $ raw-positions rest))))

; Where each of a body's [n] results is written: the entries of a final values form holding one per result,
; else the final expression (lib/elab.ml's result_locs).
(def-fns _ $ (many result-sites : (many (Env) env) (many (List $ Raw) body) (many (Nat) n) -> (many (List $ Pos) r))
  (match many (list-rev _ body) _
    ((Nil _) (match many (env-loc env) _ ((MkLoc _ here) (list-replicate _ n here))))
    ((Cons _ final _)
      (let ((many whole)) $ list-replicate _ n $ raw-pos final)
      (match many final _
        ((RList _ items)
          (match many items _
            ((Cons _ v entries) (match many (and (is-special env v $ SpExpr $ ExValues) $ nat-eq (list-length _ entries) n) _ ((BTrue) (raw-positions entries)) ((BFalse) whole)))
            ((Nil _) whole)))
        (else whole)))))

(def-fns _ $ (many check-results-count : (many (Env) env) (many (List $ Raw) body) (many (List $ Entry) tele) (many (List $ Res) ress) (many (List $ Term) ids) -> (many (Env) r))
  (let ((many n)) $ list-length _ tele)
  (let ((many m)) $ list-length _ ress)
  (match many (nat-cmp n m) _
    ((CEq _ _ _) (check-results tele env ress ids $ result-sites env body n))
    (else (count-error env " values" n m))))

; prove-subterm (section 8): the first, canonicalized, is a strict subtree of the second through constructor
; applications only.
(def-fns _ $ (many mint-subterm : (many (Env) env) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty) -> (many (Env) r) (many (Res) res))
  (let ((many ca)) $ canon-env env a)
  (let ((many cb)) $ canon-env env b)
  (def-fns msg-lvl $ (many msg-subterm : -> (many (String) s)) (str-cat3 (qshow env a) " is not a strict subterm of " $ qshow env b))
  (let ((many env2)) $ error-unless-msg env (is-strict-subterm cb ca) msg-subterm)
  (mint env2 $ proof-type subterm-id $ Cons _ aty $ Cons _ a $ Cons _ bty $ Cons _ b $ Nil _))

; prove-predates (section 8): the variable was in scope when the level was minted (ASSUMPTIONS 13).
(def-fns _ $ (many mint-predates : (many (Env) env) (many (Nat) x0) (many (Nat) lvl) -> (many (Env) r) (many (Res) res))
  (let ((many env2)) $ error-unless env (entry-minted env lvl) $ str-cat (qname env lvl) " is not a level minted by `def-lvl`")
  (let ((many (Nat) x))
    (match many (nat-lt x0 lvl) _
      ((BTrue) x0)
      ((BFalse) (match many (canon-env env2 $ TVar x0) (((Nat) _)) ((TVar y) y) (else x0)))))
  (let ((many env3)) $ error-unless env2 (nat-lt x lvl) $ str-cat3 (qname env2 x) " was not in scope when level " $ str-cat (qname env2 lvl) " was minted")
  (mint env3 $ proof-type predates-id $ Cons _ (type-of env3 x) $ Cons _ (TVar x) $ Cons _ (TVar lvl) $ Nil _))

; The arguments of a proof of the given kind, with an error where the term is not one.
(def-fns _ $ (many proof-args : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Maybe $ List $ Term) r))
  (match many (canon-env env $ res-ty p) _
    ((TApp h args) (match many h _ ((TVar c) (match many (nat-cmp c ctor) _ ((CEq _ _ _) (Some _ args)) (else (None _)))) (else (None $ List $ Term)))) (else (None $ List $ Term))))

(def-fns _ $ (many not-a-proof : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Env) r))
  (env-error env $ str-cat3 "expected a " (qname env ctor) $ str-cat3 " proof, got " (qshow env $ res-term p) $ str-cat " : " $ qshow env $ res-ty p))

(def-fns _ $ (many proof-errs : (subterm many (Nat) n) -> (many (List $ Term) ts))
  (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ (TErr "proof") $ notail $ proof-errs k))))

; The three arguments of a Predates proof, or the four of a Subterm or Coercible proof (section 8).
(def-fns _ $ (many proof-terms : (many (Env) env) (many (Nat) ctor) (many (Res) p) (many (Nat) n) -> (many (Env) r) (many (List $ Term) args))
  (let ((many (Maybe $ List $ Term) args))
    (match many (proof-args env ctor p) _
      ((None _) (None _))
      ((Some _ ts) (match many (nat-cmp (list-length _ ts) n) (((Maybe $ List $ Term) _)) ((CEq _ _ _) (Some _ ts)) (else (None _))))))
  (match many args _
    ((None _) (values (not-a-proof env ctor p) $ proof-errs n))
    ((Some _ ts) (values env ts))))

(def-fns _ $ (many expect-proof3 : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2))
  (let ((many env2) (many args)) $ proof-terms env ctor p 3)
  (values env2 (nth-term args 0) (nth-term args 1) $ nth-term args 2))

(def-fns _ $ (many expect-proof4 : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3))
  (let ((many env2) (many args)) $ proof-terms env ctor p 4)
  (values env2 (nth-term args 0) (nth-term args 1) (nth-term args 2) $ nth-term args 3))

(def-fns _ $ (many expect-proof6 : (many (Env) env) (many (Nat) ctor) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3) (many (Term) t4) (many (Term) t5))
  (let ((many env2) (many args)) $ proof-terms env ctor p 6)
  (values env2 (nth-term args 0) (nth-term args 1) (nth-term args 2) (nth-term args 3) (nth-term args 4) $ nth-term args 5))

(def-fns _ $ (many expected-proof-type : (many (Env) env) (many (Maybe $ List $ Entry) tele) -> (many (Maybe $ Term) r))
  (match many tele _
    ((None _) (None _))
    ((Some _ es)
      (match many es _
        ((Nil _) (None _))
        ((Cons _ e rest)
          (match many rest _
            ((Cons _ _ _) (None _))
            ((Nil _)
              (Some _ $ canon-env env $ match many (entry-sg e) (((Term) _)) ((SgTy t) t) ((SgIs _ ty) ty)))))))))

(def-fns _ $ (many expected-coercible-sides : (many (Env) env) (many (Maybe $ List $ Entry) tele) -> (many (Maybe $ Pair (Term) $ Term) r))
  (match many (expected-proof-type env tele) _
    ((None _) (None _))
    ((Some _ ty)
      (match many ty _
        ((TApp h args)
          (match many (and (term-eq h $ TVar coercible-id) $ nat-eq (list-length _ args) 6) _
            ((BTrue) (Some _ $ MkPair _ _ (nth-term args 0) $ nth-term args 3))
            ((BFalse) (None _))))
        (else (None $ Pair (Term) $ Term))))))

(def-fns _ $ (many coercible-mint : (many (Env) env) (many (Maybe $ List $ Entry) tele) (many (Term) ty) -> (many (Env) e) (many (Res) r))
  (let ((many env2)) $ match many (expected-proof-type env tele) (((Env) _)) ((None _) env) ((Some _ want) (check env "type" ty want)))
  (mint env2 $ metaless env2 ty))

(def-fns _ $ (many sharing-mult : (many (Env) env) (many (Term) side) -> (many (Env) e) (many (Mult) m))
  (let ((many t)) $ canon-env env side)
  (match many (term-eq t unique-term) _
    ((BTrue) (values env $ Once))
    ((BFalse)
      (match many (term-eq t shared-term) _
        ((BTrue) (values env $ Many))
        ((BFalse) (values (env-error env "expected `(Unique)` or `(Shared)`") $ Many))))))

(def-fns _ $ (many sharing-of-fn : (many (Env) env) (many (Term) ty) -> (many (Term) r))
  (match many (canon-env env ty) _
    ((TFn unique2 _ _ _) (match many unique2 _ ((BTrue) unique-term) ((BFalse) shared-term)))
    (else shared-term)))

(def-fns _ $ (many wrap-sharing : (subterm many (List $ Entry) tele) (many (Term) side) -> (many (Term) r))
  (match many tele _
    ((Nil _) shared-term)
    ((Cons _ e rest) (match many (entry-mult e) _ ((Erased) (tail $ wrap-sharing rest side)) ((Many) shared-term) ((Once) side)))))

(def-fns _ $ (many coercible-code : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Mult) src) (many (Code ctx (Cons (Mult) src (Nil (Mult)))) code) -> (many (Code ctx expect) r))
  (match many (mults-same (Cons _ src $ Nil _) expect) _
    ((Some _ same) (recast _ expect (Cons _ src $ Nil _) same code))
    ((None _) (CErased _ expect))))

(def-fns _ $ (many coercible-proof-tele : (many (Env) env) (many (Nat) ctor) (many (Maybe $ Pair (Term) $ Term) sides) -> (many (Env) e) (many (Maybe $ List $ Entry) tele))
  (match many sides _
    ((None _) (values env $ None _))
    ((Some _ p)
      (match many p _
        ((MkPair _ _ sa sb)
          (let ((many env1) (many ta)) $ bind-as env (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) type-term (None _) delegate-id)
          (let ((many env2) (many va)) $ bind-as env1 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TVar ta) (None _) delegate-id)
          (let ((many env3) (many tb)) $ bind-as env2 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) type-term (None _) delegate-id)
          (let ((many env4) (many vb)) $ bind-as env3 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) (TVar tb) (None _) delegate-id)
          (let ((many ty)) $ proof-type ctor $ Cons _ sa $ Cons _ (TVar ta) $ Cons _ (TVar va) $ Cons _ sb $ Cons _ (TVar tb) $ Cons _ (TVar vb) $ Nil _)
          (values env4 $ Some _ $ Cons _ (MkEntry (None _) (BFalse) (Erased) (SgTy ty) (None _) $ None _) $ Nil _))))))

(def-fns _ $ (many list-drop : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) r))
  (match many n _
    ((Zero) xs)
    ((Succ k) (match many xs _ ((Nil _) (Nil _)) ((Cons _ _ rest) (tail $ list-drop _ k rest))))))

(def-fns _ $ (many trans-proofs : (many (Env) env) (many (Nat) ctor) (many (Nat) n) (many (Res) p) (many (Res) q) -> (many (Env) r) (many (Res) res))
  (let ((many env2) (many pa)) $ proof-terms env ctor p n)
  (let ((many env3) (many qa)) $ proof-terms env2 ctor q n)
  (let ((many env4)) $ check env3 "value" (nth-term qa 1) $ nth-term pa $ nat-pred n)
  (mint env4 $ proof-type ctor $ Cons _ (nth-term pa 0) $ Cons _ (nth-term pa 1) $ list-drop _ 2 qa))

(def-fns _ $ (many sp-name-in : (subterm many (List $ SpEntry) es) (many (Sp) sp) -> (many (String) name))
  (match many es _
    ((Nil _) "?")
    ((Cons _ e rest) (match many e _ ((MkSpEntry n s) (match many (sp-eq s sp) _ ((BTrue) n) ((BFalse) (tail $ sp-name-in rest sp))))))))

(def-fns _ $ (many sp-name : (many (Sp) sp) -> (many (String) name))
  (sp-name-in sp-table sp))

(def-fns _ $ (many find-matchable : (many (Env) env) (many (Nat) tid) -> (many (Env) r) (many (Maybe $ MatchInfo) info))
  (values env $ find-matchable-in (env-opens env) env tid $ index-of tid $ env-index env))

; The constructors an extern function builds its result with, read off its model's return type (section 41):
; the implementation's view and the declaration must agree on the shape, as they must for an extern type.
(def-fns _ $ (many extern-ctors : (many (Env) env) (many (String) name) (many (List $ Entry) rets) (many (List $ Nat) want) -> (many (Env) r) (many (List $ Ctor) cs))
  (let ((many (Maybe $ Nat) head))
    (match many rets _
      ((Nil _) (None _))
      ((Cons _ e _)
        (let ((many ty) (many rule)) $ fact-of env $ entry-sg e)
        (type-head env ty))))
  (match many head _
    ((None _) (values (env-error env $ str-cat3 "the extern implementation of " (tick name) " builds no declared type") (Nil _)))
    ((Some _ tid)
      (let ((many env2) (many found)) $ find-matchable env tid)
      (let ((many (Maybe $ Adt) got))
        (match many found _
          ((None _) (None _))
          ((Some _ info) (match many info _ ((MkMatchInfo mid _ _ _) (adt-of env2 mid))))))
      (match many got _
        ((None _) (values (env-error env2 $ str-cat3 "the extern implementation of " (tick name) $ str-cat3 " needs " (qname env2 tid) " declared before it") (Nil _)))
        ((Some _ adt)
          (let ((many records)) $ adt-ctors adt)
          (let ((many ns)) $ ctor-arities records)
          (let ((many (String) how)) $ match many (adt-tagged adt) _ ((BTrue) "(") ((BFalse) "the untagged ("))
          (let ((many (String) msg))
            (str-cat3 "the extern implementation of " (tick name) $ str-cat3 " has the tagged shape (" (spell-nats want) $ str-cat3 "), its declaration " how $ str-cat (spell-nats ns) ")"))
          (values (error-unless env2 (and (adt-tagged adt) $ nat-list-eq ns want) msg) records))))))

; ---- Opening a Matchable or Newtype (section 19, ASSUMPTIONS 139)

; The entries of [os] whose ids are in [ids], in order.
(def-fns _ $ (many opened-among : (subterm many (List $ Opened) os) (many (List $ Nat) ids) -> (many (List $ Opened) r))
  (match many os _
    ((Nil _) (Nil _))
    ((Cons _ o rest) (match many (list-mem-bin ids $ opened-x o) _ ((BTrue) (Cons _ o $ notail $ opened-among rest ids)) ((BFalse) (tail $ opened-among rest ids))))))

; Two opened objects of one kind naming one thing.
(def-fns _ $ (many opened-share : (many (Opened) x) (many (Opened) y) -> (many (Bool) r))
  (match many x _
    ((MkOpened _ kx nx)
      (match many y _
        ((MkOpened _ ky ny)
          (and (nat-eq (open-kind-code kx) $ open-kind-code ky) $ and (nat-lt (open-kind-code kx) 2) $ nats-share nx ny))))))

; The first of [ys] sharing a name with x; only one older than x, of a smaller id (an object is opened after
; the entries it may share with were bound), when [older-only].
(def-fns _ $ (many first-sharing : (subterm many (List $ Opened) ys) (many (Opened) x) (many (Bool) older-only) -> (many (Maybe $ Nat) r))
  (match many ys _
    ((Nil _) (None _))
    ((Cons _ y rest)
      (match many (and (or (not older-only) $ nat-lt (opened-x y) $ opened-x x) $ opened-share x y) _
        ((BTrue) (Some _ $ opened-x y))
        ((BFalse) (tail $ first-sharing rest x older-only))))))

; A newer opened object and an older one naming one thing, if any: the newest such object, and the newest
; older one it shares with; the list holds the newer first. Only a pair with a [touched] object, one whose
; names changed since the invariant last held, can share, the others having been disjoint then, so an
; untouched object is compared with the touched ones [tos] alone.
(def-fns _ $ (many open-pair : (subterm many (List $ Opened) opens) (many (List $ Nat) touched) (many (List $ Opened) tos) -> (many (Maybe $ Pair (Nat) (Nat)) r))
  (match many opens _
    ((Nil _) (None _))
    ((Cons _ x rest)
      (let ((many (Maybe $ Nat) y))
        (match many (list-mem-bin touched $ opened-x x) _
          ((BTrue) (first-sharing rest x $ BFalse))
          ((BFalse) (first-sharing tos x $ BTrue))))
      (match many y _
        ((Some _ yy) (Some _ $ MkPair _ _ (opened-x x) yy))
        ((None _) (tail $ open-pair rest touched tos))))))

; At most one opened Matchable names a given type constructor or value constructor, and at most one opened
; Newtype a given constructor (section 19): two that would are unified, forcing, and the better-ranked entry
; kept, the older on a tie, until no two name one thing; [fuel] bounds the merges by the list's length, and
; [touched] holds the objects whose names changed since the invariant last held, the unification adding to
; the environment's own those it changes.
(def-fns _ $ (many merge-opens : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Nat) touched) -> (many (UnifyRes) r))
  (match many fuel _
    ((Zero) (UOk env))
    ((Succ f)
      (let ((many opens)) $ env-opens env)
      (match many (open-pair opens touched $ opened-among opens touched) _
        ((None _) (UOk env))
        ((Some _ pr)
          (match many pr _
            ((MkPair _ _ newer older)
              (match many (unify-force (Forcing env) (type-of env newer) (type-of env older)) _
                ((Refuted m) (UContra m))
                ((Forcing env2)
                  (let ((many drop)) $ match many (nat-lt (matchable-rank env2 newer) $ matchable-rank env2 older) (((Nat) _)) ((BTrue) older) ((BFalse) newer))
                  (let ((many env3)) $ env-unopen env2 drop)
                  (let ((many all) (erased cat)) $ list-append _ (env-touched env3) $ nats-remove touched drop)
                  (tail $ merge-opens f (env-settled env3) all))))))))))

; The invariant restored after a forcing (refine, open-adt, the printers), for the objects it touched.
(def-fns _ $ (many merge-all : (many (Forced) fe) -> (many (UnifyRes) r))
  (match many fe _
    ((Refuted m) (UContra m))
    ((Forcing env)
      (match many (env-touched env) _
        ((Nil _) (UOk env))
        ((Cons _ _ _) (merge-opens (Succ $ list-length _ $ env-opens env) (env-settled env) $ env-touched env))))))

; Opens x (section 19): its constructors must be distinct after canonicalization, and it then merges with
; whatever open names one of them or its type constructor.
(def-fns _ $ (many env-open-adt : (many (Env) env) (many (Nat) x) -> (many (UnifyRes) r))
  (let ((many dup)) $ match many (type-of env x) (((Maybe $ Nat) _)) ((TMatchable _ _ _ _ cs) (nats-dup $ mctor-ids cs)) (else (None _)))
  (match many dup _
    ((Some _ c) (UContra $ CCat (CTerm $ TVar c) $ CText " is listed twice"))
    ((None _) (merge-all $ Forcing $ env-open env x))))

; def-adts opens what it mints; a fresh object relates to nothing open, so the assertion holds.
(def-fns _ $ (many open-minted : (many (Env) env) (many (Nat) x) -> (many (Env) r))
  (match many (env-open-adt env x) _ ((UOk env2) env2) ((UContra m) (env-error env $ str-cat "internal: " $ clash-str env m))))

; An anonymous let at [mult] of a Matchable or Newtype, elaborated by the caller into [inner]: the entry an
; open records (section 19). Run at once in run position, as a let's right-hand side is.
(def-fns _ $ (many open-bind : (many (List $ List $ Nat) ctx) (many (Env) env) (many (Env) inner) (many (Res) r) (many (Mult) mult) (many (Code ctx (Cons (Mult) mult (Nil (Mult)))) code) ->
    (many (Env) r2) (many (Nat) x) (many (Term) t))
  (let ((many t)) $ res-term r)
  (let ((many inner2)) $ settle-res inner r)
  (let ((many (Env) inner3))
    (match many (canon-env inner2 $ res-ty r) _
      ((TMatchable _ _ _ _ _) inner2)
      (else (env-error inner2 $ str-cat3 (qshow inner2 t) " : " $ str-cat (qshow inner2 $ res-ty r) " is not a `Matchable`"))))
  (let ((many run)) $ env-run-pos env)
  (let ((many env3) (many x)) $ bind (env-hide env inner3) (None _) (None _) (BFalse) mult (res-ty r) (Some _ t) delegate-id)
  (let ((many (Env) env4))
    (match many run _
      ((BFalse) (match many t (((Env) _)) ((TVar y) (forward-state env3 x y)) (else env3)))
      ((BTrue)
        (match many mult (((Env) _))
          ((Erased) (env-set-tokens env3 $ Cons _ x $ Nil _))
          (else
            (match many ctx (((Env) _))
              ((Cons _ _ _) (env-set-tokens env3 $ Cons _ x $ Nil _))
              ((Nil _)
                (match many (list-is-empty _ $ env-errors inner3) (((Env) _))
                  ((BTrue) (env-run-let env3 (Cons _ mult $ Nil _) code $ Cons _ x $ Nil _))
                  ((BFalse) (env-set-tokens env3 $ Cons _ x $ Nil _))))))))))
  (values env4 x t))

; A type is empty when its Matchable lists no constructor (section 37).
(def-fns _ $ (many check-empty : (many (Env) env) (many (Term) ty) -> (many (Env) r))
  (let ((many (Bool) empty))
    (match many (type-head env ty) _
      ((None _) (BFalse))
      ((Some _ t)
        (let ((many env2) (many found)) $ find-matchable env t)
        (match many found (((Bool) _))
          ((None _) (BFalse))
          ((Some _ info) (match many info (((Bool) _)) ((MkMatchInfo _ _ cs _) (list-is-empty _ cs))))))))
  (def-fns msg-lvl $ (many msg-empty : -> (many (String) s)) (str-cat (qshow env ty) " is not an empty type"))
  (error-unless-msg env empty msg-empty))

(def-fns _ $ (many mint-level : (many (Env) env) (many (Maybe $ String) name) (many (Maybe $ Loc) site) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ bind-erased env name site (BTrue) (Erased) level-term (None _) delegate-id)
  (values (mark-minted env2 x) x))

; Entering a branch forces the scrutinee equal to the constructor over its fields, and its type to the
; constructor's return (section 18).
(def-fns _ $ (many newtype-fields-at : (subterm many (List $ Entry) tele) (many (List $ Nat) fids) (many (Env) env) (many (Res) scrut) -> (many (Env) out))
  (match many tele _
    ((Nil _) env)
    ((Cons _ _ rest) (match many fids _
      ((Nil _) env)
      ((Cons _ x tail2)
        (let ((many env1)) (match many (mult-is-many $ entry-mult-of env x) (((Env) _))
          ((BFalse) env) ((BTrue) (match many (res-place scrut) _ ((None _) env) ((Some _ loc) (at-merge env (TVar x) loc))))))
        (tail $ newtype-fields-at rest tail2 env1 scrut))))))

(def-fns _ $ (many refine : (many (Env) env) (many (Res) scrut) (many (Nat) c) (many (List $ Nat) fids) (many (Term) ret) -> (many (UnifyRes) r))
  (let ((many params) (many ignored)) (ctor-type env c))
  (let ((many env14)) (match many (find-newtype env c) (((Env) _)) ((None _) env) ((Some _ _) (newtype-fields-at params fids env scrut))))
  (let ((many fvars)) $ tvars-rev fids $ Nil _)
  (merge-all $ unify-force (unify-force (Forcing env14) (res-term scrut) $ TApp (TVar c) $ list-rev _ fvars) (res-ty scrut) $ instantiate fvars ret))

(def-fns _ $ (many open-fields : (many (Env) env) (many (List $ Entry) tele) (many (List $ Maybe $ String) names) (many (List $ Maybe $ Loc) sites) (many (Maybe $ List $ Mult) mults) (many (Res) sres) (many (Nat) c) (many (Term) ret) ->
    (many (Env) r) (many (List $ Nat) fids) (many (UnifyRes) u))
  (let ((many env2) (many fids) (erased lock)) $ open-tele tele env (Some _ names) (Some _ sites) mults (Nil _) $ BFalse)
  (let ((many env2d)) (mark-words fids env2 (BFalse)))
  (values env2d fids (refine env2d sres c fids ret)))

(def-fns _ $ (many disc-of-checked : (many (Env) env) (many (Raw) d) -> (many (Env) r) (many (Disc) disc))
  (match many (is-mark env d $ MkUnion) _
    ((BTrue) (values env $ DUnion))
    ((BFalse)
      (match many (is-mark env d $ MkEnum) _
        ((BTrue) (values env $ DEnum))
        ((BFalse) (values (env-error env "expected `enum` or `union`") $ DEnum))))))

; A claim on the FFI's fixed table (ASSUMPTIONS 42): each implementation backs one declaration per program.
(def-fns _ $ (many claim-extern : (many (Env) env) (many (String) name) (many (Bool) known) -> (many (Env) r))
  (match many known _
    ((BFalse) (env-error env $ str-cat "no extern implementation for " $ tick name))
    ((BTrue)
      (match many (claimed-at (env-claimed env) name) _
        ((Some _ l)
          (env-note-at (env-error env $ str-cat3 "the extern implementation of " (tick name) " is already bound")
            l "the declaration that bound it"))
        ((None _) (env-claim env name))))))


; ---- Small helpers the block's checks use

(def-fns _ $ (many not-applicable : (many (Env) env) (many (Res) h) -> (many (String) s))
  (str-cat3 (qshow env $ res-term h) " : " $ str-cat (qshow env $ res-ty h) " is not applicable"))

(def-fns _ $ (many cannot-apply-in-type : (many (Env) env) (many (Term) h) (many (Term) hty) -> (many (String) s))
  (str-cat3 (qshow env h) " has type " $ str-cat (qshow env hty) " and cannot be applied in a type"))

(def-fns _ $ (many annotation-kind : (many (Env) env) (many (Res) callee) (many (Bool) same) -> (many (String) s))
  (match many same _
    ((BTrue) (str-cat3 "same-level call to " (qshow env $ res-term callee) " takes a `(subterm p)` annotation, not `(predates p)`"))
    ((BFalse) (str-cat3 "lower-level call to " (qshow env $ res-term callee) " takes a `(predates p)` annotation, not `(subterm p)`"))))

(def-fns _ $ (many level-of-error : (many (Env) env) (many (Term) f) (many (Term) ty) -> (many (String) s))
  (str-cat3 "`level-of`: " (qshow env f) $ str-cat3 " : " (qshow env ty) " is not a function"))

(def-fns _ $ (many expr-error : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Env) env) (many (String) msg) (many (String) tag) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
  (values (env-error env msg) (Nil _) $ CError _ expect tag))

(def-fns _ $ (many erased-result : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Env) env) (many (Res) r) -> (many (Env) r2) (many (List $ Res) ress) (many (Code ctx expect) code))
  (values env (Cons _ r $ Nil _) $ CErased _ expect))

; A constructor named in source, read through its alias, which must hold a value constructor.
(def-fns _ $ (many ctor-var : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Nat) c))
  (let ((many env2) (many c)) $ named env raw "a constructor")
  (match many (type-of env2 c) _
    ((TValCtor _ _) (values env2 c))
    ((TErr _) (values env2 c)) (else (values (env-error env2 $ str-cat (qname env2 c) " is not a value constructor") c))))

(def-fns _ $ (many runtime-one : (erased (List $ List $ Nat) ctx) (many (Mult) pos)
    (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) code) -> (many (Code ctx many-one) out))
  (match many pos _
    ((Erased) (CErased _ many-one))
    ((Many) code)
    (else (match many (mults-same (Cons _ pos (Nil _)) many-one) _
      ((None _) (CError _ many-one "invalid runtime shape"))
      ((Some _ same) (recast _ many-one (Cons _ pos (Nil _)) same code))))))

(def-fns _ $ (many bridge-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) outer) (erased (List $ Mult) inner) (many (DemandBridge outer inner) bridge) (many (Code ctx inner) code) -> (many (Code ctx outer) out))
  (match many bridge _ ((KeepDemand _) code) ((HeadDemand mode) (runtime-one _ mode code))))

(def-fns _ $ (many prepare-argument : (many (Env) env) (many (Mult) pos) (many (Res) res) ->
    (many (Env) env2) (many (Res) prepared) (many (Nat) id))
  (let ((many env1) (many id)) (bind-as env (BFalse) (BTrue) (None _) (None _) (BFalse) pos (res-ty res) (Some _ (res-term res)) delegate-id))
  (let ((many env2)) (mark-word env1 id (BTrue)))
  (let ((many env3)) (match many (res-place res) (((Env) _))
    ((None _) env2) ((Some _ place) (at-merge env2 (TVar id) place))))
  (values env3 (res-of env3 id) id))

(def-fns _ $ (many code-var : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) -> (many (Maybe $ Nat) r))
  (match many code _
    ((CVar _ z _) (Some _ z))
    ((CConst _ z) (Some _ z))
    ((CValues _ _ cs _) (match many cs _ ((Cons _ c rest) (match many rest _ ((Nil _) (tail $ code-var _ _ c)) (else (None _)))) (else (None _))))
    (else (None _))))

(def-fns _ $ (many prepare-or-keep : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (many (Env) env) (many (Mult) pos) (many (Res) res) (many (Code ctx ms) code) ->
    (many (Env) env2) (many (Res) prepared) (many (Nat) id))
  (let ((many (Maybe $ Nat) same))
    (match many (res-term res) _
      ((TVar y) (match many (code-var _ _ code) _ ((Some _ z) (match many (nat-eq y z) _ ((BTrue) (Some _ y)) ((BFalse) (None _)))) ((None _) (match many (mult-is-many pos) _ ((BTrue) (None _)) ((BFalse) (Some _ y))))))
      (else (None _))))
  (match many same _
    ((Some _ y) (values env res y))
    ((None _) (prepare-argument env pos res))))

(def-fns _ $ (many frame-pairs : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) pairs) -> (many (List $ Pair (Nat) $ Code ctx many-one) r))
  (match many pairs _
    ((Nil _) (Nil _))
    ((Cons _ pair rest)
      (let ((many more)) (notail $ frame-pairs _ rest))
      (match many pair _ ((MkPair _ _ id code)
        (match many (code-var _ _ code) _
          ((Some _ z) (match many (nat-eq id z) _ ((BTrue) more) ((BFalse) (Cons _ pair more))))
          ((None _) (Cons _ pair more))))))))

(def-fns _ $ (many prepare-pack : (erased (List $ List $ Nat) ctx)
    (subterm many (List $ Pair (Nat) $ Code ctx many-one) pairs) ->
    (many (List $ Mult) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) ipk)
    (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk))
  (match many pairs _
    ((Nil _) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _)))
    ((Cons _ pair rest)
      (let-match many pair (MkPair _ _ id code))
      (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (notail $ prepare-pack _ rest))
      (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk)
        (Cons _ code codes) (PkMany _ ms code codes cpk)))))

(def-fns _ $ (many prepared-codes : (erased (List $ List $ Nat) from) (subterm many (List $ Pair (Nat) $ Code from many-one) pairs) (many (Env) env) (many (List $ List $ Nat) ctx) -> (many (List $ Code ctx many-one) codes))
  (match many pairs _
    ((Nil _) (Nil _))
    ((Cons _ pair rest) (match many pair _ ((MkPair _ _ id _) (Cons _ (var-code env ctx id) $ notail $ prepared-codes _ rest env ctx))))))

(def-fns _ $ (many cell-result : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect)
    (many (Env) env) (many (Res) res) (many (Code ctx many-one) code) ->
    (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) out))
  (values env (Cons _ res (Nil _))
    (match many (mult-is-many (pos-mult expect)) (((Code ctx expect) _))
      ((BFalse) (CErased _ expect))
      ((BTrue) (match many (mults-same many-one expect) (((Code ctx expect) _))
        ((None _) (CError _ expect "size")) ((Some _ same) (recast _ expect many-one same code)))))))

(def-fns _ $ (many cells-allowed : (many (Env) env) (many (Nat) mid) -> (many (Bool) r))
  (match many (type-of env mid) _
    ((TMatchable _ nt ext _ _) (and (not nt) (or (not ext) (env-in-extern env))))
    (else (BFalse))))

(def-fns _ $ (many cell-shape : (many (Env) env) (many (Nat) c) ->
    (many (Env) env2) (many (Ctor) ctor) (many (List $ Entry) params) (many (Term) ret) (many (Mult) mark))
  (let ((many params) (many ret)) (ctor-type env c))
  (let ((many tid)) (tid-of env c))
  (let ((many env1) (many found)) (find-matchable env tid))
  (match many found _
    ((None _)
      (values (env-error env1 "cell constructor has no opened `Matchable`")
        (MkCtor (name-of env c) c 0 (many-count params) (BFalse) (None _) (Nil _) (BFalse)) params ret (Erased)))
    ((Some _ info)
      (let-match many info (MkMatchInfo mid disc cs rank))
      (let ((many env2)) (match many (type-of env1 mid) (((Env) _))
        ((TMatchable _ nt ext _ _)
          (error-when (error-when env1 nt "newtype constructors have no cells")
            (and ext (not (env-in-extern env1))) "extern constructors have no cells outside an extern model"))
        (else (env-error env1 "invalid cell `Matchable`"))))
      (let ((many env2b)) (error-unless env2 (list-mem-bin (mctor-ids cs) c)
        (str-cat3 (name-of env2 c) " is not a constructor of " (name-of env2 tid))))
      (let ((many env2d)) (error-unless env2b (mult-is-many $ marker cs c) "phantom constructors have no cells"))
      (let ((many ss)) (shapes cs env2d))
      (values env2d (MkCtor (name-of env2d c) c (discriminant ss c) (many-count params)
        (tagged-of disc ss) (None _) (cshape-arities (non-phantom ss)) (BFalse)) params ret (marker cs c)))))

(def-fns _ $ (many pattern-slots : (subterm many (List $ Entry) params) (many (List $ Nat) ids) -> (many (List $ Term) slots))
  (match many params _
    ((Nil _) (Nil _))
    ((Cons _ entry2 rest)
      (match many ids _
        ((Nil _) (Nil _))
        ((Cons _ id tail2)
          (let ((many slots)) (notail $ pattern-slots rest tail2))
          (match many (entry-mult entry2) _ ((Erased) slots) (else (Cons _ (TSlotHolds (TVar id)) slots))))))))

(def-fns _ $ (many pattern-cell : (many (Env) env) (many (Mult) mult) (many (Res) scrut)
    (many (Nat) ctor) (many (List $ Nat) fids) (many (Maybe $ String) name) -> (many (Env) env2) (many (Nat) id))
  (let ((many params) (many ret)) (ctor-type env ctor))
  (let ((many env1) (many id)) (bind env name (None _) (BFalse) mult (TCell (TVar ctor) (pattern-slots params fids)) (None _) delegate-id))
  (let ((many env2)) (mark-word env1 id (BFalse)))
  (let ((many env3)) (match many (res-place scrut) (((Env) _))
    ((None _) env2) ((Some _ place) (at-merge env2 (TVar id) place))))
  (values env3 id))

(def-fns _ $ (many field-mults : (subterm many (List $ Mult) ms) (many (Mult) mode) -> (many (List $ Mult) r))
  (match many ms _ ((Nil _) ms) ((Cons _ m rest) (Cons _ (field-under mode m) $ notail $ field-mults rest mode))))

(def-fns _ $ (many split-pattern-fields : (subterm many (List $ Entry) tele) (many (List $ Raw) fields) -> (many (List $ Raw) prefix) (many (List $ Raw) suffix))
  (match many tele _
    ((Nil _) (values (Nil _) fields))
    ((Cons _ _ rest) (match many fields _
      ((Nil _) (values (Nil _) fields))
      ((Cons _ f tail2) (let ((many prefix) (many suffix)) (notail $ split-pattern-fields rest tail2)) (values (Cons _ f prefix) suffix))))))

(def-fns _ $ (many pattern-fields : (many (Env) env) (many (Nat) c) (many (List $ Entry) tele) (many (List $ Raw) fields) (many (Bool) extra) -> (many (Env) out) (many (List $ Raw) ordinary) (many (Maybe $ String) name))
  (let ((many env14)) (error-unless env (atoms-only fields) "pattern binders must be names or `_`"))
  (match many extra _
    ((BFalse) (values (match many (nat-cmp (list-length _ fields) (list-length _ tele)) _ ((CEq _ _ _) env14) (else (env-error env14 $ str-cat3 (qname env14 c) " has " $ str-cat (nat-str $ list-length _ tele) " fields"))) fields (None _)))
    ((BTrue)
      (let ((many env1)) (match many (nat-cmp (list-length _ fields) (Succ $ list-length _ tele)) (((Env) _)) ((CEq _ _ _) env14) (else (env-error env14 "unique constructor pattern needs fields and a cell binder"))))
      (let ((many ordinary) (many rest)) (split-pattern-fields tele fields))
      (values env1 ordinary (match many rest (((Maybe $ String) _)) ((Nil _) (None _)) ((Cons _ r _) (name-or-anon $ raw-name r)))))))

(def-fns _ $ (many pattern-cell-option : (many (Env) env) (many (Mult) mult) (many (Res) scrut) (many (Nat) c) (many (List $ Nat) fids) (many (Bool) extra) (many (Maybe $ String) name) -> (many (Env) out) (many (Maybe $ Nat) cell))
  (match many extra _
    ((BFalse) (values env (None _)))
    ((BTrue)
      (let ((many env1) (many id)) (pattern-cell env mult scrut c fids name))
      (let ((many env2)) (match many (res-term scrut) (((Env) _)) ((TVar x) (forward-state env1 id x)) (else env1)))
      (values env2 (Some _ id)))))


(def-adts $ (ElseBody : ((Raw) raw) -> Type)
  enum
  (many MkElseBody : (erased (Raw) raw) (many (Maybe $ String) name) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) raw) p) -> (ElseBody raw)))
(def-fns _ $ (many else-parts : (many (Raw) raw) (many (Bool) extra) -> (many (Maybe $ ElseBody raw) r))
  (match many raw _
    ((RList _ items) (match many items _
      ((Nil _) (None _))
      ((Cons _ _ body) (match many extra _
        ((BFalse) (Some _ $ MkElseBody raw (None _) body $ prove-subterm body raw))
        ((BTrue) (match many body _
          ((Nil _) (None _))
          ((Cons _ name rest) (match many (raw-atom name) _ ((None _) (None _)) ((Some _ n) (Some _ $ MkElseBody raw (name-or-anon n) rest $ prove-subterm rest raw))))))))))
    (else (None _))))

(def-fns _ $ (many else-binder : (many (Env) env) (many (Res) scrut) (many (Mult) mult) (many (Bool) extra) (many (Maybe $ String) name) -> (many (Env) out) (many (Maybe $ Nat) binder))
  (match many extra _
    ((BFalse) (values env (None _)))
    ((BTrue)
      (let ((many env1) (many x)) (bind env name (None _) (BFalse) mult (res-ty scrut) (Some _ $ res-term scrut) delegate-id))
      (let ((many env2)) (mark-word env1 x (BFalse)))
      (let ((many env3)) (match many (res-place scrut) (((Env) _)) ((None _) env2) ((Some _ loc) (at-merge env2 (TVar x) loc))))
      (values env3 (Some _ x)))))

(def-fns _ $ (many slot-direct : (many (Env) env) (many (Raw) raw) -> (many (Env) env2) (many (Nat) id))
  (let ((many env1) (many id)) (var-of-raw env raw "a direct variable reference"))
  (let ((many env2)) (error-unless env1 (mult-is-many (entry-mult-of env1 id)) "`SlotHolds` needs a declared non-erased variable"))
  (values (error-when env2 (list-mem-bin (env-signature env2) id) "`SlotHolds` cannot name a telescope binder; abstract over a `Slot` instead") id))

(def-fns _ $ (many cell-slot-codes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) -> (many (List $ Code ctx many-one) codes))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ id rest)
      (Cons _ (match many id (((Code ctx many-one) _))
        ((None _) (CValue _ (BToken _))) ((Some _ x) (var-code env ctx x))) (notail $ cell-slot-codes env ctx rest)))))

(def-fns _ $ (many cell-slot-writes : (many (Env) env) (many (List $ List $ Nat) ctx)
    (subterm many (List $ Maybe $ Nat) ids) (many (Nat) index) -> (many (List $ Pair (Nat) $ Code ctx many-one) writes))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ id rest)
      (let ((many writes)) (notail $ cell-slot-writes env ctx rest (Succ index)))
      (match many id _ ((None _) writes) ((Some _ x) (Cons _ (MkPair _ _ index (var-code env ctx x)) writes))))))

(def-fns _ $ (many cell-alloc-result : (many (Env) env) (many (List $ List $ Nat) ctx)
    (many (List $ Mult) expect) (many (Nat) c) (many (Ctor) ct) (many (List $ Term) slots)
    (many (List $ Maybe $ Nat) slotids) (many (List $ Pair (Nat) $ Code ctx many-one) pairs) ->
    (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
  (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (prepare-pack _ pairs))
  (let ((many env1) (many x)) (bind env (None _) (None _) (BFalse) (under (pos-mult expect) (Once)) (TCell (TVar c) slots) (None _) delegate-id))
  (cell-result _ expect env1 (res-with-place (res-of env1 x) (None _))
    (CLet _ ms _ ids ipk (CValues _ ms codes cpk)
      (CCellAlloc _ ct (cell-slot-codes env1 (Cons _ ids ctx) slotids)))))

(def-fns _ $ (many cell-mark-token : (many (Env) env) (many (Raw) raw) -> (many (Bool) is-at))
  (match many raw _
    ((RList _ items)
      (match many items _ ((Cons _ m rest) (and (list-is-empty _ rest) (is-mark env m (MkAt)))) ((Nil _) (BFalse))))
    (else (BFalse))))

(def-fns _ $ (many cell-marks : (erased (List $ Raw) root) (subterm many (List $ Sub root) items)
    (many (Env) env) (many (Bool) pending) -> (many (Env) env2) (many (List $ Sub root) args) (many (List $ Bool) marks))
  (match many items _
    ((Nil _) (values (error-when env pending "`at` must precede an argument") (Nil _) (Nil _)))
    ((Cons _ item rest)
      (let-match many item (MkSub rt raw p))
      (match many (cell-mark-token env raw) _
        ((BTrue) (tail $ cell-marks _ rest env (BTrue)))
        ((BFalse)
          (let ((many env2) (many args) (many marks)) (notail $ cell-marks _ rest env (BFalse)))
          (values env2 (Cons _ item args) (Cons _ pending marks)))))))

(def-fns _ $ (many cell-invoke-writes : (many (Env) env) (many (List $ List $ Nat) ctx) (many (Bool) full)
    (subterm many (List $ Entry) params) (many (List $ Term) terms) (many (List $ Bool) marks)
    (many (List $ Term) slots) (many (Nat) index) -> (many (Env) env2) (many (List $ Pair (Nat) $ Code ctx many-one) writes))
  (match many params _
    ((Nil _) (values env (Nil _)))
    ((Cons _ param rest)
      (let ((many term) (many ts)) (match many terms (((Term) _) ((List $ Term) xs))
        ((Nil _) (values (TErr "missing argument") (Nil _))) ((Cons _ x xs) (values x xs))))
      (let ((many skip) (many ms)) (match many marks (((Bool) _) ((List $ Bool) xs))
        ((Nil _) (values (BFalse) (Nil _))) ((Cons _ x xs) (values x xs))))
      (match many (entry-mult param) _
        ((Erased) (tail $ cell-invoke-writes (error-when env skip "`at` cannot mark an erased argument") ctx full rest ts ms slots index))
        (else
          (let ((many slot) (many ss)) (match many slots (((Term) _) ((List $ Term) xs))
            ((Nil _) (values (TErr "missing slot") (Nil _))) ((Cons _ x xs) (values x xs))))
          (let ((many same)) (match many (canon-env env slot) (((Bool) _))
            ((TSlotHolds target) (at-equal env target term)) (else (BFalse))))
          (let ((many omit)) (or full skip))
          (let ((many env1)) (error-when env (and omit (not same))
            (str-cat3 "`at` argument " (nat-str (Succ index)) " is not in its slot's location class")))
          (let ((many env2) (many writes)) (notail $ cell-invoke-writes env1 ctx full rest ts ms ss (Succ index)))
          (values env2 (match many omit (((List $ Pair (Nat) $ Code ctx many-one) _))
            ((BTrue) writes) ((BFalse) (Cons _ (MkPair _ _ index (var-code env2 ctx (term-var term))) writes)))))))))

(def-fns _ $ (many cell-read-bindings : (many (Env) env) (many (List $ List $ Nat) ctx)
    (many (Nat) sid) (many (Ctor) k2) (subterm many (Nat) n) (many (List $ Raw) names)
    (many (List $ Term) slots) (many (Mult) pos) (many (Nat) index) ->
    (many (Env) env2) (many (List $ Pair (Nat) $ Code ctx many-one) pairs) (many (List $ Raw) restnames))
  (match many n _
    ((Zero) (values env (Nil _) names))
    ((Succ k)
      (match many names _
        ((Nil _) (values (env-error env "`cell-match` needs more binders") (Nil _) (Nil _)))
        ((Cons _ name rest)
          (let ((many slot) (many ss)) (match many slots (((Term) _) ((List $ Term) ss))
            ((Nil _) (values (TErr "missing slot") (Nil _))) ((Cons _ s ss) (values s ss))))
          (let ((many env1) (many id)) (bind env (name-or-anon (raw-name name)) (None _) (BFalse) (under pos (Many)) slot-term (Some _ slot) delegate-id))
          (let ((many env2)) (mark-word env1 id (BFalse)))
          (let ((many env3) (many pairs) (many restnames)) (notail $ cell-read-bindings env2 ctx sid k2 k rest ss pos (Succ index)))
          (values env3 (Cons _ (MkPair _ _ id (CCellRead _ k2 index (var-code env3 ctx sid))) pairs) restnames))))))

(def-fns _ $ (many parse-entries-checked : (erased (List $ Raw) root) (subterm many (List $ Sub root) subs) (many (Env) env) -> (many (Env) r) (many (List $ SrcEntry root) es))
  (match many subs _
    ((Nil _) (values env $ Nil _))
    ((Cons _ s rest)
      (let ((many (Env) env1) (many (List $ SrcEntry root) here))
        (match many s _
          ((MkSub _ r p)
            (match many (raw-atom r) (((Env) _) ((List $ SrcEntry root) l))
              ((Some _ str) (values (env-error env $ str-cat "expected a telescope entry, got " str) $ Nil _))
              ((None _)
                (let ((many es)) $ parse-entry env r _ p)
                (match many es (((Env) _) ((List $ SrcEntry root) l))
                  ((Nil _) (values (env-error env $ str-cat "malformed telescope entry " $ qraw r) es))
                  ((Cons _ _ _) (values env es))))))))
      (let ((many env2) (many more)) $ notail $ parse-entries-checked _ rest env1)
      (let ((many all) (erased cat)) $ list-append _ here more)
      (values env2 all))))

(def-fns _ $ (many check-binder-mults : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) (many (Env) env) -> (many (Env) r))
  (match many es _
    ((Nil _) env)
    ((Cons _ e rest)
      (match many e _
        ((MkSrcEntry _ _ m _ _ _ _)
          (match many m _
            ((Some _ _) (tail $ check-binder-mults _ rest env))
            ((None _) (tail $ check-binder-mults _ rest $ env-error env "`let` binder needs a multiplicity"))))))))

(def-fns _ $ (many colon-checked : (many (Env) env) (many (Raw) colon) (many (Env) bad) -> (many (Env) r))
  (match many (is-mark env colon $ MkColon) _ ((BTrue) env) ((BFalse) bad)))

(def-fns _ $ (many mult-checked : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Mult) m))
  (match many (mult-of env raw) _
    ((Some _ m) (values env m))
    ((None _) (values (env-error env $ str-cat "expected a multiplicity, got " $ qraw raw) $ Many))))

(def-fns _ $ (many level-var-checked : (many (Env) env) (many (Term) t) -> (many (Env) r) (many (Nat) x))
  (def-fns msg-lvl $ (many bad : -> (many (Env) r)) (env-error env $ str-cat (qshow env t) " is not a level"))
  (match many (canon-env env t) _
    ((TVar x) (match many (equal-env env (type-of env x) level-term) _ ((BTrue) (values env x)) ((BFalse) (values (bad) x)))) (else (values (bad) $ Zero))))

(def-fns _ $ (many one-arg : (many (List $ Raw) args) -> (many (Raw) r))
  (match many args _ ((Nil _) (RAtom (MkPos 0 0) "_")) ((Cons _ r _) r)))

(def-fns _ $ (many comptime-shape : (many (List $ Raw) args) -> (many (Maybe $ Pair (Raw) $ Pair (Raw) $ List $ Raw) r))
  (match many args _
    ((Nil _) (None _))
    ((Cons _ x rest)
      (match many rest _
        ((Nil _) (None _))
        ((Cons _ pat more)
          (match many more _
            ((Cons _ _ _) (None _))
            ((Nil _)
              (match many (raw-items pat) _
                ((Nil _) (None _))
                ((Cons _ craw fields)
                  (match many (atoms-only fields) _
                    ((BTrue) (Some _ $ MkPair _ _ x $ MkPair _ _ craw fields))
                    ((BFalse) (None _))))))))))))

; numeral-of (ASSUMPTIONS 53): a numeral or character literal by its own spelling, never an expression.
(def-fns _ $ (many numeral-of-key : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Env) env) (many (String) key) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
  (match many (lit-lookup env key) _
    ((None _) (expr-error _ expect env (str-cat3 "literal " key " is not in scope") "numeral-of"))
    ((Some _ x)
      (match many (lit-proof (env-lits env) x) _
        ((None _) (expr-error _ expect env (str-cat key " is a string literal, which carries no `Numeral` proof") "numeral-of"))
        ((Some _ p) (values env (Cons _ (res-of env p) $ Nil _) $ CErased _ expect))))))

(def-fns _ $ (many numeral-of-lit : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Env) env) (many (Raw) arg) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
  (match many arg _
    ((RList _ _) (expr-error _ expect env (str-cat "expected a literal, got " $ qraw arg) "numeral-of"))
    ((RString _ _) (expr-error _ expect env (str-cat (show-r arg) " is a string literal, which carries no `Numeral` proof") "numeral-of"))
    ((RAtom _ s)
      (match many (literal-error s) _
        ((Some _ msg) (expr-error _ expect env msg "numeral-of"))
        ((None _)
          (match many (classify s) _
            ((LName) (expr-error _ expect env (str-cat "`numeral-of` takes a literal, not " $ tick s) "numeral-of")) (else (numeral-of-key _ expect env s))))))))

; The number a numeral or character literal spells, if the raw is one (lib/literal.ml's classify).
(def-fns _ $ (many lit-number : (many (Raw) raw) -> (many (Maybe $ Nat) n))
  (match many raw _
    ((RAtom _ s)
      (match many (literal-error s) _
        ((Some _ _) (None _))
        ((None _)
          (match many (classify s) _
            ((LName) (None _))
            ((LNumeral) (Some _ $ parse-nat s 0))
            ((LChar) (char-lit-code s)))))) (else (None $ Nat))))

; The entry holding the Nat a numeral or character literal stands for, a character's being its code's
; (lib/elab.ml's numeral_entry).
(def-fns _ $ (many numeral-entry : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ Nat) e))
  (match many (lit-number raw) _
    ((None _)
      (values (env-error env
                (match many raw (((String) _))
                  ((RAtom _ s) (str-cat s " is not a numeral or character literal")) (else (str-cat "expected a numeral or character literal, got " $ show-r raw))))
              $ None _))
    ((Some _ z)
      (match many (lit-lookup env $ nat-str z) _
        ((None _) (values (env-error env $ str-cat3 "literal " (nat-str z) " is not in scope") $ None _))
        ((Some _ x) (values env $ Some _ $ MkPair _ _ z x))))))

; A generated form is read and its literals interned in the prelude's scope, so user shadowing cannot
; reach it, and the caller's scope restored after; the level context stays the caller's throughout
; (lib/elab.ml's in_prelude).
(def-fns _ $ (many generated-form : (many (Raw) g) (many (Env) env) -> (many (Env) r))
  (intern-literals g $ env-set-scope env $ env-prelude env))

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

; A branch of the raw b: present, refuted automatically with (absurd C), or absurd by proof (section 12).
(def-adts $ (BranchParts : ((Raw) b) -> Type)
  enum
  (many BPresent : (erased (Raw) b) (many (Raw) craw) (many (List $ Raw) fields) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) b) p) -> (BranchParts b))
  (many BRefuted : (erased (Raw) b) (many (Raw) craw) -> (BranchParts b))
  (many BAbsurd : (erased (Raw) b) (many (Raw) craw) (many (List $ Raw) fields) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) b) p) -> (BranchParts b)))

(def-fns _ $ (many pattern-parts : (many (Raw) pat) -> (many (Maybe $ Pair (Raw) $ List $ Raw) r))
  (match many pat _
    ((RAtom _ _) (Some _ $ MkPair _ _ pat $ Nil _))
    ((RString _ _) (None _))
    ((RList _ items)
      (match many items _
        ((Nil _) (None _))
        ((Cons _ c fs) (match many (atoms-only fs) _ ((BTrue) (Some _ $ MkPair _ _ c fs)) ((BFalse) (None _))))))))

(def-fns _ $ (many branch-parts : (many (Env) env) (many (Raw) braw) -> (many (Maybe $ BranchParts braw) r))
  (match many braw _
    ((RList _ items)
      (match many items _
        ((Nil _) (None _))
        ((Cons _ first more)
          (match many (is-mark env first $ MkAbsurd) _
            ((BFalse)
              (match many (pattern-parts first) _
                ((None _) (None _))
                ((Some _ pp) (match many pp _ ((MkPair _ _ c fs) (Some _ $ BPresent _ c fs more $ prove-subterm more braw))))))
            ((BTrue)
              (match many more _
                ((Nil _) (None _))
                ((Cons _ pat body)
                  (match many body _
                    ((Nil _)
                      (match many (raw-atom pat) _
                        ((Some _ _) (Some _ $ BRefuted _ pat))
                        ((None _) (None _))))
                    ((Cons _ _ _)
                      (match many (pattern-parts pat) _
                        ((None _) (None _))
                        ((Some _ pp) (match many pp _ ((MkPair _ _ cc fs) (Some _ $ BAbsurd _ cc fs body $ prove-subterm body braw)))))))))))))) (else (None $ BranchParts braw))))

(def-fns _ $ (many marker-checked : (many (Env) env) (many (Nat) tid) (many (List $ MCtor) mctors) (many (Nat) c) -> (many (Env) r) (many (Mult) m))
  (match many (mctors-list mctors c) _
    ((BTrue) (values env $ marker mctors c))
    ((BFalse) (values (env-error env $ str-cat3 (qname env c) " is not a constructor of " $ qname env tid) $ Many))))

(def-fns _ $ (many scrutinee-matchable : (many (Env) env) (many (Mult) smult) (many (Res) sres) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ MatchInfo) found))
  (let ((many env1)) $ settle-res env sres)
  (match many (type-head env1 $ res-ty sres) _
    ((None _) (values (env-error env1 $ str-cat3 "cannot match on " (qshow env1 $ res-term sres) $ str-cat " : " $ qshow env1 $ res-ty sres) $ None _))
    ((Some _ tid)
      (let ((many env2) (many found)) $ find-matchable env1 tid)
      (match many found _
        ((None _) (values (env-error env2 $ str-cat (qname env2 tid) " has no `Matchable` open") $ None _))
        ((Some _ info)
          (values (match many (mult-is-many smult) (((Env) _)) ((BTrue) (warn-use env2 (env-loc env2) "match on" $ TVar tid)) ((BFalse) env2))
            $ Some _ $ MkPair _ _ tid info))))))

(def-fns _ $ (many check-field-count : (many (Env) env) (many (Nat) c) (many (List $ Raw) fields) (many (List $ Entry) tele) -> (many (Env) r))
  (match many (nat-cmp (list-length _ fields) $ list-length _ tele) _
    ((CEq _ _ _) env)
    (else (env-error env $ str-cat3 (qname env c) " has " $ str-cat (nat-str $ list-length _ tele) " fields"))))

(def-fns _ $ (many count-bins : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Nat) n))
  (match many xs _
    ((Nil _) 0)
    ((Cons _ y rest) (match many (nat-cmp x y) _ ((CEq _ _ _) (Succ $ notail $ count-bins rest x)) (else (tail $ count-bins rest x))))))

; Every constructor of the Matchable appears exactly once (ASSUMPTIONS 21).
(def-fns _ $ (many is-else-branch : (many (Env) env) (many (Raw) braw) -> (many (Bool) r))
  (match many braw _
    ((RList _ items) (match many items _ ((Nil _) (BFalse)) ((Cons _ first _) (is-mark env first $ MkElse)))) (else (BFalse))))

; The unlisted constructors an else stands for: those whose forced unification does not contradict; the first of
; them, and whether any could run (section 12).
; The forcing trial for constructor [c], [m] its multiplicity marker: the environment it opens its fields in, and
; whether forcing contradicts. covered-of and the error path's ctor-trial both run it.
(def-fns _ $ (many run-trial : (many (Mult) m) (many (Nat) c) (many (Env) env) (many (Res) sres) (many (Mult) smult) -> (many (Env) envb) (many (UnifyRes) u))
  (let ((many ctele) (many ret)) $ ctor-type env c)
  (let ((many (List $ Mult) mults)) $ match many (mult-is-many m) _ ((BFalse) (all-erased $ tele-mults ctele)) ((BTrue) (field-mults (tele-mults ctele) smult)))
  (let ((many envb) (many fids) (many u)) $ open-fields (env-set-run-pos env $ BFalse) ctele (anon-names ctele) (anon-sites ctele) (Some _ mults) sres c ret)
  (values envb u))

(def-fns _ $ (many covered-of : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Nat) seen) (many (Res) sres) (many (Mult) smult) (many (Maybe $ Nat) first) (many (Bool) reachable) (many (List $ Nat) covered) -> (many (Env) r) (many (Maybe $ Nat) first2) (many (Bool) reachable2) (many (List $ Nat) covered2))
  (match many mctors _
    ((Nil _) (values env first reachable covered))
    ((Cons _ mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let ((many c)) $ term-var t)
          (match many (nat-cmp (count-bins seen c) 0) _
            (else (tail $ covered-of rest env seen sres smult first reachable covered))
            ((CEq _ _ _)
              (let ((many phantom)) $ not $ mult-is-many m)
              (let ((many envb) (many u)) $ run-trial m c env sres smult)
              (match many u _
                ((UContra _) (tail $ covered-of rest (env-discard env envb) seen sres smult first reachable covered))
                ((UOk envb2)
                  (tail $ covered-of rest (env-discard env envb2) seen sres smult
                    (match many first (((Maybe $ Nat) _)) ((None _) (Some _ c)) ((Some _ _) first))
                    (or reachable $ not $ and phantom $ mult-is-many smult)
                    $ match many phantom (((List $ Nat) _)) ((BTrue) covered) ((BFalse) (Cons _ c covered))))))))))))

; The environment the forcing trial for constructor [c] leaves, as covered-of runs it, where it does not
; refute the constructor.
(def-fns _ $ (many ctor-trial : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Mult) smult) (many (Nat) c) -> (many (Maybe $ Env) r))
  (match many mctors _
    ((Nil _) (None _))
    ((Cons _ mc rest)
      (match many mc _
        ((MkMCtor m t)
          (match many (nat-eq (term-var t) c) _
            ((BFalse) (tail $ ctor-trial rest env sres smult c))
            ((BTrue)
              (let ((many envb) (many u)) $ run-trial m c env sres smult)
              (match many u _ ((UContra _) (None _)) ((UOk envb2) (Some _ envb2))))))))))

; An error about branches forcing left standing, with the notes each trial's literals earn.
(def-fns _ $ (many forced-error : (many (List $ MCtor) mctors) (many (Env) env) (many (Res) sres) (many (Mult) smult) (subterm many (List $ Nat) cs) (many (Env) out) -> (many (Env) r))
  (match many cs _
    ((Nil _) out)
    ((Cons _ c rest)
      (let ((many out2)) $ match many (ctor-trial mctors env sres smult c) (((Env) _)) ((None _) out) ((Some _ trial) (forced-notes env trial sres out)))
      (tail $ forced-error mctors env sres smult rest out2))))

(def-fns _ $ (many discs-of : (subterm many (List $ Nat) cs) (many (List $ CShape) ss) -> (many (List $ Nat) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest) (Cons _ (discriminant ss c) $ notail $ discs-of rest ss))))

(def-fns _ $ (many check-coverage : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Nat) seen) -> (many (Env) r))
  (match many mctors _
    ((Nil _) env)
    ((Cons _ mc rest)
      (match many mc _
        ((MkMCtor _ t)
          (let ((many c)) $ term-var t)
          (let ((many n)) $ count-bins seen c)
          (match many (nat-lt 1 n) _
            ((BFalse) (tail $ check-coverage rest env seen))
            ((BTrue) (tail $ check-coverage rest (env-error env $ str-cat3 "constructor " (qname env c) $ str-cat3 " has " (nat-str n) " branches") seen))))))))


; The ids at the many positions of a list of multiplicities, in step, as the frame a binder list makes.
(def-fns _ $ (many many-of : (subterm many (List $ Mult) ms) (many (List $ Nat) ids) -> (many (List $ Nat) r))
  (match many ms _
    ((Nil _) (Nil _))
    ((Cons _ m rest)
      (match many ids _
        ((Nil _) (Nil _))
        ((Cons _ x xrest) (match many m _ ((Many) (Cons _ x $ notail $ many-of rest xrest))
                                          ((Once) (Cons _ x $ notail $ many-of rest xrest)) ((Erased) (tail $ many-of rest xrest))))))))

; Whether a def-fns group binds a many function; a group of erased ones leaves nothing behind (ASSUMPTIONS 77).
; ---- The elaborator proper: one block recursing on the raws it elaborates (self/README.md)

; What the statements read from their raws, holding the parts they elaborate later inside those raws.
(def-adts
  ((Header : ((Raw) f) -> Type)
    enum
    (many MkHeader : (erased (Raw) f) (many (Pos) site) (many (String) name) (many (Mult) mult) (many (Bool) is-unique) (many (Bool) is-absurd) (many (Maybe $ Impl) impl) (many (List $ Entry) params) (many (List $ Entry) rets) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) f) p) -> (Header f)))
  ((Headers : ((List $ Raw) fns) -> Type)
    enum
    (many HStop : (erased (List $ Raw) fns) -> (Headers fns))
    (many HCons : (erased (Raw) f) (erased (List $ Raw) rest) (many (Header f) h) (many (Headers rest) hs) -> (Headers $ Cons (Raw) f rest)))
  ; [gids]: the frame the group binds, its many functions' ids; an erased function is checked and leaves nothing
  ; behind (ASSUMPTIONS 77).
  ((Bound : ((List $ Raw) fns) ((Headers fns) hs) ((List $ Nat) gids) -> Type)
    enum
    (many BStop : (erased (List $ Raw) fns) -> (Bound fns (HStop fns) (Nil (Nat))))
    (many BMany : (erased (Raw) f) (erased (List $ Raw) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Nat) gids) (many (Nat) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Raw) f rest) (HCons f rest h hs) (Cons (Nat) x gids)))
    (many BErased : (erased (Raw) f) (erased (List $ Raw) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Nat) gids) (many (Nat) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Raw) f rest) (HCons f rest h hs) gids)))
  ((AdtHeader : ((Raw) f) -> Type)
    enum
    (many MkAdtHeader : (erased (Raw) f) (many (String) name) (many (Disc) disc) (many (Bool) is-newtype) (many (Bool) is-extern) (many (List $ Raw) ctors) (erased (Subterm (List $ Raw) ctors (Raw) f) p) -> (AdtHeader f)))
  ((AdtHeaders : ((List $ Raw) adts) -> Type)
    enum
    (many AStop : (erased (List $ Raw) adts) -> (AdtHeaders adts))
    (many AHCons : (erased (Raw) f) (erased (List $ Raw) rest) (many (AdtHeader f) h) (many (AdtHeaders rest) hs) -> (AdtHeaders $ Cons (Raw) f rest)))
  ((Tids : ((List $ Raw) adts) ((AdtHeaders adts) hs) -> Type)
    enum
    (many TStop : (erased (List $ Raw) adts) -> (Tids adts $ AStop adts))
    (many TCons : (erased (Raw) f) (erased (List $ Raw) rest) (erased (AdtHeader f) h) (erased (AdtHeaders rest) hs) (many (Nat) x) (many (Tids rest hs) more) -> (Tids (Cons (Raw) f rest) $ AHCons f rest h hs)))
  ((LetParts : ((List $ Raw) args) -> Type)
    enum
    (many MkLetParts : (erased (List $ Raw) args) (many (List $ SrcEntry args) binders) (many (List $ Raw) rhs) (erased (Within rhs args) wr) -> (LetParts args)))
  ((CtorParts : ((Raw) c) -> Type)
    enum
    (many MkCtorParts : (erased (Raw) c) (many (Mult) mult) (many (String) name) (many (List $ Raw) sg) (erased (Subterm (List $ Raw) sg (Raw) c) p) -> (CtorParts c))))

(def-adts $ (RealBranch : ((List $ List $ Nat) ctx) ((List $ Mult) ns) -> Type)
  enum
  (many MkRealBranch : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (many (Nat) c) (many (List $ Nat) fids) (many (Code (Cons (List (Nat)) fids ctx) ns) code) -> (RealBranch ctx ns)))

(def-fns _ $ (many real-ctors : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ RealBranch ctx ns) bs) -> (many (List $ Nat) r))
  (match many bs _
    ((Nil _) (Nil _))
    ((Cons _ b rest) (match many b _ ((MkRealBranch _ _ c _ _) (Cons _ c $ notail $ real-ctors _ _ rest))))))

(def-fns _ $ (many real-branches-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ RealBranch ctx ns) bs) (many (List $ CShape) ss) -> (many (List $ Branch ctx ns) r))
  (match many bs _
    ((Nil _) (Nil _))
    ((Cons _ b rest)
      (match many b _
        ((MkRealBranch _ _ c fids code) (Cons _ (MkBranch _ _ (discriminant ss c) fids code) $ notail $ real-branches-code _ _ rest ss))))))

(def-fns _ $ (many bind-headers : (erased (List $ Raw) fns) (subterm many (Headers fns) hs) (many (Env) env) (many (Nat) lvl) -> (many (Env) r) (many (List $ Nat) gids) (many (Bound fns hs gids) ids))
  (match many hs _
    ((HStop _) (values env (Nil _) (BStop _)))
    ((HCons _ _ h more)
      (match many h _
        ((MkHeader _ hpos name mult uq _ _ params rets _ _)
          (let ((many env2) (many x)) $ bind env (Some _ name) (Some _ $ loc-in env hpos) (BTrue) mult (TFn uq (TVar lvl) params rets) (None _) delegate-id)
          (let ((many env3) (many gids) (many ids)) $ notail $ bind-headers _ more (mark-word env2 x $ BFalse) lvl)
          (match many mult _
            ((Many) (values env3 (Cons _ x gids) (BMany _ _ _ _ _ x ids)))
            ((Once) (values env3 (Cons _ x gids) (BMany _ _ _ _ _ x ids)))
            ((Erased) (values env3 gids (BErased _ _ _ _ _ x ids)))))))))

(def-fns _ $ (many set-const-states : (subterm many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) cs) (many (Env) env) -> (many (Env) r))
  (match many cs _
    ((Nil _) env)
    ((Cons _ p rest)
      (match many p _
        ((MkPair _ _ id v) (tail $ set-const-states rest $ set-state-closed env id v))))))

(def-fns _ $ (many ctor-values : (subterm many (List $ Ctor) cs) -> (many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest) (Cons _ (MkPair _ _ (ctor-id c) $ BCtorFn _ c) $ notail $ ctor-values rest))))

(def-fns _ $ (many mctors-of : (subterm many (List $ Pair (Mult) $ Nat) cs) -> (many (List $ MCtor) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ p rest) (match many p _ ((MkPair _ _ m c) (Cons _ (MkMCtor m $ TVar c) $ notail $ mctors-of rest))))))


(def-fns _ $ (many codes-missing : (erased (List $ List $ Nat) ctx) (subterm many (List $ Mult) ms) -> (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) pk))
  (match many ms _
    ((Nil _) (values (Nil _) (PkNil _)))
    ((Cons _ m rest)
      (let ((many codes) (erased pk)) $ notail $ codes-missing ctx rest)
      (let ((many (Code ctx many-one) missing)) $ no-code _)
      (match many m _
        ((Many) (values (Cons _ missing codes) (PkMany _ rest missing codes pk)))
        ((Once) (values (Cons _ missing codes) (PkOnce _ rest missing codes pk)))
        ((Erased) (values codes (PkErased _ rest codes pk)))))))

(def-fns _ $ (many bin-ids-of : (subterm many (List $ Term) ts) -> (many (List $ Nat) r))
  (match many ts _
    ((Nil _) (Nil _))
    ((Cons _ t rest)
      (match many t _
        ((TVar x) (Cons _ x $ notail $ bin-ids-of rest)) (else (tail $ bin-ids-of rest))))))

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
    (many RNil : (erased (List $ List $ Nat) ctx) -> (Ren (Nil (List (Nat))) ctx))
    (many RFrame : (erased (List $ Nat) f) (erased (List $ List $ Nat) rest) (erased (List $ List $ Nat) ctx) (many (List $ Atom ctx) atoms) (erased (Lockstep (Nat) (Atom ctx) f atoms) lk) (many (Ren rest ctx) r) -> (Ren (Cons (List (Nat)) f rest) ctx))))

(def-fns _ $ (many atom-code : (erased (List $ List $ Nat) ctx) (many (Atom ctx) a) -> (many (Code ctx many-one) r))
  (match many a _ ((AVar _ x p) (CVar _ x p)) ((AConst _ x) (CConst _ x))))

(def-fns _ $ (many atom-there : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (many (Atom ctx) a) -> (many (Atom (Cons (List (Nat)) f ctx)) r))
  (match many a _ ((AVar _ x p) (AVar _ x $ MThere _ _ _ p)) ((AConst _ x) (AConst _ x))))

(def-fns _ $ (many atoms-there : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (subterm many (List $ Atom ctx) as) -> (many (List $ Atom (Cons (List (Nat)) f ctx)) r) (erased (Lockstep (Atom ctx) (Atom (Cons (List (Nat)) f ctx)) as r) lk))
  (match many as _
    ((Nil _) (values (Nil _) (LsNil _ _)))
    ((Cons _ x rest)
      (let ((many r) (erased lk)) $ notail $ atoms-there ctx f rest)
      (let ((many y)) $ atom-there _ f x)
      (values (Cons _ y r) (LsCons _ _ x y rest r lk)))))

(def-fns _ $ (many self-atoms : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (subterm many (List $ AtIn f) ats) -> (many (List $ Atom (Cons (List (Nat)) f ctx)) r) (erased (Lockstep (AtIn f) (Atom (Cons (List (Nat)) f ctx)) ats r) lk))
  (match many ats _
    ((Nil _) (values (Nil _) (LsNil _ _)))
    ((Cons _ at2 rest)
      (let ((many r) (erased lk)) $ notail $ self-atoms ctx f rest)
      (let ((many (Atom (Cons (List (Nat)) f ctx)) atom)) $ match many at2 _ ((MkAtIn _ x p) (AVar _ x $ MHere _ _ _ p)))
      (values (Cons _ atom r) (LsCons _ _ at2 atom rest r lk)))))

(def-fns _ $ (many ren-under : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (erased (List $ Nat) f) (subterm many (Ren from ctx) ren) -> (many (Ren from (Cons (List (Nat)) f ctx)) r))
  (match many ren _
    ((RNil _) (RNil _))
    ((RFrame _ _ _ atoms lk r)
      (let ((many atoms2) (erased lk2)) $ atoms-there _ f atoms)
      (RFrame _ _ _ atoms2 (lockstep-trans _ _ _ _ _ _ lk lk2) $ notail $ ren-under _ _ f r))))

(def-fns _ $ (many ren-weaken : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (Ren from ctx) ren) -> (many (Ren (Cons (List (Nat)) f from) (Cons (List (Nat)) f ctx)) r))
  (let ((many ats) (erased lk)) $ at-ins f)
  (let ((many atoms) (erased lk2)) $ self-atoms ctx _ ats)
  (RFrame _ _ _ atoms (lockstep-trans _ _ _ _ _ _ lk lk2) $ ren-under _ _ f ren))

(def-fns _ $ (many ren-id : (subterm many (List $ List $ Nat) ctx) -> (many (Ren ctx ctx) r))
  (match many ctx _
    ((Nil _) (RNil _))
    ((Cons _ f rest) (ren-weaken _ _ f $ notail $ ren-id rest))))

(def-fns _ $ (many ren-get : (erased (Nat) x) (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (Mem x from) p) (many (Ren from ctx) ren) -> (many (Atom ctx) r))
  (match many p _
    ((MHere _ _ _ q)
      (let-match many ren (RFrame g rest c2 atoms lk r))
      (let ((many a) (erased sq)) $ at-get _ _ _ q atoms lk) a)
    ((MThere _ _ _ q)
      (let-match many ren (RFrame g rest c2 atoms lk r))
      (tail $ ren-get _ _ _ q r))))

; The atoms a let binds, if its right-hand side is nothing but variables and constants.
(def-fns _ $ (many atoms-of : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Atom ctx) r))
  (match many cs _
    ((Nil _) (Some _ $ Nil _))
    ((Cons _ c rest)
      (match many (notail $ atoms-of _ rest) _
        ((None _) (None _))
        ((Some _ more)
          (match many c _
            ((CVar _ x p) (Some _ $ Cons _ (AVar _ x p) more))
            ((CConst _ x) (Some _ $ Cons _ (AConst _ x) more)) (else (None $ List $ Atom ctx))))))))

(def-fns _ $ (many rhs-atoms : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (many (Code ctx ms) c) -> (many (Maybe $ List $ Atom ctx) r))
  (match many c _
    ((CVar _ x p) (Some _ $ Cons _ (AVar _ x p) $ Nil _))
    ((CConst _ x) (Some _ $ Cons _ (AConst _ x) $ Nil _))
    ((CErased _ _) (Some _ $ Nil _))
    ((CValues _ _ cs _) (atoms-of _ cs)) (else (None $ List $ Atom ctx))))

(def-fns _ $ (many vars-of : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Nat) r))
  (match many cs _
    ((Nil _) (Some _ $ Nil _))
    ((Cons _ c rest)
      (match many c _
        ((CVar _ x _)
          (match many (notail $ vars-of _ rest) _
            ((None _) (None _))
            ((Some _ xs) (Some _ $ Cons _ x xs)))) (else (None $ List $ Nat))))))

(def-fns _ $ (many bins-eq : (subterm many (List $ Nat) as) (many (List $ Nat) bs) -> (many (Bool) r))
  (match many as _
    ((Nil _) (list-is-empty _ bs))
    ((Cons _ x rest) (match many bs _ ((Nil _) (BFalse)) ((Cons _ y brest) (and (nat-eq x y) $ notail $ bins-eq rest brest))))))

; Whether a body returns exactly the let's ids, in order, with the two erasure lists then agreeing on their many entries.
(def-fns _ $ (many returns-same : (erased (List $ List $ Nat) ctx) (subterm many (List $ Mult) ms) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (subterm many (List $ Mult) ns) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ns cs) qk) -> (many (Maybe $ ManySame ms ns) r))
  (match many (vars-of _ cs) _
    ((None _) (None _))
    ((Some _ vars)
      (match many (bins-eq ids vars) _
        ((BTrue) (mults-same ms ns))
        ((BFalse) (None _))))))

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
  (match many d _
    ((DHere _ _) (match many p _ ((MHere _ _ _ _) (None _)) ((MThere _ _ _ q) (Some _ q))))
    ((DUnder _ _ _ d2)
      (match many p _
        ((MHere _ _ _ at2) (Some _ $ MHere _ _ _ at2))
        ((MThere _ _ _ q) (match many (notail $ mem-drop _ _ _ q d2) _ ((Some _ q2) (Some _ $ MThere _ _ _ q2)) ((None _) (None _))))))))

(def-fns _
  ((many strengthen : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code from ms) c) (many (Drop from ctx) d) -> (many (Maybe $ Code ctx ms) r))
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
        (match many (notail $ strengthen _ _ _ f d) _
          ((None _) (None _))
          ((Some _ f2)
            (match many (notail $ strengthen-list _ _ args d) _
              ((KNo _ _ _) (None _))
              ((KYes _ _ _ args2 _) (Some _ $ CApp _ ms2 f2 args2 cc))))))
      ((CLet _ ms2 _ ids pk rhs rest)
        (match many (notail $ strengthen _ _ _ rhs d) _
          ((None _) (None _))
          ((Some _ rhs2)
            (match many (notail $ strengthen _ _ _ rest $ DUnder _ _ _ d) _
              ((None _) (None _))
              ((Some _ rest2) (Some _ $ CLet _ ms2 _ ids pk rhs2 rest2))))))
      ((CLetRec _ _ _ g rest)
        (match many g _
          ((MkGroup _ ids fns lk)
            (match many (notail $ strengthen-fns _ _ ids fns d) _
              ((KNo _ _ _) (None _))
              ((KYes _ _ _ fns2 lk2)
                (match many (notail $ strengthen _ _ _ rest $ DUnder _ _ _ d) _
                  ((None _) (None _))
                  ((Some _ rest2) (Some _ $ CLetRec _ _ _ (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2) rest2))))))))
      ((CMatch _ ns scrut shape bs dfl live)
        (match many (notail $ strengthen _ _ _ scrut d) _
          ((None _) (None _))
          ((Some _ scrut2)
            (let ((many (Maybe $ Shape ctx) shape2))
              (match many shape _
                ((ShKnown _ adt) (Some _ $ ShKnown _ adt))
                ((ShNone _) (Some _ $ ShNone _))
                ((ShHeld _ mc tags) (match many (notail $ strengthen _ _ _ mc d) _ ((None _) (None _)) ((Some _ mc2) (Some _ $ ShHeld _ mc2 tags))))))
            (match many shape2 _
              ((None _) (None _))
              ((Some _ sh)
                (match many (notail $ strengthen-branches _ _ ns bs d) _
                  ((None _) (None _))
                  ((Some _ bs2)
                    (match many dfl _
                      ((None _) (Some _ $ CMatch _ ns scrut2 sh bs2 (None _) live))
                      ((Some _ dd)
                        (match many (notail $ strengthen _ _ _ dd $ DUnder _ _ _ d) _
                          ((None _) (None _))
                          ((Some _ dd2) (Some _ $ CMatch _ ns scrut2 sh bs2 (Some _ dd2) live))))))))))))

      ((CCellAlloc _ ctor slots)
        (match many (notail $ strengthen-list _ _ slots d) _ ((KNo _ _ _) (None _)) ((KYes _ _ _ slots2 _) (Some _ $ CCellAlloc _ ctor slots2))))
      ((CCellWrite _ k2 cell slots)
        (match many (notail $ strengthen _ _ _ cell d) _
          ((None _) (None _))
          ((Some _ cell2) (match many (notail $ strengthen-slots _ _ slots d) _ ((None _) (None _)) ((Some _ slots2) (Some _ $ CCellWrite _ k2 cell2 slots2))))))
      ((CCellRead _ k2 index cell)
        (match many (notail $ strengthen _ _ _ cell d) _ ((None _) (None _)) ((Some _ cell2) (Some _ $ CCellRead _ k2 index cell2))))
      ((CAbsurd _ ms2) (Some _ $ CAbsurd _ ms2))
      ((CError _ ms2 m) (Some _ $ CError _ ms2 m))))
  ((many strengthen-list : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code from many-one) cs) (many (Drop from ctx) d) -> (many (Kept (Code from many-one) (Code ctx many-one) cs) r))
    (match many cs _
      ((Nil _) (KYes _ _ _ (Nil _) (LsNil _ _)))
      ((Cons _ c rest)
        (match many (notail $ strengthen _ _ _ c d) _
          ((None _) (KNo _ _ _))
          ((Some _ c2)
            (match many (notail $ strengthen-list _ _ rest d) _
              ((KNo _ _ _) (KNo _ _ _))
              ((KYes _ _ _ r lk) (KYes _ _ _ (Cons _ c2 r) (LsCons _ _ c c2 rest r lk)))))))))

  ((many strengthen-slots : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code from many-one) slots) (many (Drop from ctx) d) -> (many (Maybe $ List $ Pair (Nat) $ Code ctx many-one) r))
    (match many slots _
      ((Nil _) (Some _ $ Nil _))
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ index code)
        (match many (notail $ strengthen _ _ _ code d) _
          ((None _) (None _))
          ((Some _ code2) (match many (notail $ strengthen-slots _ _ rest d) _ ((None _) (None _)) ((Some _ rest2) (Some _ $ Cons _ (MkPair _ _ index code2) rest2))))))))))

  ((many strengthen-fns : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids from) fns) (many (Drop from ctx) d) -> (many (Kept (Pair (Nat) $ Func gids from) (Pair (Nat) $ Func gids ctx) fns) r))
    (match many fns _
      ((Nil _) (KYes _ _ _ (Nil _) (LsNil _ _)))
      ((Cons _ p rest)
        (match many p _
          ((MkPair _ _ id fn)
            (let ((many (Maybe $ Func gids ctx) fn2))
              (match many fn _
                ((MkFunc _ _ rets n i ps body impl top)
                  (match many (notail $ strengthen _ _ _ body $ DUnder _ _ _ $ DUnder _ _ _ d) _ ((None _) (None _)) ((Some _ body2) (Some _ $ MkFunc _ _ rets n i ps body2 impl top))))
                ((MkAlias _ _ n i target)
                  (match many (notail $ strengthen _ _ _ target $ DUnder _ _ _ d) _ ((None _) (None _)) ((Some _ t2) (Some _ $ MkAlias _ _ n i t2))))))
            (match many fn2 _
              ((None _) (KNo _ _ _))
              ((Some _ f2)
                (match many (notail $ strengthen-fns _ _ gids rest d) _
                  ((KNo _ _ _) (KNo _ _ _))
                  ((KYes _ _ _ r lk)
                    (let ((many p2)) $ MkPair _ _ id f2)
                    (KYes _ _ _ (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))))))))))
  ((many strengthen-branches : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch from ns) bs) (many (Drop from ctx) d) -> (many (Maybe $ List $ Branch ctx ns) r))
    (match many bs _
      ((Nil _) (Some _ $ Nil _))
      ((Cons _ b rest)
        (match many b _
          ((MkBranch _ _ dsc ids body)
            (match many (notail $ strengthen _ _ _ body $ DUnder _ _ _ d) _
              ((None _) (None _))
              ((Some _ body2)
                (match many (notail $ strengthen-branches _ _ ns rest d) _
                  ((None _) (None _))
                  ((Some _ r) (Some _ $ Cons _ (MkBranch _ _ dsc ids body2) r)))))))))))

; A let's right-hand side of values embedded by elaboration alone, as lib/elab.ml's constant.
(def-fns _ $ (many all-values : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r))
  (match many cs _
    ((Nil _) (BTrue))
    ((Cons _ c rest) (match many c _ ((CValue _ _) (tail $ all-values _ rest)) (else (BFalse))))))

(def-fns _ $ (many constant-rhs : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (many (Code ctx ms) c) -> (many (Bool) r))
  (match many c _ ((CErased _ _) (BTrue)) ((CValue _ _) (BTrue)) ((CValues _ _ cs _) (all-values _ cs)) (else (BFalse))))

(def-fns _ $ (many normal-values : (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ms cs) pk) -> (many (Code ctx ms) r))
  (match many ms _
    ((Cons _ m rest)
      (match many m _
        ((Many) (match many rest _
          ((Nil _) (match many cs _
            ((Cons _ code more) (match many more _ ((Nil _) code) (else (CValues _ ms cs pk))))
            (else (CValues _ ms cs pk))))
          (else (CValues _ ms cs pk))))
        (else (CValues _ ms cs pk))))
    (else (CValues _ ms cs pk))))

(def-fns _
  ((many norm : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Mult) ms) (subterm many (Code from ms) c) (many (Ren from ctx) ren) -> (many (Code ctx ms) r))
    (match many c _
      ((CVar _ _ p) (atom-code _ $ ren-get _ _ _ p ren))
      ((CConst _ x) (CConst _ x))
      ((CValue _ v) (CValue _ v))
      ((CErased _ ms2) (CErased _ ms2))
      ((CValues _ ms2 cs pk)
        (let ((many cs2) (erased lk)) $ notail $ norm-list _ _ cs ren)
        (normal-values _ ms2 cs2 $ picked-along _ _ _ _ _ pk lk))
      ((CApp _ ms2 f as cc)
        (let ((many as2) (erased lk)) $ notail $ norm-list _ _ as ren)
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
        (match many dropped _
          ((Some _ ren2) (tail $ norm _ _ ms rest ren2))
          ((None _)
            (let ((many rest2)) $ notail $ norm _ _ ms rest $ ren-weaken _ _ ids ren)
            (let ((many (Maybe $ ManySame ms2 ms) same))
              (match many rest2 _
                ((CVar _ y p) (returns-same _ ms2 ids pk many-one (Cons _ (CVar _ y p) $ Nil _) $ PkMany _ (Nil _) (CVar _ y p) (Nil _) $ PkNil _))
                ((CValues _ ns3 cs pk3) (returns-same _ ms2 ids pk ns3 cs pk3))
                (else (None _))))
            (match many same _
              ((Some _ p) (recast _ ms ms2 p rhs2))
              ((None _)
                (let ((many (Maybe $ Code ctx ms) gone)) $ match many (constant-rhs _ _ rhs2) _ ((BTrue) (strengthen _ _ _ rest2 $ DHere _ _)) ((BFalse) (None _)))
                (match many gone _
                  ((Some _ r) r)
                  ((None _) (CLet _ ms2 _ ids pk rhs2 rest2))))))))
      ((CLetRec _ _ _ g rest) (match many g _ ((MkGroup _ ids _ _) (CLetRec _ _ _ (notail $ norm-group _ _ _ g ren) $ notail $ norm _ _ ms rest $ ren-weaken _ _ ids ren))))
      ((CMatch _ ns scrut shape bs dfl live)
        (let ((many (Maybe $ Code ctx ns) dropped))
          (match many shape _
            ((ShNone _)
              (match many bs _
                ((Nil _) (match many dfl _ ((Some _ d) (Some _ $ notail $ norm _ _ ns d $ RFrame _ _ _ (Nil _) (LsNil _ _) ren)) ((None _) (None _))))
                ((Cons _ b rest)
                  (match many rest _
                    ((Cons _ _ _) (None _))
                    ((Nil _)
                      (match many b _
                        ((MkBranch _ _ _ ids body)
                          (match many ids _
                            ((Nil _) (Some _ $ notail $ norm _ _ ns body $ RFrame _ _ _ (Nil _) (LsNil _ _) ren))
                            ((Cons _ _ _) (None _))))))))))
            (else (None _))))
        (match many dropped _
          ((Some _ d) d)
          ((None _)
            (CMatch _ ns (notail $ norm _ _ many-one scrut ren)
                    (match many shape (((Shape ctx) _)) ((ShKnown _ adt) (ShKnown _ adt)) ((ShNone _) (ShNone _)) ((ShHeld _ mc tags) (ShHeld _ (notail $ norm _ _ many-one mc ren) tags)))
                    (notail $ norm-branches _ _ ns bs ren)
                    (match many dfl (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _)) ((Some _ d) (Some _ $ notail $ norm _ _ ns d $ ren-weaken _ _ (Nil _) ren)) ((None _) (None _)))
                    live))))

      ((CCellAlloc _ ctor slots)
        (let ((many slots2) (erased lk)) $ notail $ norm-list _ _ slots ren)
        (CCellAlloc _ ctor slots2))
      ((CCellWrite _ k2 cell slots) (CCellWrite _ k2 (notail $ norm _ _ many-one cell ren) $ notail $ norm-slots _ _ slots ren))
      ((CCellRead _ k2 index cell) (CCellRead _ k2 index $ notail $ norm _ _ many-one cell ren))
      ((CAbsurd _ ms2) (CAbsurd _ ms2))
      ((CError _ ms2 m) (CError _ ms2 m))))
  ((many norm-list : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code from many-one) cs) (many (Ren from ctx) ren) -> (many (List $ Code ctx many-one) r) (erased (Lockstep (Code from many-one) (Code ctx many-one) cs r) lock))
    (match many cs _
      ((Nil _) (values (Nil _) (LsNil _ _)))
      ((Cons _ c rest)
        (let ((many r) (erased p)) $ notail $ norm-list _ _ rest ren)
        (let ((many c2)) $ notail $ norm _ _ many-one c ren)
        (values (Cons _ c2 r) (LsCons _ _ c c2 rest r p)))))

  ((many norm-slots : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code from many-one) slots) (many (Ren from ctx) ren) -> (many (List $ Pair (Nat) $ Code ctx many-one) r))
    (match many slots _
      ((Nil _) (Nil _))
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ index code) (Cons _ (MkPair _ _ index $ notail $ norm _ _ many-one code ren) $ notail $ norm-slots _ _ rest ren))))))

  ((many norm-group : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (erased (List $ Nat) gids) (subterm many (Group gids from) g) (many (Ren from ctx) ren) -> (many (Group gids ctx) r))
    (match many g _
      ((MkGroup _ ids fns lk)
        (let ((many fns2) (erased lk2)) $ notail $ norm-fns _ _ ids fns ren)
        (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2))))
  ((many norm-fns : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids from) fns) (many (Ren from ctx) ren) -> (many (List $ Pair (Nat) $ Func gids ctx) r) (erased (Lockstep (Pair (Nat) $ Func gids from) (Pair (Nat) $ Func gids ctx) fns r) lk))
    (match many fns _
      ((Nil _) (values (Nil _) (LsNil _ _)))
      ((Cons _ p rest)
        (let ((many r) (erased lk)) $ notail $ norm-fns _ _ gids rest ren)
        (match many p _
          ((MkPair _ _ id fn)
            (let ((many (Func gids ctx) fn2))
              (match many fn _
                ((MkFunc _ _ rets n i ps body impl top) (MkFunc _ _ rets n i ps (notail $ norm _ _ rets body $ ren-weaken _ _ ps $ ren-weaken _ _ gids ren) impl top))
                ((MkAlias _ _ n i target) (MkAlias _ _ n i $ notail $ norm _ _ many-one target $ ren-weaken _ _ gids ren))))
            (let ((many p2)) $ MkPair _ _ id fn2)
            (values (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))))))
  ((many norm-branches : (erased (List $ List $ Nat) from) (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch from ns) bs) (many (Ren from ctx) ren) -> (many (List $ Branch ctx ns) r))
    (match many bs _
      ((Nil _) (Nil _))
      ((Cons _ b rest) (match many b _ ((MkBranch _ _ d ids body) (Cons _ (MkBranch _ _ d ids $ notail $ norm _ _ ns body $ ren-weaken _ _ ids ren) $ notail $ norm-branches _ _ ns rest ren)))))))

(def-fns _ $ (many bind-lift : (many (List $ List $ Nat) ctx) (many (List $ Mult) ns) (many (List $ Nat) ids) (many (List $ Nat) frame)
    (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (Code (Cons (List (Nat)) ids (Cons (List (Nat)) frame ctx)) ns) r))
  (norm _ _ ns rest $ ren-weaken _ _ ids $ ren-under _ _ frame $ ren-id ctx))

(def-fns _
  ((many bind-through : (many (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (List $ Mult) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk)
      (subterm many (Code ctx ms) rhs) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (Code ctx ns) r))
    (match many rhs _
      ((CLet _ first _ frame fpk value body)
        (CLet _ first _ frame fpk value $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest))
      ((CLetRec _ _ _ group body)
        (match many group _ ((MkGroup _ frame _ _)
          (CLetRec _ _ _ group $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest))))
      ((CMatch _ _ scrut shape branches dflt live)
        (match many (rhs-atoms _ _ rest) _
          ((None _) (CLet _ ms _ ids pk rhs rest))
          ((Some _ _)
            (CMatch _ ns scrut shape (notail $ bind-through-branches ctx ms ns ids pk branches rest)
              (match many dflt (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ns) _))
                ((None _) (None _))
                ((Some _ body) (Some _ $ notail $ bind-through (Cons _ (Nil _) ctx) ms ns ids pk body $ bind-lift ctx ns ids (Nil _) rest))) live))))
      (else (CLet _ ms _ ids pk rhs rest))))
  ((many bind-through-branches : (many (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (List $ Mult) ns) (many (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk)
      (subterm many (List $ Branch ctx ms) branches) (many (Code (Cons (List (Nat)) ids ctx) ns) rest) -> (many (List $ Branch ctx ns) r))
    (match many branches _
      ((Nil _) (Nil _))
      ((Cons _ branch more)
        (match many branch _ ((MkBranch _ _ disc frame body)
          (Cons _ (MkBranch _ _ disc frame $ notail $ bind-through (Cons _ frame ctx) ms ns ids pk body $ bind-lift ctx ns ids frame rest)
            $ notail $ bind-through-branches ctx ms ns ids pk more rest)))))))

(def-fns _
  ((many distribute : (many (List $ List $ Nat) ctx) (many (List $ Mult) ms) (subterm many (Code ctx ms) code) -> (many (Code ctx ms) r))
    (match many code _
      ((CLet _ first _ ids pk rhs rest)
        (bind-through ctx first ms ids pk (notail $ distribute ctx first rhs) $ notail $ distribute (Cons _ ids ctx) ms rest))
      ((CLetRec _ _ _ group rest)
        (match many group _ ((MkGroup _ ids fns lk)
          (let ((many fs) (erased lk2)) $ notail $ distribute-fns ctx ids fns)
          (CLetRec _ _ _ (MkGroup _ ids fs $ lockstep-trans _ _ _ _ _ _ lk lk2) $ notail $ distribute (Cons _ ids ctx) ms rest))))
      ((CMatch _ _ scrut shape branches dflt live)
        (CMatch _ ms (notail $ distribute ctx many-one scrut)
          (match many shape (((Shape ctx) _)) ((ShKnown _ _) shape) ((ShNone _) shape) ((ShHeld _ mc adt) (ShHeld _ (notail $ distribute ctx many-one mc) adt)))
          (notail $ distribute-branches ctx ms branches)
          (match many dflt (((Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) ms) _)) ((None _) (None _)) ((Some _ body) (Some _ $ notail $ distribute (Cons _ (Nil _) ctx) ms body))) live))
      ((CValues _ _ values2 pk)
        (let ((many vs) (erased lk)) $ notail $ distribute-list ctx values2)
        (CValues _ ms vs $ picked-along _ _ _ _ _ pk lk))
      ((CApp _ _ fn args cc)
        (let ((many as) (erased lk)) $ notail $ distribute-list ctx args)
        (CApp _ ms (notail $ distribute ctx many-one fn) as cc))
      ((CCellAlloc _ ctor slots)
        (let ((many ss) (erased lk)) $ notail $ distribute-list ctx slots)
        (CCellAlloc _ ctor ss))
      ((CCellWrite _ k2 cell slots) (CCellWrite _ k2 (notail $ distribute ctx many-one cell) $ notail $ distribute-slots ctx slots))
      ((CCellRead _ k2 index cell) (CCellRead _ k2 index $ notail $ distribute ctx many-one cell))
      (else code)))
  ((many distribute-list : (many (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) codes) ->
      (many (List $ Code ctx many-one) r) (erased (Lockstep (Code ctx many-one) (Code ctx many-one) codes r) lk))
    (match many codes _
      ((Nil _) (values (Nil _) $ LsNil _ _))
      ((Cons _ code rest)
        (let ((many c)) $ notail $ distribute ctx many-one code)
        (let ((many cs) (erased lk)) $ notail $ distribute-list ctx rest)
        (values (Cons _ c cs) $ LsCons _ _ code c rest cs lk))))
  ((many distribute-slots : (many (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) -> (many (List $ Pair (Nat) $ Code ctx many-one) r))
    (match many slots _
      ((Nil _) (Nil _))
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ index code)
        (Cons _ (MkPair _ _ index $ notail $ distribute ctx many-one code) $ notail $ distribute-slots ctx rest))))))
  ((many distribute-branches : (many (List $ List $ Nat) ctx) (many (List $ Mult) ms) (subterm many (List $ Branch ctx ms) branches) -> (many (List $ Branch ctx ms) r))
    (match many branches _
      ((Nil _) (Nil _))
      ((Cons _ branch rest) (match many branch _ ((MkBranch _ _ disc ids body)
        (Cons _ (MkBranch _ _ disc ids $ notail $ distribute (Cons _ ids ctx) ms body) $ notail $ distribute-branches ctx ms rest))))))
  ((many distribute-fns : (many (List $ List $ Nat) ctx) (many (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) ->
      (many (List $ Pair (Nat) $ Func gids ctx) r) (erased (Lockstep (Pair (Nat) $ Func gids ctx) (Pair (Nat) $ Func gids ctx) fns r) lk))
    (match many fns _
      ((Nil _) (values (Nil _) $ LsNil _ _))
      ((Cons _ pair rest) (match many pair _ ((MkPair _ _ id fn)
        (let ((many (Func gids ctx) fn2))
          (match many fn _
            ((MkFunc _ _ ms name fid ps body impl top) (MkFunc _ _ ms name fid ps (notail $ distribute (Cons _ ps $ Cons _ gids ctx) ms body) impl top))
            ((MkAlias _ _ _ _ _) fn)))
        (let ((many p)) $ MkPair _ _ id fn2)
        (let ((many more) (erased lk)) $ notail $ distribute-fns ctx gids rest)
        (values (Cons _ p more) $ LsCons _ _ pair p rest more lk)))))))

(def-fns _ $ (many normalize : (many (List $ List $ Nat) ctx) (many (List $ Mult) ms) (many (Code ctx ms) code) -> (many (Code ctx ms) r))
  (norm _ _ ms (distribute ctx ms $ norm _ _ ms code $ ren-id ctx) $ ren-id ctx))


; ---- tail and delegate (section 9, ASSUMPTIONS 17): judged on the normalized post-erasure code, per
; function, so a nested def-fns's marks are its own.

(def-fns _ $ (many cc-marked : (many (CC) cc) (many (Bool) only-delegate) -> (many (Bool) r))
  (match many cc _ ((CCTail) (not only-delegate)) ((CCDelegate) (BTrue)) (else (BFalse))))

(def-fns _ $ (many marked-call : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (CC) cc) -> (many (Bool) r))
  (match many code _
    ((CApp _ _ _ _ cc2) (cc-eq cc cc2))
    ((CLet _ _ _ _ _ rhs rest) (or (notail $ marked-call _ _ rhs cc) $ notail $ marked-call _ _ rest cc))
    (else (BFalse))))

(def-fns _
  ((many has-marked : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) (many (Bool) only) -> (many (Bool) r))
    (match many c _
      ((CApp _ _ f args cc) (or (cc-marked cc only) $ or (notail $ has-marked _ _ f only) $ notail $ has-marked-list _ args only))

      ((CCellAlloc _ _ slots) (tail $ has-marked-list _ slots only))
      ((CCellWrite _ _ cell slots) (or (notail $ has-marked _ _ cell only) $ notail $ has-marked-slots _ slots only))
      ((CCellRead _ _ _ cell) (tail $ has-marked _ _ cell only))
      ((CValues _ _ cs _) (tail $ has-marked-list _ cs only))
      ((CLet _ _ _ _ _ rhs rest) (or (notail $ has-marked _ _ rhs only) $ notail $ has-marked _ _ rest only))
      ((CLetRec _ _ _ _ rest) (tail $ has-marked _ _ rest only))
      ((CMatch _ _ scrut shape bs dfl _) (or (notail $ has-marked _ _ scrut only) $ or (match many shape (((Bool) _)) ((ShKnown _ _) (BFalse)) ((ShNone _) (BFalse)) ((ShHeld _ mc _) (notail $ has-marked _ _ mc only))) $ or (notail $ has-marked-branches _ _ bs only) $ match many dfl (((Bool) _)) ((Some _ d) (notail $ has-marked _ _ d only)) ((None _) (BFalse)))) (else (BFalse))))
  ((many has-marked-list : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Bool) only) -> (many (Bool) r))
    (match many cs _
      ((Nil _) (BFalse))
      ((Cons _ c rest) (or (notail $ has-marked _ _ c only) $ notail $ has-marked-list _ rest only))))

  ((many has-marked-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Bool) only) -> (many (Bool) r))
    (match many slots _
      ((Nil _) (BFalse))
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ _ code) (or (notail $ has-marked _ _ code only) $ notail $ has-marked-slots _ rest only))))))

  ((many has-marked-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) only) -> (many (Bool) r))
    (match many bs _
      ((Nil _) (BFalse))
      ((Cons _ b rest) (match many b _ ((MkBranch _ _ _ _ body) (or (notail $ has-marked _ _ body only) $ notail $ has-marked-branches _ _ rest only)))))))

; Every marked call sits in tail position: the body's final call, through lets, let recs and match branches
; for tail, directly for delegate.
(def-fns _
  ((many tails-ok : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) (many (Bool) direct) -> (many (Bool) r))
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
        (match many direct _
          ((BTrue) (not $ has-marked _ _ c $ BFalse))
          ((BFalse) (and (not $ has-marked _ _ scrut $ BFalse)
                      (and (match many shape (((Bool) _)) ((ShKnown _ _) (BTrue)) ((ShNone _) (BTrue)) ((ShHeld _ mc _) (not $ has-marked _ _ mc $ BFalse)))
                        (and (notail $ tails-ok-branches _ _ bs direct)
                          $ match many dfl (((Bool) _)) ((Some _ d) (notail $ tails-ok _ _ d direct)) ((None _) (BTrue))))))))

      ((CCellAlloc _ _ slots) (not $ has-marked-list _ slots $ BFalse))
      ((CCellWrite _ _ cell slots) (and (not $ has-marked _ _ cell $ BFalse) $ not $ has-marked-slots _ slots $ BFalse))
      ((CCellRead _ _ _ cell) (not $ has-marked _ _ cell $ BFalse))
      ((CValues _ _ cs _) (not $ has-marked-list _ cs $ BFalse)) (else (BTrue))))
  ((many tails-ok-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) direct) -> (many (Bool) r))
    (match many bs _
      ((Nil _) (BTrue))
      ((Cons _ b rest) (match many b _ ((MkBranch _ _ _ _ body) (and (notail $ tails-ok _ _ body direct) $ notail $ tails-ok-branches _ _ rest direct)))))))

; Every call with whether it sits in tail position, as tails-ok reads it: a notail call there is refused, and
; an unmarked same-level call warns, naming the mark that fits.
(def-fns _ $ (many report-call : (many (CC) cc) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
  (match many cc _
    ((CCNoTail) (error-when env in-tail "a `notail`-marked call is in tail position"))
    ((CCSame l callee)
      (env-warn-at env l $ str-cat3 "same-level call to " (qshow env callee) $ str-cat " is unmarked; mark it "
        $ match many in-tail (((String) _)) ((BTrue) "`tail`") ((BFalse) "`notail`")))
    (else env)))

(def-fns _
  ((many call-report : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
    (match many c _
      ((CApp _ _ f args cc)
        (let ((many env1)) $ report-call cc in-tail env)
        (let ((many env2)) $ notail $ call-report _ _ f (BFalse) env1)
        (tail $ call-report-list _ args env2))
      ((CCellAlloc _ _ slots) (tail $ call-report-list _ slots env))
      ((CCellWrite _ _ cell slots)
        (let ((many env1)) $ notail $ call-report _ _ cell (BFalse) env)
        (tail $ call-report-slots _ slots env1))
      ((CCellRead _ _ _ cell) (tail $ call-report _ _ cell (BFalse) env))
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
    (match many cs _
      ((Nil _) env)
      ((Cons _ c rest) (let ((many env1)) $ notail $ call-report _ _ c (BFalse) env) (tail $ call-report-list _ rest env1))))
  ((many call-report-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Env) env) -> (many (Env) r))
    (match many slots _
      ((Nil _) env)
      ((Cons _ slot rest)
        (match many slot _
          ((MkPair _ _ _ code) (let ((many env1)) $ notail $ call-report _ _ code (BFalse) env) (tail $ call-report-slots _ rest env1))))))
  ((many call-report-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) in-tail) (many (Env) env) -> (many (Env) r))
    (match many bs _
      ((Nil _) env)
      ((Cons _ b rest)
        (match many b _
          ((MkBranch _ _ _ _ body) (let ((many env1)) $ notail $ call-report _ _ body in-tail env) (tail $ call-report-branches _ _ rest in-tail env1)))))))

; Validates the marks in a body and returns the normalized code and, for a delegate, the callee (section 9).
(def-fns _ $ (many check-marks : (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) pids) (many (List $ Mult) ms) (many (Code ctx ms) code) -> (many (Env) r) (many (Code ctx ms) code2) (many (Maybe $ Nat) delegated))
  (let ((many code2)) $ normalize ctx ms code)
  (let ((many delegate2)) $ has-marked _ _ code2 $ BTrue)
  (let ((many (String) kind)) $ match many delegate2 _ ((BTrue) "delegate") ((BFalse) "tail"))
  (let ((many env0)) $ call-report _ _ code2 (BTrue) env)
  (let ((many env1)) $ error-unless env0 (tails-ok _ _ code2 delegate2) $ str-cat3 "a " (tick kind) "-marked call is not in tail position")
  (match many delegate2 _
        ((BFalse) (values env1 code2 $ None _))
        ((BTrue)
          (let ((many (Maybe $ Pair (Nat) $ List $ Code ctx many-one) call))
            (match many code2 _
              ((CApp _ _ f args _) (match many f _ ((CVar _ g _) (Some _ $ MkPair _ _ g args)) ((CConst _ g) (Some _ $ MkPair _ _ g args)) (else (None _)))) (else (None _))))
          (match many call _
            ((None _) (values (env-error env1 "`delegate` needs exactly one call to a named function") code2 $ None _))
            ((Some _ pr)
              (match many pr _
                ((MkPair _ _ g args)
                  (let ((many straight)) $ match many (vars-of _ args) (((Bool) _)) ((None _) (BFalse)) ((Some _ ids) (bins-eq ids pids)))
                  (match many straight _
                    ((BTrue) (values env1 code2 $ Some _ g))
                    ((BFalse) (values (env-error env1 "a `delegate` call must pass the function's non-erased parameters straight through") code2 $ None _))))))))))


; A call's decrease annotation (section 9): (predates p) right after the callee, or (subterm p) right before
; the decreasing argument, whose position it carries; a written proof p sits inside the call's arguments
; root, and _ or no annotation at all leaves the proof to the elaborator (SUGAR.md 3).
(def-adts $ (Given : ((List $ Raw) root) -> Type)
  enum
  (many Inferred : (erased (List $ Raw) root) -> (Given root))
  (many Written : (erased (List $ Raw) root) (many (Raw) p) (erased (Subterm (Raw) p (List $ Raw) root) q) -> (Given root)))

(def-adts $ (Ann : ((List $ Raw) root) -> Type)
  enum
  (many AnnNone : (erased (List $ Raw) root) -> (Ann root))
  (many AnnPredates : (erased (List $ Raw) root) (many (Given root) g) -> (Ann root))
  (many AnnSubterm : (erased (List $ Raw) root) (many (Nat) i) (many (Given root) g) -> (Ann root)))

(def-fns _ $ (many given-of : (erased (List $ Raw) root) (many (Raw) p) (erased (Subterm (Raw) p (List $ Raw) root) q) -> (many (Given root) g))
  (match many (is-underscore p) _ ((BTrue) (Inferred _)) ((BFalse) (Written _ p q))))

(def-fns _ $ (many ann-of : (many (Env) env) (many (Raw) arg) (many (Nat) i) (erased (List $ Raw) root) (erased (Subterm (Raw) arg (List $ Raw) root) pa) -> (many (Ann root) r))
  (match many arg _
    ((RList _ items)
      (match many items _
        ((Nil _) (AnnNone _))
        ((Cons _ k krest)
          (match many krest _
            ((Nil _) (AnnNone _))
            ((Cons _ p prest)
              (match many prest _
                ((Cons _ _ _) (AnnNone _))
                ((Nil _)
                  (let ((erased pp)) $ subterm-trans (prove-subterm p arg) pa)
                  (match many (and (is-mark env k $ MkPredates) $ nat-is-zero i) _
                    ((BTrue) (AnnPredates _ $ given-of _ p pp))
                    ((BFalse) (match many (is-mark env k $ MkSubterm) _ ((BTrue) (AnnSubterm _ i $ given-of _ p pp)) ((BFalse) (AnnNone _)))))))))))) (else (AnnNone root))))

; The first annotation and the arguments without it; a second annotation stays an argument, as in lib/elab.ml.
(def-fns _ $ (many split-annotation : (subterm many (List $ Raw) args) (erased (List $ Raw) root) (erased (Within args root) w) (many (Env) env) (many (Nat) i) -> (many (Ann root) ann) (many (List $ Sub root) rest))
  (match many args _
    ((Nil _) (values (AnnNone _) $ Nil _))
    ((Cons _ arg more)
      (let ((erased pa)) $ in-within _ _ _ _ (prove-subterm arg args) w)
      (let ((erased wm)) $ within-step _ _ _ (prove-subterm more args) w)
      (match many (ann-of env arg i _ pa) _
        ((AnnNone _)
          (let ((many ann) (many rest)) $ notail $ split-annotation more _ wm env $ Succ i)
          (values ann $ Cons _ (MkSub _ arg pa) rest))
        ((AnnPredates _ g) (values (AnnPredates _ g) $ subs-of more _ wm))
        ((AnnSubterm _ j g) (values (AnnSubterm _ j g) $ subs-of more _ wm))))))

(def-fns _ $ (many subterm-indices : (subterm many (List $ Entry) tele) (many (Nat) i) -> (many (List $ Nat) r))
  (match many tele _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (match many (entry-sub e) _
        ((BTrue) (Cons _ i $ notail $ subterm-indices rest $ Succ i))
        ((BFalse) (tail $ subterm-indices rest $ Succ i))))))

; A bare call's annotation (SUGAR.md 3): where the levels differ, otherwise at the
; first subterm argument that differs from its counterpart; a written annotation stays as it is.
(def-fns _ $ (many first-differing : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) -> (many (Maybe $ Nat) r))
  (match many positions _
    ((Nil _) (None _))
    ((Cons _ pi rest)
      (match many (list-nth _ (env-subterms env) j) _
        ((NthMiss _ _ _ _) (None _))
        ((NthHit _ _ _ counterpart _)
          (match many (equal-env env (nth-term args pi) $ TVar counterpart) _
            ((BFalse) (Some _ pi))
            ((BTrue) (tail $ first-differing rest env args $ Succ j))))))))

(def-fns _ $ (many resolve-ann : (many (Env) env) (erased (List $ Raw) root) (many (Ann root) ann) (many (Res) callee) (many (Bool) same) (many (List $ Nat) positions) (many (List $ Term) args) -> (many (Env) r) (many (Ann root) a))
  (match many ann _
    ((AnnNone _)
      (match many same _
        ((BFalse) (values env $ AnnPredates _ $ Inferred _))
        ((BTrue)
          (match many (first-differing positions env args 0) _
            ((Some _ i) (values env $ AnnSubterm _ i $ Inferred _))
            ((None _) (values (env-error env $ str-cat3 "same-level call to " (qshow env $ res-term callee) " decreases no subterm argument") $ AnnNone _))))))
    (else (values env ann))))

(def-fns _ $ (many index-of-nat : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (match many xs _
    ((Nil _) (None _))
    ((Cons _ y rest) (match many (nat-cmp x y) _ ((CEq _ _ _) (Some _ i)) (else (tail $ index-of-nat rest x $ Succ i))))))

; Earlier subterm arguments must equal their counterparts (section 9's lexicographic discipline).
(def-fns _ $ (many check-earlier : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) (many (Nat) k) -> (many (Env) r))
  (match many positions _
    ((Nil _) env)
    ((Cons _ pi rest)
      (match many (nat-lt j k) _
        ((BFalse) env)
        ((BTrue)
          (let ((many (Env) env2))
            (match many (list-nth _ (env-subterms env) j) _
              ((NthMiss _ _ _ _) (env-error env $ str-cat3 "the enclosing function has no subterm parameter at position " (nat-str j) ""))
              ((NthHit _ _ _ counterpart _) (check env "value" (nth-term args pi) $ TVar counterpart))))
          (tail $ check-earlier rest env2 args (Succ j) k))))))

(def-fns _ $ (many erased-in-many : (subterm many (List $ Mult) expect) (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) expect ress) lock) (many (Env) env) -> (many (Env) r))
  (match many expect _
    ((Nil _) env)
    ((Cons _ m rest)
      (let-match erased lock (LsCons ta tb x y xs ys p))
      (let-match many ress (Cons b r rrest))
      (def-fns msg-lvl $ (many msg-erased : -> (many (String) s)) (str-cat3 "erased value " (qshow env $ res-term r) $ str-cat3 " : " (qshow env $ res-ty r) " used in a non-erased position"))
      (let ((many env2)) $ error-when-msg env (and (mult-is-many m) $ not $ mult-is-many $ res-erasure r) msg-erased)
      (let ((many env3)) $ match many (and (not $ env-usage-erased env) $ mult-is-many m) (((Env) _))
        ((BFalse) env2)
        ((BTrue) (match many m (((Env) _))
          ((Once)
            (def-fns msg-lvl $ (many msg-many : -> (many (String) s)) (str-cat3 "many value " (qshow env $ res-term r) " used at unique"))
            (error-when-msg env2 (and (mult-is-many $ res-erasure r) $ not $ mult-is-once $ res-erasure r) msg-many))
          ((Many)
            (def-fns msg-lvl $ (many msg-unique : -> (many (String) s)) (str-cat3 "unique value " (qshow env $ res-term r) " needs an explicit `share`"))
            (error-when-msg env2 (mult-is-once $ res-erasure r) msg-unique))
          ((Erased) env2))))
      (tail $ erased-in-many rest rrest p env3))))

(def-fns _ $ (many mode-result-check : (many (Env) env) (many (List $ Res) ress) (many (Bool) final) -> (many (Env) out))
  (match many ress _
    ((Nil _) env)
    ((Cons _ r _)
      (let ((many mode)) (mode-demand env (res-ty r) final))
      (erased-in-many (Cons _ mode (Nil _)) (Cons _ r (Nil _)) (LsCons _ _ mode r (Nil _) (Nil _) (LsNil _ _)) env))))

; A call's or application's argument count against its telescope (lib/elab.ml's check_args).
(def-fns _ $ (many count-check : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r))
  (match many (nat-cmp expected got) _
    ((CEq _ _ _) env)
    (else (count-error env what expected got))))

(def-fns _ $ (many check-arity : (many (Env) env) (many (List $ Entry) tele) (many (Nat) m) -> (many (Env) r))
  (count-check env " arguments" (list-length _ tele) m))

(def-fns _ $ (many malformed : (erased (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
  (expr-error _ expect env (str-cat3 "malformed " (tick $ sp-name sp) " form") "malformed"))

; The field at a wrapping constructor's one many position, given the arguments in order.
(def-fns _ $ (many wrap-field : (subterm many (List $ Entry) tele) (many (List $ Term) args) (many (List $ Term) tys) -> (many (Maybe $ Pair (Term) (Term)) r))
  (match many tele _
    ((Nil _) (None _))
    ((Cons _ e rest)
      (match many args _
        ((Nil _) (None _))
        ((Cons _ t trest)
          (match many tys _
            ((Nil _) (None _))
            ((Cons _ ty tyrest)
              (match many (entry-mult e) _
                ((Many) (match many (many-count rest) _ ((Zero) (Some _ $ MkPair _ _ t ty)) ((Succ _) (None _))))
                ((Once) (match many (many-count rest) _ ((Zero) (Some _ $ MkPair _ _ t ty)) ((Succ _) (None _))))
                ((Erased) (tail $ wrap-field rest trest tyrest))))))))))

(def-fns _ $ (many missing-arg : (many (Env) env) -> (many (Env) r) (many (Nat) x))
  (let ((many env2) (many x)) $ var (env-at env $ MkPos 0 0) "_")
  (values (env-back env env2) x))

(def-fns _ $ (many erased-res : (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) erased-one ress) lock) -> (many (Res) r))
  (first-res _ _ ress lock))

(def-fns _ $ (many erased-term : (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) erased-one ress) lock) -> (many (Term) t))
  (res-term $ erased-res ress lock))

(def-fns _ $ (many settle-empty : (many (Env) env) (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) erased-one ress) lock) -> (many (Env) r))
  (let ((many r)) $ erased-res ress lock)
  (check-empty (settle-res env r) $ res-ty r))

(let ((many no-tele)) $ None $ List $ Entry)

; ---- `_` arguments (SUGAR.md 6): what an application's result looks like over its parameters' metas, and
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
(def-fns _ $ (many sg-type : (many (Env) env) (many (Sg) sg) -> (many (Maybe $ Term) r))
  (match many sg _
    ((SgTy t) (Some _ t))
    ((SgIs t ty) (match many (dangling t 0) _ ((BTrue) (None _)) ((BFalse) (Some _ ty))))))

; A result entry against an expected one: values where both are is-entries, types always.
(def-fns _ $ (many solve-pair : (many (Env) env) (many (Sg) e) (many (Sg) r) (many (Bool) strict) -> (many (Env) r2) (many (Bool) ok))
  (let ((many (Env) env1) (many (Bool) ok1))
    (match many e _
      ((SgIs a _) (match many r (((Env) _) ((Bool) b)) ((SgIs b2 _) (solve env "value" b2 a strict)) ((SgTy _) (values env $ BTrue))))
      ((SgTy _) (values env $ BTrue))))
  (match many ok1 _
    ((BFalse) (values env1 $ BFalse))
    ((BTrue)
      (match many (sg-type env1 r) _
        ((None _) (values env1 $ BTrue))
        ((Some _ rt)
          (match many (sg-type env1 e) _
            ((None _) (values env1 $ BTrue))
            ((Some _ et) (solve env1 "type" rt et strict))))))))

(def-fns _ $ (many solve-tele : (subterm many (List $ Entry) expect) (many (List $ Entry) result) (many (Env) env) (many (Bool) strict) -> (many (Env) r) (many (Bool) ok))
  (match many expect _
    ((Nil _) (values env $ BTrue))
    ((Cons _ e rest)
      (match many result _
        ((Nil _) (values env $ BTrue))
        ((Cons _ r rrest)
          (let ((many env1) (many ok1)) $ solve-pair env (entry-sg e) (entry-sg r) strict)
          (match many ok1 _
            ((BFalse) (values env1 $ BFalse))
            ((BTrue) (tail $ solve-tele rest rrest env1 strict))))))))

; [result] over [mvars] against the expectation, where an application has a `_`: not [strict], a failure
; leaves the environment as it was; strict, the mismatch is reported.
(def-fns _ $ (many solve-against : (many (Env) env) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (List $ Term) mvars) (many (Bool) wilds) (many (Bool) strict) -> (many (Env) r))
  (match many expect _
    ((None _) env)
    ((Some _ tele)
      (match many wilds _
        ((BFalse) env)
        ((BTrue)
          (let ((many res)) $ app-result-tele result mvars)
          (let ((many n)) $ list-length _ tele)
          (let ((many m)) $ list-length _ res)
          (match many (nat-cmp n m) _
            (else (match many strict _ ((BTrue) (count-error env " values" n m)) ((BFalse) env)))
            ((CEq _ _ _)
              (let ((many env2) (many ok)) $ solve-tele tele res env strict)
              (match many (or ok strict) _ ((BTrue) env2) ((BFalse) env)))))))))

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
(def-fns _ $ (many report-unsolved : (subterm many (List $ Term) args) (many (Env) env) (many (Nat) i) -> (many (Env) r))
  (match many args _
    ((Nil _) env)
    ((Cons _ t rest)
      (match many (has-meta-env env t) _
        ((BTrue) (env-error env $ str-cat3 "argument " (nat-str i) " is `_` and cannot be inferred"))
        ((BFalse) (tail $ report-unsolved rest env $ Succ i))))))

(def-fns _ $ (many any-wild : (erased (List $ Raw) root) (subterm many (List $ Sub root) args) -> (many (Bool) r))
  (match many args _
    ((Nil _) (BFalse))
    ((Cons _ s rest) (match many s _ ((MkSub _ arg _) (or (is-underscore arg) $ notail $ any-wild _ rest))))))

; Where each `_` among [args] is written, for the meta that stands for it; nothing for any other argument.
(def-fns _ $ (many wild-sites : (erased (List $ Raw) root) (many (Env) env) (subterm many (List $ Sub root) args) -> (many (List $ Maybe $ Loc) r))
  (match many args _
    ((Nil _) (Nil _))
    ((Cons _ s rest)
      (match many s _
        ((MkSub _ arg _)
          (Cons _ (match many (is-underscore arg) (((Maybe $ Loc) _)) ((BTrue) (Some _ $ loc-in env $ raw-pos arg)) ((BFalse) (None _)))
            $ notail $ wild-sites _ env rest))))))

; comptime-match (section 15): a Const, non-erased scrutinee with a non-erased discriminant, verified
; against the named constructor; the fields are bound Const and the facts refined as a branch would.
; ---- A Const's value printed through its type, for section 15's mismatch message (ASSUMPTIONS 66): a
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
; Nat (section 38), so neither is unwrapped first. None where the type is not one of the three, or the block does
; not carry the payload it would need.
(def-fns _ $ (many lit-rope : (erased (Hist Block) hs) (many (Env) env) (many (Term) ty) (many (Block (Ref Block hs)) blk) -> (many (Maybe $ Rope) r))
  (match many blk _
    ((BExt _ p)
      (match many p (((Maybe $ Rope) _))
        ((PNat n)
          (match many (prelude-nullary env ty "Nat") (((Maybe $ Rope) _))
            ((BTrue) (Some _ $ RStr $ nat-str n))
            ((BFalse)
              (match many (prelude-nullary env ty "Char") (((Maybe $ Rope) _))
                ((BTrue) (Some _ $ lit-char-rope n))
                ((BFalse) (None $ Rope))))))
        ((PStr st)
          (match many (prelude-nullary env ty "String") (((Maybe $ Rope) _))
            ((BTrue) (Some _ $ lit-string-rope st))
            ((BFalse) (None $ Rope))))
        ((PHalf _) (None $ Rope))))
    (else (None $ Rope))))

(def-fns _ $ (many show-plain : (erased (Hist Block) a) (many (Block (Ref Block a)) b) -> (many (Rope) r))
  (match many b _
    ((BExt _ p) (match many p _ ((PNat n) (show-nat n)) ((PHalf x) (show-half x)) ((PStr x) (show-str x))))
    ((BCtorFn _ c) (rwrap "<constructor " (RStr $ ctor-name c) ">"))
    ((BMat _ adt) (rwrap "<matchable " (RStr $ adt-name adt) ">"))
    ((BToken _) (RStr "_"))
    ((BError _ m) (rwrap "<error: " (RStr m) ">"))
    (else (RStr "?"))))

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
  (match many e _
    ((ExtHalf)
      (match many b (((Rope) _))
        ((BExt _ p) (match many p (((Rope) _)) ((PHalf n) (show-half-typed n)) (else (show-plain _ b))))
        (else (show-plain _ b))))
    ((ExtArray) (show-plain _ b))
    ((ExtNat) (show-plain _ b))
    ((ExtString) (show-plain _ b))))

(def-fns _ $ (many types-of : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Term) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (Cons _ (type-of env x) $ notail $ types-of env rest))))

; The many fields' types of a constructor at an instance of its type, as entering its branch reads them.
; One entry per field in declaration order, None where the field is erased: it has no word, so it takes none
; from the destructure and prints `_` (ASSUMPTIONS 184).
(def-fns _ $ (many field-slots : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Maybe $ Term) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest)
      (Cons _ (match many (entry-mult-of env x) (((Maybe $ Term) _))
                ((Erased) (None _))
                (else (Some _ $ type-of env x)))
        $ notail $ field-slots env rest))))

; The fields' types in the environment the unification refined, which a nested field's own printing reads
; them in (lib/elab.ml's show_value passes its env' down).
(def-fns _ $ (many field-types : (many (Env) env) (many (Term) ty) (many (Ctor) c) -> (many (Env) e) (many (List $ Maybe $ Term) tys))
  (let ((many ctele) (many ret)) $ ctor-type env $ ctor-id c)
  (let ((many envb) (many fids) (erased lock)) $ open-tele ctele env (None _) (None _) (None _) (Nil _) $ BFalse)
  (match many (merge-all $ unify-force (Forcing envb) (instantiate (tvars-rev fids $ Nil _) ret) ty) _
    ((UOk e2) (values e2 (field-slots e2 fids)))
    ((UContra _) (values env (Nil _)))))

(def-fns _ $ (many type-adt : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Adt) r))
  (match many (type-head env ty) _
    ((None _) (None _))
    ((Some _ tid)
      (let ((many envf) (many found)) $ find-matchable env tid)
      (match many found _
        ((None _) (None _))
        ((Some _ info) (match many info _ ((MkMatchInfo mid _ _ _) (adt-of env mid))))))))

; The constructor's name over its fields, without the outer parens: show-at hands those to its caller as the
; Bool beside the rope, so a last argument that is an application takes `$` instead of its own pair (DESIGN 2).
(def-fns _ $ (many ctor-body : (many (Ctor) ct) (many (List $ Rope) fields) -> (many (Rope) r))
  (rjoin (Cons _ (RStr $ ctor-name ct) fields) " "))

; The sole non-phantom constructor, where a type has exactly one and so needs no tag (ASSUMPTIONS 184).
(def-fns _ $ (many lone-ctor : (many (Adt) adt) -> (many (Maybe $ Ctor) c))
  (match many (adt-ctors adt) _
    ((Nil _) (None _))
    ((Cons _ c more) (match many more (((Maybe $ Ctor) _)) ((Nil _) (Some _ c)) ((Cons _ _ _) (None _))))))

(def-fns _
  ; The rope is the rendering, and the Bool says it is an application body still missing its parens, which is
  ; what lets a caller write `$` before a last one instead (ASSUMPTIONS 184).
  ((many show-at : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) r) (subterm many (Nat) depth)
      (many (Env) env) (many (Term) ty0) -> (many (Rope) rope) (many (Bool) app))
    (match many depth (((Rope) _) ((Bool) b0))
      ((Zero) (values (RStr "_") (BFalse)))
      ((Succ dd)
        (let ((many ty)) $ canon-env env ty0)
        (match many (term-eq ty slot-term) (((Rope) _) ((Bool) b1))
          ((BTrue) (values (RStr "_") (BFalse)))
          ((BFalse)
            (match many ty (((Rope) _) ((Bool) b2))
              ((TCell _ _) (values (RStr "_") (BFalse)))
              (else
                (let ((erased rs) (many blk) (erased sf)) $ store-read Block hs hp r)
                (match many (lit-rope _ env ty blk) (((Rope) _) ((Bool) b3))
                  ((Some _ text) (values text (BFalse)))
                  ((None _)
                    (match many (type-adt env ty) (((Rope) _) ((Bool) b4))
                      ((None _) (values (RStr "_") (BFalse)))
                      ((Some _ adt)
                        (let ((erased hs2) (many hp2) (erased le) (many read)) $ dispatch _ hp (adt-ext adt) (adt-tagged adt) r)
                        (match many read (((Rope) _) ((Bool) b5))
                          ((Some _ pair)
                            (match many pair (((Rope) _) ((Bool) b6))
                              ((MkPair _ _ index fields)
                                (match many (ctor-at adt index) (((Rope) _) ((Bool) b7))
                                  ((None _) (values (RStr "_") (BFalse)))
                                  ((Some _ ct)
                                    (let ((many e2) (many tys)) (field-types env ty ct))
                                    (values (ctor-body ct $ notail $ show-fields _ hp2 dd tys fields e2) (BTrue)))))))
                          ((None _)
                            (match many (lone-ctor adt) (((Rope) _) ((Bool) b8))
                              ((None _) (values (RStr "_") (BFalse)))
                              ((Some _ ct)
                                (let ((many e2) (many tys)) (field-types env ty ct))
                                (values (ctor-body ct $ notail $ show-fields _ hp dd tys
                                          (ctor-fields _ hp (adt-newtype adt) (ctor-arity ct) r) e2) (BTrue)))))))))))))))))

  ; Walks the declared fields, an erased one taking no word from the destructure; a field that is an application
  ; takes its own parens, or `$` where it is the last (DESIGN 2, ASSUMPTIONS 184).
  ((many show-fields : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (Nat) depth)
      (subterm many (List $ Maybe $ Term) tys) (many (List $ Ref Block hs) fs) (many (Env) env) -> (many (List $ Rope) rs))
    (match many tys _
      ((Nil _) (Nil _))
      ((Cons _ mt rest)
        (let ((many (Rope) shown) (many (List $ Ref Block hs) more))
          (match many mt (((Rope) _) ((List $ Ref Block hs) l))
            ((None _) (values (RStr "_") fs))
            ((Some _ t)
              (match many fs (((Rope) _) ((List $ Ref Block hs) l2))
                ((Nil _) (values (RStr "_") fs))
                ((Cons _ f rst)
                  (let ((many body) (many app))
                    (match many depth (((Rope) _) ((Bool) b3))
                      ((Zero) (values (RStr "_") (BFalse)))
                      ((Succ dd) (notail $ show-at _ hp f dd env t))))
                  (values (match many app (((Rope) _))
                            ((BFalse) body)
                            ((BTrue) (match many rest (((Rope) _))
                                       ((Nil _) (RCat (RStr "$ ") body))
                                       ((Cons _ _ _) (rwrap "(" body ")")))))
                          rst))))))
        (Cons _ shown $ notail $ show-fields _ hp depth rest more env)))))


(def-fns _ $ (many show-typed : (many (Env) env) (many (Term) ty) (many (Nat) x) -> (many (Rope) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store env)
  (match many (idmap-get _ x en) _
    ((Miss _ _ _ _) (RStr "?"))
    ((Hit _ _ _ info _)
      (match many info _
        ((MkEInfo _ _ _ s _ _ _)
          (match many s _
            ((SDyn _) (RStr "?"))
            ((SConst _ v)
              (let ((many body) (many app)) $ show-at _ hp v 100000 env ty)
              (match many app (((Rope) _)) ((BTrue) (rwrap "(" body ")")) ((BFalse) body)))))))))

(def-fns _ $ (many elab-comptime-match : (erased (List $ List $ Nat) ctx) (many (Env) env) (many (List $ Raw) args) -> (many (Env) r) (many (StmtCode ctx ctx) sc))
    (let ((many (Env) env14) (many (Mult) mode) (many (List $ Raw) tail3))
      (match many args _
        ((Nil _) (values (env-error env "`comptime-match` needs `many` or `unique`") (Many) args))
        ((Cons _ mraw rest)
          (let ((many env1) (many m)) (mult-checked env mraw))
          (values (error-unless env1 (mult-is-many m) "`comptime-match` needs `many` or `unique`") m rest))))
    (let ((many shape)) $ comptime-shape tail3)
    (match many shape _
      ((None _) (values (env-error env14 "malformed `comptime-match`: expected `(comptime-match many|unique x (C field ...))`") $ SNone _))
      ((Some _ triple)
        (match many triple _
          ((MkPair _ t xraw cpat)
            (match many cpat _
              ((MkPair _ _ craw fields)
                (let ((many env1)) $ error-unless env14 (env-run-pos env14) "`comptime-match` is a run-position statement (section 15)")
                (let ((many env2) (many x) (many sharing))
                  (match many (share-arg env1 xraw) (((Env) _) ((Nat) i) ((Bool) b))
                    ((None _)
                      (let ((many envb) (many z)) $ var-of-raw env1 xraw "a variable")
                      (values envb z (BFalse)))
                    ((Some _ arg)
                      (let ((many envb) (many y)) $ var-of-raw env1 arg "a variable")
                      (let ((many envc)) $ error-when envb (not $ mult-is-once $ entry-mult-of envb y) "`share` needs a unique value")
                      (let ((many envd)) $ error-when envc (mult-is-once mode) $ str-cat3 "many value " (qname envc y) " used at unique")
                      (values envd y (BTrue)))))
                (let ((many env2d)) (use-entry env2 mode x sharing))
                (let ((many (Env) env3))
                  (match many (and (is-const env2d x) $ mult-is-many $ entry-mult-of env2d x) _
                    ((BTrue) env2d)
                    ((BFalse) (env-error env2d "`comptime-match` needs a Const, non-erased scrutinee"))))
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
                      (match many info (((Env) _))
                        ((MkMatchInfo mid disc mctors _)
                          (let ((many env5a)) $ error-unless env5 (is-some _ $ adt-of env5 mid) $ str-cat3 "the `Matchable` for " (qname env5 tid) " is not Const, so `comptime-match` cannot consult it")
                          (let ((many env5b)) $ use-entry (warn-use env5a (env-loc env5a) "match on" $ TVar tid) (Many) mid (BFalse))
                          (let ((many env6a)) $ match many disc (((Env) _)) ((DUnion) (env-error env5b "`comptime-match` needs a non-erased discriminant")) ((DEnum) env5b))
                          (let ((many env6b) (many mk)) $ marker-checked env6a tid mctors c)
                          (error-unless env6b (mult-is-many mk) $ str-cat3 "`comptime-match`: " (qname env6b c) " is phantom, so no non-erased value is headed by it"))))))
                (let ((many (Env) env7))
                  (match many (ctor-of env6 c) _
                    ((None _) (env-error env6 $ str-cat (qname env6 c) " is not a run-position constructor"))
                    ((Some _ ct)
                      (let ((many env6b) (many mi)) $ env-destruct env6 x ct)
                      (match many mi (((Env) _))
                        ((None _) env6b)
                        ((Some _ i)
                          (match many (nat-cmp i $ ctor-index ct) (((Env) _))
                            ((CEq _ _ _) env6b)
                            (else (env-error env6b $ str-cat3 "`comptime-match`: expected " (qname env6b c) $ str-cat ", got " $ tick $ rope-str $ show-typed env6b (type-of env6b x) x))))))))
                (let ((many extra)) (match many found (((Bool) _)) ((None _) (BFalse)) ((Some _ info) (match many info _ ((MkMatchInfo mid _ cs _) (and (mult-is-many $ marker cs c) $ and (mult-is-once mode) (cells-allowed env7 mid)))))))
                (let ((many env8) (many ordinary) (many cellname)) (pattern-fields env7 c tele fields extra))
                (let ((many mults)) (field-mults (tele-mults tele) mode))
                (let ((many env10) (many fids) (many u)) $ open-fields env8 tele (raw-names ordinary) (raw-sites ordinary env8) (Some _ mults) (res-of env8 x) c ret)
                (match many u _
                  ((UOk env11)
                    (let ((many env12)) (match many (ctor-of env11 c) (((Env) _)) ((None _) env11) ((Some _ ct) (env-set-fields env11 x ct fids mults))))
                    (let ((many env13) (many cell)) (pattern-cell-option env12 mode (res-of env12 x) c fids extra cellname))
                    (values env13 $ SNone _))
                  ((UContra msg) (values (env-error env10 $ str-cat3 "internal: the verified value contradicts the facts in force (" (clash-str env10 msg) ")") $ SNone _))))))))))

; Every function recurses on a raw it elaborates: the first subterm parameter is that raw or list, a later
; one a structure parsed from it (its entries prove they sit inside it) or a Steps budget spent when a
; function hands its whole raw to another.
; ---- Sugar (SUGAR.md 5): unary and distinct stand for calls on the prelude's Numeral lemmas, written
; down as the reference writes them and elaborated where the form is met. The elaborator's group takes a
; budget of such expansions as its first subterm parameter, spent when a generated form is elaborated,
; which is what lets that raw be of the elaborator's own making (ASSUMPTIONS 111).

(let ((many sugar-budget)) 1)

(def-fns _ $ (many gen-atom : (many (String) s) -> (many (Raw) r))
  (RAtom (MkPos 1 1) s))

(def-fns _ $ (many gen-nat : (many (Nat) n) -> (many (Raw) r))
  (gen-atom $ nat-str n))

(def-fns _ $ (many gen-of : (many (String) head) (many (List $ Raw) args) -> (many (Raw) r))
  (RList (MkPos 1 1) $ Cons _ (gen-atom head) args))

(def-fns _ $ (many gen-numeral-of : (many (Nat) n) -> (many (Raw) r))
  (gen-of "numeral-of" $ Cons _ (gen-nat n) $ Nil _))

(def-fns _ $ (many bin-raw : (subterm many (Bin) b) -> (many (Raw) r))
  (gen-of (bin-ctor b) $ match many b (((List $ Raw) _)) ((BZ) (Nil _)) ((B1 x) (Cons _ (notail $ bin-raw x) $ Nil _)) ((B2 x) (Cons _ (notail $ bin-raw x) $ Nil _))))

(def-fns _ $ (many bin-text : (many (Nat) n) -> (many (Raw) r))
  (bin-raw $ bin-of-nat n))

(def-fns _ $ (many bin-succ : (subterm many (Bin) b) -> (many (Bin) c))
  (match many b _ ((BZ) (B1 $ BZ)) ((B1 b1) (B2 b1)) ((B2 b1) (B1 $ notail $ bin-succ b1))))

; The witness that n's spelling steps to (n+1)'s: (B1 x) steps to (B2 x), and (B2 x) to (B1 (succ x)).
(def-fns _ $ (many bin-succ-witness : (subterm many (Bin) b) -> (many (Raw) r))
  (match many b _
    ((BZ) (gen-of "BSZ" $ Nil _))
    ((B1 x) (gen-of "BS1" $ Cons _ (bin-raw x) $ Nil _))
    ((B2 x) (gen-of "BS2" $ Cons _ (bin-raw x) $ Cons _ (bin-raw $ bin-succ x) $ Cons _ (notail $ bin-succ-witness x) $ Nil _))))

(def-fns _ $ (many succs : (subterm many (Nat) k) (many (Raw) base) -> (many (Raw) r))
  (match many k _
    ((Zero) base)
    ((Succ j) (tail $ succs j $ gen-of "Succ" $ Cons _ base $ Nil _))))

(def-fns _ $ (many unary-fold : (subterm many (Nat) k) (many (Nat) z) (many (Nat) lo) (many (Raw) floor) (many (Raw) acc) -> (many (Raw) r))
  (match many k _
    ((Zero) acc)
    ((Succ j)
      (let ((many n)) $ Succ z)
      (let ((many below)) $ succs (nat-sub z lo) floor)
      (let ((many stp)) $ gen-of "numeral-succ" $ Cons _ (bin-text z) $ Cons _ (bin-text n) $ Cons _ (gen-nat z) $ Cons _ (gen-nat n)
                          $ Cons _ (bin-succ-witness $ bin-of-nat z) $ Cons _ (gen-numeral-of z) $ Cons _ (gen-numeral-of n) $ Nil _)
      (let ((many congd)) $ gen-of "eq-cong-succ" $ Cons _ (gen-nat z) $ Cons _ below $ Cons _ acc $ Nil _)
      (let ((many acc2)) $ gen-of "eq-trans" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat n) $ Cons _ (gen-of "Succ" $ Cons _ (gen-nat z) $ Nil _)
                          $ Cons _ (gen-of "Succ" $ Cons _ below $ Nil _) $ Cons _ stp $ Cons _ congd $ Nil _)
      (tail $ unary-fold j n lo floor acc2))))

(def-fns _ $ (many unary-source : (many (Nat) za) (many (Nat) lo) (many (Bool) floored) -> (many (Raw) r))
  (let ((many (Raw) floor) (many (Raw) acc))
    (match many floored _
      ((BFalse) (values (gen-of "Zero" $ Nil _) $ gen-of "numeral-zero" $ Cons _ (gen-nat 0) $ Cons _ (gen-numeral-of 0) $ Nil _))
      ((BTrue) (values (gen-nat lo) $ gen-of "Refl" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat lo) $ Nil _))))
  (gen-of "let-match" $ Cons _ (gen-atom "erased") $ Cons _ (unary-fold (nat-sub za lo) lo lo floor acc)
    $ Cons _ (gen-of "Refl" $ Cons _ (gen-atom "_") $ Cons _ (gen-atom "_") $ Nil _) $ Nil _))

(def-fns _ $ (many distinct-source : (many (Nat) za) (many (Nat) zb) -> (many (Raw) r))
  (gen-of "match" $ Cons _ (gen-atom "erased")
    $ Cons _ (gen-of "numeral-inj" $ Cons _ (bin-text za) $ Cons _ (bin-text zb) $ Cons _ (gen-nat za) $ Cons _ (gen-numeral-of za) $ Cons _ (gen-numeral-of zb) $ Nil _)
    $ Cons _ (RList (MkPos 1 1) $ Cons _ (RList (MkPos 1 1) $ Cons _ (gen-of "False" $ Nil _) $ Cons _ (gen-atom "f") $ Nil _) $ Nil _)
    $ Cons _ (gen-of "absurd" $ Cons _ (gen-atom "Refl") $ Nil _) $ Nil _))


; ---- dump-context (ASSUMPTIONS 196, lib/dump.ml)

(def-adts
  ((Goal : -> Type)
    enum
    (many GoalStatement : -> (Goal))
    (many GoalType : -> (Goal))
    (many GoalValues : (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) -> (Goal)))
  ((Focus : -> Type)
    enum
    (many MkFocus : (many (String) source) (many (Term) t) (many (Term) ty) -> (Focus))))

(def-fns _ $ (many join-strs : (subterm many (List $ String) xs) (many (String) sep) -> (many (String) r))
  (match many xs _
    ((Nil _) "")
    ((Cons _ x rest) (match many rest _ ((Nil _) x) ((Cons _ _ _) (str-cat3 x sep $ notail $ join-strs rest sep))))))

(def-fns _ $ (many cat-strs : (subterm many (List $ String) xs) (many (List $ String) ys) -> (many (List $ String) r))
  (match many xs _ ((Nil _) ys) ((Cons _ x rest) (Cons _ x $ notail $ cat-strs rest ys))))

(def-fns _ $ (many prefix-all : (many (String) p) (subterm many (List $ String) xs) -> (many (List $ String) r))
  (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (str-cat p x) $ notail $ prefix-all p rest))))

(def-fns _ $ (many when-str : (many (Bool) b) (many (String) x) (many (List $ String) rest) -> (many (List $ String) r))
  (match many b _ ((BTrue) (Cons _ x rest)) ((BFalse) rest)))

(def-fns _ $ (many mult-names : (subterm many (List $ Mult) ms) -> (many (List $ String) r))
  (match many ms _ ((Nil _) (Nil _)) ((Cons _ m rest) (Cons _ (mult-name m) $ notail $ mult-names rest))))

(def-fns _ $ (many qnames : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (qname env x) $ notail $ qnames env rest))))

(def-fns _ $ (many bound-here : (many (Env) env) (many (Nat) x) -> (many (Bool) r))
  (and (list-mem-bin (scope-ids $ env-scope env) x) $ not $ is-prelude env x))

(let ((many proof-ids)) (Cons _ predates-id $ Cons _ subterm-id $ Cons _ coercible-id $ Cons _ delegate-id $ Nil _))

(def-fns _ $ (many entry-kind : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (match many (canon-env env $ type-of env x) _
    ((TFn uq _ _ _) (match many uq _ ((BTrue) "unique function") ((BFalse) "function")))
    ((TTyCtor _) "type constructor")
    ((TValCtor _ _) "constructor")
    ((TMatchable _ _ _ _ _) "Matchable")
    ((TCell _ _) "cell")
    ((TApp h _)
      (match many h _
        ((TVar hd)
          (match many (nat-eq hd level-id) _
            ((BTrue) (match many (entry-minted env x) _ ((BTrue) "level minted by `def-lvl`") ((BFalse) "level")))
            ((BFalse)
              (match many (nat-eq hd univ-id) _
                ((BTrue) "type")
                ((BFalse)
                  (match many (nat-eq hd special-id) _
                    ((BTrue) "special form")
                    ((BFalse) (match many (list-mem-bin proof-ids hd) _ ((BTrue) "proof") ((BFalse) "value")))))))))
        (else "value")))
    (else "value")))

(def-fns _ $ (many entry-flags : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (let ((erased hs) (many e)) $ entry env x)
  (match many e _
    ((MkEInfo _ name mult state _ _ site)
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
      (join-strs (Cons _ (mult-name mult) $ Cons _ (match many state (((String) _)) ((SConst _ _) "Const") ((SDyn _) "Dyn")) $ Cons _ (entry-kind env x) rest2) ", "))))

(def-fns _ $ (many unique-status : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (match many (mult-is-once $ entry-mult-of env x) _
    ((BFalse) (Nil _))
    ((BTrue)
      (let ((many (String) status))
        (match many (idmap-get _ x $ env-uses env) _
          ((Miss _ _ _ _) "unique: live, neither consumed nor shared on this path")
          ((Hit _ _ _ u _)
            (match many u _
              ((UseConsumed l) (str-cat3 "unique: consumed at " (loc-str $ Some _ l) ", so usable only erased from here on"))
              ((UseShared l) (str-cat3 "unique: shared at " (loc-str $ Some _ l) $ str-cat3 ", so usable at many, written `(share " (name-of env x) ")`, and never again at unique"))))))
      (Cons _ status $ when-str (list-mem-bin (env-captures env) x) "unique: closed over by the enclosing `def-fns`, so usable here only erased or through `share`" $ Nil _))))

(def-fns _ $ (many entry-value : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (match many (and (is-const env x) $ mult-is-many $ entry-mult-of env x) _
    ((BFalse) (Nil _))
    ((BTrue)
      (let ((many shown)) $ rope-str $ show-typed env (type-of env x) x)
      (match many (str-eq shown "_") _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "= " shown))))))

(def-fns _ $ (many entry-lines : (many (Env) env) (many (Nat) x) -> (many (List $ String) r))
  (let ((many ty) (many rule)) $ fact-at env x)
  (let ((many (List $ String) is-line))
    (match many rule _
      ((None _) (Nil _))
      ((Some _ r0)
        (let ((many r)) $ canon-env env r0)
        (let ((many (Bool) anonymous)) $ match many r _ ((TVar y) (match many (env-entry-name env y) _ ((None _) (BTrue)) ((Some _ _) (BFalse)))) (else (BFalse)))
        (match many anonymous _ ((BTrue) (Nil _)) ((BFalse) (list1 _ $ str-cat "is " $ show-t-except env r $ Some _ x))))))
  (Cons _ (str-cat3 (name-of env x) " : " $ str-cat3 (show-t env $ type-of env x) "  [" $ str-cat (entry-flags env x) "]")
    $ prefix-all "    " $ cat-strs is-line $ cat-strs (entry-value env x) $ unique-status env x))

(def-fns _ $ (many ctor-strs : (many (Env) env) (subterm many (List $ MCtor) cs) -> (many (List $ String) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest)
      (match many c _
        ((MkMCtor _ t)
          (let ((many ty)) $ match many t (((Term) _)) ((TVar cid) (type-of env cid)) (else t))
          (Cons _ (str-cat3 (show-t env t) " : " $ show-t env ty) $ notail $ ctor-strs env rest))))))

(def-fns _ $ (many ctor-lines : (many (Env) env) (many (Term) ty) -> (many (List $ String) r))
  (match many (type-head env ty) _
    ((None _) (Nil _))
    ((Some _ tid)
      (let ((many env2) (many found)) $ find-matchable env tid)
      (match many found _
        ((None _) (Nil _))
        ((Some _ info)
          (match many info _
            ((MkMatchInfo _ _ cs _) (list1 _ $ str-cat3 "constructors of `" (name-of env tid) $ str-cat "`: " $ join-strs (ctor-strs env cs) "; "))))))))

(def-fns _ $ (many ctor-lines-tele : (many (Env) env) (subterm many (List $ Entry) es) -> (many (List $ String) r))
  (match many es _
    ((Nil _) (Nil _))
    ((Cons _ e rest)
      (let ((many more)) $ notail $ ctor-lines-tele env rest)
      (match many (entry-sg e) _
        ((SgIs _ _) more)
        ((SgTy t) (match many (dangling t 0) _ ((BTrue) more) ((BFalse) (cat-strs (ctor-lines env t) more))))))))

(def-fns _ $ (many with-mults : (subterm many (List $ Mult) ms) (many (List $ Entry) es) -> (many (List $ Entry) r))
  (match many ms _
    ((Nil _) es)
    ((Cons _ m mrest)
      (match many es _
        ((Nil _) es)
        ((Cons _ e erest) (match many e _ ((MkEntry n s _ sg pl site) (Cons _ (MkEntry n s m sg pl site) $ notail $ with-mults mrest erest))))))))

(def-fns _ $ (many goal-lines : (many (Env) env) (many (Goal) goal) -> (many (List $ String) r))
  (match many goal _
    ((GoalStatement) (list1 _ "goal: none; `dump-context` stands as a statement here, so nothing is expected of it"))
    ((GoalType) (list1 _ "goal: a type, in an erased position"))
    ((GoalValues expect tele)
      (match many tele _
        ((None _)
          (let ((many n)) $ list-length _ expect)
          (let ((many (String) plural)) $ match many n _ ((Succ p) (match many p _ ((Zero) " value") (else " values"))) ((Zero) " values"))
          (list1 _ $ str-cat3 "goal: " (nat-str n) $ str-cat3 plural " at " $ str-cat (join-strs (mult-names expect) ", ") "; the position fixes no type"))
        ((Some _ es)
          (let ((many (List $ Entry) es2)) $ match many (nat-eq (list-length _ es) $ list-length _ expect) _ ((BTrue) (with-mults expect es)) ((BFalse) es))
          (Cons _ (str-cat "goal:" $ show-tele-t env es2) $ ctor-lines-tele env es2))))))

(def-fns _ $ (many position-lines : (many (Env) env) (many (Goal) goal) -> (many (List $ String) r))
  (let ((many (List $ String) pos))
    (match many goal _
      ((GoalStatement) (Nil _))
      ((GoalType) (list1 _ "position: erased"))
      ((GoalValues expect _) (list1 _ $ str-cat "position: " $ mult-name $ pos-mult expect))))
  (let ((many (String) level))
    (match many (env-level env) _
      ((None _) "level: the top level, above every function's level")
      ((Some _ lvl)
        (str-cat3 "level: " (qname env lvl)
          (match many (env-subterms env) (((String) _))
            ((Nil _) "; the enclosing function has no subterm parameter")
            ((Cons _ _ _) (str-cat "; its subterm arguments, in order: " $ join-strs (qnames env $ env-subterms env) ", ")))))))
  (cat-strs pos
    $ when-str (env-usage-erased env) "erased context: nothing here counts as a use, so no unique binder is consumed or shared by this code"
    $ Cons _ (match many (env-run-pos env) (((String) _)) ((BTrue) "run position: a statement here runs at once and its binders are Const") ((BFalse) "inside a function body or a match branch: binders here are Dyn and calls need their proofs"))
    $ Cons _ level
    $ when-str (env-in-extern env) "inside an extern function's model, so extern types' constructors have cells" $ Nil _))

(def-fns _ $ (many insert-asc : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (list1 _ x))
    ((Cons _ y rest)
      (match many (nat-cmp x y) _
        ((CLt _ _ _ _ _) (Cons _ x xs))
        ((CEq _ _ _) xs)
        (else (Cons _ y $ notail $ insert-asc x rest))))))

(def-fns _ $ (many pairs-ids : (subterm many (List $ Pair (Nat) (Nat)) ps) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (match many ps _
    ((Nil _) acc)
    ((Cons _ p rest) (match many p _ ((MkPair _ _ k v) (tail $ pairs-ids rest $ insert-asc k $ insert-asc v acc))))))

(def-fns _ $ (many class-add : (many (Nat) root) (many (Nat) x) (subterm many (List $ Pair (Nat) $ List $ Nat) cs) -> (many (List $ Pair (Nat) $ List $ Nat) r))
  (match many cs _
    ((Nil _) (list1 _ $ MkPair _ _ root $ list1 _ x))
    ((Cons _ c rest)
      (match many c _
        ((MkPair _ _ r members)
          (match many (nat-cmp root r) _
            ((CLt _ _ _ _ _) (Cons _ (MkPair _ _ root $ list1 _ x) cs))
            ((CEq _ _ _) (Cons _ (MkPair _ _ r $ list-rev _ $ Cons _ x $ list-rev _ members) rest))
            (else (Cons _ c $ notail $ class-add root x rest))))))))

(def-fns _ $ (many at-classes : (many (Env) env) (subterm many (List $ Nat) ids) (many (List $ Pair (Nat) $ List $ Nat) acc) -> (many (List $ Pair (Nat) $ List $ Nat) r))
  (match many ids _
    ((Nil _) acc)
    ((Cons _ x rest) (tail $ at-classes env rest $ class-add (location-root x $ env-locations env) x acc))))

(def-fns _ $ (many lit-spelling : (subterm many (List $ LitEntry) ls) (many (Nat) x) -> (many (Maybe $ String) r))
  (match many ls _
    ((Nil _) (None _))
    ((Cons _ l rest) (match many l _ ((MkLitEntry y _ s) (match many (nat-eq x y) _ ((BTrue) (Some _ s)) ((BFalse) (tail $ lit-spelling rest x))))))))

(def-fns _ $ (many at-member : (many (Env) env) (many (Nat) x) -> (many (Maybe $ String) r))
  (match many (nat-eq x null-id) _
    ((BTrue) (Some _ "(SlotVacant)"))
    ((BFalse)
      (match many (lit-spelling (env-lits env) x) _
        ((Some _ s) (Some _ s))
        ((None _) (match many (bound-here env x) _ ((BTrue) (Some _ $ name-of env x)) ((BFalse) (None _))))))))

(def-fns _ $ (many at-members : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) shown) (many (Bool) bound))
  (match many xs _
    ((Nil _) (values (Nil _) (BFalse)))
    ((Cons _ x rest)
      (let ((many shown) (many bound)) $ notail $ at-members env rest)
      (let ((many bound2)) $ or bound $ bound-here env x)
      (match many (at-member env x) _
        ((None _) (values shown bound2))
        ((Some _ s) (values (Cons _ s shown) bound2))))))

(def-fns _ $ (many at-shown : (many (Env) env) (subterm many (List $ Pair (Nat) $ List $ Nat) cs) -> (many (List $ String) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest)
      (let ((many more)) $ notail $ at-shown env rest)
      (match many c _
        ((MkPair _ _ _ members)
          (let ((many shown) (many bound)) $ at-members env members)
          (match many (and bound $ nat-lt 1 $ list-length _ shown) _
            ((BTrue) (Cons _ (str-cat3 "{" (join-strs shown ", ") "}") more))
            ((BFalse) more)))))))

(def-fns _ $ (many at-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many ids)) $ pairs-ids (idmap-pairs _ (env-locations env) 1 0 $ Nil _) $ Nil _)
  (match many (at-shown env $ at-classes env ids $ Nil _) _
    ((Nil _) (list1 _ "at-database: every entry is at a location of its own"))
    ((Cons _ c cs) (list1 _ $ str-cat "at-database, the entries at one location: " $ join-strs (Cons _ c cs) " "))))

(def-fns _ $ (many opened-split : (many (Env) env) (subterm many (List $ Opened) os) -> (many (List $ String) mine) (many (Nat) prelude))
  (match many os _
    ((Nil _) (values (Nil _) 0))
    ((Cons _ o rest)
      (let ((many mine) (many n)) $ notail $ opened-split env rest)
      (match many (is-prelude env $ opened-x o) _
        ((BTrue) (values mine $ Succ n))
        ((BFalse) (values (Cons _ (show-t env $ type-of env $ opened-x o) mine) n))))))

(def-fns _ $ (many opened-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many mine) (many n)) $ opened-split env $ env-opens env)
  (list1 _ $ str-cat3 "opened, beyond the prelude's " (nat-str n) $ str-cat ": " $ match many mine (((String) _)) ((Nil _) "none") ((Cons _ _ _) (join-strs mine " "))))

(def-fns _ $ (many numeral-rules : (many (Env) env) (subterm many (List $ LitEntry) ls) -> (many (List $ String) r))
  (match many ls _
    ((Nil _) (Nil _))
    ((Cons _ l rest)
      (let ((many more)) $ notail $ numeral-rules env rest)
      (match many l _
        ((MkLitEntry x _ s)
          (match many (all-digits s) _
            ((BFalse) more)
            ((BTrue)
              (let ((many c)) $ canon-env env $ TVar x)
              (match many c _ ((TApp _ _) (Cons _ (str-cat3 s " is " $ show-t env c) more)) (else more)))))))))

(def-fns _ $ (many literal-lines : (many (Env) env) -> (many (List $ String) r))
  (match many (numeral-rules env $ env-lits env) _
    ((Nil _) (Nil _))
    ((Cons _ r rs) (list1 _ $ str-cat "numerals with rules: " $ join-strs (Cons _ r rs) "; "))))

(def-fns _ $ (many not-prelude : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (match many (is-prelude env x) _ ((BTrue) (tail $ not-prelude env rest)) ((BFalse) (Cons _ x $ notail $ not-prelude env rest))))))

(def-fns _ $ (many entries-lines : (many (Env) env) (subterm many (List $ Nat) xs) -> (many (List $ String) r))
  (match many xs _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (cat-strs (prefix-all "  " $ entry-lines env x) $ notail $ entries-lines env rest))))

(def-fns _ $ (many scope-lines : (many (Env) env) -> (many (List $ String) r))
  (let ((many mine)) $ not-prelude env $ scope-ids $ env-scope env)
  (Cons _ (str-cat3 "in scope, newest first (" (nat-str $ list-length _ mine) $ str-cat3 " entries; the prelude's " (nat-str $ list-length _ $ scope-ids $ env-prelude env) " are not listed, and `(dump-context x)` shows any one):")
    $ entries-lines env mine))

(def-fns _ $ (many focus-lines : (many (Env) env) (subterm many (List $ Focus) fs) -> (many (List $ String) r))
  (match many fs _
    ((Nil _) (Nil _))
    ((Cons _ f rest)
      (let ((many more)) $ notail $ focus-lines env rest)
      (match many f _
        ((MkFocus source t ty)
          (let ((many (Maybe $ Nat) variable)) $ match many t _ ((TVar x) (match many (is-meta env x) _ ((BTrue) (None _)) ((BFalse) (Some _ x)))) (else (None _)))
          (match many variable _
            ((Some _ x) (cat-strs (entry-lines env x) more))
            ((None _)
              (let ((many (String) typed)) $ match many ty _ ((TErr _) "") (else (str-cat " : " $ qshow env ty)))
              (Cons _ (str-cat3 (tick source) " canonicalizes to " $ str-cat (qshow env t) typed) more))))))))

(def-fns _ $ (many dump-report : (many (Env) env) (many (Goal) goal) (many (List $ Focus) focus) -> (many (Env) r))
  (let ((many (List $ String) shown)) $ match many focus _ ((Nil _) (scope-lines env)) ((Cons _ _ _) (focus-lines env focus)))
  (let ((many body)) $ cat-strs (goal-lines env goal) $ cat-strs (position-lines env goal) $ cat-strs shown $ cat-strs (at-lines env) $ cat-strs (opened-lines env) $ literal-lines env)
  (env-error env $ join-strs (Cons _ "`dump-context` stops elaboration here and reports what the checker knows" $ prefix-all "  " body) "\n"))

(def-fns _
  ; An expression of the given size and erasures (sections 16, 20); [tele] is the telescope a bare _ reuses.
  ((many elab-expr-demand : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) (many (ExprDemand expect) demand) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Mult) (Res) expect ress) lock))
    (let ((many envl0)) $ env-at env $ raw-pos raw)
    (let ((many envl)) $ env-set-usage-erased envl0 $ or (env-usage-erased env) $ not $ mult-is-many $ pos-mult expect)
    (let ((many pos) (erased pf)) $ pos-of expect)
    (let ((many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
      (match many raw _
        (else
          (let ((many env1) (many x)) $ var-of-raw envl raw "a name")
          (let ((many mode)) (match many demand (((Mult) _)) ((Fixed _) (pos-mult expect)) ((CallableHead) (head-demand env1 (type-of env1 x))) ((FinalDemand) (final-demand env1 (type-of env1 x)))))
          (let ((many env2)) $ use-entry env1 mode x $ BFalse)
          (values env2 (Cons _ (res-of env2 x) $ Nil _) $ coercible-code _ expect (Many) $ var-code env2 ctx x))
        ((RList _ items)
          (match many items (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
            ((Nil _) (expr-error _ expect envl "empty form" "empty form"))
            ((Cons a head args)
              (match many (special-of envl head) (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                ((Some _ sp)
                  (let ((many envl2)) $ read-special envl head (BFalse) pos)
                  (let ((many multi)) $ or (sp-eq sp $ SpExpr $ ExCellMatch) $ or (sp-eq sp $ SpExpr $ ExValues) $ or (sp-eq sp $ SpExpr $ ExMatch) $ or (sp-eq sp $ SpExpr $ ExOpenAbsurd) $ or (sp-eq sp $ SpMark $ MkTail) $ or (sp-eq sp $ SpMark $ MkNoTail) $ or (sp-eq sp $ SpMark $ MkDelegate) $ sp-eq sp $ SpStmt $ StDumpContext)
                  (let ((many (Env) env0))
                    (match many multi _
                      ((BTrue) envl2)
                      ((BFalse)
                        (match many expect (((Env) _))
                          ((Nil _) (env-error envl2 $ str-cat (tick $ sp-name sp) " produces one value"))
                          ((Cons _ _ rest) (match many rest (((Env) _)) ((Nil _) envl2) ((Cons _ _ _) (env-error envl2 $ str-cat (tick $ sp-name sp) " produces one value"))))))))
                  (match many sp (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                    ((SpFormer _)
                      (let ((many env1)) $ error-when env0 (mult-is-many pos) "a type in a non-erased position")
                      (let ((many env2) (many t)) $ notail $ elab-type-form sugar args two-steps env1 sp)
                      (erased-result _ expect env2 $ term-res env2 t type-term))
                    ((SpStmt sk)
                      (match many sk (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                        ((StDumpContext)
                          (let ((many env1) (many focus)) $ notail $ elab-focus sugar args _ two-steps env0)
                          (values (dump-report env1 (GoalValues expect tele) focus) (Nil _) $ CError _ expect "dump-context"))
                        (else (expr-error _ expect env0 (str-cat (tick $ sp-name sp) " is a statement, not an expression") "statement as expression"))))
                    ((SpMark mk)
                      (match many mk (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                        ((MkAt) (notail $ elab-cell-at sugar args env0 ctx expect tele))
                        ((MkTail) (notail $ elab-marked sugar args env0 ctx expect tele (CCTail) sp demand))
                        ((MkNoTail) (notail $ elab-marked sugar args env0 ctx expect tele (CCNoTail) sp demand))
                        ((MkDelegate) (notail $ elab-marked sugar args env0 ctx expect tele (CCDelegate) sp demand)) (else (malformed _ expect env0 sp))))
                    ((SpExpr ex)
                      (match many ex (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                        ((ExSlotVacant)
                          (cell-result _ expect (count-check env0 " arguments" 0 (list-length _ args))
                            (MkRes (TSlotHolds (TVar null-id)) slot-term (pos-mult expect) (None _)) (CValue _ (BToken _))))
                        ((ExSlotHolds)
                          (let ((many env1) (many id)) (slot-direct (count-check env0 " arguments" 1 (list-length _ args)) (one-arg args)))
                          (cell-result _ expect env1 (MkRes (TSlotHolds (TVar id)) slot-term (pos-mult expect) (None _)) (var-code env1 ctx id)))
                        ((ExCellAlloc) (notail $ elab-cell-alloc sugar args env0 ctx expect))
                        ((ExCellWrite) (notail $ elab-cell-write sugar args env0 ctx expect))
                        ((ExCellMatch) (notail $ elab-cell-match sugar args env0 ctx expect tele demand))
                        ((ExShare)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ arg rest)
                              (let ((many env1)) $ error-unless env0 (list-is-empty _ rest) "`share` takes one value")
                              (let ((many env1c)) $ error-when env1 (not $ mult-is-many pos) "`share` in an erased position")
                              (let ((many mode)) $ under pos $ Once)
                              (let ((many env2) (many r) (many physical))
                                (match many arg (((Env) _) ((Res) r) ((Code ctx many-one) c))
                                  ((RAtom _ n)
                                    (let ((many env2) (many x)) $ var (env-at env1c $ raw-pos arg) n)
                                    (let ((many env3)) $ error-when env2 (and (mult-is-many pos) $ not $ mult-is-once $ entry-mult-of env2 x) "`share` needs a unique value")
                                    (let ((many env4)) $ use-entry env3 (under pos $ Many) x $ BTrue)
                                    (values (env-back env1c env4) (res-of env4 x) $ var-code env4 ctx x))
                                  (else
                                    (let ((many env2) (many rs) (many code) (erased lock)) $ notail $ elab-expr-demand sugar arg env1c ctx (Cons _ mode $ Nil _) no-tele (CCPlain) (Fixed _))
                                    (values env2 (first-res _ _ rs lock) $ runtime-one _ mode code))))
                              (cell-result _ expect env2 (MkRes (res-term r) (res-ty r) (under pos $ Many) $ res-place r) physical))))
                        ((ExValues)
                          (match many demand (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((CallableHead) (notail $ elab-values-one sugar args env0 ctx tele (CallableHead)))
                            ((FinalDemand) (notail $ elab-values-one sugar args env0 ctx tele (FinalDemand)))
                            ((Fixed _)
                              (let ((many n)) $ list-length _ expect)
                              (let ((many na)) $ list-length _ args)
                              (let ((many env1)) $ count-check env0 " values" n na)
                              (let ((many env2) (many ress) (many codes) (erased pk)) $ notail $ elab-values sugar args env1 ctx expect tele $ Nil _)
                              (values env2 ress $ CValues _ expect codes pk))))
                        ((ExMatch)
                          (let ((many env2) (many ress) (many code)) $ notail $ elab-match sugar args env0 ctx expect tele demand)
                          (values env2 ress code))
                        ((ExMatchableOf)
                          (let ((many env2) (many tid)) $ named env0 (one-arg args) "a type constructor")
                          (let ((many env3) (many found)) $ find-matchable env2 tid)
                          (match many found (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((None _) (expr-error _ expect env3 (str-cat (qname env3 tid) " has no `Matchable` open") "no Matchable"))
                            ((Some c info) (match many info (((Env) _) ((List $ Res) rs) ((Code ctx expect) c3)) ((MkMatchInfo mid _ _ _) (values (use-entry env3 (under pos $ Many) mid $ BFalse) (Cons _ (res-of env3 mid) $ Nil _) $ single _ expect pos pf $ matchable-code env3 ctx pos mid))))))

                        ((ExNumeralOf) (numeral-of-lit _ expect env0 $ one-arg args))
                        ((ExDistinct) (let ((many env2) (many rs)) $ notail $ elab-distinct sugar args env0 ctx) (values env2 rs $ CErased _ expect))
                        ((ExOpenAbsurd)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons c eraw more)
                              (match many more (((Env) _) ((List $ Res) rs) ((Code ctx expect) c3))
                                ((Nil _) (malformed _ expect env0 sp))
                                ((Cons _ ann more2)
                                  (match many more2 (((Env) _) ((List $ Res) rs) ((Code ctx expect) c3))
                                    ((Cons _ _ _) (malformed _ expect env0 sp))
                                    ((Nil _)
                                      (let ((many env1) (many ress) (many code0) (erased lock)) $ notail $ elab-expr-demand sugar eraw env0 ctx erased-one no-tele (CCPlain) (Fixed _))
                                      (let ((many env2) (many x) (many t)) $ open-bind ctx env0 env1 (first-res _ _ ress lock) (Erased) code0)
                                      (let ((erased on) (erased of) (many obnd) (many otb)) $ env-table env2)
                                      (let ((many kind) (many names)) $ open-names _ _ obnd otb x)
                                      (let ((many (Env) env3))
                                        (match many kind _

                                          ((OKNone) env2)
                                          ((OKMatchable)
                                            (match many (env-open-adt env2 x) (((Env) _))
                                              ((UOk _) (env-error env2 $ str-cat3 "`open-absurd`: opening " (qshow env2 t) " contradicts nothing"))
                                              ((UContra _) env2)))))
                                      (let ((many env4) (many ann-tele) (many result-mults) (many result-bridge)) $ notail $ result-tele sugar ann env3 expect tele demand)
                                      (let ((many env5) (many rids) (erased lock2)) $ open-tele ann-tele env4 (Some _ $ anon-names ann-tele) (None _) (None _) (Nil _) $ BFalse)
                                      (values env5 (ress-of rids env5) $ match many pos (((Code ctx expect) _)) ((Erased) (CErased _ expect)) (else (CAbsurd _ expect))))))))))
                        ((ExLevelOf)
                          (let ((many env2) (many f) (many fty0)) $ notail $ elab-one-term sugar args env0)
                          (let ((many fty)) $ canon-env env2 fty0)
                          (match many fty (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((TFn _ lv _ _) (erased-result _ expect env2 $ MkRes lv level-term (Erased) $ None _)) (else (expr-error _ expect env2 (level-of-error env2 f fty) "level-of"))))
                        ((ExProveSubterm)
                          (let ((many env2) (many a2) (many aty) (many b2) (many bty)) $ notail $ elab-two-terms sugar args env0)
                          (let ((many env3) (many r)) $ mint-subterm env2 a2 aty b2 bty)
                          (erased-result _ expect env3 r))
                        ((ExProvePredates)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (expr-error _ expect env0 "malformed `prove-predates` form" "prove-predates"))
                            ((Cons _ xraw rest)
                              (let ((many env2) (many x)) $ var-of-raw env0 xraw "a variable")
                              (let ((many env3) (many lt) (many ltty)) $ notail $ elab-one-term sugar rest env2)
                              (let ((many env4) (many lvl)) $ level-var-checked env3 lt)
                              (let ((many env5) (many r)) $ mint-predates env4 x lvl)
                              (erased-result _ expect env5 r))))
                        ((ExPredatesTrans)
                          (let ((many env1) (many p) (many q)) $ notail $ two-proofs sugar args env0 ctx)
                          (let ((many env2) (many r)) $ trans-proofs env1 predates-id 3 p q)
                          (erased-result _ expect env2 r))
                        ((ExSubtermTrans)
                          (let ((many env1) (many p) (many q)) $ notail $ two-proofs sugar args env0 ctx)
                          (let ((many env2) (many r)) $ trans-proofs env1 subterm-id 4 p q)
                          (erased-result _ expect env2 r))
                        ((ExCoercibleTrans)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ _ rest)
                              (let ((many env1) (many mid)) $ bind-as env0 (BTrue) (BFalse) (None _) (None _) (BFalse) (Erased) sharing-term (None _) delegate-id)
                              (let ((many first)) $ match many (expected-coercible-sides env1 tele) (((Maybe $ Pair (Term) $ Term) _)) ((None _) (None _)) ((Some _ sides) (match many sides (((Maybe $ Pair (Term) $ Term) _)) ((MkPair _ _ sa _) (Some _ $ MkPair _ _ sa $ TVar mid)))))
                              (let ((many env2) (many p)) $ notail $ elab-coercible-proof sugar args env1 ctx coercible-id first)
                              (let ((many env3) (many sa) (many ta) (many va) (many sm) (many tb) (many vb)) $ expect-proof6 env2 coercible-id p)
                              (let ((many target)) $ match many (expected-coercible-sides env3 tele) (((Term) _)) ((None _) (TVar mid)) ((Some _ sides) (match many sides (((Term) _)) ((MkPair _ _ _ s2) s2))))
                              (let ((many env4) (many q)) $ notail $ elab-coercible-proof sugar rest env3 ctx coercible-id $ Some _ $ MkPair _ _ sm target)
                              (let ((many env5) (many sm2) (many tb2) (many vb2) (many sb) (many tc) (many vc)) $ expect-proof6 env4 coercible-id q)
                              (let ((many env6)) $ check (check (check env5 "sharing" sm sm2) "type" tb tb2) "value" vb vb2)
                              (let ((many env7) (many r)) $ coercible-mint env6 tele $ proof-type coercible-id $ Cons _ sa $ Cons _ ta $ Cons _ va $ Cons _ sb $ Cons _ tc $ Cons _ vc $ Nil _)
                              (erased-result _ expect env7 r))))
                        ((ExPredatesSubterm)
                          (let ((many env1) (many p) (many q)) $ notail $ two-proofs sugar args env0 ctx)
                          (let ((many env2a) (many p0) (many p1) (many p2)) $ expect-proof3 env1 predates-id p)
                          (let ((many env2) (many q0) (many q1) (many q2) (many q3)) $ expect-proof4 env2a subterm-id q)
                          (let ((many env3)) $ check env2 "value" q3 p1)
                          (let ((many env4) (many r)) $ mint env3 $ proof-type predates-id $ Cons _ q0 $ Cons _ q1 $ Cons _ p2 $ Nil _)
                          (erased-result _ expect env4 r))
                        ((ExCoerce)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ araw rest)
                              (let ((many env1) (many p)) $ notail $ elab-coercible-proof sugar rest env0 ctx coercible-id $ None _)
                              (let ((many env2) (many sa) (many ta) (many va) (many sb) (many tb) (many vb)) $ expect-proof6 env1 coercible-id p)
                              (let ((many env3) (many src) (many dst))
                                (match many pos (((Env) _) ((Mult) src) ((Mult) dst))
                                  ((Erased) (values env2 (Erased) $ Erased))
                                  (else
                                    (let ((many env2a) (many src)) $ sharing-mult env2 sa)
                                    (let ((many env2b) (many dst)) $ sharing-mult env2a sb)
                                    (values env2b src dst))))
                              (let ((many env4) (many ars) (many code) (erased lock)) $ notail $ elab-expr-demand sugar araw env3 ctx (Cons _ src $ Nil _) no-tele (CCPlain) (Fixed _))
                              (let ((many ar)) $ first-res _ _ ars lock)
                              (let ((many env5)) $ check (settle-res env4 ar) "value" (res-term ar) va)
                              (let ((many env6) (many x)) $ bind env5 (None _) (None _) (BFalse) dst tb (Some _ vb) delegate-id)
                              (let ((many env7)) $ match many (res-place ar) (((Env) _)) ((None _) env6) ((Some _ place) (at-merge env6 (TVar x) place)))
                              (values env7 (Cons _ (res-with-place (res-of env7 x) $ res-place ar) $ Nil _) $ coercible-code _ expect src code))))
                        ((ExCoercibleRefl)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ _ rest)
                              (let ((many env1) (many s)) $ notail $ elab-sharing-side sugar args env0)
                              (let ((many env2) (many e) (many ty)) $ notail $ elab-one-term sugar rest env1)
                              (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ s $ Cons _ ty $ Cons _ e $ Cons _ s $ Cons _ ty $ Cons _ e $ Nil _)
                              (erased-result _ expect env3 r))))
                        ((ExCoercibleSym)
                          (let ((many sides)) $ match many (expected-coercible-sides env0 tele) (((Maybe $ Pair (Term) $ Term) _)) ((None _) (None _)) ((Some _ p) (match many p (((Maybe $ Pair (Term) $ Term) _)) ((MkPair _ _ sa sb) (Some _ $ MkPair _ _ sb sa)))))
                          (let ((many env1) (many p)) $ notail $ elab-coercible-proof sugar args env0 ctx coercible-id sides)
                          (let ((many env2) (many sa) (many ta) (many va) (many sb) (many tb) (many vb)) $ expect-proof6 env1 coercible-id p)
                          (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ sb $ Cons _ tb $ Cons _ vb $ Cons _ sa $ Cons _ ta $ Cons _ va $ Nil _)
                          (erased-result _ expect env3 r))
                        ((ExCoercibleShare)
                          (let ((many env1) (many p)) $ notail $ elab-coercible-proof sugar args env0 ctx coercible-id $ None _)
                          (let ((many env2) (many sa) (many ta) (many va) (many sb) (many tb) (many vb)) $ expect-proof6 env1 coercible-id p)
                          (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ shared-term $ Cons _ ta $ Cons _ va $ Cons _ shared-term $ Cons _ tb $ Cons _ vb $ Nil _)
                          (erased-result _ expect env3 r))
                        ((ExCoercibleWrap)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ _ rest)
                              (let ((many env1) (many s)) $ notail $ elab-sharing-side sugar args env0)
                              (match many rest (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                                ((Nil _) (malformed _ expect env1 sp))
                                ((Cons _ craw wargs)
                                  (let ((many env2) (many cid)) $ ctor-var env1 craw)
                                  (let ((many ctele) (many ret)) $ ctor-type env2 cid)
                                  (let ((many env3)) $ match many (find-newtype env2 cid) (((Env) _)) ((None _) (env-error env2 $ str-cat (qname env2 cid) " has no opened newtype `Matchable` for its wrapping constructor")) ((Some _ _) env2))
                                  (let ((many env4a) (many acc) (many tys) (many codes) (many prepared)) $ notail $ check-args sugar wargs (subs-all wargs) one-step env3 ctx ctele (Erased) no-tele (ARApp (TVar cid) ret) (BTrue) (BFalse) (BFalse))
                                  (let ((many env4)) $ settle-list acc env4a)
                                  (let ((many env5) (many f) (many fty))
                                    (match many (wrap-field ctele (list-rev _ acc) $ list-rev _ tys) (((Env) _) ((Term) f) ((Term) fty))
                                      ((Some _ pr) (match many pr (((Env) _) ((Term) f) ((Term) fty)) ((MkPair _ _ g gty) (values env4 g gty))))
                                      ((None _) (values (env-error env4 "not the wrapping constructor") (TErr "wrapper") $ TErr "wrapper"))))
                                  (let ((many env6) (many r)) $ coercible-mint env5 tele $ proof-type coercible-id $ Cons _ (wrap-sharing ctele s) $ Cons _ fty $ Cons _ f $ Cons _ s $ Cons _ (instantiate acc ret) $ Cons _ (TApp (TVar cid) $ list-rev _ acc) $ Nil _)
                                  (erased-result _ expect env6 r))))))
                        ((ExCoercibleCtor)
                          (match many args (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil _) (malformed _ expect env0 sp))
                            ((Cons _ _ rest)
                              (let ((many env1) (many s)) $ notail $ elab-sharing-side sugar args env0)
                              (let ((many env2)) $ match many (expected-coercible-sides env1 tele) (((Env) _)) ((None _) env1) ((Some _ p) (match many p (((Env) _)) ((MkPair _ _ sa _) (check env1 "sharing" s sa)))))
                              (match many rest (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                                ((Nil _) (malformed _ expect env2 sp))
                                ((Cons _ craw cargs)
                                  (let ((many env3) (many cid)) $ ctor-var env2 craw)
                                  (let ((many ctele) (many ret)) $ ctor-type env3 cid)
                                  (let ((many env4) (many src) (many tgt)) $ notail $ coercible-ctor-args sugar cargs env3 ctx ctele (Nil _) (Nil _) cid s)
                                  (let ((many env5) (many r)) $ coercible-mint env4 tele $ proof-type coercible-id $ Cons _ s $ Cons _ (instantiate src ret) $ Cons _ (TApp (TVar cid) $ list-rev _ src) $ Cons _ s $ Cons _ (instantiate tgt ret) $ Cons _ (TApp (TVar cid) $ list-rev _ tgt) $ Nil _)
                                  (erased-result _ expect env5 r))))))
                        ((ExCoercibleOf)
                          (let ((many env1) (many p)) $ notail $ elab-coercible-proof sugar args env0 ctx delegate-id $ expected-coercible-sides env0 tele)
                          (let ((many env2) (many sg) (many tg) (many vg) (many sf) (many tf) (many vf)) $ expect-proof6 env1 delegate-id p)
                          (let ((many env3) (many r)) $ coercible-mint env2 tele $ proof-type coercible-id $ Cons _ sg $ Cons _ tg $ Cons _ vg $ Cons _ sf $ Cons _ tf $ Cons _ vf $ Nil _)
                          (erased-result _ expect env3 r))
                        ((ExDelegateOf)
                          (let ((many env2) (many g)) $ named env0 (one-arg args) "a function name")
                          (match many (find-delegate (env-objects env2) env2 g) (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                            ((None _) (expr-error _ expect env2 (str-cat (qname env2 g) " has no `Delegate` proof in scope") "no delegate proof"))
                            ((Some _ x) (erased-result _ expect env2 $ res-of env2 x))))))))
                ((None _)
                  (let ((many env2) (many h) (many hcode))
                    (match many head (((Env) _) ((Res) r) ((Code ctx (Cons (Mult) pos (Nil (Mult)))) c))
                      (else (let ((many env2) (many x)) $ var-of-raw envl head "a name") (values env2 (res-of env2 x) $ coercible-code _ (Cons _ pos $ Nil _) (Many) $ var-code env2 ctx x))
                      ((RList _ _)
                        (let ((many (Env) env2) (many (Res) hr) (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) hc))
                          (match many pos _
                            ((Erased)
                              (let ((many env2) (many rs) (many hc) (erased lock)) (notail $ elab-expr-demand sugar head envl ctx erased-one no-tele (CCPlain) (Fixed _)))
                              (values env2 (first-res _ _ rs lock) hc))
                            (else
                              (let ((many env2) (many rs) (many hc) (erased lock)) (notail $ elab-expr-demand sugar head envl ctx many-one no-tele (CCPlain) (CallableHead)))
                              (values env2 (first-res _ _ rs lock) (coercible-code _ (Cons _ pos (Nil _)) (Many) hc)))))
                        (let ((many env3) (many hr2) (many hid)) (prepare-argument env2 (res-erasure hr) hr))
                        (values env3 hr2 hc))))
                  (match many (canon-env env2 $ res-ty h) (((Env) _) ((List $ Res) rs) ((Code ctx expect) c))
                    ((TCell ctor slots)
                      (let ((many envm) (many rawargs) (many marks)) (cell-marks _ (subs-all args) env2 (BFalse)))
                      (notail $ elab-cell-invoke sugar args rawargs two-steps envm ctx expect tele h (runtime-one _ pos hcode) ctor slots (BFalse) marks))
                    ((TTyCtor ttele)
                      (let ((many env3)) $ error-when env2 (mult-is-many pos) "type constructor application in a non-erased position")
                      (let ((many env4) (many acc) (many tys) (many codes) (many prepared)) $ notail $ check-args sugar args (subs-all args) one-step (check-arity env3 ttele $ list-length _ args) ctx ttele (Erased) tele (ARApp (res-term h) type-term) (BTrue) (BFalse) (BFalse))
                      (erased-result _ expect env4 $ MkRes (TApp (res-term h) $ list-rev _ acc) type-term (Erased) $ None _))
                    ((TValCtor ctele ret)
                      (let ((many mode)) (match many demand (((Mult) _)) ((Fixed _) (pos-mult expect)) ((CallableHead) (head-demand env2 ret)) ((FinalDemand) (final-demand env2 ret))))
                      (def-fns msg-lvl $ (many msg-ctor : -> (many (String) s)) (str-cat3 "erased constructor " (qshow env2 $ res-term h) " in a non-erased position"))
                      (let ((many env2d)) $ error-when-msg env2 (and (mult-is-many pos) $ not $ mult-is-many $ res-erasure h) msg-ctor)
                      (let ((many env2e)) $ match many (mult-is-many mode) (((Env) _)) ((BTrue) (warn-use env2d (loc-in env2d $ raw-pos head) "application of" $ res-term h)) ((BFalse) env2d))
                      (let ((many env3)) $ match many (res-term h) (((Env) _)) ((TVar x) (use-entry env2e (under pos $ Many) x $ BFalse)) (else env2e))
                      (let ((many env3a) (many hr) (many hid)) $ prepare-or-keep _ _ env3 (under pos $ Many) h hcode)
                      (let ((many env4) (many acc) (many tys) (many codes) (many pairs)) $ notail $ check-args sugar args (subs-all args) one-step (check-arity env3a ctele $ list-length _ args) ctx ctele mode tele (ARApp (res-term h) ret) (BFalse) (BFalse) $ BTrue)
                      (let ((many wrapped)) $ match many (canon-env env4 $ res-term h) (((Bool) _)) ((TVar c) (is-some _ $ find-newtype env4 c)) (else (BFalse)))
                      (let ((many place)) $ match many (and wrapped $ mult-is-many mode) (((Maybe $ Term) _))
                        ((BFalse) (None _))
                        ((BTrue) (match many (wrap-field ctele (list-rev _ acc) $ list-rev _ tys) (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ p) (match many p (((Maybe $ Term) _)) ((MkPair _ _ t _) (Some _ t)))))))
                      (let ((many result)) $ MkRes (TApp (res-term h) $ list-rev _ acc) (instantiate acc ret) mode place)
                      (let ((many inputs)) $ Cons _ (MkPair _ _ hid $ runtime-one _ pos hcode) pairs)
                      (let ((many ims) (many iids) (erased ipk) (many ics) (erased icpk)) $ prepare-pack _ $ frame-pairs _ inputs)
                      (let ((many ictx)) $ Cons _ iids ctx)
                      (let ((many actuals)) $ prepared-codes _ pairs env4 ictx)
                      (let ((many code)) $ match many wrapped (((Code ictx many-one) _))
                        ((BFalse) (CApp _ many-one (var-code env4 ictx hid) actuals $ CCCtor))
                        ((BTrue) (match many actuals (((Code ictx many-one) _)) ((Nil _) (CError _ many-one "no newtype field")) ((Cons _ first _) first))))
                      (cell-result _ expect env4 result $ CLet _ ims _ iids ipk (CValues _ ims ics icpk) code))
                    ((TFn uq lv params rets)
                      (let ((many ann) (many args2)) $ split-annotation args _ (WHere args) env2 0)
                      (notail $ elab-call sugar args (MkPair _ _ args2 ann) env2 ctx expect tele h pos hcode uq lv params rets cc))
                    ((TErr m) (expr-error _ expect env2 (not-applicable env2 h) m)) (else (expr-error _ expect env2 (not-applicable env2 h) "not applicable"))))))))))
    (let ((many n)) $ list-length _ expect)
    (let ((many m)) $ list-length _ ress)
    (let ((many ress2) (erased lock)) $ list-fit _ _ expect (metaless-ress ress env2) no-res)
    (match many (nat-cmp n m) _
      (else (values (env-back env $ count-error env2 " values" n m) ress2 code lock))
      ((CEq _ _ _) (values (env-set-usage-erased (env-back env $ match many demand (((Env) _))
        ((Fixed _) (erased-in-many expect ress2 lock env2))
        ((CallableHead) (mode-result-check env2 ress2 $ BFalse))
        ((FinalDemand) (mode-result-check env2 ress2 $ BTrue))) $ env-usage-erased env) ress2 code lock))))
  ; A values of one entry under a head or driver demand: the entry is elaborated under the same demand.
  ((many elab-values-one : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Maybe $ List $ Entry) tele) (many (ExprDemand many-one) demand) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx many-one) code))
    (match many args _
      ((Nil _) (expr-error _ many-one env "a callable head needs one value" "values"))
      ((Cons _ item _)
        (let ((many env1)) (count-check env " values" 1 (list-length _ args)))
        (let ((many env2) (many rs) (many code) (erased lock)) (tail $ elab-expr-demand sugar item env1 ctx many-one tele (CCPlain) demand))
        (values env2 rs code))))
  ((many elab-one-term : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) -> (many (Env) r) (many (Term) t) (many (Term) ty))
    (match many args _
      ((Nil _) (let ((many env2) (many x)) $ missing-arg env) (values env2 (TVar x) $ type-of env2 x))
      ((Cons _ araw _) (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar araw env (BFalse) no-tele) (values (settle env2 t) t ty))))

  ((many elab-one-erased : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (many (Env) r) (many (Res) p))
    (match many args _
      ((Nil _) (let ((many env2) (many x)) $ missing-arg env) (values env2 $ res-of env2 x))
      ((Cons _ araw _)
        (let ((many env2) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar araw env ctx erased-one no-tele (CCPlain) (Fixed _))
        (values (settle env2 $ erased-term ress lock) $ erased-res ress lock))))

  ((many elab-focus : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (erased (Nat) n) (subterm many (Steps n) st) (many (Env) env) -> (many (Env) r) (many (List $ Focus) fs))
    (match many args _
      ((Nil _) (values env $ Nil _))
      ((Cons _ raw rest)
        (let ((many env1) (many t) (many ty)) $ notail $ elab-term sugar raw env (BFalse) no-tele)
        (let ((many env2) (many more)) $ notail $ elab-focus sugar rest _ st env1)
        (values env2 $ Cons _ (MkFocus (show-r raw) t ty) more))))

  ; Grammar expressions (section 5): variables, constructor applications and type formers; [as-type] also
  ; checks the result is a type.
  ((many elab-term : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (Bool) as-type) (many (Maybe $ List $ Entry) tele) -> (many (Env) r) (many (Term) t) (many (Term) ty))
    (let ((many envl)) $ env-at env $ raw-pos raw)
    (let ((many (Env) env2) (many (Term) t) (many (Term) ty))
      (match many raw _
        (else
          (match many (is-underscore raw) (((Env) _) ((Term) t0) ((Term) ty0))
            ((BTrue) (let ((many env2) (many x)) $ bind-as envl (BTrue) (BFalse) (None _) (Some _ $ loc-in env $ raw-pos raw) (BFalse) (Erased) type-term (None _) delegate-id) (values env2 (TVar x) type-term))
            ((BFalse) (let ((many env2) (many x)) $ var-of-raw envl raw "a name") (values env2 (TVar x) $ type-of env2 x))))
        ((RList _ items)
          (match many items (((Env) _) ((Term) t0) ((Term) ty0))
            ((Nil _) (values (env-error envl "empty form") (TErr "empty form") $ TErr "empty form"))
            ((Cons _ head args)
              (match many (special-of envl head) (((Env) _) ((Term) t0) ((Term) ty0))
                ((Some _ sp)
                  (let ((many env2) (many t)) $ notail $ elab-type-form sugar args two-steps envl sp)
                  (values env2 t (match many t (((Term) _)) ((TSlotHolds _) slot-term) (else type-term))))
                ((None _)
                  (let ((many env2) (many x)) $ var-of-raw envl head "a constructor")
                  (let ((many h)) $ TVar x)
                  (let ((many hty)) $ canon-env env2 $ type-of env2 x)
                  (match many hty (((Env) _) ((Term) t0) ((Term) ty0))
                    ((TTyCtor ttele)
                      (let ((many env3) (many acc) (many tys) (many codes) (many prepared)) $ notail $ check-args sugar args (subs-all args) one-step (check-arity env2 ttele $ list-length _ args) (Nil _) ttele (Erased) tele (ARApp h type-term) (BTrue) (BFalse) (BFalse))
                      (values env3 (TApp h $ list-rev _ acc) type-term))
                    ((TValCtor ctele ret)
                      (let ((many env3) (many acc) (many tys) (many codes) (many prepared)) $ notail $ check-args sugar args (subs-all args) one-step (check-arity env2 ctele $ list-length _ args) (Nil _) ctele (Erased) tele (ARApp h ret) (BTrue) (BFalse) (BFalse))
                      (values env3 (TApp h $ list-rev _ acc) $ instantiate acc ret))
                    ((TFn _ _ _ _) (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "function in type") $ TErr "function in type"))
                    ((TErr m) (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr m) $ TErr m)) (else (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "not applicable") $ TErr "not applicable"))))))))))
    (let ((many (Env) env3)) $ match many as-type _ ((BFalse) env2) ((BTrue) (check env2 "type" ty type-term)))
    (values (env-back env env3) t ty))

  ((many elab-type-form : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (subterm many (Steps $ Succ $ Succ $ Zero) st) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (Term) t))
    (let-match many st (SS sn k))
    (match many sp _
      ((SpFormer fo)
        (match many fo _
          ((FoCell)
            (match many args _
              ((Nil _) (values (env-error env "malformed `Cell`") (TErr "malformed `Cell`")))
              ((Cons _ craw rest)
                (let ((many env1) (many c)) (ctor-var env craw))
                (let ((many env2) (many ct) (many params) (many ret) (many cm)) (cell-shape env1 c))
                (let ((many env3) (many slots)) (notail $ elab-slot-terms sugar rest env2))
                (values (count-check env3 " slots" (ctor-arity ct) (list-length _ slots)) (TCell (TVar c) slots)))))
          ((FoFn)
            (match many args _
              ((Nil _) (values (env-error env "malformed `Fn`") $ TErr "malformed `Fn`"))
              ((Cons _ lvraw rest)
                (let ((many env2) (many lv) (many lvty)) $ notail $ elab-term sugar lvraw env (BFalse) no-tele)
                (let ((many env3)) $ check env2 "type" lvty level-term)
                (let ((many ps) (many after) (erased wa)) $ split-arrow rest _ (WHere rest) env3)
                (let ((many env4) (many params) (many rets)) $ notail $ elab-fn-type sugar rest one-step (MkPair _ _ ps $ subs-of after _ wa) env3)
                (values env4 $ TFn (BFalse) lv params rets))))
          ((FoUniqueFn)
            (match many args _
              ((Nil _) (values (env-error env "malformed `Fn`") $ TErr "malformed `Fn`"))
              ((Cons _ lvraw rest)
                (let ((many env2) (many lv) (many lvty)) $ notail $ elab-term sugar lvraw env (BFalse) no-tele)
                (let ((many env3)) $ check env2 "type" lvty level-term)
                (let ((many ps) (many after) (erased wa)) $ split-arrow rest _ (WHere rest) env3)
                (let ((many env4) (many params) (many rets)) $ notail $ elab-fn-type sugar rest one-step (MkPair _ _ ps $ subs-of after _ wa) env3)
                (values env4 $ TFn (BTrue) lv params rets))))
          ((FoTyCtor)
            (let ((many ps) (many after) (erased wa)) $ split-arrow args _ (WHere args) env)
            (tail $ elab-tyctor sugar args k (MkPair _ _ ps $ subs-of after _ wa) env))
          ((FoValCtor)
            (let ((many ps) (many after) (erased wa)) $ split-arrow args _ (WHere args) env)
            (let ((many env2) (many tele) (many ret) (many t)) $ notail $ elab-valctor sugar args k (MkPair _ _ ps $ subs-of after _ wa) env)
            (values env2 t))
          ((FoMatchable)
            (match many args _
              ((Nil _) (values (env-error env "malformed `Matchable`") $ TErr "malformed Matchable"))
              ((Cons _ d rest)
                (let ((many nt) (many ext) (many marked) (erased wm)) $ take-marks rest _ (WHere rest) env (MkNewtypeMark) $ MkExtern)
                (match many marked _
                  ((Nil _) (values (env-error env "malformed `Matchable`") $ TErr "malformed Matchable"))
                  ((Cons _ t cs)
                    (let ((many env2) (many disc)) $ disc-of-checked env d)
                    (let ((many env3) (many tid)) $ named env2 t "a type constructor")
                    (let ((many env4) (many mcs)) $ notail $ elab-mctors sugar (subterm (within-in cs rest (List (Raw)) args (within-step cs marked rest (prove-subterm cs marked) wm) (prove-subterm rest args))) cs env3)
                    (values env4 $ TMatchable disc nt ext (TVar tid) mcs))))))
          ))
      ((SpStmt sk)
        (match many sk (((Env) _) ((Term) t))
          ((StDumpContext)
            (let ((many env1) (many focus)) $ notail $ elab-focus sugar args _ k env)
            (values (dump-report env1 (GoalType) focus) $ TErr "dump-context"))
          (else (values (env-error env $ str-cat (tick $ sp-name sp) " cannot appear in a type") $ TErr "statement in type"))))
      ((SpExpr e)
        (match many e _
          ((ExSlotVacant) (values (count-check env " arguments" 0 (list-length _ args)) (TSlotHolds (TVar null-id))))
          ((ExSlotHolds)
            (let ((many env1) (many id)) (slot-direct (count-check env " arguments" 1 (list-length _ args)) (one-arg args)))
            (values env1 (TSlotHolds (TVar id))))
          (else (values (env-error env (str-cat (tick $ sp-name sp) " cannot appear in a type")) (TErr "expression in type")))))
      ((SpMark _) (values (env-error env $ str-cat (tick $ sp-name sp) " cannot appear in a type") $ TErr "mark in type"))))

  ((many elab-cell-items : (subterm many (Nat) sugar) (subterm many (List $ Raw) items)
      (many (List $ Term) slots) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) pos) ->
      (many (Env) env2) (many (List $ Term) slots2) (many (List $ Maybe $ Nat) ids)
      (many (List $ Pair (Nat) $ Code ctx many-one) pairs))
    (match many items _
      ((Nil _) (values env slots (repeat-field _ (list-length _ slots) (None _)) (Nil _)))
      ((Cons _ item rest)
        (let ((many old) (many tail3)) (match many slots (((Term) _) ((List $ Term) xs))
          ((Nil _) (values (TSlotHolds (TVar null-id)) (Nil _))) ((Cons _ x xs) (values x xs))))
        (match many (is-underscore item) _
          ((BTrue)
            (let ((many env2) (many slots2) (many ids) (many pairs)) (notail $ elab-cell-items sugar rest tail3 env ctx pos))
            (values env2 (Cons _ old slots2) (Cons _ (None _) ids) pairs))
          ((BFalse)
            (let ((many mult)) (under pos (Many)))
            (let ((many env1) (many rs) (many code) (erased lk)) (notail $ elab-expr-demand sugar item env ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
            (let ((many res)) (first-res _ _ rs lk))
            (let ((many env2)) (settle-res (check env1 "type" (res-ty res) slot-term) res))
            (let ((many env3) (many prepared) (many id)) (prepare-argument env2 mult res))
            (let ((many env4) (many slots2) (many ids) (many pairs)) (notail $ elab-cell-items sugar rest tail3 env3 ctx pos))
            (values env4 (Cons _ (res-term res) slots2) (Cons _ (Some _ id) ids)
              (Cons _ (MkPair _ _ id (runtime-one _ mult code)) pairs)))))))

  ((many elab-cell-at : (subterm many (Nat) sugar) (subterm many (List $ Raw) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) ->
      (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
    (match many args _
      ((Nil _) (expr-error _ expect env "`at` wraps a `Cell` invocation" "at"))
      ((Cons _ raw _)
        (let ((many env0)) (count-check env " arguments" 1 (list-length _ args)))
        (match many raw _
          ((RList _ items)
            (match many items _
              ((Nil _) (expr-error _ expect env0 "`at` wraps a `Cell` invocation" "at"))
              ((Cons _ hraw actuals)
                (let ((many env1) (many h) (many hcode))
                  (match many hraw (((Env) _) ((Res) r) ((Code ctx many-one) c))
                    ((RList _ _)
                      (let ((many mult)) (under (pos-mult expect) (Once)))
                      (let ((many env1) (many rs) (many code) (erased lk)) (notail $ elab-expr-demand sugar hraw env0 ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
                      (values env1 (first-res _ _ rs lk) (runtime-one _ mult code)))
                    (else
                      (let ((many env1) (many id)) (var-of-raw env0 hraw "a name"))
                      (values env1 (res-of env1 id) (var-code env1 ctx id)))))
                (match many (canon-env env1 (res-ty h)) _
                  ((TCell c slots)
                    (let ((many envm) (many rawargs) (many marks)) (cell-marks _ (subs-all actuals) env1 (BFalse)))
                    (tail $ elab-cell-invoke sugar actuals rawargs two-steps envm ctx expect tele h hcode c slots (BTrue) marks))
                  (else (expr-error _ expect env1 "`at` wraps a `Cell` invocation" "at"))))))
          (else (expr-error _ expect env0 "`at` wraps a `Cell` invocation" "at"))))))

  ((many elab-cell-alloc : (subterm many (Nat) sugar) (subterm many (List $ Raw) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) ->
      (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
    (match many args _
      ((Nil _) (expr-error _ expect env "malformed `cell-alloc`" "cell-alloc"))
      ((Cons _ raw _)
        (let ((many env0)) (count-check env " arguments" 1 (list-length _ args)))
        (match many raw _
          ((RList _ items)
            (match many items _
              ((Nil _) (expr-error _ expect env0 "malformed `cell-alloc`" "cell-alloc"))
              ((Cons _ craw rest)
                (let ((many env1) (many c)) (ctor-var env0 craw))
                (let ((many env2) (many ct) (many params) (many ret) (many cm)) (cell-shape env1 c))
                (let ((many n)) (ctor-arity ct))
                (let ((many env3)) (count-check env2 " slot items" n (list-length _ rest)))
                (let ((many env4) (many slots) (many ids) (many pairs))
                  (notail $ elab-cell-items sugar rest (repeat-field _ n (TSlotHolds (TVar null-id))) env3 ctx (pos-mult expect)))
                (cell-alloc-result env4 ctx expect c ct slots ids pairs))))
          (else
            (let ((many env1) (many c)) (ctor-var env0 raw))
            (let ((many env2) (many ct) (many params) (many ret) (many cm)) (cell-shape env1 c))
            (let ((many n)) (ctor-arity ct))
            (cell-alloc-result env2 ctx expect c ct (repeat-field _ n (TSlotHolds (TVar null-id)))
              (repeat-field _ n (None _)) (Nil _)))))))

  ((many elab-cell-write : (subterm many (Nat) sugar) (subterm many (List $ Raw) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) ->
      (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
    (match many args _
      ((Nil _) (expr-error _ expect env "malformed `cell-write`" "cell-write"))
      ((Cons _ input rest)
        (match many rest _
          ((Nil _) (expr-error _ expect env "malformed `cell-write`" "cell-write"))
          ((Cons _ spec _)
            (let ((many env0)) (count-check env " arguments" 2 (list-length _ args)))
            (let ((many mult)) (under (pos-mult expect) (Once)))
            (let ((many env1) (many rs) (many inputcode) (erased lk)) (notail $ elab-expr-demand sugar input env0 ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
            (let ((many res)) (first-res _ _ rs lk))
            (let ((many env2) (many prepared) (many sid)) (prepare-argument env1 mult res))
            (let ((many hctx)) (Cons _ (Cons _ sid (Nil _)) ctx))
            (match many spec _
              ((RList _ items)
                (match many items _
                  ((Nil _) (expr-error _ expect env2 "malformed `cell-write`" "cell-write"))
                  ((Cons _ craw items4)
                    (let ((many env3) (many c)) (ctor-var env2 craw))
                    (let ((many env4) (many ct) (many params) (many ret) (many cm)) (cell-shape env3 c))
                    (match many (canon-env env4 (res-ty res)) _
                      ((TCell existing slots)
                        (let ((many env5)) (count-check (check env4 "value" (TVar c) existing) " slot items" (list-length _ slots) (list-length _ items4)))
                        (let ((many env6) (many slots2) (many ids2) (many pairs)) (notail $ elab-cell-items sugar items4 slots env5 hctx (pos-mult expect)))
                        (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (prepare-pack _ pairs))
                        (let ((many bctx)) (Cons _ ids hctx))
                        (let ((many env7) (many x)) (bind env6 (None _) (None _) (BFalse) mult (TCell (TVar c) slots2) (None _) delegate-id))
                        (let ((many env8)) (at-merge env7 (TVar x) (TVar sid)))
                        (cell-result _ expect env8 (res-with-place (res-of env8 x) (res-place prepared))
                          (CLet _ many-one _ (Cons _ sid (Nil _)) (PkMany _ _ _ _ (PkNil _)) (runtime-one _ mult inputcode)
                            (CLet _ ms _ ids ipk (CValues _ ms codes cpk)
                              (CCellWrite _ ct (var-code env8 bctx sid) (cell-slot-writes env8 bctx ids2 0))))))
                      (else (expr-error _ expect env4 "`cell-write` needs a `Cell`" "cell-write"))))))
              (else (expr-error _ expect env2 "malformed `cell-write`" "cell-write"))))))))

  ((many elab-cell-match : (subterm many (Nat) sugar) (subterm many (List $ Raw) args)
      (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) ->
      (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
    (match many args _
      ((Nil _) (expr-error _ expect env "malformed `cell-match`" "cell-match"))
      ((Cons _ mraw rest)
        (match many rest _
          ((Nil _) (expr-error _ expect env "malformed `cell-match`" "cell-match"))
          ((Cons _ input rest2)
            (match many rest2 _
              ((Nil _) (expr-error _ expect env "malformed `cell-match`" "cell-match"))
              ((Cons _ ann rest3)
                (match many rest3 _
                  ((Nil _) (expr-error _ expect env "malformed `cell-match`" "cell-match"))
                  ((Cons _ pattern body)
                    (let ((many pos)) (pos-mult expect))
                    (let ((many env14)) (error-when env (not $ mult-is-many pos) "`cell-match` in an erased position"))
                    (let ((many env0) (many mode)) (mult-checked env14 mraw))
                    (let ((many mult)) (under pos mode))
                    (let ((many env1) (many rs) (many inputcode) (erased lk)) (notail $ elab-expr-demand sugar input env0 ctx (Cons _ mult (Nil _)) no-tele (CCPlain) (Fixed _)))
                    (let ((many res)) (first-res _ _ rs lk))
                    (let ((many env2) (many prepared) (many sid)) (prepare-argument env1 mult res))
                    (let ((many hctx)) (Cons _ (Cons _ sid (Nil _)) ctx))
                    (match many pattern _
                      ((RList _ items)
                        (match many items _
                          ((Nil _) (expr-error _ expect env2 "malformed `cell-match`" "cell-match"))
                          ((Cons _ craw names)
                            (let ((many env3) (many c)) (ctor-var env2 craw))
                            (let ((many env4) (many ct) (many params) (many ret) (many cm)) (cell-shape env3 c))
                            (match many (canon-env env4 (res-ty res)) _
                              ((TCell existing slots)
                                (let ((many n)) (ctor-arity ct))
                                (let ((many needed)) (match many (mult-is-once mode) (((Nat) _)) ((BTrue) (Succ n)) ((BFalse) n)))
                                (let ((many env5)) (count-check (check env4 "value" (TVar c) existing) " binders for `cell-match`" needed (list-length _ names)))
                                (let ((many outer-expect)) expect)
                                (let ((many env6) (many anntele) (many inner-expect) (many bridge)) (notail $ result-tele sugar ann env5 expect tele demand))
                                (let ((many expect2)) inner-expect)
                                (let ((many env7) (many pairs) (many restnames)) (cell-read-bindings env6 hctx sid ct n names slots pos 0))
                                (let ((many env8) (many pairs2))
                                  (match many (mult-is-once mode) (((Env) _) ((List $ Pair (Nat) $ Code hctx many-one) ps))
                                    ((BFalse) (values env7 pairs))
                                    ((BTrue)
                                      (let ((many name)) (match many restnames (((Maybe $ String) _))
                                        ((Nil _) (None _)) ((Cons _ raw _) (name-or-anon (raw-name raw)))))
                                      (let ((many envb) (many back)) (bind env7 name (None _) (BFalse) (under pos (Once)) (res-ty res) (Some _ (res-term res)) delegate-id))
                                      (let ((many envb2)) (at-merge (mark-word envb back (BFalse)) (TVar back) (TVar sid)))
                                      (let ((many pairs2) (erased appended)) (list-append _ pairs (Cons _ (MkPair _ _ back (var-code envb2 hctx sid)) (Nil _))))
                                      (values envb2 pairs2))))
                                (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (prepare-pack _ pairs2))
                                (let ((many bctx)) (Cons _ ids hctx))
                                (let ((many env9) (many ress) (many bcode) (erased lock))
                                  (notail $ elab-body sugar body body (WHere _) (env-set-run-pos env8 (BFalse)) bctx expect2 (Some _ anntele)))
                                (let ((many env10)) (check-results-count env9 body anntele ress (Nil _)))
                                (let ((many env11) (many resultids) (erased rl))
                                  (open-tele anntele (env-discard env6 env10) (Some _ (anon-names anntele)) (None _) (None _) (Nil _) (BFalse)))
                                (values env11 (ress-of resultids env11)
                                  (bridge-code _ outer-expect expect2 bridge (match many (mult-is-many pos) (((Code ctx expect2) _))
                                    ((BFalse) (CErased _ expect2))
                                    ((BTrue)
                                      (CLet _ many-one _ (Cons _ sid (Nil _)) (PkMany _ _ _ _ (PkNil _)) (runtime-one _ mult inputcode)
                                        (CLet _ ms _ ids ipk (CValues _ ms codes cpk) bcode)))))))
                              (else (expr-error _ expect env4 "`cell-match` needs a `Cell`" "cell-match"))))))
                      (else (expr-error _ expect env2 "malformed `cell-match`" "cell-match"))))))))))))

  ((many elab-cell-invoke : (subterm many (Nat) sugar) (subterm many (List $ Raw) args)
      (subterm many (List $ Sub args) rawargs) (subterm many (Steps $ Succ $ Succ $ Zero) st) (many (Env) env) (many (List $ List $ Nat) ctx)
      (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (Res) head)
      (many (Code ctx many-one) hcode) (many (Term) ctor) (many (List $ Term) slots) (many (Bool) full) (many (List $ Bool) marks) ->
      (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code))
    (let-match many st (SS sn step))
    (let ((many pos)) (pos-mult expect))
    (let ((many mult)) (under pos (Once)))
    (let ((many env0)) (match many (res-term head) (((Env) _))
      ((TVar x) (use-entry env mult x (BFalse))) (else env)))
    (let ((many env1)) (error-when env0 (and (mult-is-many pos) (not (mult-is-once (res-erasure head)))) "`Cell` invocation needs a unique cell"))
    (match many (canon-env env1 ctor) _
      ((TVar c)
        (let ((many env2) (many ct) (many params) (many ret) (many cm)) (cell-shape env1 c))
        (let ((many env3)) (error-when env2 (and (mult-is-many pos) (not (mult-is-many cm))) "phantom constructor cannot be invoked through a `Cell` at runtime"))
        (let ((many env4) (many hres) (many sid)) (prepare-argument env3 mult head))
        (let ((many hctx)) (Cons _ (Cons _ sid (Nil _)) ctx))
        (let ((many env6) (many acc) (many tys) (many codes0) (many pairs))
          (notail $ check-args sugar args rawargs (subterm (prove-subterm step st)) step env4 hctx params pos tele (ARApp (TVar c) ret) (BFalse) (BFalse) (BTrue)))
        (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) (prepare-pack _ pairs))
        (let ((many bctx)) (Cons _ ids hctx))
        (let ((many env7) (many writes)) (cell-invoke-writes env6 bctx full params (list-rev _ acc) marks slots 0))
        (cell-result _ expect env7 (MkRes (TApp (TVar c) (list-rev _ acc)) (instantiate acc ret) pos (res-place hres))
          (CLet _ many-one _ (Cons _ sid (Nil _)) (PkMany _ _ _ _ (PkNil _)) hcode
            (CLet _ ms _ ids ipk (CValues _ ms codes cpk)
              (match many writes (((Code bctx many-one) _))
                ((Nil _) (var-code env7 bctx sid))
                ((Cons _ _ _) (CCellWrite _ ct (var-code env7 bctx sid) writes)))))))
      (else (expr-error _ expect env1 "`Cell` constructor is not a variable" "cell invocation"))))

  ((many elab-slot-terms : (subterm many (Nat) sugar) (subterm many (List $ Raw) items) (many (Env) env) ->
      (many (Env) env2) (many (List $ Term) slots))
    (match many items _
      ((Nil _) (values env (Nil _)))
      ((Cons _ item rest)
        (let ((many env1) (many term) (many ty)) (notail $ elab-term sugar item env (BFalse) no-tele))
        (let ((many env2) (many slots)) (notail $ elab-slot-terms sugar rest (check env1 "type" ty slot-term)))
        (values env2 (Cons _ term slots)))))

  ((many elab-mctors : (subterm many (Nat) sugar) (subterm many (List $ Raw) cs) (many (Env) env) -> (many (Env) r) (many (List $ MCtor) mcs))
    (match many cs _
      ((Nil _) (values env $ Nil _))
      ((Cons _ c rest)
        (let ((many bad)) $ env-error env "expected (multiplicity Constructor)")
        (let ((many (Env) env1) (many (Mult) m) (many (Raw) craw))
          (match many (raw-items c) _
            ((Nil _) (values bad (Many) c))
            ((Cons _ mraw more)
              (match many more (((Env) _) ((Mult) m0) ((Raw) r0))
                ((Nil _) (values bad (Many) c))
                ((Cons _ cr more2)
                  (match many more2 (((Env) _) ((Mult) m0) ((Raw) r0))
                    ((Cons _ _ _) (values bad (Many) cr))
                    ((Nil _)
                      (match many (mult-of env mraw) (((Env) _) ((Mult) m0) ((Raw) r0))
                        ((None _) (values (env-error env $ str-cat "expected a multiplicity, got " $ qraw mraw) (Many) cr))
                        ((Some _ mm) (values env mm cr))))))))))
        (let ((many env2) (many cid)) $ ctor-var env1 craw)
        (let ((many env3) (many mcs)) $ notail $ elab-mctors sugar rest env2)
        (values env3 $ Cons _ (MkMCtor m $ TVar cid) mcs))))

  ; The signature pieces [piece] were read from [root]; [st] pays for the parse of each telescope.
  ((many elab-fn-type : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (List $ Entry) params) (many (List $ Entry) rets))
    (match many piece _
      ((MkPair _ _ ps rs)
        (let ((many env2) (many ids) (many params)) $ notail $ elab-tele sugar root st ps env (MMDeclared) (Nil _) (BTrue) (BFalse) $ BFalse)
        (let ((many env3) (many ids2) (many rets)) $ notail $ elab-tele sugar root st rs env2 (MMDeclared) (tvars-rev ids $ Nil _) (BFalse) (BFalse) $ BTrue)
        (values (env-discard env env3) params rets))))

  ((many elab-tyctor : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (Term) t))
    (match many piece _
      ((MkPair _ _ ps ret)
        (let ((many env2) (many ids) (many tele)) $ notail $ elab-tele sugar root st ps env (MMErased) (Nil _) (BFalse) (BFalse) $ BFalse)
        (let ((many (Env) env3))
          (match many ret _
            ((Cons _ s more)
              (match many more (((Env) _))
                ((Nil _) (match many s (((Env) _)) ((MkSub _ r p) (let ((many env3) (many t) (many ty)) $ notail $ elab-term sugar (subterm p) r env2 (BFalse) no-tele) (check env3 "value" t type-term))))
                ((Cons _ _ _) (env-error env2 "`TyCtor` returns `Type`"))))
            ((Nil _) (env-error env2 "`TyCtor` returns `Type`"))))
        (values (env-discard env env3) $ TTyCtor tele))))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type; the return is an application of a type constructor in scope (ASSUMPTIONS 70, 80).
  ((many elab-valctor : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (List $ Entry) tele) (many (Term) ret) (many (Term) t))
    (match many piece _
      ((MkPair _ _ ps rets)
        (let ((many env2) (many ids) (many tele)) $ notail $ elab-tele sugar root st ps env (MMDeclared) (Nil _) (BFalse) (BFalse) $ BFalse)
        (let ((many (Env) env3a) (many (Term) ret))
          (match many rets _
            ((Nil _) (values (env-error env2 "a constructor returns one type") $ TErr "no return"))
            ((Cons _ s more)
              (match many more (((Env) _) ((Term) t0))
                ((Nil _) (match many s (((Env) _) ((Term) t0)) ((MkSub _ r p) (let ((many env3) (many t) (many ty)) $ notail $ elab-term sugar (subterm p) r env2 (BTrue) no-tele) (values env3 t))))
                ((Cons _ _ _) (values (env-error env2 "a constructor returns one type") $ TErr "no return"))))))
        (let ((many env3)) $ settle env3a ret)
        (let ((many (Bool) ok))
          (match many (canon-env env3 ret) _
            ((TApp h _)
              (match many h (((Bool) _))
                ((TVar t) (and (not $ list-mem-bin ids t)
                             $ match many (type-of env3 t) (((Bool) _)) ((TTyCtor _) (BTrue)) (else (BFalse)))) (else (BFalse)))) (else (BFalse))))
        (def-fns msg-lvl $ (many msg-return : -> (many (String) s)) (str-cat "a constructor returns an application of a type constructor in scope, not " $ qshow env3 ret))
        (let ((many env4)) $ error-unless-msg env3 ok msg-return)
        (values (env-set-signature env4 $ env-signature env) tele ret $ TValCtor tele $ abstract (list-rev _ ids) ret))))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 30).
  ; [ids]: binders already in force, innermost first.
  ((many elab-tele : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (List $ Sub root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (Bool) subterm-ok) (many (Bool) holes) (many (Bool) places) -> (many (Env) r) (many (List $ Nat) bound) (many (List $ Entry) tele))
    (let-match many st (SS sn k))
    (let ((many env2) (many entries2)) $ parse-entries-checked _ entries env)
    (tail $ elab-src-entries sugar root k entries2 env2 mode ids (Nil _) subterm-ok holes places))

  ((many elab-src-entries : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Zero) st) (subterm many (List $ SrcEntry root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (List $ Nat) bound) (many (Bool) subterm-ok) (many (Bool) holes) (many (Bool) places) -> (many (Env) r) (many (List $ Nat) bound2) (many (List $ Entry) tele))
    (match many entries _
      ((Nil _) (values env (list-rev _ bound) $ Nil _))
      ((Cons _ e rest)
        (match many e _
          ((MkSrcEntry _ sub2 smult ssg name place epos)
            (let ((many env0)) $ error-when env (and sub2 $ not subterm-ok) "`subterm` is not allowed here")
            (let ((many (Env) env1) (many (Mult) mult) (many (MultsMode) mode2))
              (match many mode _
                ((MMDeclared) (match many smult (((Env) _) ((Mult) m0) ((MultsMode) md0)) ((None _) (values (env-error env0 $ str-cat3 "entry " (tick name) " needs a multiplicity") (Many) mode)) ((Some _ m) (values env0 m mode))))
                ((MMErased) (match many smult (((Env) _) ((Mult) m0) ((MultsMode) md0)) ((None _) (values env0 (Erased) mode)) ((Some _ _) (values (env-error env0 "these entries carry no multiplicity") (Erased) mode))))
                ((MMExpect ms)
                  (let ((many env0b)) $ match many smult (((Env) _)) ((None _) env0) ((Some _ _) (env-error env0 "a match annotation carries no multiplicities")))
                  (match many ms (((Env) _) ((Mult) m0) ((MultsMode) md0)) ((Nil _) (values env0b (Erased) mode)) ((Cons _ m more) (values env0b m $ MMExpect more))))))
            (let ((many (Env) env2) (many (Sg) sg))
              (match many ssg _
                ((None _) (values (env-error env1 $ str-cat3 "entry " (tick name) " needs a type or an `is` clause") $ SgTy $ TErr "no type"))
                ((Some _ s)
                  (match many s (((Env) _) ((Sg) s0))
                    ((SrcTy _ r p) (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar (subterm p) r env1 (BTrue) no-tele) (values env2 $ SgTy t))
                    ((SrcIs _ r p) (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar (subterm p) r env1 (BFalse) no-tele) (values env2 $ SgIs t ty))))))
            (let ((many ty) (many rule)) $ fact-of env2 sg)
            (let ((many nm)) $ name-or-anon name)
            (let ((many env2a) (many atplace))
              (match many place (((Env) _) ((Maybe $ Term) p0))
                ((None _) (values env2 $ None _))
                ((Some _ target)
                  (let ((many envp) (many p)) $ var env2 target)
                  (let ((many envq)) $ error-unless envp places "`at` is allowed only on returns and match annotations")
                  (let ((many envr)) $ error-unless envq (and (or (mult-is-many mult) $ match many mode (((Bool) _)) ((MMExpect _) (BTrue)) (else (BFalse))) $ and (mult-is-many $ entry-mult-of envq p) $ not $ list-mem-bin bound p) "`at` needs a non-erased argument or closed-over variable")
                  (values envr $ Some _ $ TSlotHolds $ TVar p))))
            (let ((many env3) (many x)) $ bind-as env2a (BFalse) holes nm (Some _ $ loc-in env2a epos) (BTrue) mult ty rule delegate-id)
            (let ((many env3e)) (env-set-signature env3 (Cons _ x (env-signature env3))))
            (let ((many ap)) $ match many atplace (((Maybe $ Term) _)) ((None _) (None _)) ((Some _ p) (Some _ $ abstract (bin-ids-of ids) p)))
            (let ((many entry3)) $ MkEntry nm sub2 mult (abstract-sg (bin-ids-of ids) sg) ap (Some _ $ loc-in env2a epos))
            (let ((many env4) (many bound2) (many tele)) $ notail $ elab-src-entries sugar root st rest env3e mode2 (Cons _ (TVar x) ids) (Cons _ x bound) subterm-ok holes places)
            (values env4 bound2 $ Cons _ entry3 tele))))))
  ; A body: statements then the final expression (section 16); [items] sits within [root].
  ((many elab-body : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Raw) items) (erased (Within items root) w) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Mult) (Res) expect ress) lock))
    (match many items _
      ((Nil _)
        (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res)
        (values (env-error env "a body needs a final expression") ress (CError _ expect "empty body") lock))
      ((Cons _ item rest)
        (let ((erased pi)) $ in-within _ _ _ _ (prove-subterm item items) w)
        (match many rest _
          ((Nil _) (tail $ elab-expr-demand sugar (subterm pi) item env ctx expect tele (CCPlain) (Fixed _)))
          ((Cons _ _ _)
            (let ((many env2) (many ctx2) (many sc)) $ notail $ elab-stmt sugar (subterm pi) item env ctx (pos-mult expect))
            (let ((many env3) (many ctx3) (many sc2) (many final)) $ notail $ elab-stmts sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2 (pos-mult expect))
            (match many final _
              ((FinalNone _)
                (let ((many ress) (erased lock)) $ list-fit _ _ expect (Nil _) no-res)
                (values (env-error env3 "a body needs a final expression") ress (CError _ expect "empty body") lock))
              ((FinalIs _ fin pf)
                (let ((many env4) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar (subterm pf) fin env3 ctx3 expect tele (CCPlain) (Fixed _))
                (values env4 ress (wrap-stmt _ _ expect (SSeq _ _ _ sc sc2) code) lock))))))))

  ; The statements before a body's final expression and the code they wrap around what follows them
  ; (lib/elab.ml's elab_stmts), then the final expression with its place in [root].
  ((many elab-stmts : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Raw) items) (erased (Within items root) w) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) spos) ->
      (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc) (many (Final root) final))
    (match many items _
      ((Nil _) (values env ctx (SNone _) $ FinalNone _))
      ((Cons _ item rest)
        (let ((erased pi)) $ in-within _ _ _ _ (prove-subterm item items) w)
        (match many rest _
          ((Nil _) (values env ctx (SNone _) $ FinalIs _ item pi))
          ((Cons _ _ _)
            (let ((many env2) (many ctx2) (many sc)) $ notail $ elab-stmt sugar (subterm pi) item env ctx spos)
            (let ((many env3) (many ctx3) (many sc2) (many final)) $ notail $ elab-stmts sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2 spos)
            (values env3 ctx3 (SSeq _ _ _ sc sc2) final))))))

  ((many elab-stmt : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) spos) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many envl)) $ env-at env $ raw-pos raw)
    (let ((many bad)) $ env-error envl $ str-cat (qraw raw) " is not a statement")
    (let ((many (Env) env2) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
      (match many raw _
        ((RList _ items)
          (match many items (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
            ((Nil _) (values bad ctx $ SNone _))
            ((Cons _ head args)
              (match many (special-of envl head) (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                ((None _) (values bad ctx $ SNone _))
                ((Some _ sp)
                  (let ((many envl2)) $ read-special envl head (BFalse) spos)
                  (match many sp (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                    ((SpStmt st)
                      (match many st (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                        ((StLet)
                          (let ((many envb) (many braws) (many rhs) (erased wr)) $ bracket-parts args envl2 "malformed `let`: expected `(let (<binder> ...) <value> ...)`")
                          (let ((many env0) (many binders)) $ parse-entries-checked _ braws envb)
                          (let ((many env0b) (many tele))
                            (match many (all-have-sg _ binders) (((Env) _) ((Maybe $ List $ Entry) t))
                              ((BFalse) (values env0 no-tele))
                              ((BTrue)
                                (let ((many env1) (many bound) (many t)) $ notail $ elab-src-entries sugar args (SZ) binders env0 (MMDeclared) (Nil _) (Nil _) (BFalse) (BTrue) $ BFalse)
                                (values (env-restore env0 env1) $ Some _ t))))
                          (notail $ elab-let sugar args (MkLetParts _ binders rhs wr) env0b ctx tele spos))
                        ((StDefLvl)
                          (match many args (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                            ((Nil _) (values (env-error envl2 "`def-lvl` needs a name") ctx $ SNone _))
                            ((Cons _ n _)
                              (let ((many env2) (many x)) $ mint-level envl2 (name-or-anon $ raw-name n) (Some _ $ loc-in envl2 $ raw-pos n))
                              (values env2 ctx $ SNone _))))
                        ((StDefFns) (notail $ elab-def-fns sugar args envl2 ctx $ BFalse))
                        ((StDefUnique) (notail $ elab-def-fns sugar args envl2 ctx $ BTrue))
                        ((StDefAdts)
                          (let ((many env3) (many headers) (many tids)) $ notail $ elab-adt-headers sugar args envl2)
                          (let ((many env4) (many consts)) $ notail $ define-adts sugar args headers env3 tids)
                          (match many (env-run-pos env4) (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                            ((BTrue) (values (set-const-states consts env4) ctx $ SNone _))
                            ((BFalse)
                              (let ((many ms) (many ids) (erased ipk) (many codes) (erased cpk)) $ consts-codes ctx consts)
                              (values env4 (Cons _ ids ctx) $ SLet _ ms ids ipk $ CValues _ ms codes cpk))))
                        ((StComptimeMatch) (let ((many env2) (many sc)) $ elab-comptime-match ctx envl2 args) (values env2 ctx sc))
                        ((StLetMatch) (notail $ elab-let-match sugar args envl2 ctx spos))
                        ((StUnary) (notail $ elab-unary sugar args envl2 ctx spos))
                        ((StOpenAdt) (notail $ elab-open-adt sugar args envl2 ctx))
                        ((StDumpContext)
                          (let ((many env1) (many focus)) $ notail $ elab-focus sugar args _ two-steps envl2)
                          (values (dump-report env1 (GoalStatement) focus) ctx $ SNone _)))) (else (values bad ctx $ SNone _)))))))) (else (values bad ctx $ SNone _))))
    (values (env-back env env2) ctx2 sc))

  ; open-adt (section 19, ASSUMPTIONS 139): an anonymous let at the written multiplicity, then the open of that
  ; binder; the entry is bound by the code where the let would be.
  ((many elab-open-adt : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many bad)) $ env-error env "malformed `open-adt`: expected `(open-adt <multiplicity> e)`")
    (match many args _
      ((Nil _) (values bad ctx $ SNone _))
      ((Cons _ mraw rest)
        (match many rest _
          ((Nil _) (values bad ctx $ SNone _))
          ((Cons _ eraw rest2)
            (match many rest2 _
              ((Cons _ _ _) (values bad ctx $ SNone _))
              ((Nil _)
                (let ((many env0) (many mult)) $ mult-checked env mraw)
                (let ((many env1) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar eraw env0 ctx (Cons _ mult $ Nil _) no-tele (CCPlain) (Fixed _))
                (let ((many env2) (many x) (many t)) $ open-bind ctx env0 env1 (first-res _ _ ress lock) mult code)
                (match many (env-open-adt env2 x) _
                  ((UContra m) (values (env-error env2 $ str-cat3 "`open-adt`: " (qshow env2 t) $ str-cat3 " contradicts what is open (" (clash-str env2 m) ")") ctx $ SNone _))
                  ((UOk env3)
                    (match many mult _
                      ((Erased) (values env3 ctx $ SNone _))
                      (else
                        (match many (env-run-pos env0) _
                          ((BTrue) (values env3 ctx $ SNone _))
                          ((BFalse) (values env3 (Cons _ (Cons _ x $ Nil _) ctx) $ SLet _ (Cons _ (Many) $ Nil _) (Cons _ x $ Nil _) (PkMany _ (Nil _) x (Nil _) $ PkNil _) $ runtime-one _ mult code))))))))))))))

  ; let-match (section 16, ASSUMPTIONS 99-100): the sole unrefuted constructor binds outward, its fields at the
  ; scrutinee's own erasure; erased or run at once it leaves no code, else one branch wraps the rest.
  ((many elab-let-match : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) spos) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many bad)) $ env-error env "malformed `let-match`: expected `(let-match <multiplicity> x (C field ...))`")
    (match many args _
      ((Nil _) (values bad ctx $ SNone _))
      ((Cons _ mraw more)
        (match many more _
          ((Nil _) (values bad ctx $ SNone _))
          ((Cons _ scrut more2)
            (match many more2 _
              ((Nil _) (values bad ctx $ SNone _))
              ((Cons c pat more3)
                (match many more3 _
                  ((Cons _ _ _) (values bad ctx $ SNone _))
                  ((Nil _)
                    (match many (raw-items pat) _
                      ((Nil _) (values bad ctx $ SNone _))
                      ((Cons _ craw fields)
                        (let ((many env0) (many smult)) $ mult-checked env mraw)
                        (let ((many env0d)) $ written env0 spos smult "let-match")
                        (let ((many env1a) (many srs) (many scode) (erased lock)) $ notail $ elab-expr-demand sugar scrut env0d ctx (Cons _ smult $ Nil _) no-tele (CCPlain) (Fixed _))
                        (let ((many original)) $ first-res _ _ srs lock)
                        (let ((many source-code)) (runtime-one _ smult scode))
                        (let ((many env1a2) (many sres) (many saved)) (prepare-argument env1a smult original))
                        (let ((many env2) (many found)) $ scrutinee-matchable env1a2 smult sres)
                        (match many found _
                          ((None _) (values env2 ctx $ SNone _))
                          ((Some _ pr)
                            (match many pr _
                              ((MkPair _ _ tid info)
                                (match many info _
                                  ((MkMatchInfo mid disc mctors _)
                                    (let ((many (Env) env2h))
                                      (match many (mult-is-many smult) _
                                        ((BTrue) (use-entry (held-needs-many env2 tid mid) (Many) mid (BFalse)))
                                        ((BFalse) env2)))
                                    (let ((many env4) (many c3)) $ ctor-var env2h craw)
                                    (let ((many env5) (many mk)) $ marker-checked env4 tid mctors c3)
                                    (let ((many env6)) $ error-unless env5 (or (not $ mult-is-many smult) $ mult-is-many mk) $ str-cat (qname env5 c3) " is phantom")
                                    ; covered-of tests each alternative in an independent branch environment;
                                    ; phantom alternatives count too, even when they cannot run.
                                    (let ((many env6a) (many other) (many reachable) (many covered))
                                      $ covered-of mctors env6 (Cons _ c3 $ Nil _) sres smult (None _) (BFalse) $ Nil _)
                                    (let ((many (Env) env6b))
                                      (match many other _
                                        ((None _) env6a)
                                        ((Some _ alternative)
                                          (forced-error mctors env6a sres smult (Cons _ alternative $ Nil _) $ env-error env6a $ str-cat3 "constructor " (qname env6a alternative)
                                            $ str-cat3 " is not refuted, so " (qname env6a tid) " needs an ordinary `match`"))))
                                    (let ((many ctele) (many ret)) $ ctor-type env6b c3)
                                    (let ((many extra)) (and (mult-is-many mk) $ and (mult-is-once smult) (cells-allowed env6b mid)))
                                    (let ((many env7) (many ordinary) (many cellname)) (pattern-fields env6b c3 ctele fields extra))
                                    (let ((many mults)) $ field-mults (tele-mults ctele) smult)
                                    (let ((many ss)) $ shapes mctors env7)
                                    (let ((many run)) $ and (env-run-pos env7) $ and (mult-is-many smult) $ list-is-empty _ $ env-errors env7)
                                    (let ((many env9) (many fids) (many u)) $ open-fields env7 ctele (raw-names ordinary) (raw-sites ordinary env7) (Some _ mults) sres c3 ret)
                                    (match many u _
                                      ((UContra msg) (values (env-error env9 $ str-cat3 "the scrutinee contradicts the facts in force (" (clash-str env9 msg) ")") ctx $ SNone _))
                                      ((UOk env10)
                                        (let ((many env10b) (many alias)) (pattern-cell-option env10 smult sres c3 fids extra cellname))
                                        (match many smult _
                                          ((Erased) (values env10b ctx $ SNone _))
                                          (else
                                            (match many run _
                                              ((BTrue)
                                                (match many ctx (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                                                  ((Cons _ _ _) (values env10b ctx $ SNone _))
                                                  ((Nil _)
                                                    (match many (ctor-of env10b c3) (((Env) _) ((List $ List $ Nat) c0) ((StmtCode ctx c0) sc0))
                                                      ((None _) (values env10b ctx $ SNone _))
                                                      ((Some _ ct)
                                                        (let ((many env11)) (env-run-let env10b many-one source-code (Cons _ saved (Nil _))))
                                                        (let ((many env12)) (env-set-fields env11 saved ct fids mults))
                                                        (let ((many env13)) (match many alias (((Env) _)) ((None _) env12) ((Some _ x) (forward-state env12 x saved))))
                                                        (values env13 ctx $ SNone _))))))
                                              ((BFalse)
                                                (let ((many mfids)) $ many-of mults fids)
                                                (let ((many savedctx)) (Cons _ (Cons _ saved (Nil _)) ctx))
                                                (let ((many fieldctx)) (Cons _ mfids savedctx))
                                                (let ((many save)) (SLet ctx many-one (Cons _ saved (Nil _)) (PkMany _ (Nil _) saved (Nil _) (PkNil _)) source-code))
                                                (let ((many destruct2)) (SMatch savedctx (var-code env10b savedctx saved) (match-shape env10b savedctx mid tid disc ss) (discriminant ss c3) mfids))
                                                (match many alias (((Env) _) ((List $ List $ Nat) c4) ((StmtCode ctx c4) sc))
                                                  ((None _) (values env10b fieldctx (SSeq _ _ _ save destruct2)))
                                                  ((Some _ x)
                                                    (let ((many bindcell)) (SLet fieldctx many-one (Cons _ x (Nil _)) (PkMany _ (Nil _) x (Nil _) (PkNil _)) (var-code env10b fieldctx saved)))
                                                    (values env10b (Cons _ (Cons _ x (Nil _)) fieldctx) (SSeq _ _ _ save (SSeq _ _ _ destruct2 bindcell))))))))))))))))))))))))))))

  ; unary (SUGAR.md 5): the literals checked in the reference's order, then the let-match the form stands
  ; for, written out as there.
  ((many elab-unary : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Mult) spos) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (let ((many arity-error)) $ env-error env "`unary` takes one or two literals")
    (match many args _
      ((Nil _) (values arity-error ctx $ SNone _))
      ((Cons _ araw rest)
        (let ((many env1) (many ea)) $ numeral-entry env araw)
        (match many ea _
          ((None _) (values env1 ctx $ SNone _))
          ((Some _ pa)
            (match many pa _
              ((MkPair _ _ za _)
                (let ((many (Env) env2) (many (Maybe $ Nat) lo))
                  (match many rest _
                    ((Nil _) (values env1 $ Some _ 0))
                    ((Cons _ braw rest2)
                      (match many rest2 (((Env) _) ((Maybe $ Nat) l0))
                        ((Cons _ _ _) (values arity-error $ None _))
                        ((Nil _)
                          (let ((many env2) (many eb)) $ numeral-entry env1 braw)
                          (match many eb (((Env) _) ((Maybe $ Nat) l0))
                            ((None _) (values env2 $ None _))
                            ((Some _ pb)
                              (match many pb (((Env) _) ((Maybe $ Nat) l0))
                                ((MkPair _ _ zb _)
                                  (match many (nat-lt zb za) (((Env) _) ((Maybe $ Nat) l0))
                                    ((BTrue) (values env2 $ Some _ zb))
                                    ((BFalse) (values (env-error env2 $ str-cat3 "`unary`: " (nat-str za) $ str-cat " does not exceed " $ nat-str zb) $ None _))))))))))))
                (match many lo _
                  ((None _) (values env2 ctx $ SNone _))
                  ((Some _ l)
                    (let ((many k)) $ nat-sub za l)
                    (match many (nat-lt 4096 k) _
                      ((BTrue) (values (env-error env2 $ str-cat3 "`unary`: " (nat-str k) " successors is beyond the limit") ctx $ SNone _))
                      ((BFalse)
                        (let ((many (Bool) floored)) $ match many rest _ ((Nil _) (BFalse)) ((Cons _ _ _) (BTrue)))
                        (match many sugar _
                          ((Zero) (values (env-error env2 "internal: a generated form contains sugar") ctx $ SNone _))
                          ((Succ k2)
                            (let ((many gen)) $ unary-source za l floored)
                            (let ((many env3) (many ctx2) (many sc)) $ notail $ elab-stmt k2 gen (generated-form gen env2) ctx spos)
                            (values (leave-prelude env2 env3) ctx2 sc))))))))))))))

  ; distinct (SUGAR.md 5): a match on numeral-inj's Eq, once the two literals are checked to be different
  ; spellings of one canonical value.
  ((many elab-distinct : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (many (Env) r) (many (List $ Res) ress))
    (let ((many none)) $ Nil $ Res)
    (let ((many arity-error)) $ env-error env "`distinct` takes two literals")
    (match many args _
      ((Nil _) (values arity-error none))
      ((Cons _ araw rest)
        (match many rest _
          ((Nil _) (values arity-error none))
          ((Cons _ braw rest2)
            (match many rest2 _
              ((Cons _ _ _) (values arity-error none))
              ((Nil _)
                (let ((many env1) (many ea)) $ numeral-entry env araw)
                (let ((many env2) (many eb)) $ numeral-entry env1 braw)
                (match many ea _
                  ((None _) (values env2 none))
                  ((Some _ pa)
                    (match many eb _
                      ((None _) (values env2 none))
                      ((Some _ pb)
                        (match many pa _
                          ((MkPair _ _ za xa)
                            (match many pb _
                              ((MkPair _ _ zb xb)
                                (match many (nat-cmp za zb) _
                                  ((CEq _ _ _) (values (env-error env2 $ str-cat3 "`distinct`: " (nat-str za) " is the same literal twice") none))
                                  (else
                                    (match many (equal-env env2 (TVar xa) $ TVar xb) _
                                      ((BFalse) (values (env-error env2 $ str-cat3 "`distinct`: " (nat-str za) $ str-cat3 " and " (nat-str zb) " do not canonicalize equally here") none))
                                      ((BTrue)
                                        (match many sugar (((Env) _) ((List $ Res) rs0))
                                          ((Zero) (values (env-error env2 "internal: a generated form contains sugar") none))
                                          ((Succ k)
                                            (let ((many gen)) $ distinct-source za zb)
                                            (let ((many env3) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand k gen (generated-form gen env2) ctx erased-one no-tele (CCPlain) (Fixed _))
                                            (values (leave-prelude env2 env3) ress))))))))))))))))))))))

  ; let (section 9): binders, then the right-hand side; run at once in run position (section 34); an
  ; annotation is a checked redundancy.
  ; Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
  ; produce (SUGAR.md 6); the check of each binder against its value stays as it was.
  ((many elab-let : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (subterm many (LetParts args) parts) (many (Env) env0) (many (List $ List $ Nat) ctx) (many (Maybe $ List $ Entry) tele) (many (Mult) spos) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (match many parts _
      ((MkLetParts _ binders rhs wr)
        (let ((many env1)) $ check-binder-mults _ binders env0)
        (let ((many expect) (erased lbe)) $ src-mults _ binders)
        (let ((many env1b) (many ctx2) (many sc) (many final)) $ notail $ elab-stmts sugar args rhs wr env1 ctx spos)
        (match many final _
          ((FinalNone _) (values (env-error env1b "a body needs a final expression") ctx2 sc))
          ((FinalIs _ fin pf)
            (let ((many inner) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar (subterm pf) fin env1b ctx2 expect tele (CCPlain) (Fixed _))
            (let ((many run)) $ env-run-pos env1)
            (let ((many env2) (many ids) (erased lids)) $ notail $ bind-let sugar args binders (env-hide env1 inner) ress (lockstep-trans _ _ _ _ _ _ lbe lock) run tele $ Nil _)
            (let ((many many-ids) (erased pk)) $ picked-of _ expect ids $ lockstep-trans _ _ _ _ _ _ (lockstep-sym _ _ _ _ lbe) lids)
            (let ((many (Env) env3))
              (match many ctx2 _
                ((Cons _ _ _) env2)
                ((Nil _)
                  (match many run (((Env) _))
                    ((BFalse) env2)
                    ((BTrue)
                      (match many (and (mult-is-many $ pos-mult expect) $ list-is-empty _ $ env-errors inner) (((Env) _))
                        ((BTrue) (env-run-let env2 expect code ids))
                        ((BFalse) (env-set-tokens env2 ids))))))))
            (match many (or run $ not $ mult-is-many $ pos-mult expect) _
              ((BTrue) (values env3 ctx2 sc))
              ((BFalse) (values env3 (Cons _ many-ids ctx2) $ SSeq _ _ _ sc $ SLet _ expect many-ids pk code))))))))

  ((many bind-let : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ SrcEntry root) binders) (many (Env) env) (many (List $ Res) ress) (erased (Lockstep (SrcEntry root) (Res) binders ress) lr) (many (Bool) run) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) ->
      (many (Env) r) (many (List $ Nat) ids) (erased (Lockstep (SrcEntry root) (Nat) binders ids) lids))
    (match many binders _
      ((Nil _) (values env (Nil _) (LsNil _ _)))
      ((Cons _ b brest)
        (match many b _
          ((MkSrcEntry _ _ smult ssg name place epos)
            (let ((many (Res) r) (many (List $ Res) rrest) (erased (Lockstep (SrcEntry root) (Res) brest rrest) lr2))
              (let-match erased lr (LsCons ta tb x y xs ys p))
              (let-match many ress (Cons c r rs))
              (values r rs p))
            (let ((many (Mult) mult)) $ match many smult _ ((None _) (Many)) ((Some _ m) m))
            (let ((many (Env) env1a) (many (Maybe $ List $ Entry) trest))
              (match many tele _
                ((Some _ es)
                  (match many es (((Env) _) ((Maybe $ List $ Entry) t0))
                    ((Nil _) (values env no-tele))
                    ((Cons _ e erest) (values (check-sg env (sg-inst done $ entry-sg e) r) $ Some _ erest))))
                ((None _)
                  (match many ssg (((Env) _) ((Maybe $ List $ Entry) t0))
                    ((None _) (values env no-tele))
                    ((Some _ s)
                      (match many s (((Env) _) ((Maybe $ List $ Entry) t0))
                        ((SrcTy _ t p) (let ((many env1) (many ty) (many tyty)) $ notail $ elab-term sugar (subterm p) t env (BTrue) no-tele) (values (check-sg env1 (SgTy ty) r) no-tele))
                        ((SrcIs _ t p) (let ((many env1) (many ty) (many tyty)) $ notail $ elab-term sugar (subterm p) t env (BFalse) no-tele) (values (check-sg env1 (SgIs ty tyty) r) no-tele))))))))
            (let ((many env1)) $ error-when (settle-res env1a r) (is-some _ place) "`at` is allowed only on returns and match annotations")
            (let ((many env2a) (many x)) $ bind env1 (name-or-anon name) (Some _ $ loc-in env1 epos) (BTrue) mult (res-ty r) (Some _ $ res-term r) delegate-id)
            (let ((many env2b)) $ mark-word env2a x $ BFalse)
            (let ((many env2)) $ match many (res-place r) (((Env) _)) ((None _) env2b) ((Some _ p) (at-merge env2b (TVar x) p)))
            (let ((many (Env) env3))
              (match many run _
                ((BTrue) env2)
                ((BFalse) (match many (res-term r) (((Env) _)) ((TVar y) (forward-state env2 x y)) (else env2)))))
            (let ((many env4) (many ids) (erased lk)) $ notail $ bind-let sugar root brest env3 rrest lr2 run trest $ Cons _ (res-term r) done)
            (values env4 (Cons _ x ids) (LsCons _ _ b x brest ids lk)))))))

  ; def-fns (sections 7, 27): headers bound Dyn, each body elaborated at the block's level under its own
  ; subterm parameters and checked against its return telescope; closures minted Const in run position.
  ((many elab-def-fns : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Bool) uq) -> (many (Env) r) (many (List $ List $ Nat) ctx2) (many (StmtCode ctx ctx2) sc))
    (match many args _
      ((Nil _) (values (env-error env "`def-fns` needs a level") ctx $ SNone _))
      ((Cons _ lvraw fns)
        (let ((many (Env) env2) (many (Nat) lvl))
          (match many (is-underscore lvraw) _
            ((BTrue) (mint-level env (None _) (None _)))
            ((BFalse) (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar lvraw env (BFalse) no-tele) (level-var-checked env2 t))))
        (let ((many env2a)) $ error-when env2 (and uq $ not $ nat-eq (list-length _ fns) 1) "`def-unique` defines exactly one function")
        (let ((many env3) (many headers)) $ notail $ elab-headers sugar fns env2a lvl uq)
        (let ((many env4) (many gids) (many fids)) $ bind-headers _ headers env3 lvl)
        (let ((many env5) (many fns2) (erased lk)) $ notail $ define-fns sugar fns headers env4 ctx gids gids fids lvl $ env-run-pos env4)
        (let ((many group)) $ MkGroup _ gids fns2 lk)
        (match many gids _
          ((Nil _) (values env5 ctx $ SNone _))
          ((Cons _ _ _)
            (match many ctx _
              ((Nil _) (values (env-close-group env5 _ group) ctx $ SNone _))
              ((Cons _ _ _) (values env5 (Cons _ gids ctx) $ SLetRec _ _ group))))))))

  ((many elab-headers : (subterm many (Nat) sugar) (subterm many (List $ Raw) fns) (many (Env) env) (many (Nat) lvl) (many (Bool) uq) -> (many (Env) r) (many (Headers fns) hs))
    (match many fns _
      ((Nil _) (values env $ HStop _))
      ((Cons _ f rest)
        (let ((many envl)) $ env-at env $ raw-pos f)
        (let ((many bad)) $ env-error envl "malformed function definition")
        (match many f _
          ((RList _ items)
            (match many items _
              ((Nil _) (values bad $ HStop _))
              ((Cons _ sigraw body)
                (match many sigraw _
                  ((RList _ sitems)
                    (match many sitems _
                      ((Nil _) (values bad $ HStop _))
                      ((Cons _ mraw items1)
                        (let ((many env0a) (many mult)) $ mult-checked envl mraw)
                        (let ((many env0)) $ match many uq (((Env) _))
                          ((BTrue) (error-when env0a (and (mult-is-many mult) $ not $ mult-is-once mult) "`def-unique` requires `unique` or `erased`"))
                          ((BFalse) (error-when env0a (mult-is-once mult) "use `def-unique` to define a unique function")))
                        (let ((many isabs) (many isext) (many items2) (erased w2)) $ take-marks items1 _ (WIn items1 sitems $ prove-subterm items1 sitems) env0 (MkAbsurd) $ MkExtern)
                        (let ((many bad0)) $ env-error env0 "malformed function header")
                        (match many items2 _
                          ((Nil _) (values bad0 $ HStop _))
                          ((Cons _ nraw items3)
                            (let ((many name)) $ raw-name nraw)
                            (match many items3 _
                              ((Nil _) (values bad0 $ HStop _))
                              ((Cons _ colon sg)
                                (let ((many env1)) $ colon-checked env0 colon bad0)
                                (let ((erased psg)) $ subterm-trans (prove-subterm sg items2) $ within-in _ _ _ _ w2 $ subterm-trans (prove-subterm sitems sigraw) $ subterm-trans (prove-subterm sigraw items) $ prove-subterm items f)
                                (let ((many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env1)
                                (let ((many rs)) $ subs-of after _ wa)
                                (let ((many env2) (many params) (many rets)) $ notail $ elab-fn-type sugar (subterm (subterm-trans psg $ prove-subterm f fns)) sg one-step (MkPair _ _ ps rs) env1)
                                (let ((many found)) $ extern-of name)
                                (let ((many (Env) env2b))
                                  (match many found _
                                    ((None _) env2)
                                    ((Some _ se)
                                      (match many se _
                                        ((MkSomeExtern _ e)
                                          (error-when env2 (and isext $ not $ nat-eq (many-count params) $ ext-arity _ e) $ str-cat3 "the extern implementation of " (tick name) $ str-cat3 " takes " (nat-str $ ext-arity _ e) $ str-cat3 " arguments, its model " (nat-str $ many-count params) ""))))))
                                (let ((many (Env) env3)) $ match many isext _ ((BTrue) (claim-extern env2b name $ is-some _ found)) ((BFalse) env2b))
                                (let ((many (Maybe $ SomeExtern) se)) $ match many isext _ ((BTrue) found) ((BFalse) (None _)))
                                (let ((many (Env) env3b) (many (Maybe $ Impl) impl))
                                  (match many se _
                                    ((None _) (values env3 (None _)))
                                    ((Some _ e2)
                                      (match many e2 _
                                        ((MkSomeExtern _ e)
                                          (match many (ext-result-shape _ e) _
                                            ((None _) (values env3 (Some _ $ MkImpl e2 $ Nil _)))
                                            ((Some _ want)
                                              (let ((many env3a) (many cs)) $ extern-ctors env3 name rets want)
                                              (values env3a (Some _ $ MkImpl e2 cs)))))))))
                                (let ((many env4) (many hs)) $ notail $ elab-headers sugar rest (env-back env env3b) lvl uq)
                                (values env4 $ HCons _ _ (MkHeader _ (raw-pos sigraw) name mult uq isabs impl params rets body $ subterm-trans (prove-subterm body items) $ prove-subterm items f) hs)))))))) (else (values bad $ HStop _)))))) (else (values bad $ HStop fns))))))

  ((many define-fns : (subterm many (Nat) sugar) (subterm many (List $ Raw) fns) (subterm many (Headers fns) headers) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) gall) (many (List $ Nat) gids) (many (Bound fns headers gids) fids) (many (Nat) lvl) (many (Bool) top) ->
      (many (Env) r) (many (List $ Pair (Nat) $ Func gall ctx) fns2) (erased (Lockstep (Nat) (Pair (Nat) $ Func gall ctx) gids fns2) lk))
    (match many fns _
      ((Nil _)
        (let-match many fids (BStop z))
        (values env (Nil _) (LsNil _ _)))
      ((Cons _ f rest)
        (match many headers _
          ((HStop _)
            (let-match many fids (BStop z2))
            (values env (Nil _) (LsNil _ _)))
          ((HCons _ _ h hrest)
            (match many fids _
              ((BMany _ _ _ _ _ x xrest)
                (let-match many gids (Cons zg xg grest))
                (let ((many env3) (many fn)) $ notail $ define-fn sugar (subterm (prove-subterm f fns)) f h env ctx gall x lvl top)
                (let ((many env4) (many more) (erased lk)) $ notail $ define-fns sugar rest hrest env3 ctx gall grest xrest lvl top)
                (values env4 (Cons _ (MkPair _ _ x fn) more) (LsCons _ _ x (MkPair _ _ x fn) grest more lk)))
              ((BErased _ _ _ _ _ x xrest)
                (let ((many env3) (many fn)) $ notail $ define-fn sugar (subterm (prove-subterm f fns)) f h env ctx gall x lvl top)
                (tail $ define-fns sugar rest hrest env3 ctx gall gids xrest lvl top))))))))

  ; One function's body checked at its level under its parameters, the group's frame and the defining scope,
  ; its marks validated, and its delegate proof bound where it has one.
  ((many define-fn : (subterm many (Nat) sugar) (subterm many (Raw) f) (many (Header f) h) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Nat) gall) (many (Nat) x) (many (Nat) lvl) (many (Bool) top) ->
      (many (Env) r) (many (Func gall ctx) fn))
    (match many h _
      ((MkHeader _ hpos name mult uq isabs impl params rets body pb)
        (let ((many ty)) $ TFn uq (TVar lvl) params rets)
        (let ((many env0)) $ match many uq (((Env) _)) ((BTrue) (set-entry-mult env x $ Erased)) ((BFalse) env))
        (let ((many envb0) (many pids) (erased lock)) $ open-tele params (env-set-run-pos env0 $ BFalse) (None _) (None _) (None _) (Nil _) $ BFalse)
        (let ((many envb1)) $ env-enter-body (mark-words pids envb0 $ BFalse) lvl $ subterm-params params pids)
        (let ((many captures)) $ match many uq (((List $ Nat) _)) ((BTrue) (env-captures env)) ((BFalse) (env-words env)))
        (let ((many envb)) $ env-set-captures (env-set-usage-erased (env-set-in-extern envb1 (or (env-in-extern env) $ is-some _ impl)) (or (env-usage-erased env) $ not $ mult-is-many mult)) captures)
        (let ((many rms)) $ under-list (tele-mults rets) mult)
        (let ((many mps)) $ many-of (tele-mults params) pids)
        (let ((many bctx)) $ Cons _ mps $ Cons _ gall ctx)
        (let ((many (Env) envb2) (many (Code bctx rms) code))
          (match many isabs _
            ((BTrue)
              (let ((many envb1b) (many ress) (many code) (erased lock3)) $ notail $ elab-body sugar (subterm pb) body body (WHere _) envb bctx erased-one no-tele)
              (let ((many envb2)) $ settle-empty envb1b ress lock3)
              (values envb2 $ CAbsurd _ rms))
            ((BFalse)
              (let ((many pvars)) $ tvars-rev pids $ Nil _)
              (let ((many tele)) $ instantiate-tele pvars rets)
              (let ((many envb1b) (many ress) (many code) (erased lock3)) $ notail $ elab-body sugar (subterm pb) body body (WHere _) envb bctx rms (Some _ tele))
              (let ((many envb2)) $ check-results-count envb1b body rets ress pvars)
              (values envb2 $ match many mult (((Code bctx rms) _)) ((Erased) (CErased _ rms)) (else code)))))
        (let ((many physical)) $ under-list (physical-mults rets) mult)
        (let ((many envb2a) (many projected)) $ project-code bctx envb2 rms physical code)
        (let ((many envb3) (many code2) (many delegated)) $ check-marks envb2a bctx mps physical projected)
        (let ((many env2)) $ set-entry-mult (env-set-uses (env-discard env envb3) $ uses-join (env-uses env) $ env-uses envb3) x mult)
        (let ((many (Env) env3))
          (match many delegated _
            ((None _) env2)
            ((Some _ callee)
              (let ((many env2b))
                (match many (is-some _ impl) (((Env) _))
                  ((BTrue) (env-error (env-at env2 hpos) "a function marked `extern` cannot have a `delegate` body: its implementation is promised only under its own signature, and a `Delegate` proof would let a `coerce` run it under the callee's; mark the call `tail`"))
                  ((BFalse) (match many (nat-lt callee x) _ ((BTrue) env2) ((BFalse) (env-error (env-at env2 hpos) "the function a `delegate` call names must be introduced before the function whose body it is"))))))
              (let ((many env2c)) $ env-set-aliases env2b $ idmap-set _ x (alias-target env2b callee) $ env-aliases env2b)
              (let ((many env3) (many px)) $ bind env2c (None _) (None _) (BFalse) (Erased) (proof-type delegate-id $ Cons _ (sharing-of-fn env2 ty) $ Cons _ ty $ Cons _ (TVar x) $ Cons _ (sharing-of-fn env2 $ type-of env2 callee) $ Cons _ (type-of env2 callee) $ Cons _ (TVar callee) $ Nil _) (None _) delegate-id)
              env3)))
        (values env3 $ match many delegated (((Func gall ctx) _))
          ((None _) (MkFunc _ _ physical name x mps code2 impl top))
          ((Some _ callee) (MkAlias _ _ name x $ var-code env3 (Cons _ gall ctx) $ alias-target env3 callee))))))

  ; def-adts (sections 12, 19, 27): type constructors bound first, each as soon as its header is read so a
  ; later header may mention it, then each type's constructors, Matchable and Newtype; every constructor
  ; returns its own type.
  ((many elab-adt-headers : (subterm many (Nat) sugar) (subterm many (List $ Raw) adts) (many (Env) env) -> (many (Env) r) (many (AdtHeaders adts) hs) (many (Tids adts hs) tids))
    (match many adts _
      ((Nil _) (values env (AStop _) $ TStop _))
      ((Cons _ adt rest)
        (let ((many envl)) $ env-at env $ raw-pos adt)
        (let ((many bad)) $ env-error envl "malformed `def-adts` entry")
        (match many adt _
          ((RList _ items)
            (match many items _
              ((Nil _) (values bad (AStop _) $ TStop _))
              ((Cons _ sigraw rest2)
                (match many sigraw _
                  ((RList _ sitems)
                    (match many sitems _
                      ((Nil _) (values bad (AStop _) $ TStop _))
                      ((Cons _ nraw items1)
                        (let ((many name)) $ raw-name nraw)
                        (match many items1 _
                          ((Nil _) (values bad (AStop _) $ TStop _))
                          ((Cons _ colon sg)
                            (let ((many env0)) $ colon-checked envl colon bad)
                            (let ((many bad0)) $ env-error env0 "malformed `def-adts` entry")
                            (let ((many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env0)
                            (match many after _
                              ((Nil _) (values bad0 (AStop _) $ TStop _))
                              ((Cons _ tyraw after2)
                                (match many rest2 _
                                  ((Nil _) (values bad0 (AStop _) $ TStop _))
                                  ((Cons _ draw after3)
                                    (let ((many stray)) $ match many after2 (((Bool) _)) ((Nil _) (BFalse)) ((Cons _ _ _) (BTrue)))
                                    (let ((many env0c)) $ error-when env0 stray "a type constructor declares one return")
                                    (let ((many env1) (many disc)) $ disc-of-checked env0c draw)
                                    (let ((many nt) (many ext) (many cs) (erased wc)) $ take-marks after3 _ (within-step after3 rest2 items (prove-subterm after3 rest2) $ WIn rest2 items $ prove-subterm rest2 items) env1 (MkNewtypeMark) $ MkExtern)
                                    (let ((many tyraws)) $ Cons _ (MkSub _ tyraw $ in-within (Raw) tyraw after sg (prove-subterm tyraw after) wa) $ Nil _)
                                    (let ((many env2) (many ty)) $ notail $ elab-tyctor sugar sg one-step (MkPair _ _ ps tyraws) env1)
                                    (let ((many env2b) (many x)) $ bind-erased env2 (Some _ name) (Some _ $ loc-in env2 $ raw-head-pos adt) (BTrue) (Erased) ty (None _) delegate-id)
                                    (let ((many env3) (many hs) (many tids)) $ notail $ elab-adt-headers sugar rest $ env-back env env2b)
                                    (let ((many h)) $ MkAdtHeader _ name disc nt ext cs $ within-in cs items (Raw) adt wc $ prove-subterm items adt)
                                    (values env3 (AHCons _ _ h hs) $ TCons _ _ _ _ x tids)))))))))) (else (values bad (AStop _) $ TStop _)))))) (else (values bad (AStop adts) $ TStop adts))))))

  ((many define-adts : (subterm many (Nat) sugar) (subterm many (List $ Raw) adts) (subterm many (AdtHeaders adts) headers) (many (Env) env) (many (Tids adts headers) tids) -> (many (Env) r) (many (List $ Pair (Nat) $ Block (Ref Block (HEmpty Block))) consts))
    (match many adts _
      ((Nil _) (values env $ Nil _))
      ((Cons _ adt rest)
        (match many headers _
          ((AStop _) (values env $ Nil _))
          ((AHCons _ _ h hrest)
            (let-match many tids (TCons g3 r3 h3 hs3 tid trest))
            (match many h _
              ((MkAdtHeader _ name disc nt ext ctors pc)
                (let ((many envh)) $ env-at env $ raw-head-pos adt)
                (let ((many env2) (many mcpairs)) $ notail $ elab-ctors sugar (subterm (subterm-trans pc $ prove-subterm adt adts)) ctors envh tid)
                (let ((many mctors)) $ mctors-of mcpairs)
                (let ((many ss)) $ shapes mctors env2)
                (let ((many tagged)) $ tagged-of disc ss)
                (let ((many found)) $ ext-type-of name)
                (let ((many (Env) env2b)) $ match many ext _ ((BTrue) (claim-extern env2 name $ is-some _ found)) ((BFalse) env2))
                (let ((many (Maybe $ ExtType) extname)) $ match many ext _ ((BTrue) found) ((BFalse) (None _)))
                (let ((many (Env) env2c))
                  (match many extname _
                    ((None _) env2b)
                    ((Some _ et)
                      (let ((many ns)) $ cshape-arities $ non-phantom ss)
                      (let ((many want)) $ ext-type-shape et)
                      (let ((many (String) how)) $ match many tagged _ ((BTrue) "(") ((BFalse) "the untagged ("))
                      (error-unless env2b (and tagged $ nat-list-eq ns want) $ str-cat3 "the extern implementation of " (tick name) $ str-cat3 " has the tagged shape (" (spell-nats want) $ str-cat3 "), its declaration " how $ str-cat (spell-nats ns) ")"))))
                (let ((many adt2)) $ mint-adt env2c tid disc ss extname nt)
                (let ((many records)) $ adt-ctors adt2)
                (let ((many cvals)) $ ctor-values records)
                (let ((many env3) (many mid)) $ bind-closed env2c (None _) (None _) (BFalse) (Many) (BMat _ adt2) (TMatchable disc nt ext (TVar tid) mctors) (None _) delegate-id)
                (let ((many env3b)) $ open-minted env3 mid)
                (let ((many (Env) env4))
                  (match many nt _
                    ((BFalse) env3b)
                    ((BTrue)
                      (match many (wrapper disc ss) (((Env) _))
                        ((None _) (env-error env3b $ str-cat (tick name) " is not of newtype shape (section 38)"))
                        ((Some _ _) env3b)))))
                (let ((many env5) (many more)) $ notail $ define-adts sugar rest hrest env4 trest)
                (let ((many all) (erased cat)) $ list-append _ cvals $ Cons _ (MkPair _ _ mid $ BMat _ adt2) more)
                (values env5 all))))))))

  ((many elab-ctors : (subterm many (Nat) sugar) (subterm many (List $ Raw) ctors) (many (Env) env) (many (Nat) tid) -> (many (Env) r) (many (List $ Pair (Mult) $ Nat) cs))
    (match many ctors _
      ((Nil _) (values env $ Nil _))
      ((Cons _ craw rest)
        (let ((many envl)) $ env-at env $ raw-pos craw)
        (let ((many bad)) $ env-error envl "malformed constructor")
        (let ((many (Env) env0) (many (Maybe $ CtorParts craw) parsed))
          (match many craw _
            ((RList _ items)
              (match many items (((Env) _) ((Maybe $ CtorParts craw) p0))
                ((Nil _) (values bad $ None _))
                ((Cons _ mraw items1)
                  (let ((many env0) (many mult)) $ mult-checked envl mraw)
                  (let ((many bad0)) $ env-error env0 "malformed constructor")
                  (match many items1 (((Env) _) ((Maybe $ CtorParts craw) p0))
                    ((Nil _) (values bad0 $ None _))
                    ((Cons _ nraw more)
                      (match many more (((Env) _) ((Maybe $ CtorParts craw) p0))
                        ((Nil _) (values bad0 $ None _))
                        ((Cons _ colon sg)
                          (let ((many env1)) $ colon-checked env0 colon bad0)
                          (values env1 $ Some _ $ MkCtorParts _ mult (raw-name nraw) sg $ prove-subterm sg craw)))))))) (else (values bad $ None $ CtorParts craw))))
        (match many parsed _
          ((None _) (tail $ elab-ctors sugar rest (env-back env env0) tid))
          ((Some _ cp)
            (match many cp _
              ((MkCtorParts _ mult name sg psg)
                (let ((many ps) (many after) (erased wa)) $ split-arrow sg _ (WHere sg) env0)
                (let ((many env2) (many tele) (many ret) (many ty)) $ notail $ elab-valctor sugar (subterm (subterm-trans psg $ prove-subterm craw ctors)) sg one-step (MkPair _ _ ps $ subs-of after _ wa) env0)
                (let ((many (Env) env2b))
                  (match many (type-head env2 ret) _
                    ((None _) (env-error env2 $ str-cat3 (tick name) " must return an application of " $ qname env2 tid))
                    ((Some _ t) (match many (nat-cmp t tid) (((Env) _)) ((CEq _ _ _) env2) (else (env-error env2 $ str-cat3 (tick name) " must return an application of " $ qname env2 tid))))))
                (let ((many (Env) env2c))
                  (match many (and (not $ mult-is-many mult) $ not $ nat-is-zero $ many-count tele) _
                    ((BTrue) (env-warn env2b $ located env2b ": warning: " $ str-cat3 "phantom constructor " (tick name) " has a non-erased field"))
                    ((BFalse) env2b)))
                (let ((many env3)) $ env-discard env0 env2c)
                (let ((many (Env) env4) (many (Nat) c)) $ match many mult _ ((Erased) (bind-erased env3 (Some _ name) (Some _ $ loc-in env3 $ raw-pos craw) (BTrue) mult ty (None _) delegate-id)) (else (bind env3 (Some _ name) (Some _ $ loc-in env3 $ raw-pos craw) (BTrue) mult ty (None _) delegate-id)))
                (let ((many env5) (many cs)) $ notail $ elab-ctors sugar rest (env-back env env4) tid)
                (values env5 $ Cons _ (MkPair _ _ mult c) cs))))))))
  ; tail and delegate wrap a call (section 9, ASSUMPTIONS 9); the compiled code must be that call.
  ((many elab-marked : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) (many (Sp) sp) (many (ExprDemand expect) demand) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
    (let ((many env1)) $ error-unless env (mult-is-many $ pos-mult expect) $ str-cat (tick $ sp-name sp) " in an erased position")
    (match many args _
      ((Nil _) (expr-error _ expect env1 (str-cat (tick $ sp-name sp) " marks a function call, not nothing") "mark"))
      ((Cons _ call _)
        (let ((many env2) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar call env1 ctx expect tele cc demand)
        (let ((many ok)) $ marked-call _ _ code cc)
        (match many ok _
          ((BTrue) (values env2 ress code))
          ((BFalse) (values (env-error env2 $ str-cat3 (tick $ sp-name sp) " marks a function call, not " $ qraw call) ress code))))))

  ; Each entry of a values against its entry of the telescope expected, instantiated with the entries before it.
  ((many elab-values : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) -> (many (Env) r) (many (List $ Res) ress) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) expect codes) pk))
    (match many expect _
      ((Nil _) (values env (Nil _) (Nil _) (PkNil _)))
      ((Cons _ m mrest)
        (match many args _
          ((Nil _)
            (let ((many codes) (erased pk)) $ codes-missing ctx expect)
            (values env (Nil _) codes pk))
          ((Cons _ arg arest)
            (let ((many (Maybe $ List $ Entry) here) (many (Maybe $ List $ Entry) trest))
              (match many tele _
                ((None _) (values no-tele no-tele))
                ((Some _ es)
                  (match many es (((Maybe $ List $ Entry) _) ((Maybe $ List $ Entry) t))
                    ((Nil _) (values no-tele no-tele))
                    ((Cons _ e erest) (values (Some _ $ Cons _ (entry-with-sg e $ sg-inst done $ entry-sg e) $ Nil _) $ Some _ erest))))))
            (let ((many env2) (many rs) (many code) (erased lock)) $ notail $ elab-expr-demand sugar arg env ctx (Cons _ m $ Nil _) here (CCPlain) (Fixed _))
            (let ((many env3) (many ress) (many codes) (erased pk)) $ notail $ elab-values sugar arest env2 ctx mrest trest $ Cons _ (res-term $ first-res _ _ rs lock) done)
            (let ((many codes2) (erased pk2))
              (match many m (((List $ Code ctx many-one) cs) ((Picked (Code ctx many-one) expect cs) p))
                ((Many) (values (Cons _ code codes) (PkMany _ mrest code codes pk)))
                ((Once) (let ((many one)) $ runtime-one _ m code) (values (Cons _ one codes) (PkOnce _ mrest one codes pk)))
                ((Erased) (values codes (PkErased _ mrest codes pk)))))
            (values env3 (Cons _ (first-res _ _ rs lock) ress) codes2 pk2))))))

  ((many elab-two-terms : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) -> (many (Env) r) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty))
    (let ((many bad) (many m)) $ values (env-error env "two arguments expected") $ TErr "missing")
    (match many args _
      ((Nil _) (values bad m m m m))
      ((Cons _ araw rest)
        (match many rest _
          ((Nil _) (values bad m m m m))
          ((Cons _ braw _)
            (let ((many env2) (many a) (many aty)) $ notail $ elab-term sugar araw env (BFalse) no-tele)
            (let ((many env3) (many b) (many bty)) $ notail $ elab-term sugar braw env2 (BFalse) no-tele)
            (values (settle (settle env3 a) b) a aty b bty))))))

  ; Two proofs of the given kinds, elaborated erased (ASSUMPTIONS 23).
  ((many two-proofs : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) -> (many (Env) r) (many (Res) p) (many (Res) q))
    (let ((many bad)) $ env-error env "two proofs expected")
    (match many args _
      ((Nil _) (values bad no-res no-res))
      ((Cons _ araw rest)
        (match many rest _
          ((Nil _) (values bad no-res no-res))
          ((Cons _ braw _)
            (let ((many env2) (many prs) (many pc) (erased lockp)) $ notail $ elab-expr-demand sugar araw env ctx erased-one no-tele (CCPlain) (Fixed _))
            (let ((many env3) (many qrs) (many qc) (erased lockq)) $ notail $ elab-expr-demand sugar braw env2 ctx erased-one no-tele (CCPlain) (Fixed _))
            (values (settle (settle env3 $ erased-term prs lockp) $ erased-term qrs lockq) (erased-res prs lockp) $ erased-res qrs lockq))))))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field, each checked against
  ; the field's type on its side (section 38).
  ((many elab-sharing-side : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) -> (many (Env) e) (many (Term) side))
    (match many args _
      ((Nil _) (values (env-error env "a `Sharing` argument is required") $ TErr "Sharing"))
      ((Cons _ raw _)
        (match many (is-underscore raw) _
          ((BTrue)
            (let ((many env2) (many x)) $ bind-as env (BTrue) (BFalse) (None _) (Some _ $ loc-in env $ raw-pos raw) (BFalse) (Erased) sharing-term (None _) delegate-id)
            (values env2 $ TVar x))
          ((BFalse)
            (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar raw env (BFalse) no-tele)
            (values (check env2 "type" ty sharing-term) t))))))

  ((many elab-coercible-proof : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) ctor) (many (Maybe $ Pair (Term) $ Term) sides) -> (many (Env) e) (many (Res) r))
    (match many args _
      ((Nil _) (values (env-error env $ str-cat "a " $ str-cat (qname env ctor) " proof is required") no-res))
      ((Cons _ raw _)
        (let ((many env1) (many tele)) $ coercible-proof-tele env ctor sides)
        (let ((many env2) (many ress) (many code) (erased lock)) $ notail $ elab-expr-demand sugar raw env1 ctx erased-one tele (CCPlain) (Fixed _))
        (let ((many r)) $ erased-res ress lock)
        (values (settle-res env2 r) r))))

  ((many coercible-ctor-args : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) tele) (many (List $ Term) src) (many (List $ Term) tgt) (many (Nat) c) (many (Term) side) -> (many (Env) r) (many (List $ Term) src2) (many (List $ Term) tgt2))
    (let ((many wrong)) $ env-error env $ str-cat "`coercible-ctor`: wrong number of arguments for " $ qname env c)
    (match many tele _
      ((Nil _) (match many args _ ((Nil _) (values env src tgt)) ((Cons _ _ _) (values wrong src tgt))))
      ((Cons _ e rest)
        (match many (entry-mult e) _
          ((Erased)
            (match many args _
              ((Nil _) (values wrong src tgt))
              ((Cons _ sraw more)
                (match many more _
                  ((Nil _) (values wrong src tgt))
                  ((Cons _ traw args2)
                    (let ((many env2) (many s) (many sty)) $ notail $ elab-term sugar sraw env (BFalse) no-tele)
                    (let ((many env3) (many t) (many tty)) $ notail $ elab-term sugar traw env2 (BFalse) no-tele)
                    (let ((many env4)) $ check-sg (settle (settle env3 s) t) (sg-inst src $ entry-sg e) $ term-res env3 s sty)
                    (let ((many env5)) $ check-sg env4 (sg-inst tgt $ entry-sg e) $ term-res env4 t tty)
                    (tail $ coercible-ctor-args sugar args2 env5 ctx rest (Cons _ s src) (Cons _ t tgt) c side))))))
          (else
            (match many args _
              ((Nil _) (values wrong src tgt))
              ((Cons _ praw more)
                (let ((many fs)) $ match many (entry-mult e) (((Term) _)) ((Once) side) (else shared-term))
                (let ((many env0) (many ptele)) $ coercible-proof-tele env coercible-id $ Some _ $ MkPair _ _ fs fs)
                (let ((many env1a) (many prs) (many pc) (erased lock)) $ notail $ elab-expr-demand sugar praw env0 ctx erased-one ptele (CCPlain) (Fixed _))
                (let ((many p)) $ erased-res prs lock)
                (let ((many env1)) $ settle-res env1a p)
                (let ((many env2) (many sa) (many sty) (many s) (many sb) (many tty) (many t)) $ expect-proof6 env1 coercible-id p)
                (let ((many env3)) $ check (check env2 "sharing" sa fs) "sharing" sb fs)
                (let ((many env4)) $ check-sg env3 (sg-inst src $ entry-sg e) $ term-res env3 s sty)
                (let ((many env5)) $ check-sg env4 (sg-inst tgt $ entry-sg e) $ term-res env4 t tty)
                (tail $ coercible-ctor-args sugar more env5 ctx rest (Cons _ s src) (Cons _ t tgt) c side))))))))

  ; match (sections 11, 12, 18): the scrutinee, its Matchable, the annotation, then one branch per
  ; constructor, each refined by its forced facts or refuted by them.
  ((many elab-match : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
    (let ((many bad) (many bad-ress) (many bad-code)) $ expr-error ctx expect env "malformed match" "match")
    (match many args _
      ((Nil _) (values bad bad-ress bad-code))
      ((Cons _ mraw more)
        (match many more _
          ((Nil _) (values bad bad-ress bad-code))
          ((Cons _ scrut more2)
            (match many more2 _
              ((Nil _) (values bad bad-ress bad-code))
              ((Cons _ ann branches)
                (let ((many pos) (erased pos-proof)) $ pos-of expect)
                (let ((many env0) (many sm)) $ mult-checked env mraw)
                (let ((many env0d)) $ written env0 pos sm "match")
                (let ((many smult)) $ under pos sm)
                (let ((many env2a) (many srs) (many scode) (erased lock)) $ notail $ elab-expr-demand sugar scrut env0d ctx (Cons _ smult $ Nil _) no-tele (CCPlain) (Fixed _))
                (let ((many original)) $ first-res _ _ srs lock)
                (let ((many source-ctx)) ctx)
                (let ((many source-code)) (runtime-one _ smult scode))
                (let ((many env2a2) (many sres) (many saved)) (prepare-argument env2a smult original))
                (let ((many ctx4)) (Cons _ (Cons _ saved (Nil _)) source-ctx))
                (let ((many scode2)) (var-code env2a2 ctx4 saved))
                (let ((many env2b) (many found)) $ scrutinee-matchable env2a2 smult sres)
                (match many found _
                  ((None _) (values env2b (Nil _) $ CError _ expect "no head"))
                  ((Some _ pr)
                    (match many pr _
                      ((MkPair _ _ tid info)
                        (match many info _
                          ((MkMatchInfo mid disc mctors _)
                            (let ((many ss)) $ shapes mctors env2b)
                            (let ((many tagged)) $ tagged-of disc ss)
                            (let ((many (Env) env2c))
                              (match many (and (mult-is-many pos) $ mult-is-many smult) _
                                ((BTrue) (use-entry (held-needs-many env2b tid mid) (Many) mid (BFalse)))
                                ((BFalse) env2b)))
                            (let ((many outer-expect)) expect)
                            (let ((many env3b) (many ann-tele) (many inner-expect) (many bridge)) $ notail $ result-tele sugar ann env2c expect tele demand)
                            (let ((many expect2)) inner-expect)
                            (let ((many extra)) (and (mult-is-once smult) (cells-allowed env3b mid)))
                            (let ((many incoming)) (env-uses env3b))
                            (let ((many env5) (many real) (many seen)) $ notail $ elab-branches sugar branches env3b ctx4 tid sres smult mctors ann-tele expect2 (Nil _) (Nil _) extra saved incoming incoming)
                            (let ((many env6)) $ check-coverage mctors env5 seen)
                            (let ((many env6b) (many first) (many reachable) (many covered)) $ covered-of mctors env6 seen sres smult (None _) (BFalse) $ Nil _)
                            (let ((many env6c) (many dflt)) $ notail $ elab-else sugar branches env6b ctx4 ann-tele expect2 first reachable (None _) (None _) sres smult extra saved incoming mctors)
                            (let ((many nreal)) $ nat-add (list-length _ real) $ match many dflt (((Nat) _)) ((None _) 0) ((Some _ _) 1))
                            (let ((many env7)) $ match many (and (mult-is-many pos) $ and (or (not tagged) $ not $ mult-is-many smult) $ nat-lt 1 nreal) (((Env) _))
                              ((BTrue) (forced-error mctors env6c sres smult (real-ctors _ _ real) $ env-error env6c "a match without a runtime discriminant can have only one real branch"))
                              ((BFalse) env6c))
                            (let ((many live) (erased lp)) $ list-append _ (discs-of (real-ctors _ _ real) ss) $ discs-of covered ss)
                            (let ((many (Code ctx4 expect2) code))
                              (match many pos _
                                ((Erased) (CErased _ expect2))
                                (else
                                  (match many real (((Code ctx4 expect2) _))
                                    ((Nil _)
                                      (match many dflt (((Code ctx4 expect2) _))
                                        ((None _) (CAbsurd _ expect2))
                                        ((Some _ _)
                                          (match many smult (((Code ctx4 expect2) _))
                                            ((Erased) (CMatch _ expect2 (CErased _ many-one) (ShNone _) (Nil _) dflt live))
                                            (else
                                              (match many tagged (((Code ctx4 expect2) _))
                                                ((BFalse) (CMatch _ expect2 scode2 (ShNone _) (Nil _) dflt live))
                                                ((BTrue) (CMatch _ expect2 scode2 (match-shape env7 ctx4 mid tid disc ss) (Nil _) dflt live))))))))
                                    ((Cons _ _ more3)
                                      (match many smult (((Code ctx4 expect2) _))
                                        ((Erased)
                                          (match many more3 (((Code ctx4 expect2) _))
                                            ((Nil _) (CMatch _ expect2 (CErased _ many-one) (ShNone _) (real-branches-code _ _ real ss) dflt live))
                                            ((Cons _ _ _) (CError _ expect2 "one real branch"))))
                                        (else (CMatch _ expect2 scode2 (match-shape env7 ctx4 mid tid disc ss) (real-branches-code _ _ real ss) dflt live))))))))
                            (let ((many env8) (many rids) (erased lock3)) $ open-tele ann-tele env7 (Some _ $ anon-names ann-tele) (None _) (None _) (Nil _) $ BFalse)
                            (values env8 (ress-of rids env8) (bridge-code _ outer-expect expect2 bridge (match many pos _ ((Erased) (CErased _ expect2)) (else (CLet source-ctx many-one expect2 (Cons _ saved (Nil _)) (PkMany _ (Nil _) saved (Nil _) (PkNil _)) source-code code))))))))))))))))))

  ; A match's or open-absurd's return annotation: a telescope of the position's size, or _ for the enclosing one.
  ((many result-tele : (subterm many (Nat) sugar) (subterm many (Raw) ann) (many (Env) env) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (ExprDemand expect) demand) -> (many (Env) r) (many (List $ Entry) t) (many (List $ Mult) inner) (many (DemandBridge expect inner) bridge))
    (let ((many (Env) env3) (many (List $ Entry) ann-tele))
      (match many (is-underscore ann) _
        ((BTrue)
          (match many tele (((Env) _) ((List $ Entry) t0))
            ((None _) (values (env-error env "no telescope to reuse for `_`") $ Nil _))
            ((Some _ t)
              (match many (tele-has-meta t env) (((Env) _) ((List $ Entry) t0))
                ((BTrue) (values (env-error env "the telescope `_` would reuse still has a `_` to infer") t))
                ((BFalse) (values env t))))))
        ((BFalse)
          (match many ann (((Env) _) ((List $ Entry) t0))
            ((RList _ aitems)
              (let ((many env3) (many ids) (many t)) $ notail $ elab-tele sugar aitems one-step (subs-all aitems) env (MMExpect expect) (Nil _) (BFalse) (BTrue) $ BTrue)
              (let ((many env3b)) $ env-restore env env3)
              (let ((many (Env) env3c))
                (match many tele _
                  ((None _) env3b)
                  ((Some _ et)
                    (match many (nat-cmp (list-length _ et) $ list-length _ t) _
                      (else env3b)
                      ((CEq _ _ _) (let ((many env3c) (many ok)) $ solve-tele et t env3b $ BTrue) env3c)))))
              (let ((many env3d)) $ settle-tele t env3c)
              (values env3d $ metaless-tele t env3d)) (else (values (env-error env "malformed match annotation") $ Nil $ Entry))))))
    (match many (nat-cmp (list-length _ ann-tele) $ list-length _ expect) _
      ((CEq _ _ _) (finish-demand-tele expect demand env3 ann-tele))
      (else (finish-demand-tele expect demand (env-error env3 $ str-cat3 "match annotation has " (nat-str $ list-length _ ann-tele) $ str-cat " entries, position needs " $ nat-str $ list-length _ expect) ann-tele))))

  ((many elab-branch-body : (subterm many (Nat) sugar) (subterm many (Raw) braw) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) braw) p) (many (Env) env) (many (List $ List $ Nat) bctx) (many (List $ Mult) ex) (many (List $ Entry) ann-tele) ->
      (many (Env) r) (many (Code bctx ex) code))
    (let ((many envb) (many ress) (many code) (erased lock)) $ notail $ elab-body sugar (subterm p) body body (WHere _) env bctx ex $ Some _ ann-tele)
    (values (check-results-count envb body ann-tele ress $ Nil _) code))

  ((many elab-pattern-body : (subterm many (Nat) sugar) (subterm many (Raw) braw) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) braw) p) (many (Env) env) (many (List $ List $ Nat) bctx) (many (List $ Mult) ex) (many (List $ Entry) ann-tele) (many (Nat) saved) (many (Maybe $ Nat) alias) -> (many (Env) r) (many (Code bctx ex) code))
    (match many alias _
      ((None _)
        (let ((many env2) (many ress) (many code) (erased lock)) (notail $ elab-body sugar (subterm p) body body (WHere _) env bctx ex (Some _ ann-tele)))
        (values (check-results-count env2 body ann-tele ress (Nil _)) code))
      ((Some _ x)
        (let ((many env2) (many ress) (many code) (erased lock)) (notail $ elab-body sugar (subterm p) body body (WHere _) env (Cons _ (Cons _ x (Nil _)) bctx) ex (Some _ ann-tele)))
        (values (check-results-count env2 body ann-tele ress (Nil _)) (CLet _ many-one ex (Cons _ x (Nil _)) (PkMany _ (Nil _) x (Nil _) (PkNil _)) (var-code env bctx saved) code)))))

  ; Each branch: present, refuted automatically with (absurd C), or absurd by proof (section 12).
  ((many elab-branches : (subterm many (Nat) sugar) (subterm many (List $ Raw) branches) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Nat) tid) (many (Res) sres) (many (Mult) smult) (many (List $ MCtor) mctors) (many (List $ Entry) ann-tele) (many (List $ Mult) expect) (many (List $ RealBranch ctx expect) acc) (many (List $ Nat) seen) (many (Bool) extra) (many (Nat) saved) (many (IdMap $ Use) incoming) (many (IdMap $ Use) joined) ->
      (many (Env) r) (many (List $ RealBranch ctx expect) real) (many (List $ Nat) seen2))
    (match many branches _
      ((Nil _) (values (env-set-uses env joined) (list-rev _ acc) seen))
      ((Cons _ braw brest)
        (let ((many envl)) (env-at (env-set-uses env incoming) (raw-pos braw)))
        (match many (is-else-branch envl braw) _
          ((BTrue) (tail $ elab-branches sugar brest env ctx tid sres smult mctors ann-tele expect acc seen extra saved incoming joined))
          ((BFalse)
            (match many (branch-parts envl braw) _
              ((None _) (tail $ elab-branches sugar brest (env-back env $ env-error envl "malformed branch") ctx tid sres smult mctors ann-tele expect acc seen extra saved incoming joined))
              ((Some _ bp)
                (let ((many (Raw) craw) (many (List $ Raw) fields) (many (Bool) refuted))
                  (match many bp _
                    ((BPresent _ c fs _ _) (values c fs (BFalse)))
                    ((BRefuted _ c) (values c (Nil _) (BTrue)))
                    ((BAbsurd _ c fs _ _) (values c fs (BFalse)))))
                (let ((many env1) (many c)) (ctor-var envl craw))
                (let ((many env2) (many mk)) (marker-checked env1 tid mctors c))
                (let ((many phantom)) (not $ mult-is-many mk))
                (let ((many cell-extra)) (and extra $ not phantom))
                (let ((many ctele) (many ret)) (ctor-type env2 c))
                (let ((many (Env) env3) (many (List $ Raw) ordinary) (many (Maybe $ String) cellname))
                  (match many refuted _ ((BTrue) (values env2 fields (None _))) ((BFalse) (pattern-fields env2 c ctele fields cell-extra))))
                (let ((many unreachable)) (and phantom $ mult-is-many smult))
                (let ((many ghost)) (or unreachable $ not $ mult-is-many $ pos-mult expect))
                (let ((many mults)) (field-mults (tele-mults ctele) (match many phantom _ ((BTrue) (Erased)) ((BFalse) smult))))
                (let ((many names)) (match many refuted (((List $ Maybe $ String) _)) ((BTrue) (anon-names ctele)) ((BFalse) (raw-names ordinary))))
                (let ((many sites)) (match many refuted (((List $ Maybe $ Loc) _)) ((BTrue) (anon-sites ctele)) ((BFalse) (raw-sites ordinary env3))))
                (let ((many envb) (many fids) (many u)) (open-fields (env-set-run-pos env3 (BFalse)) ctele names sites (Some _ mults) sres c ret))
                (let ((many mfids)) (many-of mults fids))
                (let ((many bctx)) (Cons _ mfids ctx))
                (let ((many (Env) env4) (many (List $ RealBranch ctx expect) acc2))
                  (match many u _
                    ((UContra _)
                      (match many refuted _
                        ((BTrue) (values (env-discard env3 envb) acc))
                        ((BFalse) (values (env-error (env-discard env3 envb) $ str-cat3 "branch " (qname env3 c) " is refuted; write `absurd`") acc))))
                    ((UOk envb2)
                      (let ((many envb2a) (many alias)) (pattern-cell-option envb2 (match many ghost _ ((BTrue) (Erased)) ((BFalse) (Once))) sres c fids (and cell-extra $ not refuted) cellname))
                      (let ((many envb2b)) (env-set-usage-erased envb2a (or ghost $ env-usage-erased envb2a)))
                      (match many bp _
                        ((BPresent _ _ _ body p)
                          (match many unreachable _
                            ((BTrue)
                              (let ((many envb3) (many code)) (notail $ elab-pattern-body sugar braw body p envb2b bctx (all-erased expect) ann-tele saved alias))
                              (values (env-discard env3 envb3) acc))
                            ((BFalse)
                              (let ((many envb3) (many code)) (notail $ elab-pattern-body sugar braw body p envb2b bctx expect ann-tele saved alias))
                              (let ((many outer)) (env-discard env3 envb3))
                              (values (match many ghost _ ((BTrue) outer) ((BFalse) (env-set-uses outer $ env-uses envb3))) (Cons _ (MkRealBranch _ _ c mfids code) acc)))))
                        ((BRefuted _ _) (values (forced-notes env3 envb2 sres $ env-error (env-discard env3 envb2b) $ str-cat3 "branch " (qname env3 c) " is not refuted") acc))
                        ((BAbsurd _ _ _ body p)
                          (let ((erased q)) (subterm-trans p $ prove-subterm braw branches))
                          (let ((many actx)) (match many alias (((List $ List $ Nat) _)) ((None _) bctx) ((Some _ x) (Cons _ (Cons _ x (Nil _)) bctx))))
                          (let ((many envb2c) (many ress) (many code) (erased lock)) (notail $ elab-body sugar (subterm q) body body (WHere _) (env-set-usage-erased envb2b (BTrue)) actx erased-one no-tele))
                          (let ((many envb3)) (settle-empty envb2c ress lock))
                          (values (env-discard env3 envb3) acc))))))
                (tail $ elab-branches sugar brest (env-back env env4) ctx tid sres smult mctors ann-tele expect acc2 (Cons _ c seen) extra saved incoming (uses-join joined $ env-uses env4)))))))))

  ; The else branch (section 12): at most one, standing for at least one constructor, its body under no forced
  ; facts and erased throughout when none of them could run.
  ((many elab-else : (subterm many (Nat) sugar) (subterm many (List $ Raw) branches) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) ann-tele) (many (List $ Mult) expect) (many (Maybe $ Nat) first) (many (Bool) reachable) (many (Maybe $ Loc) seen-else) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) found) (many (Res) sres) (many (Mult) smult) (many (Bool) extra) (many (Nat) saved) (many (IdMap $ Use) incoming) (many (List $ MCtor) mctors) ->
      (many (Env) r) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) code))
    (match many branches _
      ((Nil _)
        (match many seen-else _
          ((Some _ _) (values env found))
          ((None _) (match many first _ ((None _) (values env found)) ((Some _ c) (values (forced-error mctors env sres smult (Cons _ c $ Nil _) $ env-error env $ str-cat3 "constructor " (qname env c) " has 0 branches") found))))))
      ((Cons _ braw brest)
        (match many (is-else-branch env braw) _
          ((BFalse) (tail $ elab-else sugar brest env ctx ann-tele expect first reachable seen-else found sres smult extra saved incoming mctors))
          ((BTrue)
            (let ((many envl)) (env-at (env-set-uses env incoming) (raw-pos braw)))
            (let ((many (Env) env2) (many (Maybe $ Code (Cons (List (Nat)) (Nil (Nat)) ctx) expect) found2))
              (match many seen-else _
                ((Some _ l)
                  (values (env-note-at (env-error envl "a match has at most one `else` branch") l "the first `else` branch") found))
                ((None _)
                  (match many first _
                    ((None _) (values (env-error envl "`else` covers no constructor") found))
                    ((Some _ _)
                      (match many (else-parts braw extra) _
                        ((None _) (values (env-error envl "malformed `else` branch") found))
                        ((Some _ parts)
                          (match many parts _
                            ((MkElseBody _ name body p)
                              (let ((many live)) (and reachable $ mult-is-many $ pos-mult expect))
                              (let ((many envb) (many alias)) (else-binder (env-set-run-pos envl (BFalse)) sres (match many live _ ((BTrue) smult) ((BFalse) (Erased))) extra name))
                              (let ((many envb1)) (env-set-usage-erased envb (or (not live) $ env-usage-erased envb)))
                              (match many reachable _
                                ((BTrue)
                                  (let ((many envb2) (many code)) (notail $ elab-pattern-body sugar braw body p envb1 (Cons _ (Nil _) ctx) expect ann-tele saved alias))
                                  (let ((many outer)) (env-discard envl envb2))
                                  (values (match many live _ ((BTrue) (env-set-uses outer $ env-uses envb2)) ((BFalse) outer)) (Some _ code)))
                                ((BFalse)
                                  (let ((many envb2) (many code)) (notail $ elab-pattern-body sugar braw body p envb1 (Cons _ (Nil _) ctx) (all-erased expect) ann-tele saved alias))
                                  (values (env-discard envl envb2) (None _)))))))))))))
            (tail $ elab-else sugar brest (env-set-uses (env-back env env2) (uses-join (env-uses env) (env-uses env2))) ctx ann-tele expect first reachable (Some _ $ env-loc envl) found2 sres smult extra saved incoming mctors))))))

  ; Arguments against a telescope, each at the position's multiplicity and checked against its entry
  ; (section 20); returns the terms innermost first and the code of the many ones in order.
  ; The arguments of an application against [tele] (SUGAR.md 6): a meta stands for each parameter; an
  ; argument written `_` is left to it, and is an error unless erased where it stands; any other is checked
  ; against its parameter and bound to its meta, as a term where [as-term] (section 5's grammar) and as an
  ; expression otherwise. [result], over the metas, is solved against [expect] eagerly, where a `_` is present,
  ; before any argument is read, and again, reporting the mismatch, when a `_` would otherwise stay unsolved
  ; at the closing paren; every `_` is solved by then or refused. Returns the argument terms innermost first.
  ((many check-args : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Succ $ Zero) st) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) tele) (many (Mult) pos) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (Bool) as-term) (many (Bool) boundary) (many (Bool) prepare) ->
      (many (Env) r) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ Code ctx many-one) codes) (many (List $ Pair (Nat) $ Code ctx many-one) pairs))
    (let-match many st (SS sn k))
    (let ((many env1) (many metas) (erased lock)) $ open-tele tele env (Some _ $ anon-names tele) (Some _ $ wild-sites _ env args) (Some _ $ all-erased $ tele-mults tele) (Nil _) $ BTrue)
    (let ((many mvars)) $ tvars-rev metas $ Nil _)
    (let ((many wilds)) $ any-wild _ args)
    (let ((many env2)) $ solve-against env1 expect result mvars wilds $ BFalse)
    (let ((many fields)) (match many result (((Bool) _)) ((ARApp _ _) (BTrue)) ((ARCall _) (BFalse))))
    (let ((many env3) (many acc) (many tys) (many codes) (many pairs)) $ notail $ check-args-go sugar root args k env2 ctx tele metas lock pos as-term prepare fields (Nil _) (Nil _) (Nil _) (Nil _))
    (let ((many (Env) env4)) $ match many (and boundary $ terms-have-meta acc env3) _ ((BTrue) (solve-against env3 expect result mvars wilds $ BTrue)) ((BFalse) env3))
    (let ((many (Env) env5)) $ match many boundary _ ((BTrue) (report-unsolved (list-rev _ acc) env4 1)) ((BFalse) env4))
    (values env5 (metaless-list acc env5) (metaless-list tys env5) codes pairs))

  ((many check-args-go : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Zero) st) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Entry) tele) (many (List $ Nat) metas) (erased (Lockstep (Entry) (Nat) tele metas) lock) (many (Mult) pos) (many (Bool) as-term) (many (Bool) prepare) (many (Bool) fields) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ Code ctx many-one) codes) (many (List $ Pair (Nat) $ Code ctx many-one) pairs) ->
      (many (Env) r) (many (List $ Term) acc2) (many (List $ Term) tys2) (many (List $ Code ctx many-one) codes2) (many (List $ Pair (Nat) $ Code ctx many-one) pairs2))
    (match many tele _
      ((Nil _)
        (match many args _
          ((Nil _) (values env acc tys (list-rev _ codes) (list-rev _ pairs)))
          ((Cons _ _ _) (values (env-error env $ str-cat "expected fewer arguments, got " $ nat-str $ list-length _ args) acc tys (list-rev _ codes) (list-rev _ pairs)))))
      ((Cons _ e rest)
        (match many args _
          ((Nil _) (values (env-error env $ str-cat "expected " $ str-cat (nat-str $ list-length _ tele) " more arguments, got 0") acc tys (list-rev _ codes) (list-rev _ pairs)))
          ((Cons _ s arest)
            (let-match erased lock (LsCons ta tb e0 m0 rest0 mrest0 lp))
            (let-match many metas (Cons c m mrest))
            (match many s _
              ((MkSub _ arg p)
                (let ((many mult)) (match many fields (((Mult) _)) ((BTrue) (field-under pos (entry-mult e))) ((BFalse) (under pos (entry-mult e)))))
                (let ((many sg)) $ sg-inst acc $ entry-sg e)
                (match many (is-underscore arg) _
                  ((BTrue)
                    (let ((many (Env) env2))
                      (match many (mult-is-many mult) _
                        ((BTrue) (env-back env $ env-error (env-at env $ raw-pos arg) $ str-cat3 "`_` stands for an erased argument, and argument " (nat-str $ Succ $ list-length _ acc) " here is not erased"))
                        ((BFalse) env)))
                    (tail $ check-args-go sugar root arest st env2 ctx rest mrest lp pos as-term prepare fields (Cons _ (TVar m) acc) (Cons _ (type-of env2 m) tys) codes pairs))
                  ((BFalse)
                    (let ((many (Env) env2) (many (Res) r) (many (Code ctx (Cons (Mult) mult (Nil (Mult)))) code))
                      (match many as-term _
                        ((BTrue)
                          (let ((many env2) (many t) (many ty)) $ notail $ elab-term sugar (subterm p) arg env (BFalse) $ Some _ $ Cons _ (entry-with-sg e sg) $ Nil _)
                          (values env2 (term-res env2 t ty) $ CErased _ $ Cons _ mult $ Nil _))
                        ((BFalse)
                          (let ((many env2) (many rs) (many code) (erased lock3)) $ notail $ elab-expr-demand sugar (subterm p) arg env ctx (Cons _ mult $ Nil _) (Some _ $ Cons _ (entry-with-sg e sg) $ Nil _) (CCPlain) (Fixed _))
                          (values env2 (first-res _ _ rs lock3) code))))
                    (let ((many env3)) $ check-sg env2 sg r)
                    (let ((many env4)) $ check env3 "value" (res-term r) $ TVar m)
                    (let ((many env5) (many r2) (many id))
                      (match many (and prepare (mult-is-many mult)) (((Env) _) ((Res) r0) ((Nat) x0))
                        ((BTrue) (prepare-or-keep _ _ env4 mult r code))
                        ((BFalse) (values env4 r 0))))
                    (let ((many (List $ Code ctx many-one) codes2) (many (List $ Pair (Nat) $ Code ctx many-one) pairs2))
                      (match many mult _
                        ((Erased) (values codes pairs))
                        (else (let ((many physical)) (runtime-one _ mult code))
                          (values (Cons _ physical codes) (Cons _ (MkPair _ _ id physical) pairs)))))
                    (tail $ check-args-go sugar root arest st env5 ctx rest mrest lp pos as-term prepare fields
                      (Cons _ (res-term r2) acc) (Cons _ (res-ty r2) tys) codes2 pairs2))))))))))

  ; A function call (section 9): a lower-level call carries a Predates proof about the callee's level, a
  ; same-level call a Subterm proof for its decreasing argument; the top level carries neither (section 24).
  ((many elab-call : (subterm many (Nat) sugar) (subterm many (List $ Raw) rawargs) (subterm many (Pair (List $ Sub rawargs) $ Ann rawargs) parts) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (Res) callee) (many (Mult) pos) (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) hcode) (many (Bool) uq) (many (Term) lv) (many (List $ Entry) params) (many (List $ Entry) rets) (many (CC) cc) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code))
    (match many parts _
      ((MkPair x _ args ann)
        (let ((many mode)) $ under pos $ match many uq (((Mult) _)) ((BTrue) (Once)) ((BFalse) (Many)))
        (def-fns msg-lvl $ (many msg-fn : -> (many (String) s)) (str-cat3 "erased function " (qshow env $ res-term callee) " called in a non-erased position"))
        (let ((many env14)) $ error-when-msg env (and (mult-is-many pos) $ not $ mult-is-many $ res-erasure callee) msg-fn)
        (let ((many env0)) $ match many (res-term callee) (((Env) _)) ((TVar x2) (use-entry env14 mode x2 $ BFalse)) (else env14))
        (let ((many env1)) $ error-when env0 (and uq $ and (mult-is-many pos) $ not $ mult-is-once $ res-erasure callee) "a shared `UniqueFn` is callable only erased")
        (let ((many env1a) (many hres) (many hid)) $ prepare-or-keep _ _ env1 mode callee hcode)
        (let ((many env2) (many acc) (many tys) (many codes) (many pairs)) $ notail $ check-args sugar rawargs args one-step (check-arity env1a params $ list-length _ args) ctx params pos tele (ARCall rets) (BFalse) (BTrue) $ BTrue)
        (let ((many arg-terms)) $ list-rev _ acc)
        (let ((many env3)) $ notail $ check-call-proof sugar rawargs ann env2 ctx callee lv params arg-terms $ list-rev _ tys)
        (let ((many rmults)) $ physical-mults rets)
        (let ((many env4) (many ids) (erased lock)) $ open-tele rets env3 (Some _ $ anon-names rets) (None _) (Some _ $ under-list (tele-mults rets) pos) acc $ BFalse)
        (let ((many (Env) env5) (many (Code ctx expect) code))
          (match many (mult-is-many pos) _
            ((BFalse) (values env4 $ CErased _ expect))
            ((BTrue)
              (let ((many inputs)) $ Cons _ (MkPair _ _ hid $ runtime-one _ pos hcode) pairs)
              (let ((many ims) (many iids) (erased ipk) (many ics) (erased icpk)) $ prepare-pack _ $ frame-pairs _ inputs)
              (let ((many ictx)) $ Cons _ iids ctx)
              (let ((many actuals)) $ prepared-codes _ pairs env4 ictx)
              (let ((many (CC) cc2))
                (match many (and (cc-eq cc $ CCPlain) $ match many (env-level env4) (((Bool) _)) ((None _) (BFalse)) ((Some _ cur) (equal-env env4 lv $ TVar cur))) _
                  ((BTrue) (CCSame (env-loc env) $ res-term callee))
                  ((BFalse) cc)))
              (let ((many call)) $ CApp ictx rmults (var-code env4 ictx hid) actuals cc2)
              (match many (lockstep-dec _ _ rmults ids) (((Env) _) ((Code ctx expect) c0))
                ((LdNo _ _ _ _) (values (env-error env4 "internal: call return count") $ CError _ expect "size"))
                ((LdYes _ _ _ _ lk)
                  (let ((many bound) (erased bpk)) $ picked-of _ rmults ids lk)
                  (let ((many env5) (many kept) (erased kpk)) $ result-codes expect rets ids acc env4 $ Cons _ bound ictx)
                  (values env5 $ CLet _ ims _ iids ipk (CValues _ ims ics icpk) $ CLet _ rmults _ bound bpk call $ CValues _ expect kept kpk))))))
        (values env5 (ress-of ids env5) code))))

  ; The call-site proof (section 9), read against the current level and enclosing subterm parameters; a bare
  ; call gets its annotation from resolve-ann first.
  ((many check-call-proof : (subterm many (Nat) sugar) (subterm many (List $ Raw) rawargs) (subterm many (Ann rawargs) ann) (many (Env) env) (many (List $ List $ Nat) ctx) (many (Res) callee) (many (Term) lv) (many (List $ Entry) params) (many (List $ Term) args) (many (List $ Term) arg-tys) -> (many (Env) r))
    (match many (env-level env) _
      ((None _)
        (match many ann _
          ((AnnNone _) env) (else (env-error env "the top level calls without proofs; drop the decrease annotation (section 24)"))))
      ((Some _ cur)
        (let ((many same)) $ equal-env env lv $ TVar cur)
        (let ((many positions)) $ subterm-indices params 0)
        (let ((many env1) (many ann2)) $ resolve-ann env _ ann callee same positions args)
        (match many ann2 _
          ((AnnNone _) env1)
          ((AnnSubterm _ i g)
            (match many same _
              ((BFalse) (env-error env1 $ annotation-kind env1 callee same))
              ((BTrue)
                (match many (index-of-nat positions i 0) _
                  ((None _) (env-error env1 $ str-cat3 "argument " (nat-str i) " is not a subterm parameter"))
                  ((Some _ kk)
                    (let ((many env2)) $ check-earlier positions env1 args 0 kk)
                    (match many (list-nth _ (env-subterms env2) kk) _
                      ((NthMiss _ _ _ _) (env-error env2 $ str-cat3 "the enclosing function has no subterm parameter at position " (nat-str kk) ""))
                      ((NthHit _ _ _ counterpart _)
                        (let ((many arg)) $ nth-term args i)
                        (let ((many (Env) env3) (many (Res) pres))
                          (match many g _
                            ((Inferred _) (mint-subterm env2 arg (nth-term arg-tys i) (TVar counterpart) $ type-of env2 counterpart))
                            ((Written _ p pp)
                              (let ((many env3) (many prs) (many pc) (erased lock)) $ notail $ elab-expr-demand sugar (subterm pp) p env2 ctx erased-one no-tele (CCPlain) (Fixed _))
                              (values env3 $ erased-res prs lock))))
                        (let ((many env4) (many s0) (many s1) (many s2) (many s3)) $ expect-proof4 env3 subterm-id pres)
                        (let ((many env5)) $ check env4 "value" s1 arg)
                        (check env5 "value" s3 $ TVar counterpart))))))))
          ((AnnPredates _ g)
            (match many same _
              ((BTrue) (env-error env1 $ annotation-kind env1 callee same))
              ((BFalse)
                (let ((many (Env) env2) (many (Res) pres))
                  (match many g _
                    ((Inferred _)
                      (def-fns msg-lvl $ (many not-variable : -> (many (Env) e) (many (Res) r))
                        (values (env-error env1 $ str-cat (qshow env1 lv) " is not a variable") $ MkRes (TErr "level") (TErr "level") (Erased) $ None _))
                      (match many (canon-env env1 lv) (((Env) _) ((Res) r0))
                        ((TVar m) (mint-predates env1 m cur))
                        ((TErr m) (values (env-error env1 m) $ MkRes (TErr m) (TErr m) (Erased) $ None _)) (else (not-variable))))
                    ((Written _ p pp)
                      (let ((many env2) (many prs) (many pc) (erased lock)) $ notail $ elab-expr-demand sugar (subterm pp) p env1 ctx erased-one no-tele (CCPlain) (Fixed _))
                      (values env2 $ erased-res prs lock))))
                (let ((many env3) (many p0) (many p1) (many p2)) $ expect-proof3 env2 predates-id pres)
                (let ((many env4)) $ check env3 "value" p2 $ TVar cur)
                (def-fns msg-lvl $ (many msg-level : -> (many (String) s)) (str-cat3 (qshow env4 $ res-term pres) " : " $ str-cat3 (qshow env4 $ res-ty pres) " does not relate the callee's level " $ qshow env4 lv))
                (error-unless-msg env4 (equal-env env4 p1 lv) msg-level)))))))))

(def-fns _ $ (many elab-expr : (many (Nat) sugar) (many (Raw) raw) (many (Env) env) (many (List $ List $ Nat) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) ->
    (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Mult) (Res) expect ress) lock))
  (elab-expr-demand sugar raw env ctx expect tele cc (Fixed _)))

; ---- The top level (section 16): statements run as they are elaborated, the final expression consumed;
; only the last form may be an expression (ASSUMPTIONS 12).

(def-fns _ $ (many pragma-of : (many (Raw) raw) -> (many (Maybe $ List $ Raw) r))
  (match many raw _
    ((RList _ items)
      (match many items _
        ((Cons _ h rest) (match many h _ ((RAtom _ w) (match many (str-eq w ";!") _ ((BTrue) (Some _ rest)) ((BFalse) (None _)))) (else (None _))))
        ((Nil _) (None _))))
    (else (None _))))

(def-fns _ $ (many pragma-warn : (many (Env) env) (many (Pos) l) (many (Raw) nraw) (many (Raw) mraw) -> (many (Env) r))
  (match many nraw _
    ((RAtom nl n)
      (match many mraw _
        ((RAtom _ msg)
          (match many (lookup env n) _
            ((None _) (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick n) ", which is not in scope"))
            ((Some _ x)
              (match many (canon-env env $ TVar x) _
                ((TVar c)
                  (match many (match many (canon-env env $ type-of env x) (((Bool) _)) ((TTyCtor _) (BTrue)) ((TValCtor _ _) (BTrue)) (else (BFalse))) _
                    ((BFalse) (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick n) ", which is neither a type constructor nor a value constructor"))
                    ((BTrue)
                      (match many (warned-find (env-warned env) c) _
                        ((Some _ w) (match many w _ ((MkWarned _ pl _) (env-note-at (env-error env $ str-cat "second `;! warn` for " $ tick n) pl "the first is here"))))
                        ((None _) (env-set-warned env $ Cons _ (MkWarned c (loc-in env l) msg) $ env-warned env))))))
                (else (env-error (env-at env nl) $ str-cat3 "`;! warn` names " (tick n) ", which is neither a type constructor nor a value constructor"))))))
        (else env)))
    (else env)))

(def-fns _ $ (many pragma : (many (Env) env) (many (Pos) l) (many (List $ Raw) words) -> (many (Env) r))
  (match many (match many words (((List $ Raw) _)) ((Cons _ _ rest) rest) ((Nil _) words)) _
    ((Nil _) (env-error env "`;! warn` needs a name and a message"))
    ((Cons _ nraw more)
      (match many more _
        ((Nil _) (env-error env "`;! warn` needs a message after the name"))
        ((Cons _ mraw _) (pragma-warn env l nraw mraw))))))

(def-fns _ $ (many sweep-regions : (many (Env) env) (subterm many (List $ Region) rs) (many (List $ Nat) used) -> (many (Env) r))
  (match many rs _
    ((Nil _) env)
    ((Cons _ r rest)
      (match many r _ ((MkRegion k n from _)
        (tail $ sweep-regions
          (match many (list-mem-bin used k) (((Env) _))
            ((BTrue) env)
            ((BFalse) (env-back env $ env-warn-at env (loc-in env from) $ str-cat3 "`;! suppress warn` for " (tick n) " silenced nothing")))
          rest used))))))

(def-fns _ $ (many end-file : (many (Env) env) -> (many (Env) r))
  (let ((many swept)) $ match many (env-errors env) (((Env) _))
    ((Nil _) (sweep-regions env (env-regions env) $ env-silenced env))
    ((Cons _ _ _) env))
  (env-set-regions (env-set-said swept $ said-without-silenced $ env-said swept) $ Nil _))

(def-fns _ $ (many run-toplevel : (subterm many (List $ Raw) items) (many (Env) env) -> (many (Env) r))
  (match many items _
    ((Nil _) env)
    ((Cons _ item rest)
      (match many (pragma-of item) _
        ((Some _ words) (tail $ run-toplevel rest $ pragma (env-at env $ raw-pos item) (raw-pos item) words))
        ((None _)
          (let ((many env2)) $ intern-literals item $ env-at env $ raw-pos item)
          (match many (is-statement env2 item) _
            ((BTrue)
              (let ((many env3) (many ctx2) (many sc)) $ elab-stmt sugar-budget item env2 (Nil _) (Many))
              (tail $ run-toplevel rest env3))
            ((BFalse)
              (match many rest _
                ((Cons _ _ _) (tail $ run-toplevel rest $ env-error env2 "only the last top-level form may be an expression"))
                ((Nil _)
                  (let ((many env3a) (many ress) (many code) (erased lock)) $ elab-expr-demand sugar-budget item env2 (Nil _) many-one no-tele (CCPlain) (FinalDemand))
                  (let ((many env3)) $ settle-res env3a $ first-res _ _ ress lock)
                  (match many (env-errors env3) _
                    ((Cons _ _ _) env3)
                    ((Nil _) (env-run-final env3 code $ res-ty $ first-res _ _ ress lock))))))))))))
