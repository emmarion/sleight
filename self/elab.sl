; self/elab.sl -- the elaborator and checker (self/README.md): head dispatch (DESIGN.md section 4), erasure
; by position (section 20), calls with their proofs, matches with refutation and else (sections 12, 17, 38),
; the seven statements with run-position statements run at once (sections 16, 34), literals, and the sugar
; expansions. It mirrors lib/elab.ml with every check ported (ASSUMPTIONS 91); an error is recorded as a
; value and elaboration goes on, so a program may be refused with more than one message.

(def-adts $ Res : -> Type
  enum
  (many MkRes : (many (Term) term) (many (Term) ty) (many (Mult) erasure) -> (Res)))

(def-fns _ $ many res-term : (many (Res) r) -> (many (Term) t) (match many r _ ((MkRes t ty e) t)))
(def-fns _ $ many res-ty : (many (Res) r) -> (many (Term) t) (match many r _ ((MkRes t ty e) ty)))
(def-fns _ $ many res-erasure : (many (Res) r) -> (many (Mult) t) (match many r _ ((MkRes t ty e) e)))

(def-fns _ $ many res-of : (many (Env) env) (many (Bin) x) -> (many (Res) r)
  (MkRes (TVar x) (type-of env x) $ entry-mult-of env x))

(def-fns _ $ many term-res : (many (Env) env) (many (Term) t) (many (Term) ty) -> (many (Res) r)
  (MkRes t ty $ Erased))

(let (many no-res) $ MkRes (TErr "no value") (TErr "no value") $ Erased)
(let (many erased-one) $ Cons _ (Erased) $ Nil _)

; One value's code at the shape the position expects, that position read from the shape; a shape of another
; count has its count reported at the expression's end.
(def-fns _ $ many single : (erased (List $ List $ Bin) ctx) (many (List $ Mult) expect) (erased (Mult) pos) (erased (PosOf expect pos) pf) (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) c) -> (many (Code ctx expect) r)
  (match many expect _
    ((Nil a) (CError _ expect "size"))
    ((Cons a m rest)
      (match many rest _
        ((Cons b m2 rest2) (CError _ expect "size"))
        ((Nil b)
          (match many m _
            ((Many) (match erased pf _ ((PoMany r0) c)))
            ((Erased) (match erased pf _ ((PoErased r0 p0 q) (match erased q _ ((PoNil) c)))))))))))

(def-fns _ $ many first-res : (erased (Mult) m) (erased (List $ Mult) ms) (many (List $ Res) rs) (erased (Lockstep (Mult) (Res) (Cons (Mult) m ms) rs) lock) -> (many (Res) r)
  (match erased lock _
    ((LsCons a b x y xs ys p) (match many rs _ ((Cons c r rest) r)))))

; What a statement leaves in the code after it (lib/elab.ml's wrap functions), and the frame it binds.
(def-adts $ StmtCode : ((List $ List $ Bin) ctx) ((List $ List $ Bin) ctx2) -> Type
  enum
  (many SNone : (erased (List $ List $ Bin) ctx) -> (StmtCode ctx ctx))
  (many SLet : (erased (List $ List $ Bin) ctx) (many (List $ Mult) ms) (many (List $ Bin) ids) (erased (Picked (Bin) ms ids) pk) (many (Code ctx ms) rhs) -> (StmtCode ctx (Cons (List (Bin)) ids ctx)))
  (many SLetRec : (erased (List $ List $ Bin) ctx) (erased (List $ Bin) gids) (many (Group gids ctx) g) -> (StmtCode ctx (Cons (List (Bin)) gids ctx)))
  (many SMatch : (erased (List $ List $ Bin) ctx) (many (Code ctx many-one) scrut) (many (Shape ctx) shape) (many (Nat) disc) (many (List $ Bin) ids) -> (StmtCode ctx (Cons (List (Bin)) ids ctx))))

(def-fns _ $ many consts-codes : (erased (List $ List $ Bin) ctx) (subterm many (List $ Pair (Bin) $ Value) cs) ->
    (many (List $ Mult) ms) (many (List $ Bin) ids) (erased (Picked (Bin) ms ids) ipk) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) cpk)
  (match many cs _
    ((Nil a) (values (Nil _) (Nil _) (PkNil _) (Nil _) (PkNil _)))
    ((Cons a p rest)
      (let (many ms) (many ids) (erased ipk) (many codes) (erased cpk) $ consts-codes ctx rest)
      (match many p _
        ((MkPair x y id v) (values (Cons _ (Many) ms) (Cons _ id ids) (PkMany _ ms id ids ipk) (Cons _ (CValue _ v) codes) (PkMany _ ms (CValue _ v) codes cpk)))))))

(def-fns _ $ many wrap-stmt : (erased (List $ List $ Bin) ctx) (erased (List $ List $ Bin) ctx2) (many (List $ Mult) ns) (many (StmtCode ctx ctx2) sc) (many (Code ctx2 ns) rest) -> (many (Code ctx ns) r)
  (match many sc _
    ((SNone c) rest)
    ((SLet c ms ids pk rhs) (CLet _ ms _ ids pk rhs rest))
    ((SLetRec c gids g) (CLetRec _ _ _ g rest))
    ((SMatch c scrut shape disc ids) (CMatch _ ns scrut shape (Cons _ (MkBranch _ _ disc ids rest) $ Nil _) $ None _))))

; ---- Raw helpers and the special-form head test

(def-fns _ $ many raw-atom : (many (Raw) r) -> (many (Maybe $ String) s)
  (match many r _ ((RAtom lq s) (Some _ s)) (else (None $ String))))

(def-fns _ $ many raw-items : (many (Raw) r) -> (many (List $ Raw) items)
  (match many r _ ((RList lq items) items) (else (Nil $ Raw))))

(def-fns _ $ many raw-name : (many (Raw) r) -> (many (String) s)
  (match many r _ ((RAtom lq s) s) (else "_")))

(def-fns _ $ many atoms-only : (subterm many (List $ Raw) rs) -> (many (Bool) r)
  (match many rs _
    ((Nil a) (BTrue))
    ((Cons a r rest) (match many (raw-atom r) _ ((None b) (BFalse)) ((Some b s) (atoms-only rest))))))

(def-fns _ $ many is-underscore : (many (Raw) r) -> (many (Bool) b)
  (match many (raw-atom r) _ ((None a) (BFalse)) ((Some a s) (str-eq s "_"))))

(def-fns _ $ many name-or-anon : (many (String) n) -> (many (Maybe $ String) r)
  (match many (str-cmp n "_") _ ((CEq eq-t eq-r eq-x) (None _)) (else (Some _ n))))

; A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4).
(def-fns _ $ many special-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ Sp) r)
  (match many (raw-atom raw) _
    ((None a) (None _))
    ((Some a n)
      (match many (lookup env n) _
        ((None b) (None _))
        ((Some b x)
          (match many (entry env x) _
            ((MkEInfo nm mult st mi me)
              (match many st _
                ((SDyn) (None _))
                ((SConst v)
                  (match many v _
                    ((VCtor c fs)
                      (match many (and (mult-is-many mult) $ equal-env env (type-of env x) special-term) _
                        ((BTrue) (sp-of-index $ ctor-index c))
                        ((BFalse) (None _)))) (else (None $ Sp))))))))))))

(def-fns _ $ many is-special : (many (Env) env) (many (Raw) raw) (many (Sp) sp) -> (many (Bool) r)
  (match many (special-of env raw) _
    ((None a) (BFalse))
    ((Some a s) (sp-eq s sp))))

(def-fns _ $ many is-mark : (many (Env) env) (many (Raw) raw) (many (MarkK) k) -> (many (Bool) r)
  (is-special env raw $ SpMark k))

(def-fns _ $ many mult-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ Mult) r)
  (match many (special-of env raw) _
    ((None a) (None _))
    ((Some a s)
      (match many (sp-eq s $ SpMark $ MkErased) _
        ((BTrue) (Some _ $ Erased))
        ((BFalse) (match many (sp-eq s $ SpMark $ MkMany) _ ((BTrue) (Some _ $ Many)) ((BFalse) (None _))))))))

(def-fns _ $ many stmt-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe $ StmtK) r)
  (match many (raw-items raw) _
    ((Nil a) (None _))
    ((Cons a h rest)
      (match many (special-of env h) _
        ((None b) (None _))
        ((Some b sp)
          (match many sp _
            ((SpStmt k) (Some _ k)) (else (None $ StmtK))))))))

(def-fns _ $ many is-statement : (many (Env) env) (many (Raw) raw) -> (many (Bool) r)
  (match many (stmt-of env raw) _ ((None a) (BFalse)) ((Some a k) (BTrue))))


(def-fns _ $ many show-t : (many (Env) env) (many (Term) t) -> (many (String) s)
  (rope-str $ show-term (canon-env env t) env))

(def-fns _ $ many show-r : (many (Raw) r) -> (many (String) s)
  (rope-str $ show-raw r))

; ---- Literals (ASSUMPTIONS 51-53, 60): numerals, characters and strings, interned per program

(def-adts $ LitKind : -> Type
  enum
  (many LName : -> (LitKind))
  (many LNumeral : -> (LitKind))
  (many LChar : -> (LitKind)))

(def-fns _ $ many classify : (many (String) s) -> (many (LitKind) k)
  (match many s _
    ((SNil) (LName))
    ((SCons c rest)
      (match many (all-digits s) _
        ((BTrue) (LNumeral))
        ((BFalse)
          (match many (and (char-is c 35) $ match many rest (((Bool) b)) ((SNil) (BFalse)) ((SCons c2 rest2) (char-is c2 92))) _
            ((BTrue) (LChar))
            ((BFalse) (LName))))))))

(def-fns _ $ many parse-nat : (subterm many (String) s) (many (Nat) acc) -> (many (Nat) n)
  (match many s _
    ((SNil) acc)
    ((SCons c rest)
      (let (many d2) $ nat-add acc acc)
      (let (many d4) $ nat-add d2 d2)
      (let (many d8) $ nat-add d4 d4)
      (parse-nat rest $ nat-add (nat-add d8 d2) $ nat-sub (char-code c) 48))))

(def-fns _ $ many is-hex : (many (Char) c) -> (many (Bool) r)
  (or (char-between c 48 57) $ or (char-between c 97 102) $ char-between c 65 70))

(def-fns _ $ many hex-digit : (many (Char) c) -> (many (Nat) d)
  (let (many n) $ char-code c)
  (match many (char-between c 48 57) _
    ((BTrue) (nat-sub n 48))
    ((BFalse)
      (match many (char-between c 97 102) _
        ((BTrue) (nat-sub n 87))
        ((BFalse) (nat-sub n 55))))))

(def-fns _ $ many times16 : (many (Nat) hi) -> (many (Nat) n)
  (let (many d2) $ nat-add hi hi)
  (let (many d4) $ nat-add d2 d2)
  (let (many d8) $ nat-add d4 d4)
  (nat-add d8 d8))

(def-fns _ $ many char-lit-body : (many (String) s) -> (many (String) body)
  (match many s _ ((SNil) (SNil)) ((SCons c rest) (match many rest _ ((SNil) (SNil)) ((SCons c2 rest2) rest2)))))

; The code of #\c, #\space, #\newline, #\tab or #\xHH, or None where the literal is malformed.
(def-fns _ $ many char-lit-code : (many (String) s) -> (many (Maybe $ Nat) n)
  (let (many body) $ char-lit-body s)
  (match many (str-cmp body "space") _
    ((CEq eq-t eq-r eq-x) (Some _ 32))
    (else
      (match many (str-cmp body "newline") _
        ((CEq eq-t eq-r eq-x) (Some _ 10))
        (else
          (match many (str-cmp body "tab") _
            ((CEq eq-t eq-r eq-x) (Some _ 9))
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
                            ((BTrue) (Some _ $ nat-add (times16 $ hex-digit h1) $ hex-digit h2))
                            ((BFalse) (None _))))))))))))))))

; What is wrong with a literal's spelling, if anything (lib/literal.ml's classify).
(def-fns _ $ many literal-error : (many (String) s) -> (many (Maybe $ String) r)
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
        ((Some a n) (None _))
        ((None a) (Some _ $ str-cat "malformed character literal " s))))))

(def-fns _ $ many prelude-id : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Bin) x)
  (match many (lookup env name) _
    ((None a) (values (env-error env $ str-cat "unbound name " name) $ BZ))
    ((Some a x) (values env x))))

(def-fns _ $ many prelude-type : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Term) t)
  (let (many env2) (many x) $ prelude-id env name)
  (values env2 $ TApp (TVar x) $ Nil _))

(def-fns _ $ many bin-of-nat : (subterm many (Nat) n) (many (Bin) acc) -> (many (Bin) b)
  (match many n _
    ((Zero) acc)
    ((Succ m) (bin-of-nat m $ bin-succ acc))))

(def-fns _ $ many bin-term : (subterm many (Bin) b) (many (Env) env) -> (many (Env) r) (many (Term) t)
  (match many b _
    ((BZ) (let (many env2) (many c) $ prelude-id env "BZ") (values env2 $ TApp (TVar c) $ Nil _))
    ((B1 b1)
      (let (many env2) (many c) $ prelude-id env "B1")
      (let (many env3) (many t) $ bin-term b1 env2)
      (values env3 $ TApp (TVar c) $ Cons _ t $ Nil _))
    ((B2 b1)
      (let (many env2) (many c) $ prelude-id env "B2")
      (let (many env3) (many t) $ bin-term b1 env2)
      (values env3 $ TApp (TVar c) $ Cons _ t $ Nil _))))

; The bijective base-2 spelling of a number as a term over the prelude's Bin (ASSUMPTIONS 50).
(def-fns _ $ many nat-bin-term : (many (Nat) n) (many (Env) env) -> (many (Env) r) (many (Term) t)
  (bin-term (bin-of-nat n $ BZ) env))

(def-fns _ $ many lit-lookup : (many (Env) env) (many (String) key) -> (many (Maybe $ Bin) r)
  (match many (nm-get _ key $ env-literals env) _ ((NHit lt ln lm x lp) (Some _ x)) ((NMiss lt ln lm lp) (None _))))

; Interns a numeral: a Const Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
(def-fns _ $ many intern-numeral : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Bin) x) (many (Bin) proof)
  (let (many n) $ parse-nat key 0)
  (let (many env1) (many nat-ty) $ prelude-type env "Nat")
  (let (many env2) (many x) $ bind env1 (None _) (Many) (SConst $ vnat n) nat-ty (None _) coercible-id)
  (let (many env2b) (many numeral) $ prelude-id env2 "Numeral")
  (let (many env2c) (many spelled) $ nat-bin-term n env2b)
  (let (many pty) $ TApp (TVar numeral) $ Cons _ spelled $ Cons _ (TVar x) $ Nil _)
  (let (many env3) (many p) $ bind env2c (None _) (Erased) (SConst $ VToken) pty (None _) coercible-id)
  (let (many env4) $ env-set-literals env3 $ nm-set _ key x $ env-literals env3)
  (values (env-push-lit (env-push-trace env4 $ TrConst x $ vnat n) x $ Some _ p) x p))

(def-fns _ $ many lit-proof : (subterm many (List $ Pair (Bin) $ Maybe $ Bin) lits) (many (Bin) x) -> (many (Maybe $ Bin) r)
  (match many lits _
    ((Nil a) (None _))
    ((Cons a p rest)
      (match many p _
        ((MkPair s t y proof) (match many (bin-cmp x y) _ ((CEq eq-t eq-r eq-x) proof) (else (lit-proof rest x))))))))

(def-fns _ $ many intern-numeral-once : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Bin) x) (many (Bin) proof)
  (match many (lit-lookup env key) _
    ((Some a x)
      (match many (lit-proof (env-lits env) x) _
        ((Some b p) (values env x p))
        ((None b) (values env x $ BZ))))
    ((None a) (intern-numeral env key))))

; Interns a numeral or character literal (ASSUMPTIONS 51, 52): a character is (MkChar (MkU8 n p)) over its
; code's numeral, transparent down to the opaque n.
(def-fns _ $ many intern : (many (Env) env) (many (String) key) (many (LitKind) kind) -> (many (Env) r)
  (match many (lit-lookup env key) _
    ((Some a x) env)
    ((None a)
      (match many (literal-error key) _
        ((Some b msg) (env-error env msg))
        ((None b)
          (match many kind _
            ((LNumeral) (let (many env2) (many x) (many p) $ intern-numeral env key) env2)
            ((LChar)
              (let (many (Nat) code) $ match many (char-lit-code key) _ ((None c) 0) ((Some c n) n))
              (let (many env2) (many num) (many np) $ intern-numeral-once env $ nat-str code)
              (let (many env2b) (many lt-id) $ prelude-id env2 "Lt")
              (let (many env2c) (many modulus) $ prelude-id env2b "u8-modulus")
              (let (many env3) (many lt) (bind env2c (None _) (Erased) (SConst $ VToken)
                                          (TApp (TVar lt-id) $ Cons _ (TVar num) $ Cons _ (TVar modulus) $ Nil _) (None _) coercible-id))
              (let (many env3b) (many mk-char) $ prelude-id env3 "MkChar")
              (let (many env3c) (many mk-u8) $ prelude-id env3b "MkU8")
              (let (many rule) $ TApp (TVar mk-char) $ Cons _ (TApp (TVar mk-u8) $ Cons _ (TVar num) $ Cons _ (TVar lt) $ Nil _) $ Nil _)
              (let (many v) $ vnat code)
              (let (many env3d) (many char-ty) $ prelude-type env3c "Char")
              (let (many env4) (many x) $ bind env3d (None _) (Many) (SConst v) char-ty (Some _ rule) coercible-id)
              (let (many env5) $ env-set-literals env4 $ nm-set _ key x $ env-literals env4)
              (env-push-lit (env-push-trace env5 $ TrConst x v) x $ Some _ np))
            ((LName) env)))))))

; Interns a string (ASSUMPTIONS 60): its characters, holding no proof.
(def-fns _ $ many intern-string : (many (Env) env) (many (String) key) -> (many (Env) r)
  (match many (lit-lookup env key) _
    ((Some a x) env)
    ((None a)
      (let (many v) $ VExt str-adt $ PStr $ match many key (((String) s)) ((SNil) (SNil)) ((SCons q rest) rest))
      (let (many env1) (many str-ty) $ prelude-type env "String")
      (let (many env2) (many x) $ bind env1 (None _) (Many) (SConst v) str-ty (None _) coercible-id)
      (let (many env3) $ env-set-literals env2 $ nm-set _ key x $ env-literals env2)
      (env-push-lit (env-push-trace env3 $ TrConst x v) x $ None _))))

(def-fns _
  (many intern-literals : (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r)
    (match many raw _
      ((RAtom lq s)
        (match many (classify s) _
          ((LName) env)
          ((LNumeral) (intern env s $ LNumeral))
          ((LChar) (intern env s $ LChar))))
      ((RString lq s) (intern-string env $ SCons #\x22 s))
      ((RList lq items) (intern-literals-list items env))))
  (many intern-literals-list : (subterm many (List $ Raw) rs) (many (Env) env) -> (many (Env) r)
    (match many rs _
      ((Nil a) env)
      ((Cons a r rest) (intern-literals-list rest $ intern-literals r env)))))

; The entry an atom names: a literal's, or the newest of that name in scope; id zero, which nothing binds,
; stands for an error already recorded.
(def-fns _ $ many var : (many (Env) env) (many (String) n) -> (many (Env) r) (many (Bin) x)
  (match many (literal-error n) _
    ((Some a msg) (values (env-error env msg) $ BZ))
    ((None a)
      (match many (classify n) _
        ((LName)
          (match many (lookup env n) _
            ((Some b x) (values env x))
            ((None b) (values (env-error env $ str-cat "unbound name " n) $ BZ)))) (else (match many (lit-lookup env n) _ ((Some b x) (values env x)) ((None b) (values (env-error env $ str-cat3 "literal " n " outside a top-level form") $ BZ))))))))

(def-fns _ $ many var-of-raw : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Bin) x)
  (match many raw _
    ((RAtom lq s) (var env s))
    ((RString lq s)
      (match many (lit-lookup env $ SCons #\x22 s) _
        ((Some a x) (values env x))
        ((None a) (values (env-error env "string literal outside a top-level form") $ BZ))))
    ((RList lq items) (values (env-error env $ str-cat3 "expected " what $ str-cat ", got " $ rope-str $ show-raw raw) $ BZ))))

; A name read through its alias (ASSUMPTIONS 78), which must resolve to a variable.
(def-fns _ $ many named : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Bin) x)
  (let (many env2) (many x) $ var-of-raw env raw what)
  (match many (canon-env env2 $ TVar x) _
    ((TVar y) (values env2 y))
    ((TBound k) (values env2 x)) ((TErr m) (values env2 x)) (else (values (env-error env2 $ str-cat3 (show-t env2 $ TVar x) " is not " what) x))))


; ---- Source telescopes (section 30), with erased proofs placing every raw they hold inside the raw list it
; was read from; the elaborator recurses on those raws.

; b is a, or a strict subterm of a.
(def-adts $ Within : ((List $ Raw) b) ((List $ Raw) a) -> Type
  enum
  (many WHere : (erased (List $ Raw) a) -> (Within a a))
  (many WIn : (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm (List $ Raw) b (List $ Raw) a) p) -> (Within b a)))

(def-fns _ $ erased in-within : (erased Type A) (erased A x) (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm A x (List $ Raw) b) p) (erased (Within b a) w) -> (erased (Subterm A x (List $ Raw) a) q)
  (match erased w _
    ((WHere y) p)
    ((WIn y z s) (subterm-trans p s))))

(def-fns _ $ erased within-in : (erased (List $ Raw) c) (erased (List $ Raw) b) (erased Type A) (erased A x) (erased (Within c b) w) (erased (Subterm (List $ Raw) b A x) p) -> (erased (Subterm (List $ Raw) c A x) q)
  (match erased w _
    ((WHere y) p)
    ((WIn y z s) (subterm-trans s p))))

(def-fns _ $ erased within-step : (erased (List $ Raw) c) (erased (List $ Raw) b) (erased (List $ Raw) a) (erased (Subterm (List $ Raw) c (List $ Raw) b) p) (erased (Within b a) w) -> (erased (Within c a) q)
  (WIn _ _ $ in-within (List $ Raw) c b a p w))

; A raw strictly inside the list root.
(def-adts $ Sub : ((List $ Raw) root) -> Type
  enum
  (many MkSub : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (Sub root)))

(def-fns _ $ many subs-of : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) -> (many (List $ Sub root) r)
  (match many items _
    ((Nil a) (Nil _))
    ((Cons a t rest)
      (Cons _ (MkSub _ t $ in-within (Raw) t items root (prove-subterm t items) w)
        $ subs-of rest _ $ within-step rest items root (prove-subterm rest items) w))))

(def-fns _ $ many subs-all : (many (List $ Raw) items) -> (many (List $ Sub items) r)
  (subs-of items _ $ WHere items))

; A hop budget: a function that hands its whole raw to another spends one step (see the elaborator block).
(def-adts $ Steps : ((Nat) n) -> Type
  enum
  (many SZ : -> (Steps $ Zero))
  (many SS : (erased (Nat) n) (many (Steps n) k) -> (Steps $ Succ n)))
(let (many one-step) $ SS _ $ SZ)
(let (many two-steps) $ SS _ one-step)

(def-adts
  (SrcEntry : ((List $ Raw) root) -> Type
    enum
    (many MkSrcEntry : (erased (List $ Raw) root) (many (Bool) sub) (many (Maybe $ Mult) mult) (many (Maybe $ SrcSg root) sg) (many (String) name) -> (SrcEntry root)))
  (SrcSg : ((List $ Raw) root) -> Type
    enum
    (many SrcTy : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (SrcSg root))
    (many SrcIs : (erased (List $ Raw) root) (many (Raw) r) (erased (Subterm (Raw) r (List $ Raw) root) p) -> (SrcSg root))))

; Whether every binder carries a type or an is clause, so a let's binders are a telescope (SUGAR.md 6).
(def-fns _ $ many all-have-sg : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) -> (many (Bool) r)
  (match many es _
    ((Nil a) (BFalse))
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry rt sub smult ssg name)
          (match many ssg _
            ((None b) (BFalse))
            ((Some b sg) (match many rest _ ((Nil c) (BTrue)) ((Cons c e2 rest2) (all-have-sg _ rest))))))))))

(def-fns _ $ many entries-of-names : (subterm many (List $ Raw) names) (many (Bool) sub) (many (Maybe $ Mult) mult) (erased (List $ Raw) root) (many (Raw) ty) (erased (Subterm (Raw) ty (List $ Raw) root) pty) -> (many (List $ SrcEntry root) r)
  (match many names _
    ((Nil a) (Nil _))
    ((Cons a n rest) (Cons _ (MkSrcEntry _ sub mult (Some _ $ SrcTy _ ty pty) $ raw-name n) $ entries-of-names rest sub mult _ ty pty))))

(def-fns _ $ many parse-entry : (many (Env) env) (many (Raw) raw) (erased (List $ Raw) root) (erased (Subterm (Raw) raw (List $ Raw) root) pr) -> (many (List $ SrcEntry root) r)
  (match many raw _
    ((RList lq items0)
      (let (erased w0) $ WIn _ _ $ subterm-trans (prove-subterm items0 raw) pr)
      (let (many (Bool) sub) (many (List $ Raw) items1) (erased (Within items1 root) w1)
        (match many items0 _
          ((Nil a) (values (BFalse) items0 w0))
          ((Cons a t rest)
            (match many (is-mark env t $ MkSubterm) (((Bool) b) ((List $ Raw) l) ((Within l root) w))
              ((BTrue) (values (BTrue) rest $ within-step _ _ _ (prove-subterm rest items0) w0))
              ((BFalse) (values (BFalse) items0 w0))))))
      (let (many (Maybe $ Mult) mult) (many (List $ Raw) items) (erased (Within items root) w2)
        (match many items1 _
          ((Nil a) (values (None _) items1 w1))
          ((Cons a t rest)
            (match many (mult-of env t) (((Maybe $ Mult) m) ((List $ Raw) l) ((Within l root) w))
              ((None b) (values (None _) items1 w1))
              ((Some b m) (values (Some _ m) rest $ within-step _ _ _ (prove-subterm rest items1) w1))))))
      (match many items _
        ((Nil a) (Nil _))
        ((Cons a first rest)
          (let (erased pf) $ in-within _ _ _ _ (prove-subterm first items) w2)
          (match many rest _
            ((Nil b) (Cons _ (MkSrcEntry _ sub mult (None _) $ raw-name first) $ Nil _))
            ((Cons b second rest2)
              (match many rest2 _
                ((Cons c third rest3)
                  (match many (and (is-mark env second $ MkIs) $ list-is-empty _ rest3) _
                    ((BTrue) (Cons _ (MkSrcEntry _ sub mult (Some _ $ SrcIs _ first pf) $ raw-name third) $ Nil _))
                    ((BFalse) (entries-of-names rest sub mult _ first pf))))
                ((Nil c) (entries-of-names rest sub mult _ first pf)))))))) (else (Nil $ SrcEntry root))))

; The items before the arrow, and those after it, which sit within the root.
(def-fns _ $ many split-arrow : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) (many (Env) env) -> (many (List $ Sub root) before) (many (List $ Raw) after) (erased (Within after root) wa)
  (match many items _
    ((Nil a) (values (Nil _) items w))
    ((Cons a t rest)
      (let (erased wr) $ within-step _ _ _ (prove-subterm rest items) w)
      (match many (is-mark env t $ MkArrow) _
        ((BTrue) (values (Nil _) rest wr))
        ((BFalse)
          (let (many before) (many after) (erased wa) $ split-arrow rest _ wr env)
          (values (Cons _ (MkSub _ t $ in-within (Raw) t items root (prove-subterm t items) w) before) after wa))))))

; Leading items that are lists headed by a multiplicity token are return entries or let binders (ASSUMPTIONS 11).
(def-fns _ $ many split-returns : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) (many (Env) env) -> (many (List $ Sub root) rets) (many (List $ Raw) body) (erased (Within body root) wb)
  (match many items _
    ((Nil a) (values (Nil _) items w))
    ((Cons a t rest)
      (let (many (Bool) headed) $ match many (raw-items t) _ ((Nil b) (BFalse)) ((Cons b m r) (match many (mult-of env m) (((Bool) x)) ((None c) (BFalse)) ((Some c mm) (BTrue)))))
      (match many headed _
        ((BFalse) (values (Nil _) items w))
        ((BTrue)
          (let (many rets) (many body) (erased wb) $ split-returns rest _ (within-step rest items root (prove-subterm rest items) w) env)
          (values (Cons _ (MkSub _ t $ in-within (Raw) t items root (prove-subterm t items) w) rets) body wb))))))

; Leading annotation tokens from the marks given, in any order; returns the flags for absurd/newtype and extern.
(def-fns _ $ many take-marks : (subterm many (List $ Raw) items) (erased (List $ Raw) root) (erased (Within items root) w) (many (Env) env) (many (MarkK) first) (many (MarkK) second) -> (many (Bool) has-first) (many (Bool) has-second) (many (List $ Raw) rest) (erased (Within rest root) wr)
  (match many items _
    ((Nil a) (values (BFalse) (BFalse) items w))
    ((Cons a t more)
      (let (erased wm) $ within-step _ _ _ (prove-subterm more items) w)
      (match many (is-mark env t first) _
        ((BTrue)
          (let (many f) (many s) (many rest) (erased wr) $ take-marks more _ wm env first second)
          (values (BTrue) s rest wr))
        ((BFalse)
          (match many (is-mark env t second) _
            ((BTrue)
              (let (many f) (many s) (many rest) (erased wr) $ take-marks more _ wm env first second)
              (values f (BTrue) rest wr))
            ((BFalse) (values (BFalse) (BFalse) items w))))))))

; ---- Constructors, Matchables and shapes (sections 17, 19, 38)

(def-fns _ $ many adt-of : (many (Env) env) (many (Bin) x) -> (many (Maybe $ Adt) r)
  (match many (entry-state env x) _
    ((SDyn) (None _))
    ((SConst v)
      (match many v _
        ((VMatchable adt) (Some _ adt)) (else (None $ Adt))))))

(def-fns _ $ many ctor-of : (many (Env) env) (many (Bin) x) -> (many (Maybe $ Ctor) r)
  (match many (entry-state env x) _
    ((SDyn) (None _))
    ((SConst v)
      (match many v _
        ((VCtorFn c) (Some _ c)) (else (None $ Ctor))))))

(def-fns _ $ many ctor-type : (many (Env) env) (many (Bin) c) -> (many (List $ Entry) tele) (many (Term) ret)
  (match many (type-of env c) _
    ((TValCtor tele ret) (values tele ret)) ((TErr m) (values (Nil _) $ TErr m)) (else (values (Nil $ Entry) $ TErr "not a constructor"))))

(def-fns _ $ many tid-of : (many (Env) env) (many (Bin) c) -> (many (Bin) tid)
  (let (many tele) (many ret) $ ctor-type env c)
  (match many (type-head env ret) _ ((None a) (BZ)) ((Some a t) t)))

(def-adts $ MatchInfo : -> Type
  enum
  (many MkMatchInfo : (many (Bin) mid) (many (Disc) disc) (many (List $ MCtor) ctors) (many (Nat) rank) -> (MatchInfo)))

(def-fns _ $ many matchable-rank : (many (Env) env) (many (Bin) x) -> (many (Nat) r)
  (match many (adt-of env x) _
    ((Some a adt) 0)
    ((None a) (match many (entry-mult-of env x) _ ((Many) 1) ((Erased) 2)))))

; Consistent Matchables for one type are interchangeable (section 19); the pick prefers one whose ADT the
; elaborator can see, then a non-erased one (ASSUMPTIONS 84, 86).
(def-fns _ $ many find-matchable-in : (subterm many (List $ Bin) objects) (many (Env) env) (many (Bin) tid) (many (Maybe $ MatchInfo) best) -> (many (Maybe $ MatchInfo) r)
  (match many objects _
    ((Nil a) best)
    ((Cons a x rest)
      (let (many (Maybe $ MatchInfo) cand)
        (match many (type-of env x) _
          ((TMatchable d t cs)
            (match many t (((Maybe $ MatchInfo) c))
              ((TVar t2)
                (match many (bin-cmp t2 tid) (((Maybe $ MatchInfo) c))
                  ((CEq eq-t eq-r eq-x) (let (many y) $ resolve env x) (Some _ $ MkMatchInfo y d cs $ matchable-rank env y))
                  (else (None _)))) (else (None $ MatchInfo)))) (else (None $ MatchInfo))))
      (let (many (Maybe $ MatchInfo) best2)
        (match many cand _
          ((None b) best)
          ((Some b info)
            (match many best (((Maybe $ MatchInfo) c))
              ((None c) cand)
              ((Some c old)
                (match many old (((Maybe $ MatchInfo) c))
                  ((MkMatchInfo m1 d1 c1 r1)
                    (match many info (((Maybe $ MatchInfo) c))
                      ((MkMatchInfo m2 d2 c2 r2) (match many (nat-lt r2 r1) (((Maybe $ MatchInfo) c)) ((BTrue) cand) ((BFalse) best)))))))))))
      (find-matchable-in rest env tid best2))))


(def-fns _ $ many find-newtype : (subterm many (List $ Bin) objects) (many (Env) env) (many (Bin) c) -> (many (Maybe $ Bin) r)
  (match many objects _
    ((Nil a) (None _))
    ((Cons a x rest)
      (match many (type-of env x) _
        ((TNewtype t)
          (match many t _
            ((TVar c2) (match many (bin-cmp c2 c) _ ((CEq eq-t eq-r eq-x) (Some _ x)) (else (find-newtype rest env c)))) (else (find-newtype rest env c)))) (else (find-newtype rest env c))))))

; The anonymous Coercible proof def-fns minted for a delegating function g (section 38).
(def-fns _ $ many find-coercible : (subterm many (List $ Bin) objects) (many (Env) env) (many (Bin) g) -> (many (Maybe $ Bin) r)
  (match many objects _
    ((Nil a) (None _))
    ((Cons a x rest)
      (let (many (Bool) hit)
        (match many (type-of env x) _
          ((TApp h args)
            (match many (list-nth _ args 1) (((Bool) b))
              ((NthMiss nt nl ni np) (BFalse))
              ((NthHit nt nl ni t np)
                (match many t (((Bool) b))
                  ((TVar g2) (and (bin-eq g2 g) $ match many (entry env x) (((Bool) b)) ((MkEInfo n m s mi me) (match many n (((Bool) b)) ((None c) (BTrue)) ((Some c nm) (BFalse)))))) (else (BFalse)))))) (else (BFalse))))
      (match many hit _
        ((BTrue) (Some _ x))
        ((BFalse) (find-coercible rest env g))))))

; A Matchable's constructors, each with its phantom marker, id and number of many fields (section 38).
(def-adts $ CShape : -> Type
  enum
  (many MkCShape : (many (Mult) m) (many (Bin) c) (many (Nat) arity) -> (CShape)))

(def-fns _ $ many shapes : (subterm many (List $ MCtor) ctors) (many (Env) env) -> (many (List $ CShape) r)
  (match many ctors _
    ((Nil a) (Nil _))
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let (many (Bin) c) $ match many t _ ((TVar x) x) (else (BZ)))
          (let (many tele) (many ret) $ ctor-type env c)
          (Cons _ (MkCShape m c $ many-count tele) $ shapes rest env))))))

(def-fns _ $ many non-phantom : (subterm many (List $ CShape) ss) -> (many (List $ CShape) r)
  (match many ss _
    ((Nil a) (Nil _))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n) (match many m _ ((Many) (Cons _ s $ non-phantom rest)) ((Erased) (non-phantom rest))))))))

(def-fns _ $ many shape-index : (subterm many (List $ CShape) ss) (many (Bin) c) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many ss _
    ((Nil a) (None _))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c2 n) (match many (bin-cmp c c2) _ ((CEq eq-t eq-r eq-x) (Some _ i)) (else (shape-index rest c $ Succ i))))))))

; A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only.
(def-fns _ $ many discriminant : (many (List $ CShape) ss) (many (Bin) c) -> (many (Nat) r)
  (match many (shape-index (non-phantom ss) c 0) _ ((None a) 0) ((Some a i) i)))

(def-fns _ $ many tagged-of : (many (Disc) disc) (many (List $ CShape) ss) -> (many (Bool) r)
  (match many disc _
    ((DUnion) (BFalse))
    ((DEnum) (nat-lt 1 $ list-length _ $ non-phantom ss))))

(def-fns _ $ many marker : (subterm many (List $ MCtor) ctors) (many (Bin) c) -> (many (Mult) m)
  (match many ctors _
    ((Nil a) (Many))
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (match many t _
            ((TVar c2) (match many (bin-cmp c c2) _ ((CEq eq-t eq-r eq-x) m) (else (marker rest c)))) (else (marker rest c))))))))



; The wrapping constructor of a type of newtype shape (section 38), if any.
(def-fns _ $ many wrappers : (subterm many (List $ CShape) ss) -> (many (List $ Bin) r)
  (match many ss _
    ((Nil a) (Nil _))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n)
          (match many (and (mult-is-many m) $ nat-eq n 1) _
            ((BTrue) (Cons _ c $ wrappers rest))
            ((BFalse) (wrappers rest))))))))

(def-fns _ $ many others-bare : (subterm many (List $ CShape) ss) (many (Bin) w) -> (many (Bool) r)
  (match many ss _
    ((Nil a) (BTrue))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n)
          (and (or (not $ mult-is-many m) $ or (bin-eq c w) $ nat-is-zero n)
            $ others-bare rest w))))))

(def-fns _ $ many wrapper : (many (Disc) disc) (many (List $ CShape) ss) -> (many (Maybe $ Bin) r)
  (match many (wrappers ss) _
    ((Nil a) (None _))
    ((Cons a w rest)
      (match many rest _
        ((Cons b w2 rest2) (None _))
        ((Nil b)
          (match many (and (not $ tagged-of disc ss) $ others-bare ss w) _
            ((BTrue) (Some _ w))
            ((BFalse) (None _))))))))

(def-fns _ $ many ctor-records : (subterm many (List $ CShape) ss) (many (Env) env) (many (Nat) index) (many (Bool) tagged) (many (Maybe $ ExtType) ext) -> (many (List $ Ctor) r)
  (match many ss _
    ((Nil a) (Nil _))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n) (Cons _ (MkCtor (name-of env c) c index n tagged ext) $ ctor-records rest env (Succ index) tagged ext))))))

; A variable in a non-erased position: a Const entry's value embedded with its entry (section 34), or a
; Dyn entry's place in the frames the code binds.
(def-fns _ $ many var-code : (many (Env) env) (many (List $ List $ Bin) ctx) (many (Bin) x) -> (many (Code ctx many-one) r)
  (match many (entry-state env x) _
    ((SConst v) (CConst _ x v))
    ((SDyn)
      (match many (mem-dec x ctx) _
        ((Some a p) (CVar _ x p))
        ((None a) (CError _ many-one $ str-cat "internal: not bound at runtime: " $ name-of env x))))))

(def-fns _ $ many matchable-code : (many (Env) env) (many (List $ List $ Bin) ctx) (many (Mult) pos) (many (Bin) x) -> (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) r)
  (match many pos _
    ((Erased) (CErased _ $ Cons _ pos $ Nil _))
    ((Many) (match many (adt-of env x) _ ((Some a adt) (CValue _ $ VMatchable adt)) ((None a) (var-code env ctx x))))))

; A match on an ADT the elaborator can see reads no Matchable at runtime (section 17).
(def-fns _ $ many match-shape : (many (Env) env) (many (List $ List $ Bin) ctx) (many (Bin) x) (many (Bool) tagged) -> (many (Shape ctx) r)
  (match many (adt-of env x) _ ((Some a adt) (ShKnown _ adt)) ((None a) (ShHeld _ (var-code env ctx x) tagged))))

(def-fns _ $ many mint : (many (Env) env) (many (Term) ty) -> (many (Env) r) (many (Res) res)
  (let (many env2) (many x) $ bind env (None _) (Erased) (SDyn) ty (None _) coercible-id)
  (values env2 $ res-of env2 x))


(def-fns _ $ many fact-of : (many (Env) env) (many (Sg) sg) -> (many (Term) ty) (many (Maybe $ Term) rule)
  (match many sg _
    ((SgTy t) (values t $ None _))
    ((SgIs t ty) (values ty $ Some _ t))))

(def-fns _ $ many proof-type : (many (Bin) ctor) (many (List $ Term) args) -> (many (Term) t)
  (TApp (TVar ctor) args))

(def-fns _ $ many nth-term : (many (List $ Term) ts) (many (Nat) i) -> (many (Term) t)
  (match many (list-nth _ ts i) _ ((NthMiss nt nl ni np) (TErr "missing argument")) ((NthHit nt nl ni t np) t)))

; Values for binders, many ones from the list in order, erased ones the token.
(def-fns _ $ many spread : (subterm many (List $ Mult) mults) (many (List $ Value) vs) -> (many (List $ Value) r) (erased (Lockstep (Mult) (Value) mults r) lock)
  (match many mults _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a m rest)
      (let (many v) (many vrest)
        (match many m (((Value) v0) ((List $ Value) vs0))
          ((Erased) (values (VToken) vs))
          ((Many) (match many vs (((Value) v0) ((List $ Value) vs0)) ((Nil b) (values (VError "missing value") vs)) ((Cons b v vrest) (values v vrest))))))
      (let (many r) (erased p) $ spread rest vrest)
      (values (Cons _ v r) (LsCons _ _ m v rest r p)))))

(def-fns _ $ many non-erased : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (List $ Bin) r)
  (match many ids _
    ((Nil a) (Nil _))
    ((Cons a x rest)
      (match many (entry-mult-of env x) _
        ((Many) (Cons _ x $ non-erased rest env))
        ((Erased) (non-erased rest env))))))

(def-fns _ $ many ress-of : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (List $ Res) r)
  (match many ids _
    ((Nil a) (Nil _))
    ((Cons a x rest) (Cons _ (res-of env x) $ ress-of rest env))))

(def-fns _ $ many tvars-rev : (subterm many (List $ Bin) ids) (many (List $ Term) acc) -> (many (List $ Term) r)
  (match many ids _
    ((Nil a) acc)
    ((Cons a x rest) (tvars-rev rest $ Cons _ (TVar x) acc))))

(def-fns _ $ many under-list : (subterm many (List $ Mult) ms) (many (Mult) pos) -> (many (List $ Mult) r)
  (match many ms _
    ((Nil a) (Nil _))
    ((Cons a m rest) (Cons _ (under pos m) $ under-list rest pos))))

(def-fns _ $ many all-erased : (subterm many (List $ Mult) ms) -> (many (List $ Mult) r)
  (match many ms _
    ((Nil a) (Nil _))
    ((Cons a m rest) (Cons _ (Erased) $ all-erased rest))))

(def-fns _ $ many states-of : (subterm many (List $ Value) vs) -> (many (List $ State) r)
  (match many vs _
    ((Nil a) (Nil _))
    ((Cons a v rest) (Cons _ (SConst v) $ states-of rest))))

; Binds fresh ids for the many returns and keeps those the position takes many (ASSUMPTIONS 39): the ids
; first, then each one's place in the frame they form, then the code referring to them there.
(def-fns _ $ many fresh-bound : (subterm many (List $ Mult) rets) (many (Env) env) -> (many (Env) r) (many (List $ Bin) bound) (erased (Picked (Bin) rets bound) bpk)
  (match many rets _
    ((Nil a) (values env (Nil _) (PkNil _)))
    ((Cons a m rest)
      (match many m _
        ((Erased)
          (let (many env2) (many bound) (erased bpk) $ fresh-bound rest env)
          (values env2 bound (PkErased _ rest bound bpk)))
        ((Many)
          (let (many env2) (many t) $ env-fresh-id env)
          (let (many env3) (many bound) (erased bpk) $ fresh-bound rest env2)
          (values env3 (Cons _ t bound) (PkMany _ rest t bound bpk)))))))

(def-fns _ $ many kept-of : (erased (List $ List $ Bin) ctx) (erased (List $ Bin) frame) (subterm many (List $ Mult) expect) (many (List $ Mult) rets) (erased (Lockstep (Mult) (Mult) expect rets) lock) (erased (List $ Bin) bound) (erased (Picked (Bin) rets bound) bpk) (many (List $ AtIn frame) ats) (erased (Lockstep (Bin) (AtIn frame) bound ats) lk) ->
    (many (List $ Code (Cons (List (Bin)) frame ctx) many-one) kept) (erased (Picked (Code (Cons (List (Bin)) frame ctx) many-one) expect kept) kpk)
  (match many expect _
    ((Nil a) (values (Nil _) (PkNil _)))
    ((Cons a m rest)
      (match erased lock _
        ((LsCons x y m0 rm0 rest0 rrest0 lp)
          (match many rets _
            ((Cons b rm rrest)
              (match many rm _
                ((Erased)
                  (match erased bpk _
                    ((PkErased tb rr bb bp)
                      (let (many kept) (erased kpk) $ kept-of ctx frame rest rrest lp _ bp ats lk)
                      (match many m _
                        ((Erased) (values kept (PkErased _ rest kept kpk)))
                        ((Many) (values (Cons _ (CError _ many-one "no value") kept) (PkMany _ rest (CError _ many-one "no value") kept kpk)))))))
                ((Many)
                  (match erased bpk _
                    ((PkMany tb rr t bb bp)
                      (match erased lk _
                        ((LsCons tc td t0 a0 bb0 arest0 lq)
                          (match many ats _
                            ((Cons c at arest)
                              (let (many kept) (erased kpk) $ kept-of ctx frame rest rrest lp _ bp arest lq)
                              (let (many (Code (Cons (List (Bin)) frame ctx) many-one) code) $ match many at _ ((MkAtIn f z p) (CVar _ z $ MHere _ _ _ p)))
                              (match many m _
                                ((Many) (values (Cons _ code kept) (PkMany _ rest code kept kpk)))
                                ((Erased) (values kept (PkErased _ rest kept kpk)))))))))))))))))))

(def-fns _ $ many projection : (erased (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (List $ Mult) rets) (erased (Lockstep (Mult) (Mult) expect rets) lock) (many (Env) env) ->
    (many (Env) r) (many (List $ Bin) bound) (erased (Picked (Bin) rets bound) bpk) (many (List $ Code (Cons (List (Bin)) bound ctx) many-one) kept) (erased (Picked (Code (Cons (List (Bin)) bound ctx) many-one) expect kept) kpk)
  (let (many env2) (many bound) (erased bpk) $ fresh-bound rets env)
  (let (many ats) (erased lk) $ at-ins bound)
  (let (many kept) (erased kpk) $ kept-of ctx bound expect rets lock bound bpk ats lk)
  (values env2 bound bpk kept kpk))

; Strips the call-site decrease annotations, (predates p) and (subterm p) (section 9).
(def-fns _ $ many strip-annotations : (subterm many (List $ Raw) args) (many (Env) env) -> (many (List $ Raw) r)
  (match many args _
    ((Nil a) (Nil _))
    ((Cons a arg rest)
      (let (many (Bool) ann)
        (match many (raw-items arg) _
          ((Nil b) (BFalse))
          ((Cons b k krest)
            (match many krest (((Bool) b))
              ((Nil c) (BFalse))
              ((Cons c p prest)
                (match many prest (((Bool) b))
                  ((Cons d q qrest) (BFalse))
                  ((Nil d) (or (is-mark env k $ MkPredates) $ is-mark env k $ MkSubterm))))))))
      (match many ann _
        ((BTrue) (strip-annotations rest env))
        ((BFalse) (Cons _ arg $ strip-annotations rest env))))))

; The delegate-marked call's callee in a body, if any (section 9); read through lets and match branches.
(def-fns _
  (many find-delegate : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) -> (many (Maybe $ Bin) r)
    (match many code _
      ((CApp c0 ms2 f args cc)
        (match many cc _
          ((CCDelegate) (match many f _ ((CVar c1 x p) (Some _ x)) ((CConst c1 x v) (Some _ x)) (else (None $ Bin)))) (else (None $ Bin))))
      ((CLet c0 ms2 ns ids pk rhs rest) (match many (find-delegate _ _ rhs) _ ((Some a x) (Some _ x)) ((None a) (find-delegate _ _ rest))))
      ((CLetRec c0 ns gids g rest) (find-delegate _ _ rest))
      ((CMatch c0 ns scrut shape branches dfl)
        (match many (find-delegate-branches _ _ branches) _
          ((Some a x) (Some _ x))
          ((None a) (match many dfl _ ((Some b d) (find-delegate _ _ d)) ((None b) (None _)))))) (else (None $ Bin))))
  (many find-delegate-branches : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) -> (many (Maybe $ Bin) r)
    (match many bs _
      ((Nil a) (None _))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c0 n0 d ids body)
            (match many (find-delegate _ _ body) _
              ((Some c x) (Some _ x))
              ((None c) (find-delegate-branches _ _ rest)))))))))

; [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
; their ids in order; names, multiplicities and states override the telescope's own when given.
; ---- Opening telescopes into scope

(def-adts $ MultsMode : -> Type
  enum
  (many MMDeclared : -> (MultsMode))
  (many MMErased : -> (MultsMode))
  (many MMExpect : (many (List $ Mult) ms) -> (MultsMode)))

(def-fns _ $ many open-tele : (subterm many (List $ Entry) tele) (many (Env) env) (many (Maybe $ List $ Maybe $ String) names) (many (Maybe $ List $ Mult) mults) (many (Maybe $ List $ State) states) (many (List $ Term) ids) (many (Bool) meta) ->
    (many (Env) r) (many (List $ Bin) fresh) (erased (Lockstep (Entry) (Bin) tele fresh) lock)
  (match many tele _
    ((Nil a) (values env (Nil _) (LsNil _ _)))
    ((Cons a e rest)
      (match many e _
        ((MkEntry ename esub emult esg)
          (let (many (Sg) sg2) $ match many esg _ ((SgTy t) (SgTy $ instantiate ids t)) ((SgIs t ty) (SgIs (instantiate ids t) $ instantiate ids ty)))
          (let (many ty) (many rule) $ fact-of env sg2)
          (let (many (Maybe $ String) name) (many (Maybe $ List $ Maybe $ String) names2)
            (match many names _
              ((None b) (values ename names))
              ((Some b ns) (match many ns (((Maybe $ String) n) ((Maybe $ List $ Maybe $ String) ns2)) ((Nil c) (values ename names)) ((Cons c n nrest) (values n $ Some _ nrest))))))
          (let (many (Mult) mult) (many (Maybe $ List $ Mult) mults2)
            (match many mults _
              ((None b) (values emult mults))
              ((Some b ms) (match many ms (((Mult) m) ((Maybe $ List $ Mult) ms2)) ((Nil c) (values emult mults)) ((Cons c m mrest) (values m $ Some _ mrest))))))
          (let (many (State) st) (many (Maybe $ List $ State) states2)
            (match many states _
              ((None b) (values (SDyn) states))
              ((Some b ss) (match many ss (((State) s) ((Maybe $ List $ State) ss2)) ((Nil c) (values (SDyn) states)) ((Cons c s srest) (values s $ Some _ srest))))))
          (let (many env2) (many x) $ bind-as env meta (BFalse) name mult st ty rule coercible-id)
          (let (many env3) (many more) (erased p) $ open-tele rest env2 names2 mults2 states2 (Cons _ (TVar x) ids) meta)
          (values env3 (Cons _ x more) (LsCons _ _ e x rest more p)))))))

(def-fns _ $ many anon-names : (subterm many (List $ Entry) tele) -> (many (List $ Maybe $ String) r)
  (match many tele _
    ((Nil a) (Nil _))
    ((Cons a e rest) (Cons _ (None _) $ anon-names rest))))

(def-fns _ $ many raw-names : (subterm many (List $ Raw) rs) -> (many (List $ Maybe $ String) r)
  (match many rs _
    ((Nil a) (Nil _))
    ((Cons a r rest) (Cons _ (name-or-anon $ raw-name r) $ raw-names rest))))

; Entering a branch forces the scrutinee equal to the constructor over its fields (section 18).

(def-fns _ $ many subterm-params : (subterm many (List $ Entry) tele) (many (List $ Bin) ids) -> (many (List $ Bin) r)
  (match many tele _
    ((Nil a) (Nil _))
    ((Cons a e rest)
      (match many ids _
        ((Nil b) (Nil _))
        ((Cons b x irest)
          (match many (entry-sub e) _
            ((BTrue) (Cons _ x $ subterm-params rest irest))
            ((BFalse) (subterm-params rest irest))))))))

; Per-value multiplicities of the binders of a let or the entries of a signature.
(def-fns _ $ many src-mults : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) -> (many (List $ Mult) r) (erased (Lockstep (SrcEntry root) (Mult) es r) lock)
  (match many es _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a e rest)
      (let (many m) $ match many e (((Mult) m0)) ((MkSrcEntry rt sub sm sg n) (match many sm (((Mult) x)) ((None b) (Many)) ((Some b mm) mm))))
      (let (many r) (erased p) $ src-mults _ rest)
      (values (Cons _ m r) (LsCons _ _ e m rest r p)))))


; ---- Checks (section 5's canonicalize-then-compare) and proofs (section 8)

; Identity after canonicalization (section 5), solving any metas either side holds (unify-env); a mismatch
; is reported only when asked to.
(def-fns _ $ many solve : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) (many (Bool) report) -> (many (Env) r) (many (Bool) ok)
  (match many (unify-env env actual expected $ BFalse) _
    ((UOk env2) (values env2 $ BTrue))
    ((UContra m)
      (match many report _
        ((BTrue) (values (env-error env $ str-cat3 what " mismatch: expected " $ str-cat3 (show-t env expected) ", got " $ show-t env actual) $ BFalse))
        ((BFalse) (values env $ BFalse))))))

(def-fns _ $ many check : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) -> (many (Env) r)
  (let (many env2) (many ok) $ solve env what actual expected $ BTrue)
  env2)

(def-fns _ $ many check-sg : (many (Env) env) (many (Sg) sg) (many (Res) r) -> (many (Env) e)
  (match many sg _
    ((SgTy ty) (check env "type" (res-ty r) ty))
    ((SgIs t t-ty) (check env "value" (res-term r) t))))

(def-fns _ $ many count-error : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r)
  (env-error env $ str-cat3 "expected " (nat-str expected) $ str-cat3 what ", got " $ nat-str got))

; A boundary (SUGAR.md 6): a term reaching one with a `_` still open is refused.
(def-fns _ $ many settle : (many (Env) env) (many (Term) t) -> (many (Env) r)
  (match many (has-meta-env env t) _
    ((BTrue) (env-error env $ str-cat "cannot infer the _ in " $ show-t env t))
    ((BFalse) env)))

(def-fns _ $ many settle-res : (many (Env) env) (many (Res) r) -> (many (Env) e)
  (settle (settle env $ res-term r) $ res-ty r))

(def-fns _ $ many settle-list : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Env) r)
  (match many ts _
    ((Nil a) env)
    ((Cons a t rest) (settle-list rest $ settle env t))))

(def-fns _ $ many metaless-ress : (subterm many (List $ Res) rs) (many (Env) env) -> (many (List $ Res) r)
  (match many rs _
    ((Nil a) (Nil _))
    ((Cons a r rest) (Cons _ (MkRes (metaless env $ res-term r) (metaless env $ res-ty r) $ res-erasure r) $ metaless-ress rest env))))

(def-fns _ $ many metaless-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (List $ Entry) r)
  (match many es _
    ((Nil a) (Nil _))
    ((Cons a e rest)
      (match many e _
        ((MkEntry n s m sg) (Cons _ (MkEntry n s m $ match many sg (((Sg) g)) ((SgTy t) (SgTy $ metaless env t)) ((SgIs t ty) (SgIs (metaless env t) $ metaless env ty))) $ metaless-tele rest env))))))

(def-fns _ $ many settle-tele : (subterm many (List $ Entry) es) (many (Env) env) -> (many (Env) r)
  (match many es _
    ((Nil a) env)
    ((Cons a e rest) (settle-tele rest $ settle env $ sg-term $ entry-sg e))))

; Results against a return telescope; [ids] as in open-tele.
(def-fns _ $ many check-results : (subterm many (List $ Entry) tele) (many (Env) env) (many (List $ Res) ress) (many (List $ Term) ids) -> (many (Env) r)
  (match many tele _
    ((Nil a) (match many ress _ ((Nil b) env) ((Cons b r rest) (env-error env "expected fewer values"))))
    ((Cons a e rest)
      (match many ress _
        ((Nil b) (env-error env "expected more values"))
        ((Cons b r rrest)
          (let (many (Sg) sg) $ match many (entry-sg e) _ ((SgTy t) (SgTy $ instantiate ids t)) ((SgIs t ty) (SgIs (instantiate ids t) $ instantiate ids ty)))
          (check-results rest (settle-res (check-sg env sg r) r) rrest $ Cons _ (res-term r) ids))))))

(def-fns _ $ many check-results-count : (many (Env) env) (many (List $ Entry) tele) (many (List $ Res) ress) (many (List $ Term) ids) -> (many (Env) r)
  (let (many n) $ list-length _ tele)
  (let (many m) $ list-length _ ress)
  (match many (nat-cmp n m) _
    ((CEq eq-t eq-r eq-x) (check-results tele env ress ids))
    (else (count-error env " values" n m))))

(def-fns _
  (many is-strict-subterm : (subterm many (Term) b) (many (Term) a) -> (many (Bool) r)
    (match many b _
      ((TApp h args) (subterm-in args a)) (else (BFalse))))
  (many subterm-in : (subterm many (List $ Term) ts) (many (Term) a) -> (many (Bool) r)
    (match many ts _
      ((Nil x) (BFalse))
      ((Cons x t rest) (or (term-eq a t) $ or (is-strict-subterm t a) $ subterm-in rest a)))))

; prove-subterm (section 8): the first, canonicalized, is a strict subtree of the second through constructor
; applications only.
(def-fns _ $ many mint-subterm : (many (Env) env) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty) -> (many (Env) r) (many (Res) res)
  (let (many ca) $ canon-env env a)
  (let (many cb) $ canon-env env b)
  (let (many (Env) env2)
    (match many (is-strict-subterm cb ca) _
      ((BTrue) env)
      ((BFalse) (env-error env $ str-cat3 (show-t env a) " is not a strict subterm of " $ show-t env b))))
  (mint env2 $ proof-type subterm-id $ Cons _ aty $ Cons _ a $ Cons _ bty $ Cons _ b $ Nil _))

; prove-predates (section 8): the variable was in scope when the level was minted (ASSUMPTIONS 13).
(def-fns _ $ many mint-predates : (many (Env) env) (many (Bin) x0) (many (Bin) lvl) -> (many (Env) r) (many (Res) res)
  (let (many (Env) env2)
    (match many (entry-minted env lvl) _
      ((BTrue) env)
      ((BFalse) (env-error env $ str-cat (name-of env lvl) " is not a level minted by def-lvl"))))
  (let (many (Bin) x)
    (match many (bin-lt x0 lvl) _
      ((BTrue) x0)
      ((BFalse) (match many (canon-env env2 $ TVar x0) (((Bin) y)) ((TVar y) y) (else x0)))))
  (let (many (Env) env3)
    (match many (bin-lt x lvl) _
      ((BTrue) env2)
      ((BFalse) (env-error env2 $ str-cat3 (name-of env2 x) " was not in scope when level " $ str-cat (name-of env2 lvl) " was minted"))))
  (mint env3 $ proof-type predates-id $ Cons _ (type-of env3 x) $ Cons _ (TVar x) $ Cons _ (TVar lvl) $ Nil _))

; The arguments of a proof of the given kind, with an error where the term is not one.
(def-fns _ $ many proof-args : (many (Env) env) (many (Bin) ctor) (many (Res) p) -> (many (Maybe $ List $ Term) r)
  (match many (canon-env env $ res-ty p) _
    ((TApp h args) (match many h _ ((TVar c) (match many (bin-cmp c ctor) _ ((CEq eq-t eq-r eq-x) (Some _ args)) (else (None _)))) (else (None $ List $ Term)))) (else (None $ List $ Term))))

(def-fns _ $ many not-a-proof : (many (Env) env) (many (Bin) ctor) (many (Res) p) -> (many (Env) r)
  (env-error env $ str-cat3 "expected a " (name-of env ctor) $ str-cat3 " proof, got " (show-t env $ res-term p) $ str-cat " : " $ show-t env $ res-ty p))

; The three arguments of a Predates proof, or the four of a Subterm or Coercible proof (section 8).
(def-fns _ $ many expect-proof3 : (many (Env) env) (many (Bin) ctor) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2)
  (let (many bad) (many e0) (many e1) (many e2) $ values (not-a-proof env ctor p) (TErr "proof") (TErr "proof") $ TErr "proof")
  (match many (proof-args env ctor p) _
    ((None a) (values bad e0 e1 e2))
    ((Some a args)
      (match many args _
        ((Nil b) (values bad e0 e1 e2))
        ((Cons b t0 r1)
          (match many r1 _
            ((Nil c) (values bad e0 e1 e2))
            ((Cons c t1 r2)
              (match many r2 _
                ((Nil d) (values bad e0 e1 e2))
                ((Cons d t2 r3) (match many r3 _ ((Nil f) (values env t0 t1 t2)) ((Cons f x y) (values bad e0 e1 e2))))))))))))

(def-fns _ $ many expect-proof4 : (many (Env) env) (many (Bin) ctor) (many (Res) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3)
  (let (many bad) (many e0) (many e1) (many e2) (many e3) $ values (not-a-proof env ctor p) (TErr "proof") (TErr "proof") (TErr "proof") $ TErr "proof")
  (match many (proof-args env ctor p) _
    ((None a) (values bad e0 e1 e2 e3))
    ((Some a args)
      (match many args _
        ((Nil b) (values bad e0 e1 e2 e3))
        ((Cons b t0 r1)
          (match many r1 _
            ((Nil c) (values bad e0 e1 e2 e3))
            ((Cons c t1 r2)
              (match many r2 _
                ((Nil d) (values bad e0 e1 e2 e3))
                ((Cons d t2 r3)
                  (match many r3 _
                    ((Nil f) (values bad e0 e1 e2 e3))
                    ((Cons f t3 r4) (match many r4 _ ((Nil g) (values env t0 t1 t2 t3)) ((Cons g x y) (values bad e0 e1 e2 e3))))))))))))))

(def-fns _ $ many sp-name-in : (subterm many (List $ SpEntry) es) (many (Sp) sp) -> (many (String) name)
  (match many es _
    ((Nil a) "?")
    ((Cons a e rest) (match many e _ ((MkSpEntry n s) (match many (sp-eq s sp) _ ((BTrue) n) ((BFalse) (sp-name-in rest sp))))))))

(def-fns _ $ many sp-name : (many (Sp) sp) -> (many (String) name)
  (sp-name-in sp-table sp))

; The candidates are ranked; several must agree (section 19), else the ambiguity is an error.
(def-fns _ $ many agree : (subterm many (List $ Bin) objects) (many (Env) env) (many (Bin) tid) (many (Term) best) -> (many (Bool) r)
  (match many objects _
    ((Nil a) (BTrue))
    ((Cons a x rest)
      (let (many ty) $ type-of env x)
      (let (many (Bool) mine)
        (match many ty _
          ((TMatchable d t cs) (match many t (((Bool) b)) ((TVar t2) (bin-eq t2 tid)) (else (BFalse)))) (else (BFalse))))
      (match many mine _
        ((BFalse) (agree rest env tid best))
        ((BTrue) (and (term-eq ty best) $ agree rest env tid best))))))

(def-fns _ $ many find-matchable : (many (Env) env) (many (Bin) tid) -> (many (Env) r) (many (Maybe $ MatchInfo) info)
  (match many (find-matchable-in (env-objects env) env tid $ None _) _
    ((None a) (values env $ None _))
    ((Some a info)
      (match many info _
        ((MkMatchInfo mid d cs rank)
          (match many (agree (env-objects env) env tid $ type-of env mid) _
            ((BTrue) (values env $ Some _ info))
            ((BFalse) (values (env-error env $ str-cat "ambiguous Matchables for " $ name-of env tid) $ Some _ info))))))))

(def-fns _ $ many phantom : (many (Env) env) (many (Bin) c) -> (many (Bool) r)
  (let (many env2) (many found) $ find-matchable env $ tid-of env c)
  (match many found _
    ((None a) (BFalse))
    ((Some a info) (match many info _ ((MkMatchInfo mid d cs rank) (match many (marker cs c) _ ((Erased) (BTrue)) ((Many) (BFalse))))))))

; A type is empty when its Matchable lists no constructor (section 37).
(def-fns _ $ many check-empty : (many (Env) env) (many (Term) ty) -> (many (Env) r)
  (let (many (Bool) empty)
    (match many (type-head env ty) _
      ((None a) (BFalse))
      ((Some a t)
        (let (many env2) (many found) $ find-matchable env t)
        (match many found (((Bool) b))
          ((None b) (BFalse))
          ((Some b info) (match many info (((Bool) b)) ((MkMatchInfo mid d cs rank) (list-is-empty _ cs))))))))
  (match many empty _
    ((BTrue) env)
    ((BFalse) (env-error env $ str-cat (show-t env ty) " is not an empty type"))))

(def-fns _ $ many mint-level : (many (Env) env) (many (Maybe $ String) name) -> (many (Env) r) (many (Bin) x)
  (let (many (State) st) $ match many (env-run-pos env) _ ((BTrue) (SConst $ VToken)) ((BFalse) (SDyn)))
  (let (many env2) (many x) $ bind env name (Erased) st level-term (None _) coercible-id)
  (values (mark-minted env2 x) x))

; Entering a branch forces the scrutinee equal to the constructor over its fields, and its type to the
; constructor's return (section 18).
(def-fns _ $ many refine : (many (Env) env) (many (Res) scrut) (many (Bin) c) (many (List $ Bin) fids) (many (Term) ret) -> (many (UnifyRes) r)
  (let (many fvars) $ tvars-rev fids $ Nil _)
  (match many (unify-env env (res-term scrut) (TApp (TVar c) $ list-rev _ fvars) $ BTrue) _
    ((UContra m) (UContra m))
    ((UOk env2) (unify-env env2 (res-ty scrut) (instantiate fvars ret) $ BTrue))))

(def-fns _ $ many disc-of-checked : (many (Env) env) (many (Raw) d) -> (many (Env) r) (many (Disc) disc)
  (match many (is-mark env d $ MkUnion) _
    ((BTrue) (values env $ DUnion))
    ((BFalse)
      (match many (is-mark env d $ MkEnum) _
        ((BTrue) (values env $ DEnum))
        ((BFalse) (values (env-error env "expected enum or union") $ DEnum))))))

; A claim on the FFI's fixed table (ASSUMPTIONS 42): each implementation backs one declaration per program.
(def-fns _ $ many claim-extern : (many (Env) env) (many (String) name) (many (Bool) known) -> (many (Env) r)
  (match many known _
    ((BFalse) (env-error env $ str-cat "no extern implementation for " name))
    ((BTrue)
      (match many (list-mem-str (env-claimed env) name) _
        ((BTrue) (env-error env $ str-cat3 "the extern implementation of " name " is already bound"))
        ((BFalse) (env-claim env name))))))


; ---- Small helpers the block's checks use

(def-fns _ $ many not-applicable : (many (Env) env) (many (Res) h) -> (many (String) s)
  (str-cat3 (show-t env $ res-term h) " : " $ str-cat (show-t env $ res-ty h) " is not applicable"))

(def-fns _ $ many cannot-apply-in-type : (many (Env) env) (many (Term) h) (many (Term) hty) -> (many (String) s)
  (str-cat3 (show-t env h) " has type " $ str-cat (show-t env hty) " and cannot be applied in a type"))

(def-fns _ $ many annotation-kind : (many (Env) env) (many (Res) callee) (many (Bool) same) -> (many (String) s)
  (match many same _
    ((BTrue) (str-cat3 "same-level call to " (show-t env $ res-term callee) " takes a (subterm p) annotation, not (predates p)"))
    ((BFalse) (str-cat3 "lower-level call to " (show-t env $ res-term callee) " takes a (predates p) annotation, not (subterm p)"))))

(def-fns _ $ many level-of-error : (many (Env) env) (many (Term) f) (many (Term) ty) -> (many (String) s)
  (str-cat3 "level-of: " (show-t env f) $ str-cat3 " : " (show-t env ty) " is not a function"))

; A constructor named in source, read through its alias, which must hold a value constructor.
(def-fns _ $ many ctor-var : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Bin) c)
  (let (many env2) (many c) $ named env raw "a constructor")
  (match many (type-of env2 c) _
    ((TValCtor tele ret) (values env2 c))
    ((TErr m) (values env2 c)) (else (values (env-error env2 $ str-cat (name-of env2 c) " is not a value constructor") c))))

(def-fns _ $ many parse-entries-checked : (erased (List $ Raw) root) (subterm many (List $ Sub root) subs) (many (Env) env) -> (many (Env) r) (many (List $ SrcEntry root) es)
  (match many subs _
    ((Nil a) (values env $ Nil _))
    ((Cons a s rest)
      (let (many (Env) env1) (many (List $ SrcEntry root) here)
        (match many s _
          ((MkSub rt r p)
            (match many (raw-atom r) (((Env) e) ((List $ SrcEntry root) l))
              ((Some b str) (values (env-error env $ str-cat "expected a telescope entry, got " str) $ Nil _))
              ((None b)
                (let (many es) $ parse-entry env r _ p)
                (match many es (((Env) e) ((List $ SrcEntry root) l))
                  ((Nil c) (values (env-error env $ str-cat "malformed telescope entry " $ show-r r) es))
                  ((Cons c x more) (values env es))))))))
      (let (many env2) (many more) $ parse-entries-checked _ rest env1)
      (let (many all) (erased cat) $ list-append _ here more)
        (values env2 all))))

(def-fns _ $ many check-binder-mults : (erased (List $ Raw) root) (subterm many (List $ SrcEntry root) es) (many (Env) env) -> (many (Env) r)
  (match many es _
    ((Nil a) env)
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry rt sub m sg n)
          (match many m _
            ((Some b mm) (check-binder-mults _ rest env))
            ((None b) (check-binder-mults _ rest $ env-error env "let binder needs a multiplicity"))))))))

(def-fns _ $ many mult-checked : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Mult) m)
  (match many (mult-of env raw) _
    ((Some a m) (values env m))
    ((None a) (values (env-error env $ str-cat "expected a multiplicity, got " $ show-r raw) $ Many))))

(def-fns _ $ many level-var-checked : (many (Env) env) (many (Term) t) -> (many (Env) r) (many (Bin) x)
  (let (many bad) $ env-error env $ str-cat (show-t env t) " is not a level")
  (match many (canon-env env t) _
    ((TVar x) (match many (equal-env env (type-of env x) level-term) _ ((BTrue) (values env x)) ((BFalse) (values bad x)))) (else (values bad $ BZ))))

(def-fns _ $ many one-arg : (many (List $ Raw) args) -> (many (Raw) r)
  (match many args _ ((Nil a) (RAtom 0 "_")) ((Cons a r rest) r)))

(def-fns _ $ many comptime-shape : (many (List $ Raw) args) -> (many (Maybe $ Pair (Raw) $ Pair (Raw) $ List $ Raw) r)
  (match many args _
    ((Nil a) (None _))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (None _))
        ((Cons b pat more)
          (match many more _
            ((Cons c y z) (None _))
            ((Nil c)
              (match many (raw-items pat) _
                ((Nil d) (None _))
                ((Cons d craw fields)
                  (match many (atoms-only fields) _
                    ((BTrue) (Some _ $ MkPair _ _ x $ MkPair _ _ craw fields))
                    ((BFalse) (None _))))))))))))

; numeral-of (ASSUMPTIONS 53): a numeral or character literal by its own spelling, never an expression.
(def-fns _ $ many numeral-of-key : (erased (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Env) env) (many (String) key) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
  (match many (lit-lookup env key) _
    ((None a) (values (env-error env $ str-cat3 "literal " key " is not in scope") (Nil _) $ CError _ expect "numeral-of"))
    ((Some a x)
      (match many (lit-proof (env-lits env) x) _
        ((None b) (values (env-error env $ str-cat key " is a string literal, which carries no Numeral proof") (Nil _) $ CError _ expect "numeral-of"))
        ((Some b p) (values env (Cons _ (res-of env p) $ Nil _) $ CErased _ expect))))))

(def-fns _ $ many numeral-of-lit : (erased (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Env) env) (many (Raw) arg) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
  (match many arg _
    ((RList lq items) (values (env-error env $ str-cat "expected a literal, got " $ show-r arg) (Nil _) $ CError _ expect "numeral-of"))
    ((RString lq s) (values (env-error env $ str-cat (show-r arg) " is a string literal, which carries no Numeral proof") (Nil _) $ CError _ expect "numeral-of"))
    ((RAtom lq s)
      (match many (literal-error s) _
        ((Some a msg) (values (env-error env msg) (Nil _) $ CError _ expect "numeral-of"))
        ((None a)
          (match many (classify s) _
            ((LName) (values (env-error env $ str-cat "numeral-of takes a literal, not " s) (Nil _) $ CError _ expect "numeral-of")) (else (numeral-of-key _ expect env s))))))))

; The number a numeral or character literal spells, if the raw is one (lib/literal.ml's classify).
(def-fns _ $ many lit-number : (many (Raw) raw) -> (many (Maybe $ Nat) n)
  (match many raw _
    ((RAtom lq s)
      (match many (literal-error s) _
        ((Some a msg) (None _))
        ((None a)
          (match many (classify s) _
            ((LName) (None _))
            ((LNumeral) (Some _ $ parse-nat s 0))
            ((LChar) (char-lit-code s)))))) (else (None $ Nat))))

; The entry holding the Nat a numeral or character literal stands for, a character's being its code's
; (lib/elab.ml's numeral_entry).
(def-fns _ $ many numeral-entry : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Maybe $ Pair (Nat) $ Bin) e)
  (match many (lit-number raw) _
    ((None a)
      (values (env-error env
                (match many raw (((String) m))
                  ((RAtom lq s) (str-cat s " is not a numeral or character literal")) (else (str-cat "expected a numeral or character literal, got " $ show-r raw))))
              $ None _))
    ((Some a z)
      (match many (lit-lookup env $ nat-str z) _
        ((None b) (values (env-error env $ str-cat3 "literal " (nat-str z) " is not in scope") $ None _))
        ((Some b x) (values env $ Some _ $ MkPair _ _ z x))))))

; A generated form is read and its literals interned in the prelude's scope, so user shadowing cannot
; reach it, and the caller's scope restored after; the level context stays the caller's throughout
; (lib/elab.ml's in_prelude).
(def-fns _ $ many generated-form : (many (Raw) g) (many (Env) env) -> (many (Env) r)
  (intern-literals g $ env-set-scope env $ env-prelude env))

(def-fns _ $ many leave-prelude : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (env-set-scope inner $ env-scope outer))

(def-fns _ $ many cc-eq : (many (CC) a) (many (CC) b) -> (many (Bool) r)
  (match many a _
    ((CCPlain) (match many b _ ((CCPlain) (BTrue)) (else (BFalse))))
    ((CCTail) (match many b _ ((CCTail) (BTrue)) (else (BFalse))))
    ((CCDelegate) (match many b _ ((CCDelegate) (BTrue)) (else (BFalse))))
    ((CCCtor) (match many b _ ((CCCtor) (BTrue)) (else (BFalse))))))

(def-fns _ $ many sg-inst : (many (List $ Term) args) (many (Sg) sg) -> (many (Sg) r)
  (match many sg _
    ((SgTy t) (SgTy $ instantiate args t))
    ((SgIs t ty) (SgIs (instantiate args t) $ instantiate args ty))))


; A branch of the raw b: present, refuted automatically with (absurd C), or absurd by proof (section 12).
(def-adts $ BranchParts : ((Raw) b) -> Type
  enum
  (many BPresent : (erased (Raw) b) (many (Raw) craw) (many (List $ Raw) fields) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) b) p) -> (BranchParts b))
  (many BRefuted : (erased (Raw) b) (many (Raw) craw) -> (BranchParts b))
  (many BAbsurd : (erased (Raw) b) (many (Raw) craw) (many (List $ Raw) fields) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) b) p) -> (BranchParts b)))

(def-fns _ $ many pattern-parts : (many (Raw) pat) -> (many (Maybe $ Pair (Raw) $ List $ Raw) r)
  (match many pat _
    ((RAtom lq s) (Some _ $ MkPair _ _ pat $ Nil _))
    ((RString lq s) (None _))
    ((RList lq items)
      (match many items _
        ((Nil a) (None _))
        ((Cons a c fs) (match many (atoms-only fs) _ ((BTrue) (Some _ $ MkPair _ _ c fs)) ((BFalse) (None _))))))))

(def-fns _ $ many branch-parts : (many (Env) env) (many (Raw) braw) -> (many (Maybe $ BranchParts braw) r)
  (match many braw _
    ((RList lq items)
      (match many items _
        ((Nil a) (None _))
        ((Cons a first more)
          (match many (is-mark env first $ MkAbsurd) _
            ((BFalse)
              (match many (pattern-parts first) _
                ((None b) (None _))
                ((Some b pp) (match many pp _ ((MkPair s t c fs) (Some _ $ BPresent _ c fs more $ prove-subterm more braw))))))
            ((BTrue)
              (match many more _
                ((Nil b) (None _))
                ((Cons b pat body)
                  (match many body _
                    ((Nil c)
                      (match many (raw-atom pat) _
                        ((Some d s) (Some _ $ BRefuted _ pat))
                        ((None d) (None _))))
                    ((Cons c x y)
                      (match many (pattern-parts pat) _
                        ((None d) (None _))
                        ((Some d pp) (match many pp _ ((MkPair s t cc fs) (Some _ $ BAbsurd _ cc fs body $ prove-subterm body braw)))))))))))))) (else (None $ BranchParts braw))))

(def-fns _ $ many marker-checked : (many (Env) env) (many (Bin) tid) (many (List $ MCtor) mctors) (many (Bin) c) -> (many (Env) r) (many (Mult) m)
  (match many (mctors-list mctors c) _
    ((BTrue) (values env $ marker mctors c))
    ((BFalse) (values (env-error env $ str-cat3 (name-of env c) " is not a constructor of " $ name-of env tid) $ Many))))

(def-fns _ $ many count-bins : (subterm many (List $ Bin) xs) (many (Bin) x) -> (many (Nat) n)
  (match many xs _
    ((Nil a) 0)
    ((Cons a y rest) (match many (bin-cmp x y) _ ((CEq eq-t eq-r eq-x) (Succ $ count-bins rest x)) (else (count-bins rest x))))))

; Every constructor of the Matchable appears exactly once (ASSUMPTIONS 21).
(def-fns _ $ many is-else-branch : (many (Env) env) (many (Raw) braw) -> (many (Bool) r)
  (match many braw _
    ((RList lq items) (match many items _ ((Nil a) (BFalse)) ((Cons a first more) (is-mark env first $ MkElse)))) (else (BFalse))))

; The unlisted constructors an else stands for: those whose forced unification does not contradict; the first of
; them, and whether any could run (section 12).
(def-fns _ $ many covered-of : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Bin) seen) (many (Res) sres) (many (Mult) smult) (many (Maybe $ Bin) first) (many (Bool) reachable) -> (many (Env) r) (many (Maybe $ Bin) first2) (many (Bool) reachable2)
  (match many mctors _
    ((Nil a) (values env first reachable))
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let (many (Bin) c) $ match many t _ ((TVar x) x) (else (BZ)))
          (match many (nat-cmp (count-bins seen c) 0) _
            (else (covered-of rest env seen sres smult first reachable))
            ((CEq eq-t eq-r eq-x)
              (let (many (Bool) phantom) $ match many m _ ((Erased) (BTrue)) ((Many) (BFalse)))
              (let (many ctele) (many ret) $ ctor-type env c)
              (let (many (List $ Mult) mults) $ match many phantom _ ((BTrue) (all-erased $ tele-mults ctele)) ((BFalse) (under-list (tele-mults ctele) smult)))
              (let (many envb) (many fids) (erased lock) $ open-tele ctele (env-set-run-pos env $ BFalse) (Some _ $ anon-names ctele) (Some _ mults) (None _) (Nil _) $ BFalse)
              (match many (refine envb sres c fids ret) _
                ((UContra msg) (covered-of rest (env-discard env envb) seen sres smult first reachable))
                ((UOk envb2)
                  (covered-of rest (env-discard env envb2) seen sres smult
                    (match many first (((Maybe $ Bin) f)) ((None b) (Some _ c)) ((Some b x) first))
                    $ or reachable $ not $ and phantom $ mult-is-many smult))))))))))

(def-fns _ $ many check-coverage : (subterm many (List $ MCtor) mctors) (many (Env) env) (many (List $ Bin) seen) -> (many (Env) r)
  (match many mctors _
    ((Nil a) env)
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let (many (Bin) c) $ match many t _ ((TVar x) x) (else (BZ)))
          (let (many n) $ count-bins seen c)
          (match many (nat-lt 1 n) _
            ((BFalse) (check-coverage rest env seen))
            ((BTrue) (check-coverage rest (env-error env $ str-cat3 "constructor " (name-of env c) $ str-cat3 " has " (nat-str n) " branches") seen))))))))


; The ids at the many positions of a list of multiplicities, in step, as the frame a binder list makes.
(def-fns _ $ many many-of : (subterm many (List $ Mult) ms) (many (List $ Bin) ids) -> (many (List $ Bin) r)
  (match many ms _
    ((Nil a) (Nil _))
    ((Cons a m rest)
      (match many ids _
        ((Nil b) (Nil _))
        ((Cons b x xrest) (match many m _ ((Many) (Cons _ x $ many-of rest xrest)) ((Erased) (many-of rest xrest))))))))

; Whether a def-fns group binds a many function; a group of erased ones leaves nothing behind (ASSUMPTIONS 77).
; ---- The elaborator proper: one block recursing on the raws it elaborates (self/README.md)

; What the statements read from their raws, holding the parts they elaborate later inside those raws.
(def-adts
  (Header : ((Raw) f) -> Type
    enum
    (many MkHeader : (erased (Raw) f) (many (String) name) (many (Mult) mult) (many (Bool) absurd) (many (Maybe $ SomeExtern) impl) (many (List $ Entry) params) (many (List $ Entry) rets) (many (List $ Raw) body) (erased (Subterm (List $ Raw) body (Raw) f) p) -> (Header f)))
  (Headers : ((List $ Raw) fns) -> Type
    enum
    (many HStop : (erased (List $ Raw) fns) -> (Headers fns))
    (many HCons : (erased (Raw) f) (erased (List $ Raw) rest) (many (Header f) h) (many (Headers rest) hs) -> (Headers $ Cons (Raw) f rest)))
  ; [gids]: the frame the group binds, its many functions' ids; an erased function is checked and leaves nothing
  ; behind (ASSUMPTIONS 77).
  (Bound : ((List $ Raw) fns) ((Headers fns) hs) ((List $ Bin) gids) -> Type
    enum
    (many BStop : (erased (List $ Raw) fns) -> (Bound fns (HStop fns) (Nil (Bin))))
    (many BMany : (erased (Raw) f) (erased (List $ Raw) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Bin) gids) (many (Bin) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Raw) f rest) (HCons f rest h hs) (Cons (Bin) x gids)))
    (many BErased : (erased (Raw) f) (erased (List $ Raw) rest) (erased (Header f) h) (erased (Headers rest) hs) (erased (List $ Bin) gids) (many (Bin) x) (many (Bound rest hs gids) more) -> (Bound (Cons (Raw) f rest) (HCons f rest h hs) gids)))
  (AdtHeader : ((Raw) f) -> Type
    enum
    (many MkAdtHeader : (erased (Raw) f) (many (String) name) (many (Disc) disc) (many (Bool) newtype) (many (Bool) extern) (many (List $ Raw) ctors) (erased (Subterm (List $ Raw) ctors (Raw) f) p) -> (AdtHeader f)))
  (AdtHeaders : ((List $ Raw) adts) -> Type
    enum
    (many AStop : (erased (List $ Raw) adts) -> (AdtHeaders adts))
    (many ACons : (erased (Raw) f) (erased (List $ Raw) rest) (many (AdtHeader f) h) (many (AdtHeaders rest) hs) -> (AdtHeaders $ Cons (Raw) f rest)))
  (Tids : ((List $ Raw) adts) ((AdtHeaders adts) hs) -> Type
    enum
    (many TStop : (erased (List $ Raw) adts) -> (Tids adts $ AStop adts))
    (many TCons : (erased (Raw) f) (erased (List $ Raw) rest) (erased (AdtHeader f) h) (erased (AdtHeaders rest) hs) (many (Bin) x) (many (Tids rest hs) more) -> (Tids (Cons (Raw) f rest) $ ACons f rest h hs)))
  (LetParts : ((List $ Raw) args) -> Type
    enum
    (many MkLetParts : (erased (List $ Raw) args) (many (List $ SrcEntry args) binders) (many (List $ Raw) rhs) (erased (Within rhs args) wr) -> (LetParts args)))
  (CtorParts : ((Raw) c) -> Type
    enum
    (many MkCtorParts : (erased (Raw) c) (many (Mult) mult) (many (String) name) (many (List $ Raw) sg) (erased (Subterm (List $ Raw) sg (Raw) c) p) -> (CtorParts c))))

(def-adts $ RealBranch : ((List $ List $ Bin) ctx) ((List $ Mult) ns) -> Type
  enum
  (many MkRealBranch : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (many (Bin) c) (many (List $ Bin) fids) (many (Code (Cons (List (Bin)) fids ctx) ns) code) -> (RealBranch ctx ns)))

(def-fns _ $ many real-branches-code : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ RealBranch ctx ns) bs) (many (List $ CShape) ss) -> (many (List $ Branch ctx ns) r)
  (match many bs _
    ((Nil a) (Nil _))
    ((Cons a b rest)
      (match many b _
        ((MkRealBranch c0 n0 c fids code) (Cons _ (MkBranch _ _ (discriminant ss c) fids code) $ real-branches-code _ _ rest ss))))))

(def-fns _ $ many bind-headers : (erased (List $ Raw) fns) (subterm many (Headers fns) hs) (many (Env) env) (many (Bin) lvl) -> (many (Env) r) (many (List $ Bin) gids) (many (Bound fns hs gids) ids)
  (match many hs _
    ((HStop z) (values env (Nil _) (BStop _)))
    ((HCons f rest h more)
      (match many h _
        ((MkHeader g name mult isabs impl params rets body p)
          (let (many env2) (many x) $ bind env (Some _ name) mult (SDyn) (TFn (TVar lvl) params rets) (None _) coercible-id)
          (let (many env3) (many gids) (many ids) $ bind-headers _ more env2 lvl)
          (match many mult _
            ((Many) (values env3 (Cons _ x gids) (BMany _ _ _ _ _ x ids)))
            ((Erased) (values env3 gids (BErased _ _ _ _ _ x ids)))))))))

(def-fns _ $ many set-fn-states : (subterm many (List $ Bin) ids) (many (List $ Value) vs) (erased (Lockstep (Bin) (Value) ids vs) lk) (many (Env) env) -> (many (Env) r)
  (match many ids _
    ((Nil a) env)
    ((Cons a id rest)
      (match erased lk _
        ((LsCons ta tb x v0 xs vs0 p) (match many vs _ ((Cons b v vrest) (set-fn-states rest vrest p $ set-state env id $ SConst v))))))))

(def-fns _ $ many set-const-states : (subterm many (List $ Pair (Bin) $ Value) cs) (many (Env) env) -> (many (Env) r)
  (match many cs _
    ((Nil a) env)
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id v) (set-const-states rest $ env-push-trace (set-state env id $ SConst v) $ TrConst id v))))))

(def-fns _ $ many ctor-values : (subterm many (List $ Ctor) cs) -> (many (List $ Pair (Bin) $ Value) r)
  (match many cs _
    ((Nil a) (Nil _))
    ((Cons a c rest) (Cons _ (MkPair _ _ (ctor-id c) $ VCtorFn c) $ ctor-values rest))))

(def-fns _ $ many mctors-of : (subterm many (List $ Pair (Mult) $ Bin) cs) -> (many (List $ MCtor) r)
  (match many cs _
    ((Nil a) (Nil _))
    ((Cons a p rest) (match many p _ ((MkPair x y m c) (Cons _ (MkMCtor m $ TVar c) $ mctors-of rest))))))

(def-fns _ $ many code-of-values : (erased (List $ List $ Bin) ctx) (many (List $ Mult) ms) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) pk) (many (Mult) pos) -> (many (Code ctx ms) r)
  (match many pos _ ((Erased) (CErased _ ms)) ((Many) (CValues _ ms codes pk))))

(def-fns _ $ many codes-missing : (erased (List $ List $ Bin) ctx) (subterm many (List $ Mult) ms) -> (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) ms codes) pk)
  (match many ms _
    ((Nil a) (values (Nil _) (PkNil _)))
    ((Cons a m rest)
      (let (many codes) (erased pk) $ codes-missing ctx rest)
      (match many m _
        ((Many) (values (Cons _ (CError _ many-one "no value") codes) (PkMany _ rest (CError _ many-one "no value") codes pk)))
        ((Erased) (values codes (PkErased _ rest codes pk)))))))

(def-fns _ $ many tail-cc : (many (Sp) sp) -> (many (CC) cc)
  (match many (sp-eq sp $ SpExpr $ ExMatch) _ (else (CCPlain))))

(def-fns _ $ many strip-quote : (many (String) s) -> (many (String) r)
  (match many s _ ((SNil) (SNil)) ((SCons c rest) rest)))


(def-fns _ $ many bin-ids-of : (subterm many (List $ Term) ts) -> (many (List $ Bin) r)
  (match many ts _
    ((Nil a) (Nil _))
    ((Cons a t rest)
      (match many t _
        ((TVar x) (Cons _ x $ bin-ids-of rest)) (else (bin-ids-of rest))))))

; Post-erasure normalization (ASSUMPTIONS 72, 74, 88; lib/elab.ml's check_marks): a let whose right-hand
; side is variables and constants is substituted away, and one whose body returns exactly what it binds is
; replaced by its right-hand side, so a marked call stands in tail position in the code that runs. A
; substitution maps every variable of the code's frames to a variable or a constant of the frames it is
; rewritten into.

(def-adts
  (Atom : ((List $ List $ Bin) ctx) -> Type
    enum
    (many AVar : (erased (List $ List $ Bin) ctx) (many (Bin) x) (many (Mem x ctx) p) -> (Atom ctx))
    (many AConst : (erased (List $ List $ Bin) ctx) (many (Bin) x) (many (Value) v) -> (Atom ctx)))
  (Ren : ((List $ List $ Bin) from) ((List $ List $ Bin) ctx) -> Type
    enum
    (many RNil : (erased (List $ List $ Bin) ctx) -> (Ren (Nil (List (Bin))) ctx))
    (many RFrame : (erased (List $ Bin) f) (erased (List $ List $ Bin) rest) (erased (List $ List $ Bin) ctx) (many (List $ Atom ctx) atoms) (erased (Lockstep (Bin) (Atom ctx) f atoms) lk) (many (Ren rest ctx) r) -> (Ren (Cons (List (Bin)) f rest) ctx))))

(def-fns _ $ many atom-code : (erased (List $ List $ Bin) ctx) (many (Atom ctx) a) -> (many (Code ctx many-one) r)
  (match many a _ ((AVar c x p) (CVar _ x p)) ((AConst c x v) (CConst _ x v))))

(def-fns _ $ many atom-there : (erased (List $ List $ Bin) ctx) (erased (List $ Bin) f) (many (Atom ctx) a) -> (many (Atom (Cons (List (Bin)) f ctx)) r)
  (match many a _ ((AVar c x p) (AVar _ x $ MThere _ _ _ p)) ((AConst c x v) (AConst _ x v))))

(def-fns _ $ many atoms-there : (erased (List $ List $ Bin) ctx) (erased (List $ Bin) f) (subterm many (List $ Atom ctx) as) -> (many (List $ Atom (Cons (List (Bin)) f ctx)) r) (erased (Lockstep (Atom ctx) (Atom (Cons (List (Bin)) f ctx)) as r) lk)
  (match many as _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (let (many r) (erased lk) $ atoms-there ctx f rest)
      (let (many y) $ atom-there _ f x)
      (values (Cons _ y r) (LsCons _ _ x y rest r lk)))))

(def-fns _ $ many self-atoms : (erased (List $ List $ Bin) ctx) (erased (List $ Bin) f) (subterm many (List $ AtIn f) ats) -> (many (List $ Atom (Cons (List (Bin)) f ctx)) r) (erased (Lockstep (AtIn f) (Atom (Cons (List (Bin)) f ctx)) ats r) lk)
  (match many ats _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a at rest)
      (let (many r) (erased lk) $ self-atoms ctx f rest)
      (let (many (Atom (Cons (List (Bin)) f ctx)) atom) $ match many at _ ((MkAtIn g x p) (AVar _ x $ MHere _ _ _ p)))
      (values (Cons _ atom r) (LsCons _ _ at atom rest r lk)))))

(def-fns _ $ many ren-under : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (erased (List $ Bin) f) (subterm many (Ren from ctx) ren) -> (many (Ren from (Cons (List (Bin)) f ctx)) r)
  (match many ren _
    ((RNil c) (RNil _))
    ((RFrame g rest c atoms lk r)
      (let (many atoms2) (erased lk2) $ atoms-there _ f atoms)
      (RFrame _ _ _ atoms2 (lockstep-trans _ _ _ _ _ _ lk lk2) $ ren-under _ _ f r))))

(def-fns _ $ many ren-weaken : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Bin) f) (many (Ren from ctx) ren) -> (many (Ren (Cons (List (Bin)) f from) (Cons (List (Bin)) f ctx)) r)
  (let (many ats) (erased lk) $ at-ins f)
  (let (many atoms) (erased lk2) $ self-atoms ctx _ ats)
  (RFrame _ _ _ atoms (lockstep-trans _ _ _ _ _ _ lk lk2) $ ren-under _ _ f ren))

(def-fns _ $ many ren-id : (subterm many (List $ List $ Bin) ctx) -> (many (Ren ctx ctx) r)
  (match many ctx _
    ((Nil a) (RNil _))
    ((Cons a f rest) (ren-weaken _ _ f $ ren-id rest))))

(def-fns _ $ many ren-get : (erased (Bin) x) (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (subterm many (Mem x from) p) (many (Ren from ctx) ren) -> (many (Atom ctx) r)
  (match many p _
    ((MHere y f c q) (match many ren _ ((RFrame g rest c2 atoms lk r) (let (many a) (erased sq) $ at-get _ _ _ q atoms lk) a)))
    ((MThere y f c q) (match many ren _ ((RFrame g rest c2 atoms lk r) (ren-get _ _ _ q r))))))

; The atoms a let binds, if its right-hand side is nothing but variables and constants.
(def-fns _ $ many atoms-of : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Atom ctx) r)
  (match many cs _
    ((Nil a) (Some _ $ Nil _))
    ((Cons a c rest)
      (match many (atoms-of _ rest) _
        ((None b) (None _))
        ((Some b more)
          (match many c _
            ((CVar c0 x p) (Some _ $ Cons _ (AVar _ x p) more))
            ((CConst c0 x v) (Some _ $ Cons _ (AConst _ x v) more)) (else (None $ List $ Atom ctx))))))))

(def-fns _ $ many rhs-atoms : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (many (Code ctx ms) c) -> (many (Maybe $ List $ Atom ctx) r)
  (match many c _
    ((CVar c0 x p) (Some _ $ Cons _ (AVar _ x p) $ Nil _))
    ((CConst c0 x v) (Some _ $ Cons _ (AConst _ x v) $ Nil _))
    ((CErased c0 ms2) (Some _ $ Nil _))
    ((CValues c0 ms2 cs pk) (atoms-of _ cs)) (else (None $ List $ Atom ctx))))

(def-fns _ $ many vars-of : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Maybe $ List $ Bin) r)
  (match many cs _
    ((Nil a) (Some _ $ Nil _))
    ((Cons a c rest)
      (match many c _
        ((CVar c0 x p)
          (match many (vars-of _ rest) _
            ((None b) (None _))
            ((Some b xs) (Some _ $ Cons _ x xs)))) (else (None $ List $ Bin))))))

(def-fns _ $ many bins-eq : (subterm many (List $ Bin) as) (many (List $ Bin) bs) -> (many (Bool) r)
  (match many as _
    ((Nil a) (list-is-empty _ bs))
    ((Cons a x rest) (match many bs _ ((Nil b) (BFalse)) ((Cons b y brest) (and (bin-eq x y) $ bins-eq rest brest))))))

; Whether a body returns exactly the let's ids, in order, with the two erasure lists then agreeing on their many entries.
(def-fns _ $ many returns-same : (erased (List $ List $ Bin) ctx) (subterm many (List $ Mult) ms) (many (List $ Bin) ids) (erased (Picked (Bin) ms ids) pk) (subterm many (List $ Mult) ns) (many (List $ Code ctx many-one) cs) (erased (Picked (Code ctx many-one) ns cs) qk) -> (many (Maybe $ ManySame ms ns) r)
  (match many ms _
    ((Nil a)
      (match many ns _
        ((Nil b) (Some _ $ MsNil))
        ((Cons b n nrest)
          (match many n _
            ((Many) (None _))
            ((Erased)
              (match erased qk _
                ((PkErased t ns2 cs2 q2)
                  (match many (returns-same _ ms ids pk nrest cs q2) _
                    ((Some c p) (Some _ $ MsErasedR _ _ p))
                    ((None c) (None _))))))))))
    ((Cons a m mrest)
      (match many m _
        ((Erased)
          (match erased pk _
            ((PkErased t ms2 ids2 p2)
              (match many (returns-same _ mrest ids p2 ns cs qk) _
                ((Some c p) (Some _ $ MsErasedL _ _ p))
                ((None c) (None _))))))
        ((Many)
          (match erased pk _
            ((PkMany t ms2 x ids2 p2)
              (match many ids _
                ((Cons b x2 idrest)
                  (match many ns _
                    ((Nil c) (None _))
                    ((Cons c n nrest)
                      (match many n _
                        ((Erased)
                          (match erased qk _
                            ((PkErased t2 ns2 cs2 q2)
                              (match many (returns-same _ ms ids pk nrest cs q2) _
                                ((Some d p) (Some _ $ MsErasedR _ _ p))
                                ((None d) (None _))))))
                        ((Many)
                          (match erased qk _
                            ((PkMany t2 ns2 c0 cs2 q2)
                              (match many cs _
                                ((Cons d c crest)
                                  (match many c _
                                    ((CVar c0 y p0)
                                      (match many (bin-cmp x2 y) _
                                        ((CEq eq-t eq-r eq-x)
                                          (match many (returns-same _ mrest idrest p2 nrest crest q2) _
                                            ((Some e p) (Some _ $ MsMany _ _ p))
                                            ((None e) (None _))))
                                        (else (None _))))
                                    (else (None _))))))))))))))))))))

; Dropping a frame nothing mentions (lib/elab.ml's constant let): the code rebuilt one frame shorter, or None
; where some variable sits in that frame.
(def-adts
  (Drop : ((List $ List $ Bin) from) ((List $ List $ Bin) ctx) -> Type
    enum
    (many DHere : (erased (List $ Bin) f) (erased (List $ List $ Bin) ctx) -> (Drop (Cons (List (Bin)) f ctx) ctx))
    (many DUnder : (erased (List $ Bin) g) (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (Drop from ctx) d) -> (Drop (Cons (List (Bin)) g from) (Cons (List (Bin)) g ctx))))
  (Kept : (Type A) (Type B) ((List A) xs) -> Type
    enum
    (many KNo : (erased Type A) (erased Type B) (erased (List A) xs) -> (Kept A B xs))
    (many KYes : (erased Type A) (erased Type B) (erased (List A) xs) (many (List B) ys) (erased (Lockstep A B xs ys) lk) -> (Kept A B xs))))

(def-fns _ $ many mem-drop : (erased (Bin) x) (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (subterm many (Mem x from) p) (many (Drop from ctx) d) -> (many (Maybe $ Mem x ctx) r)
  (match many d _
    ((DHere f c) (match many p _ ((MHere y f2 c2 at) (None _)) ((MThere y f2 c2 q) (Some _ q))))
    ((DUnder g fr c d2)
      (match many p _
        ((MHere y f2 c2 at) (Some _ $ MHere _ _ _ at))
        ((MThere y f2 c2 q) (match many (mem-drop _ _ _ q d2) _ ((Some a q2) (Some _ $ MThere _ _ _ q2)) ((None a) (None _))))))))

(def-fns _
  (many strengthen : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code from ms) c) (many (Drop from ctx) d) -> (many (Maybe $ Code ctx ms) r)
    (match many c _
      ((CVar c0 x p) (match many (mem-drop _ _ _ p d) _ ((Some a q) (Some _ $ CVar _ x q)) ((None a) (None _))))
      ((CConst c0 x v) (Some _ $ CConst _ x v))
      ((CValue c0 v) (Some _ $ CValue _ v))
      ((CErased c0 ms2) (Some _ $ CErased _ ms2))
      ((CValues c0 ms2 cs pk)
        (match many (strengthen-list _ _ cs d) _
          ((KNo a b e) (None _))
          ((KYes a b e cs2 lk) (Some _ $ CValues _ ms2 cs2 $ picked-along _ _ _ _ _ pk lk))))
      ((CApp c0 ms2 f args cc)
        (match many (strengthen _ _ _ f d) _
          ((None a) (None _))
          ((Some a f2)
            (match many (strengthen-list _ _ args d) _
              ((KNo x y z) (None _))
              ((KYes x y z args2 lk) (Some _ $ CApp _ ms2 f2 args2 cc))))))
      ((CLet c0 ms2 ns ids pk rhs rest)
        (match many (strengthen _ _ _ rhs d) _
          ((None a) (None _))
          ((Some a rhs2)
            (match many (strengthen _ _ _ rest $ DUnder _ _ _ d) _
              ((None b) (None _))
              ((Some b rest2) (Some _ $ CLet _ ms2 _ ids pk rhs2 rest2))))))
      ((CLetRec c0 ns gids g rest)
        (match many g _
          ((MkGroup c1 ids fns lk)
            (match many (strengthen-fns _ _ ids fns d) _
              ((KNo x y z) (None _))
              ((KYes x y z fns2 lk2)
                (match many (strengthen _ _ _ rest $ DUnder _ _ _ d) _
                  ((None b) (None _))
                  ((Some b rest2) (Some _ $ CLetRec _ _ _ (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2) rest2))))))))
      ((CMatch c0 ns scrut shape bs dfl)
        (match many (strengthen _ _ _ scrut d) _
          ((None a) (None _))
          ((Some a scrut2)
            (let (many (Maybe $ Shape ctx) shape2)
              (match many shape _
                ((ShKnown c1 adt) (Some _ $ ShKnown _ adt))
                ((ShNone c1) (Some _ $ ShNone _))
                ((ShHeld c1 mc tags) (match many (strengthen _ _ _ mc d) _ ((None b) (None _)) ((Some b mc2) (Some _ $ ShHeld _ mc2 tags))))))
            (match many shape2 _
              ((None b) (None _))
              ((Some b sh)
                (match many (strengthen-branches _ _ ns bs d) _
                  ((None e) (None _))
                  ((Some e bs2)
                    (match many dfl _
                      ((None f) (Some _ $ CMatch _ ns scrut2 sh bs2 $ None _))
                      ((Some f dd)
                        (match many (strengthen _ _ _ dd $ DUnder _ _ _ d) _
                          ((None h) (None _))
                          ((Some h dd2) (Some _ $ CMatch _ ns scrut2 sh bs2 $ Some _ dd2))))))))))))
      ((CAbsurd c0 ms2) (Some _ $ CAbsurd _ ms2))
      ((CError c0 ms2 m) (Some _ $ CError _ ms2 m))))
  (many strengthen-list : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code from many-one) cs) (many (Drop from ctx) d) -> (many (Kept (Code from many-one) (Code ctx many-one) cs) r)
    (match many cs _
      ((Nil a) (KYes _ _ _ (Nil _) (LsNil _ _)))
      ((Cons a c rest)
        (match many (strengthen _ _ _ c d) _
          ((None b) (KNo _ _ _))
          ((Some b c2)
            (match many (strengthen-list _ _ rest d) _
              ((KNo x y z) (KNo _ _ _))
              ((KYes x y z r lk) (KYes _ _ _ (Cons _ c2 r) (LsCons _ _ c c2 rest r lk)))))))))
  (many strengthen-fns : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Bin) gids) (subterm many (List $ Pair (Bin) $ Func gids from) fns) (many (Drop from ctx) d) -> (many (Kept (Pair (Bin) $ Func gids from) (Pair (Bin) $ Func gids ctx) fns) r)
    (match many fns _
      ((Nil a) (KYes _ _ _ (Nil _) (LsNil _ _)))
      ((Cons a p rest)
        (match many p _
          ((MkPair s t id fn)
            (match many fn _
              ((MkFunc g c rets n i ps body impl top)
                (match many (strengthen _ _ _ body $ DUnder _ _ _ $ DUnder _ _ _ d) _
                  ((None b) (KNo _ _ _))
                  ((Some b body2)
                    (match many (strengthen-fns _ _ gids rest d) _
                      ((KNo x y z) (KNo _ _ _))
                      ((KYes x y z r lk)
                        (let (many p2) $ MkPair _ _ id $ MkFunc _ _ rets n i ps body2 impl top)
                        (KYes _ _ _ (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))))))))))))
  (many strengthen-branches : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch from ns) bs) (many (Drop from ctx) d) -> (many (Maybe $ List $ Branch ctx ns) r)
    (match many bs _
      ((Nil a) (Some _ $ Nil _))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c0 n0 dsc ids body)
            (match many (strengthen _ _ _ body $ DUnder _ _ _ d) _
              ((None x) (None _))
              ((Some x body2)
                (match many (strengthen-branches _ _ ns rest d) _
                  ((None y) (None _))
                  ((Some y r) (Some _ $ Cons _ (MkBranch _ _ dsc ids body2) r)))))))))))

; A let's right-hand side of values embedded by elaboration alone, as lib/elab.ml's constant.
(def-fns _ $ many all-values : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r)
  (match many cs _
    ((Nil a) (BTrue))
    ((Cons a c rest) (match many c _ ((CValue c0 v) (all-values _ rest)) (else (BFalse))))))

(def-fns _ $ many constant-rhs : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (many (Code ctx ms) c) -> (many (Bool) r)
  (match many c _ ((CValues c0 ms2 cs pk) (all-values _ cs)) (else (BFalse))))

(def-fns _
  (many norm : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Mult) ms) (subterm many (Code from ms) c) (many (Ren from ctx) ren) -> (many (Code ctx ms) r)
    (match many c _
      ((CVar c0 x p) (atom-code _ $ ren-get _ _ _ p ren))
      ((CConst c0 x v) (CConst _ x v))
      ((CValue c0 v) (CValue _ v))
      ((CErased c0 ms2) (CErased _ ms2))
      ((CValues c0 ms2 cs pk)
        (let (many cs2) (erased lk) $ norm-list _ _ cs ren)
        (CValues _ ms2 cs2 $ picked-along _ _ _ _ _ pk lk))
      ((CApp c0 ms2 f as cc)
        (let (many as2) (erased lk) $ norm-list _ _ as ren)
        (CApp _ ms2 (norm _ _ many-one f ren) as2 cc))
      ((CLet c0 ms2 ns ids pk rhs rest)
        (let (many rhs2) $ norm _ _ ms2 rhs ren)
        (let (many (Maybe $ Ren (Cons (List (Bin)) ids from) ctx) dropped)
          (match many (rhs-atoms _ _ rhs2) _
            ((None a) (None _))
            ((Some a atoms)
              (match many (lockstep-dec _ _ ids atoms) _
                ((LdYes t1 t2 t3 t4 lk) (Some _ $ RFrame _ _ _ atoms lk ren))
                ((LdNo t1 t2 t3 t4) (None _))))))
        (match many dropped _
          ((Some a ren2) (norm _ _ ms rest ren2))
          ((None a)
            (let (many rest2) $ norm _ _ ms rest $ ren-weaken _ _ ids ren)
            (let (many (Maybe $ ManySame ms2 ms) same)
              (match many rest2 _
                ((CVar c1 y p) (returns-same _ ms2 ids pk many-one (Cons _ (CVar _ y p) $ Nil _) $ PkMany _ (Nil _) (CVar _ y p) (Nil _) $ PkNil _))
                ((CValues c1 ns3 cs pk3) (returns-same _ ms2 ids pk ns3 cs pk3))
                (else (None _))))
            (match many same _
              ((Some b p) (recast _ ms ms2 p rhs2))
              ((None b)
                (let (many (Maybe $ Code ctx ms) gone) $ match many (constant-rhs _ _ rhs2) _ ((BTrue) (strengthen _ _ _ rest2 $ DHere _ _)) ((BFalse) (None _)))
                (match many gone _
                  ((Some e r) r)
                  ((None e) (CLet _ ms2 _ ids pk rhs2 rest2))))))))
      ((CLetRec c0 ns gids g rest) (match many g _ ((MkGroup c1 ids fns lk) (CLetRec _ _ _ (norm-group _ _ _ g ren) $ norm _ _ ms rest $ ren-weaken _ _ ids ren))))
      ((CMatch c0 ns scrut shape bs dfl)
        (let (many (Maybe $ Code ctx ns) dropped)
          (match many shape _
            ((ShNone c1)
              (match many bs _
                ((Nil a) (match many dfl _ ((Some b d) (Some _ $ norm _ _ ns d $ RFrame _ _ _ (Nil _) (LsNil _ _) ren)) ((None b) (None _))))
                ((Cons a b rest)
                  (match many rest _
                    ((Cons a2 b2 rest2) (None _))
                    ((Nil a2)
                      (match many b _
                        ((MkBranch c2 n0 d ids body)
                          (match many ids _
                            ((Nil z) (Some _ $ norm _ _ ns body $ RFrame _ _ _ (Nil _) (LsNil _ _) ren))
                            ((Cons z x xs) (None _))))))))))
            (else (None _))))
        (match many dropped _
          ((Some a d) d)
          ((None a)
        (CMatch _ ns (norm _ _ many-one scrut ren)
                (match many shape (((Shape ctx) s)) ((ShKnown c1 adt) (ShKnown _ adt)) ((ShNone c1) (ShNone _)) ((ShHeld c1 mc tags) (ShHeld _ (norm _ _ many-one mc ren) tags)))
                (norm-branches _ _ ns bs ren)
                $ match many dfl (((Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) ns) r)) ((Some a d) (Some _ $ norm _ _ ns d $ ren-weaken _ _ (Nil _) ren)) ((None a) (None _))))))
      ((CAbsurd c0 ms2) (CAbsurd _ ms2))
      ((CError c0 ms2 m) (CError _ ms2 m))))
  (many norm-list : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code from many-one) cs) (many (Ren from ctx) ren) -> (many (List $ Code ctx many-one) r) (erased (Lockstep (Code from many-one) (Code ctx many-one) cs r) lock)
    (match many cs _
      ((Nil a) (values (Nil _) (LsNil _ _)))
      ((Cons a c rest)
        (let (many r) (erased p) $ norm-list _ _ rest ren)
        (let (many c2) $ norm _ _ many-one c ren)
        (values (Cons _ c2 r) (LsCons _ _ c c2 rest r p)))))
  (many norm-group : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (erased (List $ Bin) gids) (subterm many (Group gids from) g) (many (Ren from ctx) ren) -> (many (Group gids ctx) r)
    (match many g _
      ((MkGroup c ids fns lk)
        (let (many fns2) (erased lk2) $ norm-fns _ _ ids fns ren)
        (MkGroup _ ids fns2 $ lockstep-trans _ _ _ _ _ _ lk lk2))))
  (many norm-fns : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Bin) gids) (subterm many (List $ Pair (Bin) $ Func gids from) fns) (many (Ren from ctx) ren) -> (many (List $ Pair (Bin) $ Func gids ctx) r) (erased (Lockstep (Pair (Bin) $ Func gids from) (Pair (Bin) $ Func gids ctx) fns r) lk)
    (match many fns _
      ((Nil a) (values (Nil _) (LsNil _ _)))
      ((Cons a p rest)
        (let (many r) (erased lk) $ norm-fns _ _ gids rest ren)
        (match many p _
          ((MkPair s t id fn)
            (match many fn _
              ((MkFunc g c rets n i ps body impl top)
                (let (many p2) $ MkPair _ _ id $ MkFunc _ _ rets n i ps (norm _ _ rets body $ ren-weaken _ _ ps $ ren-weaken _ _ gids ren) impl top)
                (values (Cons _ p2 r) (LsCons _ _ p p2 rest r lk)))))))))
  (many norm-branches : (erased (List $ List $ Bin) from) (erased (List $ List $ Bin) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch from ns) bs) (many (Ren from ctx) ren) -> (many (List $ Branch ctx ns) r)
    (match many bs _
      ((Nil a) (Nil _))
      ((Cons a b rest) (match many b _ ((MkBranch c0 n0 d ids body) (Cons _ (MkBranch _ _ d ids $ norm _ _ ns body $ ren-weaken _ _ ids ren) $ norm-branches _ _ ns rest ren)))))))

(def-fns _ $ many normalize : (many (List $ List $ Bin) ctx) (many (List $ Mult) ms) (many (Code ctx ms) code) -> (many (Code ctx ms) r)
  (norm _ _ ms code $ ren-id ctx))


; ---- tail and delegate (section 9, ASSUMPTIONS 17): judged on the normalized post-erasure code, per
; function, so a nested def-fns's marks are its own.

(def-fns _ $ many cc-marked : (many (CC) cc) -> (many (Bool) r)
  (match many cc _ ((CCTail) (BTrue)) ((CCDelegate) (BTrue)) (else (BFalse))))

(def-fns _
  (many has-marked : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) -> (many (Bool) r)
    (match many c _
      ((CApp c0 ms2 f args cc) (or (cc-marked cc) $ or (has-marked _ _ f) $ has-marked-list _ args))
      ((CValues c0 ms2 cs pk) (has-marked-list _ cs))
      ((CLet c0 ms2 ns ids pk rhs rest) (or (has-marked _ _ rhs) $ has-marked _ _ rest))
      ((CLetRec c0 ns gids g rest) (has-marked _ _ rest))
      ((CMatch c0 ns scrut shape bs dfl) (or (has-marked _ _ scrut) $ or (match many shape (((Bool) b)) ((ShKnown c1 a) (BFalse)) ((ShNone c1) (BFalse)) ((ShHeld c1 mc t) (has-marked _ _ mc))) $ or (has-marked-branches _ _ bs) $ match many dfl (((Bool) b)) ((Some a d) (has-marked _ _ d)) ((None a) (BFalse)))) (else (BFalse))))
  (many has-marked-list : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (or (has-marked _ _ c) $ has-marked-list _ rest))))
  (many has-marked-branches : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BFalse))
      ((Cons a b rest) (match many b _ ((MkBranch c0 n0 d ids body) (or (has-marked _ _ body) $ has-marked-branches _ _ rest)))))))

(def-fns _
  (many has-delegate : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) -> (many (Bool) r)
    (match many c _
      ((CApp c0 ms2 f args cc) (or (match many cc (((Bool) b)) ((CCDelegate) (BTrue)) (else (BFalse))) $ or (has-delegate _ _ f) $ has-delegate-list _ args))
      ((CValues c0 ms2 cs pk) (has-delegate-list _ cs))
      ((CLet c0 ms2 ns ids pk rhs rest) (or (has-delegate _ _ rhs) $ has-delegate _ _ rest))
      ((CLetRec c0 ns gids g rest) (has-delegate _ _ rest))
      ((CMatch c0 ns scrut shape bs dfl) (or (has-delegate _ _ scrut) $ or (match many shape (((Bool) b)) ((ShKnown c1 a) (BFalse)) ((ShNone c1) (BFalse)) ((ShHeld c1 mc t) (has-delegate _ _ mc))) $ or (has-delegate-branches _ _ bs) $ match many dfl (((Bool) b)) ((Some a d) (has-delegate _ _ d)) ((None a) (BFalse)))) (else (BFalse))))
  (many has-delegate-list : (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (or (has-delegate _ _ c) $ has-delegate-list _ rest))))
  (many has-delegate-branches : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BFalse))
      ((Cons a b rest) (match many b _ ((MkBranch c0 n0 d ids body) (or (has-delegate _ _ body) $ has-delegate-branches _ _ rest)))))))

; Every marked call sits in tail position: the body's final call, through lets, let recs and match branches
; for tail, directly for delegate.
(def-fns _
  (many tails-ok : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) c) (many (Bool) direct) -> (many (Bool) r)
    (match many c _
      ((CApp c0 ms2 f args cc) (and (not $ has-marked _ _ f) $ not $ has-marked-list _ args))
      ((CLet c0 ms2 ns ids pk rhs rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ c))
          ((BFalse) (and (not $ has-marked _ _ rhs) $ tails-ok _ _ rest direct))))
      ((CLetRec c0 ns gids g rest)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ rest))
          ((BFalse) (tails-ok _ _ rest direct))))
      ((CMatch c0 ns scrut shape bs dfl)
        (match many direct _
          ((BTrue) (not $ has-marked _ _ c))
          ((BFalse) (and (not $ has-marked _ _ scrut)
                      (and (match many shape (((Bool) b)) ((ShKnown c1 a) (BTrue)) ((ShNone c1) (BTrue)) ((ShHeld c1 mc t) (not $ has-marked _ _ mc)))
                        (and (tails-ok-branches _ _ bs direct)
                          $ match many dfl (((Bool) b)) ((Some a d) (tails-ok _ _ d direct)) ((None a) (BTrue))))))))
      ((CValues c0 ms2 cs pk) (not $ has-marked-list _ cs)) (else (BTrue))))
  (many tails-ok-branches : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Bool) direct) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BTrue))
      ((Cons a b rest) (match many b _ ((MkBranch c0 n0 d ids body) (and (tails-ok _ _ body direct) $ tails-ok-branches _ _ rest direct)))))))

; Validates the marks in a body and returns the normalized code and, for a delegate, the callee (section 9).
(def-fns _ $ many check-marks : (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Bin) pids) (many (List $ Mult) ms) (many (Code ctx ms) code) -> (many (Env) r) (many (Code ctx ms) code2) (many (Maybe $ Bin) delegated)
  (let (many code2) $ normalize ctx ms code)
  (match many (has-marked _ _ code2) _
    ((BFalse) (values env code2 $ None _))
    ((BTrue)
      (let (many delegate) $ has-delegate _ _ code2)
      (let (many (String) kind) $ match many delegate _ ((BTrue) "delegate") ((BFalse) "tail"))
      (let (many (Env) env1)
        (match many (tails-ok _ _ code2 delegate) _
          ((BTrue) env)
          ((BFalse) (env-error env $ str-cat3 "a " kind "-marked call is not in tail position"))))
      (match many delegate _
        ((BFalse) (values env1 code2 $ None _))
        ((BTrue)
          (match many code2 _
            ((CApp c0 ms2 f args cc)
              (let (many (Maybe $ Bin) named) $ match many f _ ((CVar c1 g p) (Some _ g)) ((CConst c1 g v) (Some _ g)) (else (None $ Bin)))
              (match many named _
                ((Some z g)
                  (match many (vars-of _ args) _
                    ((None a) (values (env-error env1 "a delegate call must pass the function's non-erased parameters straight through") code2 $ None _))
                    ((Some a ids)
                      (match many (bins-eq ids pids) _
                        ((BTrue) (values env1 code2 $ Some _ g))
                        ((BFalse) (values (env-error env1 "a delegate call must pass the function's non-erased parameters straight through") code2 $ None _)))))) (else (values (env-error env1 "delegate needs exactly one call to a named function") code2 $ None $ Bin)))) (else (values (env-error env1 "delegate needs exactly one call to a named function") code2 $ None $ Bin))))))))


; A call's decrease annotation (section 9): (predates p) right after the callee, or (subterm p) right before
; the decreasing argument, whose position it carries; a written proof p sits inside the call's arguments
; root, and _ or no annotation at all leaves the proof to the elaborator (SUGAR.md 3).
(def-adts $ Given : ((List $ Raw) root) -> Type
  enum
  (many Inferred : (erased (List $ Raw) root) -> (Given root))
  (many Written : (erased (List $ Raw) root) (many (Raw) p) (erased (Subterm (Raw) p (List $ Raw) root) q) -> (Given root)))

(def-adts $ Ann : ((List $ Raw) root) -> Type
  enum
  (many AnnNone : (erased (List $ Raw) root) -> (Ann root))
  (many AnnPredates : (erased (List $ Raw) root) (many (Given root) g) -> (Ann root))
  (many AnnSubterm : (erased (List $ Raw) root) (many (Nat) i) (many (Given root) g) -> (Ann root)))

(def-fns _ $ many given-of : (erased (List $ Raw) root) (many (Raw) p) (erased (Subterm (Raw) p (List $ Raw) root) q) -> (many (Given root) g)
  (match many (is-underscore p) _ ((BTrue) (Inferred _)) ((BFalse) (Written _ p q))))

(def-fns _ $ many ann-of : (many (Env) env) (many (Raw) arg) (many (Nat) i) (erased (List $ Raw) root) (erased (Subterm (Raw) arg (List $ Raw) root) pa) -> (many (Ann root) r)
  (match many arg _
    ((RList lq items)
      (match many items _
        ((Nil b) (AnnNone _))
        ((Cons b k krest)
          (match many krest _
            ((Nil c) (AnnNone _))
            ((Cons c p prest)
              (match many prest _
                ((Cons d q qrest) (AnnNone _))
                ((Nil d)
                  (let (erased pp) $ subterm-trans (prove-subterm p arg) pa)
                  (match many (and (is-mark env k $ MkPredates) $ nat-is-zero i) _
                    ((BTrue) (AnnPredates _ $ given-of _ p pp))
                    ((BFalse) (match many (is-mark env k $ MkSubterm) _ ((BTrue) (AnnSubterm _ i $ given-of _ p pp)) ((BFalse) (AnnNone _)))))))))))) (else (AnnNone root))))

; The first annotation and the arguments without it; a second annotation stays an argument, as in lib/elab.ml.
(def-fns _ $ many split-annotation : (subterm many (List $ Raw) args) (erased (List $ Raw) root) (erased (Within args root) w) (many (Env) env) (many (Nat) i) -> (many (Ann root) ann) (many (List $ Sub root) rest)
  (match many args _
    ((Nil a) (values (AnnNone _) $ Nil _))
    ((Cons a arg more)
      (let (erased pa) $ in-within _ _ _ _ (prove-subterm arg args) w)
      (let (erased wm) $ within-step _ _ _ (prove-subterm more args) w)
      (match many (ann-of env arg i _ pa) _
        ((AnnNone z)
          (let (many ann) (many rest) $ split-annotation more _ wm env $ Succ i)
          (values ann $ Cons _ (MkSub _ arg pa) rest))
        ((AnnPredates z g) (values (AnnPredates _ g) $ subs-of more _ wm))
        ((AnnSubterm z j g) (values (AnnSubterm _ j g) $ subs-of more _ wm))))))

(def-fns _ $ many subterm-indices : (subterm many (List $ Entry) tele) (many (Nat) i) -> (many (List $ Nat) r)
  (match many tele _
    ((Nil a) (Nil _))
    ((Cons a e rest)
      (match many (entry-sub e) _
        ((BTrue) (Cons _ i $ subterm-indices rest $ Succ i))
        ((BFalse) (subterm-indices rest $ Succ i))))))

; A bare call's annotation (SUGAR.md 3): where the levels differ, otherwise at the
; first subterm argument that differs from its counterpart; a written annotation stays as it is.
(def-fns _ $ many first-differing : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) -> (many (Maybe $ Nat) r)
  (match many positions _
    ((Nil a) (None _))
    ((Cons a pi rest)
      (match many (list-nth _ (env-subterms env) j) _
        ((NthMiss nt nl ni np) (None _))
        ((NthHit nt nl ni counterpart np)
          (match many (equal-env env (nth-term args pi) $ TVar counterpart) _
            ((BFalse) (Some _ pi))
            ((BTrue) (first-differing rest env args $ Succ j))))))))

(def-fns _ $ many resolve-ann : (many (Env) env) (erased (List $ Raw) root) (many (Ann root) ann) (many (Res) callee) (many (Bool) same) (many (List $ Nat) positions) (many (List $ Term) args) -> (many (Env) r) (many (Ann root) a)
  (match many ann _
    ((AnnNone z)
      (match many same _
        ((BFalse) (values env $ AnnPredates _ $ Inferred _))
        ((BTrue)
          (match many (first-differing positions env args 0) _
            ((Some b i) (values env $ AnnSubterm _ i $ Inferred _))
            ((None b) (values (env-error env $ str-cat3 "same-level call to " (show-t env $ res-term callee) " decreases no subterm argument") $ AnnNone _))))))
    (else (values env ann))))

(def-fns _ $ many index-of-nat : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many xs _
    ((Nil a) (None _))
    ((Cons a y rest) (match many (nat-cmp x y) _ ((CEq eq-t eq-r eq-x) (Some _ i)) (else (index-of-nat rest x $ Succ i))))))

; Earlier subterm arguments must equal their counterparts (section 9's lexicographic discipline).
(def-fns _ $ many check-earlier : (subterm many (List $ Nat) positions) (many (Env) env) (many (List $ Term) args) (many (Nat) j) (many (Nat) k) -> (many (Env) r)
  (match many positions _
    ((Nil a) env)
    ((Cons a pi rest)
      (match many (nat-lt j k) _
        ((BFalse) env)
        ((BTrue)
          (let (many (Env) env2)
            (match many (list-nth _ (env-subterms env) j) _
              ((NthMiss nt nl ni np) (env-error env $ str-cat3 "the enclosing function has no subterm parameter at position " (nat-str j) ""))
              ((NthHit nt nl ni counterpart np) (check env "value" (nth-term args pi) $ TVar counterpart))))
          (check-earlier rest env2 args (Succ j) k))))))

(def-fns _ $ many erased-in-many : (subterm many (List $ Mult) expect) (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) expect ress) lock) (many (Env) env) -> (many (Env) r)
  (match many expect _
    ((Nil a) env)
    ((Cons a m rest)
      (match erased lock _
        ((LsCons ta tb x y xs ys p)
          (match many ress _
            ((Cons b r rrest)
              (let (many (Env) env2)
                (match many (and (mult-is-many m) $ not $ mult-is-many $ res-erasure r) _
                  ((BTrue) (env-error env $ str-cat3 "erased value " (show-t env $ res-term r) $ str-cat3 " : " (show-t env $ res-ty r) " used in a non-erased position"))
                  ((BFalse) env)))
              (erased-in-many rest rrest p env2))))))))

; A call's or application's argument count against its telescope (lib/elab.ml's check_args).
(def-fns _ $ many check-arity : (many (Env) env) (many (List $ Entry) tele) (many (Nat) m) -> (many (Env) r)
  (let (many n) $ list-length _ tele)
  (match many (nat-cmp n m) _
    ((CEq eq-t eq-r eq-x) env)
    (else (count-error env " arguments" n m))))

(def-fns _ $ many malformed : (erased (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
  (values (env-error env $ str-cat3 "malformed " (sp-name sp) " form") (Nil _) $ CError _ expect "malformed"))

; The field at a wrapping constructor's one many position, given the arguments in order.
(def-fns _ $ many wrap-field : (subterm many (List $ Entry) tele) (many (List $ Term) args) (many (List $ Term) tys) -> (many (Maybe $ Pair (Term) (Term)) r)
  (match many tele _
    ((Nil a) (None _))
    ((Cons a e rest)
      (match many args _
        ((Nil b) (None _))
        ((Cons b t trest)
          (match many tys _
            ((Nil c) (None _))
            ((Cons c ty tyrest)
              (match many (entry-mult e) _
                ((Many) (match many (many-count rest) _ ((Zero) (Some _ $ MkPair _ _ t ty)) ((Succ k) (None _))))
                ((Erased) (wrap-field rest trest tyrest))))))))))

(def-fns _ $ many trace-many-fields : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (Env) r)
  (match many ids _
    ((Nil a) env)
    ((Cons a x rest)
      (match many (entry-mult-of env x) _
        ((Erased) (trace-many-fields rest env))
        ((Many)
          (match many (entry-state env x) _
            ((SDyn) (trace-many-fields rest env))
            ((SConst v) (trace-many-fields rest $ env-push-trace env $ TrConst x v))))))))

(def-fns _ $ many missing-arg : (many (Env) env) -> (many (Env) r) (many (Bin) x)
  (let (many env2) (many x) $ var (env-at env 0) "_")
  (values (env-back env env2) x))

(def-fns _ $ many erased-res : (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) erased-one ress) lock) -> (many (Res) r)
  (first-res _ _ ress lock))

(def-fns _ $ many erased-term : (many (List $ Res) ress) (erased (Lockstep (Mult) (Res) erased-one ress) lock) -> (many (Term) t)
  (res-term $ erased-res ress lock))

(let (many no-tele) $ None $ List $ Entry)

; ---- `_` arguments (SUGAR.md 6): what an application's result looks like over its parameters' metas, and
; the solving of that against the telescope the application is expected to produce.

(def-adts $ AppResult : -> Type
  enum
  (many ARApp : (many (Term) h) (many (Term) ret) -> (AppResult))
  (many ARCall : (many (List $ Entry) rets) -> (AppResult)))

(def-fns _ $ many result-tele : (many (AppResult) r) (many (List $ Term) mvars) -> (many (List $ Entry) tele)
  (match many r _
    ((ARApp h ret) (Cons _ (MkEntry (None _) (BFalse) (Erased) $ SgIs (TApp h $ list-rev _ mvars) $ instantiate mvars ret) $ Nil _))
    ((ARCall rets) (instantiate-tele mvars rets))))

(def-fns _ $ many entry-with-sg : (many (Entry) e) (many (Sg) sg) -> (many (Entry) r)
  (match many e _ ((MkEntry n s m sg0) (MkEntry n s m sg))))

; An entry's type: as given, or inferred from its value where no binder of the telescope is mentioned.
(def-fns _ $ many sg-type : (many (Env) env) (many (Sg) sg) -> (many (Maybe $ Term) r)
  (match many sg _
    ((SgTy t) (Some _ t))
    ((SgIs t ty) (match many (dangling t 0) _ ((BTrue) (None _)) ((BFalse) (Some _ ty))))))

; A result entry against an expected one: values where both are is-entries, types always.
(def-fns _ $ many solve-pair : (many (Env) env) (many (Sg) e) (many (Sg) r) (many (Bool) strict) -> (many (Env) r2) (many (Bool) ok)
  (let (many (Env) env1) (many (Bool) ok1)
    (match many e _
      ((SgIs a a-ty) (match many r (((Env) x) ((Bool) b)) ((SgIs b2 b2-ty) (solve env "value" b2 a strict)) ((SgTy t) (values env $ BTrue))))
      ((SgTy t) (values env $ BTrue))))
  (match many ok1 _
    ((BFalse) (values env1 $ BFalse))
    ((BTrue)
      (match many (sg-type env1 r) _
        ((None a) (values env1 $ BTrue))
        ((Some a rt)
          (match many (sg-type env1 e) _
            ((None b) (values env1 $ BTrue))
            ((Some b et) (solve env1 "type" rt et strict))))))))

(def-fns _ $ many solve-tele : (subterm many (List $ Entry) expect) (many (List $ Entry) result) (many (Env) env) (many (Bool) strict) -> (many (Env) r) (many (Bool) ok)
  (match many expect _
    ((Nil a) (values env $ BTrue))
    ((Cons a e rest)
      (match many result _
        ((Nil b) (values env $ BTrue))
        ((Cons b r rrest)
          (let (many env1) (many ok1) $ solve-pair env (entry-sg e) (entry-sg r) strict)
          (match many ok1 _
            ((BFalse) (values env1 $ BFalse))
            ((BTrue) (solve-tele rest rrest env1 strict))))))))

; [result] over [mvars] against the expectation, where an application has a `_`: not [strict], a failure
; leaves the environment as it was; strict, the mismatch is reported.
(def-fns _ $ many solve-against : (many (Env) env) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (List $ Term) mvars) (many (Bool) wilds) (many (Bool) strict) -> (many (Env) r)
  (match many expect _
    ((None a) env)
    ((Some a tele)
      (match many wilds _
        ((BFalse) env)
        ((BTrue)
          (let (many res) $ result-tele result mvars)
          (let (many n) $ list-length _ tele)
          (let (many m) $ list-length _ res)
          (match many (nat-cmp n m) _
            (else (match many strict _ ((BTrue) (count-error env " values" n m)) ((BFalse) env)))
            ((CEq eq-t eq-r eq-x)
              (let (many env2) (many ok) $ solve-tele tele res env strict)
              (match many (or ok strict) _ ((BTrue) env2) ((BFalse) env)))))))))

(def-fns _ $ many tele-has-meta : (subterm many (List $ Entry) es) (many (Env) env) -> (many (Bool) r)
  (match many es _
    ((Nil a) (BFalse))
    ((Cons a e rest) (or (has-meta-env env $ sg-term $ entry-sg e) $ tele-has-meta rest env))))

(def-fns _ $ many terms-have-meta : (subterm many (List $ Term) ts) (many (Env) env) -> (many (Bool) r)
  (match many ts _
    ((Nil a) (BFalse))
    ((Cons a t rest) (or (has-meta-env env t) $ terms-have-meta rest env))))

(def-fns _ $ many metaless-list : (subterm many (List $ Term) ts) (many (Env) env) -> (many (List $ Term) r)
  (match many ts _
    ((Nil a) (Nil _))
    ((Cons a t rest) (Cons _ (metaless env t) $ metaless-list rest env))))

; The first argument, in order, still holding a `_` no unification solved.
(def-fns _ $ many report-unsolved : (subterm many (List $ Term) args) (many (Env) env) (many (Nat) i) -> (many (Env) r)
  (match many args _
    ((Nil a) env)
    ((Cons a t rest)
      (match many (has-meta-env env t) _
        ((BTrue) (env-error env $ str-cat3 "argument " (nat-str i) " is _ and cannot be inferred"))
        ((BFalse) (report-unsolved rest env $ Succ i))))))

(def-fns _ $ many any-wild : (erased (List $ Raw) root) (subterm many (List $ Sub root) args) -> (many (Bool) r)
  (match many args _
    ((Nil a) (BFalse))
    ((Cons a s rest) (match many s _ ((MkSub z arg p) (or (is-underscore arg) $ any-wild _ rest))))))

; comptime-match (section 15): a Const, non-erased scrutinee with a non-erased discriminant, verified
; against the named constructor; the fields are bound Const and the facts refined as a branch would.
(def-fns _ $ many elab-comptime-match : (erased (List $ List $ Bin) ctx) (many (Env) env) (many (List $ Raw) args) -> (many (Env) r) (many (StmtCode ctx ctx) sc)
    (let (many shape) $ comptime-shape args)
    (match many shape _
      ((None a) (values (env-error env "malformed comptime-match: expected (comptime-match x (C field ...))") $ SNone _))
      ((Some a triple)
        (match many triple _
          ((MkPair s t xraw cpat)
            (match many cpat _
              ((MkPair s2 t2 craw fields)
                (let (many (Env) env1) $ match many (env-run-pos env) _ ((BTrue) env) ((BFalse) (env-error env "comptime-match is a run-position statement (section 15)")))
                (let (many env2) (many x) $ var-of-raw env1 xraw "a variable")
                (let (many (Env) env3) (many (Value) value)
                  (match many (entry env2 x) _
                    ((MkEInfo nm mult st mi me)
                      (match many st (((Env) e) ((Value) v))
                        ((SConst v) (match many mult (((Env) e) ((Value) v)) ((Many) (values env2 v)) ((Erased) (values (env-error env2 "comptime-match needs a Const, non-erased scrutinee") v))))
                        ((SDyn) (values (env-error env2 "comptime-match needs a Const, non-erased scrutinee") $ VError "Dyn"))))))
                (let (many env4) (many c) $ ctor-var env3 craw)
                (let (many tele) (many ret) $ ctor-type env4 c)
                (let (many head) $ type-head env4 $ type-of env4 x)
                (let (many (Bin) tid) $ match many head _ ((None b) (BZ)) ((Some b t) t))
                (let (many (Env) env5) (many (Maybe $ MatchInfo) found)
                  (match many head _
                    ((None b) (values (env-error env4 "scrutinee is not a datatype value") $ None _))
                    ((Some b t) (find-matchable env4 t))))
                (let (many (Env) env6)
                  (match many found _
                    ((None b) env5)
                    ((Some b info)
                      (match many info (((Env) e))
                        ((MkMatchInfo mid disc mctors rank)
                          (let (many env6a) $ match many disc (((Env) e)) ((DUnion) (env-error env5 "comptime-match needs a non-erased discriminant")) ((DEnum) env5))
                          (let (many env6b) (many mk) $ marker-checked env6a tid mctors c)
                          (match many mk (((Env) e))
                            ((Erased) (env-error env6b $ str-cat3 "comptime-match: " (name-of env6b c) " is phantom, so no non-erased value is headed by it"))
                            ((Many) env6b)))))))
                (let (many (Env) env7) (many (List $ Value) vs)
                  (match many (ctor-of env6 c) _
                    ((None d) (values (env-error env6 $ str-cat (name-of env6 c) " is not a run-position constructor") $ Nil _))
                    ((Some d ct)
                      (let (many i) (many vs) $ destruct ct value)
                      (match many (nat-cmp i $ ctor-index ct) (((Env) e) ((List $ Value) vs))
                        ((CEq eq-t eq-r eq-x) (values env6 vs))
                        (else (values (env-error env6 $ str-cat3 "comptime-match: expected " (name-of env6 c) $ str-cat ", got " $ rope-str $ show-value value) vs))))))
                (let (many (Env) env8)
                  (match many (nat-cmp (list-length _ fields) $ list-length _ tele) _
                    ((CEq eq-t eq-r eq-x) env7)
                    (else (env-error env7 $ str-cat3 (name-of env7 c) " has " $ str-cat (nat-str $ list-length _ tele) " fields"))))
                (let (many sv) (erased lsv) $ spread (tele-mults tele) vs)
                (let (many states) $ states-of sv)
                (let (many env9) (many fids) (erased lock) $ open-tele tele env8 (Some _ $ raw-names fields) (None _) (Some _ states) (Nil _) $ BFalse)
                (let (many env10) $ trace-many-fields fids env9)
                (match many (refine env10 (res-of env10 x) c fids ret) _
                  ((UOk env11) (values env11 $ SNone _))
                  ((UContra msg) (values (env-error env10 $ str-cat3 "internal: the verified value contradicts the facts in force (" msg ")") $ SNone _))))))))))

; Every function recurses on a raw it elaborates: the first subterm parameter is that raw or list, a later
; one a structure parsed from it (its entries prove they sit inside it) or a Steps budget spent when a
; function hands its whole raw to another.
; ---- Sugar (SUGAR.md 5): unary and distinct stand for calls on the prelude's Numeral lemmas, written
; down as the reference writes them and elaborated where the form is met. The elaborator's group takes a
; budget of such expansions as its first subterm parameter, spent when a generated form is elaborated,
; which is what lets that raw be of the elaborator's own making (ASSUMPTIONS 111).

(let (many sugar-budget) 1)

(def-fns _ $ many gen-atom : (many (String) s) -> (many (Raw) r)
  (RAtom 1 s))

(def-fns _ $ many gen-nat : (many (Nat) n) -> (many (Raw) r)
  (gen-atom $ nat-str n))

(def-fns _ $ many gen-of : (many (String) head) (many (List $ Raw) args) -> (many (Raw) r)
  (RList 1 $ Cons _ (gen-atom head) args))

(def-fns _ $ many gen-numeral-of : (many (Nat) n) -> (many (Raw) r)
  (gen-of "numeral-of" $ Cons _ (gen-nat n) $ Nil _))

(def-fns _ $ many bin-raw : (subterm many (Bin) b) -> (many (Raw) r)
  (match many b _
    ((BZ) (gen-of "BZ" $ Nil _))
    ((B1 x) (gen-of "B1" $ Cons _ (bin-raw x) $ Nil _))
    ((B2 x) (gen-of "B2" $ Cons _ (bin-raw x) $ Nil _))))

(def-fns _ $ many bin-text : (many (Nat) n) -> (many (Raw) r)
  (bin-raw $ bin-of-nat n $ BZ))

; The witness that n's spelling steps to (n+1)'s: (B1 x) steps to (B2 x), and (B2 x) to (B1 (succ x)).
(def-fns _ $ many bin-succ-witness : (subterm many (Bin) b) -> (many (Raw) r)
  (match many b _
    ((BZ) (gen-of "BSZ" $ Nil _))
    ((B1 x) (gen-of "BS1" $ Cons _ (bin-raw x) $ Nil _))
    ((B2 x) (gen-of "BS2" $ Cons _ (bin-raw x) $ Cons _ (bin-raw $ bin-succ x) $ Cons _ (bin-succ-witness x) $ Nil _))))

(def-fns _ $ many succs : (subterm many (Nat) k) (many (Raw) base) -> (many (Raw) r)
  (match many k _
    ((Zero) base)
    ((Succ j) (succs j $ gen-of "Succ" $ Cons _ base $ Nil _))))

(def-fns _ $ many unary-fold : (subterm many (Nat) k) (many (Nat) z) (many (Nat) lo) (many (Raw) floor) (many (Raw) acc) -> (many (Raw) r)
  (match many k _
    ((Zero) acc)
    ((Succ j)
      (let (many n) $ Succ z)
      (let (many below) $ succs (nat-sub z lo) floor)
      (let (many stp) $ gen-of "numeral-succ" $ Cons _ (bin-text z) $ Cons _ (bin-text n) $ Cons _ (gen-nat z) $ Cons _ (gen-nat n)
                          $ Cons _ (bin-succ-witness $ bin-of-nat z $ BZ) $ Cons _ (gen-numeral-of z) $ Cons _ (gen-numeral-of n) $ Nil _)
      (let (many congd) $ gen-of "eq-cong-succ" $ Cons _ (gen-nat z) $ Cons _ below $ Cons _ acc $ Nil _)
      (let (many acc2) $ gen-of "eq-trans" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat n) $ Cons _ (gen-of "Succ" $ Cons _ (gen-nat z) $ Nil _)
                          $ Cons _ (gen-of "Succ" $ Cons _ below $ Nil _) $ Cons _ stp $ Cons _ congd $ Nil _)
      (unary-fold j n lo floor acc2))))

(def-fns _ $ many unary-source : (many (Nat) za) (many (Nat) lo) (many (Bool) floored) -> (many (Raw) r)
  (let (many (Raw) floor) (many (Raw) acc)
    (match many floored _
      ((BFalse) (values (gen-of "Zero" $ Nil _) $ gen-of "numeral-zero" $ Cons _ (gen-nat 0) $ Cons _ (gen-numeral-of 0) $ Nil _))
      ((BTrue) (values (gen-nat lo) $ gen-of "Refl" $ Cons _ (gen-of "Nat" $ Nil _) $ Cons _ (gen-nat lo) $ Nil _))))
  (gen-of "let-match" $ Cons _ (gen-atom "erased") $ Cons _ (unary-fold (nat-sub za lo) lo lo floor acc)
    $ Cons _ (gen-of "Refl" $ Cons _ (gen-atom "_") $ Cons _ (gen-atom "_") $ Nil _) $ Nil _))

(def-fns _ $ many distinct-source : (many (Nat) za) (many (Nat) zb) -> (many (Raw) r)
  (gen-of "match" $ Cons _ (gen-atom "erased")
    $ Cons _ (gen-of "numeral-inj" $ Cons _ (bin-text za) $ Cons _ (bin-text zb) $ Cons _ (gen-nat za) $ Cons _ (gen-numeral-of za) $ Cons _ (gen-numeral-of zb) $ Nil _)
    $ Cons _ (RList 1 $ Cons _ (RList 1 $ Cons _ (gen-of "False" $ Nil _) $ Cons _ (gen-atom "f") $ Nil _) $ Nil _)
    $ Cons _ (gen-of "absurd" $ Cons _ (gen-atom "Refl") $ Nil _) $ Nil _))

(def-fns _
  ; An expression of the given size and erasures (sections 16, 20); [tele] is the telescope a bare _ reuses.
  (many elab-expr : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Mult) (Res) expect ress) lock)
    (let (many envl) $ env-at env $ raw-line raw)
    (let (many pos) (erased pf) $ pos-of expect)
    (let (many (Env) env2) (many (List $ Res) ress) (many (Code ctx expect) code)
      (match many raw _
        ((RAtom lq n)
          (let (many env2) (many x) $ var envl n)
          (values env2 (Cons _ (res-of env2 x) $ Nil _) $ match many pos (((Code ctx expect) c)) ((Many) (single _ expect pos pf $ var-code env2 ctx x)) ((Erased) (CErased _ expect))))
        ((RString lq s)
          (let (many env2) (many x) $ var-of-raw envl raw "a name")
          (values env2 (Cons _ (res-of env2 x) $ Nil _) $ match many pos (((Code ctx expect) c)) ((Many) (single _ expect pos pf $ var-code env2 ctx x)) ((Erased) (CErased _ expect))))
        ((RList lq items)
          (match many items (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
            ((Nil a) (values (env-error envl "empty form") (Nil _) $ CError _ expect "empty form"))
            ((Cons a head args)
              (match many (special-of envl head) (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                ((Some b sp)
                  (let (many multi) $ or (sp-eq sp $ SpExpr $ ExValues) $ or (sp-eq sp $ SpExpr $ ExMatch) $ or (sp-eq sp $ SpMark $ MkTail) $ sp-eq sp $ SpMark $ MkDelegate)
                  (let (many (Env) env0)
                    (match many multi _
                      ((BTrue) envl)
                      ((BFalse)
                        (match many expect (((Env) e))
                          ((Nil c) (env-error envl $ str-cat (sp-name sp) " produces one value"))
                          ((Cons c m1 rest) (match many rest (((Env) e)) ((Nil d) envl) ((Cons d m2 rest2) (env-error envl $ str-cat (sp-name sp) " produces one value"))))))))
                  (match many sp (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                    ((SpFormer fo)
                      (let (many env1) $ match many pos (((Env) e)) ((Many) (env-error env0 "a type in a non-erased position")) ((Erased) env0))
                      (let (many env2) (many t) $ elab-type-form sugar args two-steps env1 sp)
                      (values env2 (Cons _ (term-res env2 t type-term) $ Nil _) $ CErased _ expect))
                    ((SpStmt st) (values (env-error env0 $ str-cat (sp-name sp) " is a statement, not an expression") (Nil _) $ CError _ expect "statement as expression"))
                    ((SpMark mk)
                      (match many mk (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                        ((MkTail) (elab-marked sugar args env0 ctx expect tele (CCTail) sp))
                        ((MkDelegate) (elab-marked sugar args env0 ctx expect tele (CCDelegate) sp)) (else (malformed _ expect env0 sp))))
                    ((SpExpr ex)
                      (match many ex (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                        ((ExValues)
                          (let (many n) $ list-length _ expect)
                          (let (many na) $ list-length _ args)
                          (let (many env1) $ match many (nat-eq n na) (((Env) e)) ((BTrue) env0) ((BFalse) (count-error env0 " values" n na)))
                          (let (many env2) (many ress) (many codes) (erased pk) $ elab-values sugar args env1 ctx expect tele $ Nil _)
                          (values env2 ress $ code-of-values _ expect codes pk pos))
                        ((ExMatch)
                          (let (many env2) (many ress) (many code) $ elab-match sugar args env0 ctx expect tele)
                          (values env2 ress code))
                        ((ExMatchableOf)
                          (let (many env2) (many tid) $ named env0 (one-arg args) "a type constructor")
                          (let (many env3) (many found) $ find-matchable env2 tid)
                          (match many found (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((None c) (values (env-error env3 $ str-cat (name-of env3 tid) " has no Matchable in scope") (Nil _) $ CError _ expect "no Matchable"))
                            ((Some c info) (match many info (((Env) e) ((List $ Res) rs) ((Code ctx expect) c)) ((MkMatchInfo mid d cs rank) (values env3 (Cons _ (res-of env3 mid) $ Nil _) $ single _ expect pos pf $ matchable-code env3 ctx pos mid))))))
                        ((ExNewtypeOf)
                          (let (many env2) (many c) $ ctor-var env0 $ one-arg args)
                          (match many (find-newtype (env-objects env2) env2 c) (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((None d) (values (env-error env2 $ str-cat (name-of env2 c) " has no Newtype in scope") (Nil _) $ CError _ expect "no Newtype"))
                            ((Some d x) (values env2 (Cons _ (res-of env2 x) $ Nil _) $ CErased _ expect))))
                        ((ExNumeralOf) (numeral-of-lit _ expect env0 $ one-arg args))
                        ((ExDistinct) (let (many env2) (many rs) $ elab-distinct sugar args env0 ctx) (values env2 rs $ CErased _ expect))
                        ((ExLevelOf)
                          (let (many env2) (many f) (many fty0) $ elab-one-term sugar args env0)
                          (let (many fty) $ canon-env env2 fty0)
                          (match many fty (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((TFn lv ps rs) (values env2 (Cons _ (MkRes lv level-term $ Erased) $ Nil _) $ CErased _ expect)) (else (values (env-error env2 $ level-of-error env2 f fty) (Nil $ Res) $ CError _ expect "level-of"))))
                        ((ExProveSubterm)
                          (let (many env2) (many a) (many aty) (many b2) (many bty) $ elab-two-terms sugar args env0)
                          (let (many env3) (many r) $ mint-subterm env2 a aty b2 bty)
                          (values env3 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExProvePredates)
                          (match many args (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil c) (values (env-error env0 "malformed prove-predates form") (Nil _) $ CError _ expect "prove-predates"))
                            ((Cons c xraw rest)
                              (let (many env2) (many x) $ var-of-raw env0 xraw "a variable")
                              (let (many env3) (many lt) (many ltty) $ elab-one-term sugar rest env2)
                              (let (many env4) (many lvl) $ level-var-checked env3 lt)
                              (let (many env5) (many r) $ mint-predates env4 x lvl)
                              (values env5 (Cons _ r $ Nil _) $ CErased _ expect))))
                        ((ExPredatesTrans)
                          (let (many env1) (many p) (many q) $ two-proofs sugar args env0 ctx)
                          (let (many env2a) (many p0) (many p1) (many p2) $ expect-proof3 env1 predates-id p)
                          (let (many env2) (many q0) (many q1) (many q2) $ expect-proof3 env2a predates-id q)
                          (let (many env3) $ check env2 "value" q1 p2)
                          (let (many env4) (many r) $ mint env3 $ proof-type predates-id $ Cons _ p0 $ Cons _ p1 $ Cons _ q2 $ Nil _)
                          (values env4 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExSubtermTrans)
                          (let (many env1) (many p) (many q) $ two-proofs sugar args env0 ctx)
                          (let (many env2a) (many p0) (many p1) (many p2) (many p3) $ expect-proof4 env1 subterm-id p)
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) $ expect-proof4 env2a subterm-id q)
                          (let (many env3) $ check env2 "value" q1 p3)
                          (let (many env4) (many r) $ mint env3 $ proof-type subterm-id $ Cons _ p0 $ Cons _ p1 $ Cons _ q2 $ Cons _ q3 $ Nil _)
                          (values env4 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExCoercibleTrans)
                          (let (many env1) (many p) (many q) $ two-proofs sugar args env0 ctx)
                          (let (many env2a) (many p0) (many p1) (many p2) (many p3) $ expect-proof4 env1 coercible-id p)
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) $ expect-proof4 env2a coercible-id q)
                          (let (many env3) $ check env2 "value" q1 p3)
                          (let (many env4) (many r) $ mint env3 $ proof-type coercible-id $ Cons _ p0 $ Cons _ p1 $ Cons _ q2 $ Cons _ q3 $ Nil _)
                          (values env4 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExPredatesSubterm)
                          (let (many env1) (many p) (many q) $ two-proofs sugar args env0 ctx)
                          (let (many env2a) (many p0) (many p1) (many p2) $ expect-proof3 env1 predates-id p)
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) $ expect-proof4 env2a subterm-id q)
                          (let (many env3) $ check env2 "value" q3 p1)
                          (let (many env4) (many r) $ mint env3 $ proof-type predates-id $ Cons _ q0 $ Cons _ q1 $ Cons _ p2 $ Nil _)
                          (values env4 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExCoerce)
                          (match many args (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil c) (values (env-error env0 "malformed coerce form") (Nil _) $ CError _ expect "coerce"))
                            ((Cons c araw rest)
                              (let (many env2a) (many ars) (many code) (erased lock) $ elab-expr sugar araw env0 ctx (Cons _ pos $ Nil _) no-tele $ CCPlain)
                              (let (many env2) $ settle-res env2a $ first-res _ _ ars lock)
                              (let (many env3) (many p) $ elab-one-erased sugar rest env2 ctx)
                              (let (many env4) (many p0) (many p1) (many p2) (many p3) $ expect-proof4 env3 coercible-id p)
                              (let (many env5) $ check env4 "value" (res-term $ first-res _ _ ars lock) p1)
                              (let (many env6) (many x) $ bind env5 (None _) pos (SDyn) p2 (Some _ p3) coercible-id)
                              (values env6 (Cons _ (res-of env6 x) $ Nil _) $ single _ expect pos pf code))))
                        ((ExCoercibleRefl)
                          (let (many env2) (many e) (many ty) $ elab-one-term sugar args env0)
                          (let (many env3) (many r) $ mint env2 $ proof-type coercible-id $ Cons _ ty $ Cons _ e $ Cons _ ty $ Cons _ e $ Nil _)
                          (values env3 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExCoercibleSym)
                          (let (many env2) (many p) $ elab-one-erased sugar args env0 ctx)
                          (let (many env3) (many p0) (many p1) (many p2) (many p3) $ expect-proof4 env2 coercible-id p)
                          (let (many env4) (many r) $ mint env3 $ proof-type coercible-id $ Cons _ p2 $ Cons _ p3 $ Cons _ p0 $ Cons _ p1 $ Nil _)
                          (values env4 (Cons _ r $ Nil _) $ CErased _ expect))
                        ((ExCoercibleWrap)
                          (match many args (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil c) (values (env-error env0 "malformed coercible-wrap form") (Nil _) $ CError _ expect "coercible-wrap"))
                            ((Cons c craw wargs)
                              (let (many env2) (many cid) $ ctor-var env0 craw)
                              (let (many ctele) (many ret) $ ctor-type env2 cid)
                              (let (many env3)
                                (match many (find-newtype (env-objects env2) env2 cid) (((Env) e))
                                  ((None d) (env-error env2 $ str-cat (name-of env2 cid) " has no Newtype in scope: only a marked newtype's wrapping constructor has one"))
                                  ((Some d x) env2)))
                              (let (many env4a) (many acc) (many tys) (many codes) $ check-args sugar wargs (subs-all wargs) one-step env3 ctx ctele (Erased) no-tele (ARApp (TVar cid) ret) (BTrue) $ BFalse)
                              (let (many env4) $ settle-list acc env4a)
                              (let (many env5) (many f) (many fty)
                                (match many (wrap-field ctele (list-rev _ acc) $ list-rev _ tys) (((Env) e0) ((Term) t0) ((Term) ty0))
                                  ((Some d pr) (match many pr (((Env) e0) ((Term) t0) ((Term) ty0)) ((MkPair a1 a2 g gty) (values env4 g gty))))
                                  ((None d) (values (env-error env4 $ str-cat (name-of env4 cid) " is not the wrapping constructor") (TErr "not the wrapping constructor") $ TErr "not the wrapping constructor"))))
                              (let (many env6) (many r) $ mint env5 $ proof-type coercible-id $ Cons _ fty $ Cons _ f $ Cons _ (instantiate acc ret) $ Cons _ (TApp (TVar cid) $ list-rev _ acc) $ Nil _)
                              (values env6 (Cons _ r $ Nil _) $ CErased _ expect))))
                        ((ExCoercibleCtor)
                          (match many args (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((Nil c) (values (env-error env0 "malformed coercible-ctor form") (Nil _) $ CError _ expect "coercible-ctor"))
                            ((Cons c craw cargs)
                              (let (many env2) (many cid) $ ctor-var env0 craw)
                              (let (many ctele) (many ret) $ ctor-type env2 cid)
                              (let (many env3) $ match many (phantom env2 cid) (((Env) e)) ((BTrue) (env-error env2 $ str-cat (name-of env2 cid) " is phantom")) ((BFalse) env2))
                              (let (many env4) (many src) (many tgt) $ coercible-ctor-args sugar cargs env3 ctx ctele (Nil _) (Nil _) cid)
                              (let (many env5) (many r) $ mint env4 $ proof-type coercible-id $ Cons _ (instantiate src ret) $ Cons _ (TApp (TVar cid) $ list-rev _ src) $ Cons _ (instantiate tgt ret) $ Cons _ (TApp (TVar cid) $ list-rev _ tgt) $ Nil _)
                              (values env5 (Cons _ r $ Nil _) $ CErased _ expect))))
                        ((ExCoercibleOf)
                          (let (many env2) (many g) $ named env0 (one-arg args) "a function name")
                          (match many (find-coercible (env-objects env2) env2 g) (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                            ((None c) (values (env-error env2 $ str-cat (name-of env2 g) " has no delegate proof in scope") (Nil _) $ CError _ expect "no delegate proof"))
                            ((Some c x) (values env2 (Cons _ (res-of env2 x) $ Nil _) $ CErased _ expect))))))))
                ((None b)
                  (let (many env2) (many h) (many hcode)
                    (match many head (((Env) e) ((Res) r) ((Code ctx (Cons (Mult) pos (Nil (Mult)))) c))
                      ((RAtom lq2 n) (let (many env2) (many x) $ var envl n) (values env2 (res-of env2 x) $ match many pos (((Code ctx (Cons (Mult) pos (Nil (Mult)))) c0)) ((Many) (var-code env2 ctx x)) ((Erased) (CErased _ $ Cons _ pos $ Nil _))))
                      ((RString lq2 s) (let (many env2) (many x) $ var-of-raw envl head "a name") (values env2 (res-of env2 x) $ match many pos (((Code ctx (Cons (Mult) pos (Nil (Mult)))) c0)) ((Many) (var-code env2 ctx x)) ((Erased) (CErased _ $ Cons _ pos $ Nil _))))
                      ((RList lq2 hitems)
                        (let (many env2) (many rs) (many hcode) (erased lock) $ elab-expr sugar head envl ctx (Cons _ pos $ Nil _) no-tele $ CCPlain)
                        (values env2 (first-res _ _ rs lock) hcode))))
                  (match many (canon-env env2 $ res-ty h) (((Env) e) ((List $ Res) rs) ((Code ctx expect) c))
                    ((TTyCtor ttele)
                      (let (many env3) $ match many pos (((Env) e)) ((Many) (env-error env2 "type constructor application in a non-erased position")) ((Erased) env2))
                      (let (many env4) (many acc) (many tys) (many codes) $ check-args sugar args (subs-all args) one-step (check-arity env3 ttele $ list-length _ args) ctx ttele (Erased) tele (ARApp (res-term h) type-term) (BTrue) $ BFalse)
                      (values env4 (Cons _ (MkRes (TApp (res-term h) $ list-rev _ acc) type-term $ Erased) $ Nil _) $ CErased _ expect))
                    ((TValCtor ctele ret)
                      (let (many env3)
                        (match many (and (mult-is-many pos) $ not $ mult-is-many $ res-erasure h) (((Env) e))
                          ((BTrue) (env-error env2 $ str-cat3 "erased constructor " (show-t env2 $ res-term h) " in a non-erased position"))
                          ((BFalse) env2)))
                      (let (many env4) (many acc) (many tys) (many codes) $ check-args sugar args (subs-all args) one-step (check-arity env3 ctele $ list-length _ args) ctx ctele pos tele (ARApp (res-term h) ret) (BFalse) $ BFalse)
                      (let (many code) $ match many pos (((Code ctx (Cons (Mult) pos (Nil (Mult)))) c)) ((Erased) (CErased _ $ Cons _ pos $ Nil _)) ((Many) (CApp _ many-one hcode codes $ CCCtor)))
                      (values env4 (Cons _ (MkRes (TApp (res-term h) $ list-rev _ acc) (instantiate acc ret) pos) $ Nil _) $ single _ expect pos pf code))
                    ((TFn lv params rets)
                      (let (many ann) (many args2) $ split-annotation args _ (WHere args) env2 0)
                      (elab-call sugar args (MkPair _ _ args2 ann) env2 ctx expect tele h pos hcode lv params rets cc))
                    ((TErr m) (values (env-error env2 $ not-applicable env2 h) (Nil _) $ CError _ expect m)) (else (values (env-error env2 $ not-applicable env2 h) (Nil $ Res) $ CError _ expect "not applicable"))))))))))
    (let (many n) $ list-length _ expect)
    (let (many m) $ list-length _ ress)
    (let (many ress2) (erased lock) $ list-fit _ _ expect (metaless-ress ress env2) no-res)
    (match many (nat-cmp n m) _
      (else (values (env-back env $ count-error env2 " values" n m) ress2 code lock))
      ((CEq eq-t eq-r eq-x) (values (env-back env $ erased-in-many expect ress2 lock env2) ress2 code lock))))
  (many elab-one-term : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) -> (many (Env) r) (many (Term) t) (many (Term) ty)
    (match many args _
      ((Nil a) (let (many env2) (many x) $ missing-arg env) (values env2 (TVar x) $ type-of env2 x))
      ((Cons a araw rest) (let (many env2) (many t) (many ty) $ elab-term sugar araw env (BFalse) no-tele) (values (settle env2 t) t ty))))

  (many elab-one-erased : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (Res) p)
    (match many args _
      ((Nil a) (let (many env2) (many x) $ missing-arg env) (values env2 $ res-of env2 x))
      ((Cons a araw rest)
        (let (many env2) (many ress) (many code) (erased lock) $ elab-expr sugar araw env ctx erased-one no-tele $ CCPlain)
        (values (settle env2 $ erased-term ress lock) $ erased-res ress lock))))

  ; Grammar expressions (section 5): variables, constructor applications and type formers; [as-type] also
  ; checks the result is a type.
  (many elab-term : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (Bool) as-type) (many (Maybe $ List $ Entry) tele) -> (many (Env) r) (many (Term) t) (many (Term) ty)
    (let (many envl) $ env-at env $ raw-line raw)
    (let (many (Env) env2) (many (Term) t) (many (Term) ty)
      (match many raw _
        ((RAtom lq n)
          (match many (str-cmp n "_") (((Env) e0) ((Term) t0) ((Term) ty0))
            ((CEq eq-t eq-r eq-x) (let (many env2) (many x) $ bind-as envl (BTrue) (BFalse) (None _) (Erased) (SDyn) type-term (None _) coercible-id) (values env2 (TVar x) type-term))
            (else (let (many env2) (many x) $ var envl n) (values env2 (TVar x) $ type-of env2 x))))
        ((RString lq s) (let (many env2) (many x) $ var-of-raw envl raw "a name") (values env2 (TVar x) $ type-of env2 x))
        ((RList lq items)
          (match many items (((Env) e0) ((Term) t0) ((Term) ty0))
            ((Nil a) (values (env-error envl "empty form") (TErr "empty form") $ TErr "empty form"))
            ((Cons a head args)
              (match many (special-of envl head) (((Env) e0) ((Term) t0) ((Term) ty0))
                ((Some b sp)
                  (let (many env2) (many t) $ elab-type-form sugar args two-steps envl sp)
                  (values env2 t type-term))
                ((None b)
                  (let (many env2) (many x) $ var-of-raw envl head "a constructor")
                  (let (many h) $ TVar x)
                  (let (many hty) $ canon-env env2 $ type-of env2 x)
                  (match many hty (((Env) e0) ((Term) t0) ((Term) ty0))
                    ((TTyCtor ttele)
                      (let (many env3) (many acc) (many tys) (many codes) $ check-args sugar args (subs-all args) one-step (check-arity env2 ttele $ list-length _ args) (Nil _) ttele (Erased) tele (ARApp h type-term) (BTrue) $ BFalse)
                      (values env3 (TApp h $ list-rev _ acc) type-term))
                    ((TValCtor ctele ret)
                      (let (many env3) (many acc) (many tys) (many codes) $ check-args sugar args (subs-all args) one-step (check-arity env2 ctele $ list-length _ args) (Nil _) ctele (Erased) tele (ARApp h ret) (BTrue) $ BFalse)
                      (values env3 (TApp h $ list-rev _ acc) $ instantiate acc ret))
                    ((TFn l p r) (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "function in type") $ TErr "function in type"))
                    ((TErr m) (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr m) $ TErr m)) (else (values (env-error env2 $ cannot-apply-in-type env2 h hty) (TErr "not applicable") $ TErr "not applicable"))))))))))
    (let (many (Env) env3) $ match many as-type _ ((BFalse) env2) ((BTrue) (check env2 "type" ty type-term)))
    (values (env-back env env3) t ty))

  (many elab-type-form : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (subterm many (Steps $ Succ $ Succ $ Zero) st) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (Term) t)
    (match many st _
      ((SS sn k)
        (match many sp _
          ((SpFormer fo)
            (match many fo _
              ((FoFn)
                (match many args _
                  ((Nil a) (values (env-error env "malformed Fn") $ TErr "malformed Fn"))
                  ((Cons a lvraw rest)
                    (let (many env2) (many lv) (many lvty) $ elab-term sugar lvraw env (BFalse) no-tele)
                    (let (many env3) $ check env2 "type" lvty level-term)
                    (let (many ps) (many after) (erased wa) $ split-arrow rest _ (WHere rest) env3)
                    (let (many env4) (many params) (many rets) $ elab-fn-type sugar rest one-step (MkPair _ _ ps $ subs-of after _ wa) env3)
                    (values env4 $ TFn lv params rets))))
              ((FoTyCtor)
                (let (many ps) (many after) (erased wa) $ split-arrow args _ (WHere args) env)
                (elab-tyctor sugar args k (MkPair _ _ ps $ subs-of after _ wa) env))
              ((FoValCtor)
                (let (many ps) (many after) (erased wa) $ split-arrow args _ (WHere args) env)
                (let (many env2) (many tele) (many ret) (many t) $ elab-valctor sugar args k (MkPair _ _ ps $ subs-of after _ wa) env)
                (values env2 t))
              ((FoMatchable)
                (match many args _
                  ((Nil a) (values (env-error env "malformed Matchable") $ TErr "malformed Matchable"))
                  ((Cons a d rest)
                    (match many rest _
                      ((Nil b) (values (env-error env "malformed Matchable") $ TErr "malformed Matchable"))
                      ((Cons b t cs)
                        (let (many env2) (many disc) $ disc-of-checked env d)
                        (let (many env3) (many tid) $ named env2 t "a type constructor")
                        (let (many env4) (many mcs) $ elab-mctors sugar cs env3)
                        (values env4 $ TMatchable disc (TVar tid) mcs))))))
              ((FoNewtype)
                (match many args _
                  ((Nil a) (values (env-error env "malformed Newtype") $ TErr "malformed Newtype"))
                  ((Cons a c rest)
                    (match many rest _
                      ((Cons b x more) (values (env-error env "malformed Newtype") $ TErr "malformed Newtype"))
                      ((Nil b)
                        (let (many env2) (many cid) $ ctor-var env c)
                        (values env2 $ TNewtype $ TVar cid))))))))
          ((SpStmt s) (values (env-error env $ str-cat (sp-name sp) " cannot appear in a type") $ TErr "statement in type"))
          ((SpExpr e) (values (env-error env $ str-cat (sp-name sp) " cannot appear in a type") $ TErr "expression in type"))
          ((SpMark m) (values (env-error env $ str-cat (sp-name sp) " cannot appear in a type") $ TErr "mark in type"))))))

  (many elab-mctors : (subterm many (Nat) sugar) (subterm many (List $ Raw) cs) (many (Env) env) -> (many (Env) r) (many (List $ MCtor) mcs)
    (match many cs _
      ((Nil a) (values env $ Nil _))
      ((Cons a c rest)
        (let (many (Env) env1) (many (Mult) m) (many (Raw) craw)
          (match many (raw-items c) _
            ((Nil b) (values (env-error env "expected (multiplicity Constructor)") (Many) c))
            ((Cons b mraw more)
              (match many more (((Env) e0) ((Mult) m0) ((Raw) r0))
                ((Nil d) (values (env-error env "expected (multiplicity Constructor)") (Many) c))
                ((Cons d cr more2)
                  (match many more2 (((Env) e0) ((Mult) m0) ((Raw) r0))
                    ((Cons f x y) (values (env-error env "expected (multiplicity Constructor)") (Many) cr))
                    ((Nil f)
                      (match many (mult-of env mraw) (((Env) e0) ((Mult) m0) ((Raw) r0))
                        ((None g) (values (env-error env $ str-cat "expected a multiplicity, got " $ show-r mraw) (Many) cr))
                        ((Some g mm) (values env mm cr))))))))))
        (let (many env2) (many cid) $ ctor-var env1 craw)
        (let (many env3) (many mcs) $ elab-mctors sugar rest env2)
        (values env3 $ Cons _ (MkMCtor m $ TVar cid) mcs))))

  ; The signature pieces [piece] were read from [root]; [st] pays for the parse of each telescope.
  (many elab-fn-type : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (List $ Entry) params) (many (List $ Entry) rets)
    (match many piece _
      ((MkPair x y ps rs)
        (let (many env2) (many ids) (many params) $ elab-tele sugar root st ps env (MMDeclared) (Nil _) (BTrue) $ BFalse)
        (let (many env3) (many ids2) (many rets) $ elab-tele sugar root st rs env2 (MMDeclared) (tvars-rev ids $ Nil _) (BFalse) $ BFalse)
        (values (env-discard env env3) params rets))))

  (many elab-tyctor : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (Term) t)
    (match many piece _
      ((MkPair x y ps ret)
        (let (many env2) (many ids) (many tele) $ elab-tele sugar root st ps env (MMErased) (Nil _) (BFalse) $ BFalse)
        (let (many (Env) env3)
          (match many ret _
            ((Cons a s more)
              (match many more (((Env) e0))
                ((Nil b) (match many s (((Env) e0)) ((MkSub rt r p) (let (many env3) (many t) (many ty) $ elab-term sugar (subterm p) r env2 (BFalse) no-tele) (check env3 "value" t type-term))))
                ((Cons b x2 y2) (env-error env2 "TyCtor returns Type"))))
            ((Nil a) (env-error env2 "TyCtor returns Type"))))
        (values (env-discard env env3) $ TTyCtor tele))))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type; the return is an application of a type constructor in scope (ASSUMPTIONS 70, 80).
  (many elab-valctor : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (Pair (List $ Sub root) $ List $ Sub root) piece) (many (Env) env) -> (many (Env) r) (many (List $ Entry) tele) (many (Term) ret) (many (Term) t)
    (match many piece _
      ((MkPair x y ps rets)
        (let (many env2) (many ids) (many tele) $ elab-tele sugar root st ps env (MMDeclared) (Nil _) (BFalse) $ BFalse)
        (let (many (Env) env3) (many (Term) ret)
          (match many rets _
            ((Nil a) (values (env-error env2 "a constructor returns one type") $ TErr "no return"))
            ((Cons a s more)
              (match many more (((Env) e0) ((Term) t0))
                ((Nil b) (match many s (((Env) e0) ((Term) t0)) ((MkSub rt r p) (let (many env3) (many t) (many ty) $ elab-term sugar (subterm p) r env2 (BTrue) no-tele) (values env3 t))))
                ((Cons b x2 y2) (values (env-error env2 "a constructor returns one type") $ TErr "no return"))))))
        (let (many (Bool) ok)
          (match many (canon-env env3 ret) _
            ((TApp h as)
              (match many h (((Bool) b0))
                ((TVar t) (and (not $ list-mem-bin ids t)
                             $ match many (type-of env3 t) (((Bool) b0)) ((TTyCtor p) (BTrue)) (else (BFalse)))) (else (BFalse)))) (else (BFalse))))
        (let (many (Env) env4)
          (match many ok _
            ((BTrue) env3)
            ((BFalse) (env-error env3 $ str-cat "a constructor returns an application of a type constructor in scope, not " $ show-t env3 ret))))
        (values env4 tele ret $ TValCtor tele $ abstract (list-rev _ ids) ret))))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 30).
  ; [ids]: binders already in force, innermost first.
  (many elab-tele : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Succ $ Zero) st) (subterm many (List $ Sub root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (Bool) subterm-ok) (many (Bool) holes) -> (many (Env) r) (many (List $ Bin) bound) (many (List $ Entry) tele)
    (match many st _
      ((SS sn k)
        (let (many env2) (many entries2) $ parse-entries-checked _ entries env)
        (elab-src-entries sugar root k entries2 env2 mode ids (Nil _) subterm-ok holes))))

  (many elab-src-entries : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (Steps $ Zero) st) (subterm many (List $ SrcEntry root) entries) (many (Env) env) (many (MultsMode) mode) (many (List $ Term) ids) (many (List $ Bin) bound) (many (Bool) subterm-ok) (many (Bool) holes) -> (many (Env) r) (many (List $ Bin) bound2) (many (List $ Entry) tele)
    (match many entries _
      ((Nil a) (values env (list-rev _ bound) $ Nil _))
      ((Cons a e rest)
        (match many e _
          ((MkSrcEntry rt sub smult ssg name)
            (let (many (Env) env0)
              (match many (and sub $ not subterm-ok) _
                ((BTrue) (env-error env "subterm is not allowed here"))
                ((BFalse) env)))
            (let (many (Env) env1) (many (Mult) mult) (many (MultsMode) mode2)
              (match many mode _
                ((MMDeclared) (match many smult (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((None b) (values (env-error env0 $ str-cat3 "entry " name " needs a multiplicity") (Many) mode)) ((Some b m) (values env0 m mode))))
                ((MMErased) (match many smult (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((None b) (values env0 (Erased) mode)) ((Some b m) (values (env-error env0 "these entries carry no multiplicity") (Erased) mode))))
                ((MMExpect ms)
                  (let (many env0b) $ match many smult (((Env) e0)) ((None b) env0) ((Some b m) (env-error env0 "a match annotation carries no multiplicities")))
                  (match many ms (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((Nil b) (values env0b (Erased) mode)) ((Cons b m more) (values env0b m $ MMExpect more))))))
            (let (many (Env) env2) (many (Sg) sg)
              (match many ssg _
                ((None b) (values (env-error env1 $ str-cat3 "entry " name " needs a type or an is clause") $ SgTy $ TErr "no type"))
                ((Some b s)
                  (match many s (((Env) e0) ((Sg) s0))
                    ((SrcTy rt2 r p) (let (many env2) (many t) (many ty) $ elab-term sugar (subterm p) r env1 (BTrue) no-tele) (values env2 $ SgTy t))
                    ((SrcIs rt2 r p) (let (many env2) (many t) (many ty) $ elab-term sugar (subterm p) r env1 (BFalse) no-tele) (values env2 $ SgIs t ty))))))
            (let (many ty) (many rule) $ fact-of env2 sg)
            (let (many nm) $ name-or-anon name)
            (let (many env3) (many x) $ bind-as env2 (BFalse) holes nm mult (SDyn) ty rule coercible-id)
            (let (many entry) $ MkEntry nm sub mult $ abstract-sg (bin-ids-of ids) sg)
            (let (many env4) (many bound2) (many tele) $ elab-src-entries sugar root st rest env3 mode2 (Cons _ (TVar x) ids) (Cons _ x bound) subterm-ok holes)
            (values env4 bound2 $ Cons _ entry tele))))))
  ; A body: statements then the final expression (section 16); [items] sits within [root].
  (many elab-body : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Raw) items) (erased (Within items root) w) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code) (erased (Lockstep (Mult) (Res) expect ress) lock)
    (match many items _
      ((Nil a)
        (let (many ress) (erased lock) $ list-fit _ _ expect (Nil _) no-res)
        (values (env-error env "a body needs a final expression") ress (CError _ expect "empty body") lock))
      ((Cons a item rest)
        (let (erased pi) $ in-within _ _ _ _ (prove-subterm item items) w)
        (match many rest _
          ((Nil b) (elab-expr sugar (subterm pi) item env ctx expect tele $ CCPlain))
          ((Cons b item2 rest2)
            (let (many env2) (many ctx2) (many sc) $ elab-stmt sugar (subterm pi) item env ctx)
            (let (many env3) (many ress) (many code) (erased lock) $ elab-body sugar root rest (within-step rest items root (prove-subterm rest items) w) env2 ctx2 expect tele)
            (values env3 ress (wrap-stmt _ _ expect sc code) lock))))))

  (many elab-stmt : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
    (let (many envl) $ env-at env $ raw-line raw)
    (let (many bad) $ env-error envl $ str-cat (show-r raw) " is not a statement")
    (let (many (Env) env2) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
      (match many raw _
        ((RList lq items)
          (match many items (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
            ((Nil a) (values bad ctx $ SNone _))
            ((Cons a head args)
              (match many (special-of envl head) (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
                ((None b) (values bad ctx $ SNone _))
                ((Some b sp)
                  (match many sp (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
                    ((SpStmt st)
                      (match many st (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
                        ((StLet)
                          (let (many braws) (many rhs) (erased wr) $ split-returns args _ (WHere args) envl)
                          (let (many env0) (many binders) $ parse-entries-checked _ braws envl)
                          (let (many env0b) (many tele)
                            (match many (all-have-sg _ binders) (((Env) e0) ((Maybe $ List $ Entry) t))
                              ((BFalse) (values env0 no-tele))
                              ((BTrue)
                                (let (many env1) (many bound) (many t) $ elab-src-entries sugar args (SZ) binders env0 (MMDeclared) (Nil _) (Nil _) (BFalse) $ BTrue)
                                (values (env-restore env0 env1) $ Some _ t))))
                          (elab-let sugar args (MkLetParts _ binders rhs wr) env0b ctx tele))
                        ((StDefLvl)
                          (match many args (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
                            ((Nil c) (values (env-error envl "def-lvl needs a name") ctx $ SNone _))
                            ((Cons c n more)
                              (let (many env2) (many x) $ mint-level envl $ name-or-anon $ raw-name n)
                              (values env2 ctx $ SNone _))))
                        ((StDefFns) (elab-def-fns sugar args envl ctx))
                        ((StDefAdts)
                          (let (many env3) (many headers) (many tids) $ elab-adt-headers sugar args envl)
                          (let (many env4) (many consts) $ define-adts sugar args headers env3 tids)
                          (match many (env-run-pos env4) (((Env) e0) ((List $ List $ Bin) c0) ((StmtCode ctx c0) sc0))
                            ((BTrue) (values (set-const-states consts env4) ctx $ SNone _))
                            ((BFalse)
                              (let (many ms) (many ids) (erased ipk) (many codes) (erased cpk) $ consts-codes ctx consts)
                              (values env4 (Cons _ ids ctx) $ SLet _ ms ids ipk $ CValues _ ms codes cpk))))
                        ((StComptimeMatch) (let (many env2) (many sc) $ elab-comptime-match ctx envl args) (values env2 ctx sc))
                        ((StLetMatch) (elab-let-match sugar args envl ctx))
                        ((StUnary) (elab-unary sugar args envl ctx)))) (else (values bad ctx $ SNone _)))))))) (else (values bad ctx $ SNone _))))
    (values (env-back env env2) ctx2 sc))

  ; let-match (section 16, ASSUMPTIONS 99-100): a one-constructor match binding outward, its fields at the
  ; scrutinee's own erasure; erased or run at once it leaves no code, else one branch wraps the rest.
  (many elab-let-match : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
    (let (many bad) $ env-error env "malformed let-match: expected (let-match <multiplicity> x (C field ...))")
    (match many args _
      ((Nil a) (values bad ctx $ SNone _))
      ((Cons a mraw more)
        (match many more _
          ((Nil b) (values bad ctx $ SNone _))
          ((Cons b scrut more2)
            (match many more2 _
              ((Nil c) (values bad ctx $ SNone _))
              ((Cons c pat more3)
                (match many more3 _
                  ((Cons d x more4) (values bad ctx $ SNone _))
                  ((Nil d)
                    (match many (raw-items pat) _
                      ((Nil e) (values bad ctx $ SNone _))
                      ((Cons e craw fields)
                        (let (many env0) (many smult) $ mult-checked env mraw)
                        (let (many env1a) (many srs) (many scode) (erased lock) $ elab-expr sugar scrut env0 ctx (Cons _ smult $ Nil _) no-tele $ CCPlain)
                        (let (many sres) $ first-res _ _ srs lock)
                        (let (many env1) $ settle-res env1a sres)
                        (match many (type-head env1 $ res-ty sres) _
                          ((None f) (values (env-error env1 $ str-cat3 "cannot match on " (show-t env1 $ res-term sres) $ str-cat " : " $ show-t env1 $ res-ty sres) ctx $ SNone _))
                          ((Some f tid)
                            (let (many env2) (many found) $ find-matchable env1 tid)
                            (match many found _
                              ((None g) (values (env-error env2 $ str-cat (name-of env2 tid) " has no Matchable in scope") ctx $ SNone _))
                              ((Some g info)
                                (match many info _
                                  ((MkMatchInfo mid disc mctors rank)
                                    (let (many (Env) env3)
                                      (match many (nat-cmp (list-length _ mctors) 1) _
                                        ((CEq eq-t eq-r eq-x) env2)
                                        (else (env-error env2 $ str-cat3 (name-of env2 tid) " has " $ str-cat (nat-str $ list-length _ mctors) " constructors, so it needs an ordinary match"))))
                                    (let (many env4) (many c) $ ctor-var env3 craw)
                                    (let (many env5) (many mk) $ marker-checked env4 tid mctors c)
                                    (let (many (Env) env6) $ match many mk _ ((Erased) (env-error env5 $ str-cat (name-of env5 c) " is phantom")) ((Many) env5))
                                    (let (many ctele) (many ret) $ ctor-type env6 c)
                                    (let (many (Env) env7)
                                      (match many (nat-cmp (list-length _ fields) $ list-length _ ctele) _
                                        ((CEq eq-t eq-r eq-x) env6)
                                        (else (env-error env6 $ str-cat3 (name-of env6 c) " has " $ str-cat (nat-str $ list-length _ ctele) " fields"))))
                                    (let (many mults) $ under-list (tele-mults ctele) smult)
                                    (let (many ss) $ shapes mctors env7)
                                    (let (many run) $ and (env-run-pos env7) $ and (mult-is-many smult) $ list-is-empty _ $ env-errors env7)
                                    (let (many (Maybe $ List $ State) states)
                                      (match many smult _
                                        ((Erased) (None _))
                                        ((Many)
                                          (match many ctx (((Maybe $ List $ State) st0))
                                            ((Cons z1 z2 z3) (None _))
                                            ((Nil z1)
                                              (match many (and (env-run-pos env7) $ list-is-empty _ $ env-errors env7) (((Maybe $ List $ State) st0))
                                                ((BFalse) (None _))
                                                ((BTrue)
                                                  (match many (ctor-of env7 c) (((Maybe $ List $ State) st0))
                                                    ((None h) (None _))
                                                    ((Some h ct)
                                                      (let (many i) (many vs) $ destruct ct $ vals-one $ run-code _ scode)
                                                      (let (many sv) (erased lsv) $ spread mults vs)
                                                      (Some _ $ states-of sv))))))))))
                                    (let (many env8) (many fids) (erased lock) $ open-tele ctele env7 (Some _ $ raw-names fields) (Some _ mults) states (Nil _) $ BFalse)
                                    (let (many (Env) env9) $ match many run _ ((BTrue) (trace-many-fields fids env8)) ((BFalse) env8))
                                    (match many (refine env9 sres c fids ret) _
                                      ((UContra msg) (values (env-error env9 $ str-cat3 "the scrutinee contradicts the facts in force (" msg ")") ctx $ SNone _))
                                      ((UOk env10)
                                        (match many smult _
                                          ((Erased) (values env10 ctx $ SNone _))
                                          ((Many)
                                            (match many run _
                                              ((BTrue) (values env10 ctx $ SNone _))
                                              ((BFalse)
                                                (let (many mfids) $ many-of mults fids)
                                                (values env10 (Cons _ mfids ctx) $ SMatch _ scode (match-shape env10 ctx mid $ tagged-of disc ss) (discriminant ss c) mfids))))))))))))))))))))))))

  ; unary (SUGAR.md 5): the literals checked in the reference's order, then the let-match the form stands
  ; for, written out as there.
  (many elab-unary : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
    (let (many arity-error) $ env-error env "unary takes one or two literals")
    (match many args _
      ((Nil a) (values arity-error ctx $ SNone _))
      ((Cons a araw rest)
        (let (many env1) (many ea) $ numeral-entry env araw)
        (match many ea _
          ((None b) (values env1 ctx $ SNone _))
          ((Some b pa)
            (match many pa _
              ((MkPair s t za xa)
                (let (many (Env) env2) (many (Maybe $ Nat) lo)
                  (match many rest _
                    ((Nil c) (values env1 $ Some _ 0))
                    ((Cons c braw rest2)
                      (match many rest2 (((Env) e0) ((Maybe $ Nat) l0))
                        ((Cons d x rest3) (values arity-error $ None _))
                        ((Nil d)
                          (let (many env2) (many eb) $ numeral-entry env1 braw)
                          (match many eb (((Env) e0) ((Maybe $ Nat) l0))
                            ((None e) (values env2 $ None _))
                            ((Some e pb)
                              (match many pb (((Env) e0) ((Maybe $ Nat) l0))
                                ((MkPair s2 t2 zb xb)
                                  (match many (nat-lt zb za) (((Env) e0) ((Maybe $ Nat) l0))
                                    ((BTrue) (values env2 $ Some _ zb))
                                    ((BFalse) (values (env-error env2 $ str-cat3 "unary: " (nat-str za) $ str-cat " does not exceed " $ nat-str zb) $ None _))))))))))))
                (match many lo _
                  ((None c) (values env2 ctx $ SNone _))
                  ((Some c l)
                    (let (many k) $ nat-sub za l)
                    (match many (nat-lt 4096 k) _
                      ((BTrue) (values (env-error env2 $ str-cat3 "unary: " (nat-str k) " successors is beyond the limit") ctx $ SNone _))
                      ((BFalse)
                        (let (many (Bool) floored) $ match many rest _ ((Nil d) (BFalse)) ((Cons d x rest2) (BTrue)))
                        (match many sugar _
                          ((Zero) (values (env-error env2 "internal: a generated form contains sugar") ctx $ SNone _))
                          ((Succ k)
                            (let (many gen) $ unary-source za l floored)
                            (let (many env3) (many ctx2) (many sc) $ elab-stmt k gen (generated-form gen env2) ctx)
                            (values (leave-prelude env2 env3) ctx2 sc))))))))))))))

  ; distinct (SUGAR.md 5): a match on numeral-inj's Eq, once the two literals are checked to be different
  ; spellings of one canonical value.
  (many elab-distinct : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (List $ Res) ress)
    (let (many none) $ Nil $ Res)
    (let (many arity-error) $ env-error env "distinct takes two literals")
    (match many args _
      ((Nil a) (values arity-error none))
      ((Cons a araw rest)
        (match many rest _
          ((Nil b) (values arity-error none))
          ((Cons b braw rest2)
            (match many rest2 _
              ((Cons c x rest3) (values arity-error none))
              ((Nil c)
                (let (many env1) (many ea) $ numeral-entry env araw)
                (let (many env2) (many eb) $ numeral-entry env1 braw)
                (match many ea _
                  ((None d) (values env2 none))
                  ((Some d pa)
                    (match many eb _
                      ((None e) (values env2 none))
                      ((Some e pb)
                        (match many pa _
                          ((MkPair s t za xa)
                            (match many pb _
                              ((MkPair s2 t2 zb xb)
                                (match many (nat-cmp za zb) _
                                  ((CEq eq-t eq-r eq-x) (values (env-error env2 $ str-cat3 "distinct: " (nat-str za) " is the same literal twice") none))
                                  (else
                                    (match many (equal-env env2 (TVar xa) $ TVar xb) _
                                      ((BFalse) (values (env-error env2 $ str-cat3 "distinct: " (nat-str za) $ str-cat3 " and " (nat-str zb) " do not canonicalize equally here") none))
                                      ((BTrue)
                                        (match many sugar (((Env) e0) ((List $ Res) rs0))
                                          ((Zero) (values (env-error env2 "internal: a generated form contains sugar") none))
                                          ((Succ k)
                                            (let (many gen) $ distinct-source za zb)
                                            (let (many env3) (many ress) (many code) (erased lock) $ elab-expr k gen (generated-form gen env2) ctx erased-one no-tele $ CCPlain)
                                            (values (leave-prelude env2 env3) ress))))))))))))))))))))))

  ; let (section 9): binders, then the right-hand side; run at once in run position (section 34); an
  ; annotation is a checked redundancy.
  ; Binders that all carry a type or an is clause are the telescope the right-hand side is expected to
  ; produce (SUGAR.md 6); the check of each binder against its value stays as it was.
  (many elab-let : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (subterm many (LetParts args) parts) (many (Env) env0) (many (List $ List $ Bin) ctx) (many (Maybe $ List $ Entry) tele) -> (many (Env) r) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
    (match many parts _
      ((MkLetParts z binders rhs wr)
        (let (many env1) $ check-binder-mults _ binders env0)
        (let (many expect) (erased lbe) $ src-mults _ binders)
        (let (many inner) (many ress) (many code) (erased lock) $ elab-body sugar args rhs wr env1 ctx expect tele)
        (let (many run) $ env-run-pos env1)
        (let (many (Vals expect) vals)
          (match many ctx _
            ((Cons z1 z2 z3) (vals-of expect $ VToken))
            ((Nil z1)
              (match many (and run $ and (mult-is-many $ pos-mult expect) $ list-is-empty _ $ env-errors inner) _
                ((BTrue) (run-code _ code))
                ((BFalse) (vals-of expect $ VToken))))))
        (let (many svals) (erased lv) $ vals-spread _ vals)
        (let (many env2) (many ids) (erased lids) $ bind-let sugar args binders (env-restore env1 inner) ress svals (lockstep-trans _ _ _ _ _ _ lbe lock) (lockstep-trans _ _ _ _ _ _ lbe lv) run tele $ Nil _)
        (let (many many-ids) (erased pk) $ picked-of _ expect ids $ lockstep-trans _ _ _ _ _ _ (lockstep-sym _ _ _ _ lbe) lids)
        (match many (or run $ list-is-empty _ many-ids) _
          ((BTrue) (values env2 ctx $ SNone _))
          ((BFalse) (values env2 (Cons _ many-ids ctx) $ SLet _ expect many-ids pk code))))))

  (many bind-let : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ SrcEntry root) binders) (many (Env) env) (many (List $ Res) ress) (many (List $ Value) vals) (erased (Lockstep (SrcEntry root) (Res) binders ress) lr) (erased (Lockstep (SrcEntry root) (Value) binders vals) lv) (many (Bool) run) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) ->
      (many (Env) r) (many (List $ Bin) ids) (erased (Lockstep (SrcEntry root) (Bin) binders ids) lids)
    (match many binders _
      ((Nil a) (values env (Nil _) (LsNil _ _)))
      ((Cons a b brest)
        (match many b _
          ((MkSrcEntry rt sub smult ssg name)
            (let (many (Res) r) (many (List $ Res) rrest) (erased (Lockstep (SrcEntry root) (Res) brest rrest) lr2)
              (match erased lr _ ((LsCons ta tb x y xs ys p) (match many ress _ ((Cons c r rs) (values r rs p))))))
            (let (many (Value) v) (many (List $ Value) vrest) (erased (Lockstep (SrcEntry root) (Value) brest vrest) lv2)
              (match erased lv _ ((LsCons ta tb x y xs ys p) (match many vals _ ((Cons c v vs) (values v vs p))))))
            (let (many (Mult) mult) $ match many smult _ ((None c) (Many)) ((Some c m) m))
            (let (many (Env) env1a) (many (Maybe $ List $ Entry) trest)
              (match many tele _
                ((Some c es)
                  (match many es (((Env) e0) ((Maybe $ List $ Entry) t0))
                    ((Nil d) (values env no-tele))
                    ((Cons d e erest) (values (check-sg env (sg-inst done $ entry-sg e) r) $ Some _ erest))))
                ((None c)
                  (match many ssg (((Env) e0) ((Maybe $ List $ Entry) t0))
                    ((None d) (values env no-tele))
                    ((Some d s)
                      (match many s (((Env) e0) ((Maybe $ List $ Entry) t0))
                        ((SrcTy rt2 t p) (let (many env1) (many ty) (many tyty) $ elab-term sugar (subterm p) t env (BTrue) no-tele) (values (check-sg env1 (SgTy ty) r) no-tele))
                        ((SrcIs rt2 t p) (let (many env1) (many ty) (many tyty) $ elab-term sugar (subterm p) t env (BFalse) no-tele) (values (check-sg env1 (SgIs ty tyty) r) no-tele))))))))
            (let (many env1) $ settle-res env1a r)
            (let (many (State) st)
              (match many run _
                ((BTrue) (SConst v))
                ((BFalse)
                  (match many (res-term r) (((State) s0))
                    ((TVar y) (entry-state env1 y)) (else (SDyn))))))
            (let (many env2) (many x) $ bind env1 (name-or-anon name) mult st (res-ty r) (Some _ $ res-term r) coercible-id)
            (let (many (Env) env3)
              (match many (and run $ mult-is-many mult) _
                ((BTrue) (env-push-trace env2 $ TrConst x v))
                ((BFalse) env2)))
            (let (many env4) (many ids) (erased lk) $ bind-let sugar root brest env3 rrest vrest lr2 lv2 run trest $ Cons _ (res-term r) done)
            (values env4 (Cons _ x ids) (LsCons _ _ b x brest ids lk)))))))

  ; def-fns (sections 7, 27): headers bound Dyn, each body elaborated at the block's level under its own
  ; subterm parameters and checked against its return telescope; closures minted Const in run position.
  (many elab-def-fns : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (List $ List $ Bin) ctx2) (many (StmtCode ctx ctx2) sc)
    (match many args _
      ((Nil a) (values (env-error env "def-fns needs a level") ctx $ SNone _))
      ((Cons a lvraw fns)
        (let (many (Env) env2) (many (Bin) lvl)
          (match many (is-underscore lvraw) _
            ((BTrue) (mint-level env $ None _))
            ((BFalse) (let (many env2) (many t) (many ty) $ elab-term sugar lvraw env (BFalse) no-tele) (level-var-checked env2 t))))
        (let (many env3) (many headers) $ elab-headers sugar fns env2 lvl)
        (let (many env4) (many gids) (many fids) $ bind-headers _ headers env3 lvl)
        (let (many env5) (many fns2) (erased lk) $ define-fns sugar fns headers env4 ctx gids gids fids lvl $ env-run-pos env4)
        (let (many group) $ MkGroup _ gids fns2 lk)
        (match many gids _
          ((Nil z0) (values env5 ctx $ SNone _))
          ((Cons z0 g0 grest)
            (match many ctx _
              ((Nil z1)
                (match many (close-group _ _ group $ VNil) _
                  ((VFrame z2 ids vs lkv rest)
                    (let (many env6) $ set-fn-states ids vs lkv env5)
                    (values (env-push-trace env6 $ TrFns _ group) ctx $ SNone _))))
              ((Cons z1 z2 z3) (values env5 (Cons _ gids ctx) $ SLetRec _ _ group))))))))

  (many elab-headers : (subterm many (Nat) sugar) (subterm many (List $ Raw) fns) (many (Env) env) (many (Bin) lvl) -> (many (Env) r) (many (Headers fns) hs)
    (match many fns _
      ((Nil a) (values env $ HStop _))
      ((Cons a f rest)
        (let (many envl) $ env-at env $ raw-line f)
        (let (many bad) $ env-error envl "malformed function definition")
        (match many f _
          ((RList lq items)
            (match many items _
              ((Nil b) (values bad $ HStop _))
              ((Cons b mraw items1)
                (let (many env0) (many mult) $ mult-checked envl mraw)
                (let (many isabs) (many isext) (many items2) (erased w2) $ take-marks items1 _ (WIn items1 items $ prove-subterm items1 items) env0 (MkAbsurd) $ MkExtern)
                (match many items2 _
                  ((Nil c) (values (env-error env0 "malformed function header") $ HStop _))
                  ((Cons c nraw items3)
                    (let (many name) $ raw-name nraw)
                    (match many items3 _
                      ((Nil d) (values (env-error env0 "malformed function header") $ HStop _))
                      ((Cons d colon sg)
                        (let (many (Env) env1) $ match many (is-mark env0 colon $ MkColon) _ ((BTrue) env0) ((BFalse) (env-error env0 "malformed function header")))
                        (let (erased psg) $ subterm-trans (prove-subterm sg items2) $ within-in _ _ _ _ w2 $ prove-subterm items f)
                        (let (many ps) (many after) (erased wa) $ split-arrow sg _ (WHere sg) env1)
                        (let (many rs) (many body) (erased wb) $ split-returns after _ wa env1)
                        (let (many env2) (many params) (many rets) $ elab-fn-type sugar (subterm (subterm-trans psg $ prove-subterm f fns)) sg one-step (MkPair _ _ ps rs) env1)
                        (let (many found) $ extern-of name)
                        (let (many (Env) env2b)
                          (match many found _
                            ((None z) env2)
                            ((Some z se)
                              (match many se _
                                ((MkSomeExtern n e)
                                  (match many (and isext $ not $ nat-eq (many-count params) $ ext-arity _ e) _
                                    ((BFalse) env2)
                                    ((BTrue) (env-error env2 $ str-cat3 "the extern implementation of " name $ str-cat3 " takes " (nat-str $ ext-arity _ e) $ str-cat3 " arguments, its model " (nat-str $ many-count params) ""))))))))
                        (let (many (Env) env3) $ match many isext _ ((BTrue) (claim-extern env2b name $ is-some _ found)) ((BFalse) env2b))
                        (let (many (Maybe $ SomeExtern) impl) $ match many isext _ ((BTrue) found) ((BFalse) (None _)))
                        (let (many env4) (many hs) $ elab-headers sugar rest (env-back env env3) lvl)
                        (values env4 $ HCons _ _ (MkHeader _ name mult isabs impl params rets body $ within-in body sg (Raw) f wb psg) hs)))))))) (else (values bad $ HStop fns))))))

  (many define-fns : (subterm many (Nat) sugar) (subterm many (List $ Raw) fns) (subterm many (Headers fns) headers) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Bin) gall) (many (List $ Bin) gids) (many (Bound fns headers gids) fids) (many (Bin) lvl) (many (Bool) top) ->
      (many (Env) r) (many (List $ Pair (Bin) $ Func gall ctx) fns2) (erased (Lockstep (Bin) (Pair (Bin) $ Func gall ctx) gids fns2) lk)
    (match many fns _
      ((Nil a) (match many fids _ ((BStop z) (values env (Nil _) (LsNil _ _)))))
      ((Cons a f rest)
        (match many headers _
          ((HStop z) (match many fids _ ((BStop z2) (values env (Nil _) (LsNil _ _)))))
          ((HCons g r h hrest)
            (match many fids _
              ((BMany g3 r3 h3 hs3 grest0 x xrest)
                (match many gids _
                  ((Cons zg xg grest)
                    (let (many env3) (many fn) $ define-fn sugar (subterm (prove-subterm f fns)) f h env ctx gall x lvl top)
                    (let (many env4) (many more) (erased lk) $ define-fns sugar rest hrest env3 ctx gall grest xrest lvl top)
                    (values env4 (Cons _ (MkPair _ _ x fn) more) (LsCons _ _ x (MkPair _ _ x fn) grest more lk)))))
              ((BErased g3 r3 h3 hs3 grest0 x xrest)
                (let (many env3) (many fn) $ define-fn sugar (subterm (prove-subterm f fns)) f h env ctx gall x lvl top)
                (define-fns sugar rest hrest env3 ctx gall gids xrest lvl top))))))))

  ; One function's body checked at its level under its parameters, the group's frame and the defining scope,
  ; its marks validated, and its delegate proof bound where it has one.
  (many define-fn : (subterm many (Nat) sugar) (subterm many (Raw) f) (many (Header f) h) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Bin) gall) (many (Bin) x) (many (Bin) lvl) (many (Bool) top) ->
      (many (Env) r) (many (Func gall ctx) fn)
    (match many h _
      ((MkHeader g2 name mult isabs impl params rets body pb)
        (let (many ty) $ TFn (TVar lvl) params rets)
        (let (many envb0) (many pids) (erased lock) $ open-tele params (env-set-run-pos env $ BFalse) (None _) (None _) (None _) (Nil _) $ BFalse)
        (let (many envb) $ env-enter-body envb0 lvl $ subterm-params params pids)
        (let (many rms) $ under-list (tele-mults rets) mult)
        (let (many mps) $ many-of (tele-mults params) pids)
        (let (many bctx) $ Cons _ mps $ Cons _ gall ctx)
        (let (many (Env) envb2) (many (Code bctx rms) code)
          (match many isabs _
            ((BTrue)
              (let (many envb1) (many ress) (many code) (erased lock) $ elab-body sugar (subterm pb) body body (WHere _) envb bctx erased-one no-tele)
              (let (many envb2) $ check-empty (settle-res envb1 $ first-res _ _ ress lock) $ res-ty $ first-res _ _ ress lock)
              (values envb2 $ CAbsurd _ rms))
            ((BFalse)
              (let (many pvars) $ tvars-rev pids $ Nil _)
              (let (many tele) $ instantiate-tele pvars rets)
              (let (many envb1) (many ress) (many code) (erased lock) $ elab-body sugar (subterm pb) body body (WHere _) envb bctx rms (Some _ tele))
              (let (many envb2) $ check-results-count envb1 rets ress pvars)
              (values envb2 $ match many mult (((Code bctx rms) c0)) ((Erased) (CErased _ rms)) ((Many) code)))))
        (let (many envb3) (many code2) (many delegated) $ check-marks envb2 bctx mps rms code)
        (let (many env2) $ env-discard env envb3)
        (let (many (Env) env3)
          (match many delegated _
            ((None c) env2)
            ((Some c callee)
              (let (many env3) (many px) $ bind env2 (None _) (Erased) (SDyn) (proof-type coercible-id $ Cons _ ty $ Cons _ (TVar x) $ Cons _ (type-of env2 callee) $ Cons _ (TVar callee) $ Nil _) (None _) coercible-id)
              env3)))
        (values env3 $ MkFunc _ _ rms name x mps code2 impl top))))

  ; def-adts (sections 12, 19, 27): type constructors bound first, each as soon as its header is read so a
  ; later header may mention it, then each type's constructors, Matchable and Newtype; every constructor
  ; returns its own type.
  (many elab-adt-headers : (subterm many (Nat) sugar) (subterm many (List $ Raw) adts) (many (Env) env) -> (many (Env) r) (many (AdtHeaders adts) hs) (many (Tids adts hs) tids)
    (match many adts _
      ((Nil a) (values env (AStop _) $ TStop _))
      ((Cons a adt rest)
        (let (many envl) $ env-at env $ raw-line adt)
        (let (many bad) $ env-error envl "malformed def-adts entry")
        (match many adt _
          ((RList lq items)
            (match many items _
              ((Nil b) (values bad (AStop _) $ TStop _))
              ((Cons b nraw items1)
                (let (many name) $ raw-name nraw)
                (match many items1 _
                  ((Nil c) (values bad (AStop _) $ TStop _))
                  ((Cons c colon sg)
                    (let (many (Env) env0) $ match many (is-mark envl colon $ MkColon) _ ((BTrue) envl) ((BFalse) bad))
                    (let (many ps) (many after) (erased wa) $ split-arrow sg _ (WHere sg) env0)
                    (match many after _
                      ((Nil d) (values (env-error env0 "malformed def-adts entry") (AStop _) $ TStop _))
                      ((Cons d tyraw after2)
                        (match many after2 _
                          ((Nil f) (values (env-error env0 "malformed def-adts entry") (AStop _) $ TStop _))
                          ((Cons f draw after3)
                            (let (many env1) (many disc) $ disc-of-checked env0 draw)
                            (let (many nt) (many ext) (many cs) (erased wc) $ take-marks after3 _ (within-step after3 after sg (prove-subterm after3 after) wa) env1 (MkNewtypeMark) $ MkExtern)
                            (let (many tyraws) $ Cons _ (MkSub _ tyraw $ in-within (Raw) tyraw after sg (prove-subterm tyraw after) wa) $ Nil _)
                            (let (many env2) (many ty) $ elab-tyctor sugar sg one-step (MkPair _ _ ps tyraws) env1)
                            (let (many (State) st) $ match many (env-run-pos env2) _ ((BTrue) (SConst $ VToken)) ((BFalse) (SDyn)))
                            (let (many env2b) (many x) $ bind env2 (Some _ name) (Erased) st ty (None _) coercible-id)
                            (let (many env3) (many hs) (many tids) $ elab-adt-headers sugar rest $ env-back env env2b)
                            (let (many h) $ MkAdtHeader _ name disc nt ext cs $ within-in cs sg (Raw) adt wc $ prove-subterm sg adt)
                            (values env3 (ACons _ _ h hs) $ TCons _ _ _ _ x tids)))))))))) (else (values bad (AStop adts) $ TStop adts))))))

  (many define-adts : (subterm many (Nat) sugar) (subterm many (List $ Raw) adts) (subterm many (AdtHeaders adts) headers) (many (Env) env) (many (Tids adts headers) tids) -> (many (Env) r) (many (List $ Pair (Bin) $ Value) consts)
    (match many adts _
      ((Nil a) (values env $ Nil _))
      ((Cons a adt rest)
        (match many headers _
          ((AStop z) (values env $ Nil _))
          ((ACons g r h hrest)
            (match many tids _
              ((TCons g3 r3 h3 hs3 tid trest)
                (match many h _
                  ((MkAdtHeader g2 name disc nt ext ctors pc)
                    (let (many env2) (many mcpairs) $ elab-ctors sugar (subterm (subterm-trans pc $ prove-subterm adt adts)) ctors env tid)
                    (let (many mctors) $ mctors-of mcpairs)
                    (let (many ss) $ shapes mctors env2)
                    (let (many tagged) $ tagged-of disc ss)
                    (let (many found) $ ext-type-of name)
                    (let (many (Env) env2b) $ match many ext _ ((BTrue) (claim-extern env2 name $ is-some _ found)) ((BFalse) env2))
                    (let (many (Maybe $ ExtType) extname) $ match many ext _ ((BTrue) found) ((BFalse) (None _)))
                    (let (many records) $ ctor-records (non-phantom ss) env2b 0 tagged extname)
                    (let (many adt2) $ MkAdt name tagged records extname)
                    (let (many cvals) $ ctor-values records)
                    (let (many env3) (many mid) $ bind env2b (None _) (Many) (SConst $ VMatchable adt2) (TMatchable disc (TVar tid) mctors) (None _) coercible-id)
                    (let (many (Env) env4)
                      (match many nt _
                        ((BFalse) env3)
                        ((BTrue)
                          (match many (wrapper disc ss) (((Env) e0))
                            ((None c) (env-error env3 $ str-cat name " is not of newtype shape (section 38)"))
                            ((Some c w) (let (many env4) (many nx) $ bind env3 (None _) (Erased) (SDyn) (TNewtype $ TVar w) (None _) coercible-id) env4)))))
                    (let (many env5) (many more) $ define-adts sugar rest hrest env4 trest)
                    (let (many all) (erased cat) $ list-append _ cvals $ Cons _ (MkPair _ _ mid $ VMatchable adt2) more)
                    (values env5 all))))))))))

  (many elab-ctors : (subterm many (Nat) sugar) (subterm many (List $ Raw) ctors) (many (Env) env) (many (Bin) tid) -> (many (Env) r) (many (List $ Pair (Mult) $ Bin) cs)
    (match many ctors _
      ((Nil a) (values env $ Nil _))
      ((Cons a craw rest)
        (let (many envl) $ env-at env $ raw-line craw)
        (let (many bad) $ env-error envl "malformed constructor")
        (let (many (Env) env0) (many (Maybe $ CtorParts craw) parsed)
          (match many craw _
            ((RList lq items)
              (match many items (((Env) e0) ((Maybe $ CtorParts craw) p0))
                ((Nil b) (values bad $ None _))
                ((Cons b mraw items1)
                  (let (many env0) (many mult) $ mult-checked envl mraw)
                  (match many items1 (((Env) e0) ((Maybe $ CtorParts craw) p0))
                    ((Nil c) (values (env-error env0 "malformed constructor") $ None _))
                    ((Cons c nraw more)
                      (match many more (((Env) e0) ((Maybe $ CtorParts craw) p0))
                        ((Nil d) (values (env-error env0 "malformed constructor") $ None _))
                        ((Cons d colon sg)
                          (let (many env1) $ match many (is-mark env0 colon $ MkColon) (((Env) e0)) ((BTrue) env0) ((BFalse) (env-error env0 "malformed constructor")))
                          (values env1 $ Some _ $ MkCtorParts _ mult (raw-name nraw) sg $ prove-subterm sg craw)))))))) (else (values bad $ None $ CtorParts craw))))
        (match many parsed _
          ((None b) (elab-ctors sugar rest (env-back env env0) tid))
          ((Some b cp)
            (match many cp _
              ((MkCtorParts z mult name sg psg)
                (let (many ps) (many after) (erased wa) $ split-arrow sg _ (WHere sg) env0)
                (let (many env2) (many tele) (many ret) (many ty) $ elab-valctor sugar (subterm (subterm-trans psg $ prove-subterm craw ctors)) sg one-step (MkPair _ _ ps $ subs-of after _ wa) env0)
                (let (many (Env) env2b)
                  (match many (type-head env2 ret) _
                    ((None c) (env-error env2 $ str-cat3 name " must return an application of " $ name-of env2 tid))
                    ((Some c t) (match many (bin-cmp t tid) (((Env) e0)) ((CEq eq-t eq-r eq-x) env2) (else (env-error env2 $ str-cat3 name " must return an application of " $ name-of env2 tid))))))
                (let (many (Env) env2c)
                  (match many (and (not $ mult-is-many mult) $ not $ nat-is-zero $ many-count tele) _
                    ((BTrue) (env-warn env2b $ str-cat3 "warning: phantom constructor " name " has a many field"))
                    ((BFalse) env2b)))
                (let (many env3) $ env-discard env0 env2c)
                (let (many (State) st) $ match many mult _ ((Erased) (match many (env-run-pos env3) (((State) s0)) ((BTrue) (SConst $ VToken)) ((BFalse) (SDyn)))) ((Many) (SDyn)))
                (let (many env4) (many c) $ bind env3 (Some _ name) mult st ty (None _) coercible-id)
                (let (many env5) (many cs) $ elab-ctors sugar rest (env-back env env4) tid)
                (values env5 $ Cons _ (MkPair _ _ mult c) cs))))))))
  ; tail and delegate wrap a call (section 9, ASSUMPTIONS 9); the compiled code must be that call.
  (many elab-marked : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (CC) cc) (many (Sp) sp) -> (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
    (let (many (Env) env1) $ match many (pos-mult expect) _ ((Erased) (env-error env $ str-cat (sp-name sp) " in an erased position")) ((Many) env))
    (match many args _
      ((Nil a) (values (env-error env1 $ str-cat (sp-name sp) " marks a function call, not nothing") (Nil _) $ CError _ expect "mark"))
      ((Cons a call rest)
        (let (many env2) (many ress) (many code) (erased lock) $ elab-expr sugar call env1 ctx expect tele cc)
        (let (many (Bool) ok)
          (match many code _
            ((CApp c0 ms f as cc2) (cc-eq cc cc2))
            ((CLet c0 ms ns ids pk rhs body) (match many rhs (((Bool) b0)) ((CApp c0 ms2 f as cc2) (cc-eq cc cc2)) (else (BFalse)))) (else (BFalse))))
        (match many ok _
          ((BTrue) (values env2 ress code))
          ((BFalse) (values (env-error env2 $ str-cat3 (sp-name sp) " marks a function call, not " $ show-r call) ress code))))))

  ; Each entry of a values against its entry of the telescope expected, instantiated with the entries before it.
  (many elab-values : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (List $ Term) done) -> (many (Env) r) (many (List $ Res) ress) (many (List $ Code ctx many-one) codes) (erased (Picked (Code ctx many-one) expect codes) pk)
    (match many expect _
      ((Nil a) (values env (Nil _) (Nil _) (PkNil _)))
      ((Cons a m mrest)
        (match many args _
          ((Nil b)
            (let (many codes) (erased pk) $ codes-missing ctx expect)
            (values env (Nil _) codes pk))
          ((Cons b arg arest)
            (let (many (Maybe $ List $ Entry) here) (many (Maybe $ List $ Entry) trest)
              (match many tele _
                ((None c) (values no-tele no-tele))
                ((Some c es)
                  (match many es (((Maybe $ List $ Entry) h) ((Maybe $ List $ Entry) t))
                    ((Nil d) (values no-tele no-tele))
                    ((Cons d e erest) (values (Some _ $ Cons _ (entry-with-sg e $ sg-inst done $ entry-sg e) $ Nil _) $ Some _ erest))))))
            (let (many env2) (many rs) (many code) (erased lock) $ elab-expr sugar arg env ctx (Cons _ m $ Nil _) here $ CCPlain)
            (let (many env3) (many ress) (many codes) (erased pk) $ elab-values sugar arest env2 ctx mrest trest $ Cons _ (res-term $ first-res _ _ rs lock) done)
            (let (many codes2) (erased pk2)
              (match many m (((List $ Code ctx many-one) cs) ((Picked (Code ctx many-one) expect cs) p))
                ((Many) (values (Cons _ code codes) (PkMany _ mrest code codes pk)))
                ((Erased) (values codes (PkErased _ mrest codes pk)))))
            (values env3 (Cons _ (first-res _ _ rs lock) ress) codes2 pk2))))))

  (many elab-two-terms : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) -> (many (Env) r) (many (Term) a) (many (Term) aty) (many (Term) b) (many (Term) bty)
    (match many args _
      ((Nil x) (values (env-error env "two arguments expected") (TErr "missing") (TErr "missing") (TErr "missing") $ TErr "missing"))
      ((Cons x araw rest)
        (match many rest _
          ((Nil y) (values (env-error env "two arguments expected") (TErr "missing") (TErr "missing") (TErr "missing") $ TErr "missing"))
          ((Cons y braw more)
            (let (many env2) (many a) (many aty) $ elab-term sugar araw env (BFalse) no-tele)
            (let (many env3) (many b) (many bty) $ elab-term sugar braw env2 (BFalse) no-tele)
            (values (settle (settle env3 a) b) a aty b bty))))))

  ; Two proofs of the given kinds, elaborated erased (ASSUMPTIONS 23).
  (many two-proofs : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) -> (many (Env) r) (many (Res) p) (many (Res) q)
    (match many args _
      ((Nil x) (values (env-error env "two proofs expected") no-res no-res))
      ((Cons x araw rest)
        (match many rest _
          ((Nil y) (values (env-error env "two proofs expected") no-res no-res))
          ((Cons y braw more)
            (let (many env2) (many prs) (many pc) (erased lockp) $ elab-expr sugar araw env ctx erased-one no-tele $ CCPlain)
            (let (many env3) (many qrs) (many qc) (erased lockq) $ elab-expr sugar braw env2 ctx erased-one no-tele $ CCPlain)
            (values (settle (settle env3 $ erased-term prs lockp) $ erased-term qrs lockq) (erased-res prs lockp) $ erased-res qrs lockq))))))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field, each checked against
  ; the field's type on its side (section 38).
  (many coercible-ctor-args : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Entry) tele) (many (List $ Term) src) (many (List $ Term) tgt) (many (Bin) c) -> (many (Env) r) (many (List $ Term) src2) (many (List $ Term) tgt2)
    (let (many wrong) $ env-error env $ str-cat "coercible-ctor: wrong number of arguments for " $ name-of env c)
    (match many tele _
      ((Nil a) (match many args _ ((Nil b) (values env src tgt)) ((Cons b x more) (values wrong src tgt))))
      ((Cons a e rest)
        (match many (entry-mult e) _
          ((Erased)
            (match many args _
              ((Nil b) (values wrong src tgt))
              ((Cons b sraw more)
                (match many more _
                  ((Nil d) (values wrong src tgt))
                  ((Cons d traw args2)
                    (let (many env2) (many s) (many sty) $ elab-term sugar sraw env (BFalse) no-tele)
                    (let (many env3) (many t) (many tty) $ elab-term sugar traw env2 (BFalse) no-tele)
                    (let (many env4) $ check-sg (settle (settle env3 s) t) (sg-inst src $ entry-sg e) $ term-res env3 s sty)
                    (let (many env5) $ check-sg env4 (sg-inst tgt $ entry-sg e) $ term-res env4 t tty)
                    (coercible-ctor-args sugar args2 env5 ctx rest (Cons _ s src) (Cons _ t tgt) c))))))
          ((Many)
            (match many args _
              ((Nil b) (values wrong src tgt))
              ((Cons b praw more)
                (let (many env2a) (many prs) (many pc) (erased lock) $ elab-expr sugar praw env ctx erased-one no-tele $ CCPlain)
                (let (many env2) $ settle env2a $ erased-term prs lock)
                (let (many env3) (many sty) (many s) (many tty) (many t) $ expect-proof4 env2 coercible-id $ erased-res prs lock)
                (let (many env4) $ check-sg env3 (sg-inst src $ entry-sg e) $ MkRes s sty $ Erased)
                (let (many env5) $ check-sg env4 (sg-inst tgt $ entry-sg e) $ MkRes t tty $ Erased)
                (coercible-ctor-args sugar more env5 ctx rest (Cons _ s src) (Cons _ t tgt) c))))))))

  ; match (sections 11, 12, 18): the scrutinee, its Matchable, the annotation, then one branch per
  ; constructor, each refined by its forced facts or refuted by them.
  (many elab-match : (subterm many (Nat) sugar) (subterm many (List $ Raw) args) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
    (let (many bad) (many bad-ress) (many bad-code) $ values (env-error env "malformed match") (Nil $ Res) $ CError ctx expect "match")
    (match many args _
      ((Nil a) (values bad bad-ress bad-code))
      ((Cons a mraw more)
        (match many more _
          ((Nil b) (values bad bad-ress bad-code))
          ((Cons b scrut more2)
            (match many more2 _
              ((Nil c) (values bad bad-ress bad-code))
              ((Cons c ann branches)
                (let (many pos) $ pos-mult expect)
                (let (many env0) (many sm) $ mult-checked env mraw)
                (let (many smult) $ under pos sm)
                (let (many env2a) (many srs) (many scode) (erased lock) $ elab-expr sugar scrut env0 ctx (Cons _ smult $ Nil _) no-tele $ CCPlain)
                (let (many sres) $ first-res _ _ srs lock)
                (let (many env2) $ settle-res env2a sres)
                (match many (type-head env2 $ res-ty sres) _
                  ((None d) (values (env-error env2 $ str-cat3 "cannot match on " (show-t env2 $ res-term sres) $ str-cat " : " $ show-t env2 $ res-ty sres) (Nil _) $ CError _ expect "no head"))
                  ((Some d tid)
                    (let (many env2b) (many found) $ find-matchable env2 tid)
                    (match many found _
                      ((None e) (values (env-error env2b $ str-cat (name-of env2b tid) " has no Matchable in scope") (Nil _) $ CError _ expect "no Matchable"))
                      ((Some e info)
                        (match many info _
                          ((MkMatchInfo mid disc mctors rank)
                            (let (many ss) $ shapes mctors env2b)
                            (let (many tagged) $ tagged-of disc ss)
                            (let (many (Env) env2c)
                              (match many (and (mult-is-many pos) $ and (mult-is-many smult) $ not $ mult-is-many $ entry-mult-of env2b mid) _
                                ((BTrue) (env-error env2b $ str-cat3 "the Matchable for " (name-of env2b tid) " is erased, so a non-erased match cannot take a value of it apart"))
                                ((BFalse) env2b)))
                            (let (many (Env) env3) (many (List $ Entry) ann-tele)
                              (match many (is-underscore ann) _
                                ((BTrue)
                                  (match many tele (((Env) e0) ((List $ Entry) t0))
                                    ((None f) (values (env-error env2c "no telescope to reuse for _") $ Nil _))
                                    ((Some f t)
                                      (match many (tele-has-meta t env2c) (((Env) e0) ((List $ Entry) t0))
                                        ((BTrue) (values (env-error env2c "the telescope _ would reuse still has a _ to infer") t))
                                        ((BFalse) (values env2c t))))))
                                ((BFalse)
                                  (match many ann (((Env) e0) ((List $ Entry) t0))
                                    ((RList lq aitems)
                                      (let (many env3) (many ids) (many t) $ elab-tele sugar aitems one-step (subs-all aitems) env2c (MMExpect expect) (Nil _) (BFalse) $ BTrue)
                                      (let (many env3b) $ env-restore env2c env3)
                                      (let (many (Env) env3c)
                                        (match many tele _
                                          ((None g) env3b)
                                          ((Some g et)
                                            (match many (nat-cmp (list-length _ et) $ list-length _ t) _
                                              (else env3b)
                                              ((CEq eq-t eq-r eq-x) (let (many env3c) (many ok) $ solve-tele et t env3b $ BTrue) env3c)))))
                                      (let (many env3d) $ settle-tele t env3c)
                                      (values env3d $ metaless-tele t env3d)) (else (values (env-error env2c "malformed match annotation") $ Nil $ Entry))))))
                            (let (many (Env) env3b)
                              (match many (nat-cmp (list-length _ ann-tele) $ list-length _ expect) _
                                ((CEq eq-t eq-r eq-x) env3)
                                (else (env-error env3 $ str-cat3 "match annotation has " (nat-str $ list-length _ ann-tele) $ str-cat " entries, position needs " $ nat-str $ list-length _ expect))))
                            (let (many env5) (many real) (many seen) $ elab-branches sugar branches env3b ctx tid sres smult mctors ann-tele expect (Nil _) $ Nil _)
                            (let (many env6) $ check-coverage mctors env5 seen)
                            (let (many env6b) (many first) (many reachable) $ covered-of mctors env6 seen sres smult (None _) $ BFalse)
                            (let (many env6c) (many dflt) $ elab-else sugar branches env6b ctx ann-tele expect first reachable (BFalse) $ None _)
                            (let (many nreal) $ nat-add (list-length _ real) $ match many dflt (((Nat) n0)) ((None f) 0) ((Some f d) 1))
                            (let (many (Env) env7)
                              (match many (and (mult-is-many pos) $ and (or (not tagged) $ not $ mult-is-many smult) $ nat-lt 1 nreal) _
                                ((BTrue) (env-error env6c "a match without a runtime discriminant can have only one real branch"))
                                ((BFalse) env6c)))
                            (let (many (Code ctx expect) code)
                              (match many pos _
                                ((Erased) (CErased _ expect))
                                ((Many)
                                  (match many real (((Code ctx expect) c0))
                                    ((Nil f)
                                      (match many dflt (((Code ctx expect) c0))
                                        ((None g) (CAbsurd _ expect))
                                        ((Some g body)
                                          (match many smult (((Code ctx expect) c0))
                                            ((Erased) (CMatch _ expect (CErased _ many-one) (ShNone _) (Nil _) dflt))
                                            ((Many)
                                              (match many tagged (((Code ctx expect) c0))
                                                ((BFalse) (CMatch _ expect scode (ShNone _) (Nil _) dflt))
                                                ((BTrue) (CMatch _ expect scode (match-shape env7 ctx mid tagged) (Nil _) dflt))))))))
                                    ((Cons f rb more3)
                                      (match many smult (((Code ctx expect) c0))
                                        ((Erased)
                                          (match many more3 (((Code ctx expect) c0))
                                            ((Nil g) (CMatch _ expect (CErased _ many-one) (ShNone _) (real-branches-code _ _ real ss) dflt))
                                            ((Cons g rb2 more4) (CError _ expect "one real branch"))))
                                        ((Many) (CMatch _ expect scode (match-shape env7 ctx mid tagged) (real-branches-code _ _ real ss) dflt))))))))
                            (let (many env8) (many rids) (erased lock) $ open-tele ann-tele env7 (Some _ $ anon-names ann-tele) (None _) (None _) (Nil _) $ BFalse)
                            (values env8 (ress-of rids env8) code))))))))))))))

  ; Each branch: present, refuted automatically with (absurd C), or absurd by proof (section 12).
  (many elab-branches : (subterm many (Nat) sugar) (subterm many (List $ Raw) branches) (many (Env) env) (many (List $ List $ Bin) ctx) (many (Bin) tid) (many (Res) sres) (many (Mult) smult) (many (List $ MCtor) mctors) (many (List $ Entry) ann-tele) (many (List $ Mult) expect) (many (List $ RealBranch ctx expect) acc) (many (List $ Bin) seen) ->
      (many (Env) r) (many (List $ RealBranch ctx expect) real) (many (List $ Bin) seen2)
    (match many branches _
      ((Nil a) (values env (list-rev _ acc) seen))
      ((Cons a braw brest)
        (let (many envl) $ env-at env $ raw-line braw)
        (match many (is-else-branch envl braw) _
          ((BTrue) (elab-branches sugar brest env ctx tid sres smult mctors ann-tele expect acc seen))
          ((BFalse)
        (match many (branch-parts envl braw) _
          ((None b) (elab-branches sugar brest (env-back env $ env-error envl "malformed branch") ctx tid sres smult mctors ann-tele expect acc seen))
          ((Some b bp)
            (let (many (Raw) craw) (many (List $ Raw) fields) (many (Bool) refuted)
              (match many bp _
                ((BPresent z c fs body p) (values c fs $ BFalse))
                ((BRefuted z c) (values c (Nil _) $ BTrue))
                ((BAbsurd z c fs body p) (values c fs $ BFalse))))
            (let (many env1) (many c) $ ctor-var envl craw)
            (let (many env2) (many mk) $ marker-checked envl tid mctors c)
            (let (many (Bool) phantom) $ match many mk _ ((Erased) (BTrue)) ((Many) (BFalse)))
            (let (many ctele) (many ret) $ ctor-type env2 c)
            (let (many (Env) env3)
              (match many (or refuted $ nat-eq (list-length _ fields) $ list-length _ ctele) _
                ((BTrue) env2)
                ((BFalse) (env-error env2 $ str-cat3 (name-of env2 c) " has " $ str-cat (nat-str $ list-length _ ctele) " fields"))))
            (let (many unreachable) $ and phantom $ mult-is-many smult)
            (let (many (List $ Mult) mults) $ match many phantom _ ((BTrue) (all-erased $ tele-mults ctele)) ((BFalse) (under-list (tele-mults ctele) smult)))
            (let (many (List $ Maybe $ String) names) $ match many refuted _ ((BTrue) (anon-names ctele)) ((BFalse) (raw-names fields)))
            (let (many envb) (many fids) (erased lock) $ open-tele ctele (env-set-run-pos env3 $ BFalse) (Some _ names) (Some _ mults) (None _) (Nil _) $ BFalse)
            (let (many mfids) $ many-of mults fids)
            (let (many bctx) $ Cons _ mfids ctx)
            (let (many (Env) env4) (many (List $ RealBranch ctx expect) acc2)
              (match many (refine envb sres c fids ret) _
                ((UContra msg)
                  (match many refuted (((Env) e0) ((List $ RealBranch ctx expect) rs0))
                    ((BTrue) (values (env-discard env3 envb) acc))
                    ((BFalse) (values (env-error (env-discard env3 envb) $ str-cat3 "branch " (name-of env3 c) $ str-cat3 " is refuted; write (absurd " (name-of env3 c) ")") acc))))
                ((UOk envb2)
                  (match many bp (((Env) e0) ((List $ RealBranch ctx expect) rs0))
                    ((BPresent z c2 fs body p)
                      (let (erased q) $ subterm-trans p $ prove-subterm braw branches)
                      (match many unreachable _
                        ((BTrue)
                          (let (many ex) $ all-erased expect)
                          (let (many envb3) (many ress) (many code) (erased lock) $ elab-body sugar (subterm q) body body (WHere _) envb2 bctx ex (Some _ ann-tele))
                          (let (many envb4) $ check-results-count envb3 ann-tele ress $ Nil _)
                          (values (env-discard env3 envb4) acc))
                        ((BFalse)
                          (let (many envb3) (many ress) (many code) (erased lock) $ elab-body sugar (subterm q) body body (WHere _) envb2 bctx expect (Some _ ann-tele))
                          (let (many envb4) $ check-results-count envb3 ann-tele ress $ Nil _)
                          (values (env-discard env3 envb4) (Cons _ (MkRealBranch _ _ c mfids code) acc)))))
                    ((BRefuted z c2) (values (env-error (env-discard env3 envb2) $ str-cat3 "branch " (name-of env3 c) " is not refuted") acc))
                    ((BAbsurd z c2 fs body p)
                      (let (erased q) $ subterm-trans p $ prove-subterm braw branches)
                      (let (many envb2b) (many ress) (many code) (erased lock) $ elab-body sugar (subterm q) body body (WHere _) envb2 bctx erased-one no-tele)
                      (let (many envb3) $ check-empty (settle-res envb2b $ first-res _ _ ress lock) $ res-ty $ first-res _ _ ress lock)
                      (values (env-discard env3 envb3) acc))))))
            (elab-branches sugar brest (env-back env env4) ctx tid sres smult mctors ann-tele expect acc2 $ Cons _ c seen))))))))

  ; The else branch (section 12): at most one, standing for at least one constructor, its body under no forced
  ; facts and erased throughout when none of them could run.
  (many elab-else : (subterm many (Nat) sugar) (subterm many (List $ Raw) branches) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Entry) ann-tele) (many (List $ Mult) expect) (many (Maybe $ Bin) first) (many (Bool) reachable) (many (Bool) seen-else) (many (Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) found) ->
      (many (Env) r) (many (Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) code)
    (match many branches _
      ((Nil a)
        (match many seen-else _
          ((BTrue) (values env found))
          ((BFalse)
            (match many first _
              ((None b) (values env found))
              ((Some b c) (values (env-error env $ str-cat3 "constructor " (name-of env c) " has 0 branches") found))))))
      ((Cons a braw brest)
        (match many (is-else-branch env braw) _
          ((BFalse) (elab-else sugar brest env ctx ann-tele expect first reachable seen-else found))
          ((BTrue)
            (let (many envl) $ env-at env $ raw-line braw)
            (let (many (Env) env2) (many (Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) found2)
              (match many seen-else _
                ((BTrue) (values (env-error envl "a match has at most one else branch") found))
                ((BFalse)
                  (match many first (((Env) e0) ((Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) f0))
                    ((None b) (values (env-error envl "else covers no constructor") found))
                    ((Some b c0)
                      (match many braw (((Env) e0) ((Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) f0))
                        ((RList lq items)
                          (match many items (((Env) e0) ((Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) f0))
                            ((Nil c) (values (env-error envl "malformed branch") found))
                            ((Cons c token body)
                              (match many reachable (((Env) e0) ((Maybe $ Code (Cons (List (Bin)) (Nil (Bin)) ctx) expect) f0))
                                ((BTrue)
                                  (let (many envb) (many ress) (many code) (erased lock) $ elab-body sugar body body (WHere body) (env-set-run-pos envl $ BFalse) (Cons _ (Nil _) ctx) expect (Some _ ann-tele))
                                  (let (many envb2) $ check-results-count envb ann-tele ress $ Nil _)
                                  (values (env-discard envl envb2) $ Some _ code))
                                ((BFalse)
                                  (let (many ex) $ all-erased expect)
                                  (let (many envb) (many ress) (many code) (erased lock) $ elab-body sugar body body (WHere body) (env-set-run-pos envl $ BFalse) (Cons _ (Nil _) ctx) ex (Some _ ann-tele))
                                  (let (many envb2) $ check-results-count envb ann-tele ress $ Nil _)
                                  (values (env-discard envl envb2) $ None _)))))) (else (values (env-error envl "malformed branch") found))))))))
            (elab-else sugar brest (env-back env env2) ctx ann-tele expect first reachable (BTrue) found2))))))

  ; Arguments against a telescope, each at the position's multiplicity and checked against its entry
  ; (section 20); returns the terms innermost first and the code of the many ones in order.
  ; The arguments of an application against [tele] (SUGAR.md 6): a meta stands for each parameter; an
  ; argument written `_` is left to it, and is an error unless erased where it stands; any other is checked
  ; against its parameter and bound to its meta, as a term where [as-term] (section 5's grammar) and as an
  ; expression otherwise. [result], over the metas, is solved against [expect] eagerly, where a `_` is present,
  ; before any argument is read, and again, reporting the mismatch, when a `_` would otherwise stay unsolved
  ; at the closing paren; every `_` is solved by then or refused. Returns the argument terms innermost first.
  (many check-args : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Succ $ Zero) st) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Entry) tele) (many (Mult) pos) (many (Maybe $ List $ Entry) expect) (many (AppResult) result) (many (Bool) as-term) (many (Bool) boundary) ->
      (many (Env) r) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ Code ctx many-one) codes)
    (match many st _
      ((SS sn k)
        (let (many env1) (many metas) (erased lock) $ open-tele tele env (Some _ $ anon-names tele) (Some _ $ all-erased $ tele-mults tele) (None _) (Nil _) $ BTrue)
        (let (many mvars) $ tvars-rev metas $ Nil _)
        (let (many wilds) $ any-wild _ args)
        (let (many env2) $ solve-against env1 expect result mvars wilds $ BFalse)
        (let (many env3) (many acc) (many tys) (many codes) $ check-args-go sugar root args k env2 ctx tele metas lock pos as-term (Nil _) (Nil _) $ Nil _)
        (let (many (Env) env4) $ match many (and boundary $ terms-have-meta acc env3) _ ((BTrue) (solve-against env3 expect result mvars wilds $ BTrue)) ((BFalse) env3))
        (let (many (Env) env5) $ match many boundary _ ((BTrue) (report-unsolved (list-rev _ acc) env4 1)) ((BFalse) env4))
        (values env5 (metaless-list acc env5) (metaless-list tys env5) codes))))

  (many check-args-go : (subterm many (Nat) sugar) (subterm many (List $ Raw) root) (subterm many (List $ Sub root) args) (subterm many (Steps $ Zero) st) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Entry) tele) (many (List $ Bin) metas) (erased (Lockstep (Entry) (Bin) tele metas) lock) (many (Mult) pos) (many (Bool) as-term) (many (List $ Term) acc) (many (List $ Term) tys) (many (List $ Code ctx many-one) codes) ->
      (many (Env) r) (many (List $ Term) acc2) (many (List $ Term) tys2) (many (List $ Code ctx many-one) codes2)
    (match many tele _
      ((Nil a)
        (match many args _
          ((Nil b) (values env acc tys $ list-rev _ codes))
          ((Cons b x more) (values (env-error env $ str-cat "expected fewer arguments, got " $ nat-str $ list-length _ args) acc tys $ list-rev _ codes))))
      ((Cons a e rest)
        (match many args _
          ((Nil b) (values (env-error env $ str-cat "expected " $ str-cat (nat-str $ list-length _ tele) " more arguments, got 0") acc tys $ list-rev _ codes))
          ((Cons b s arest)
            (match erased lock _
              ((LsCons ta tb e0 m0 rest0 mrest0 lp)
              (match many metas _
              ((Cons c m mrest)
                (match many s _
                  ((MkSub z arg p)
                    (let (many mult) $ under pos $ entry-mult e)
                    (let (many sg) $ sg-inst acc $ entry-sg e)
                    (match many (is-underscore arg) _
                      ((BTrue)
                        (let (many (Env) env2)
                          (match many (mult-is-many mult) _
                            ((BTrue) (env-back env $ env-error (env-at env $ raw-line arg) $ str-cat3 "_ stands for an erased argument, and argument " (nat-str $ Succ $ list-length _ acc) " here is not erased"))
                            ((BFalse) env)))
                        (check-args-go sugar root arest st env2 ctx rest mrest lp pos as-term (Cons _ (TVar m) acc) (Cons _ (type-of env2 m) tys) codes))
                      ((BFalse)
                        (let (many (Env) env2) (many (Res) r) (many (Code ctx (Cons (Mult) mult (Nil (Mult)))) code)
                          (match many as-term _
                            ((BTrue)
                              (let (many env2) (many t) (many ty) $ elab-term sugar (subterm p) arg env (BFalse) $ Some _ $ Cons _ (entry-with-sg e sg) $ Nil _)
                              (values env2 (term-res env2 t ty) $ CErased _ $ Cons _ mult $ Nil _))
                            ((BFalse)
                              (let (many env2) (many rs) (many code) (erased lock) $ elab-expr sugar (subterm p) arg env ctx (Cons _ mult $ Nil _) (Some _ $ Cons _ (entry-with-sg e sg) $ Nil _) $ CCPlain)
                              (values env2 (first-res _ _ rs lock) code))))
                        (let (many env3) $ check-sg env2 sg r)
                        (let (many env4) $ check env3 "value" (res-term r) $ TVar m)
                        (check-args-go sugar root arest st env4 ctx rest mrest lp pos as-term (Cons _ (res-term r) acc) (Cons _ (res-ty r) tys)
                          $ match many mult (((List $ Code ctx many-one) l0)) ((Many) (Cons _ code codes)) ((Erased) codes)))))))))))))))

  ; A function call (section 9): a lower-level call carries a Predates proof about the callee's level, a
  ; same-level call a Subterm proof for its decreasing argument; the top level carries neither (section 24).
  (many elab-call : (subterm many (Nat) sugar) (subterm many (List $ Raw) rawargs) (subterm many (Pair (List $ Sub rawargs) $ Ann rawargs) parts) (many (Env) env) (many (List $ List $ Bin) ctx) (many (List $ Mult) expect) (many (Maybe $ List $ Entry) tele) (many (Res) callee) (many (Mult) pos) (many (Code ctx (Cons (Mult) pos (Nil (Mult)))) hcode) (many (Term) lv) (many (List $ Entry) params) (many (List $ Entry) rets) (many (CC) cc) ->
      (many (Env) r) (many (List $ Res) ress) (many (Code ctx expect) code)
    (match many parts _
      ((MkPair x y args ann)
        (let (many (Env) env1)
          (match many (and (mult-is-many pos) $ not $ mult-is-many $ res-erasure callee) _
            ((BTrue) (env-error env $ str-cat3 "erased function " (show-t env $ res-term callee) " called in a non-erased position"))
            ((BFalse) env)))
        (let (many env2) (many acc) (many tys) (many codes) $ check-args sugar rawargs args one-step (check-arity env1 params $ list-length _ args) ctx params pos tele (ARCall rets) (BFalse) $ BTrue)
        (let (many arg-terms) $ list-rev _ acc)
        (let (many env3) $ check-call-proof sugar rawargs ann env2 ctx callee lv params arg-terms $ list-rev _ tys)
        (let (many rmults) $ tele-mults rets)
        (let (many env4) (many ids) (erased lock) $ open-tele rets env3 (Some _ $ anon-names rets) (Some _ $ under-list rmults pos) (None _) acc $ BFalse)
        (let (many (Env) env5) (many (Code ctx expect) code)
          (match many pos _
            ((Erased) (values env4 $ CErased _ expect))
            ((Many)
              (let (many call) $ CApp ctx rmults hcode codes cc)
              (match many (lockstep-dec _ _ expect rmults) (((Env) e0) ((Code ctx expect) c0))
                ((LdNo a b c d) (values env4 $ CError _ expect "size"))
                ((LdYes a b c d lk)
                  (let (many env5) (many bound) (erased bpk) (many kept) (erased kpk) $ projection ctx expect rmults lk env4)
                  (values env5 $ CLet _ rmults _ bound bpk call $ CValues _ expect kept kpk))))))
        (values env5 (ress-of ids env5) code))))

  ; The call-site proof (section 9), read against the current level and enclosing subterm parameters; a bare
  ; call gets its annotation from resolve-ann first.
  (many check-call-proof : (subterm many (Nat) sugar) (subterm many (List $ Raw) rawargs) (subterm many (Ann rawargs) ann) (many (Env) env) (many (List $ List $ Bin) ctx) (many (Res) callee) (many (Term) lv) (many (List $ Entry) params) (many (List $ Term) args) (many (List $ Term) arg-tys) -> (many (Env) r)
    (match many (env-level env) _
      ((None a)
        (match many ann _
          ((AnnNone z) env) (else (env-error env "the top level calls without proofs; drop the decrease annotation (section 24)"))))
      ((Some a cur)
        (let (many same) $ equal-env env lv $ TVar cur)
        (let (many positions) $ subterm-indices params 0)
        (let (many env1) (many ann2) $ resolve-ann env _ ann callee same positions args)
        (match many ann2 _
          ((AnnNone z) env1)
          ((AnnSubterm z i g)
            (match many same _
              ((BFalse) (env-error env1 $ annotation-kind env1 callee same))
              ((BTrue)
                (match many (index-of-nat positions i 0) _
                  ((None b) (env-error env1 $ str-cat3 "argument " (nat-str i) " is not a subterm parameter"))
                  ((Some b kk)
                    (let (many env2) $ check-earlier positions env1 args 0 kk)
                    (match many (list-nth _ (env-subterms env2) kk) _
                      ((NthMiss nt nl ni np) (env-error env2 $ str-cat3 "the enclosing function has no subterm parameter at position " (nat-str kk) ""))
                      ((NthHit nt nl ni counterpart np)
                        (let (many arg) $ nth-term args i)
                        (let (many (Env) env3) (many (Res) pres)
                          (match many g _
                            ((Inferred w) (mint-subterm env2 arg (nth-term arg-tys i) (TVar counterpart) $ type-of env2 counterpart))
                            ((Written w p pp)
                              (let (many env3) (many prs) (many pc) (erased lock) $ elab-expr sugar (subterm pp) p env2 ctx erased-one no-tele $ CCPlain)
                              (values env3 $ erased-res prs lock))))
                        (let (many env4) (many s0) (many s1) (many s2) (many s3) $ expect-proof4 env3 subterm-id pres)
                        (let (many env5) $ check env4 "value" s1 arg)
                        (check env5 "value" s3 $ TVar counterpart))))))))
          ((AnnPredates z g)
            (match many same _
              ((BTrue) (env-error env1 $ annotation-kind env1 callee same))
              ((BFalse)
                (let (many (Env) env2) (many (Res) pres)
                  (match many g _
                    ((Inferred w)
                      (let (many nv-env) (many nv-res) $ values (env-error env1 $ str-cat (show-t env1 lv) " is not a variable") $ MkRes (TErr "level") (TErr "level") $ Erased)
                      (match many (canon-env env1 lv) (((Env) e0) ((Res) r0))
                        ((TVar m) (mint-predates env1 m cur))
                        ((TErr m) (values (env-error env1 m) $ MkRes (TErr m) (TErr m) $ Erased)) (else (values nv-env nv-res))))
                    ((Written w p pp)
                      (let (many env2) (many prs) (many pc) (erased lock) $ elab-expr sugar (subterm pp) p env1 ctx erased-one no-tele $ CCPlain)
                      (values env2 $ erased-res prs lock))))
                (let (many env3) (many p0) (many p1) (many p2) $ expect-proof3 env2 predates-id pres)
                (let (many env4) $ check env3 "value" p2 $ TVar cur)
                (match many (equal-env env4 p1 lv) _
                  ((BTrue) env4)
                  ((BFalse) (env-error env4 $ str-cat3 (show-t env4 $ res-term pres) " : " $ str-cat3 (show-t env4 $ res-ty pres) " does not relate the callee's level " $ show-t env4 lv)))))))))))

; ---- The top level (section 16): statements run as they are elaborated, the final expression consumed;
; only the last form may be an expression (ASSUMPTIONS 12).

(def-fns _ $ many run-toplevel : (subterm many (List $ Raw) items) (many (Env) env) -> (many (Env) r)
  (match many items _
    ((Nil a) env)
    ((Cons a item rest)
      (let (many env2) $ intern-literals item $ env-at env $ raw-line item)
      (match many (is-statement env2 item) _
        ((BTrue)
          (let (many env3) (many ctx2) (many sc) $ elab-stmt sugar-budget item env2 $ Nil _)
          (run-toplevel rest env3))
        ((BFalse)
          (match many rest _
            ((Cons b x more) (run-toplevel rest $ env-error env2 "only the last top-level form may be an expression"))
            ((Nil b)
              (let (many env3a) (many ress) (many code) (erased lock) $ elab-expr sugar-budget item env2 (Nil _) many-one no-tele $ CCPlain)
              (let (many env3) $ settle-res env3a $ first-res _ _ ress lock)
              (match many (env-errors env3) _
                ((Cons c e es) env3)
                ((Nil c)
                  (let (many v) $ vals-one $ run-code _ code)
                  (env-push-trace env3 $ TrFinal v $ res-ty $ first-res _ _ ress lock))))))))))