; self/elab.sl -- the trusting elaborator (self/README.md): head dispatch (DESIGN.md section 4), erasure by
; position (section 20), calls, matches compiled against their Matchable (sections 12, 17, 38), the five
; statements with run-position statements run at once (sections 16, 34), and literals. It mirrors
; lib/elab.ml with the checks left out: it assumes its input was accepted by the reference checker, so a
; proof is never inspected, a branch never refuted, and a type never compared.

(def-adts $ Res : -> Type
  enum
  (many MkRes : (many (Term) term) (many (Term) ty) (many (Mult) erasure) -> (Res)))

(def-fns _ $ many res-term : (many (Res) r) -> (many (Term) t) (match many r _ ((MkRes t ty e) t)))
(def-fns _ $ many res-ty : (many (Res) r) -> (many (Term) t) (match many r _ ((MkRes t ty e) ty)))
(def-fns _ $ many res-erasure : (many (Res) r) -> (many (Mult) t) (match many r _ ((MkRes t ty e) e)))

(def-fns _ $ many res-of : (many (Env) env) (many (Bin) x) -> (many (Res) r)
  (MkRes (TVar x) (type-of (predates _) env x) (entry-mult-of (predates _) env x)))

(def-fns _ $ many term-res : (many (Env) env) (many (Term) t) -> (many (Res) r)
  (MkRes t (infer (predates _) t env) (Erased)))

(def-fns _ $ many first-res : (many (List (Res)) rs) -> (many (Res) r)
  (match many rs _
    ((Nil a) (MkRes (TErr "no value") (TErr "no value") (Erased)))
    ((Cons a r rest) r)))

; What a statement leaves in the code after it (lib/elab.ml's wrap functions).
(def-adts $ StmtCode : -> Type
  enum
  (many SNone : -> (StmtCode))
  (many SLet : (many (List (Bin)) ids) (many (Code) rhs) -> (StmtCode))
  (many SLetRec : (many (List (Pair (Bin) (Func))) fns) -> (StmtCode))
  (many SConsts : (many (List (Pair (Bin) (Value))) cs) -> (StmtCode))
  (many SMatch : (many (Code) scrut) (many (Shape) shape) (many (Nat) disc) (many (List (Bin)) ids) -> (StmtCode)))

(def-fns _ $ many consts-codes : (subterm many (List (Pair (Bin) (Value))) cs) -> (many (List (Bin)) ids) (many (List (Code)) codes)
  (match many cs _
    ((Nil a) (values (Nil (Bin)) (Nil (Code))))
    ((Cons a p rest)
      (let (many ids) (many codes) (consts-codes (subterm _) rest))
      (match many p _
        ((MkPair x y id v) (values (Cons (Bin) id ids) (Cons (Code) (CConst v) codes)))))))

(def-fns _ $ many wrap-stmt : (many (StmtCode) sc) (many (Code) rest) -> (many (Code) r)
  (match many sc _
    ((SNone) rest)
    ((SLet ids rhs) (CLet ids rhs rest))
    ((SLetRec fns) (CLetRec fns rest))
    ((SConsts cs)
      (let (many ids) (many codes) (consts-codes (predates _) cs))
      (CLet ids (CValues codes) rest))
    ((SMatch scrut shape disc ids) (CMatch scrut shape (Cons (Branch) (MkBranch disc ids rest) (Nil (Branch)))))))

; ---- Raw helpers and the special-form head test

(def-fns _ $ many raw-atom : (many (Raw) r) -> (many (Maybe (String)) s)
  (match many r _ ((RAtom lq s) (Some (String) s)) ((RString lq s) (None (String))) ((RList lq items) (None (String)))))

(def-fns _ $ many raw-items : (many (Raw) r) -> (many (List (Raw)) items)
  (match many r _ ((RAtom lq s) (Nil (Raw))) ((RString lq s) (Nil (Raw))) ((RList lq items) items)))

(def-fns _ $ many raw-name : (many (Raw) r) -> (many (String) s)
  (match many r _ ((RAtom lq s) s) ((RString lq s) "_") ((RList lq items) "_")))

(def-fns _ $ many atoms-only : (subterm many (List (Raw)) rs) -> (many (Bool) r)
  (match many rs _
    ((Nil a) (BTrue))
    ((Cons a r rest) (match many (raw-atom (predates _) r) _ ((None b) (BFalse)) ((Some b s) (atoms-only (subterm _) rest))))))

(def-fns _ $ many is-underscore : (many (Raw) r) -> (many (Bool) b)
  (match many (raw-atom (predates _) r) _ ((None a) (BFalse)) ((Some a s) (str-eq (predates _) s "_"))))

(def-fns _ $ many name-or-anon : (many (String) n) -> (many (Maybe (String)) r)
  (match many (str-eq (predates _) n "_") _ ((BTrue) (None (String))) ((BFalse) (Some (String) n))))

; A special form's head: a Const, non-erased entry of type (Special) holding one of its variants (section 4).
(def-fns _ $ many special-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe (Sp)) r)
  (match many (raw-atom (predates _) raw) _
    ((None a) (None (Sp)))
    ((Some a n)
      (match many (lookup (predates _) env n) _
        ((None b) (None (Sp)))
        ((Some b x)
          (match many (entry (predates _) env x) _
            ((MkEInfo nm mult st mi)
              (match many st _
                ((SDyn) (None (Sp)))
                ((SConst v)
                  (match many v _
                    ((VCtor c fs)
                      (match many (and (predates _) (mult-is-many (predates _) mult) (equal-env (predates _) env (type-of (predates _) env x) special-term)) _
                        ((BTrue) (sp-of-index (predates _) (ctor-index (predates _) c)))
                        ((BFalse) (None (Sp)))))
                    ((VTuple fs) (None (Sp))) ((VExt ad p) (None (Sp))) ((VCtorFn c) (None (Sp))) ((VMatchable ad) (None (Sp)))
                    ((VFn cl) (None (Sp))) ((VToken) (None (Sp))) ((VError m) (None (Sp)))))))))))))

(def-fns _ $ many is-special : (many (Env) env) (many (Raw) raw) (many (Sp) sp) -> (many (Bool) r)
  (match many (special-of (predates _) env raw) _
    ((None a) (BFalse))
    ((Some a s) (sp-eq (predates _) s sp))))

(def-fns _ $ many is-mark : (many (Env) env) (many (Raw) raw) (many (MarkK) k) -> (many (Bool) r)
  (is-special (predates _) env raw (SpMark k)))

(def-fns _ $ many mult-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe (Mult)) r)
  (match many (special-of (predates _) env raw) _
    ((None a) (None (Mult)))
    ((Some a s)
      (match many (sp-eq (predates _) s (SpMark (MkErased))) _
        ((BTrue) (Some (Mult) (Erased)))
        ((BFalse) (match many (sp-eq (predates _) s (SpMark (MkMany))) _ ((BTrue) (Some (Mult) (Many))) ((BFalse) (None (Mult)))))))))

(def-fns _ $ many stmt-of : (many (Env) env) (many (Raw) raw) -> (many (Maybe (StmtK)) r)
  (match many (raw-items (predates _) raw) _
    ((Nil a) (None (StmtK)))
    ((Cons a h rest)
      (match many (special-of (predates _) env h) _
        ((None b) (None (StmtK)))
        ((Some b sp)
          (match many sp _
            ((SpStmt k) (Some (StmtK) k))
            ((SpFormer k) (None (StmtK))) ((SpExpr k) (None (StmtK))) ((SpMark k) (None (StmtK)))))))))

(def-fns _ $ many is-statement : (many (Env) env) (many (Raw) raw) -> (many (Bool) r)
  (match many (stmt-of (predates _) env raw) _ ((None a) (BFalse)) ((Some a k) (BTrue))))


(def-fns _ $ many show-t : (many (Env) env) (many (Term) t) -> (many (String) s)
  (rope-str (predates _) (show-term (predates _) (canon-env (predates _) env t) env)))

(def-fns _ $ many show-r : (many (Raw) r) -> (many (String) s)
  (rope-str (predates _) (show-raw (predates _) r)))

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
      (match many (all-digits (predates _) s) _
        ((BTrue) (LNumeral))
        ((BFalse)
          (match many (and (predates _) (char-is (predates _) c 35) (match many rest (((Bool) b)) ((SNil) (BFalse)) ((SCons c2 rest2) (char-is (predates _) c2 92)))) _
            ((BTrue) (LChar))
            ((BFalse) (LName))))))))

(def-fns _ $ many parse-nat : (subterm many (String) s) (many (Nat) acc) -> (many (Nat) n)
  (match many s _
    ((SNil) acc)
    ((SCons c rest)
      (let (many d2) (nat-add (predates _) acc acc))
      (let (many d4) (nat-add (predates _) d2 d2))
      (let (many d8) (nat-add (predates _) d4 d4))
      (parse-nat (subterm _) rest (nat-add (predates _) (nat-add (predates _) d8 d2) (nat-sub (predates _) (char-code (predates _) c) 48))))))

(def-fns _ $ many is-hex : (many (Char) c) -> (many (Bool) r)
  (or (predates _) (char-between (predates _) c 48 57) (or (predates _) (char-between (predates _) c 97 102) (char-between (predates _) c 65 70))))

(def-fns _ $ many hex-digit : (many (Char) c) -> (many (Nat) d)
  (let (many n) (char-code (predates _) c))
  (match many (char-between (predates _) c 48 57) _
    ((BTrue) (nat-sub (predates _) n 48))
    ((BFalse)
      (match many (char-between (predates _) c 97 102) _
        ((BTrue) (nat-sub (predates _) n 87))
        ((BFalse) (nat-sub (predates _) n 55))))))

(def-fns _ $ many times16 : (many (Nat) hi) -> (many (Nat) n)
  (let (many d2) (nat-add (predates _) hi hi))
  (let (many d4) (nat-add (predates _) d2 d2))
  (let (many d8) (nat-add (predates _) d4 d4))
  (nat-add (predates _) d8 d8))

(def-fns _ $ many char-lit-body : (many (String) s) -> (many (String) body)
  (match many s _ ((SNil) (SNil)) ((SCons c rest) (match many rest _ ((SNil) (SNil)) ((SCons c2 rest2) rest2)))))

; The code of #\c, #\space, #\newline, #\tab or #\xHH, or None where the literal is malformed.
(def-fns _ $ many char-lit-code : (many (String) s) -> (many (Maybe (Nat)) n)
  (let (many body) (char-lit-body (predates _) s))
  (match many (str-eq (predates _) body "space") _
    ((BTrue) (Some (Nat) 32))
    ((BFalse)
      (match many (str-eq (predates _) body "newline") _
        ((BTrue) (Some (Nat) 10))
        ((BFalse)
          (match many (str-eq (predates _) body "tab") _
            ((BTrue) (Some (Nat) 9))
            ((BFalse)
              (match many body _
                ((SNil) (None (Nat)))
                ((SCons c rest)
                  (match many rest _
                    ((SNil) (Some (Nat) (char-code (predates _) c)))
                    ((SCons h1 rest2)
                      (match many rest2 _
                        ((SNil) (None (Nat)))
                        ((SCons h2 rest3)
                          (match many (and (predates _) (char-is (predates _) c 120) (and (predates _) (is-hex (predates _) h1) (and (predates _) (is-hex (predates _) h2) (str-is-empty (predates _) rest3)))) _
                            ((BTrue) (Some (Nat) (nat-add (predates _) (times16 (predates _) (hex-digit (predates _) h1)) (hex-digit (predates _) h2))))
                            ((BFalse) (None (Nat)))))))))))))))))

; What is wrong with a literal's spelling, if anything (lib/literal.ml's classify).
(def-fns _ $ many literal-error : (many (String) s) -> (many (Maybe (String)) r)
  (match many (classify (predates _) s) _
    ((LName) (None (String)))
    ((LNumeral)
      (match many s _
        ((SNil) (None (String)))
        ((SCons c rest)
          (match many (and (predates _) (char-is (predates _) c 48) (not (predates _) (str-is-empty (predates _) rest))) _
            ((BTrue) (Some (String) (str-cat (predates _) s " has a leading zero")))
            ((BFalse) (None (String)))))))
    ((LChar)
      (match many (char-lit-code (predates _) s) _
        ((Some a n) (None (String)))
        ((None a) (Some (String) (str-cat (predates _) "malformed character literal " s)))))))

(def-fns _ $ many prelude-id : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Bin) x)
  (match many (lookup (predates _) env name) _
    ((None a) (values (env-error (predates _) env (str-cat (predates _) "unbound name " name)) (BZ)))
    ((Some a x) (values env x))))

(def-fns _ $ many prelude-type : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Term) t)
  (let (many env2) (many x) (prelude-id (predates _) env name))
  (values env2 (TApp (TVar x) (Nil (Term)))))

(def-fns _ $ many bin-of-nat : (subterm many (Nat) n) (many (Bin) acc) -> (many (Bin) b)
  (match many n _
    ((Zero) acc)
    ((Succ m) (bin-of-nat (subterm _) m (bin-succ (predates _) acc)))))

(def-fns _ $ many bin-term : (subterm many (Bin) b) (many (Env) env) -> (many (Env) r) (many (Term) t)
  (match many b _
    ((BZ) (let (many env2) (many c) (prelude-id (predates _) env "BZ")) (values env2 (TApp (TVar c) (Nil (Term)))))
    ((B1 b1)
      (let (many env2) (many c) (prelude-id (predates _) env "B1"))
      (let (many env3) (many t) (bin-term (subterm _) b1 env2))
      (values env3 (TApp (TVar c) (Cons (Term) t (Nil (Term))))))
    ((B2 b1)
      (let (many env2) (many c) (prelude-id (predates _) env "B2"))
      (let (many env3) (many t) (bin-term (subterm _) b1 env2))
      (values env3 (TApp (TVar c) (Cons (Term) t (Nil (Term))))))))

; The bijective base-2 spelling of a number as a term over the prelude's Bin (ASSUMPTIONS 50).
(def-fns _ $ many nat-bin-term : (many (Nat) n) (many (Env) env) -> (many (Env) r) (many (Term) t)
  (bin-term (predates _) (bin-of-nat (predates _) n (BZ)) env))

(def-fns _ $ many lit-lookup : (many (Env) env) (many (String) key) -> (many (Maybe (Bin)) r)
  (nm-get (predates _) (Bin) key (env-literals (predates _) env)))

; Interns a numeral: a Const Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
(def-fns _ $ many intern-numeral : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Bin) x) (many (Bin) proof)
  (let (many n) (parse-nat (predates _) key 0))
  (let (many env1) (many nat-ty) (prelude-type (predates _) env "Nat"))
  (let (many env2) (many x) (bind (predates _) env1 (None (String)) (Many) (SConst (vnat (predates _) n)) nat-ty (None (Term)) coercible-id))
  (let (many env2b) (many numeral) (prelude-id (predates _) env2 "Numeral"))
  (let (many env2c) (many spelled) (nat-bin-term (predates _) n env2b))
  (let (many pty) (TApp (TVar numeral) (Cons (Term) spelled (Cons (Term) (TVar x) (Nil (Term))))))
  (let (many env3) (many p) (bind (predates _) env2c (None (String)) (Erased) (SConst (VToken)) pty (None (Term)) coercible-id))
  (let (many env4) (env-set-literals (predates _) env3 (nm-set (predates _) (Bin) key x (env-literals (predates _) env3))))
  (values (env-push-lit (predates _) (env-push-trace (predates _) env4 (TrConst x (vnat (predates _) n))) x (Some (Bin) p)) x p))

(def-fns _ $ many lit-proof : (subterm many (List (Pair (Bin) (Maybe (Bin)))) lits) (many (Bin) x) -> (many (Maybe (Bin)) r)
  (match many lits _
    ((Nil a) (None (Bin)))
    ((Cons a p rest)
      (match many p _
        ((MkPair s t y proof) (match many (bin-eq (predates _) x y) _ ((BTrue) proof) ((BFalse) (lit-proof (subterm _) rest x))))))))

(def-fns _ $ many intern-numeral-once : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Bin) x) (many (Bin) proof)
  (match many (lit-lookup (predates _) env key) _
    ((Some a x)
      (match many (lit-proof (predates _) (env-lits (predates _) env) x) _
        ((Some b p) (values env x p))
        ((None b) (values env x (BZ)))))
    ((None a) (intern-numeral (predates _) env key))))

; Interns a numeral or character literal (ASSUMPTIONS 51, 52): a character is (MkChar (MkU8 n p)) over its
; code's numeral, transparent down to the opaque n.
(def-fns _ $ many intern : (many (Env) env) (many (String) key) (many (LitKind) kind) -> (many (Env) r)
  (match many (lit-lookup (predates _) env key) _
    ((Some a x) env)
    ((None a)
      (match many (literal-error (predates _) key) _
        ((Some b msg) (env-error (predates _) env msg))
        ((None b)
          (match many kind _
            ((LNumeral) (let (many env2) (many x) (many p) (intern-numeral (predates _) env key)) env2)
            ((LChar)
              (let (many code) (match many (char-lit-code (predates _) key) (((Nat) n)) ((None c) 0) ((Some c n) n)))
              (let (many env2) (many num) (many np) (intern-numeral-once (predates _) env (nat-str (predates _) code)))
              (let (many env2b) (many lt-id) (prelude-id (predates _) env2 "Lt"))
              (let (many env2c) (many modulus) (prelude-id (predates _) env2b "u8-modulus"))
              (let (many env3) (many lt) (bind (predates _) env2c (None (String)) (Erased) (SConst (VToken))
                                          (TApp (TVar lt-id) (Cons (Term) (TVar num) (Cons (Term) (TVar modulus) (Nil (Term))))) (None (Term)) coercible-id))
              (let (many env3b) (many mk-char) (prelude-id (predates _) env3 "MkChar"))
              (let (many env3c) (many mk-u8) (prelude-id (predates _) env3b "MkU8"))
              (let (many rule) (TApp (TVar mk-char) (Cons (Term) (TApp (TVar mk-u8) (Cons (Term) (TVar num) (Cons (Term) (TVar lt) (Nil (Term))))) (Nil (Term)))))
              (let (many v) (vnat (predates _) code))
              (let (many env3d) (many char-ty) (prelude-type (predates _) env3c "Char"))
              (let (many env4) (many x) (bind (predates _) env3d (None (String)) (Many) (SConst v) char-ty (Some (Term) rule) coercible-id))
              (let (many env5) (env-set-literals (predates _) env4 (nm-set (predates _) (Bin) key x (env-literals (predates _) env4))))
              (env-push-lit (predates _) (env-push-trace (predates _) env5 (TrConst x v)) x (Some (Bin) np)))
            ((LName) env)))))))

; Interns a string (ASSUMPTIONS 60): its characters, holding no proof.
(def-fns _ $ many intern-string : (many (Env) env) (many (String) key) -> (many (Env) r)
  (match many (lit-lookup (predates _) env key) _
    ((Some a x) env)
    ((None a)
      (let (many v) (VExt str-adt (PStr (match many key (((String) s)) ((SNil) (SNil)) ((SCons q rest) rest)))))
      (let (many env1) (many str-ty) (prelude-type (predates _) env "String"))
      (let (many env2) (many x) (bind (predates _) env1 (None (String)) (Many) (SConst v) str-ty (None (Term)) coercible-id))
      (let (many env3) (env-set-literals (predates _) env2 (nm-set (predates _) (Bin) key x (env-literals (predates _) env2))))
      (env-push-lit (predates _) (env-push-trace (predates _) env3 (TrConst x v)) x (None (Bin))))))

(def-fns _
  (many intern-literals : (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r)
    (match many raw _
      ((RAtom lq s)
        (match many (classify (predates _) s) _
          ((LName) env)
          ((LNumeral) (intern (predates _) env s (LNumeral)))
          ((LChar) (intern (predates _) env s (LChar)))))
      ((RString lq s) (intern-string (predates _) env (SCons #\x22 s)))
      ((RList lq items) (intern-literals-list (subterm _) items env))))
  (many intern-literals-list : (subterm many (List (Raw)) rs) (many (Env) env) -> (many (Env) r)
    (match many rs _
      ((Nil a) env)
      ((Cons a r rest) (intern-literals-list (subterm _) rest (intern-literals (subterm _) r env))))))

; The entry an atom names: a literal's, or the newest of that name in scope; id zero, which nothing binds,
; stands for an error already recorded.
(def-fns _ $ many var : (many (Env) env) (many (String) n) -> (many (Env) r) (many (Bin) x)
  (match many (literal-error (predates _) n) _
    ((Some a msg) (values (env-error (predates _) env msg) (BZ)))
    ((None a)
      (match many (classify (predates _) n) _
        ((LName)
          (match many (lookup (predates _) env n) _
            ((Some b x) (values env x))
            ((None b) (values (env-error (predates _) env (str-cat (predates _) "unbound name " n)) (BZ)))))
        ((LNumeral) (match many (lit-lookup (predates _) env n) _ ((Some b x) (values env x)) ((None b) (values (env-error (predates _) env (str-cat3 (predates _) "literal " n " outside a top-level form")) (BZ)))))
        ((LChar) (match many (lit-lookup (predates _) env n) _ ((Some b x) (values env x)) ((None b) (values (env-error (predates _) env (str-cat3 (predates _) "literal " n " outside a top-level form")) (BZ)))))))))

(def-fns _ $ many var-of-raw : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Bin) x)
  (match many raw _
    ((RAtom lq s) (var (predates _) env s))
    ((RString lq s)
      (match many (lit-lookup (predates _) env (SCons #\x22 s)) _
        ((Some a x) (values env x))
        ((None a) (values (env-error (predates _) env "string literal outside a top-level form") (BZ)))))
    ((RList lq items) (values (env-error (predates _) env (str-cat3 (predates _) "expected " what (str-cat (predates _) ", got " (rope-str (predates _) (show-raw (predates _) raw))))) (BZ)))))

; A name read through its alias (ASSUMPTIONS 78), which must resolve to a variable.
(def-fns _ $ many named : (many (Env) env) (many (Raw) raw) (many (String) what) -> (many (Env) r) (many (Bin) x)
  (let (many env2) (many x) (var-of-raw (predates _) env raw what))
  (match many (canon-env (predates _) env2 (TVar x)) _
    ((TVar y) (values env2 y))
    ((TBound k) (values env2 x)) ((TErr m) (values env2 x))
    ((TApp h a) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))
    ((TFn l p r) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))
    ((TTyCtor p) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))
    ((TValCtor p r) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))
    ((TMatchable d t c) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))
    ((TNewtype c) (values (env-error (predates _) env2 (str-cat3 (predates _) (show-t (predates _) env2 (TVar x)) " is not " what)) x))))


; ---- Source telescopes (section 30), with erased proofs placing every raw they hold inside the raw list it
; was read from; the elaborator recurses on those raws.

; b is a, or a strict subterm of a.
(def-adts $ Within : ((List (Raw)) b) ((List (Raw)) a) -> Type
  enum
  (many WHere : (erased (List (Raw)) a) -> (Within a a))
  (many WIn : (erased (List (Raw)) b) (erased (List (Raw)) a) (erased (Subterm (List (Raw)) b (List (Raw)) a) p) -> (Within b a)))

(def-fns _ $ erased in-within : (erased Type A) (erased A x) (erased (List (Raw)) b) (erased (List (Raw)) a) (erased (Subterm A x (List (Raw)) b) p) (erased (Within b a) w) -> (erased (Subterm A x (List (Raw)) a) q)
  (match erased w _
    ((WHere y) p)
    ((WIn y z s) (subterm-trans p s))))

(def-fns _ $ erased within-in : (erased (List (Raw)) c) (erased (List (Raw)) b) (erased Type A) (erased A x) (erased (Within c b) w) (erased (Subterm (List (Raw)) b A x) p) -> (erased (Subterm (List (Raw)) c A x) q)
  (match erased w _
    ((WHere y) p)
    ((WIn y z s) (subterm-trans s p))))

(def-fns _ $ erased within-step : (erased (List (Raw)) c) (erased (List (Raw)) b) (erased (List (Raw)) a) (erased (Subterm (List (Raw)) c (List (Raw)) b) p) (erased (Within b a) w) -> (erased (Within c a) q)
  (WIn c a (in-within (predates _) (List (Raw)) c b a p w)))

; A raw strictly inside the list root.
(def-adts $ Sub : ((List (Raw)) root) -> Type
  enum
  (many MkSub : (erased (List (Raw)) root) (many (Raw) r) (erased (Subterm (Raw) r (List (Raw)) root) p) -> (Sub root)))

(def-fns _ $ many subs-of : (subterm many (List (Raw)) items) (erased (List (Raw)) root) (erased (Within items root) w) -> (many (List (Sub root)) r)
  (match many items _
    ((Nil a) (Nil (Sub root)))
    ((Cons a t rest)
      (Cons (Sub root) (MkSub root t (in-within (predates _) (Raw) t items root (prove-subterm t items) w))
        (subs-of (subterm _) rest root (within-step (predates _) rest items root (prove-subterm rest items) w))))))

(def-fns _ $ many subs-all : (many (List (Raw)) items) -> (many (List (Sub items)) r)
  (subs-of (predates _) items items (WHere items)))

; A hop budget: a function that hands its whole raw to another spends one step (see the elaborator block).
(def-adts $ Steps : ((Nat) n) -> Type
  enum
  (many SZ : -> (Steps (Zero)))
  (many SS : (erased (Nat) n) (many (Steps n) k) -> (Steps (Succ n))))
(let (many one-step) (SS (Zero) (SZ)))
(let (many two-steps) (SS (Succ (Zero)) one-step))

(def-adts
  (SrcEntry : ((List (Raw)) root) -> Type
    enum
    (many MkSrcEntry : (erased (List (Raw)) root) (many (Bool) sub) (many (Maybe (Mult)) mult) (many (Maybe (SrcSg root)) sg) (many (String) name) -> (SrcEntry root)))
  (SrcSg : ((List (Raw)) root) -> Type
    enum
    (many SrcTy : (erased (List (Raw)) root) (many (Raw) r) (erased (Subterm (Raw) r (List (Raw)) root) p) -> (SrcSg root))
    (many SrcIs : (erased (List (Raw)) root) (many (Raw) r) (erased (Subterm (Raw) r (List (Raw)) root) p) -> (SrcSg root))))

(def-fns _ $ many entries-of-names : (subterm many (List (Raw)) names) (many (Bool) sub) (many (Maybe (Mult)) mult) (erased (List (Raw)) root) (many (Raw) ty) (erased (Subterm (Raw) ty (List (Raw)) root) pty) -> (many (List (SrcEntry root)) r)
  (match many names _
    ((Nil a) (Nil (SrcEntry root)))
    ((Cons a n rest) (Cons (SrcEntry root) (MkSrcEntry root sub mult (Some (SrcSg root) (SrcTy root ty pty)) (raw-name (predates _) n)) (entries-of-names (subterm _) rest sub mult root ty pty)))))

(def-fns _ $ many parse-entry : (many (Env) env) (many (Raw) raw) (erased (List (Raw)) root) (erased (Subterm (Raw) raw (List (Raw)) root) pr) -> (many (List (SrcEntry root)) r)
  (match many raw _
    ((RAtom lq s) (Nil (SrcEntry root)))
    ((RString lq s) (Nil (SrcEntry root)))
    ((RList lq items0)
      (let (erased w0) (WIn items0 root (subterm-trans (prove-subterm items0 raw) pr)))
      (let (many sub) (many items1) (erased w1)
        (match many items0 (((Bool) b) ((List (Raw)) l) ((Within l root) w))
          ((Nil a) (values (BFalse) items0 w0))
          ((Cons a t rest)
            (match many (is-mark (predates _) env t (MkSubterm)) (((Bool) b) ((List (Raw)) l) ((Within l root) w))
              ((BTrue) (values (BTrue) rest (within-step (predates _) rest items0 root (prove-subterm rest items0) w0)))
              ((BFalse) (values (BFalse) items0 w0))))))
      (let (many mult) (many items) (erased w2)
        (match many items1 (((Maybe (Mult)) m) ((List (Raw)) l) ((Within l root) w))
          ((Nil a) (values (None (Mult)) items1 w1))
          ((Cons a t rest)
            (match many (mult-of (predates _) env t) (((Maybe (Mult)) m) ((List (Raw)) l) ((Within l root) w))
              ((None b) (values (None (Mult)) items1 w1))
              ((Some b m) (values (Some (Mult) m) rest (within-step (predates _) rest items1 root (prove-subterm rest items1) w1)))))))
      (match many items _
        ((Nil a) (Nil (SrcEntry root)))
        ((Cons a first rest)
          (let (erased pf) (in-within (predates _) (Raw) first items root (prove-subterm first items) w2))
          (match many rest _
            ((Nil b) (Cons (SrcEntry root) (MkSrcEntry root sub mult (None (SrcSg root)) (raw-name (predates _) first)) (Nil (SrcEntry root))))
            ((Cons b second rest2)
              (match many rest2 _
                ((Cons c third rest3)
                  (match many (and (predates _) (is-mark (predates _) env second (MkIs)) (list-is-empty (predates _) (Raw) rest3)) _
                    ((BTrue) (Cons (SrcEntry root) (MkSrcEntry root sub mult (Some (SrcSg root) (SrcIs root first pf)) (raw-name (predates _) third)) (Nil (SrcEntry root))))
                    ((BFalse) (entries-of-names (predates _) rest sub mult root first pf))))
                ((Nil c) (entries-of-names (predates _) rest sub mult root first pf))))))))))

; The items before the arrow, and those after it, which sit within the root.
(def-fns _ $ many split-arrow : (subterm many (List (Raw)) items) (erased (List (Raw)) root) (erased (Within items root) w) (many (Env) env) -> (many (List (Sub root)) before) (many (List (Raw)) after) (erased (Within after root) wa)
  (match many items _
    ((Nil a) (values (Nil (Sub root)) items w))
    ((Cons a t rest)
      (let (erased wr) (within-step (predates _) rest items root (prove-subterm rest items) w))
      (match many (is-mark (predates _) env t (MkArrow)) _
        ((BTrue) (values (Nil (Sub root)) rest wr))
        ((BFalse)
          (let (many before) (many after) (erased wa) (split-arrow (subterm _) rest root wr env))
          (values (Cons (Sub root) (MkSub root t (in-within (predates _) (Raw) t items root (prove-subterm t items) w)) before) after wa))))))

; Leading items that are lists headed by a multiplicity token are return entries or let binders (ASSUMPTIONS 11).
(def-fns _ $ many split-returns : (subterm many (List (Raw)) items) (erased (List (Raw)) root) (erased (Within items root) w) (many (Env) env) -> (many (List (Sub root)) rets) (many (List (Raw)) body) (erased (Within body root) wb)
  (match many items _
    ((Nil a) (values (Nil (Sub root)) items w))
    ((Cons a t rest)
      (let (many headed) (match many (raw-items (predates _) t) (((Bool) b)) ((Nil b) (BFalse)) ((Cons b m r) (match many (mult-of (predates _) env m) (((Bool) x)) ((None c) (BFalse)) ((Some c mm) (BTrue))))))
      (match many headed _
        ((BFalse) (values (Nil (Sub root)) items w))
        ((BTrue)
          (let (many rets) (many body) (erased wb) (split-returns (subterm _) rest root (within-step (predates _) rest items root (prove-subterm rest items) w) env))
          (values (Cons (Sub root) (MkSub root t (in-within (predates _) (Raw) t items root (prove-subterm t items) w)) rets) body wb))))))

; Leading annotation tokens from the marks given, in any order; returns the flags for absurd/newtype and extern.
(def-fns _ $ many take-marks : (subterm many (List (Raw)) items) (erased (List (Raw)) root) (erased (Within items root) w) (many (Env) env) (many (MarkK) first) (many (MarkK) second) -> (many (Bool) has-first) (many (Bool) has-second) (many (List (Raw)) rest) (erased (Within rest root) wr)
  (match many items _
    ((Nil a) (values (BFalse) (BFalse) items w))
    ((Cons a t more)
      (let (erased wm) (within-step (predates _) more items root (prove-subterm more items) w))
      (match many (is-mark (predates _) env t first) _
        ((BTrue)
          (let (many f) (many s) (many rest) (erased wr) (take-marks (subterm _) more root wm env first second))
          (values (BTrue) s rest wr))
        ((BFalse)
          (match many (is-mark (predates _) env t second) _
            ((BTrue)
              (let (many f) (many s) (many rest) (erased wr) (take-marks (subterm _) more root wm env first second))
              (values f (BTrue) rest wr))
            ((BFalse) (values (BFalse) (BFalse) items w))))))))

; ---- Constructors, Matchables and shapes (sections 17, 19, 38)

(def-fns _ $ many adt-of : (many (Env) env) (many (Bin) x) -> (many (Maybe (Adt)) r)
  (match many (entry-state (predates _) env x) _
    ((SDyn) (None (Adt)))
    ((SConst v)
      (match many v _
        ((VMatchable adt) (Some (Adt) adt))
        ((VCtor c fs) (None (Adt))) ((VTuple fs) (None (Adt))) ((VExt a p) (None (Adt))) ((VCtorFn c) (None (Adt)))
        ((VFn cl) (None (Adt))) ((VToken) (None (Adt))) ((VError m) (None (Adt)))))))

(def-fns _ $ many ctor-of : (many (Env) env) (many (Bin) x) -> (many (Maybe (Ctor)) r)
  (match many (entry-state (predates _) env x) _
    ((SDyn) (None (Ctor)))
    ((SConst v)
      (match many v _
        ((VCtorFn c) (Some (Ctor) c))
        ((VCtor c fs) (None (Ctor))) ((VTuple fs) (None (Ctor))) ((VExt a p) (None (Ctor))) ((VMatchable a) (None (Ctor)))
        ((VFn cl) (None (Ctor))) ((VToken) (None (Ctor))) ((VError m) (None (Ctor)))))))

(def-fns _ $ many ctor-type : (many (Env) env) (many (Bin) c) -> (many (List (Entry)) tele) (many (Term) ret)
  (match many (type-of (predates _) env c) _
    ((TValCtor tele ret) (values tele ret))
    ((TVar x) (values (Nil (Entry)) (TErr "not a constructor"))) ((TBound k) (values (Nil (Entry)) (TErr "not a constructor")))
    ((TApp h a) (values (Nil (Entry)) (TErr "not a constructor"))) ((TFn l p r) (values (Nil (Entry)) (TErr "not a constructor")))
    ((TTyCtor p) (values (Nil (Entry)) (TErr "not a constructor"))) ((TMatchable d t cs) (values (Nil (Entry)) (TErr "not a constructor")))
    ((TNewtype x) (values (Nil (Entry)) (TErr "not a constructor"))) ((TErr m) (values (Nil (Entry)) (TErr m)))))

(def-fns _ $ many tid-of : (many (Env) env) (many (Bin) c) -> (many (Bin) tid)
  (let (many tele) (many ret) (ctor-type (predates _) env c))
  (match many (type-head (predates _) env ret) _ ((None a) (BZ)) ((Some a t) t)))

(def-adts $ MatchInfo : -> Type
  enum
  (many MkMatchInfo : (many (Bin) mid) (many (Disc) disc) (many (List (MCtor)) ctors) (many (Nat) rank) -> (MatchInfo)))

(def-fns _ $ many matchable-rank : (many (Env) env) (many (Bin) x) -> (many (Nat) r)
  (match many (adt-of (predates _) env x) _
    ((Some a adt) 0)
    ((None a) (match many (entry-mult-of (predates _) env x) _ ((Many) 1) ((Erased) 2)))))

; Consistent Matchables for one type are interchangeable (section 19); the pick prefers one whose ADT the
; elaborator can see, then a non-erased one (ASSUMPTIONS 84, 86).
(def-fns _ $ many find-matchable-in : (subterm many (List (Bin)) objects) (many (Env) env) (many (Bin) tid) (many (Maybe (MatchInfo)) best) -> (many (Maybe (MatchInfo)) r)
  (match many objects _
    ((Nil a) best)
    ((Cons a x rest)
      (let (many cand)
        (match many (type-of (predates _) env x) (((Maybe (MatchInfo)) c))
          ((TMatchable d t cs)
            (match many t (((Maybe (MatchInfo)) c))
              ((TVar t2)
                (match many (bin-eq (predates _) t2 tid) (((Maybe (MatchInfo)) c))
                  ((BTrue) (let (many y) (resolve (predates _) env x)) (Some (MatchInfo) (MkMatchInfo y d cs (matchable-rank (predates _) env y))))
                  ((BFalse) (None (MatchInfo)))))
              ((TBound k) (None (MatchInfo))) ((TApp h as) (None (MatchInfo))) ((TFn l p r) (None (MatchInfo))) ((TTyCtor p) (None (MatchInfo)))
              ((TValCtor p r) (None (MatchInfo))) ((TMatchable d2 t2 c2) (None (MatchInfo))) ((TNewtype c2) (None (MatchInfo))) ((TErr m) (None (MatchInfo)))))
          ((TVar y) (None (MatchInfo))) ((TBound k) (None (MatchInfo))) ((TApp h as) (None (MatchInfo))) ((TFn l p r) (None (MatchInfo)))
          ((TTyCtor p) (None (MatchInfo))) ((TValCtor p r) (None (MatchInfo))) ((TNewtype c2) (None (MatchInfo))) ((TErr m) (None (MatchInfo)))))
      (let (many best2)
        (match many cand (((Maybe (MatchInfo)) c))
          ((None b) best)
          ((Some b info)
            (match many best (((Maybe (MatchInfo)) c))
              ((None c) cand)
              ((Some c old)
                (match many old (((Maybe (MatchInfo)) c))
                  ((MkMatchInfo m1 d1 c1 r1)
                    (match many info (((Maybe (MatchInfo)) c))
                      ((MkMatchInfo m2 d2 c2 r2) (match many (nat-lt (predates _) r2 r1) (((Maybe (MatchInfo)) c)) ((BTrue) cand) ((BFalse) best)))))))))))
      (find-matchable-in (subterm _) rest env tid best2))))


(def-fns _ $ many find-newtype : (subterm many (List (Bin)) objects) (many (Env) env) (many (Bin) c) -> (many (Maybe (Bin)) r)
  (match many objects _
    ((Nil a) (None (Bin)))
    ((Cons a x rest)
      (match many (type-of (predates _) env x) _
        ((TNewtype t)
          (match many t _
            ((TVar c2) (match many (bin-eq (predates _) c2 c) _ ((BTrue) (Some (Bin) x)) ((BFalse) (find-newtype (subterm _) rest env c))))
            ((TBound k) (find-newtype (subterm _) rest env c)) ((TApp h as) (find-newtype (subterm _) rest env c)) ((TFn l p r) (find-newtype (subterm _) rest env c))
            ((TTyCtor p) (find-newtype (subterm _) rest env c)) ((TValCtor p r) (find-newtype (subterm _) rest env c)) ((TMatchable d t2 cs) (find-newtype (subterm _) rest env c))
            ((TNewtype c2) (find-newtype (subterm _) rest env c)) ((TErr m) (find-newtype (subterm _) rest env c))))
        ((TVar y) (find-newtype (subterm _) rest env c)) ((TBound k) (find-newtype (subterm _) rest env c)) ((TApp h as) (find-newtype (subterm _) rest env c))
        ((TFn l p r) (find-newtype (subterm _) rest env c)) ((TTyCtor p) (find-newtype (subterm _) rest env c)) ((TValCtor p r) (find-newtype (subterm _) rest env c))
        ((TMatchable d t cs) (find-newtype (subterm _) rest env c)) ((TErr m) (find-newtype (subterm _) rest env c))))))

; The anonymous Coercible proof def-fns minted for a delegating function g (section 38).
(def-fns _ $ many find-coercible : (subterm many (List (Bin)) objects) (many (Env) env) (many (Bin) g) -> (many (Maybe (Bin)) r)
  (match many objects _
    ((Nil a) (None (Bin)))
    ((Cons a x rest)
      (let (many hit)
        (match many (type-of (predates _) env x) (((Bool) b))
          ((TApp h args)
            (match many (list-nth (predates _) (Term) args 1) (((Bool) b))
              ((None b) (BFalse))
              ((Some b t)
                (match many t (((Bool) b))
                  ((TVar g2) (and (predates _) (bin-eq (predates _) g2 g) (match many (entry (predates _) env x) (((Bool) b)) ((MkEInfo n m s mi) (match many n (((Bool) b)) ((None c) (BTrue)) ((Some c nm) (BFalse)))))))
                  ((TBound k) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
                  ((TMatchable d t2 cs) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))))
          ((TVar y) (BFalse)) ((TBound k) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
          ((TMatchable d t cs) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
      (match many hit _
        ((BTrue) (Some (Bin) x))
        ((BFalse) (find-coercible (subterm _) rest env g))))))

; A Matchable's constructors, each with its phantom marker, id and number of many fields (section 38).
(def-adts $ CShape : -> Type
  enum
  (many MkCShape : (many (Mult) m) (many (Bin) c) (many (Nat) arity) -> (CShape)))

(def-fns _ $ many shapes : (subterm many (List (MCtor)) ctors) (many (Env) env) -> (many (List (CShape)) r)
  (match many ctors _
    ((Nil a) (Nil (CShape)))
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let (many c) (match many t (((Bin) x)) ((TVar x) x) ((TBound k) (BZ)) ((TApp h as) (BZ)) ((TFn l p r) (BZ)) ((TTyCtor p) (BZ)) ((TValCtor p r) (BZ)) ((TMatchable d t2 cs) (BZ)) ((TNewtype c2) (BZ)) ((TErr msg) (BZ))))
          (let (many tele) (many ret) (ctor-type (predates _) env c))
          (Cons (CShape) (MkCShape m c (many-count (predates _) tele)) (shapes (subterm _) rest env)))))))

(def-fns _ $ many non-phantom : (subterm many (List (CShape)) ss) -> (many (List (CShape)) r)
  (match many ss _
    ((Nil a) (Nil (CShape)))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n) (match many m _ ((Many) (Cons (CShape) s (non-phantom (subterm _) rest))) ((Erased) (non-phantom (subterm _) rest))))))))

(def-fns _ $ many shape-index : (subterm many (List (CShape)) ss) (many (Bin) c) (many (Nat) i) -> (many (Maybe (Nat)) r)
  (match many ss _
    ((Nil a) (None (Nat)))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c2 n) (match many (bin-eq (predates _) c c2) _ ((BTrue) (Some (Nat) i)) ((BFalse) (shape-index (subterm _) rest c (Succ i)))))))))

; A phantom constructor heads no runtime value (section 20 rule 2), so discriminants number the others only.
(def-fns _ $ many discriminant : (many (List (CShape)) ss) (many (Bin) c) -> (many (Nat) r)
  (match many (shape-index (predates _) (non-phantom (predates _) ss) c 0) _ ((None a) 0) ((Some a i) i)))

(def-fns _ $ many tagged-of : (many (Disc) disc) (many (List (CShape)) ss) -> (many (Bool) r)
  (match many disc _
    ((DUnion) (BFalse))
    ((DEnum) (nat-lt (predates _) 1 (list-length (predates _) (CShape) (non-phantom (predates _) ss))))))

(def-fns _ $ many marker : (subterm many (List (MCtor)) ctors) (many (Bin) c) -> (many (Mult) m)
  (match many ctors _
    ((Nil a) (Many))
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (match many t _
            ((TVar c2) (match many (bin-eq (predates _) c c2) _ ((BTrue) m) ((BFalse) (marker (subterm _) rest c))))
            ((TBound k) (marker (subterm _) rest c)) ((TApp h as) (marker (subterm _) rest c)) ((TFn l p r) (marker (subterm _) rest c))
            ((TTyCtor p) (marker (subterm _) rest c)) ((TValCtor p r) (marker (subterm _) rest c)) ((TMatchable d t2 cs) (marker (subterm _) rest c))
            ((TNewtype c2) (marker (subterm _) rest c)) ((TErr msg) (marker (subterm _) rest c))))))))



; The wrapping constructor of a type of newtype shape (section 38), if any.
(def-fns _ $ many wrappers : (subterm many (List (CShape)) ss) -> (many (List (Bin)) r)
  (match many ss _
    ((Nil a) (Nil (Bin)))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n)
          (match many (and (predates _) (mult-is-many (predates _) m) (nat-eq (predates _) n 1)) _
            ((BTrue) (Cons (Bin) c (wrappers (subterm _) rest)))
            ((BFalse) (wrappers (subterm _) rest))))))))

(def-fns _ $ many others-bare : (subterm many (List (CShape)) ss) (many (Bin) w) -> (many (Bool) r)
  (match many ss _
    ((Nil a) (BTrue))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n)
          (and (predates _) (or (predates _) (not (predates _) (mult-is-many (predates _) m)) (or (predates _) (bin-eq (predates _) c w) (nat-is-zero (predates _) n)))
            (others-bare (subterm _) rest w)))))))

(def-fns _ $ many wrapper : (many (Disc) disc) (many (List (CShape)) ss) -> (many (Maybe (Bin)) r)
  (match many (wrappers (predates _) ss) _
    ((Nil a) (None (Bin)))
    ((Cons a w rest)
      (match many rest _
        ((Cons b w2 rest2) (None (Bin)))
        ((Nil b)
          (match many (and (predates _) (not (predates _) (tagged-of (predates _) disc ss)) (others-bare (predates _) ss w)) _
            ((BTrue) (Some (Bin) w))
            ((BFalse) (None (Bin)))))))))

(def-fns _ $ many ctor-records : (subterm many (List (CShape)) ss) (many (Env) env) (many (Nat) index) (many (Bool) tagged) (many (Maybe (String)) ext) -> (many (List (Ctor)) r)
  (match many ss _
    ((Nil a) (Nil (Ctor)))
    ((Cons a s rest)
      (match many s _
        ((MkCShape m c n) (Cons (Ctor) (MkCtor (name-of (predates _) env c) c index n tagged ext) (ctor-records (subterm _) rest env (Succ index) tagged ext)))))))

(def-fns _ $ many matchable-code : (many (Env) env) (many (Mult) pos) (many (Bin) x) -> (many (Code) r)
  (match many pos _
    ((Erased) (CErased))
    ((Many) (match many (adt-of (predates _) env x) _ ((Some a adt) (CConst (VMatchable adt))) ((None a) (CVar x))))))

; A match on an ADT the elaborator can see reads no Matchable at runtime (section 17).
(def-fns _ $ many match-shape : (many (Env) env) (many (Bin) x) (many (Bool) tagged) -> (many (Shape) r)
  (match many (adt-of (predates _) env x) _ ((Some a adt) (ShKnown adt)) ((None a) (ShHeld (CVar x) tagged))))


(def-fns _ $ many mint : (many (Env) env) (many (Term) ty) -> (many (Env) r) (many (Res) res)
  (let (many env2) (many x) (bind (predates _) env (None (String)) (Erased) (SDyn) ty (None (Term)) coercible-id))
  (values env2 (res-of (predates _) env2 x)))


(def-fns _ $ many fact-of : (many (Env) env) (many (Sg) sg) -> (many (Term) ty) (many (Maybe (Term)) rule)
  (match many sg _
    ((SgTy t) (values t (None (Term))))
    ((SgIs t) (values (infer (predates _) t env) (Some (Term) t)))))

(def-fns _ $ many proof-type : (many (Bin) ctor) (many (List (Term)) args) -> (many (Term) t)
  (TApp (TVar ctor) args))

; The arguments of a proof's type, or an empty list where it is not the expected proof.
(def-fns _ $ many proof-args : (many (Env) env) (many (Term) p) -> (many (List (Term)) args)
  (match many (canon-env (predates _) env (infer (predates _) p env)) _
    ((TApp h args) args)
    ((TVar x) (Nil (Term))) ((TBound k) (Nil (Term))) ((TFn l ps rs) (Nil (Term))) ((TTyCtor ps) (Nil (Term)))
    ((TValCtor ps r) (Nil (Term))) ((TMatchable d t cs) (Nil (Term))) ((TNewtype c) (Nil (Term))) ((TErr m) (Nil (Term)))))

(def-fns _ $ many nth-term : (many (List (Term)) ts) (many (Nat) i) -> (many (Term) t)
  (match many (list-nth (predates _) (Term) ts i) _ ((None a) (TErr "missing argument")) ((Some a t) t)))

; Values for binders, many ones from the list in order, erased ones the token.
(def-fns _ $ many spread : (subterm many (List (Mult)) mults) (many (List (Value)) vs) -> (many (List (Value)) r)
  (match many mults _
    ((Nil a) (Nil (Value)))
    ((Cons a m rest)
      (match many m _
        ((Erased) (Cons (Value) (VToken) (spread (subterm _) rest vs)))
        ((Many)
          (match many vs _
            ((Nil b) (Cons (Value) (VError "missing value") (spread (subterm _) rest vs)))
            ((Cons b v vrest) (Cons (Value) v (spread (subterm _) rest vrest)))))))))

(def-fns _ $ many non-erased : (subterm many (List (Bin)) ids) (many (Env) env) -> (many (List (Bin)) r)
  (match many ids _
    ((Nil a) (Nil (Bin)))
    ((Cons a x rest)
      (match many (entry-mult-of (predates _) env x) _
        ((Many) (Cons (Bin) x (non-erased (subterm _) rest env)))
        ((Erased) (non-erased (subterm _) rest env))))))

(def-fns _ $ many ress-of : (subterm many (List (Bin)) ids) (many (Env) env) -> (many (List (Res)) r)
  (match many ids _
    ((Nil a) (Nil (Res)))
    ((Cons a x rest) (Cons (Res) (res-of (predates _) env x) (ress-of (subterm _) rest env)))))

(def-fns _ $ many tvars-rev : (subterm many (List (Bin)) ids) (many (List (Term)) acc) -> (many (List (Term)) r)
  (match many ids _
    ((Nil a) acc)
    ((Cons a x rest) (tvars-rev (subterm _) rest (Cons (Term) (TVar x) acc)))))

(def-fns _ $ many under-list : (subterm many (List (Mult)) ms) (many (Mult) pos) -> (many (List (Mult)) r)
  (match many ms _
    ((Nil a) (Nil (Mult)))
    ((Cons a m rest) (Cons (Mult) (under (predates _) pos m) (under-list (subterm _) rest pos)))))

(def-fns _ $ many all-erased : (subterm many (List (Mult)) ms) -> (many (List (Mult)) r)
  (match many ms _
    ((Nil a) (Nil (Mult)))
    ((Cons a m rest) (Cons (Mult) (Erased) (all-erased (subterm _) rest)))))

(def-fns _ $ many states-of : (subterm many (List (Value)) vs) -> (many (List (State)) r)
  (match many vs _
    ((Nil a) (Nil (State)))
    ((Cons a v rest) (Cons (State) (SConst v) (states-of (subterm _) rest)))))

; Whether a call's code needs projecting: some many return taken erased by the position (ASSUMPTIONS 39).
(def-fns _ $ many needs-projection : (subterm many (List (Mult)) expect) (many (List (Mult)) rets) -> (many (Bool) r)
  (match many expect _
    ((Nil a) (BFalse))
    ((Cons a m rest)
      (match many rets _
        ((Nil b) (BFalse))
        ((Cons b rm rrest)
          (match many (and (predates _) (not (predates _) (mult-is-many (predates _) m)) (mult-is-many (predates _) rm)) _
            ((BTrue) (BTrue))
            ((BFalse) (needs-projection (subterm _) rest rrest))))))))

; Binds fresh ids for the many returns and keeps those the position takes many (ASSUMPTIONS 39).
(def-fns _ $ many projection : (subterm many (List (Mult)) expect) (many (List (Mult)) rets) (many (Env) env) -> (many (Env) r) (many (List (Bin)) bound) (many (List (Code)) kept)
  (match many expect _
    ((Nil a) (values env (Nil (Bin)) (Nil (Code))))
    ((Cons a m rest)
      (match many rets _
        ((Nil b) (values env (Nil (Bin)) (Nil (Code))))
        ((Cons b rm rrest)
          (match many rm _
            ((Erased) (projection (subterm _) rest rrest env))
            ((Many)
              (let (many env2) (many t) (env-fresh-id (predates _) env))
              (let (many env3) (many bound) (many kept) (projection (subterm _) rest rrest env2))
              (values env3 (Cons (Bin) t bound) (match many m (((List (Code)) l)) ((Many) (Cons (Code) (CVar t) kept)) ((Erased) kept))))))))))

; Strips the call-site decrease annotations, (predates p) and (subterm p) (section 9).
(def-fns _ $ many strip-annotations : (subterm many (List (Raw)) args) (many (Env) env) -> (many (List (Raw)) r)
  (match many args _
    ((Nil a) (Nil (Raw)))
    ((Cons a arg rest)
      (let (many ann)
        (match many (raw-items (predates _) arg) (((Bool) b))
          ((Nil b) (BFalse))
          ((Cons b k krest)
            (match many krest (((Bool) b))
              ((Nil c) (BFalse))
              ((Cons c p prest)
                (match many prest (((Bool) b))
                  ((Cons d q qrest) (BFalse))
                  ((Nil d) (or (predates _) (is-mark (predates _) env k (MkPredates)) (is-mark (predates _) env k (MkSubterm))))))))))
      (match many ann _
        ((BTrue) (strip-annotations (subterm _) rest env))
        ((BFalse) (Cons (Raw) arg (strip-annotations (subterm _) rest env)))))))

; The delegate-marked call's callee in a body, if any (section 9); read through lets and match branches.
(def-fns _
  (many find-delegate : (subterm many (Code) code) -> (many (Maybe (Bin)) r)
    (match many code _
      ((CApp f args cc)
        (match many cc _
          ((CCDelegate) (match many f _ ((CVar x) (Some (Bin) x)) ((CConst v) (None (Bin))) ((CErased) (None (Bin))) ((CValues cs) (None (Bin)))
                          ((CApp g a c) (None (Bin))) ((CLet i r b) (None (Bin))) ((CLetRec fs b) (None (Bin))) ((CMatch s sh bs) (None (Bin)))
                          ((CAbsurd) (None (Bin))) ((CError m) (None (Bin)))))
          ((CCPlain) (None (Bin))) ((CCTail) (None (Bin))) ((CCCtor) (None (Bin)))))
      ((CLet ids rhs rest) (match many (find-delegate (subterm _) rhs) _ ((Some a x) (Some (Bin) x)) ((None a) (find-delegate (subterm _) rest))))
      ((CLetRec fns rest) (find-delegate (subterm _) rest))
      ((CMatch scrut shape branches) (find-delegate-branches (subterm _) branches))
      ((CVar x) (None (Bin))) ((CConst v) (None (Bin))) ((CErased) (None (Bin))) ((CValues cs) (None (Bin))) ((CAbsurd) (None (Bin))) ((CError m) (None (Bin)))))
  (many find-delegate-branches : (subterm many (List (Branch)) bs) -> (many (Maybe (Bin)) r)
    (match many bs _
      ((Nil a) (None (Bin)))
      ((Cons a b rest)
        (match many b _
          ((MkBranch d ids body)
            (match many (find-delegate (subterm _) body) _
              ((Some c x) (Some (Bin) x))
              ((None c) (find-delegate-branches (subterm _) rest)))))))))


; ---- Opening telescopes into scope

(def-adts $ MultsMode : -> Type
  enum
  (many MMDeclared : -> (MultsMode))
  (many MMErased : -> (MultsMode))
  (many MMExpect : (many (List (Mult)) ms) -> (MultsMode)))

; [ids]: terms of the binders already in force, innermost first. Binds one fresh entry per item and returns
; their ids in order; names, multiplicities and states override the telescope's own when given.
(def-fns _ $ many open-tele : (subterm many (List (Entry)) tele) (many (Env) env) (many (Maybe (List (Maybe (String)))) names) (many (Maybe (List (Mult))) mults) (many (Maybe (List (State))) states) (many (List (Term)) ids) ->
    (many (Env) r) (many (List (Bin)) fresh)
  (match many tele _
    ((Nil a) (values env (Nil (Bin))))
    ((Cons a e rest)
      (match many e _
        ((MkEntry ename esub emult esg)
          (let (many sg2) (match many esg (((Sg) s)) ((SgTy t) (SgTy (instantiate (predates _) ids t))) ((SgIs t) (SgIs (instantiate (predates _) ids t)))))
          (let (many ty) (many rule) (fact-of (predates _) env sg2))
          (let (many name) (many names2)
            (match many names (((Maybe (String)) n) ((Maybe (List (Maybe (String)))) ns))
              ((None b) (values ename names))
              ((Some b ns) (match many ns (((Maybe (String)) n) ((Maybe (List (Maybe (String)))) ns2)) ((Nil c) (values ename names)) ((Cons c n nrest) (values n (Some (List (Maybe (String))) nrest)))))))
          (let (many mult) (many mults2)
            (match many mults (((Mult) m) ((Maybe (List (Mult))) ms))
              ((None b) (values emult mults))
              ((Some b ms) (match many ms (((Mult) m) ((Maybe (List (Mult))) ms2)) ((Nil c) (values emult mults)) ((Cons c m mrest) (values m (Some (List (Mult)) mrest)))))))
          (let (many st) (many states2)
            (match many states (((State) s) ((Maybe (List (State))) ss))
              ((None b) (values (SDyn) states))
              ((Some b ss) (match many ss (((State) s) ((Maybe (List (State))) ss2)) ((Nil c) (values (SDyn) states)) ((Cons c s srest) (values s (Some (List (State)) srest)))))))
          (let (many env2) (many x) (bind (predates _) env name mult st ty rule coercible-id))
          (let (many env3) (many more) (open-tele (subterm _) rest env2 names2 mults2 states2 (Cons (Term) (TVar x) ids)))
          (values env3 (Cons (Bin) x more)))))))

(def-fns _ $ many anon-names : (subterm many (List (Entry)) tele) -> (many (List (Maybe (String))) r)
  (match many tele _
    ((Nil a) (Nil (Maybe (String))))
    ((Cons a e rest) (Cons (Maybe (String)) (None (String)) (anon-names (subterm _) rest)))))

(def-fns _ $ many raw-names : (subterm many (List (Raw)) rs) -> (many (List (Maybe (String))) r)
  (match many rs _
    ((Nil a) (Nil (Maybe (String))))
    ((Cons a r rest) (Cons (Maybe (String)) (name-or-anon (predates _) (raw-name (predates _) r)) (raw-names (subterm _) rest)))))

; Entering a branch forces the scrutinee equal to the constructor over its fields (section 18).

(def-fns _ $ many subterm-params : (subterm many (List (Entry)) tele) (many (List (Bin)) ids) -> (many (List (Bin)) r)
  (match many tele _
    ((Nil a) (Nil (Bin)))
    ((Cons a e rest)
      (match many ids _
        ((Nil b) (Nil (Bin)))
        ((Cons b x irest)
          (match many (entry-sub (predates _) e) _
            ((BTrue) (Cons (Bin) x (subterm-params (subterm _) rest irest)))
            ((BFalse) (subterm-params (subterm _) rest irest))))))))

; Per-value multiplicities of the binders of a let or the entries of a signature.
(def-fns _ $ many src-mults : (erased (List (Raw)) root) (subterm many (List (SrcEntry root)) es) -> (many (List (Mult)) r)
  (match many es _
    ((Nil a) (Nil (Mult)))
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry rt sub m sg n) (Cons (Mult) (match many m (((Mult) x)) ((None b) (Many)) ((Some b mm) mm)) (src-mults root (subterm _) rest)))))))


; ---- Checks (section 5's canonicalize-then-compare) and proofs (section 8)

(def-fns _ $ many check : (many (Env) env) (many (String) what) (many (Term) actual) (many (Term) expected) -> (many (Env) r)
  (match many (equal-env (predates _) env actual expected) _
    ((BTrue) env)
    ((BFalse) (env-error (predates _) env (str-cat3 (predates _) what " mismatch: expected " (str-cat3 (predates _) (show-t (predates _) env expected) ", got " (show-t (predates _) env actual)))))))

(def-fns _ $ many check-sg : (many (Env) env) (many (Sg) sg) (many (Res) r) -> (many (Env) e)
  (match many sg _
    ((SgTy ty) (check (predates _) env "type" (res-ty (predates _) r) ty))
    ((SgIs t) (check (predates _) env "value" (res-term (predates _) r) t))))

(def-fns _ $ many count-error : (many (Env) env) (many (String) what) (many (Nat) expected) (many (Nat) got) -> (many (Env) r)
  (env-error (predates _) env (str-cat3 (predates _) "expected " (nat-str (predates _) expected) (str-cat3 (predates _) what ", got " (nat-str (predates _) got)))))

; Results against a return telescope; [ids] as in open-tele.
(def-fns _ $ many check-results : (subterm many (List (Entry)) tele) (many (Env) env) (many (List (Res)) ress) (many (List (Term)) ids) -> (many (Env) r)
  (match many tele _
    ((Nil a) (match many ress _ ((Nil b) env) ((Cons b r rest) (env-error (predates _) env "expected fewer values"))))
    ((Cons a e rest)
      (match many ress _
        ((Nil b) (env-error (predates _) env "expected more values"))
        ((Cons b r rrest)
          (let (many sg) (match many (entry-sg (predates _) e) (((Sg) s)) ((SgTy t) (SgTy (instantiate (predates _) ids t))) ((SgIs t) (SgIs (instantiate (predates _) ids t)))))
          (check-results (subterm _) rest (check-sg (predates _) env sg r) rrest (Cons (Term) (res-term (predates _) r) ids)))))))

(def-fns _ $ many check-results-count : (many (Env) env) (many (List (Entry)) tele) (many (List (Res)) ress) (many (List (Term)) ids) -> (many (Env) r)
  (let (many n) (list-length (predates _) (Entry) tele))
  (let (many m) (list-length (predates _) (Res) ress))
  (match many (nat-eq (predates _) n m) _
    ((BTrue) (check-results (predates _) tele env ress ids))
    ((BFalse) (count-error (predates _) env " values" n m))))

(def-fns _
  (many is-strict-subterm : (subterm many (Term) b) (many (Term) a) -> (many (Bool) r)
    (match many b _
      ((TApp h args) (subterm-in (subterm _) args a))
      ((TVar x) (BFalse)) ((TBound k) (BFalse)) ((TFn l p rr) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p rr) (BFalse))
      ((TMatchable d t c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
  (many subterm-in : (subterm many (List (Term)) ts) (many (Term) a) -> (many (Bool) r)
    (match many ts _
      ((Nil x) (BFalse))
      ((Cons x t rest) (or (predates _) (term-eq (predates _) a t) (or (predates _) (is-strict-subterm (subterm _) t a) (subterm-in (subterm _) rest a)))))))

; prove-subterm (section 8): the first, canonicalized, is a strict subtree of the second through constructor
; applications only.
(def-fns _ $ many mint-subterm : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Env) r) (many (Res) res)
  (let (many ca) (canon-env (predates _) env a))
  (let (many cb) (canon-env (predates _) env b))
  (let (many env2)
    (match many (is-strict-subterm (predates _) cb ca) (((Env) e))
      ((BTrue) env)
      ((BFalse) (env-error (predates _) env (str-cat3 (predates _) (show-t (predates _) env a) " is not a strict subterm of " (show-t (predates _) env b))))))
  (mint (predates _) env2 (proof-type (predates _) subterm-id (Cons (Term) (infer (predates _) a env2) (Cons (Term) a (Cons (Term) (infer (predates _) b env2) (Cons (Term) b (Nil (Term)))))))))

; prove-predates (section 8): the variable was in scope when the level was minted (ASSUMPTIONS 13).
(def-fns _ $ many mint-predates : (many (Env) env) (many (Bin) x0) (many (Bin) lvl) -> (many (Env) r) (many (Res) res)
  (let (many env2)
    (match many (entry-minted (predates _) env lvl) (((Env) e))
      ((BTrue) env)
      ((BFalse) (env-error (predates _) env (str-cat (predates _) (name-of (predates _) env lvl) " is not a level minted by def-lvl")))))
  (let (many x)
    (match many (bin-lt (predates _) x0 lvl) (((Bin) y))
      ((BTrue) x0)
      ((BFalse) (match many (canon-env (predates _) env2 (TVar x0)) (((Bin) y)) ((TVar y) y) ((TBound k) x0) ((TApp h a) x0) ((TFn l p r) x0) ((TTyCtor p) x0) ((TValCtor p r) x0) ((TMatchable d t c) x0) ((TNewtype c) x0) ((TErr m) x0)))))
  (let (many env3)
    (match many (bin-lt (predates _) x lvl) (((Env) e))
      ((BTrue) env2)
      ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) (name-of (predates _) env2 x) " was not in scope when level " (str-cat (predates _) (name-of (predates _) env2 lvl) " was minted"))))))
  (mint (predates _) env3 (proof-type (predates _) predates-id (Cons (Term) (type-of (predates _) env3 x) (Cons (Term) (TVar x) (Cons (Term) (TVar lvl) (Nil (Term))))))))

; The arguments of a proof of the given kind, with an error where the term is not one.
(def-fns _ $ many proof-args : (many (Env) env) (many (Bin) ctor) (many (Term) p) -> (many (Maybe (List (Term))) r)
  (match many (canon-env (predates _) env (infer (predates _) p env)) _
    ((TApp h args) (match many h _ ((TVar c) (match many (bin-eq (predates _) c ctor) _ ((BTrue) (Some (List (Term)) args)) ((BFalse) (None (List (Term))))))
                     ((TBound k) (None (List (Term)))) ((TApp h2 a2) (None (List (Term)))) ((TFn l pp rr) (None (List (Term)))) ((TTyCtor pp) (None (List (Term))))
                     ((TValCtor pp rr) (None (List (Term)))) ((TMatchable d t c) (None (List (Term)))) ((TNewtype c) (None (List (Term)))) ((TErr m) (None (List (Term))))))
    ((TVar x) (None (List (Term)))) ((TBound k) (None (List (Term)))) ((TFn l pp rr) (None (List (Term)))) ((TTyCtor pp) (None (List (Term))))
    ((TValCtor pp rr) (None (List (Term)))) ((TMatchable d t c) (None (List (Term)))) ((TNewtype c) (None (List (Term)))) ((TErr m) (None (List (Term))))))

(def-fns _ $ many not-a-proof : (many (Env) env) (many (Bin) ctor) (many (Term) p) -> (many (Env) r)
  (env-error (predates _) env (str-cat3 (predates _) "expected a " (name-of (predates _) env ctor) (str-cat3 (predates _) " proof, got " (show-t (predates _) env p) (str-cat (predates _) " : " (show-t (predates _) env (infer (predates _) p env)))))))

; The three arguments of a Predates proof, or the four of a Subterm or Coercible proof (section 8).
(def-fns _ $ many expect-proof3 : (many (Env) env) (many (Bin) ctor) (many (Term) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2)
  (let (many bad) (many e0) (many e1) (many e2) (values (not-a-proof (predates _) env ctor p) (TErr "proof") (TErr "proof") (TErr "proof")))
  (match many (proof-args (predates _) env ctor p) _
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

(def-fns _ $ many expect-proof4 : (many (Env) env) (many (Bin) ctor) (many (Term) p) -> (many (Env) r) (many (Term) t0) (many (Term) t1) (many (Term) t2) (many (Term) t3)
  (let (many bad) (many e0) (many e1) (many e2) (many e3) (values (not-a-proof (predates _) env ctor p) (TErr "proof") (TErr "proof") (TErr "proof") (TErr "proof")))
  (match many (proof-args (predates _) env ctor p) _
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

(def-fns _ $ many sp-name-in : (subterm many (List (SpEntry)) es) (many (Sp) sp) -> (many (String) name)
  (match many es _
    ((Nil a) "?")
    ((Cons a e rest) (match many e _ ((MkSpEntry n s) (match many (sp-eq (predates _) s sp) _ ((BTrue) n) ((BFalse) (sp-name-in (subterm _) rest sp))))))))

(def-fns _ $ many sp-name : (many (Sp) sp) -> (many (String) name)
  (sp-name-in (predates _) sp-table sp))

; The candidates are ranked; several must agree (section 19), else the ambiguity is an error.
(def-fns _ $ many agree : (subterm many (List (Bin)) objects) (many (Env) env) (many (Bin) tid) (many (Term) best) -> (many (Bool) r)
  (match many objects _
    ((Nil a) (BTrue))
    ((Cons a x rest)
      (let (many ty) (type-of (predates _) env x))
      (let (many mine)
        (match many ty (((Bool) b))
          ((TMatchable d t cs) (match many t (((Bool) b)) ((TVar t2) (bin-eq (predates _) t2 tid)) ((TBound k) (BFalse)) ((TApp h as) (BFalse)) ((TFn l p r) (BFalse))
                                 ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse)) ((TMatchable d2 t2 c2) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
          ((TVar y) (BFalse)) ((TBound k) (BFalse)) ((TApp h as) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse))
          ((TValCtor p r) (BFalse)) ((TNewtype c2) (BFalse)) ((TErr m) (BFalse))))
      (match many mine _
        ((BFalse) (agree (subterm _) rest env tid best))
        ((BTrue) (and (predates _) (term-eq (predates _) ty best) (agree (subterm _) rest env tid best)))))))

(def-fns _ $ many find-matchable : (many (Env) env) (many (Bin) tid) -> (many (Env) r) (many (Maybe (MatchInfo)) info)
  (match many (find-matchable-in (predates _) (env-objects (predates _) env) env tid (None (MatchInfo))) _
    ((None a) (values env (None (MatchInfo))))
    ((Some a info)
      (match many info _
        ((MkMatchInfo mid d cs rank)
          (match many (agree (predates _) (env-objects (predates _) env) env tid (type-of (predates _) env mid)) _
            ((BTrue) (values env (Some (MatchInfo) info)))
            ((BFalse) (values (env-error (predates _) env (str-cat (predates _) "ambiguous Matchables for " (name-of (predates _) env tid))) (Some (MatchInfo) info)))))))))

(def-fns _ $ many phantom : (many (Env) env) (many (Bin) c) -> (many (Bool) r)
  (let (many env2) (many found) (find-matchable (predates _) env (tid-of (predates _) env c)))
  (match many found _
    ((None a) (BFalse))
    ((Some a info) (match many info _ ((MkMatchInfo mid d cs rank) (match many (marker (predates _) cs c) _ ((Erased) (BTrue)) ((Many) (BFalse))))))))

; A type is empty when its Matchable lists no constructor (section 37).
(def-fns _ $ many check-empty : (many (Env) env) (many (Term) ty) -> (many (Env) r)
  (let (many empty)
    (match many (type-head (predates _) env ty) (((Bool) b))
      ((None a) (BFalse))
      ((Some a t)
        (let (many env2) (many found) (find-matchable (predates _) env t))
        (match many found (((Bool) b))
          ((None b) (BFalse))
          ((Some b info) (match many info (((Bool) b)) ((MkMatchInfo mid d cs rank) (list-is-empty (predates _) (MCtor) cs))))))))
  (match many empty _
    ((BTrue) env)
    ((BFalse) (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env ty) " is not an empty type")))))

(def-fns _ $ many mint-level : (many (Env) env) (many (Maybe (String)) name) -> (many (Env) r) (many (Bin) x)
  (let (many st) (match many (env-run-pos (predates _) env) (((State) s)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn))))
  (let (many env2) (many x) (bind (predates _) env name (Erased) st level-term (None (Term)) coercible-id))
  (values (mark-minted (predates _) env2 x) x))

; Entering a branch forces the scrutinee equal to the constructor over its fields, and its type to the
; constructor's return (section 18).
(def-fns _ $ many refine : (many (Env) env) (many (Res) scrut) (many (Bin) c) (many (List (Bin)) fids) (many (Term) ret) -> (many (UnifyRes) r)
  (let (many fvars) (tvars-rev (predates _) fids (Nil (Term))))
  (match many (unify-env (predates _) env (res-term (predates _) scrut) (TApp (TVar c) (list-rev (predates _) (Term) fvars))) _
    ((UContra m) (UContra m))
    ((UOk env2) (unify-env (predates _) env2 (res-ty (predates _) scrut) (instantiate (predates _) fvars ret)))))

(def-fns _ $ many disc-of-checked : (many (Env) env) (many (Raw) d) -> (many (Env) r) (many (Disc) disc)
  (match many (is-mark (predates _) env d (MkUnion)) _
    ((BTrue) (values env (DUnion)))
    ((BFalse)
      (match many (is-mark (predates _) env d (MkEnum)) _
        ((BTrue) (values env (DEnum)))
        ((BFalse) (values (env-error (predates _) env "expected enum or union") (DEnum)))))))

; A claim on the FFI's fixed table (ASSUMPTIONS 42): each implementation backs one declaration per program.
(def-fns _ $ many claim-extern : (many (Env) env) (many (String) name) (many (Bool) known) -> (many (Env) r)
  (match many known _
    ((BFalse) (env-error (predates _) env (str-cat (predates _) "no extern implementation for " name)))
    ((BTrue)
      (match many (list-mem-str (predates _) (env-claimed (predates _) env) name) _
        ((BTrue) (env-error (predates _) env (str-cat3 (predates _) "the extern implementation of " name " is already bound")))
        ((BFalse) (env-claim (predates _) env name))))))


; ---- Small helpers the block's checks use

(def-fns _ $ many not-applicable : (many (Env) env) (many (Res) h) -> (many (String) s)
  (str-cat3 (predates _) (show-t (predates _) env (res-term (predates _) h)) " : " (str-cat (predates _) (show-t (predates _) env (res-ty (predates _) h)) " is not applicable")))

(def-fns _ $ many cannot-apply-in-type : (many (Env) env) (many (Term) h) -> (many (String) s)
  (str-cat3 (predates _) (show-t (predates _) env h) " has type " (str-cat (predates _) (show-t (predates _) env (infer (predates _) h env)) " and cannot be applied in a type")))

(def-fns _ $ many call-needs : (many (Env) env) (many (Res) callee) (many (Bool) same) -> (many (String) s)
  (match many same _
    ((BTrue) (str-cat3 (predates _) "same-level call to " (show-t (predates _) env (res-term (predates _) callee)) " needs a (subterm p) annotation"))
    ((BFalse) (str-cat3 (predates _) "lower-level call to " (show-t (predates _) env (res-term (predates _) callee)) " needs a (predates p) annotation"))))

(def-fns _ $ many level-of-error : (many (Env) env) (many (Term) f) (many (Term) ty) -> (many (String) s)
  (str-cat3 (predates _) "level-of: " (show-t (predates _) env f) (str-cat3 (predates _) " : " (show-t (predates _) env ty) " is not a function")))

; A constructor named in source, read through its alias, which must hold a value constructor.
(def-fns _ $ many ctor-var : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Bin) c)
  (let (many env2) (many c) (named (predates _) env raw "a constructor"))
  (match many (type-of (predates _) env2 c) _
    ((TValCtor tele ret) (values env2 c))
    ((TVar x) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TBound k) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TApp h a) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TFn l p r) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TTyCtor p) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TMatchable d t cs) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TNewtype x) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is not a value constructor")) c))
    ((TErr m) (values env2 c))))

(def-fns _ $ many parse-entries-checked : (erased (List (Raw)) root) (subterm many (List (Sub root)) subs) (many (Env) env) -> (many (Env) r) (many (List (SrcEntry root)) es)
  (match many subs _
    ((Nil a) (values env (Nil (SrcEntry root))))
    ((Cons a s rest)
      (let (many env1) (many here)
        (match many s (((Env) e) ((List (SrcEntry root)) l))
          ((MkSub rt r p)
            (match many (raw-atom (predates _) r) (((Env) e) ((List (SrcEntry root)) l))
              ((Some b str) (values (env-error (predates _) env (str-cat (predates _) "expected a telescope entry, got " str)) (Nil (SrcEntry root))))
              ((None b)
                (let (many es) (parse-entry (predates _) env r root p))
                (match many es (((Env) e) ((List (SrcEntry root)) l))
                  ((Nil c) (values (env-error (predates _) env (str-cat (predates _) "malformed telescope entry " (show-r (predates _) r))) es))
                  ((Cons c x more) (values env es))))))))
      (let (many env2) (many more) (parse-entries-checked root (subterm _) rest env1))
      (values env2 (list-append (predates _) (SrcEntry root) here more)))))

(def-fns _ $ many check-binder-mults : (erased (List (Raw)) root) (subterm many (List (SrcEntry root)) es) (many (Env) env) -> (many (Env) r)
  (match many es _
    ((Nil a) env)
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry rt sub m sg n)
          (match many m _
            ((Some b mm) (check-binder-mults root (subterm _) rest env))
            ((None b) (check-binder-mults root (subterm _) rest (env-error (predates _) env "let binder needs a multiplicity")))))))))

(def-fns _ $ many mult-checked : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Mult) m)
  (match many (mult-of (predates _) env raw) _
    ((Some a m) (values env m))
    ((None a) (values (env-error (predates _) env (str-cat (predates _) "expected a multiplicity, got " (show-r (predates _) raw))) (Many)))))

(def-fns _ $ many level-var-checked : (many (Env) env) (many (Term) t) -> (many (Env) r) (many (Bin) x)
  (let (many bad) (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env t) " is not a level")))
  (match many (canon-env (predates _) env t) _
    ((TVar x) (match many (equal-env (predates _) env (type-of (predates _) env x) level-term) _ ((BTrue) (values env x)) ((BFalse) (values bad x))))
    ((TBound k) (values bad (BZ))) ((TApp h a) (values bad (BZ))) ((TFn l p r) (values bad (BZ))) ((TTyCtor p) (values bad (BZ)))
    ((TValCtor p r) (values bad (BZ))) ((TMatchable d ty c) (values bad (BZ))) ((TNewtype c) (values bad (BZ))) ((TErr m) (values bad (BZ)))))

(def-fns _ $ many one-arg : (many (List (Raw)) args) -> (many (Raw) r)
  (match many args _ ((Nil a) (RAtom 0 "_")) ((Cons a r rest) r)))

(def-fns _ $ many comptime-shape : (many (List (Raw)) args) -> (many (Maybe (Pair (Raw) (Pair (Raw) (List (Raw))))) r)
  (match many args _
    ((Nil a) (None (Pair (Raw) (Pair (Raw) (List (Raw))))))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (None (Pair (Raw) (Pair (Raw) (List (Raw))))))
        ((Cons b pat more)
          (match many more _
            ((Cons c y z) (None (Pair (Raw) (Pair (Raw) (List (Raw))))))
            ((Nil c)
              (match many (raw-items (predates _) pat) _
                ((Nil d) (None (Pair (Raw) (Pair (Raw) (List (Raw))))))
                ((Cons d craw fields)
                  (match many (atoms-only (predates _) fields) _
                    ((BTrue) (Some (Pair (Raw) (Pair (Raw) (List (Raw)))) (MkPair (Raw) (Pair (Raw) (List (Raw))) x (MkPair (Raw) (List (Raw)) craw fields))))
                    ((BFalse) (None (Pair (Raw) (Pair (Raw) (List (Raw))))))))))))))))

; numeral-of (ASSUMPTIONS 53): a numeral or character literal by its own spelling, never an expression.
(def-fns _ $ many numeral-of-key : (many (Env) env) (many (String) key) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
  (match many (lit-lookup (predates _) env key) _
    ((None a) (values (env-error (predates _) env (str-cat3 (predates _) "literal " key " is not in scope")) (Nil (Res)) (CError "numeral-of")))
    ((Some a x)
      (match many (lit-proof (predates _) (env-lits (predates _) env) x) _
        ((None b) (values (env-error (predates _) env (str-cat (predates _) key " is a string literal, which carries no Numeral proof")) (Nil (Res)) (CError "numeral-of")))
        ((Some b p) (values env (Cons (Res) (res-of (predates _) env p) (Nil (Res))) (CErased)))))))

(def-fns _ $ many numeral-of-lit : (many (Env) env) (many (Raw) arg) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
  (match many arg _
    ((RList lq items) (values (env-error (predates _) env (str-cat (predates _) "expected a literal, got " (show-r (predates _) arg))) (Nil (Res)) (CError "numeral-of")))
    ((RString lq s) (values (env-error (predates _) env (str-cat (predates _) (show-r (predates _) arg) " is a string literal, which carries no Numeral proof")) (Nil (Res)) (CError "numeral-of")))
    ((RAtom lq s)
      (match many (literal-error (predates _) s) _
        ((Some a msg) (values (env-error (predates _) env msg) (Nil (Res)) (CError "numeral-of")))
        ((None a)
          (match many (classify (predates _) s) _
            ((LName) (values (env-error (predates _) env (str-cat (predates _) "numeral-of takes a literal, not " s)) (Nil (Res)) (CError "numeral-of")))
            ((LNumeral) (numeral-of-key (predates _) env s))
            ((LChar) (numeral-of-key (predates _) env s))))))))

; The number a numeral or character literal spells, if the raw is one (lib/literal.ml's classify).
(def-fns _ $ many lit-number : (many (Raw) raw) -> (many (Maybe (Nat)) n)
  (match many raw _
    ((RList lq items) (None (Nat)))
    ((RString lq s) (None (Nat)))
    ((RAtom lq s)
      (match many (literal-error (predates _) s) _
        ((Some a msg) (None (Nat)))
        ((None a)
          (match many (classify (predates _) s) _
            ((LName) (None (Nat)))
            ((LNumeral) (Some (Nat) (parse-nat (predates _) s 0)))
            ((LChar) (char-lit-code (predates _) s))))))))

; The entry holding the Nat a numeral or character literal stands for, a character's being its code's
; (lib/elab.ml's numeral_entry).
(def-fns _ $ many numeral-entry : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Maybe (Pair (Nat) (Bin))) e)
  (match many (lit-number (predates _) raw) _
    ((None a)
      (values (env-error (predates _) env
                (match many raw (((String) m))
                  ((RAtom lq s) (str-cat (predates _) s " is not a numeral or character literal"))
                  ((RString lq s) (str-cat (predates _) "expected a numeral or character literal, got " (show-r (predates _) raw)))
                  ((RList lq items) (str-cat (predates _) "expected a numeral or character literal, got " (show-r (predates _) raw)))))
              (None (Pair (Nat) (Bin)))))
    ((Some a z)
      (match many (lit-lookup (predates _) env (nat-str (predates _) z)) _
        ((None b) (values (env-error (predates _) env (str-cat3 (predates _) "literal " (nat-str (predates _) z) " is not in scope")) (None (Pair (Nat) (Bin)))))
        ((Some b x) (values env (Some (Pair (Nat) (Bin)) (MkPair (Nat) (Bin) z x))))))))

; A generated form is read and its literals interned in the prelude's scope, so user shadowing cannot
; reach it, and the caller's scope restored after; the level context, and so (predates _), stays the
; caller's throughout (lib/elab.ml's in_prelude).
(def-fns _ $ many generated-form : (many (String) src) (many (Env) env) -> (many (Env) r) (many (Maybe (Raw)) g)
  (let (many gens) (many err) (parse (predates _) src))
  (match many gens _
    ((Nil a) (values (env-error (predates _) env "internal: a generated form does not read") (None (Raw))))
    ((Cons a g more) (values (intern-literals (predates _) g (env-set-scope (predates _) env (env-prelude (predates _) env))) (Some (Raw) g)))))

(def-fns _ $ many leave-prelude : (many (Env) outer) (many (Env) inner) -> (many (Env) r)
  (env-set-scope (predates _) inner (env-scope (predates _) outer)))

(def-fns _ $ many cc-eq : (many (CC) a) (many (CC) b) -> (many (Bool) r)
  (match many a _
    ((CCPlain) (match many b _ ((CCPlain) (BTrue)) ((CCTail) (BFalse)) ((CCDelegate) (BFalse)) ((CCCtor) (BFalse))))
    ((CCTail) (match many b _ ((CCPlain) (BFalse)) ((CCTail) (BTrue)) ((CCDelegate) (BFalse)) ((CCCtor) (BFalse))))
    ((CCDelegate) (match many b _ ((CCPlain) (BFalse)) ((CCTail) (BFalse)) ((CCDelegate) (BTrue)) ((CCCtor) (BFalse))))
    ((CCCtor) (match many b _ ((CCPlain) (BFalse)) ((CCTail) (BFalse)) ((CCDelegate) (BFalse)) ((CCCtor) (BTrue))))))

(def-fns _ $ many sg-inst : (many (List (Term)) args) (many (Sg) sg) -> (many (Sg) r)
  (match many sg _
    ((SgTy t) (SgTy (instantiate (predates _) args t)))
    ((SgIs t) (SgIs (instantiate (predates _) args t)))))


; A branch of the raw b: present, refuted automatically with (absurd C), or absurd by proof (section 12).
(def-adts $ BranchParts : ((Raw) b) -> Type
  enum
  (many BPresent : (erased (Raw) b) (many (Raw) craw) (many (List (Raw)) fields) (many (List (Raw)) body) (erased (Subterm (List (Raw)) body (Raw) b) p) -> (BranchParts b))
  (many BRefuted : (erased (Raw) b) (many (Raw) craw) -> (BranchParts b))
  (many BAbsurd : (erased (Raw) b) (many (Raw) craw) (many (List (Raw)) fields) (many (List (Raw)) body) (erased (Subterm (List (Raw)) body (Raw) b) p) -> (BranchParts b)))

(def-fns _ $ many pattern-parts : (many (Raw) pat) -> (many (Maybe (Pair (Raw) (List (Raw)))) r)
  (match many pat _
    ((RAtom lq s) (Some (Pair (Raw) (List (Raw))) (MkPair (Raw) (List (Raw)) pat (Nil (Raw)))))
    ((RString lq s) (None (Pair (Raw) (List (Raw)))))
    ((RList lq items)
      (match many items _
        ((Nil a) (None (Pair (Raw) (List (Raw)))))
        ((Cons a c fs) (match many (atoms-only (predates _) fs) _ ((BTrue) (Some (Pair (Raw) (List (Raw))) (MkPair (Raw) (List (Raw)) c fs))) ((BFalse) (None (Pair (Raw) (List (Raw)))))))))))

(def-fns _ $ many branch-parts : (many (Env) env) (many (Raw) braw) -> (many (Maybe (BranchParts braw)) r)
  (match many braw _
    ((RAtom lq s) (None (BranchParts braw)))
    ((RString lq s) (None (BranchParts braw)))
    ((RList lq items)
      (match many items _
        ((Nil a) (None (BranchParts braw)))
        ((Cons a first more)
          (match many (is-mark (predates _) env first (MkAbsurd)) _
            ((BFalse)
              (match many (pattern-parts (predates _) first) _
                ((None b) (None (BranchParts braw)))
                ((Some b pp) (match many pp _ ((MkPair s t c fs) (Some (BranchParts braw) (BPresent braw c fs more (prove-subterm more braw))))))))
            ((BTrue)
              (match many more _
                ((Nil b) (None (BranchParts braw)))
                ((Cons b pat body)
                  (match many body _
                    ((Nil c)
                      (match many (raw-atom (predates _) pat) _
                        ((Some d s) (Some (BranchParts braw) (BRefuted braw pat)))
                        ((None d) (None (BranchParts braw)))))
                    ((Cons c x y)
                      (match many (pattern-parts (predates _) pat) _
                        ((None d) (None (BranchParts braw)))
                        ((Some d pp) (match many pp _ ((MkPair s t cc fs) (Some (BranchParts braw) (BAbsurd braw cc fs body (prove-subterm body braw))))))))))))))))))

(def-fns _ $ many marker-checked : (many (Env) env) (many (Bin) tid) (many (List (MCtor)) mctors) (many (Bin) c) -> (many (Env) r) (many (Mult) m)
  (match many (mctors-list (predates _) mctors c) _
    ((BTrue) (values env (marker (predates _) mctors c)))
    ((BFalse) (values (env-error (predates _) env (str-cat3 (predates _) (name-of (predates _) env c) " is not a constructor of " (name-of (predates _) env tid))) (Many)))))

(def-fns _ $ many count-bins : (subterm many (List (Bin)) xs) (many (Bin) x) -> (many (Nat) n)
  (match many xs _
    ((Nil a) 0)
    ((Cons a y rest) (match many (bin-eq (predates _) x y) _ ((BTrue) (Succ (count-bins (subterm _) rest x))) ((BFalse) (count-bins (subterm _) rest x))))))

; Every constructor of the Matchable appears exactly once (ASSUMPTIONS 21).
(def-fns _ $ many check-coverage : (subterm many (List (MCtor)) mctors) (many (Env) env) (many (List (Bin)) seen) -> (many (Env) r)
  (match many mctors _
    ((Nil a) env)
    ((Cons a mc rest)
      (match many mc _
        ((MkMCtor m t)
          (let (many c) (match many t (((Bin) x)) ((TVar x) x) ((TBound k) (BZ)) ((TApp h as) (BZ)) ((TFn l p r) (BZ)) ((TTyCtor p) (BZ)) ((TValCtor p r) (BZ)) ((TMatchable d t2 cs) (BZ)) ((TNewtype c2) (BZ)) ((TErr msg) (BZ))))
          (let (many n) (count-bins (predates _) seen c))
          (match many (nat-eq (predates _) n 1) _
            ((BTrue) (check-coverage (subterm _) rest env seen))
            ((BFalse) (check-coverage (subterm _) rest (env-error (predates _) env (str-cat3 (predates _) "constructor " (name-of (predates _) env c) (str-cat3 (predates _) " has " (nat-str (predates _) n) " branches"))) seen))))))))


; ---- The elaborator proper: one block recursing on the raws it elaborates (self/README.md)

; What the statements read from their raws, holding the parts they elaborate later inside those raws.
(def-adts
  (Header : ((Raw) f) -> Type
    enum
    (many MkHeader : (erased (Raw) f) (many (String) name) (many (Mult) mult) (many (Bool) absurd) (many (Maybe (String)) impl) (many (List (Entry)) params) (many (List (Entry)) rets) (many (List (Raw)) body) (erased (Subterm (List (Raw)) body (Raw) f) p) -> (Header f)))
  (Headers : ((List (Raw)) fns) -> Type
    enum
    (many HStop : (erased (List (Raw)) fns) -> (Headers fns))
    (many HCons : (erased (Raw) f) (erased (List (Raw)) rest) (many (Header f) h) (many (Headers rest) hs) -> (Headers (Cons (Raw) f rest))))
  (Bound : ((List (Raw)) fns) ((Headers fns) hs) -> Type
    enum
    (many BStop : (erased (List (Raw)) fns) -> (Bound fns (HStop fns)))
    (many BCons : (erased (Raw) f) (erased (List (Raw)) rest) (erased (Header f) h) (erased (Headers rest) hs) (many (Bin) x) (many (Bound rest hs) more) -> (Bound (Cons (Raw) f rest) (HCons f rest h hs))))
  (AdtHeader : ((Raw) f) -> Type
    enum
    (many MkAdtHeader : (erased (Raw) f) (many (String) name) (many (Disc) disc) (many (Bool) newtype) (many (Bool) extern) (many (List (Raw)) ctors) (erased (Subterm (List (Raw)) ctors (Raw) f) p) -> (AdtHeader f)))
  (AdtHeaders : ((List (Raw)) adts) -> Type
    enum
    (many AStop : (erased (List (Raw)) adts) -> (AdtHeaders adts))
    (many ACons : (erased (Raw) f) (erased (List (Raw)) rest) (many (AdtHeader f) h) (many (AdtHeaders rest) hs) -> (AdtHeaders (Cons (Raw) f rest))))
  (Tids : ((List (Raw)) adts) ((AdtHeaders adts) hs) -> Type
    enum
    (many TStop : (erased (List (Raw)) adts) -> (Tids adts (AStop adts)))
    (many TCons : (erased (Raw) f) (erased (List (Raw)) rest) (erased (AdtHeader f) h) (erased (AdtHeaders rest) hs) (many (Bin) x) (many (Tids rest hs) more) -> (Tids (Cons (Raw) f rest) (ACons f rest h hs))))
  (LetParts : ((List (Raw)) args) -> Type
    enum
    (many MkLetParts : (erased (List (Raw)) args) (many (List (SrcEntry args)) binders) (many (List (Raw)) rhs) (erased (Within rhs args) wr) -> (LetParts args)))
  (CtorParts : ((Raw) c) -> Type
    enum
    (many MkCtorParts : (erased (Raw) c) (many (Mult) mult) (many (String) name) (many (List (Raw)) sg) (erased (Subterm (List (Raw)) sg (Raw) c) p) -> (CtorParts c))))

(def-adts $ RealBranch : -> Type
  enum
  (many MkRealBranch : (many (Bin) c) (many (List (Bin)) fids) (many (Code) code) -> (RealBranch)))

(def-fns _ $ many real-branches-code : (subterm many (List (RealBranch)) bs) (many (List (CShape)) ss) -> (many (List (Branch)) r)
  (match many bs _
    ((Nil a) (Nil (Branch)))
    ((Cons a b rest)
      (match many b _
        ((MkRealBranch c fids code) (Cons (Branch) (MkBranch (discriminant (predates _) ss c) fids code) (real-branches-code (subterm _) rest ss)))))))

(def-fns _ $ many bind-headers : (erased (List (Raw)) fns) (subterm many (Headers fns) hs) (many (Env) env) (many (Bin) lvl) -> (many (Env) r) (many (Bound fns hs) ids)
  (match many hs _
    ((HStop z) (values env (BStop fns)))
    ((HCons f rest h more)
      (match many h _
        ((MkHeader g name mult isabs impl params rets body p)
          (let (many env2) (many x) (bind (predates _) env (Some (String) name) mult (SDyn) (TFn (TVar lvl) params rets) (None (Term)) coercible-id))
          (let (many env3) (many ids) (bind-headers rest (subterm _) more env2 lvl))
          (values env3 (BCons f rest h more x ids)))))))

(def-fns _ $ many many-fns : (subterm many (List (Pair (Bin) (Func))) fns) (many (Env) env) -> (many (List (Pair (Bin) (Func))) r)
  (match many fns _
    ((Nil a) (Nil (Pair (Bin) (Func))))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (match many (entry-mult-of (predates _) env id) _
            ((Many) (Cons (Pair (Bin) (Func)) p (many-fns (subterm _) rest env)))
            ((Erased) (many-fns (subterm _) rest env))))))))

(def-fns _ $ many set-fn-states : (subterm many (List (Pair (Bin) (Value))) closed) (many (Env) env) -> (many (Env) r)
  (match many closed _
    ((Nil a) env)
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id v) (set-fn-states (subterm _) rest (set-state (predates _) env id (SConst v))))))))

(def-fns _ $ many set-const-states : (subterm many (List (Pair (Bin) (Value))) cs) (many (Env) env) -> (many (Env) r)
  (match many cs _
    ((Nil a) env)
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id v) (set-const-states (subterm _) rest (env-push-trace (predates _) (set-state (predates _) env id (SConst v)) (TrConst id v))))))))

(def-fns _ $ many ctor-values : (subterm many (List (Ctor)) cs) -> (many (List (Pair (Bin) (Value))) r)
  (match many cs _
    ((Nil a) (Nil (Pair (Bin) (Value))))
    ((Cons a c rest) (Cons (Pair (Bin) (Value)) (MkPair (Bin) (Value) (ctor-id (predates _) c) (VCtorFn c)) (ctor-values (subterm _) rest)))))

(def-fns _ $ many mctors-of : (subterm many (List (Pair (Mult) (Bin))) cs) -> (many (List (MCtor)) r)
  (match many cs _
    ((Nil a) (Nil (MCtor)))
    ((Cons a p rest) (match many p _ ((MkPair x y m c) (Cons (MCtor) (MkMCtor m (TVar c)) (mctors-of (subterm _) rest)))))))

(def-fns _ $ many code-of-values : (subterm many (List (Code)) codes) (many (Mult) pos) -> (many (Code) r)
  (match many pos _ ((Erased) (CErased)) ((Many) (CValues codes))))

(def-fns _ $ many tail-cc : (many (Sp) sp) -> (many (CC) cc)
  (match many (sp-eq (predates _) sp (SpExpr (ExMatch))) _ ((BTrue) (CCPlain)) ((BFalse) (CCPlain))))

(def-fns _ $ many strip-quote : (many (String) s) -> (many (String) r)
  (match many s _ ((SNil) (SNil)) ((SCons c rest) rest)))


(def-fns _ $ many bin-ids-of : (subterm many (List (Term)) ts) -> (many (List (Bin)) r)
  (match many ts _
    ((Nil a) (Nil (Bin)))
    ((Cons a t rest)
      (match many t _
        ((TVar x) (Cons (Bin) x (bin-ids-of (subterm _) rest)))
        ((TBound k) (bin-ids-of (subterm _) rest)) ((TApp h as) (bin-ids-of (subterm _) rest)) ((TFn l p r) (bin-ids-of (subterm _) rest))
        ((TTyCtor p) (bin-ids-of (subterm _) rest)) ((TValCtor p r) (bin-ids-of (subterm _) rest)) ((TMatchable d ty c) (bin-ids-of (subterm _) rest))
        ((TNewtype c) (bin-ids-of (subterm _) rest)) ((TErr m) (bin-ids-of (subterm _) rest))))))

; Post-erasure normalization (ASSUMPTIONS 72, 74, 88; lib/elab.ml's check_marks): a let that only renames is
; resolved away, one whose body returns exactly what it binds is replaced by its right-hand side, and one
; binding constants nothing mentions is dropped, so a marked call stands in tail position in the code that runs.

; A renaming maps to an already normalized variable, so one lookup resolves it.
(def-fns _ $ many resolve-sub : (many (IdMap (Bin)) sub) (many (Bin) x) -> (many (Bin) r)
  (match many (idmap-get (predates _) (Bin) x sub) _
    ((None a) x)
    ((Some a y) y)))

(def-fns _ $ many vars-of : (subterm many (List (Code)) cs) -> (many (Maybe (List (Bin))) r)
  (match many cs _
    ((Nil a) (Some (List (Bin)) (Nil (Bin))))
    ((Cons a c rest)
      (match many c _
        ((CVar x)
          (match many (vars-of (subterm _) rest) _
            ((None b) (None (List (Bin))))
            ((Some b xs) (Some (List (Bin)) (Cons (Bin) x xs)))))
        ((CConst v) (None (List (Bin)))) ((CErased) (None (List (Bin)))) ((CValues cs2) (None (List (Bin)))) ((CApp f as cc) (None (List (Bin))))
        ((CLet i r b) (None (List (Bin)))) ((CLetRec fs b) (None (List (Bin)))) ((CMatch sc sh bs) (None (List (Bin)))) ((CAbsurd) (None (List (Bin)))) ((CError m) (None (List (Bin))))))))

(def-fns _ $ many bins-eq : (subterm many (List (Bin)) as) (many (List (Bin)) bs) -> (many (Bool) r)
  (match many as _
    ((Nil a) (list-is-empty (predates _) (Bin) bs))
    ((Cons a x rest) (match many bs _ ((Nil b) (BFalse)) ((Cons b y brest) (and (predates _) (bin-eq (predates _) x y) (bins-eq (subterm _) rest brest)))))))

; Whether a body returns exactly the ids, in order.
(def-fns _ $ many returns-ids : (many (List (Bin)) ids) (many (Code) c) -> (many (Bool) r)
  (match many c _
    ((CValues cs) (match many (vars-of (predates _) cs) _ ((None a) (BFalse)) ((Some a xs) (bins-eq (predates _) xs ids))))
    ((CVar x) (bins-eq (predates _) ids (Cons (Bin) x (Nil (Bin)))))
    ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CApp f as cc) (BFalse)) ((CLet i r b) (BFalse)) ((CLetRec fs b) (BFalse))
    ((CMatch sc sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))

(def-fns _ $ many all-consts : (subterm many (List (Code)) cs) -> (many (Bool) r)
  (match many cs _
    ((Nil a) (BTrue))
    ((Cons a c rest)
      (match many c _
        ((CConst v) (all-consts (subterm _) rest))
        ((CVar x) (BFalse)) ((CErased) (BFalse)) ((CValues cs2) (BFalse)) ((CApp f as cc) (BFalse)) ((CLet i r b) (BFalse))
        ((CLetRec fs b) (BFalse)) ((CMatch sc sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))))

(def-fns _ $ many constant-code : (many (Code) c) -> (many (Bool) r)
  (match many c _
    ((CValues cs) (all-consts (predates _) cs))
    ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CApp f as cc) (BFalse)) ((CLet i r b) (BFalse))
    ((CLetRec fs b) (BFalse)) ((CMatch sc sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))

(def-fns _
  (many mentions : (subterm many (Code) c) (many (Bin) x) -> (many (Bool) r)
    (match many c _
      ((CVar y) (bin-eq (predates _) x y))
      ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))
      ((CValues cs) (mentions-list (subterm _) cs x))
      ((CApp f as cc) (or (predates _) (mentions (subterm _) f x) (mentions-list (subterm _) as x)))
      ((CLet ids rhs rest) (or (predates _) (mentions (subterm _) rhs x) (mentions (subterm _) rest x)))
      ((CLetRec fns rest) (or (predates _) (mentions-fns (subterm _) fns x) (mentions (subterm _) rest x)))
      ((CMatch scrut shape bs)
        (or (predates _) (mentions (subterm _) scrut x)
          (or (predates _) (match many shape (((Bool) b)) ((ShKnown adt) (BFalse)) ((ShHeld mc tags) (mentions (subterm _) mc x)))
            (mentions-branches (subterm _) bs x))))))
  (many mentions-list : (subterm many (List (Code)) cs) (many (Bin) x) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (or (predates _) (mentions (subterm _) c x) (mentions-list (subterm _) rest x)))))
  (many mentions-fns : (subterm many (List (Pair (Bin) (Func))) fns) (many (Bin) x) -> (many (Bool) r)
    (match many fns _
      ((Nil a) (BFalse))
      ((Cons a p rest)
        (match many p _
          ((MkPair s t id fn) (match many fn _ ((MkFunc n i ps body impl top) (or (predates _) (mentions (subterm _) body x) (mentions-fns (subterm _) rest x)))))))))
  (many mentions-branches : (subterm many (List (Branch)) bs) (many (Bin) x) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BFalse))
      ((Cons a b rest) (match many b _ ((MkBranch d ids body) (or (predates _) (mentions (subterm _) body x) (mentions-branches (subterm _) rest x))))))))

(def-fns _ $ many mentions-any : (subterm many (List (Bin)) ids) (many (Code) c) -> (many (Bool) r)
  (match many ids _
    ((Nil a) (BFalse))
    ((Cons a x rest) (or (predates _) (mentions (predates _) c x) (mentions-any (subterm _) rest c)))))

(def-fns _ $ many sub-all : (subterm many (List (Bin)) ids) (many (List (Bin)) ys) (many (IdMap (Bin)) sub) -> (many (IdMap (Bin)) r)
  (match many ids _
    ((Nil a) sub)
    ((Cons a x rest) (match many ys _ ((Nil b) sub) ((Cons b y yrest) (sub-all (subterm _) rest yrest (idmap-set (predates _) (Bin) x y sub)))))))

(def-fns _
  (many norm : (subterm many (Code) c) (many (IdMap (Bin)) sub) -> (many (Code) r)
    (match many c _
      ((CVar x) (CVar (resolve-sub (predates _) sub x)))
      ((CConst v) c) ((CErased) c) ((CAbsurd) c) ((CError m) c)
      ((CValues cs) (CValues (norm-list (subterm _) cs sub)))
      ((CApp f as cc) (CApp (norm (subterm _) f sub) (norm-list (subterm _) as sub) cc))
      ((CLet ids rhs rest)
        (let (many rhs2) (norm (subterm _) rhs sub))
        (let (many renaming)
          (match many rhs2 (((Maybe (List (Bin))) r))
            ((CVar y) (match many ids (((Maybe (List (Bin))) r)) ((Nil a) (None (List (Bin)))) ((Cons a x more) (match many more (((Maybe (List (Bin))) r)) ((Nil b) (Some (List (Bin)) (Cons (Bin) y (Nil (Bin))))) ((Cons b x2 more2) (None (List (Bin))))))))
            ((CValues cs) (match many (vars-of (predates _) cs) (((Maybe (List (Bin))) r)) ((None a) (None (List (Bin)))) ((Some a ys) (match many (nat-eq (predates _) (list-length (predates _) (Bin) ys) (list-length (predates _) (Bin) ids)) (((Maybe (List (Bin))) r)) ((BTrue) (Some (List (Bin)) ys)) ((BFalse) (None (List (Bin))))))))
            ((CConst v) (None (List (Bin)))) ((CErased) (None (List (Bin)))) ((CApp f as cc) (None (List (Bin)))) ((CLet i r b) (None (List (Bin))))
            ((CLetRec fs b) (None (List (Bin)))) ((CMatch sc sh bs) (None (List (Bin)))) ((CAbsurd) (None (List (Bin)))) ((CError m) (None (List (Bin))))))
        (match many renaming _
          ((Some a ys) (norm (subterm _) rest (sub-all (predates _) ids ys sub)))
          ((None a)
            (let (many rest2) (norm (subterm _) rest sub))
            (match many (returns-ids (predates _) ids rest2) _
              ((BTrue) rhs2)
              ((BFalse)
                (match many (and (predates _) (constant-code (predates _) rhs2) (not (predates _) (mentions-any (predates _) ids rest2))) _
                  ((BTrue) rest2)
                  ((BFalse) (CLet ids rhs2 rest2))))))))
      ((CLetRec fns rest) (CLetRec (norm-fns (subterm _) fns sub) (norm (subterm _) rest sub)))
      ((CMatch scrut shape bs)
        (CMatch (norm (subterm _) scrut sub)
                (match many shape (((Shape) s)) ((ShKnown adt) shape) ((ShHeld mc tags) (ShHeld (norm (subterm _) mc sub) tags)))
                (norm-branches (subterm _) bs sub)))))
  (many norm-list : (subterm many (List (Code)) cs) (many (IdMap (Bin)) sub) -> (many (List (Code)) r)
    (match many cs _
      ((Nil a) (Nil (Code)))
      ((Cons a c rest) (Cons (Code) (norm (subterm _) c sub) (norm-list (subterm _) rest sub)))))
  (many norm-fns : (subterm many (List (Pair (Bin) (Func))) fns) (many (IdMap (Bin)) sub) -> (many (List (Pair (Bin) (Func))) r)
    (match many fns _
      ((Nil a) (Nil (Pair (Bin) (Func))))
      ((Cons a p rest)
        (match many p _
          ((MkPair s t id fn)
            (match many fn _
              ((MkFunc n i ps body impl top)
                (Cons (Pair (Bin) (Func)) (MkPair (Bin) (Func) id (MkFunc n i ps (norm (subterm _) body sub) impl top)) (norm-fns (subterm _) rest sub)))))))))
  (many norm-branches : (subterm many (List (Branch)) bs) (many (IdMap (Bin)) sub) -> (many (List (Branch)) r)
    (match many bs _
      ((Nil a) (Nil (Branch)))
      ((Cons a b rest) (match many b _ ((MkBranch d ids body) (Cons (Branch) (MkBranch d ids (norm (subterm _) body sub)) (norm-branches (subterm _) rest sub))))))))

(def-fns _ $ many normalize : (many (Code) code) -> (many (Code) r)
  (norm (predates _) code (MEmpty (Bin))))


; ---- tail and delegate (section 9, ASSUMPTIONS 17): judged on the normalized post-erasure code, per
; function, so a nested def-fns's marks are its own.

(def-fns _ $ many cc-marked : (many (CC) cc) -> (many (Bool) r)
  (match many cc _ ((CCPlain) (BFalse)) ((CCTail) (BTrue)) ((CCDelegate) (BTrue)) ((CCCtor) (BFalse))))

(def-fns _
  (many has-marked : (subterm many (Code) c) -> (many (Bool) r)
    (match many c _
      ((CApp f args cc) (or (predates _) (cc-marked (predates _) cc) (or (predates _) (has-marked (subterm _) f) (has-marked-list (subterm _) args))))
      ((CValues cs) (has-marked-list (subterm _) cs))
      ((CLet ids rhs rest) (or (predates _) (has-marked (subterm _) rhs) (has-marked (subterm _) rest)))
      ((CLetRec fns rest) (has-marked (subterm _) rest))
      ((CMatch scrut shape bs) (or (predates _) (has-marked (subterm _) scrut) (or (predates _) (match many shape (((Bool) b)) ((ShKnown a) (BFalse)) ((ShHeld mc t) (has-marked (subterm _) mc))) (has-marked-branches (subterm _) bs))))
      ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
  (many has-marked-list : (subterm many (List (Code)) cs) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (or (predates _) (has-marked (subterm _) c) (has-marked-list (subterm _) rest)))))
  (many has-marked-branches : (subterm many (List (Branch)) bs) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BFalse))
      ((Cons a b rest) (match many b _ ((MkBranch d ids body) (or (predates _) (has-marked (subterm _) body) (has-marked-branches (subterm _) rest))))))))

(def-fns _
  (many has-delegate : (subterm many (Code) c) -> (many (Bool) r)
    (match many c _
      ((CApp f args cc) (or (predates _) (match many cc (((Bool) b)) ((CCDelegate) (BTrue)) ((CCPlain) (BFalse)) ((CCTail) (BFalse)) ((CCCtor) (BFalse))) (or (predates _) (has-delegate (subterm _) f) (has-delegate-list (subterm _) args))))
      ((CValues cs) (has-delegate-list (subterm _) cs))
      ((CLet ids rhs rest) (or (predates _) (has-delegate (subterm _) rhs) (has-delegate (subterm _) rest)))
      ((CLetRec fns rest) (has-delegate (subterm _) rest))
      ((CMatch scrut shape bs) (or (predates _) (has-delegate (subterm _) scrut) (or (predates _) (match many shape (((Bool) b)) ((ShKnown a) (BFalse)) ((ShHeld mc t) (has-delegate (subterm _) mc))) (has-delegate-branches (subterm _) bs))))
      ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
  (many has-delegate-list : (subterm many (List (Code)) cs) -> (many (Bool) r)
    (match many cs _
      ((Nil a) (BFalse))
      ((Cons a c rest) (or (predates _) (has-delegate (subterm _) c) (has-delegate-list (subterm _) rest)))))
  (many has-delegate-branches : (subterm many (List (Branch)) bs) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BFalse))
      ((Cons a b rest) (match many b _ ((MkBranch d ids body) (or (predates _) (has-delegate (subterm _) body) (has-delegate-branches (subterm _) rest))))))))

; Every marked call sits in tail position: the body's final call, through lets, let recs and match branches
; for tail, directly for delegate.
(def-fns _
  (many tails-ok : (subterm many (Code) c) (many (Bool) direct) -> (many (Bool) r)
    (match many c _
      ((CApp f args cc) (and (predates _) (not (predates _) (has-marked (predates _) f)) (not (predates _) (has-marked-list (predates _) args))))
      ((CLet ids rhs rest)
        (match many direct _
          ((BTrue) (not (predates _) (has-marked (predates _) c)))
          ((BFalse) (and (predates _) (not (predates _) (has-marked (predates _) rhs)) (tails-ok (subterm _) rest direct)))))
      ((CLetRec fns rest)
        (match many direct _
          ((BTrue) (not (predates _) (has-marked (predates _) rest)))
          ((BFalse) (tails-ok (subterm _) rest direct))))
      ((CMatch scrut shape bs)
        (match many direct _
          ((BTrue) (not (predates _) (has-marked (predates _) c)))
          ((BFalse) (and (predates _) (not (predates _) (has-marked (predates _) scrut))
                      (and (predates _) (match many shape (((Bool) b)) ((ShKnown a) (BTrue)) ((ShHeld mc t) (not (predates _) (has-marked (predates _) mc))))
                        (tails-ok-branches (subterm _) bs direct))))))
      ((CValues cs) (not (predates _) (has-marked-list (predates _) cs)))
      ((CVar x) (BTrue)) ((CConst v) (BTrue)) ((CErased) (BTrue)) ((CAbsurd) (BTrue)) ((CError m) (BTrue))))
  (many tails-ok-branches : (subterm many (List (Branch)) bs) (many (Bool) direct) -> (many (Bool) r)
    (match many bs _
      ((Nil a) (BTrue))
      ((Cons a b rest) (match many b _ ((MkBranch d ids body) (and (predates _) (tails-ok (subterm _) body direct) (tails-ok-branches (subterm _) rest direct))))))))

; Validates the marks in a body and returns the normalized code and, for a delegate, the callee (section 9).
(def-fns _ $ many check-marks : (many (Env) env) (many (List (Bin)) pids) (many (Code) code) -> (many (Env) r) (many (Code) code2) (many (Maybe (Bin)) delegated)
  (let (many code2) (normalize (predates _) code))
  (match many (has-marked (predates _) code2) _
    ((BFalse) (values env code2 (None (Bin))))
    ((BTrue)
      (let (many delegate) (has-delegate (predates _) code2))
      (let (many kind) (match many delegate (((String) s)) ((BTrue) "delegate") ((BFalse) "tail")))
      (let (many env1)
        (match many (tails-ok (predates _) code2 delegate) (((Env) e))
          ((BTrue) env)
          ((BFalse) (env-error (predates _) env (str-cat3 (predates _) "a " kind "-marked call is not in tail position")))))
      (match many delegate _
        ((BFalse) (values env1 code2 (None (Bin))))
        ((BTrue)
          (match many code2 _
            ((CApp f args cc)
              (match many f _
                ((CVar g)
                  (match many (vars-of (predates _) args) _
                    ((None a) (values (env-error (predates _) env1 "a delegate call must pass the function's non-erased parameters straight through") code2 (None (Bin))))
                    ((Some a ids)
                      (match many (bins-eq (predates _) ids pids) _
                        ((BTrue) (values env1 code2 (Some (Bin) g)))
                        ((BFalse) (values (env-error (predates _) env1 "a delegate call must pass the function's non-erased parameters straight through") code2 (None (Bin))))))))
                ((CConst v) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CErased) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CValues cs) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CApp g2 a2 c2) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CLet i r b) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CLetRec fs b) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CMatch s sh bs) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CAbsurd) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
                ((CError m) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))))
            ((CVar x) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CConst v) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CErased) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CValues cs) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CLet i r b) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CLetRec fs b) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CMatch s sh bs) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CAbsurd) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))
            ((CError m) (values (env-error (predates _) env1 "delegate needs exactly one call to a named function") code2 (None (Bin))))))))))


; A call's decrease annotation (section 9): (predates p) right after the callee, or (subterm p) right before
; the decreasing argument, whose position it carries; the proof p sits inside the call's arguments root.
(def-adts $ Ann : ((List (Raw)) root) -> Type
  enum
  (many AnnNone : (erased (List (Raw)) root) -> (Ann root))
  (many AnnPredates : (erased (List (Raw)) root) (many (Raw) p) (erased (Subterm (Raw) p (List (Raw)) root) q) -> (Ann root))
  (many AnnSubterm : (erased (List (Raw)) root) (many (Nat) i) (many (Raw) p) (erased (Subterm (Raw) p (List (Raw)) root) q) -> (Ann root)))

(def-fns _ $ many ann-of : (many (Env) env) (many (Raw) arg) (many (Nat) i) (erased (List (Raw)) root) (erased (Subterm (Raw) arg (List (Raw)) root) pa) -> (many (Ann root) r)
  (match many arg _
    ((RAtom lq s) (AnnNone root))
    ((RString lq s) (AnnNone root))
    ((RList lq items)
      (match many items _
        ((Nil b) (AnnNone root))
        ((Cons b k krest)
          (match many krest _
            ((Nil c) (AnnNone root))
            ((Cons c p prest)
              (match many prest _
                ((Cons d q qrest) (AnnNone root))
                ((Nil d)
                  (let (erased pp) (subterm-trans (prove-subterm p arg) pa))
                  (match many (and (predates _) (is-mark (predates _) env k (MkPredates)) (nat-is-zero (predates _) i)) _
                    ((BTrue) (AnnPredates root p pp))
                    ((BFalse) (match many (is-mark (predates _) env k (MkSubterm)) _ ((BTrue) (AnnSubterm root i p pp)) ((BFalse) (AnnNone root))))))))))))))

; The first annotation and the arguments without it; a second annotation stays an argument, as in lib/elab.ml.
(def-fns _ $ many split-annotation : (subterm many (List (Raw)) args) (erased (List (Raw)) root) (erased (Within args root) w) (many (Env) env) (many (Nat) i) -> (many (Ann root) ann) (many (List (Sub root)) rest)
  (match many args _
    ((Nil a) (values (AnnNone root) (Nil (Sub root))))
    ((Cons a arg more)
      (let (erased pa) (in-within (predates _) (Raw) arg args root (prove-subterm arg args) w))
      (let (erased wm) (within-step (predates _) more args root (prove-subterm more args) w))
      (match many (ann-of (predates _) env arg i root pa) _
        ((AnnNone z)
          (let (many ann) (many rest) (split-annotation (subterm _) more root wm env (Succ i)))
          (values ann (Cons (Sub root) (MkSub root arg pa) rest)))
        ((AnnPredates z p q) (values (AnnPredates root p q) (subs-of (predates _) more root wm)))
        ((AnnSubterm z j p q) (values (AnnSubterm root j p q) (subs-of (predates _) more root wm)))))))

(def-fns _ $ many subterm-indices : (subterm many (List (Entry)) tele) (many (Nat) i) -> (many (List (Nat)) r)
  (match many tele _
    ((Nil a) (Nil (Nat)))
    ((Cons a e rest)
      (match many (entry-sub (predates _) e) _
        ((BTrue) (Cons (Nat) i (subterm-indices (subterm _) rest (Succ i))))
        ((BFalse) (subterm-indices (subterm _) rest (Succ i)))))))

(def-fns _ $ many index-of-nat : (subterm many (List (Nat)) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe (Nat)) r)
  (match many xs _
    ((Nil a) (None (Nat)))
    ((Cons a y rest) (match many (nat-eq (predates _) x y) _ ((BTrue) (Some (Nat) i)) ((BFalse) (index-of-nat (subterm _) rest x (Succ i)))))))

; Earlier subterm arguments must equal their counterparts (section 9's lexicographic discipline).
(def-fns _ $ many check-earlier : (subterm many (List (Nat)) positions) (many (Env) env) (many (List (Term)) args) (many (Nat) j) (many (Nat) k) -> (many (Env) r)
  (match many positions _
    ((Nil a) env)
    ((Cons a pi rest)
      (match many (nat-lt (predates _) j k) _
        ((BFalse) env)
        ((BTrue)
          (let (many env2)
            (match many (list-nth (predates _) (Bin) (env-subterms (predates _) env) j) (((Env) e))
              ((None b) (env-error (predates _) env (str-cat3 (predates _) "the enclosing function has no subterm parameter at position " (nat-str (predates _) j) "")))
              ((Some b counterpart) (check (predates _) env "value" (nth-term (predates _) args pi) (TVar counterpart)))))
          (check-earlier (subterm _) rest env2 args (Succ j) k))))))

(def-fns _ $ many erased-in-many : (subterm many (List (Mult)) expect) (many (List (Res)) ress) (many (Env) env) -> (many (Env) r)
  (match many expect _
    ((Nil a) env)
    ((Cons a m rest)
      (match many ress _
        ((Nil b) env)
        ((Cons b r rrest)
          (let (many env2)
            (match many (and (predates _) (mult-is-many (predates _) m) (not (predates _) (mult-is-many (predates _) (res-erasure (predates _) r)))) (((Env) e))
              ((BTrue) (env-error (predates _) env (str-cat3 (predates _) "erased value " (show-t (predates _) env (res-term (predates _) r)) (str-cat3 (predates _) " : " (show-t (predates _) env (res-ty (predates _) r)) " used in a non-erased position"))))
              ((BFalse) env)))
          (erased-in-many (subterm _) rest rrest env2))))))

; A call's or application's argument count against its telescope (lib/elab.ml's check_args).
(def-fns _ $ many check-arity : (many (Env) env) (many (List (Entry)) tele) (many (Nat) m) -> (many (Env) r)
  (let (many n) (list-length (predates _) (Entry) tele))
  (match many (nat-eq (predates _) n m) _
    ((BTrue) env)
    ((BFalse) (count-error (predates _) env " arguments" n m))))

(def-fns _ $ many malformed : (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
  (values (env-error (predates _) env (str-cat3 (predates _) "malformed " (sp-name (predates _) sp) " form")) (Nil (Res)) (CError "malformed")))

; The field at a wrapping constructor's one many position, given the arguments in order.
(def-fns _ $ many wrap-field : (subterm many (List (Entry)) tele) (many (List (Term)) args) -> (many (Maybe (Term)) t)
  (match many tele _
    ((Nil a) (None (Term)))
    ((Cons a e rest)
      (match many args _
        ((Nil b) (None (Term)))
        ((Cons b t trest)
          (match many (entry-mult (predates _) e) _
            ((Many) (match many (many-count (predates _) rest) _ ((Zero) (Some (Term) t)) ((Succ k) (None (Term)))))
            ((Erased) (wrap-field (subterm _) rest trest))))))))

(def-fns _ $ many trace-many-fields : (subterm many (List (Bin)) ids) (many (Env) env) -> (many (Env) r)
  (match many ids _
    ((Nil a) env)
    ((Cons a x rest)
      (match many (entry-mult-of (predates _) env x) _
        ((Erased) (trace-many-fields (subterm _) rest env))
        ((Many)
          (match many (entry-state (predates _) env x) _
            ((SDyn) (trace-many-fields (subterm _) rest env))
            ((SConst v) (trace-many-fields (subterm _) rest (env-push-trace (predates _) env (TrConst x v))))))))))

(def-fns _ $ many missing-arg : (many (Env) env) -> (many (Env) r) (many (Term) t)
  (let (many env2) (many x) (var (predates _) (env-at (predates _) env 0) "_"))
  (values (env-back (predates _) env env2) (TVar x)))

(def-fns _ $ many erased-term : (many (List (Res)) ress) -> (many (Term) t)
  (res-term (predates _) (first-res (predates _) ress)))

(let (many erased-one) (Cons (Mult) (Erased) (Nil (Mult))))
(let (many many-one) (Cons (Mult) (Many) (Nil (Mult))))
(let (many no-tele) (None (List (Entry))))

; comptime-match (section 15): a Const, non-erased scrutinee with a non-erased discriminant, verified
; against the named constructor; the fields are bound Const and the facts refined as a branch would.
(def-fns _ $ many elab-comptime-match : (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (let (many shape) (comptime-shape (predates _) args))
    (match many shape _
      ((None a) (values (env-error (predates _) env "malformed comptime-match: expected (comptime-match x (C field ...))") (SNone)))
      ((Some a triple)
        (match many triple _
          ((MkPair s t xraw cpat)
            (match many cpat _
              ((MkPair s2 t2 craw fields)
                (let (many env1) (match many (env-run-pos (predates _) env) (((Env) e)) ((BTrue) env) ((BFalse) (env-error (predates _) env "comptime-match is a run-position statement (section 15)"))))
                (let (many env2) (many x) (var-of-raw (predates _) env1 xraw "a variable"))
                (let (many env3) (many value)
                  (match many (entry (predates _) env2 x) (((Env) e) ((Value) v))
                    ((MkEInfo nm mult st mi)
                      (match many st (((Env) e) ((Value) v))
                        ((SConst v) (match many mult (((Env) e) ((Value) v)) ((Many) (values env2 v)) ((Erased) (values (env-error (predates _) env2 "comptime-match needs a Const, non-erased scrutinee") v))))
                        ((SDyn) (values (env-error (predates _) env2 "comptime-match needs a Const, non-erased scrutinee") (VError "Dyn")))))))
                (let (many env4) (many c) (ctor-var (predates _) env3 craw))
                (let (many tele) (many ret) (ctor-type (predates _) env4 c))
                (let (many head) (type-head (predates _) env4 (type-of (predates _) env4 x)))
                (let (many tid) (match many head (((Bin) t)) ((None b) (BZ)) ((Some b t) t)))
                (let (many env5) (many found)
                  (match many head (((Env) e) ((Maybe (MatchInfo)) m))
                    ((None b) (values (env-error (predates _) env4 "scrutinee is not a datatype value") (None (MatchInfo))))
                    ((Some b t) (find-matchable (predates _) env4 t))))
                (let (many env6)
                  (match many found (((Env) e))
                    ((None b) env5)
                    ((Some b info)
                      (match many info (((Env) e))
                        ((MkMatchInfo mid disc mctors rank)
                          (let (many env6a) (match many disc (((Env) e)) ((DUnion) (env-error (predates _) env5 "comptime-match needs a non-erased discriminant")) ((DEnum) env5)))
                          (let (many env6b) (many mk) (marker-checked (predates _) env6a tid mctors c))
                          (match many mk (((Env) e))
                            ((Erased) (env-error (predates _) env6b (str-cat3 (predates _) "comptime-match: " (name-of (predates _) env6b c) " is phantom, so no non-erased value is headed by it")))
                            ((Many) env6b)))))))
                (let (many env7) (many vs)
                  (match many (ctor-of (predates _) env6 c) (((Env) e) ((List (Value)) vs))
                    ((None d) (values (env-error (predates _) env6 (str-cat (predates _) (name-of (predates _) env6 c) " is not a run-position constructor")) (Nil (Value))))
                    ((Some d ct)
                      (let (many i) (many vs) (destruct (predates _) ct value))
                      (match many (nat-eq (predates _) i (ctor-index (predates _) ct)) (((Env) e) ((List (Value)) vs))
                        ((BTrue) (values env6 vs))
                        ((BFalse) (values (env-error (predates _) env6 (str-cat3 (predates _) "comptime-match: expected " (name-of (predates _) env6 c) (str-cat (predates _) ", got " (rope-str (predates _) (show-value (predates _) value))))) vs))))))
                (let (many env8)
                  (match many (nat-eq (predates _) (list-length (predates _) (Raw) fields) (list-length (predates _) (Entry) tele)) (((Env) e))
                    ((BTrue) env7)
                    ((BFalse) (env-error (predates _) env7 (str-cat3 (predates _) (name-of (predates _) env7 c) " has " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) tele)) " fields"))))))
                (let (many states) (states-of (predates _) (spread (predates _) (tele-mults (predates _) tele) vs)))
                (let (many env9) (many fids) (open-tele (predates _) tele env8 (Some (List (Maybe (String))) (raw-names (predates _) fields)) (None (List (Mult))) (Some (List (State)) states) (Nil (Term))))
                (let (many env10) (trace-many-fields (predates _) fids env9))
                (match many (refine (predates _) env10 (res-of (predates _) env10 x) c fids ret) _
                  ((UOk env11) (values env11 (SNone)))
                  ((UContra msg) (values (env-error (predates _) env10 (str-cat3 (predates _) "internal: the verified value contradicts the facts in force (" msg ")")) (SNone)))))))))))

; Every function recurses on a raw it elaborates: the first subterm parameter is that raw or list, a later
; one a structure parsed from it (its entries prove they sit inside it) or a Steps budget spent when a
; function hands its whole raw to another.
; ---- Sugar (SUGAR.md 5): unary and distinct stand for calls on the prelude's Numeral lemmas, written
; down as the reference writes them and elaborated where the form is met. The elaborator's group takes a
; budget of such expansions as its first subterm parameter, spent when a generated form is elaborated,
; which is what lets that raw be of the elaborator's own making (ASSUMPTIONS 111).

(let (many sugar-budget) 1)

(def-fns _ $ many prelude-call : (many (Env) env) -> (many (String) p)
  (match many (env-level (predates _) env) _ ((None a) "") ((Some a l) "(predates _) ")))

(def-fns _ $ many bin-text : (many (Nat) n) -> (many (String) s)
  (rope-str (predates _) (show-bin (predates _) (bin-of-nat (predates _) n (BZ)))))

; The witness that n's spelling steps to (n+1)'s: (B1 x) steps to (B2 x), and (B2 x) to (B1 (succ x)).
(def-fns _ $ many bin-succ-witness : (subterm many (Bin) b) -> (many (String) s)
  (match many b _
    ((BZ) "(BSZ)")
    ((B1 x) (str-cat3 (predates _) "(BS1 " (rope-str (predates _) (show-bin (predates _) x)) ")"))
    ((B2 x) (str-cat3 (predates _) "(BS2 " (rope-str (predates _) (show-bin (predates _) x))
              (str-cat3 (predates _) " " (rope-str (predates _) (show-bin (predates _) (bin-succ (predates _) x)))
                (str-cat3 (predates _) " " (bin-succ-witness (subterm _) x) ")"))))))

(def-fns _ $ many succs : (subterm many (Nat) k) (many (String) base) -> (many (String) s)
  (match many k _
    ((Zero) base)
    ((Succ j) (succs (subterm _) j (str-cat3 (predates _) "(Succ " base ")")))))

; Folds the one-step proofs from z up to z+k into one Eq relating the top literal to [floor] under k
; successors: numeral-succ's step, eq-cong-succ under the successors so far, eq-trans joining them.
(def-fns _ $ many unary-fold : (subterm many (Nat) k) (many (Nat) z) (many (Nat) lo) (many (String) floor) (many (String) acc) (many (String) p) -> (many (String) s)
  (match many k _
    ((Zero) acc)
    ((Succ j)
      (let (many n) (Succ z))
      (let (many zs) (nat-str (predates _) z))
      (let (many ns) (nat-str (predates _) n))
      (let (many below) (succs (predates _) (nat-sub (predates _) z lo) floor))
      (let (many stp) (str-cat3 (predates _) "(numeral-succ " p
                        (str-cat3 (predates _) (bin-text (predates _) z) " " (str-cat3 (predates _) (bin-text (predates _) n) " "
                          (str-cat3 (predates _) zs " " (str-cat3 (predates _) ns " " (str-cat3 (predates _) (bin-succ-witness (predates _) (bin-of-nat (predates _) z (BZ)))
                            " (numeral-of " (str-cat3 (predates _) zs ") (numeral-of " (str-cat (predates _) ns "))")))))))))
      (let (many congd) (str-cat3 (predates _) "(eq-cong-succ " p (str-cat3 (predates _) zs " " (str-cat3 (predates _) below " " (str-cat (predates _) acc ")")))))
      (let (many acc2) (str-cat3 (predates _) "(eq-trans " p (str-cat3 (predates _) "(Nat) " ns
                         (str-cat3 (predates _) " (Succ " zs (str-cat3 (predates _) ") (Succ " below (str-cat3 (predates _) ") " stp (str-cat3 (predates _) " " congd ")")))))))
      (unary-fold (subterm _) j n lo floor acc2 p))))

(def-fns _ $ many unary-source : (many (Nat) za) (many (Nat) lo) (many (Bool) floored) (many (String) p) -> (many (String) s)
  (let (many floor) (many acc)
    (match many floored (((String) f) ((String) a))
      ((BFalse) (values "(Zero)" (str-cat3 (predates _) "(numeral-zero " p "0 (numeral-of 0))")))
      ((BTrue) (values (nat-str (predates _) lo) (str-cat3 (predates _) "(Refl (Nat) " (nat-str (predates _) lo) ")")))))
  (str-cat3 (predates _) "(let-match erased " (unary-fold (predates _) (nat-sub (predates _) za lo) lo lo floor acc p) " (Refl _ _))"))

(def-fns _ $ many distinct-source : (many (Nat) za) (many (Nat) zb) (many (String) p) -> (many (String) s)
  (str-cat3 (predates _) "(match erased (numeral-inj " p
    (str-cat3 (predates _) (bin-text (predates _) za) " " (str-cat3 (predates _) (bin-text (predates _) zb) " "
      (str-cat3 (predates _) (nat-str (predates _) za) " (numeral-of " (str-cat3 (predates _) (nat-str (predates _) za) ") (numeral-of "
        (str-cat (predates _) (nat-str (predates _) zb) ")) (((False) f)) (absurd Refl))")))))))

(def-fns _
  ; An expression of the given size and erasures (sections 16, 20); [tele] is the telescope a bare _ reuses.
  (many elab-expr : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (List (Mult)) expect) (many (Maybe (List (Entry))) tele) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (let (many envl) (env-at (predates _) env (raw-line (predates _) raw)))
    (let (many pos) (pos-of (predates _) expect))
    (let (many env2) (many ress) (many code)
      (match many raw (((Env) e) ((List (Res)) rs) ((Code) c))
        ((RAtom lq n)
          (let (many env2) (many x) (var (predates _) envl n))
          (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
        ((RString lq s)
          (let (many env2) (many x) (var-of-raw (predates _) envl raw "a name"))
          (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
        ((RList lq items)
          (match many items (((Env) e) ((List (Res)) rs) ((Code) c))
            ((Nil a) (values (env-error (predates _) envl "empty form") (Nil (Res)) (CError "empty form")))
            ((Cons a head args)
              (match many (special-of (predates _) envl head) (((Env) e) ((List (Res)) rs) ((Code) c))
                ((Some b sp)
                  (let (many multi) (or (predates _) (sp-eq (predates _) sp (SpExpr (ExValues))) (or (predates _) (sp-eq (predates _) sp (SpExpr (ExMatch))) (or (predates _) (sp-eq (predates _) sp (SpMark (MkTail))) (sp-eq (predates _) sp (SpMark (MkDelegate)))))))
                  (let (many env0) (many m)
                    (match many multi (((Env) e) ((Mult) m))
                      ((BTrue) (values envl pos))
                      ((BFalse)
                        (match many expect (((Env) e) ((Mult) m))
                          ((Nil c) (values (env-error (predates _) envl (str-cat (predates _) (sp-name (predates _) sp) " produces one value")) (Erased)))
                          ((Cons c m1 rest) (match many rest (((Env) e) ((Mult) m)) ((Nil d) (values envl m1)) ((Cons d m2 rest2) (values (env-error (predates _) envl (str-cat (predates _) (sp-name (predates _) sp) " produces one value")) m1))))))))
                  (match many sp (((Env) e) ((List (Res)) rs) ((Code) c))
                    ((SpFormer fo)
                      (let (many env1) (match many pos (((Env) e)) ((Many) (env-error (predates _) env0 "a type in a non-erased position")) ((Erased) env0)))
                      (let (many env2) (many t) (elab-type-form sugar (subterm _) args two-steps env1 sp))
                      (values env2 (Cons (Res) (term-res (predates _) env2 t) (Nil (Res))) (CErased)))
                    ((SpStmt st) (values (env-error (predates _) env0 (str-cat (predates _) (sp-name (predates _) sp) " is a statement, not an expression")) (Nil (Res)) (CError "statement as expression")))
                    ((SpMark mk)
                      (match many mk (((Env) e) ((List (Res)) rs) ((Code) c))
                        ((MkTail) (elab-marked sugar (subterm _) args env0 expect (CCTail) sp))
                        ((MkDelegate) (elab-marked sugar (subterm _) args env0 expect (CCDelegate) sp))
                        ((MkErased) (malformed (predates _) env0 sp)) ((MkMany) (malformed (predates _) env0 sp)) ((MkColon) (malformed (predates _) env0 sp))
                        ((MkIs) (malformed (predates _) env0 sp)) ((MkArrow) (malformed (predates _) env0 sp)) ((MkSubterm) (malformed (predates _) env0 sp))
                        ((MkEnum) (malformed (predates _) env0 sp)) ((MkUnion) (malformed (predates _) env0 sp)) ((MkPredates) (malformed (predates _) env0 sp))
                        ((MkAbsurd) (malformed (predates _) env0 sp)) ((MkNewtypeMark) (malformed (predates _) env0 sp)) ((MkExtern) (malformed (predates _) env0 sp))))
                    ((SpExpr ex)
                      (match many ex (((Env) e) ((List (Res)) rs) ((Code) c))
                        ((ExValues)
                          (let (many n) (list-length (predates _) (Mult) expect))
                          (let (many na) (list-length (predates _) (Raw) args))
                          (let (many env1) (match many (nat-eq (predates _) n na) (((Env) e)) ((BTrue) env0) ((BFalse) (count-error (predates _) env0 " values" n na))))
                          (let (many env2) (many ress) (many codes) (elab-values sugar (subterm _) args env1 expect))
                          (values env2 ress (code-of-values (predates _) codes pos)))
                        ((ExMatch) (elab-match sugar (subterm _) args env0 expect tele))
                        ((ExMatchableOf)
                          (let (many env2) (many tid) (named (predates _) env0 (one-arg (predates _) args) "a type constructor"))
                          (let (many env3) (many found) (find-matchable (predates _) env2 tid))
                          (match many found (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((None c) (values (env-error (predates _) env3 (str-cat (predates _) (name-of (predates _) env3 tid) " has no Matchable in scope")) (Nil (Res)) (CError "no Matchable")))
                            ((Some c info) (match many info (((Env) e) ((List (Res)) rs) ((Code) c)) ((MkMatchInfo mid d cs rank) (values env3 (Cons (Res) (res-of (predates _) env3 mid) (Nil (Res))) (matchable-code (predates _) env3 m mid)))))))
                        ((ExNewtypeOf)
                          (let (many env2) (many c) (ctor-var (predates _) env0 (one-arg (predates _) args)))
                          (match many (find-newtype (predates _) (env-objects (predates _) env2) env2 c) (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((None d) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " has no Newtype in scope")) (Nil (Res)) (CError "no Newtype")))
                            ((Some d x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))
                        ((ExNumeralOf) (numeral-of-lit (predates _) env0 (one-arg (predates _) args)))
                        ((ExDistinct) (elab-distinct sugar (subterm _) args env0))
                        ((ExLevelOf)
                          (let (many env2) (many f) (elab-one-term sugar (subterm _) args env0))
                          (let (many fty) (canon-env (predates _) env2 (infer (predates _) f env2)))
                          (match many fty (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((TFn lv ps rs) (values env2 (Cons (Res) (MkRes lv level-term (Erased)) (Nil (Res))) (CErased)))
                            ((TVar y) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TBound j) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TApp h as) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TTyCtor p) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TValCtor p r) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TMatchable d t c) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TNewtype c) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))
                            ((TErr msg) (values (env-error (predates _) env2 (level-of-error (predates _) env2 f fty)) (Nil (Res)) (CError "level-of")))))
                        ((ExProveSubterm)
                          (let (many env2) (many a) (many b2) (elab-two-terms sugar (subterm _) args env0))
                          (let (many env3) (many r) (mint-subterm (predates _) env2 a b2))
                          (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExProvePredates)
                          (match many args (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((Nil c) (values (env-error (predates _) env0 "malformed prove-predates form") (Nil (Res)) (CError "prove-predates")))
                            ((Cons c xraw rest)
                              (let (many env2) (many x) (var-of-raw (predates _) env0 xraw "a variable"))
                              (let (many env3) (many lt) (elab-one-term sugar (subterm _) rest env2))
                              (let (many env4) (many lvl) (level-var-checked (predates _) env3 lt))
                              (let (many env5) (many r) (mint-predates (predates _) env4 x lvl))
                              (values env5 (Cons (Res) r (Nil (Res))) (CErased)))))
                        ((ExPredatesTrans)
                          (let (many env1) (many p) (many q) (two-proofs sugar (subterm _) args env0))
                          (let (many env2a) (many p0) (many p1) (many p2) (expect-proof3 (predates _) env1 predates-id p))
                          (let (many env2) (many q0) (many q1) (many q2) (expect-proof3 (predates _) env2a predates-id q))
                          (let (many env3) (check (predates _) env2 "value" q1 p2))
                          (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) predates-id (Cons (Term) p0 (Cons (Term) p1 (Cons (Term) q2 (Nil (Term))))))))
                          (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExSubtermTrans)
                          (let (many env1) (many p) (many q) (two-proofs sugar (subterm _) args env0))
                          (let (many env2a) (many p0) (many p1) (many p2) (many p3) (expect-proof4 (predates _) env1 subterm-id p))
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) (expect-proof4 (predates _) env2a subterm-id q))
                          (let (many env3) (check (predates _) env2 "value" q1 p3))
                          (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) subterm-id (Cons (Term) p0 (Cons (Term) p1 (Cons (Term) q2 (Cons (Term) q3 (Nil (Term)))))))))
                          (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExCoercibleTrans)
                          (let (many env1) (many p) (many q) (two-proofs sugar (subterm _) args env0))
                          (let (many env2a) (many p0) (many p1) (many p2) (many p3) (expect-proof4 (predates _) env1 coercible-id p))
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) (expect-proof4 (predates _) env2a coercible-id q))
                          (let (many env3) (check (predates _) env2 "value" q1 p3))
                          (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) p0 (Cons (Term) p1 (Cons (Term) q2 (Cons (Term) q3 (Nil (Term)))))))))
                          (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExPredatesSubterm)
                          (let (many env1) (many p) (many q) (two-proofs sugar (subterm _) args env0))
                          (let (many env2a) (many p0) (many p1) (many p2) (expect-proof3 (predates _) env1 predates-id p))
                          (let (many env2) (many q0) (many q1) (many q2) (many q3) (expect-proof4 (predates _) env2a subterm-id q))
                          (let (many env3) (check (predates _) env2 "value" q3 p1))
                          (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) predates-id (Cons (Term) q0 (Cons (Term) q1 (Cons (Term) p2 (Nil (Term))))))))
                          (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExCoerce)
                          (match many args (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((Nil c) (values (env-error (predates _) env0 "malformed coerce form") (Nil (Res)) (CError "coerce")))
                            ((Cons c araw rest)
                              (let (many env2) (many ars) (many code) (elab-expr sugar (subterm _) araw env0 (Cons (Mult) m (Nil (Mult))) no-tele (CCPlain)))
                              (let (many env3) (many p) (elab-one-erased sugar (subterm _) rest env2))
                              (let (many env4) (many p0) (many p1) (many p2) (many p3) (expect-proof4 (predates _) env3 coercible-id p))
                              (let (many env5) (check (predates _) env4 "value" (res-term (predates _) (first-res (predates _) ars)) p1))
                              (let (many env6) (many x) (bind (predates _) env5 (None (String)) m (SDyn) p2 (Some (Term) p3) coercible-id))
                              (values env6 (Cons (Res) (res-of (predates _) env6 x) (Nil (Res))) code))))
                        ((ExCoercibleRefl)
                          (let (many env2) (many e) (elab-one-term sugar (subterm _) args env0))
                          (let (many ty) (infer (predates _) e env2))
                          (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) e (Cons (Term) ty (Cons (Term) e (Nil (Term)))))))))
                          (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExCoercibleSym)
                          (let (many env2) (many p) (elab-one-erased sugar (subterm _) args env0))
                          (let (many env3) (many p0) (many p1) (many p2) (many p3) (expect-proof4 (predates _) env2 coercible-id p))
                          (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) p2 (Cons (Term) p3 (Cons (Term) p0 (Cons (Term) p1 (Nil (Term)))))))))
                          (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
                        ((ExCoercibleWrap)
                          (match many args (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((Nil c) (values (env-error (predates _) env0 "malformed coercible-wrap form") (Nil (Res)) (CError "coercible-wrap")))
                            ((Cons c craw wargs)
                              (let (many env2) (many cid) (ctor-var (predates _) env0 craw))
                              (let (many ctele) (many ret) (ctor-type (predates _) env2 cid))
                              (let (many env3)
                                (match many (find-newtype (predates _) (env-objects (predates _) env2) env2 cid) (((Env) e))
                                  ((None d) (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 cid) " has no Newtype in scope: only a marked newtype's wrapping constructor has one")))
                                  ((Some d x) env2)))
                              (let (many env4) (many acc) (elab-term-args sugar (subterm _) wargs (subs-all (predates _) wargs) env3 ctele (Nil (Term))))
                              (let (many env5) (many f)
                                (match many (wrap-field (predates _) ctele (list-rev (predates _) (Term) acc)) (((Env) e0) ((Term) t0))
                                  ((Some d g) (values env4 g))
                                  ((None d) (values (env-error (predates _) env4 (str-cat (predates _) (name-of (predates _) env4 cid) " is not the wrapping constructor")) (TErr "not the wrapping constructor")))))
                              (let (many env6) (many r) (mint (predates _) env5 (proof-type (predates _) coercible-id (Cons (Term) (infer (predates _) f env5) (Cons (Term) f (Cons (Term) (instantiate (predates _) acc ret) (Cons (Term) (TApp (TVar cid) (list-rev (predates _) (Term) acc)) (Nil (Term)))))))))
                              (values env6 (Cons (Res) r (Nil (Res))) (CErased)))))
                        ((ExCoercibleCtor)
                          (match many args (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((Nil c) (values (env-error (predates _) env0 "malformed coercible-ctor form") (Nil (Res)) (CError "coercible-ctor")))
                            ((Cons c craw cargs)
                              (let (many env2) (many cid) (ctor-var (predates _) env0 craw))
                              (let (many ctele) (many ret) (ctor-type (predates _) env2 cid))
                              (let (many env3) (match many (phantom (predates _) env2 cid) (((Env) e)) ((BTrue) (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 cid) " is phantom"))) ((BFalse) env2)))
                              (let (many env4) (many src) (many tgt) (coercible-ctor-args sugar (subterm _) cargs env3 ctele (Nil (Term)) (Nil (Term)) cid))
                              (let (many env5) (many r) (mint (predates _) env4 (proof-type (predates _) coercible-id (Cons (Term) (instantiate (predates _) src ret) (Cons (Term) (TApp (TVar cid) (list-rev (predates _) (Term) src)) (Cons (Term) (instantiate (predates _) tgt ret) (Cons (Term) (TApp (TVar cid) (list-rev (predates _) (Term) tgt)) (Nil (Term)))))))))
                              (values env5 (Cons (Res) r (Nil (Res))) (CErased)))))
                        ((ExCoercibleOf)
                          (let (many env2) (many g) (named (predates _) env0 (one-arg (predates _) args) "a function name"))
                          (match many (find-coercible (predates _) (env-objects (predates _) env2) env2 g) (((Env) e) ((List (Res)) rs) ((Code) c))
                            ((None c) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 g) " has no delegate proof in scope")) (Nil (Res)) (CError "no delegate proof")))
                            ((Some c x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))))))
                ((None b)
                  (let (many env2) (many h) (many hcode)
                    (match many head (((Env) e) ((Res) r) ((Code) c))
                      ((RAtom lq2 n) (let (many env2) (many x) (var (predates _) envl n)) (values env2 (res-of (predates _) env2 x) (CVar x)))
                      ((RString lq2 s) (let (many env2) (many x) (var-of-raw (predates _) envl head "a name")) (values env2 (res-of (predates _) env2 x) (CVar x)))
                      ((RList lq2 hitems)
                        (let (many env2) (many rs) (many hcode) (elab-expr sugar (subterm _) head envl (Cons (Mult) pos (Nil (Mult))) no-tele (CCPlain)))
                        (values env2 (first-res (predates _) rs) hcode))))
                  (match many (canon-env (predates _) env2 (res-ty (predates _) h)) (((Env) e) ((List (Res)) rs) ((Code) c))
                    ((TTyCtor ttele)
                      (let (many env3) (match many pos (((Env) e)) ((Many) (env-error (predates _) env2 "type constructor application in a non-erased position")) ((Erased) env2)))
                      (let (many env4) (many acc) (elab-term-args sugar (subterm _) args (subs-all (predates _) args) (check-arity (predates _) env3 ttele (list-length (predates _) (Raw) args)) ttele (Nil (Term))))
                      (values env4 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) type-term (Erased)) (Nil (Res))) (CErased)))
                    ((TValCtor ctele ret)
                      (let (many env3)
                        (match many (and (predates _) (mult-is-many (predates _) pos) (not (predates _) (mult-is-many (predates _) (res-erasure (predates _) h)))) (((Env) e))
                          ((BTrue) (env-error (predates _) env2 (str-cat3 (predates _) "erased constructor " (show-t (predates _) env2 (res-term (predates _) h)) " in a non-erased position")))
                          ((BFalse) env2)))
                      (let (many env4) (many acc) (many codes) (check-args sugar (subterm _) args (subs-all (predates _) args) (check-arity (predates _) env3 ctele (list-length (predates _) (Raw) args)) ctele pos (Nil (Term)) (Nil (Code))))
                      (let (many code) (match many pos (((Code) c)) ((Erased) (CErased)) ((Many) (CApp hcode codes (CCCtor)))))
                      (values env4 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) (instantiate (predates _) acc ret) pos) (Nil (Res))) code))
                    ((TFn lv params rets)
                      (let (many ann) (many args2) (split-annotation (predates _) args args (WHere args) env2 0))
                      (elab-call sugar (subterm _) args (MkPair (List (Sub args)) (Ann args) args2 ann) env2 expect h hcode lv params rets cc))
                    ((TVar x) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                    ((TBound j) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                    ((TApp h2 a2) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                    ((TMatchable d t c) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                    ((TNewtype c) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                    ((TErr m) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError m)))))))))))
    (let (many n) (list-length (predates _) (Mult) expect))
    (let (many m) (list-length (predates _) (Res) ress))
    (match many (nat-eq (predates _) n m) _
      ((BFalse) (values (env-back (predates _) env (count-error (predates _) env2 " values" n m)) ress code))
      ((BTrue) (values (env-back (predates _) env (erased-in-many (predates _) expect ress env2)) ress code))))
  (many elab-one-term : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (Term) t)
    (match many args _
      ((Nil a) (missing-arg (predates _) env))
      ((Cons a araw rest) (elab-term sugar (subterm _) araw env (BFalse)))))

  (many elab-one-erased : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (Term) t)
    (match many args _
      ((Nil a) (missing-arg (predates _) env))
      ((Cons a araw rest)
        (let (many env2) (many ress) (many code) (elab-expr sugar (subterm _) araw env erased-one no-tele (CCPlain)))
        (values env2 (erased-term (predates _) ress)))))

  ; Grammar expressions (section 5): variables, constructor applications and type formers; [as-type] also
  ; checks the result is a type.
  (many elab-term : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) (many (Bool) as-type) -> (many (Env) r) (many (Term) t)
    (let (many envl) (env-at (predates _) env (raw-line (predates _) raw)))
    (let (many env2) (many t)
      (match many raw (((Env) e0) ((Term) t0))
        ((RAtom lq n) (let (many env2) (many x) (var (predates _) envl n)) (values env2 (TVar x)))
        ((RString lq s) (let (many env2) (many x) (var-of-raw (predates _) envl raw "a name")) (values env2 (TVar x)))
        ((RList lq items)
          (match many items (((Env) e0) ((Term) t0))
            ((Nil a) (values (env-error (predates _) envl "empty form") (TErr "empty form")))
            ((Cons a head args)
              (match many (special-of (predates _) envl head) (((Env) e0) ((Term) t0))
                ((Some b sp) (elab-type-form sugar (subterm _) args two-steps envl sp))
                ((None b)
                  (let (many env2) (many x) (var-of-raw (predates _) envl head "a constructor"))
                  (let (many h) (TVar x))
                  (match many (canon-env (predates _) env2 (infer (predates _) h env2)) (((Env) e0) ((Term) t0))
                    ((TTyCtor ttele)
                      (let (many env3) (many acc) (elab-term-args sugar (subterm _) args (subs-all (predates _) args) (check-arity (predates _) env2 ttele (list-length (predates _) (Raw) args)) ttele (Nil (Term))))
                      (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                    ((TValCtor ctele ret)
                      (let (many env3) (many acc) (elab-term-args sugar (subterm _) args (subs-all (predates _) args) (check-arity (predates _) env2 ctele (list-length (predates _) (Raw) args)) ctele (Nil (Term))))
                      (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                    ((TVar y) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                    ((TBound j) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                    ((TApp h2 a2) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                    ((TFn l p r) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "function in type")))
                    ((TMatchable d t c) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                    ((TNewtype c) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                    ((TErr m) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr m)))))))))))
    (let (many env3) (match many as-type (((Env) e0)) ((BFalse) env2) ((BTrue) (check (predates _) env2 "type" (infer (predates _) t env2) type-term))))
    (values (env-back (predates _) env env3) t))

  (many elab-type-form : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (subterm many (Steps (Succ (Succ (Zero)))) st) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (Term) t)
    (match many st _
      (absurd SZ)
      ((SS sn k)
        (match many sp _
          ((SpFormer fo)
            (match many fo _
              ((FoFn)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed Fn") (TErr "malformed Fn")))
                  ((Cons a lvraw rest)
                    (let (many env2) (many lv) (elab-term sugar (subterm _) lvraw env (BFalse)))
                    (let (many env3) (check (predates _) env2 "type" (infer (predates _) lv env2) level-term))
                    (let (many ps) (many after) (erased wa) (split-arrow (predates _) rest rest (WHere rest) env3))
                    (let (many env4) (many params) (many rets) (elab-fn-type sugar (subterm _) rest one-step (MkPair (List (Sub rest)) (List (Sub rest)) ps (subs-of (predates _) after rest wa)) env3))
                    (values env4 (TFn lv params rets)))))
              ((FoTyCtor)
                (let (many ps) (many after) (erased wa) (split-arrow (predates _) args args (WHere args) env))
                (elab-tyctor sugar args (subterm _) k (MkPair (List (Sub args)) (List (Sub args)) ps (subs-of (predates _) after args wa)) env))
              ((FoValCtor)
                (let (many ps) (many after) (erased wa) (split-arrow (predates _) args args (WHere args) env))
                (let (many env2) (many tele) (many ret) (many t) (elab-valctor sugar args (subterm _) k (MkPair (List (Sub args)) (List (Sub args)) ps (subs-of (predates _) after args wa)) env))
                (values env2 t))
              ((FoMatchable)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed Matchable") (TErr "malformed Matchable")))
                  ((Cons a d rest)
                    (match many rest _
                      ((Nil b) (values (env-error (predates _) env "malformed Matchable") (TErr "malformed Matchable")))
                      ((Cons b t cs)
                        (let (many env2) (many disc) (disc-of-checked (predates _) env d))
                        (let (many env3) (many tid) (named (predates _) env2 t "a type constructor"))
                        (let (many env4) (many mcs) (elab-mctors sugar (subterm _) cs env3))
                        (values env4 (TMatchable disc (TVar tid) mcs)))))))
              ((FoNewtype)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed Newtype") (TErr "malformed Newtype")))
                  ((Cons a c rest)
                    (match many rest _
                      ((Cons b x more) (values (env-error (predates _) env "malformed Newtype") (TErr "malformed Newtype")))
                      ((Nil b)
                        (let (many env2) (many cid) (ctor-var (predates _) env c))
                        (values env2 (TNewtype (TVar cid))))))))))
          ((SpStmt s) (values (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " cannot appear in a type")) (TErr "statement in type")))
          ((SpExpr e) (values (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " cannot appear in a type")) (TErr "expression in type")))
          ((SpMark m) (values (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " cannot appear in a type")) (TErr "mark in type")))))))

  (many elab-mctors : (subterm many (Nat) sugar) (subterm many (List (Raw)) cs) (many (Env) env) -> (many (Env) r) (many (List (MCtor)) mcs)
    (match many cs _
      ((Nil a) (values env (Nil (MCtor))))
      ((Cons a c rest)
        (let (many env1) (many m) (many craw)
          (match many (raw-items (predates _) c) (((Env) e0) ((Mult) m0) ((Raw) r0))
            ((Nil b) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) c))
            ((Cons b mraw more)
              (match many more (((Env) e0) ((Mult) m0) ((Raw) r0))
                ((Nil d) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) c))
                ((Cons d cr more2)
                  (match many more2 (((Env) e0) ((Mult) m0) ((Raw) r0))
                    ((Cons f x y) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) cr))
                    ((Nil f)
                      (match many (mult-of (predates _) env mraw) (((Env) e0) ((Mult) m0) ((Raw) r0))
                        ((None g) (values (env-error (predates _) env (str-cat (predates _) "expected a multiplicity, got " (show-r (predates _) mraw))) (Many) cr))
                        ((Some g mm) (values env mm cr))))))))))
        (let (many env2) (many cid) (ctor-var (predates _) env1 craw))
        (let (many env3) (many mcs) (elab-mctors sugar (subterm _) rest env2))
        (values env3 (Cons (MCtor) (MkMCtor m (TVar cid)) mcs)))))

  ; The signature pieces [piece] were read from [root]; [st] pays for the parse of each telescope.
  (many elab-fn-type : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (Steps (Succ (Zero))) st) (subterm many (Pair (List (Sub root)) (List (Sub root))) piece) (many (Env) env) -> (many (Env) r) (many (List (Entry)) params) (many (List (Entry)) rets)
    (match many piece _
      ((MkPair x y ps rs)
        (let (many env2) (many ids) (many params) (elab-tele sugar root st (subterm _) ps env (MMDeclared) (Nil (Term)) (BTrue)))
        (let (many env3) (many ids2) (many rets) (elab-tele sugar root st (subterm _) rs env2 (MMDeclared) (tvars-rev (predates _) ids (Nil (Term))) (BFalse)))
        (values (env-discard (predates _) env env3) params rets))))

  (many elab-tyctor : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (Steps (Succ (Zero))) st) (subterm many (Pair (List (Sub root)) (List (Sub root))) piece) (many (Env) env) -> (many (Env) r) (many (Term) t)
    (match many piece _
      ((MkPair x y ps ret)
        (let (many env2) (many ids) (many tele) (elab-tele sugar root st (subterm _) ps env (MMErased) (Nil (Term)) (BFalse)))
        (let (many env3)
          (match many ret (((Env) e0))
            ((Cons a s more)
              (match many more (((Env) e0))
                ((Nil b) (match many s (((Env) e0)) ((MkSub rt r p) (let (many env3) (many t) (elab-term sugar (subterm p) r env2 (BFalse))) (check (predates _) env3 "value" t type-term))))
                ((Cons b x2 y2) (env-error (predates _) env2 "TyCtor returns Type"))))
            ((Nil a) (env-error (predates _) env2 "TyCtor returns Type"))))
        (values (env-discard (predates _) env env3) (TTyCtor tele)))))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type; the return is an application of a type constructor in scope (ASSUMPTIONS 70, 80).
  (many elab-valctor : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (Steps (Succ (Zero))) st) (subterm many (Pair (List (Sub root)) (List (Sub root))) piece) (many (Env) env) -> (many (Env) r) (many (List (Entry)) tele) (many (Term) ret) (many (Term) t)
    (match many piece _
      ((MkPair x y ps rets)
        (let (many env2) (many ids) (many tele) (elab-tele sugar root st (subterm _) ps env (MMDeclared) (Nil (Term)) (BFalse)))
        (let (many env3) (many ret)
          (match many rets (((Env) e0) ((Term) t0))
            ((Nil a) (values (env-error (predates _) env2 "a constructor returns one type") (TErr "no return")))
            ((Cons a s more)
              (match many more (((Env) e0) ((Term) t0))
                ((Nil b) (match many s (((Env) e0) ((Term) t0)) ((MkSub rt r p) (elab-term sugar (subterm p) r env2 (BTrue)))))
                ((Cons b x2 y2) (values (env-error (predates _) env2 "a constructor returns one type") (TErr "no return")))))))
        (let (many ok)
          (match many (canon-env (predates _) env3 ret) (((Bool) b0))
            ((TApp h as)
              (match many h (((Bool) b0))
                ((TVar t) (and (predates _) (not (predates _) (list-mem-bin (predates _) ids t))
                             (match many (type-of (predates _) env3 t) (((Bool) b0)) ((TTyCtor p) (BTrue)) ((TVar y2) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse))
                               ((TFn l p r) (BFalse)) ((TValCtor p r) (BFalse)) ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse)))))
                ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
                ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
            ((TVar y2) (BFalse)) ((TBound j) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
            ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
        (let (many env4)
          (match many ok (((Env) e0))
            ((BTrue) env3)
            ((BFalse) (env-error (predates _) env3 (str-cat (predates _) "a constructor returns an application of a type constructor in scope, not " (show-t (predates _) env3 ret))))))
        (values env4 tele ret (TValCtor tele (abstract (predates _) (list-rev (predates _) (Bin) ids) ret))))))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 30).
  ; [ids]: binders already in force, innermost first.
  (many elab-tele : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (Steps (Succ (Zero))) st) (subterm many (List (Sub root)) entries) (many (Env) env) (many (MultsMode) mode) (many (List (Term)) ids) (many (Bool) subterm-ok) -> (many (Env) r) (many (List (Bin)) bound) (many (List (Entry)) tele)
    (match many st _
      (absurd SZ)
      ((SS sn k)
        (let (many env2) (many entries2) (parse-entries-checked (predates _) root entries env))
        (elab-src-entries sugar root (subterm _) k entries2 env2 mode ids (Nil (Bin)) subterm-ok))))

  (many elab-src-entries : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (Steps (Zero)) st) (subterm many (List (SrcEntry root)) entries) (many (Env) env) (many (MultsMode) mode) (many (List (Term)) ids) (many (List (Bin)) bound) (many (Bool) subterm-ok) -> (many (Env) r) (many (List (Bin)) bound2) (many (List (Entry)) tele)
    (match many entries _
      ((Nil a) (values env (list-rev (predates _) (Bin) bound) (Nil (Entry))))
      ((Cons a e rest)
        (match many e _
          ((MkSrcEntry rt sub smult ssg name)
            (let (many env0)
              (match many (and (predates _) sub (not (predates _) subterm-ok)) (((Env) e0))
                ((BTrue) (env-error (predates _) env "subterm is not allowed here"))
                ((BFalse) env)))
            (let (many env1) (many mult) (many mode2)
              (match many mode (((Env) e0) ((Mult) m0) ((MultsMode) md0))
                ((MMDeclared) (match many smult (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((None b) (values (env-error (predates _) env0 (str-cat3 (predates _) "entry " name " needs a multiplicity")) (Many) mode)) ((Some b m) (values env0 m mode))))
                ((MMErased) (match many smult (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((None b) (values env0 (Erased) mode)) ((Some b m) (values (env-error (predates _) env0 "these entries carry no multiplicity") (Erased) mode))))
                ((MMExpect ms)
                  (let (many env0b) (match many smult (((Env) e0)) ((None b) env0) ((Some b m) (env-error (predates _) env0 "a match annotation carries no multiplicities"))))
                  (match many ms (((Env) e0) ((Mult) m0) ((MultsMode) md0)) ((Nil b) (values env0b (Erased) mode)) ((Cons b m more) (values env0b m (MMExpect more)))))))
            (let (many env2) (many sg)
              (match many ssg (((Env) e0) ((Sg) s0))
                ((None b) (values (env-error (predates _) env1 (str-cat3 (predates _) "entry " name " needs a type or an is clause")) (SgTy (TErr "no type"))))
                ((Some b s)
                  (match many s (((Env) e0) ((Sg) s0))
                    ((SrcTy rt2 r p) (let (many env2) (many t) (elab-term sugar (subterm p) r env1 (BTrue))) (values env2 (SgTy t)))
                    ((SrcIs rt2 r p) (let (many env2) (many t) (elab-term sugar (subterm p) r env1 (BFalse))) (values env2 (SgIs t)))))))
            (let (many ty) (many rule) (fact-of (predates _) env2 sg))
            (let (many nm) (name-or-anon (predates _) name))
            (let (many env3) (many x) (bind (predates _) env2 nm mult (SDyn) ty rule coercible-id))
            (let (many entry) (MkEntry nm sub mult (abstract-sg (predates _) (bin-ids-of (predates _) ids) sg)))
            (let (many env4) (many bound2) (many tele) (elab-src-entries sugar root st (subterm _) rest env3 mode2 (Cons (Term) (TVar x) ids) (Cons (Bin) x bound) subterm-ok))
            (values env4 bound2 (Cons (Entry) entry tele)))))))
  ; A body: statements then the final expression (section 16); [items] sits within [root]. An absurd body
  ; (sections 12, 37) is erased and produces one value of an empty type.
  (many elab-body : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (List (Raw)) items) (erased (Within items root) w) (many (Env) env) (many (List (Mult)) expect) (many (Maybe (List (Entry))) tele) (many (Bool) absurd) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many items _
      ((Nil a) (values (env-error (predates _) env "a body needs a final expression") (Nil (Res)) (CError "empty body")))
      ((Cons a item rest)
        (let (erased pi) (in-within (predates _) (Raw) item items root (prove-subterm item items) w))
        (match many rest _
          ((Nil b)
            (let (many env2) (many ress) (many code) (elab-expr sugar (subterm pi) item env expect tele (CCPlain)))
            (match many absurd _
              ((BFalse) (values env2 ress code))
              ((BTrue) (values (check-empty (predates _) env2 (res-ty (predates _) (first-res (predates _) ress))) ress code))))
          ((Cons b item2 rest2)
            (let (many env2) (many sc) (elab-stmt sugar (subterm pi) item env))
            (let (many env3) (many ress) (many code) (elab-body sugar root (subterm _) rest (within-step (predates _) rest items root (prove-subterm rest items) w) env2 expect tele absurd))
            (values env3 ress (wrap-stmt (predates _) sc code)))))))

  (many elab-stmt : (subterm many (Nat) sugar) (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r) (many (StmtCode) sc)
    (let (many envl) (env-at (predates _) env (raw-line (predates _) raw)))
    (let (many bad) (env-error (predates _) envl (str-cat (predates _) (show-r (predates _) raw) " is not a statement")))
    (let (many env2) (many sc)
      (match many raw (((Env) e0) ((StmtCode) sc0))
        ((RAtom lq s) (values bad (SNone)))
        ((RString lq s) (values bad (SNone)))
        ((RList lq items)
          (match many items (((Env) e0) ((StmtCode) sc0))
            ((Nil a) (values bad (SNone)))
            ((Cons a head args)
              (match many (special-of (predates _) envl head) (((Env) e0) ((StmtCode) sc0))
                ((None b) (values bad (SNone)))
                ((Some b sp)
                  (match many sp (((Env) e0) ((StmtCode) sc0))
                    ((SpFormer k) (values bad (SNone))) ((SpExpr k) (values bad (SNone))) ((SpMark k) (values bad (SNone)))
                    ((SpStmt st)
                      (match many st (((Env) e0) ((StmtCode) sc0))
                        ((StLet)
                          (let (many braws) (many rhs) (erased wr) (split-returns (predates _) args args (WHere args) envl))
                          (let (many env0) (many binders) (parse-entries-checked (predates _) args braws envl))
                          (elab-let sugar (subterm _) args (MkLetParts args binders rhs wr) env0))
                        ((StDefLvl)
                          (match many args (((Env) e0) ((StmtCode) sc0))
                            ((Nil c) (values (env-error (predates _) envl "def-lvl needs a name") (SNone)))
                            ((Cons c n more)
                              (let (many env2) (many x) (mint-level (predates _) envl (name-or-anon (predates _) (raw-name (predates _) n))))
                              (values env2 (SNone)))))
                        ((StDefFns) (elab-def-fns sugar (subterm _) args envl))
                        ((StDefAdts)
                          (let (many env3) (many headers) (many tids) (elab-adt-headers sugar (subterm _) args envl))
                          (let (many env4) (many consts) (define-adts sugar (subterm _) args headers env3 tids))
                          (match many (env-run-pos (predates _) env4) (((Env) e0) ((StmtCode) sc0))
                            ((BTrue) (values (set-const-states (predates _) consts env4) (SNone)))
                            ((BFalse)
                              (match many consts (((Env) e0) ((StmtCode) sc0))
                                ((Nil c) (values env4 (SNone)))
                                ((Cons c cn rest) (values env4 (SConsts consts)))))))
                        ((StComptimeMatch) (elab-comptime-match (predates _) envl args))
                        ((StLetMatch) (elab-let-match sugar (subterm _) args envl))
                        ((StUnary) (elab-unary sugar (subterm _) args envl))))))))))))
    (values (env-back (predates _) env env2) sc))

  ; let-match (section 16, ASSUMPTIONS 99-100): a one-constructor match binding outward, its fields at the
  ; scrutinee's own erasure; erased or run at once it leaves no code, else one branch wraps the rest.
  (many elab-let-match : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (StmtCode) sc)
    (let (many bad) (env-error (predates _) env "malformed let-match: expected (let-match <multiplicity> x (C field ...))"))
    (match many args _
      ((Nil a) (values bad (SNone)))
      ((Cons a mraw more)
        (match many more _
          ((Nil b) (values bad (SNone)))
          ((Cons b scrut more2)
            (match many more2 _
              ((Nil c) (values bad (SNone)))
              ((Cons c pat more3)
                (match many more3 _
                  ((Cons d x more4) (values bad (SNone)))
                  ((Nil d)
                    (match many (raw-items (predates _) pat) _
                      ((Nil e) (values bad (SNone)))
                      ((Cons e craw fields)
                        (let (many env0) (many smult) (mult-checked (predates _) env mraw))
                        (let (many env1) (many srs) (many scode) (elab-expr sugar (subterm _) scrut env0 (Cons (Mult) smult (Nil (Mult))) no-tele (CCPlain)))
                        (let (many sres) (first-res (predates _) srs))
                        (match many (type-head (predates _) env1 (res-ty (predates _) sres)) _
                          ((None f) (values (env-error (predates _) env1 (str-cat3 (predates _) "cannot match on " (show-t (predates _) env1 (res-term (predates _) sres)) (str-cat (predates _) " : " (show-t (predates _) env1 (res-ty (predates _) sres))))) (SNone)))
                          ((Some f tid)
                            (let (many env2) (many found) (find-matchable (predates _) env1 tid))
                            (match many found _
                              ((None g) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 tid) " has no Matchable in scope")) (SNone)))
                              ((Some g info)
                                (match many info _
                                  ((MkMatchInfo mid disc mctors rank)
                                    (let (many env3)
                                      (match many (nat-eq (predates _) (list-length (predates _) (MCtor) mctors) 1) (((Env) e0))
                                        ((BTrue) env2)
                                        ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) (name-of (predates _) env2 tid) " has " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (MCtor) mctors)) " constructors, so it needs an ordinary match"))))))
                                    (let (many env4) (many c) (ctor-var (predates _) env3 craw))
                                    (let (many env5) (many mk) (marker-checked (predates _) env4 tid mctors c))
                                    (let (many env6) (match many mk (((Env) e0)) ((Erased) (env-error (predates _) env5 (str-cat (predates _) (name-of (predates _) env5 c) " is phantom"))) ((Many) env5)))
                                    (let (many ctele) (many ret) (ctor-type (predates _) env6 c))
                                    (let (many env7)
                                      (match many (nat-eq (predates _) (list-length (predates _) (Raw) fields) (list-length (predates _) (Entry) ctele)) (((Env) e0))
                                        ((BTrue) env6)
                                        ((BFalse) (env-error (predates _) env6 (str-cat3 (predates _) (name-of (predates _) env6 c) " has " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) ctele)) " fields"))))))
                                    (let (many mults) (under-list (predates _) (tele-mults (predates _) ctele) smult))
                                    (let (many ss) (shapes (predates _) mctors env7))
                                    (let (many run) (and (predates _) (env-run-pos (predates _) env7) (and (predates _) (mult-is-many (predates _) smult) (list-is-empty (predates _) (String) (env-errors (predates _) env7)))))
                                    (let (many states)
                                      (match many run (((Maybe (List (State))) st0))
                                        ((BFalse) (None (List (State))))
                                        ((BTrue)
                                          (match many (ctor-of (predates _) env7 c) (((Maybe (List (State))) st0))
                                            ((None h) (None (List (State))))
                                            ((Some h ct)
                                              (let (many i) (many vs) (destruct (predates _) ct (first-value (predates _) (run-code (predates _) env7 scode))))
                                              (Some (List (State)) (states-of (predates _) (spread (predates _) mults vs))))))))
                                    (let (many env8) (many fids) (open-tele (predates _) ctele env7 (Some (List (Maybe (String))) (raw-names (predates _) fields)) (Some (List (Mult)) mults) states (Nil (Term))))
                                    (let (many env9) (match many run (((Env) e0)) ((BTrue) (trace-many-fields (predates _) fids env8)) ((BFalse) env8)))
                                    (match many (refine (predates _) env9 sres c fids ret) _
                                      ((UContra msg) (values (env-error (predates _) env9 (str-cat3 (predates _) "the scrutinee contradicts the facts in force (" msg ")")) (SNone)))
                                      ((UOk env10)
                                        (match many (or (predates _) run (not (predates _) (mult-is-many (predates _) smult))) _
                                          ((BTrue) (values env10 (SNone)))
                                          ((BFalse) (values env10 (SMatch scode (match-shape (predates _) env10 mid (tagged-of (predates _) disc ss)) (discriminant (predates _) ss c) (non-erased (predates _) fids env10))))))))))))))))))))))))

  ; unary (SUGAR.md 5): the literals checked in the reference's order, then the let-match the form stands
  ; for, written out as there.
  (many elab-unary : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (StmtCode) sc)
    (let (many arity-error) (env-error (predates _) env "unary takes one or two literals"))
    (match many args _
      ((Nil a) (values arity-error (SNone)))
      ((Cons a araw rest)
        (let (many env1) (many ea) (numeral-entry (predates _) env araw))
        (match many ea _
          ((None b) (values env1 (SNone)))
          ((Some b pa)
            (match many pa _
              ((MkPair s t za xa)
                (let (many env2) (many lo)
                  (match many rest (((Env) e0) ((Maybe (Nat)) l0))
                    ((Nil c) (values env1 (Some (Nat) 0)))
                    ((Cons c braw rest2)
                      (match many rest2 (((Env) e0) ((Maybe (Nat)) l0))
                        ((Cons d x rest3) (values arity-error (None (Nat))))
                        ((Nil d)
                          (let (many env2) (many eb) (numeral-entry (predates _) env1 braw))
                          (match many eb (((Env) e0) ((Maybe (Nat)) l0))
                            ((None e) (values env2 (None (Nat))))
                            ((Some e pb)
                              (match many pb (((Env) e0) ((Maybe (Nat)) l0))
                                ((MkPair s2 t2 zb xb)
                                  (match many (nat-lt (predates _) zb za) (((Env) e0) ((Maybe (Nat)) l0))
                                    ((BTrue) (values env2 (Some (Nat) zb)))
                                    ((BFalse) (values (env-error (predates _) env2 (str-cat3 (predates _) "unary: " (nat-str (predates _) za) (str-cat (predates _) " does not exceed " (nat-str (predates _) zb)))) (None (Nat))))))))))))))
                (match many lo _
                  ((None c) (values env2 (SNone)))
                  ((Some c l)
                    (let (many k) (nat-sub (predates _) za l))
                    (match many (nat-lt (predates _) 4096 k) _
                      ((BTrue) (values (env-error (predates _) env2 (str-cat3 (predates _) "unary: " (nat-str (predates _) k) " successors is beyond the limit")) (SNone)))
                      ((BFalse)
                        (let (many floored) (match many rest (((Bool) f)) ((Nil d) (BFalse)) ((Cons d x rest2) (BTrue))))
                        (match many sugar _
                          ((Zero) (values (env-error (predates _) env2 "internal: a generated form contains sugar") (SNone)))
                          ((Succ k)
                            (let (many envp) (many g) (generated-form (predates _) (unary-source (predates _) za l floored (prelude-call (predates _) env2)) env2))
                            (match many g _
                              ((None d) (values (leave-prelude (predates _) env2 envp) (SNone)))
                              ((Some d gen)
                                (let (many env3) (many sc) (elab-stmt (subterm _) k gen envp))
                                (values (leave-prelude (predates _) env2 env3) sc))))))))))))))))

  ; distinct (SUGAR.md 5): a match on numeral-inj's Eq, once the two literals are checked to be different
  ; spellings of one canonical value.
  (many elab-distinct : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (let (many none) (Nil (Res)))
    (let (many bad) (CError "distinct"))
    (let (many arity-error) (env-error (predates _) env "distinct takes two literals"))
    (match many args _
      ((Nil a) (values arity-error none bad))
      ((Cons a araw rest)
        (match many rest _
          ((Nil b) (values arity-error none bad))
          ((Cons b braw rest2)
            (match many rest2 _
              ((Cons c x rest3) (values arity-error none bad))
              ((Nil c)
                (let (many env1) (many ea) (numeral-entry (predates _) env araw))
                (let (many env2) (many eb) (numeral-entry (predates _) env1 braw))
                (match many ea _
                  ((None d) (values env2 none bad))
                  ((Some d pa)
                    (match many eb _
                      ((None e) (values env2 none bad))
                      ((Some e pb)
                        (match many pa _
                          ((MkPair s t za xa)
                            (match many pb _
                              ((MkPair s2 t2 zb xb)
                                (match many (nat-eq (predates _) za zb) _
                                  ((BTrue) (values (env-error (predates _) env2 (str-cat3 (predates _) "distinct: " (nat-str (predates _) za) " is the same literal twice")) none bad))
                                  ((BFalse)
                                    (match many (equal-env (predates _) env2 (TVar xa) (TVar xb)) _
                                      ((BFalse) (values (env-error (predates _) env2 (str-cat3 (predates _) "distinct: " (nat-str (predates _) za) (str-cat3 (predates _) " and " (nat-str (predates _) zb) " do not canonicalize equally here"))) none bad))
                                      ((BTrue)
                                        (match many sugar (((Env) e0) ((List (Res)) rs0) ((Code) c0))
                                          ((Zero) (values (env-error (predates _) env2 "internal: a generated form contains sugar") none bad))
                                          ((Succ k)
                                            (let (many envp) (many g) (generated-form (predates _) (distinct-source (predates _) za zb (prelude-call (predates _) env2)) env2))
                                            (match many g (((Env) e0) ((List (Res)) rs0) ((Code) c0))
                                              ((None f) (values (leave-prelude (predates _) env2 envp) none bad))
                                              ((Some f gen)
                                                (let (many env3) (many ress) (many code) (elab-expr (subterm _) k gen envp erased-one no-tele (CCPlain)))
                                                (values (leave-prelude (predates _) env2 env3) ress code))))))))))))))))))))))))

  ; let (section 9): binders, then the right-hand side; run at once in run position (section 34); an
  ; annotation is a checked redundancy.
  (many elab-let : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (subterm many (LetParts args) parts) (many (Env) env0) -> (many (Env) r) (many (StmtCode) sc)
    (match many parts _
      ((MkLetParts z binders rhs wr)
        (let (many env1) (check-binder-mults (predates _) args binders env0))
        (let (many expect) (src-mults (predates _) args binders))
        (let (many inner) (many ress) (many code) (elab-body sugar args (subterm _) rhs wr env1 expect no-tele (BFalse)))
        (let (many run) (env-run-pos (predates _) env1))
        (let (many vals)
          (match many (and (predates _) run (and (predates _) (mult-is-many (predates _) (pos-of (predates _) expect)) (list-is-empty (predates _) (String) (env-errors (predates _) inner)))) (((List (Value)) vs))
            ((BTrue) (run-code (predates _) inner code))
            ((BFalse) (Nil (Value)))))
        (let (many env2) (many ids) (bind-let sugar args (subterm _) binders (env-restore (predates _) env1 inner) ress (spread (predates _) expect vals) run (Nil (Bin))))
        (let (many many-ids) (non-erased (predates _) ids env2))
        (match many (or (predates _) run (list-is-empty (predates _) (Bin) many-ids)) _
          ((BTrue) (values env2 (SNone)))
          ((BFalse) (values env2 (SLet many-ids code)))))))

  (many bind-let : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (List (SrcEntry root)) binders) (many (Env) env) (many (List (Res)) ress) (many (List (Value)) vals) (many (Bool) run) (many (List (Bin)) acc) -> (many (Env) r) (many (List (Bin)) ids)
    (match many binders _
      ((Nil a) (values env (list-rev (predates _) (Bin) acc)))
      ((Cons a b brest)
        (match many b _
          ((MkSrcEntry rt sub smult ssg name)
            (let (many r) (many rrest) (match many ress (((Res) r0) ((List (Res)) rs0)) ((Nil c) (values (MkRes (TErr "missing value") (TErr "missing value") (Erased)) ress)) ((Cons c r rs) (values r rs))))
            (let (many v) (many vrest) (match many vals (((Value) v0) ((List (Value)) vs0)) ((Nil c) (values (VToken) vals)) ((Cons c v vs) (values v vs))))
            (let (many mult) (match many smult (((Mult) m0)) ((None c) (Many)) ((Some c m) m)))
            (let (many env1)
              (match many ssg (((Env) e0))
                ((None c) env)
                ((Some c s)
                  (match many s (((Env) e0))
                    ((SrcTy rt2 t p) (let (many env1) (many ty) (elab-term sugar (subterm p) t env (BTrue))) (check-sg (predates _) env1 (SgTy ty) r))
                    ((SrcIs rt2 t p) (let (many env1) (many ty) (elab-term sugar (subterm p) t env (BFalse))) (check-sg (predates _) env1 (SgIs ty) r))))))
            (let (many st)
              (match many run (((State) s0))
                ((BTrue) (SConst v))
                ((BFalse)
                  (match many (res-term (predates _) r) (((State) s0))
                    ((TVar y) (entry-state (predates _) env1 y))
                    ((TBound j) (SDyn)) ((TApp h as) (SDyn)) ((TFn l p rr) (SDyn)) ((TTyCtor p) (SDyn)) ((TValCtor p rr) (SDyn))
                    ((TMatchable d t c) (SDyn)) ((TNewtype c) (SDyn)) ((TErr m) (SDyn))))))
            (let (many env2) (many x) (bind (predates _) env1 (name-or-anon (predates _) name) mult st (res-ty (predates _) r) (Some (Term) (res-term (predates _) r)) coercible-id))
            (let (many env3)
              (match many (and (predates _) run (mult-is-many (predates _) mult)) (((Env) e0))
                ((BTrue) (env-push-trace (predates _) env2 (TrConst x v)))
                ((BFalse) env2)))
            (bind-let sugar root (subterm _) brest env3 rrest vrest run (Cons (Bin) x acc)))))))

  ; def-fns (sections 7, 27): headers bound Dyn, each body elaborated at the block's level under its own
  ; subterm parameters and checked against its return telescope; closures minted Const in run position.
  (many elab-def-fns : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (StmtCode) sc)
    (match many args _
      ((Nil a) (values (env-error (predates _) env "def-fns needs a level") (SNone)))
      ((Cons a lvraw fns)
        (let (many env2) (many lvl)
          (match many (is-underscore (predates _) lvraw) (((Env) e0) ((Bin) x0))
            ((BTrue) (mint-level (predates _) env (None (String))))
            ((BFalse) (let (many env2) (many t) (elab-term sugar (subterm _) lvraw env (BFalse))) (level-var-checked (predates _) env2 t))))
        (let (many env3) (many headers) (elab-headers sugar (subterm _) fns env2 lvl))
        (let (many env4) (many fids) (bind-headers (predates _) fns headers env3 lvl))
        (let (many env5) (many fns2) (define-fns sugar (subterm _) fns headers env4 fids lvl (env-run-pos (predates _) env4)))
        (match many (env-run-pos (predates _) env5) _
          ((BTrue)
            (let (many env6) (set-fn-states (predates _) (close-fns (predates _) fns2 fns2 (env-values (predates _) env5)) env5))
            (values (env-push-trace (predates _) env6 (TrFns fns2)) (SNone)))
          ((BFalse)
            (let (many kept) (many-fns (predates _) fns2 env5))
            (match many kept _
              ((Nil b) (values env5 (SNone)))
              ((Cons b f rest) (values env5 (SLetRec kept)))))))))

  (many elab-headers : (subterm many (Nat) sugar) (subterm many (List (Raw)) fns) (many (Env) env) (many (Bin) lvl) -> (many (Env) r) (many (Headers fns) hs)
    (match many fns _
      ((Nil a) (values env (HStop fns)))
      ((Cons a f rest)
        (let (many envl) (env-at (predates _) env (raw-line (predates _) f)))
        (let (many bad) (env-error (predates _) envl "malformed function definition"))
        (match many f _
          ((RAtom lq s) (values bad (HStop fns)))
          ((RString lq s) (values bad (HStop fns)))
          ((RList lq items)
            (match many items _
              ((Nil b) (values bad (HStop fns)))
              ((Cons b mraw items1)
                (let (many env0) (many mult) (mult-checked (predates _) envl mraw))
                (let (many isabs) (many isext) (many items2) (erased w2) (take-marks (predates _) items1 items (WIn items1 items (prove-subterm items1 items)) env0 (MkAbsurd) (MkExtern)))
                (match many items2 _
                  ((Nil c) (values (env-error (predates _) env0 "malformed function header") (HStop fns)))
                  ((Cons c nraw items3)
                    (let (many name) (raw-name (predates _) nraw))
                    (match many items3 _
                      ((Nil d) (values (env-error (predates _) env0 "malformed function header") (HStop fns)))
                      ((Cons d colon sg)
                        (let (many env1) (match many (is-mark (predates _) env0 colon (MkColon)) (((Env) e0)) ((BTrue) env0) ((BFalse) (env-error (predates _) env0 "malformed function header"))))
                        (let (erased psg) (subterm-trans (prove-subterm sg items2) (within-in (predates _) items2 items (Raw) f w2 (prove-subterm items f))))
                        (let (many ps) (many after) (erased wa) (split-arrow (predates _) sg sg (WHere sg) env1))
                        (let (many rs) (many body) (erased wb) (split-returns (predates _) after sg wa env1))
                        (let (many env2) (many params) (many rets) (elab-fn-type sugar (subterm (subterm-trans psg (prove-subterm f fns))) sg one-step (MkPair (List (Sub sg)) (List (Sub sg)) ps rs) env1))
                        (let (many env3) (match many isext (((Env) e0)) ((BTrue) (claim-extern (predates _) env2 name (is-extern-fn (predates _) name))) ((BFalse) env2)))
                        (let (many impl) (match many (and (predates _) isext (is-extern-fn (predates _) name)) (((Maybe (String)) i0)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                        (let (many env4) (many hs) (elab-headers sugar (subterm _) rest (env-back (predates _) env env3) lvl))
                        (values env4 (HCons f rest (MkHeader f name mult isabs impl params rets body (within-in (predates _) body sg (Raw) f wb psg)) hs)))))))))))))

  (many define-fns : (subterm many (Nat) sugar) (subterm many (List (Raw)) fns) (subterm many (Headers fns) headers) (many (Env) env) (many (Bound fns headers) fids) (many (Bin) lvl) (many (Bool) top) -> (many (Env) r) (many (List (Pair (Bin) (Func))) fns2)
    (match many fns _
      ((Nil a) (values env (Nil (Pair (Bin) (Func)))))
      ((Cons a f rest)
        (match many headers _
          ((HStop z) (values env (Nil (Pair (Bin) (Func)))))
          ((HCons g r h hrest)
            (match many fids _
              (absurd BStop)
              ((BCons g3 r3 h3 hs3 x xrest)
                (match many h _
                  ((MkHeader g2 name mult isabs impl params rets body pb)
                    (let (erased q) (subterm-trans pb (prove-subterm f fns)))
                    (let (many ty) (TFn (TVar lvl) params rets))
                    (let (many envb0) (many pids) (open-tele (predates _) params (env-set-run-pos (predates _) env (BFalse)) (None (List (Maybe (String)))) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                    (let (many envb) (env-enter-body (predates _) envb0 lvl (subterm-params (predates _) params pids)))
                    (let (many envb2) (many code)
                      (match many isabs (((Env) e0) ((Code) c0))
                        ((BTrue)
                          (let (many envb2) (many ress) (many code) (elab-body sugar (subterm q) body body (WHere body) envb erased-one no-tele (BTrue)))
                          (values envb2 (CAbsurd)))
                        ((BFalse)
                          (let (many pvars) (tvars-rev (predates _) pids (Nil (Term))))
                          (let (many tele) (instantiate-tele (predates _) pvars rets))
                          (let (many envb1) (many ress) (many code) (elab-body sugar (subterm q) body body (WHere body) envb (under-list (predates _) (tele-mults (predates _) rets) mult) (Some (List (Entry)) tele) (BFalse)))
                          (let (many envb2) (check-results-count (predates _) envb1 rets ress pvars))
                          (values envb2 (match many mult (((Code) c0)) ((Erased) (CErased)) ((Many) code))))))
                    (let (many envb3) (many code2) (many delegated) (check-marks (predates _) envb2 (non-erased (predates _) pids envb2) code))
                    (let (many env2) (env-discard (predates _) env envb3))
                    (let (many env3)
                      (match many delegated (((Env) e0))
                        ((None c) env2)
                        ((Some c callee)
                          (let (many env3) (many px) (bind (predates _) env2 (None (String)) (Erased) (SDyn) (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) (TVar x) (Cons (Term) (type-of (predates _) env2 callee) (Cons (Term) (TVar callee) (Nil (Term))))))) (None (Term)) coercible-id))
                          env3)))
                    (let (many fn) (MkFunc name x (non-erased (predates _) pids envb3) code2 impl top))
                    (let (many env4) (many more) (define-fns sugar (subterm _) rest hrest env3 xrest lvl top))
                    (values env4 (Cons (Pair (Bin) (Func)) (MkPair (Bin) (Func) x fn) more)))))))))))

  ; def-adts (sections 12, 19, 27): type constructors bound first, each as soon as its header is read so a
  ; later header may mention it, then each type's constructors, Matchable and Newtype; every constructor
  ; returns its own type.
  (many elab-adt-headers : (subterm many (Nat) sugar) (subterm many (List (Raw)) adts) (many (Env) env) -> (many (Env) r) (many (AdtHeaders adts) hs) (many (Tids adts hs) tids)
    (match many adts _
      ((Nil a) (values env (AStop adts) (TStop adts)))
      ((Cons a adt rest)
        (let (many envl) (env-at (predates _) env (raw-line (predates _) adt)))
        (let (many bad) (env-error (predates _) envl "malformed def-adts entry"))
        (match many adt _
          ((RAtom lq s) (values bad (AStop adts) (TStop adts)))
          ((RString lq s) (values bad (AStop adts) (TStop adts)))
          ((RList lq items)
            (match many items _
              ((Nil b) (values bad (AStop adts) (TStop adts)))
              ((Cons b nraw items1)
                (let (many name) (raw-name (predates _) nraw))
                (match many items1 _
                  ((Nil c) (values bad (AStop adts) (TStop adts)))
                  ((Cons c colon sg)
                    (let (many env0) (match many (is-mark (predates _) envl colon (MkColon)) (((Env) e0)) ((BTrue) envl) ((BFalse) bad)))
                    (let (many ps) (many after) (erased wa) (split-arrow (predates _) sg sg (WHere sg) env0))
                    (match many after _
                      ((Nil d) (values (env-error (predates _) env0 "malformed def-adts entry") (AStop adts) (TStop adts)))
                      ((Cons d tyraw after2)
                        (match many after2 _
                          ((Nil f) (values (env-error (predates _) env0 "malformed def-adts entry") (AStop adts) (TStop adts)))
                          ((Cons f draw after3)
                            (let (many env1) (many disc) (disc-of-checked (predates _) env0 draw))
                            (let (many nt) (many ext) (many cs) (erased wc) (take-marks (predates _) after3 sg (within-step (predates _) after3 after sg (prove-subterm after3 after) wa) env1 (MkNewtypeMark) (MkExtern)))
                            (let (many tyraws) (Cons (Sub sg) (MkSub sg tyraw (in-within (predates _) (Raw) tyraw after sg (prove-subterm tyraw after) wa)) (Nil (Sub sg))))
                            (let (many env2) (many ty) (elab-tyctor sugar (subterm _) sg one-step (MkPair (List (Sub sg)) (List (Sub sg)) ps tyraws) env1))
                            (let (many st) (match many (env-run-pos (predates _) env2) (((State) s0)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn))))
                            (let (many env2b) (many x) (bind (predates _) env2 (Some (String) name) (Erased) st ty (None (Term)) coercible-id))
                            (let (many env3) (many hs) (many tids) (elab-adt-headers sugar (subterm _) rest (env-back (predates _) env env2b)))
                            (let (many h) (MkAdtHeader adt name disc nt ext cs (within-in (predates _) cs sg (Raw) adt wc (prove-subterm sg adt))))
                            (values env3 (ACons adt rest h hs) (TCons adt rest h hs x tids)))))))))))))))

  (many define-adts : (subterm many (Nat) sugar) (subterm many (List (Raw)) adts) (subterm many (AdtHeaders adts) headers) (many (Env) env) (many (Tids adts headers) tids) -> (many (Env) r) (many (List (Pair (Bin) (Value))) consts)
    (match many adts _
      ((Nil a) (values env (Nil (Pair (Bin) (Value)))))
      ((Cons a adt rest)
        (match many headers _
          ((AStop z) (values env (Nil (Pair (Bin) (Value)))))
          ((ACons g r h hrest)
            (match many tids _
              (absurd TStop)
              ((TCons g3 r3 h3 hs3 tid trest)
                (match many h _
                  ((MkAdtHeader g2 name disc nt ext ctors pc)
                    (let (many env2) (many mcpairs) (elab-ctors sugar (subterm (subterm-trans pc (prove-subterm adt adts))) ctors env tid))
                    (let (many mctors) (mctors-of (predates _) mcpairs))
                    (let (many ss) (shapes (predates _) mctors env2))
                    (let (many tagged) (tagged-of (predates _) disc ss))
                    (let (many env2b) (match many ext (((Env) e0)) ((BTrue) (claim-extern (predates _) env2 name (is-extern-type (predates _) name))) ((BFalse) env2)))
                    (let (many extname) (match many (and (predates _) ext (is-extern-type (predates _) name)) (((Maybe (String)) e0)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                    (let (many records) (ctor-records (predates _) (non-phantom (predates _) ss) env2b 0 tagged extname))
                    (let (many adt2) (MkAdt name tagged records extname))
                    (let (many cvals) (ctor-values (predates _) records))
                    (let (many env3) (many mid) (bind (predates _) env2b (None (String)) (Many) (SConst (VMatchable adt2)) (TMatchable disc (TVar tid) mctors) (None (Term)) coercible-id))
                    (let (many env4)
                      (match many nt (((Env) e0))
                        ((BFalse) env3)
                        ((BTrue)
                          (match many (wrapper (predates _) disc ss) (((Env) e0))
                            ((None c) (env-error (predates _) env3 (str-cat (predates _) name " is not of newtype shape (section 38)")))
                            ((Some c w) (let (many env4) (many nx) (bind (predates _) env3 (None (String)) (Erased) (SDyn) (TNewtype (TVar w)) (None (Term)) coercible-id)) env4)))))
                    (let (many env5) (many more) (define-adts sugar (subterm _) rest hrest env4 trest))
                    (values env5 (list-append (predates _) (Pair (Bin) (Value)) cvals (Cons (Pair (Bin) (Value)) (MkPair (Bin) (Value) mid (VMatchable adt2)) more))))))))))))

  (many elab-ctors : (subterm many (Nat) sugar) (subterm many (List (Raw)) ctors) (many (Env) env) (many (Bin) tid) -> (many (Env) r) (many (List (Pair (Mult) (Bin))) cs)
    (match many ctors _
      ((Nil a) (values env (Nil (Pair (Mult) (Bin)))))
      ((Cons a craw rest)
        (let (many envl) (env-at (predates _) env (raw-line (predates _) craw)))
        (let (many bad) (env-error (predates _) envl "malformed constructor"))
        (let (many env0) (many parsed)
          (match many craw (((Env) e0) ((Maybe (CtorParts craw)) p0))
            ((RAtom lq s) (values bad (None (CtorParts craw))))
            ((RString lq s) (values bad (None (CtorParts craw))))
            ((RList lq items)
              (match many items (((Env) e0) ((Maybe (CtorParts craw)) p0))
                ((Nil b) (values bad (None (CtorParts craw))))
                ((Cons b mraw items1)
                  (let (many env0) (many mult) (mult-checked (predates _) envl mraw))
                  (match many items1 (((Env) e0) ((Maybe (CtorParts craw)) p0))
                    ((Nil c) (values (env-error (predates _) env0 "malformed constructor") (None (CtorParts craw))))
                    ((Cons c nraw more)
                      (match many more (((Env) e0) ((Maybe (CtorParts craw)) p0))
                        ((Nil d) (values (env-error (predates _) env0 "malformed constructor") (None (CtorParts craw))))
                        ((Cons d colon sg)
                          (let (many env1) (match many (is-mark (predates _) env0 colon (MkColon)) (((Env) e0)) ((BTrue) env0) ((BFalse) (env-error (predates _) env0 "malformed constructor"))))
                          (values env1 (Some (CtorParts craw) (MkCtorParts craw mult (raw-name (predates _) nraw) sg (prove-subterm sg craw)))))))))))))
        (match many parsed _
          ((None b) (elab-ctors sugar (subterm _) rest (env-back (predates _) env env0) tid))
          ((Some b cp)
            (match many cp _
              ((MkCtorParts z mult name sg psg)
                (let (many ps) (many after) (erased wa) (split-arrow (predates _) sg sg (WHere sg) env0))
                (let (many env2) (many tele) (many ret) (many ty) (elab-valctor sugar (subterm (subterm-trans psg (prove-subterm craw ctors))) sg one-step (MkPair (List (Sub sg)) (List (Sub sg)) ps (subs-of (predates _) after sg wa)) env0))
                (let (many env2b)
                  (match many (type-head (predates _) env2 ret) (((Env) e0))
                    ((None c) (env-error (predates _) env2 (str-cat3 (predates _) name " must return an application of " (name-of (predates _) env2 tid))))
                    ((Some c t) (match many (bin-eq (predates _) t tid) (((Env) e0)) ((BTrue) env2) ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) name " must return an application of " (name-of (predates _) env2 tid))))))))
                (let (many env2c)
                  (match many (and (predates _) (not (predates _) (mult-is-many (predates _) mult)) (not (predates _) (nat-is-zero (predates _) (many-count (predates _) tele)))) (((Env) e0))
                    ((BTrue) (env-warn (predates _) env2b (str-cat3 (predates _) "warning: phantom constructor " name " has a many field")))
                    ((BFalse) env2b)))
                (let (many env3) (env-discard (predates _) env0 env2c))
                (let (many st) (match many mult (((State) s0)) ((Erased) (match many (env-run-pos (predates _) env3) (((State) s0)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn)))) ((Many) (SDyn))))
                (let (many env4) (many c) (bind (predates _) env3 (Some (String) name) mult st ty (None (Term)) coercible-id))
                (let (many env5) (many cs) (elab-ctors sugar (subterm _) rest (env-back (predates _) env env4) tid))
                (values env5 (Cons (Pair (Mult) (Bin)) (MkPair (Mult) (Bin) mult c) cs)))))))))
  ; tail and delegate wrap a call (section 9, ASSUMPTIONS 9); the compiled code must be that call.
  (many elab-marked : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) (many (List (Mult)) expect) (many (CC) cc) (many (Sp) sp) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (let (many env1) (match many (pos-of (predates _) expect) (((Env) e0)) ((Erased) (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " in an erased position"))) ((Many) env)))
    (match many args _
      ((Nil a) (values (env-error (predates _) env1 (str-cat (predates _) (sp-name (predates _) sp) " marks a function call, not nothing")) (Nil (Res)) (CError "mark")))
      ((Cons a call rest)
        (let (many env2) (many ress) (many code) (elab-expr sugar (subterm _) call env1 expect no-tele cc))
        (let (many ok)
          (match many code (((Bool) b0))
            ((CApp f as cc2) (cc-eq (predates _) cc cc2))
            ((CLet ids rhs body) (match many rhs (((Bool) b0)) ((CApp f as cc2) (cc-eq (predates _) cc cc2)) ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CValues cs) (BFalse)) ((CLet i r b2) (BFalse)) ((CLetRec fs b2) (BFalse)) ((CMatch s sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
            ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CValues cs) (BFalse)) ((CLetRec fs b2) (BFalse)) ((CMatch s sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
        (match many ok _
          ((BTrue) (values env2 ress code))
          ((BFalse) (values (env-error (predates _) env2 (str-cat3 (predates _) (sp-name (predates _) sp) " marks a function call, not " (show-r (predates _) call))) ress code))))))

  (many elab-values : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) (many (List (Mult)) expect) -> (many (Env) r) (many (List (Res)) ress) (many (List (Code)) codes)
    (match many expect _
      ((Nil a) (values env (Nil (Res)) (Nil (Code))))
      ((Cons a m mrest)
        (match many args _
          ((Nil b) (values env (Nil (Res)) (Nil (Code))))
          ((Cons b arg arest)
            (let (many env2) (many rs) (many code) (elab-expr sugar (subterm _) arg env (Cons (Mult) m (Nil (Mult))) no-tele (CCPlain)))
            (let (many env3) (many ress) (many codes) (elab-values sugar (subterm _) arest env2 mrest))
            (values env3 (Cons (Res) (first-res (predates _) rs) ress) (match many m (((List (Code)) l0)) ((Many) (Cons (Code) code codes)) ((Erased) codes))))))))

  (many elab-two-terms : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (Term) a) (many (Term) b)
    (match many args _
      ((Nil x) (values (env-error (predates _) env "two arguments expected") (TErr "missing") (TErr "missing")))
      ((Cons x araw rest)
        (match many rest _
          ((Nil y) (values (env-error (predates _) env "two arguments expected") (TErr "missing") (TErr "missing")))
          ((Cons y braw more)
            (let (many env2) (many a) (elab-term sugar (subterm _) araw env (BFalse)))
            (let (many env3) (many b) (elab-term sugar (subterm _) braw env2 (BFalse)))
            (values env3 a b))))))

  ; Two proofs of the given kinds, elaborated erased (ASSUMPTIONS 23).
  (many two-proofs : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) -> (many (Env) r) (many (Term) p) (many (Term) q)
    (match many args _
      ((Nil x) (values (env-error (predates _) env "two proofs expected") (TErr "proof") (TErr "proof")))
      ((Cons x araw rest)
        (match many rest _
          ((Nil y) (values (env-error (predates _) env "two proofs expected") (TErr "proof") (TErr "proof")))
          ((Cons y braw more)
            (let (many env2) (many prs) (many pc) (elab-expr sugar (subterm _) araw env erased-one no-tele (CCPlain)))
            (let (many env3) (many qrs) (many qc) (elab-expr sugar (subterm _) braw env2 erased-one no-tele (CCPlain)))
            (values env3 (erased-term (predates _) prs) (erased-term (predates _) qrs)))))))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field, each checked against
  ; the field's type on its side (section 38).
  (many coercible-ctor-args : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) (many (List (Entry)) tele) (many (List (Term)) src) (many (List (Term)) tgt) (many (Bin) c) -> (many (Env) r) (many (List (Term)) src2) (many (List (Term)) tgt2)
    (let (many wrong) (env-error (predates _) env (str-cat (predates _) "coercible-ctor: wrong number of arguments for " (name-of (predates _) env c))))
    (match many tele _
      ((Nil a) (match many args _ ((Nil b) (values env src tgt)) ((Cons b x more) (values wrong src tgt))))
      ((Cons a e rest)
        (match many (entry-mult (predates _) e) _
          ((Erased)
            (match many args _
              ((Nil b) (values wrong src tgt))
              ((Cons b sraw more)
                (match many more _
                  ((Nil d) (values wrong src tgt))
                  ((Cons d traw args2)
                    (let (many env2) (many s) (elab-term sugar (subterm _) sraw env (BFalse)))
                    (let (many env3) (many t) (elab-term sugar (subterm _) traw env2 (BFalse)))
                    (let (many env4) (check-sg (predates _) env3 (sg-inst (predates _) src (entry-sg (predates _) e)) (term-res (predates _) env3 s)))
                    (let (many env5) (check-sg (predates _) env4 (sg-inst (predates _) tgt (entry-sg (predates _) e)) (term-res (predates _) env4 t)))
                    (coercible-ctor-args sugar (subterm _) args2 env5 rest (Cons (Term) s src) (Cons (Term) t tgt) c))))))
          ((Many)
            (match many args _
              ((Nil b) (values wrong src tgt))
              ((Cons b praw more)
                (let (many env2) (many prs) (many pc) (elab-expr sugar (subterm _) praw env erased-one no-tele (CCPlain)))
                (let (many env3) (many sty) (many s) (many tty) (many t) (expect-proof4 (predates _) env2 coercible-id (erased-term (predates _) prs)))
                (let (many env4) (check-sg (predates _) env3 (sg-inst (predates _) src (entry-sg (predates _) e)) (MkRes s sty (Erased))))
                (let (many env5) (check-sg (predates _) env4 (sg-inst (predates _) tgt (entry-sg (predates _) e)) (MkRes t tty (Erased))))
                (coercible-ctor-args sugar (subterm _) more env5 rest (Cons (Term) s src) (Cons (Term) t tgt) c))))))))

  ; match (sections 11, 12, 18): the scrutinee, its Matchable, the annotation, then one branch per
  ; constructor, each refined by its forced facts or refuted by them.
  (many elab-match : (subterm many (Nat) sugar) (subterm many (List (Raw)) args) (many (Env) env) (many (List (Mult)) expect) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (let (many bad) (many bad-ress) (many bad-code) (values (env-error (predates _) env "malformed match") (Nil (Res)) (CError "match")))
    (match many args _
      ((Nil a) (values bad bad-ress bad-code))
      ((Cons a mraw more)
        (match many more _
          ((Nil b) (values bad bad-ress bad-code))
          ((Cons b scrut more2)
            (match many more2 _
              ((Nil c) (values bad bad-ress bad-code))
              ((Cons c ann branches)
                (let (many pos) (pos-of (predates _) expect))
                (let (many env0) (many sm) (mult-checked (predates _) env mraw))
                (let (many smult) (under (predates _) pos sm))
                (let (many env2) (many srs) (many scode) (elab-expr sugar (subterm _) scrut env0 (Cons (Mult) smult (Nil (Mult))) no-tele (CCPlain)))
                (let (many sres) (first-res (predates _) srs))
                (match many (type-head (predates _) env2 (res-ty (predates _) sres)) _
                  ((None d) (values (env-error (predates _) env2 (str-cat3 (predates _) "cannot match on " (show-t (predates _) env2 (res-term (predates _) sres)) (str-cat (predates _) " : " (show-t (predates _) env2 (res-ty (predates _) sres))))) (Nil (Res)) (CError "no head")))
                  ((Some d tid)
                    (let (many env2b) (many found) (find-matchable (predates _) env2 tid))
                    (match many found _
                      ((None e) (values (env-error (predates _) env2b (str-cat (predates _) (name-of (predates _) env2b tid) " has no Matchable in scope")) (Nil (Res)) (CError "no Matchable")))
                      ((Some e info)
                        (match many info _
                          ((MkMatchInfo mid disc mctors rank)
                            (let (many ss) (shapes (predates _) mctors env2b))
                            (let (many tagged) (tagged-of (predates _) disc ss))
                            (let (many env2c)
                              (match many (and (predates _) (mult-is-many (predates _) pos) (and (predates _) (mult-is-many (predates _) smult) (not (predates _) (mult-is-many (predates _) (entry-mult-of (predates _) env2b mid))))) (((Env) e0))
                                ((BTrue) (env-error (predates _) env2b (str-cat3 (predates _) "the Matchable for " (name-of (predates _) env2b tid) " is erased, so a non-erased match cannot take a value of it apart")))
                                ((BFalse) env2b)))
                            (let (many env3) (many ann-tele)
                              (match many (is-underscore (predates _) ann) (((Env) e0) ((List (Entry)) t0))
                                ((BTrue) (match many tele (((Env) e0) ((List (Entry)) t0)) ((None f) (values (env-error (predates _) env2c "no telescope to reuse for _") (Nil (Entry)))) ((Some f t) (values env2c t))))
                                ((BFalse)
                                  (match many ann (((Env) e0) ((List (Entry)) t0))
                                    ((RList lq aitems)
                                      (let (many env3) (many ids) (many t) (elab-tele sugar (subterm _) aitems one-step (subs-all (predates _) aitems) env2c (MMExpect expect) (Nil (Term)) (BFalse)))
                                      (values (env-discard (predates _) env2c env3) t))
                                    ((RAtom lq s) (values (env-error (predates _) env2c "malformed match annotation") (Nil (Entry))))
                                    ((RString lq s) (values (env-error (predates _) env2c "malformed match annotation") (Nil (Entry))))))))
                            (let (many env3b)
                              (match many (nat-eq (predates _) (list-length (predates _) (Entry) ann-tele) (list-length (predates _) (Mult) expect)) (((Env) e0))
                                ((BTrue) env3)
                                ((BFalse) (env-error (predates _) env3 (str-cat3 (predates _) "match annotation has " (nat-str (predates _) (list-length (predates _) (Entry) ann-tele)) (str-cat (predates _) " entries, position needs " (nat-str (predates _) (list-length (predates _) (Mult) expect))))))))
                            (let (many env4) (many rids) (open-tele (predates _) ann-tele env3b (Some (List (Maybe (String))) (anon-names (predates _) ann-tele)) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                            (let (many env5) (many real) (many seen) (elab-branches sugar (subterm _) branches env4 tid sres smult mctors ann-tele expect (Nil (RealBranch)) (Nil (Bin))))
                            (let (many env6) (check-coverage (predates _) mctors env5 seen))
                            (let (many env7)
                              (match many (and (predates _) (mult-is-many (predates _) pos) (and (predates _) (or (predates _) (not (predates _) tagged) (not (predates _) (mult-is-many (predates _) smult))) (nat-lt (predates _) 1 (list-length (predates _) (RealBranch) real)))) (((Env) e0))
                                ((BTrue) (env-error (predates _) env6 "a match without a runtime discriminant can have only one real branch"))
                                ((BFalse) env6)))
                            (let (many code)
                              (match many pos (((Code) c0))
                                ((Erased) (CErased))
                                ((Many)
                                  (match many real (((Code) c0))
                                    ((Nil f) (CAbsurd))
                                    ((Cons f rb more3)
                                      (match many (and (predates _) (not (predates _) (mult-is-many (predates _) smult)) (list-is-empty (predates _) (RealBranch) more3)) (((Code) c0))
                                        ((BTrue) (match many rb (((Code) c0)) ((MkRealBranch cc fids body) body)))
                                        ((BFalse) (CMatch scode (match-shape (predates _) env7 mid tagged) (real-branches-code (predates _) real ss)))))))))
                            (values env7 (ress-of (predates _) rids env7) code))))))))))))))

  ; Each branch: present, refuted automatically with (absurd C), or absurd by proof (section 12).
  (many elab-branches : (subterm many (Nat) sugar) (subterm many (List (Raw)) branches) (many (Env) env) (many (Bin) tid) (many (Res) sres) (many (Mult) smult) (many (List (MCtor)) mctors) (many (List (Entry)) ann-tele) (many (List (Mult)) expect) (many (List (RealBranch)) acc) (many (List (Bin)) seen) ->
      (many (Env) r) (many (List (RealBranch)) real) (many (List (Bin)) seen2)
    (match many branches _
      ((Nil a) (values env (list-rev (predates _) (RealBranch) acc) seen))
      ((Cons a braw brest)
        (let (many envl) (env-at (predates _) env (raw-line (predates _) braw)))
        (match many (branch-parts (predates _) envl braw) _
          ((None b) (elab-branches sugar (subterm _) brest (env-back (predates _) env (env-error (predates _) envl "malformed branch")) tid sres smult mctors ann-tele expect acc seen))
          ((Some b bp)
            (let (many craw) (many fields) (many refuted)
              (match many bp (((Raw) c0) ((List (Raw)) f0) ((Bool) b0))
                ((BPresent z c fs body p) (values c fs (BFalse)))
                ((BRefuted z c) (values c (Nil (Raw)) (BTrue)))
                ((BAbsurd z c fs body p) (values c fs (BFalse)))))
            (let (many env1) (many c) (ctor-var (predates _) envl craw))
            (let (many env2) (many mk) (marker-checked (predates _) envl tid mctors c))
            (let (many phantom) (match many mk (((Bool) x0)) ((Erased) (BTrue)) ((Many) (BFalse))))
            (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
            (let (many env3)
              (match many (or (predates _) refuted (nat-eq (predates _) (list-length (predates _) (Raw) fields) (list-length (predates _) (Entry) ctele))) (((Env) e0))
                ((BTrue) env2)
                ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) (name-of (predates _) env2 c) " has " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) ctele)) " fields"))))))
            (let (many unreachable) (and (predates _) phantom (mult-is-many (predates _) smult)))
            (let (many mults) (match many phantom (((List (Mult)) ms0)) ((BTrue) (all-erased (predates _) (tele-mults (predates _) ctele))) ((BFalse) (under-list (predates _) (tele-mults (predates _) ctele) smult))))
            (let (many names) (match many refuted (((List (Maybe (String))) ns0)) ((BTrue) (anon-names (predates _) ctele)) ((BFalse) (raw-names (predates _) fields))))
            (let (many envb) (many fids) (open-tele (predates _) ctele (env-set-run-pos (predates _) env3 (BFalse)) (Some (List (Maybe (String))) names) (Some (List (Mult)) mults) (None (List (State))) (Nil (Term))))
            (let (many env4) (many acc2)
              (match many (refine (predates _) envb sres c fids ret) (((Env) e0) ((List (RealBranch)) rs0))
                ((UContra msg)
                  (match many refuted (((Env) e0) ((List (RealBranch)) rs0))
                    ((BTrue) (values (env-discard (predates _) env3 envb) acc))
                    ((BFalse) (values (env-error (predates _) (env-discard (predates _) env3 envb) (str-cat3 (predates _) "branch " (name-of (predates _) env3 c) (str-cat3 (predates _) " is refuted; write (absurd " (name-of (predates _) env3 c) ")"))) acc))))
                ((UOk envb2)
                  (match many bp (((Env) e0) ((List (RealBranch)) rs0))
                    ((BPresent z c2 fs body p)
                      (let (erased q) (subterm-trans p (prove-subterm braw branches)))
                      (let (many envb3) (many ress) (many code) (elab-body sugar (subterm q) body body (WHere body) envb2 (match many unreachable (((List (Mult)) ms0)) ((BTrue) (all-erased (predates _) expect)) ((BFalse) expect)) (Some (List (Entry)) ann-tele) (BFalse)))
                      (let (many envb4) (check-results-count (predates _) envb3 ann-tele ress (Nil (Term))))
                      (values (env-discard (predates _) env3 envb4)
                              (match many unreachable (((List (RealBranch)) rs0)) ((BTrue) acc) ((BFalse) (Cons (RealBranch) (MkRealBranch c (non-erased (predates _) fids envb4) code) acc)))))
                    ((BRefuted z c2) (values (env-error (predates _) (env-discard (predates _) env3 envb2) (str-cat3 (predates _) "branch " (name-of (predates _) env3 c) " is not refuted")) acc))
                    ((BAbsurd z c2 fs body p)
                      (let (erased q) (subterm-trans p (prove-subterm braw branches)))
                      (let (many envb3) (many ress) (many code) (elab-body sugar (subterm q) body body (WHere body) envb2 erased-one no-tele (BTrue)))
                      (values (env-discard (predates _) env3 envb3) acc))))))
            (elab-branches sugar (subterm _) brest (env-back (predates _) env env4) tid sres smult mctors ann-tele expect acc2 (Cons (Bin) c seen)))))))

  ; Arguments against a telescope, each at the position's multiplicity and checked against its entry
  ; (section 20); returns the terms innermost first and the code of the many ones in order.
  (many check-args : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (List (Sub root)) args) (many (Env) env) (many (List (Entry)) tele) (many (Mult) pos) (many (List (Term)) acc) (many (List (Code)) codes) ->
      (many (Env) r) (many (List (Term)) acc2) (many (List (Code)) codes2)
    (match many tele _
      ((Nil a)
        (match many args _
          ((Nil b) (values env acc (list-rev (predates _) (Code) codes)))
          ((Cons b x more) (values (env-error (predates _) env (str-cat (predates _) "expected fewer arguments, got " (nat-str (predates _) (list-length (predates _) (Sub root) args)))) acc (list-rev (predates _) (Code) codes)))))
      ((Cons a e rest)
        (match many args _
          ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "expected " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) tele)) " more arguments, got 0"))) acc (list-rev (predates _) (Code) codes)))
          ((Cons b s arest)
            (match many s _
              ((MkSub z arg p)
                (let (many m) (entry-mult (predates _) e))
                (let (many env2) (many rs) (many code) (elab-expr sugar (subterm p) arg env (Cons (Mult) (under (predates _) pos m) (Nil (Mult))) no-tele (CCPlain)))
                (let (many r) (first-res (predates _) rs))
                (let (many sg) (match many (entry-sg (predates _) e) (((Sg) s0)) ((SgTy t) (SgTy (instantiate (predates _) acc t))) ((SgIs t) (SgIs (instantiate (predates _) acc t)))))
                (let (many env3) (check-sg (predates _) env2 sg r))
                (check-args sugar root (subterm _) arest env3 rest pos (Cons (Term) (res-term (predates _) r) acc)
                  (match many m (((List (Code)) l0)) ((Many) (Cons (Code) code codes)) ((Erased) codes))))))))))

  (many elab-term-args : (subterm many (Nat) sugar) (subterm many (List (Raw)) root) (subterm many (List (Sub root)) args) (many (Env) env) (many (List (Entry)) tele) (many (List (Term)) acc) -> (many (Env) r) (many (List (Term)) acc2)
    (match many tele _
      ((Nil a)
        (match many args _
          ((Nil b) (values env acc))
          ((Cons b x more) (values (env-error (predates _) env (str-cat (predates _) "expected fewer arguments, got " (nat-str (predates _) (list-length (predates _) (Sub root) args)))) acc))))
      ((Cons a e rest)
        (match many args _
          ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "expected " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) tele)) " more arguments, got 0"))) acc))
          ((Cons b s arest)
            (match many s _
              ((MkSub z arg p)
                (let (many env2) (many t) (elab-term sugar (subterm p) arg env (BFalse)))
                (let (many sg) (match many (entry-sg (predates _) e) (((Sg) s0)) ((SgTy ty) (SgTy (instantiate (predates _) acc ty))) ((SgIs ty) (SgIs (instantiate (predates _) acc ty)))))
                (let (many env3) (check-sg (predates _) env2 sg (term-res (predates _) env2 t)))
                (elab-term-args sugar root (subterm _) arest env3 rest (Cons (Term) t acc)))))))))

  ; A function call (section 9): a lower-level call carries a Predates proof about the callee's level, a
  ; same-level call a Subterm proof for its decreasing argument; the top level carries neither (section 24).
  (many elab-call : (subterm many (Nat) sugar) (subterm many (List (Raw)) rawargs) (subterm many (Pair (List (Sub rawargs)) (Ann rawargs)) parts) (many (Env) env) (many (List (Mult)) expect) (many (Res) callee) (many (Code) hcode) (many (Term) lv) (many (List (Entry)) params) (many (List (Entry)) rets) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many parts _
      ((MkPair x y args ann)
        (let (many pos) (pos-of (predates _) expect))
        (let (many env1)
          (match many (and (predates _) (mult-is-many (predates _) pos) (not (predates _) (mult-is-many (predates _) (res-erasure (predates _) callee)))) (((Env) e0))
            ((BTrue) (env-error (predates _) env (str-cat3 (predates _) "erased function " (show-t (predates _) env (res-term (predates _) callee)) " called in a non-erased position")))
            ((BFalse) env)))
        (let (many env2) (many acc) (many codes) (check-args sugar rawargs (subterm _) args (check-arity (predates _) env1 params (list-length (predates _) (Sub rawargs) args)) params pos (Nil (Term)) (Nil (Code))))
        (let (many arg-terms) (list-rev (predates _) (Term) acc))
        (let (many env3) (check-call-proof sugar rawargs (subterm _) ann env2 callee lv params arg-terms))
        (let (many rmults) (tele-mults (predates _) rets))
        (let (many env4) (many ids) (open-tele (predates _) rets env3 (Some (List (Maybe (String))) (anon-names (predates _) rets)) (Some (List (Mult)) (under-list (predates _) rmults pos)) (None (List (State))) acc))
        (let (many call) (CApp hcode codes cc))
        (let (many env5) (many code)
          (match many pos (((Env) e0) ((Code) c0))
            ((Erased) (values env4 (CErased)))
            ((Many)
              (match many (and (predates _) (nat-eq (predates _) (list-length (predates _) (Mult) expect) (list-length (predates _) (Entry) rets)) (needs-projection (predates _) expect rmults)) (((Env) e0) ((Code) c0))
                ((BFalse) (values env4 call))
                ((BTrue)
                  (let (many env5) (many bound) (many kept) (projection (predates _) expect rmults env4))
                  (values env5 (CLet bound call (CValues kept))))))))
        (values env5 (ress-of (predates _) ids env5) code))))

  ; The call-site proof (section 9), read against the current level and enclosing subterm parameters.
  (many check-call-proof : (subterm many (Nat) sugar) (subterm many (List (Raw)) rawargs) (subterm many (Ann rawargs) ann) (many (Env) env) (many (Res) callee) (many (Term) lv) (many (List (Entry)) params) (many (List (Term)) args) -> (many (Env) r)
    (match many (env-level (predates _) env) _
      ((None a)
        (match many ann _
          ((AnnNone z) env)
          ((AnnPredates z p pp) (env-error (predates _) env "the top level calls without proofs; drop the decrease annotation (section 24)"))
          ((AnnSubterm z i p pp) (env-error (predates _) env "the top level calls without proofs; drop the decrease annotation (section 24)"))))
      ((Some a cur)
        (let (many same) (equal-env (predates _) env lv (TVar cur)))
        (match many ann _
          ((AnnNone z) (env-error (predates _) env (call-needs (predates _) env callee same)))
          ((AnnSubterm z i p pp)
            (match many same _
              ((BFalse) (env-error (predates _) env (call-needs (predates _) env callee same)))
              ((BTrue)
                (let (many positions) (subterm-indices (predates _) params 0))
                (match many (index-of-nat (predates _) positions i 0) _
                  ((None b) (env-error (predates _) env (str-cat3 (predates _) "argument " (nat-str (predates _) i) " is not a subterm parameter")))
                  ((Some b kk)
                    (let (many env2) (check-earlier (predates _) positions env args 0 kk))
                    (match many (list-nth (predates _) (Bin) (env-subterms (predates _) env2) kk) _
                      ((None c) (env-error (predates _) env2 (str-cat3 (predates _) "the enclosing function has no subterm parameter at position " (nat-str (predates _) kk) "")))
                      ((Some c counterpart)
                        (let (many arg) (nth-term (predates _) args i))
                        (let (many env3) (many pterm)
                          (match many (is-underscore (predates _) p) (((Env) e0) ((Term) t0))
                            ((BTrue) (let (many env3) (many pr) (mint-subterm (predates _) env2 arg (TVar counterpart))) (values env3 (res-term (predates _) pr)))
                            ((BFalse)
                              (let (many env3) (many prs) (many pc) (elab-expr sugar (subterm pp) p env2 erased-one no-tele (CCPlain)))
                              (values env3 (erased-term (predates _) prs)))))
                        (let (many env4) (many s0) (many s1) (many s2) (many s3) (expect-proof4 (predates _) env3 subterm-id pterm))
                        (let (many env5) (check (predates _) env4 "value" s1 arg))
                        (check (predates _) env5 "value" s3 (TVar counterpart)))))))))
          ((AnnPredates z p pp)
            (match many same _
              ((BTrue) (env-error (predates _) env (call-needs (predates _) env callee same)))
              ((BFalse)
                (let (many env2) (many pterm)
                  (match many (is-underscore (predates _) p) (((Env) e0) ((Term) t0))
                    ((BTrue)
                      (let (many nv-env) (many nv-term) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                      (match many (canon-env (predates _) env lv) (((Env) e0) ((Term) t0))
                        ((TVar m) (let (many env2) (many pr) (mint-predates (predates _) env m cur)) (values env2 (res-term (predates _) pr)))
                        ((TBound j) (values nv-env nv-term)) ((TApp h as) (values nv-env nv-term)) ((TFn l ps rs) (values nv-env nv-term)) ((TTyCtor ps) (values nv-env nv-term))
                        ((TValCtor ps rs) (values nv-env nv-term)) ((TMatchable d t c) (values nv-env nv-term)) ((TNewtype c) (values nv-env nv-term))
                        ((TErr m) (values (env-error (predates _) env m) (TErr m)))))
                    ((BFalse)
                      (let (many env2) (many prs) (many pc) (elab-expr sugar (subterm pp) p env erased-one no-tele (CCPlain)))
                      (values env2 (erased-term (predates _) prs)))))
                (let (many env3) (many p0) (many p1) (many p2) (expect-proof3 (predates _) env2 predates-id pterm))
                (let (many env4) (check (predates _) env3 "value" p2 (TVar cur)))
                (match many (equal-env (predates _) env4 p1 lv) _
                  ((BTrue) env4)
                  ((BFalse) (env-error (predates _) env4 (str-cat3 (predates _) (show-t (predates _) env4 pterm) " : " (str-cat3 (predates _) (show-t (predates _) env4 (infer (predates _) pterm env4)) " does not relate the callee's level " (show-t (predates _) env4 lv))))))))))))))


; ---- The top level (section 16): statements run as they are elaborated, the final expression consumed;
; only the last form may be an expression (ASSUMPTIONS 12).

(def-fns _ $ many run-toplevel : (subterm many (List (Raw)) items) (many (Env) env) -> (many (Env) r)
  (match many items _
    ((Nil a) env)
    ((Cons a item rest)
      (let (many env2) (intern-literals (predates _) item (env-at (predates _) env (raw-line (predates _) item))))
      (match many (is-statement (predates _) env2 item) _
        ((BTrue)
          (let (many env3) (many sc) (elab-stmt (predates _) sugar-budget item env2))
          (run-toplevel (subterm _) rest env3))
        ((BFalse)
          (match many rest _
            ((Cons b x more) (run-toplevel (subterm _) rest (env-error (predates _) env2 "only the last top-level form may be an expression")))
            ((Nil b)
              (let (many env3) (many ress) (many code) (elab-expr (predates _) sugar-budget item env2 many-one no-tele (CCPlain)))
              (match many (env-errors (predates _) env3) _
                ((Cons c e es) env3)
                ((Nil c)
                  (let (many v) (first-value (predates _) (run-code (predates _) env3 code)))
                  (env-push-trace (predates _) env3 (TrFinal v (res-ty (predates _) (first-res (predates _) ress)))))))))))))