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
  (many SConsts : (many (List (Pair (Bin) (Value))) cs) -> (StmtCode)))

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
      (CLet ids (CValues codes) rest))))

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
  (many LChar : -> (LitKind))
  (many LString : -> (LitKind)))

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
    ((LString) (None (String)))
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

(def-fns _ $ many prelude-id : (many (Env) env) (many (String) name) -> (many (Bin) x)
  (match many (lookup (predates _) env name) _ ((None a) (BZ)) ((Some a x) x)))

(def-fns _ $ many prelude-type : (many (Env) env) (many (String) name) -> (many (Term) t)
  (TApp (TVar (prelude-id (predates _) env name)) (Nil (Term))))

(def-fns _ $ many divmod2 : (subterm many (Nat) fuel) (many (Nat) n) (many (Nat) q) -> (many (Nat) q2) (many (Nat) r)
  (match many fuel _
    ((Zero) (values q n))
    ((Succ k)
      (match many (nat-lt (predates _) n 2) _
        ((BTrue) (values q n))
        ((BFalse) (divmod2 (subterm _) k (nat-sub (predates _) n 2) (Succ q)))))))

; The bijective base-2 spelling of a number as a term over the prelude's Bin (ASSUMPTIONS 50).
(def-fns _ $ many nat-bin-term : (subterm many (Nat) fuel) (many (Nat) n) (many (Env) env) -> (many (Term) t)
  (match many fuel _
    ((Zero) (TErr "out of fuel"))
    ((Succ k)
      (match many n _
        ((Zero) (TApp (TVar (prelude-id (predates _) env "BZ")) (Nil (Term))))
        ((Succ n1)
          (let (many q) (many r) (divmod2 (predates _) n1 n1 (Zero)))
          (let (many digit) (match many r (((String) d)) ((Zero) "B1") ((Succ r1) "B2")))
          (TApp (TVar (prelude-id (predates _) env digit)) (Cons (Term) (nat-bin-term (subterm _) k q env) (Nil (Term)))))))))

(def-fns _ $ many lit-lookup : (many (Env) env) (many (String) key) -> (many (Maybe (Bin)) r)
  (nm-get (predates _) (Bin) key (env-literals (predates _) env)))

; Interns a numeral: a Const Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
(def-fns _ $ many intern-numeral : (many (Env) env) (many (String) key) -> (many (Env) r) (many (Bin) x) (many (Bin) proof)
  (let (many n) (parse-nat (predates _) key 0))
  (let (many env2) (many x) (bind (predates _) env (None (String)) (Many) (SConst (vnat (predates _) n)) (prelude-type (predates _) env "Nat") (None (Term)) coercible-id))
  (let (many pty) (TApp (TVar (prelude-id (predates _) env "Numeral")) (Cons (Term) (nat-bin-term (predates _) (Succ n) n env) (Cons (Term) (TVar x) (Nil (Term))))))
  (let (many env3) (many p) (bind (predates _) env2 (None (String)) (Erased) (SConst (VToken)) pty (None (Term)) coercible-id))
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

; Interns a literal (ASSUMPTIONS 51, 52, 60): a character is (MkChar (MkU8 n p)) over its code's numeral,
; transparent down to the opaque n; a string is its characters, holding no proof.
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
              (let (many env3) (many lt) (bind (predates _) env2 (None (String)) (Erased) (SConst (VToken))
                                          (TApp (TVar (prelude-id (predates _) env2 "Lt")) (Cons (Term) (TVar num) (Cons (Term) (TVar (prelude-id (predates _) env2 "u8-modulus")) (Nil (Term))))) (None (Term)) coercible-id))
              (let (many rule) (TApp (TVar (prelude-id (predates _) env3 "MkChar")) (Cons (Term) (TApp (TVar (prelude-id (predates _) env3 "MkU8")) (Cons (Term) (TVar num) (Cons (Term) (TVar lt) (Nil (Term))))) (Nil (Term)))))
              (let (many v) (VExt u8-adt (PU8 (nat-to-u8 (predates _) code))))
              (let (many env4) (many x) (bind (predates _) env3 (None (String)) (Many) (SConst v) (prelude-type (predates _) env3 "Char") (Some (Term) rule) coercible-id))
              (let (many env5) (env-set-literals (predates _) env4 (nm-set (predates _) (Bin) key x (env-literals (predates _) env4))))
              (env-push-lit (predates _) (env-push-trace (predates _) env5 (TrConst x v)) x (Some (Bin) np)))
            ((LString)
              (let (many v) (VExt str-adt (PStr (match many key (((String) s)) ((SNil) (SNil)) ((SCons q rest) rest)))))
              (let (many env2) (many x) (bind (predates _) env (None (String)) (Many) (SConst v) (prelude-type (predates _) env "String") (None (Term)) coercible-id))
              (let (many env3) (env-set-literals (predates _) env2 (nm-set (predates _) (Bin) key x (env-literals (predates _) env2))))
              (env-push-lit (predates _) (env-push-trace (predates _) env3 (TrConst x v)) x (None (Bin))))
            ((LName) env)))))))

(def-fns _
  (many intern-literals : (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r)
    (match many raw _
      ((RAtom lq s)
        (match many (classify (predates _) s) _
          ((LName) env)
          ((LNumeral) (intern (predates _) env s (LNumeral)))
          ((LChar) (intern (predates _) env s (LChar)))
          ((LString) env)))
      ((RString lq s) (intern (predates _) env (SCons #\x22 s) (LString)))
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
        ((LChar) (match many (lit-lookup (predates _) env n) _ ((Some b x) (values env x)) ((None b) (values (env-error (predates _) env (str-cat3 (predates _) "literal " n " outside a top-level form")) (BZ)))))
        ((LString) (values (env-error (predates _) env "internal: string as name") (BZ)))))))

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


; ---- Source telescopes (section 30)

(def-adts
  (SrcEntry : -> Type
    enum
    (many MkSrcEntry : (many (Bool) sub) (many (Maybe (Mult)) mult) (many (Maybe (SrcSg)) sg) (many (String) name) -> (SrcEntry)))
  (SrcSg : -> Type
    enum
    (many SrcTy : (many (Raw) r) -> (SrcSg))
    (many SrcIs : (many (Raw) r) -> (SrcSg))))

(def-fns _ $ many entries-of-names : (subterm many (List (Raw)) names) (many (Bool) sub) (many (Maybe (Mult)) mult) (many (Raw) ty) -> (many (List (SrcEntry)) r)
  (match many names _
    ((Nil a) (Nil (SrcEntry)))
    ((Cons a n rest) (Cons (SrcEntry) (MkSrcEntry sub mult (Some (SrcSg) (SrcTy ty)) (raw-name (predates _) n)) (entries-of-names (subterm _) rest sub mult ty)))))

(def-fns _ $ many parse-entry : (many (Env) env) (many (Raw) raw) -> (many (List (SrcEntry)) r)
  (let (many items0) (raw-items (predates _) raw))
  (let (many sub) (many items1)
    (match many items0 (((Bool) b) ((List (Raw)) l))
      ((Nil a) (values (BFalse) items0))
      ((Cons a t rest) (match many (is-mark (predates _) env t (MkSubterm)) (((Bool) b) ((List (Raw)) l)) ((BTrue) (values (BTrue) rest)) ((BFalse) (values (BFalse) items0))))))
  (let (many mult) (many items)
    (match many items1 (((Maybe (Mult)) m) ((List (Raw)) l))
      ((Nil a) (values (None (Mult)) items1))
      ((Cons a t rest) (match many (mult-of (predates _) env t) (((Maybe (Mult)) m) ((List (Raw)) l)) ((None b) (values (None (Mult)) items1)) ((Some b m) (values (Some (Mult) m) rest))))))
  (match many items _
    ((Nil a) (Nil (SrcEntry)))
    ((Cons a first rest)
      (match many rest _
        ((Nil b) (Cons (SrcEntry) (MkSrcEntry sub mult (None (SrcSg)) (raw-name (predates _) first)) (Nil (SrcEntry))))
        ((Cons b second rest2)
          (match many rest2 _
            ((Cons c third rest3)
              (match many (and (predates _) (is-mark (predates _) env second (MkIs)) (list-is-empty (predates _) (Raw) rest3)) _
                ((BTrue) (Cons (SrcEntry) (MkSrcEntry sub mult (Some (SrcSg) (SrcIs first)) (raw-name (predates _) third)) (Nil (SrcEntry))))
                ((BFalse) (entries-of-names (predates _) rest sub mult first))))
            ((Nil c) (entries-of-names (predates _) rest sub mult first))))))))

(def-fns _ $ many parse-entries : (subterm many (List (Raw)) rs) (many (Env) env) -> (many (List (SrcEntry)) r)
  (match many rs _
    ((Nil a) (Nil (SrcEntry)))
    ((Cons a r rest) (list-append (predates _) (SrcEntry) (parse-entry (predates _) env r) (parse-entries (subterm _) rest env)))))

(def-fns _ $ many split-arrow : (subterm many (List (Raw)) items) (many (Env) env) -> (many (List (Raw)) before) (many (List (Raw)) after)
  (match many items _
    ((Nil a) (values (Nil (Raw)) (Nil (Raw))))
    ((Cons a t rest)
      (match many (is-mark (predates _) env t (MkArrow)) _
        ((BTrue) (values (Nil (Raw)) rest))
        ((BFalse)
          (let (many before) (many after) (split-arrow (subterm _) rest env))
          (values (Cons (Raw) t before) after))))))

; Leading items that are lists headed by a multiplicity token are return entries or let binders (ASSUMPTIONS 11).
(def-fns _ $ many split-returns : (subterm many (List (Raw)) items) (many (Env) env) -> (many (List (Raw)) rets) (many (List (Raw)) body)
  (match many items _
    ((Nil a) (values (Nil (Raw)) (Nil (Raw))))
    ((Cons a t rest)
      (let (many headed) (match many (raw-items (predates _) t) (((Bool) b)) ((Nil b) (BFalse)) ((Cons b m r) (match many (mult-of (predates _) env m) (((Bool) x)) ((None c) (BFalse)) ((Some c mm) (BTrue))))))
      (match many headed _
        ((BFalse) (values (Nil (Raw)) items))
        ((BTrue)
          (let (many rets) (many body) (split-returns (subterm _) rest env))
          (values (Cons (Raw) t rets) body))))))

; Leading annotation tokens from the marks given, in any order; returns the flags for absurd/newtype and extern.
(def-fns _ $ many take-marks : (subterm many (List (Raw)) items) (many (Env) env) (many (MarkK) first) (many (MarkK) second) -> (many (Bool) has-first) (many (Bool) has-second) (many (List (Raw)) rest)
  (match many items _
    ((Nil a) (values (BFalse) (BFalse) items))
    ((Cons a t more)
      (match many (is-mark (predates _) env t first) _
        ((BTrue)
          (let (many f) (many s) (many rest) (take-marks (subterm _) more env first second))
          (values (BTrue) s rest))
        ((BFalse)
          (match many (is-mark (predates _) env t second) _
            ((BTrue)
              (let (many f) (many s) (many rest) (take-marks (subterm _) more env first second))
              (values f (BTrue) rest))
            ((BFalse) (values (BFalse) (BFalse) items))))))))


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
  (match many (list-nth (predates _) (Term) ts i) _ ((None a) (TErr "missing proof argument")) ((Some a t) t)))

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

(def-fns _ $ many fresh-id : (many (Env) env) -> (many (Env) r) (many (Bin) x)
  (let (many x) (bin-succ (predates _) (env-fresh (predates _) env)))
  (values (env-set-fresh (predates _) env x) x))

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
              (let (many env2) (many t) (fresh-id (predates _) env))
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

(def-fns _ $ many level-var : (many (Env) env) (many (Term) t) -> (many (Bin) x)
  (match many (canon-env (predates _) env t) _
    ((TVar x) x)
    ((TBound k) (BZ)) ((TApp h a) (BZ)) ((TFn l p r) (BZ)) ((TTyCtor p) (BZ)) ((TValCtor p r) (BZ)) ((TMatchable d ty c) (BZ)) ((TNewtype c) (BZ)) ((TErr m) (BZ))))

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
(def-fns _ $ many src-mults : (subterm many (List (SrcEntry)) es) -> (many (List (Mult)) r)
  (match many es _
    ((Nil a) (Nil (Mult)))
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry sub m sg n) (Cons (Mult) (match many m (((Mult) x)) ((None b) (Many)) ((Some b mm) mm)) (src-mults (subterm _) rest)))))))


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
(def-fns _ $ many prove-subterm : (many (Env) env) (many (Term) a) (many (Term) b) -> (many (Env) r) (many (Res) res)
  (let (many ca) (canon-env (predates _) env a))
  (let (many cb) (canon-env (predates _) env b))
  (let (many env2)
    (match many (is-strict-subterm (predates _) cb ca) (((Env) e))
      ((BTrue) env)
      ((BFalse) (env-error (predates _) env (str-cat3 (predates _) (show-t (predates _) env a) " is not a strict subterm of " (show-t (predates _) env b))))))
  (mint (predates _) env2 (proof-type (predates _) subterm-id (Cons (Term) (infer (predates _) a env2) (Cons (Term) a (Cons (Term) (infer (predates _) b env2) (Cons (Term) b (Nil (Term)))))))))

; prove-predates (section 8): the variable was in scope when the level was minted (ASSUMPTIONS 13).
(def-fns _ $ many prove-predates : (many (Env) env) (many (Bin) x0) (many (Bin) lvl) -> (many (Env) r) (many (Res) res)
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
(def-fns _ $ many expect-proof : (many (Env) env) (many (Bin) ctor) (many (Term) p) -> (many (Env) r) (many (List (Term)) args)
  (let (many ty) (canon-env (predates _) env (infer (predates _) p env)))
  (let (many found)
    (match many ty (((Maybe (List (Term))) r))
      ((TApp h args) (match many h (((Maybe (List (Term))) r)) ((TVar c) (match many (bin-eq (predates _) c ctor) (((Maybe (List (Term))) r)) ((BTrue) (Some (List (Term)) args)) ((BFalse) (None (List (Term))))))
                       ((TBound k) (None (List (Term)))) ((TApp h2 a2) (None (List (Term)))) ((TFn l pp rr) (None (List (Term)))) ((TTyCtor pp) (None (List (Term))))
                       ((TValCtor pp rr) (None (List (Term)))) ((TMatchable d t c) (None (List (Term)))) ((TNewtype c) (None (List (Term)))) ((TErr m) (None (List (Term))))))
      ((TVar x) (None (List (Term)))) ((TBound k) (None (List (Term)))) ((TFn l pp rr) (None (List (Term)))) ((TTyCtor pp) (None (List (Term))))
      ((TValCtor pp rr) (None (List (Term)))) ((TMatchable d t c) (None (List (Term)))) ((TNewtype c) (None (List (Term)))) ((TErr m) (None (List (Term))))))
  (match many found _
    ((Some a args) (values env args))
    ((None a) (values (env-error (predates _) env (str-cat3 (predates _) "expected a " (name-of (predates _) env ctor) (str-cat3 (predates _) " proof, got " (show-t (predates _) env p) (str-cat (predates _) " : " (show-t (predates _) env ty))))) (Nil (Term))))))

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

(def-fns _ $ many parse-entries-checked : (subterm many (List (Raw)) rs) (many (Env) env) -> (many (Env) r) (many (List (SrcEntry)) es)
  (match many rs _
    ((Nil a) (values env (Nil (SrcEntry))))
    ((Cons a r rest)
      (let (many env1) (many here)
        (match many (raw-atom (predates _) r) (((Env) e) ((List (SrcEntry)) l))
          ((Some b s) (values (env-error (predates _) env (str-cat (predates _) "expected a telescope entry, got " s)) (Nil (SrcEntry))))
          ((None b)
            (let (many es) (parse-entry (predates _) env r))
            (match many es (((Env) e) ((List (SrcEntry)) l))
              ((Nil c) (values (env-error (predates _) env (str-cat (predates _) "malformed telescope entry " (show-r (predates _) r))) es))
              ((Cons c x more) (values env es))))))
      (let (many env2) (many more) (parse-entries-checked (subterm _) rest env1))
      (values env2 (list-append (predates _) (SrcEntry) here more)))))

(def-fns _ $ many check-binder-mults : (subterm many (List (SrcEntry)) es) (many (Env) env) -> (many (Env) r)
  (match many es _
    ((Nil a) env)
    ((Cons a e rest)
      (match many e _
        ((MkSrcEntry sub m sg n)
          (match many m _
            ((Some b mm) (check-binder-mults (subterm _) rest env))
            ((None b) (check-binder-mults (subterm _) rest (env-error (predates _) env "let binder needs a multiplicity")))))))))

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

(def-fns _ $ many find-literal : (subterm many (List (Pair (Bin) (Maybe (Bin)))) lits) (many (Env) env) (many (Term) e) -> (many (Maybe (Maybe (Bin))) r)
  (match many lits _
    ((Nil a) (None (Maybe (Bin))))
    ((Cons a p rest)
      (match many p _
        ((MkPair s t x proof)
          (match many (equal-env (predates _) env (TVar x) e) _
            ((BTrue) (Some (Maybe (Bin)) proof))
            ((BFalse) (find-literal (subterm _) rest env e))))))))

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

(def-fns _ $ many match-parts : (many (List (Raw)) args) -> (many (Maybe (Pair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw)))))) r)
  (match many args _
    ((Nil a) (None (Pair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw)))))))
    ((Cons a m rest)
      (match many rest _
        ((Nil b) (None (Pair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw)))))))
        ((Cons b scrut rest2)
          (match many rest2 _
            ((Nil c) (None (Pair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw)))))))
            ((Cons c ann branches)
              (Some (Pair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw))))) (MkPair (Raw) (Pair (Raw) (Pair (Raw) (List (Raw)))) m (MkPair (Raw) (Pair (Raw) (List (Raw))) scrut (MkPair (Raw) (List (Raw)) ann branches)))))))))))

; A branch's kind (0 present, 1 refuted automatically, 2 absurd by proof), constructor, fields and body.
(def-adts $ BranchParts : -> Type
  enum
  (many MkBranchParts : (many (Nat) kind) (many (Raw) craw) (many (List (Raw)) fields) (many (List (Raw)) body) -> (BranchParts)))

(def-fns _ $ many pattern-parts : (many (Raw) pat) -> (many (Maybe (Pair (Raw) (List (Raw)))) r)
  (match many pat _
    ((RAtom lq s) (Some (Pair (Raw) (List (Raw))) (MkPair (Raw) (List (Raw)) pat (Nil (Raw)))))
    ((RString lq s) (None (Pair (Raw) (List (Raw)))))
    ((RList lq items)
      (match many items _
        ((Nil a) (None (Pair (Raw) (List (Raw)))))
        ((Cons a c fs) (match many (atoms-only (predates _) fs) _ ((BTrue) (Some (Pair (Raw) (List (Raw))) (MkPair (Raw) (List (Raw)) c fs))) ((BFalse) (None (Pair (Raw) (List (Raw)))))))))))

(def-fns _ $ many branch-parts : (many (Env) env) (many (Raw) braw) -> (many (Maybe (BranchParts)) r)
  (match many (raw-items (predates _) braw) _
    ((Nil a) (None (BranchParts)))
    ((Cons a first more)
      (match many (is-mark (predates _) env first (MkAbsurd)) _
        ((BFalse)
          (match many (pattern-parts (predates _) first) _
            ((None b) (None (BranchParts)))
            ((Some b pp) (match many pp _ ((MkPair s t c fs) (Some (BranchParts) (MkBranchParts 0 c fs more)))))))
        ((BTrue)
          (match many more _
            ((Nil b) (None (BranchParts)))
            ((Cons b pat body)
              (match many body _
                ((Nil c)
                  (match many (raw-atom (predates _) pat) _
                    ((Some d s) (Some (BranchParts) (MkBranchParts 1 pat (Nil (Raw)) (Nil (Raw)))))
                    ((None d) (None (BranchParts)))))
                ((Cons c x y)
                  (match many (pattern-parts (predates _) pat) _
                    ((None d) (None (BranchParts)))
                    ((Some d pp) (match many pp _ ((MkPair s t cc fs) (Some (BranchParts) (MkBranchParts 2 cc fs body)))))))))))))))

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


; ---- The elaborator proper: one block, bounded by a fuel that every call decrements

(def-adts $ Header : -> Type
  enum
  (many MkHeader : (many (String) name) (many (Mult) mult) (many (Bool) absurd) (many (Maybe (String)) impl) (many (Term) ty) (many (List (Raw)) body) -> (Header)))

(def-adts $ AdtHeader : -> Type
  enum
  (many MkAdtHeader : (many (String) name) (many (List (Raw)) params) (many (Disc) disc) (many (Bool) newtype) (many (Bool) extern) (many (List (Raw)) ctors) -> (AdtHeader)))

(def-adts $ RealBranch : -> Type
  enum
  (many MkRealBranch : (many (Bin) c) (many (List (Bin)) fids) (many (Code) code) -> (RealBranch)))

(def-fns _ $ many real-branches-code : (subterm many (List (RealBranch)) bs) (many (List (CShape)) ss) -> (many (List (Branch)) r)
  (match many bs _
    ((Nil a) (Nil (Branch)))
    ((Cons a b rest)
      (match many b _
        ((MkRealBranch c fids code) (Cons (Branch) (MkBranch (discriminant (predates _) ss c) fids code) (real-branches-code (subterm _) rest ss)))))))

(def-fns _ $ many bind-headers : (subterm many (List (Header)) hs) (many (Env) env) -> (many (Env) r) (many (List (Bin)) ids)
  (match many hs _
    ((Nil a) (values env (Nil (Bin))))
    ((Cons a h rest)
      (match many h _
        ((MkHeader name mult isabs impl ty body)
          (let (many env2) (many x) (bind (predates _) env (Some (String) name) mult (SDyn) ty (None (Term)) coercible-id))
          (let (many env3) (many ids) (bind-headers (subterm _) rest env2))
          (values env3 (Cons (Bin) x ids)))))))

(def-fns _ $ many bind-adt-headers : (subterm many (List (AdtHeader)) hs) (many (Env) env) (many (List (Term)) tys) -> (many (Env) r) (many (List (Bin)) ids)
  (match many hs _
    ((Nil a) (values env (Nil (Bin))))
    ((Cons a h rest)
      (match many h _
        ((MkAdtHeader name params disc nt ext ctors)
          (let (many ty) (many tys2) (match many tys (((Term) t) ((List (Term)) r)) ((Nil b) (values (TErr "missing type") tys)) ((Cons b t r) (values t r))))
          (let (many st) (match many (env-run-pos (predates _) env) (((State) s)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn))))
          (let (many env2) (many x) (bind (predates _) env (Some (String) name) (Erased) st ty (None (Term)) coercible-id))
          (let (many env3) (many ids) (bind-adt-headers (subterm _) rest env2 tys2))
          (values env3 (Cons (Bin) x ids)))))))

(def-fns _ $ many many-fns : (subterm many (List (Pair (Bin) (Func))) fns) (many (Env) env) -> (many (List (Pair (Bin) (Func))) r)
  (match many fns _
    ((Nil a) (Nil (Pair (Bin) (Func))))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (match many (entry-mult-of (predates _) env id) _
            ((Many) (Cons (Pair (Bin) (Func)) p (many-fns (subterm _) rest env)))
            ((Erased) (many-fns (subterm _) rest env))))))))

(def-fns _ $ many set-fn-states : (subterm many (List (Pair (Bin) (Func))) fns) (many (Env) env) (many (IdMap (Value)) values) -> (many (Env) r)
  (match many fns _
    ((Nil a) env)
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (let (many v) (match many (idmap-get (predates _) (Value) id values) (((Value) v)) ((None b) (VError "closure missing")) ((Some b v) v)))
          (set-fn-states (subterm _) rest (set-state (predates _) env id (SConst v)) values))))))

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

(def-fns _ $ many resolve-sub : (subterm many (Nat) fuel) (many (IdMap (Bin)) sub) (many (Bin) x) -> (many (Bin) r)
  (match many fuel _
    ((Zero) x)
    ((Succ k)
      (match many (idmap-get (predates _) (Bin) x sub) _
        ((None a) x)
        ((Some a y) (resolve-sub (subterm _) k sub y))))))

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
      ((CVar x) (CVar (resolve-sub (predates _) big-fuel sub x)))
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
; the decreasing argument, whose position it carries.
(def-adts $ Ann : -> Type
  enum
  (many AnnNone : -> (Ann))
  (many AnnPredates : (many (Raw) p) -> (Ann))
  (many AnnSubterm : (many (Nat) i) (many (Raw) p) -> (Ann)))

(def-fns _ $ many ann-of : (many (Env) env) (many (Raw) arg) (many (Nat) i) -> (many (Ann) r)
  (match many (raw-items (predates _) arg) _
    ((Nil b) (AnnNone))
    ((Cons b k krest)
      (match many krest _
        ((Nil c) (AnnNone))
        ((Cons c p prest)
          (match many prest _
            ((Cons d q qrest) (AnnNone))
            ((Nil d)
              (match many (and (predates _) (is-mark (predates _) env k (MkPredates)) (nat-is-zero (predates _) i)) _
                ((BTrue) (AnnPredates p))
                ((BFalse) (match many (is-mark (predates _) env k (MkSubterm)) _ ((BTrue) (AnnSubterm i p)) ((BFalse) (AnnNone))))))))))))

; The first annotation and the arguments without it; a second annotation stays an argument, as in lib/elab.ml.
(def-fns _ $ many split-annotation : (subterm many (List (Raw)) args) (many (Env) env) (many (Nat) i) -> (many (Ann) ann) (many (List (Raw)) rest)
  (match many args _
    ((Nil a) (values (AnnNone) (Nil (Raw))))
    ((Cons a arg more)
      (match many (ann-of (predates _) env arg i) _
        ((AnnNone)
          (let (many ann) (many rest) (split-annotation (subterm _) more env (Succ i)))
          (values ann (Cons (Raw) arg rest)))
        ((AnnPredates p) (values (AnnPredates p) more))
        ((AnnSubterm j p) (values (AnnSubterm j p) more))))))

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
(def-fns _ $ many check-arity : (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) -> (many (Env) r)
  (let (many n) (list-length (predates _) (Entry) tele))
  (let (many m) (list-length (predates _) (Raw) args))
  (match many (nat-eq (predates _) n m) _
    ((BTrue) env)
    ((BFalse) (count-error (predates _) env " arguments" n m))))

(let (many elab-fuel) 100000)

(def-fns _
  ; An expression of the given size and erasures (sections 16, 20); [tele] is the telescope a bare _ reuses.
  (many elab-expr : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Raw) raw) (many (Maybe (List (Entry))) tele) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values (env-error (predates _) env "out of fuel") (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many env2) (many ress) (many code) (elab-form (subterm _) k (env-at (predates _) env (raw-line (predates _) raw)) expect raw tele cc))
        (let (many n) (list-length (predates _) (Mult) expect))
        (let (many m) (list-length (predates _) (Res) ress))
        (match many (nat-eq (predates _) n m) _
          ((BFalse) (values (env-back (predates _) env (count-error (predates _) env2 " values" n m)) ress code))
          ((BTrue) (values (env-back (predates _) env (erased-in-many (predates _) expect ress env2)) ress code))))))

  (many elab-form : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Raw) raw) (many (Maybe (List (Entry))) tele) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values (env-error (predates _) env "out of fuel") (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (match many raw _
          ((RAtom lq n)
            (let (many env2) (many x) (var (predates _) env n))
            (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
          ((RString lq s)
            (let (many env2) (many x) (var-of-raw (predates _) env raw "a name"))
            (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
          ((RList lq items)
            (match many items _
              ((Nil a) (values (env-error (predates _) env "empty form") (Nil (Res)) (CError "empty form")))
              ((Cons a head args)
                (match many (special-of (predates _) env head) _
                  ((Some b sp) (elab-special (subterm _) k env expect sp args tele))
                  ((None b)
                    (let (many env2) (many h) (many hcode)
                      (match many head (((Env) e) ((Res) r) ((Code) c))
                        ((RAtom lq n) (let (many env2) (many x) (var (predates _) env n)) (values env2 (res-of (predates _) env2 x) (CVar x)))
                        ((RString lq s) (let (many env2) (many x) (var-of-raw (predates _) env head "a name")) (values env2 (res-of (predates _) env2 x) (CVar x)))
                        ((RList lq hitems)
                          (let (many env2) (many r) (many hcode) (elab-expr1 (subterm _) k env pos head))
                          (values env2 r hcode))))
                    (match many (canon-env (predates _) env2 (res-ty (predates _) h)) _
                      ((TTyCtor ttele)
                        (let (many env3) (match many pos (((Env) e)) ((Many) (env-error (predates _) env2 "type constructor application in a non-erased position")) ((Erased) env2)))
                        (let (many env4) (many acc) (elab-term-args (subterm _) k (check-arity (predates _) env3 ttele args) ttele args (Nil (Term))))
                        (values env4 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) type-term (Erased)) (Nil (Res))) (CErased)))
                      ((TValCtor ctele ret)
                        (let (many env3)
                          (match many (and (predates _) (mult-is-many (predates _) pos) (not (predates _) (mult-is-many (predates _) (res-erasure (predates _) h)))) (((Env) e))
                            ((BTrue) (env-error (predates _) env2 (str-cat3 (predates _) "erased constructor " (show-t (predates _) env2 (res-term (predates _) h)) " in a non-erased position")))
                            ((BFalse) env2)))
                        (let (many env4) (many acc) (many codes) (check-args (subterm _) k (check-arity (predates _) env3 ctele args) ctele args pos (Nil (Term)) (Nil (Code))))
                        (let (many code) (match many pos (((Code) c)) ((Erased) (CErased)) ((Many) (CApp hcode codes (CCCtor)))))
                        (values env4 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) (instantiate (predates _) acc ret) pos) (Nil (Res))) code))
                      ((TFn lv params rets) (elab-call (subterm _) k env2 expect h hcode lv params rets args cc))
                      ((TVar x) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                      ((TBound j) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                      ((TApp h2 a2) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                      ((TMatchable d t c) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                      ((TNewtype c) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError "not applicable")))
                      ((TErr m) (values (env-error (predates _) env2 (not-applicable (predates _) env2 h)) (Nil (Res)) (CError m)))))))))))))

  (many elab-expr1 : (subterm many (Nat) fuel) (many (Env) env) (many (Mult) mult) (many (Raw) raw) -> (many (Env) r) (many (Res) res) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (MkRes (TErr "out of fuel") (TErr "out of fuel") (Erased)) (CError "out of fuel")))
      ((Succ k)
        (let (many env2) (many ress) (many code) (elab-expr (subterm _) k env (Cons (Mult) mult (Nil (Mult))) raw (None (List (Entry))) (CCPlain)))
        (values env2 (first-res (predates _) ress) code))))

  ; Arguments against a telescope, each at the position's multiplicity and checked against its entry
  ; (section 20); returns the terms innermost first and the code of the many ones in order.
  (many check-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (Mult) pos) (many (List (Term)) acc) (many (List (Code)) codes) ->
      (many (Env) r) (many (List (Term)) acc2) (many (List (Code)) codes2)
    (match many fuel _
      ((Zero) (values env acc (Nil (Code))))
      ((Succ k)
        (match many tele _
          ((Nil a)
            (match many args _
              ((Nil b) (values env acc (list-rev (predates _) (Code) codes)))
              ((Cons b x more) (values (env-error (predates _) env (str-cat (predates _) "expected fewer arguments, got " (nat-str (predates _) (list-length (predates _) (Raw) args)))) acc (list-rev (predates _) (Code) codes)))))
          ((Cons a e rest)
            (match many args _
              ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "expected " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) tele)) " more arguments, got 0"))) acc (list-rev (predates _) (Code) codes)))
              ((Cons b arg arest)
                (let (many m) (entry-mult (predates _) e))
                (let (many env2) (many r) (many code) (elab-expr1 (subterm _) k env (under (predates _) pos m) arg))
                (let (many sg) (match many (entry-sg (predates _) e) (((Sg) s)) ((SgTy t) (SgTy (instantiate (predates _) acc t))) ((SgIs t) (SgIs (instantiate (predates _) acc t)))))
                (let (many env3) (check-sg (predates _) env2 sg r))
                (check-args (subterm _) k env3 rest arest pos (Cons (Term) (res-term (predates _) r) acc)
                  (match many m (((List (Code)) l)) ((Many) (Cons (Code) code codes)) ((Erased) codes))))))))))

  (many elab-term-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (List (Term)) acc) -> (many (Env) r) (many (List (Term)) acc2)
    (match many fuel _
      ((Zero) (values env acc))
      ((Succ k)
        (match many tele _
          ((Nil a)
            (match many args _
              ((Nil b) (values env acc))
              ((Cons b x more) (values (env-error (predates _) env (str-cat (predates _) "expected fewer arguments, got " (nat-str (predates _) (list-length (predates _) (Raw) args)))) acc))))
          ((Cons a e rest)
            (match many args _
              ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "expected " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) tele)) " more arguments, got 0"))) acc))
              ((Cons b arg arest)
                (let (many env2) (many t) (elab-term (subterm _) k env arg))
                (let (many sg) (match many (entry-sg (predates _) e) (((Sg) s)) ((SgTy ty) (SgTy (instantiate (predates _) acc ty))) ((SgIs ty) (SgIs (instantiate (predates _) acc ty)))))
                (let (many env3) (check-sg (predates _) env2 sg (term-res (predates _) env2 t)))
                (elab-term-args (subterm _) k env3 rest arest (Cons (Term) t acc)))))))))

  ; A function call (section 9): a lower-level call carries a Predates proof about the callee's level, a
  ; same-level call a Subterm proof for its decreasing argument; the top level carries neither (section 24).
  (many elab-call : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Res) callee) (many (Code) hcode) (many (Term) lv) (many (List (Entry)) params) (many (List (Entry)) rets) (many (List (Raw)) rawargs) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (let (many env1)
          (match many (and (predates _) (mult-is-many (predates _) pos) (not (predates _) (mult-is-many (predates _) (res-erasure (predates _) callee)))) (((Env) e))
            ((BTrue) (env-error (predates _) env (str-cat3 (predates _) "erased function " (show-t (predates _) env (res-term (predates _) callee)) " called in a non-erased position")))
            ((BFalse) env)))
        (let (many ann) (many args) (split-annotation (predates _) rawargs env1 0))
        (let (many env2) (many acc) (many codes) (check-args (subterm _) k (check-arity (predates _) env1 params args) params args pos (Nil (Term)) (Nil (Code))))
        (let (many arg-terms) (list-rev (predates _) (Term) acc))
        (let (many env3) (check-call-proof (subterm _) k env2 callee lv params arg-terms ann))
        (let (many rmults) (tele-mults (predates _) rets))
        (let (many env4) (many ids) (open-tele (predates _) rets env3 (Some (List (Maybe (String))) (anon-names (predates _) rets)) (Some (List (Mult)) (under-list (predates _) rmults pos)) (None (List (State))) acc))
        (let (many call) (CApp hcode codes cc))
        (let (many env5) (many code)
          (match many pos (((Env) e) ((Code) c))
            ((Erased) (values env4 (CErased)))
            ((Many)
              (match many (and (predates _) (nat-eq (predates _) (list-length (predates _) (Mult) expect) (list-length (predates _) (Entry) rets)) (needs-projection (predates _) expect rmults)) (((Env) e) ((Code) c))
                ((BFalse) (values env4 call))
                ((BTrue)
                  (let (many env5) (many bound) (many kept) (projection (predates _) expect rmults env4))
                  (values env5 (CLet bound call (CValues kept))))))))
        (values env5 (ress-of (predates _) ids env5) code))))

  ; The call-site proof (section 9), read against the current level and enclosing subterm parameters.
  (many check-call-proof : (subterm many (Nat) fuel) (many (Env) env) (many (Res) callee) (many (Term) lv) (many (List (Entry)) params) (many (List (Term)) args) (many (Ann) ann) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (match many (env-level (predates _) env) _
          ((None a)
            (match many ann _
              ((AnnNone) env)
              ((AnnPredates p) (env-error (predates _) env "the top level calls without proofs; drop the decrease annotation (section 24)"))
              ((AnnSubterm i p) (env-error (predates _) env "the top level calls without proofs; drop the decrease annotation (section 24)"))))
          ((Some a cur)
            (let (many same) (equal-env (predates _) env lv (TVar cur)))
            (let (many need)
              (match many ann (((Env) e))
                ((AnnNone) (env-error (predates _) env (call-needs (predates _) env callee same)))
                ((AnnSubterm i p)
                  (match many same (((Env) e))
                    ((BFalse) (env-error (predates _) env (call-needs (predates _) env callee same)))
                    ((BTrue)
                      (let (many positions) (subterm-indices (predates _) params 0))
                      (match many (index-of-nat (predates _) positions i 0) (((Env) e))
                        ((None b) (env-error (predates _) env (str-cat3 (predates _) "argument " (nat-str (predates _) i) " is not a subterm parameter")))
                        ((Some b kk)
                          (let (many env2) (check-earlier (predates _) positions env args 0 kk))
                          (match many (list-nth (predates _) (Bin) (env-subterms (predates _) env2) kk) (((Env) e))
                            ((None c) (env-error (predates _) env2 (str-cat3 (predates _) "the enclosing function has no subterm parameter at position " (nat-str (predates _) kk) "")))
                            ((Some c counterpart)
                              (let (many arg) (nth-term (predates _) args i))
                              (let (many env3) (many pterm)
                                (match many (is-underscore (predates _) p) (((Env) e) ((Term) t))
                                  ((BTrue) (let (many env3) (many pr) (prove-subterm (predates _) env2 arg (TVar counterpart))) (values env3 (res-term (predates _) pr)))
                                  ((BFalse) (elab-erased (subterm _) k env2 p))))
                              (let (many env4) (many pa) (expect-proof (predates _) env3 subterm-id pterm))
                              (let (many env5) (check (predates _) env4 "value" (nth-term (predates _) pa 1) arg))
                              (check (predates _) env5 "value" (nth-term (predates _) pa 3) (TVar counterpart)))))))))
                ((AnnPredates p)
                  (match many same (((Env) e))
                    ((BTrue) (env-error (predates _) env (call-needs (predates _) env callee same)))
                    ((BFalse)
                      (let (many env2) (many pterm)
                        (match many (is-underscore (predates _) p) (((Env) e) ((Term) t))
                          ((BTrue)
                            (match many (canon-env (predates _) env lv) (((Env) e) ((Term) t))
                              ((TVar m) (let (many env2) (many pr) (prove-predates (predates _) env m cur)) (values env2 (res-term (predates _) pr)))
                              ((TBound j) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TApp h as) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TFn l ps rs) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TTyCtor ps) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TValCtor ps rs) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TMatchable d t c) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TNewtype c) (values (env-error (predates _) env (str-cat (predates _) (show-t (predates _) env lv) " is not a variable")) (TErr "level")))
                              ((TErr m) (values (env-error (predates _) env m) (TErr m)))))
                          ((BFalse) (elab-erased (subterm _) k env p))))
                      (let (many env3) (many pa) (expect-proof (predates _) env2 predates-id pterm))
                      (let (many env4) (check (predates _) env3 "value" (nth-term (predates _) pa 2) (TVar cur)))
                      (match many (equal-env (predates _) env4 (nth-term (predates _) pa 1) lv) (((Env) e))
                        ((BTrue) env4)
                        ((BFalse) (env-error (predates _) env4 (str-cat3 (predates _) (show-t (predates _) env4 pterm) " : " (str-cat3 (predates _) (show-t (predates _) env4 (infer (predates _) pterm env4)) " does not relate the callee's level " (show-t (predates _) env4 lv)))))))))))
            need)))))

  ; Grammar expressions (section 5): variables, constructor applications and type formers.
  (many elab-term : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many t) (elab-term1 (subterm _) k (env-at (predates _) env (raw-line (predates _) raw)) raw))
        (values (env-back (predates _) env env2) t))))

  (many elab-term1 : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (match many raw _
          ((RAtom lq n) (let (many env2) (many x) (var (predates _) env n)) (values env2 (TVar x)))
          ((RString lq s) (let (many env2) (many x) (var-of-raw (predates _) env raw "a name")) (values env2 (TVar x)))
          ((RList lq items)
            (match many items _
              ((Nil a) (values (env-error (predates _) env "empty form") (TErr "empty form")))
              ((Cons a head args)
                (match many (special-of (predates _) env head) _
                  ((Some b sp) (elab-type-form (subterm _) k env sp args))
                  ((None b)
                    (let (many env2) (many x) (var-of-raw (predates _) env head "a constructor"))
                    (let (many h) (TVar x))
                    (match many (canon-env (predates _) env2 (infer (predates _) h env2)) _
                      ((TTyCtor ttele)
                        (let (many env3) (many acc) (elab-term-args (subterm _) k (check-arity (predates _) env2 ttele args) ttele args (Nil (Term))))
                        (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                      ((TValCtor ctele ret)
                        (let (many env3) (many acc) (elab-term-args (subterm _) k (check-arity (predates _) env2 ctele args) ctele args (Nil (Term))))
                        (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                      ((TVar y) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                      ((TBound j) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                      ((TApp h2 a2) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                      ((TFn l p r) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "function in type")))
                      ((TMatchable d t c) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                      ((TNewtype c) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr "not applicable")))
                      ((TErr m) (values (env-error (predates _) env2 (cannot-apply-in-type (predates _) env2 h)) (TErr m)))))))))))))

  ; A type: a grammar expression whose type is Type.
  (many elab-type : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many t) (elab-term (subterm _) k (env-at (predates _) env (raw-line (predates _) raw)) raw))
        (values (env-back (predates _) env (check (predates _) env2 "type" (infer (predates _) t env2) type-term)) t))))

  (many elab-type-form : (subterm many (Nat) fuel) (many (Env) env) (many (Sp) sp) (many (List (Raw)) args) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (match many sp _
          ((SpFormer fo)
            (match many fo _
              ((FoFn)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed Fn") (TErr "malformed Fn")))
                  ((Cons a lvraw rest)
                    (let (many env2) (many lv) (elab-term (subterm _) k env lvraw))
                    (let (many env3) (check (predates _) env2 "type" (infer (predates _) lv env2) level-term))
                    (let (many ps) (many rs) (split-arrow (predates _) rest env3))
                    (elab-fn-type (subterm _) k env3 lv ps rs))))
              ((FoTyCtor)
                (let (many ps) (many ret) (split-arrow (predates _) args env))
                (elab-tyctor (subterm _) k env ps ret))
              ((FoValCtor)
                (let (many env2) (many tele) (many ret) (many t) (elab-valctor (subterm _) k env args))
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
                        (let (many env4) (many mcs) (elab-mctors (subterm _) k env3 cs))
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

  (many elab-mctors : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) cs) -> (many (Env) r) (many (List (MCtor)) mcs)
    (match many fuel _
      ((Zero) (values env (Nil (MCtor))))
      ((Succ k)
        (match many cs _
          ((Nil a) (values env (Nil (MCtor))))
          ((Cons a c rest)
            (let (many env1) (many m) (many craw)
              (match many (raw-items (predates _) c) (((Env) e) ((Mult) m) ((Raw) r))
                ((Nil b) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) c))
                ((Cons b mraw more)
                  (match many more (((Env) e) ((Mult) m) ((Raw) r))
                    ((Nil d) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) c))
                    ((Cons d cr more2)
                      (match many more2 (((Env) e) ((Mult) m) ((Raw) r))
                        ((Cons f x y) (values (env-error (predates _) env "expected (multiplicity Constructor)") (Many) cr))
                        ((Nil f)
                          (match many (mult-of (predates _) env mraw) (((Env) e) ((Mult) m) ((Raw) r))
                            ((None g) (values (env-error (predates _) env (str-cat (predates _) "expected a multiplicity, got " (show-r (predates _) mraw))) (Many) cr))
                            ((Some g mm) (values env mm cr))))))))))
            (let (many env2) (many cid) (ctor-var (predates _) env1 craw))
            (let (many env3) (many mcs) (elab-mctors (subterm _) k env2 rest))
            (values env3 (Cons (MCtor) (MkMCtor m (TVar cid)) mcs)))))))

  (many elab-fn-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) lv) (many (List (Raw)) ps) (many (List (Raw)) rs) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many ids) (many params) (elab-tele (subterm _) k env ps (MMDeclared) (Nil (Term)) (BTrue)))
        (let (many env3) (many ids2) (many rets) (elab-tele (subterm _) k env2 rs (MMDeclared) (tvars-rev (predates _) ids (Nil (Term))) (BFalse)))
        (values (env-discard (predates _) env env3) (TFn lv params rets)))))

  (many elab-tyctor : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) ps) (many (List (Raw)) ret) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many ids) (many tele) (elab-tele (subterm _) k env ps (MMErased) (Nil (Term)) (BFalse)))
        (let (many env3)
          (match many ret (((Env) e))
            ((Cons a r more)
              (match many more (((Env) e))
                ((Nil b) (let (many env3) (many t) (elab-term (subterm _) k env2 r)) (check (predates _) env3 "value" t type-term))
                ((Cons b x y) (env-error (predates _) env2 "TyCtor returns Type"))))
            ((Nil a) (env-error (predates _) env2 "TyCtor returns Type"))))
        (values (env-discard (predates _) env env3) (TTyCtor tele)))))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type; the return is an application of a type constructor in scope (ASSUMPTIONS 70, 80).
  (many elab-valctor : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) items) -> (many (Env) r) (many (List (Entry)) tele) (many (Term) ret) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (Nil (Entry)) (TErr "out of fuel") (TErr "out of fuel")))
      ((Succ k)
        (let (many ps) (many rets) (split-arrow (predates _) items env))
        (let (many env2) (many ids) (many tele) (elab-tele (subterm _) k env ps (MMDeclared) (Nil (Term)) (BFalse)))
        (let (many env3) (many ret)
          (match many rets (((Env) e) ((Term) t))
            ((Nil a) (values (env-error (predates _) env2 "a constructor returns one type") (TErr "no return")))
            ((Cons a r more)
              (match many more (((Env) e) ((Term) t))
                ((Nil b) (elab-type (subterm _) k env2 r))
                ((Cons b x y) (values (env-error (predates _) env2 "a constructor returns one type") (TErr "no return")))))))
        (let (many ok)
          (match many (canon-env (predates _) env3 ret) (((Bool) b))
            ((TApp h as)
              (match many h (((Bool) b))
                ((TVar t) (and (predates _) (not (predates _) (list-mem-bin (predates _) ids t))
                             (match many (type-of (predates _) env3 t) (((Bool) b)) ((TTyCtor p) (BTrue)) ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse))
                               ((TFn l p r) (BFalse)) ((TValCtor p r) (BFalse)) ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse)))))
                ((TBound j) (BFalse)) ((TApp h2 a2) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
                ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
            ((TVar y) (BFalse)) ((TBound j) (BFalse)) ((TFn l p r) (BFalse)) ((TTyCtor p) (BFalse)) ((TValCtor p r) (BFalse))
            ((TMatchable d ty c) (BFalse)) ((TNewtype c) (BFalse)) ((TErr m) (BFalse))))
        (let (many env4)
          (match many ok (((Env) e))
            ((BTrue) env3)
            ((BFalse) (env-error (predates _) env3 (str-cat (predates _) "a constructor returns an application of a type constructor in scope, not " (show-t (predates _) env3 ret))))))
        (values env4 tele ret (TValCtor tele (abstract (predates _) (list-rev (predates _) (Bin) ids) ret))))))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 30).
  ; [ids]: binders already in force, innermost first.
  (many elab-tele : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) entries) (many (MultsMode) mode) (many (List (Term)) ids) (many (Bool) subterm-ok) -> (many (Env) r) (many (List (Bin)) bound) (many (List (Entry)) tele)
    (match many fuel _
      ((Zero) (values env (Nil (Bin)) (Nil (Entry))))
      ((Succ k)
        (let (many env2) (many entries2) (parse-entries-checked (predates _) entries env))
        (elab-src-entries (subterm _) k env2 entries2 mode ids (Nil (Bin)) subterm-ok))))

  (many elab-src-entries : (subterm many (Nat) fuel) (many (Env) env) (many (List (SrcEntry)) entries) (many (MultsMode) mode) (many (List (Term)) ids) (many (List (Bin)) bound) (many (Bool) subterm-ok) -> (many (Env) r) (many (List (Bin)) bound2) (many (List (Entry)) tele)
    (match many fuel _
      ((Zero) (values env bound (Nil (Entry))))
      ((Succ k)
        (match many entries _
          ((Nil a) (values env (list-rev (predates _) (Bin) bound) (Nil (Entry))))
          ((Cons a e rest)
            (match many e _
              ((MkSrcEntry sub smult ssg name)
                (let (many env0)
                  (match many (and (predates _) sub (not (predates _) subterm-ok)) (((Env) e))
                    ((BTrue) (env-error (predates _) env "subterm is not allowed here"))
                    ((BFalse) env)))
                (let (many env1) (many mult) (many mode2)
                  (match many mode (((Env) e) ((Mult) m) ((MultsMode) md))
                    ((MMDeclared) (match many smult (((Env) e) ((Mult) m) ((MultsMode) md)) ((None b) (values (env-error (predates _) env0 (str-cat3 (predates _) "entry " name " needs a multiplicity")) (Many) mode)) ((Some b m) (values env0 m mode))))
                    ((MMErased) (match many smult (((Env) e) ((Mult) m) ((MultsMode) md)) ((None b) (values env0 (Erased) mode)) ((Some b m) (values (env-error (predates _) env0 "these entries carry no multiplicity") (Erased) mode))))
                    ((MMExpect ms)
                      (let (many env0b) (match many smult (((Env) e)) ((None b) env0) ((Some b m) (env-error (predates _) env0 "a match annotation carries no multiplicities"))))
                      (match many ms (((Env) e) ((Mult) m) ((MultsMode) md)) ((Nil b) (values env0b (Erased) mode)) ((Cons b m more) (values env0b m (MMExpect more)))))))
                (let (many env2) (many sg)
                  (match many ssg (((Env) e) ((Sg) s))
                    ((None b) (values (env-error (predates _) env1 (str-cat3 (predates _) "entry " name " needs a type or an is clause")) (SgTy (TErr "no type"))))
                    ((Some b s)
                      (match many s (((Env) e) ((Sg) s))
                        ((SrcTy r) (let (many env2) (many t) (elab-type (subterm _) k env1 r)) (values env2 (SgTy t)))
                        ((SrcIs r) (let (many env2) (many t) (elab-term (subterm _) k env1 r)) (values env2 (SgIs t)))))))
                (let (many ty) (many rule) (fact-of (predates _) env2 sg))
                (let (many nm) (name-or-anon (predates _) name))
                (let (many env3) (many x) (bind (predates _) env2 nm mult (SDyn) ty rule coercible-id))
                (let (many entry) (MkEntry nm sub mult (abstract-sg (predates _) (bin-ids-of (predates _) ids) sg)))
                (let (many env4) (many bound2) (many tele) (elab-src-entries (subterm _) k env3 rest mode2 (Cons (Term) (TVar x) ids) (Cons (Bin) x bound) subterm-ok))
                (values env4 bound2 (Cons (Entry) entry tele)))))))))

  ; A body: statements then the final expression (section 16).
  (many elab-body : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) items) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (match many items _
          ((Nil a) (values (env-error (predates _) env "a body needs a final expression") (Nil (Res)) (CError "empty body")))
          ((Cons a item rest)
            (match many rest _
              ((Nil b) (elab-expr (subterm _) k env expect item tele (CCPlain)))
              ((Cons b item2 rest2)
                (let (many env2) (many sc) (elab-stmt (subterm _) k env item))
                (let (many env3) (many ress) (many code) (elab-body (subterm _) k env2 expect rest tele))
                (values env3 ress (wrap-stmt (predates _) sc code)))))))))

  ; An absurd body (sections 12, 37): erased, producing one value of an empty type.
  (many elab-absurd : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) body) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (let (many env2) (many ress) (many code) (elab-body (subterm _) k env (Cons (Mult) (Erased) (Nil (Mult))) body (None (List (Entry)))))
        (check-empty (predates _) env2 (res-ty (predates _) (first-res (predates _) ress))))))

  (many elab-stmt : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many env2) (many sc) (elab-stmt1 (subterm _) k (env-at (predates _) env (raw-line (predates _) raw)) raw))
        (values (env-back (predates _) env env2) sc))))

  (many elab-stmt1 : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many items) (raw-items (predates _) raw))
        (match many (stmt-of (predates _) env raw) _
          ((None b) (values (env-error (predates _) env (str-cat (predates _) (show-r (predates _) raw) " is not a statement")) (SNone)))
          ((Some b st)
            (let (many args) (match many items (((List (Raw)) l)) ((Nil c) (Nil (Raw))) ((Cons c head args) args)))
            (match many st _
              ((StLet) (elab-let (subterm _) k env args))
              ((StDefLvl)
                (match many args _
                  ((Nil c) (values (env-error (predates _) env "def-lvl needs a name") (SNone)))
                  ((Cons c n more)
                    (let (many env2) (many x) (mint-level (predates _) env (name-or-anon (predates _) (raw-name (predates _) n))))
                    (values env2 (SNone)))))
              ((StDefFns) (elab-def-fns (subterm _) k env args))
              ((StDefAdts) (elab-def-adts (subterm _) k env args))
              ((StComptimeMatch) (elab-comptime-match (subterm _) k env args))))))))


  ; let (section 9): binders, then the right-hand side; run at once in run position (section 34); an
  ; annotation is a checked redundancy.
  (many elab-let : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many braws) (many rhs) (split-returns (predates _) args env))
        (let (many env0) (many binders) (parse-entries-checked (predates _) braws env))
        (let (many env1) (check-binder-mults (predates _) binders env0))
        (let (many expect) (src-mults (predates _) binders))
        (let (many inner) (many ress) (many code) (elab-body (subterm _) k env1 expect rhs (None (List (Entry)))))
        (let (many run) (env-run-pos (predates _) env1))
        (let (many vals)
          (match many (and (predates _) run (and (predates _) (mult-is-many (predates _) (pos-of (predates _) expect)) (list-is-empty (predates _) (String) (env-errors (predates _) inner)))) (((List (Value)) vs))
            ((BTrue) (run-code (predates _) inner code))
            ((BFalse) (Nil (Value)))))
        (let (many env2) (many ids) (bind-let (subterm _) k (env-restore (predates _) env1 inner) binders ress (spread (predates _) expect vals) run (Nil (Bin))))
        (let (many many-ids) (non-erased (predates _) ids env2))
        (match many (or (predates _) run (list-is-empty (predates _) (Bin) many-ids)) _
          ((BTrue) (values env2 (SNone)))
          ((BFalse) (values env2 (SLet many-ids code)))))))

  (many bind-let : (subterm many (Nat) fuel) (many (Env) env) (many (List (SrcEntry)) binders) (many (List (Res)) ress) (many (List (Value)) vals) (many (Bool) run) (many (List (Bin)) acc) -> (many (Env) r) (many (List (Bin)) ids)
    (match many fuel _
      ((Zero) (values env (list-rev (predates _) (Bin) acc)))
      ((Succ k)
        (match many binders _
          ((Nil a) (values env (list-rev (predates _) (Bin) acc)))
          ((Cons a b brest)
            (match many b _
              ((MkSrcEntry sub smult ssg name)
                (let (many r) (many rrest) (match many ress (((Res) r) ((List (Res)) rs)) ((Nil c) (values (MkRes (TErr "missing value") (TErr "missing value") (Erased)) ress)) ((Cons c r rs) (values r rs))))
                (let (many v) (many vrest) (match many vals (((Value) v) ((List (Value)) vs)) ((Nil c) (values (VToken) vals)) ((Cons c v vs) (values v vs))))
                (let (many mult) (match many smult (((Mult) m)) ((None c) (Many)) ((Some c m) m)))
                (let (many env1)
                  (match many ssg (((Env) e))
                    ((None c) env)
                    ((Some c s)
                      (match many s (((Env) e))
                        ((SrcTy t) (let (many env1) (many ty) (elab-type (subterm _) k env t)) (check-sg (predates _) env1 (SgTy ty) r))
                        ((SrcIs t) (let (many env1) (many ty) (elab-term (subterm _) k env t)) (check-sg (predates _) env1 (SgIs ty) r))))))
                (let (many st)
                  (match many run (((State) s))
                    ((BTrue) (SConst v))
                    ((BFalse)
                      (match many (res-term (predates _) r) (((State) s))
                        ((TVar y) (entry-state (predates _) env1 y))
                        ((TBound j) (SDyn)) ((TApp h as) (SDyn)) ((TFn l p rr) (SDyn)) ((TTyCtor p) (SDyn)) ((TValCtor p rr) (SDyn))
                        ((TMatchable d t c) (SDyn)) ((TNewtype c) (SDyn)) ((TErr m) (SDyn))))))
                (let (many env2) (many x) (bind (predates _) env1 (name-or-anon (predates _) name) mult st (res-ty (predates _) r) (Some (Term) (res-term (predates _) r)) coercible-id))
                (let (many env3)
                  (match many (and (predates _) run (mult-is-many (predates _) mult)) (((Env) e))
                    ((BTrue) (env-push-trace (predates _) env2 (TrConst x v)))
                    ((BFalse) env2)))
                (bind-let (subterm _) k env3 brest rrest vrest run (Cons (Bin) x acc)))))))))

  ; comptime-match (section 15): a Const, non-erased scrutinee with a non-erased discriminant, verified
  ; against the named constructor; the fields are bound Const and the facts refined as a branch would.
  (many elab-comptime-match : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
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
                    (let (many env10) (trace-many-fields (subterm _) k env9 fids))
                    (match many (refine (predates _) env10 (res-of (predates _) env10 x) c fids ret) _
                      ((UOk env11) (values env11 (SNone)))
                      ((UContra msg) (values (env-error (predates _) env10 (str-cat3 (predates _) "internal: the verified value contradicts the facts in force (" msg ")")) (SNone)))))))))))))

  (many trace-many-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List (Bin)) ids) -> (many (Env) r)
    (match many fuel _
      ((Zero) env)
      ((Succ k)
        (match many ids _
          ((Nil a) env)
          ((Cons a x rest)
            (match many (entry-mult-of (predates _) env x) _
              ((Erased) (trace-many-fields (subterm _) k env rest))
              ((Many)
                (match many (entry-state (predates _) env x) _
                  ((SDyn) (trace-many-fields (subterm _) k env rest))
                  ((SConst v) (trace-many-fields (subterm _) k (env-push-trace (predates _) env (TrConst x v)) rest))))))))))

  ; def-fns (sections 7, 27): headers bound Dyn, each body elaborated at the block's level under its own
  ; subterm parameters and checked against its return telescope; closures minted Const in run position.
  (many elab-def-fns : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (match many args _
          ((Nil a) (values (env-error (predates _) env "def-fns needs a level") (SNone)))
          ((Cons a lvraw fns)
            (let (many env2) (many lvl)
              (match many (is-underscore (predates _) lvraw) (((Env) e) ((Bin) x))
                ((BTrue) (mint-level (predates _) env (None (String))))
                ((BFalse) (let (many env2) (many t) (elab-term (subterm _) k env lvraw)) (level-var-checked (predates _) env2 t))))
            (let (many env3) (many headers) (elab-headers (subterm _) k env2 fns lvl))
            (let (many env4) (many fids) (bind-headers (predates _) headers env3))
            (let (many env5) (many fns2) (define-fns (subterm _) k env4 headers fids lvl (env-run-pos (predates _) env4)))
            (match many (env-run-pos (predates _) env5) _
              ((BTrue)
                (let (many vals) (close-group (predates _) fns2 fns2 (env-values (predates _) env5)))
                (let (many env6) (set-fn-states (predates _) fns2 env5 vals))
                (values (env-push-trace (predates _) env6 (TrFns fns2)) (SNone)))
              ((BFalse)
                (let (many kept) (many-fns (predates _) fns2 env5))
                (match many kept _
                  ((Nil b) (values env5 (SNone)))
                  ((Cons b f rest) (values env5 (SLetRec kept)))))))))))

  (many elab-headers : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) fns) (many (Bin) lvl) -> (many (Env) r) (many (List (Header)) hs)
    (match many fuel _
      ((Zero) (values env (Nil (Header))))
      ((Succ k)
        (match many fns _
          ((Nil a) (values env (Nil (Header))))
          ((Cons a f rest)
            (let (many envl) (env-at (predates _) env (raw-line (predates _) f)))
            (match many (raw-items (predates _) f) _
              ((Nil b) (values (env-error (predates _) envl "malformed function definition") (Nil (Header))))
              ((Cons b mraw items)
                (let (many env0) (many mult) (mult-checked (predates _) envl mraw))
                (let (many isabs) (many isext) (many items2) (take-marks (predates _) items env0 (MkAbsurd) (MkExtern)))
                (match many items2 _
                  ((Nil c) (values (env-error (predates _) env0 "malformed function header") (Nil (Header))))
                  ((Cons c nraw items3)
                    (let (many name) (raw-name (predates _) nraw))
                    (let (many env1) (many sg)
                      (match many items3 (((Env) e) ((List (Raw)) l))
                        ((Nil d) (values (env-error (predates _) env0 "malformed function header") (Nil (Raw))))
                        ((Cons d colon sg) (match many (is-mark (predates _) env0 colon (MkColon)) (((Env) e) ((List (Raw)) l)) ((BTrue) (values env0 sg)) ((BFalse) (values (env-error (predates _) env0 "malformed function header") sg))))))
                    (let (many ps) (many after) (split-arrow (predates _) sg env1))
                    (let (many rs) (many body) (split-returns (predates _) after env1))
                    (let (many env2) (many ty) (elab-fn-type (subterm _) k env1 (TVar lvl) ps rs))
                    (let (many env3) (match many isext (((Env) e)) ((BTrue) (claim-extern (predates _) env2 name (is-extern-fn (predates _) name))) ((BFalse) env2)))
                    (let (many impl) (match many (and (predates _) isext (is-extern-fn (predates _) name)) (((Maybe (String)) i)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                    (let (many env4) (many hs) (elab-headers (subterm _) k (env-back (predates _) env env3) rest lvl))
                    (values env4 (Cons (Header) (MkHeader name mult isabs impl ty body) hs)))))))))))

  (many define-fns : (subterm many (Nat) fuel) (many (Env) env) (many (List (Header)) headers) (many (List (Bin)) fids) (many (Bin) lvl) (many (Bool) top) -> (many (Env) r) (many (List (Pair (Bin) (Func))) fns)
    (match many fuel _
      ((Zero) (values env (Nil (Pair (Bin) (Func)))))
      ((Succ k)
        (match many headers _
          ((Nil a) (values env (Nil (Pair (Bin) (Func)))))
          ((Cons a h hrest)
            (match many fids _
              ((Nil b) (values env (Nil (Pair (Bin) (Func)))))
              ((Cons b x xrest)
                (match many h _
                  ((MkHeader name mult isabs impl ty body)
                    (let (many params) (many rets)
                      (match many ty (((List (Entry)) p) ((List (Entry)) r))
                        ((TFn l p r) (values p r))
                        ((TVar y) (values (Nil (Entry)) (Nil (Entry)))) ((TBound j) (values (Nil (Entry)) (Nil (Entry)))) ((TApp hh as) (values (Nil (Entry)) (Nil (Entry))))
                        ((TTyCtor p) (values (Nil (Entry)) (Nil (Entry)))) ((TValCtor p r) (values (Nil (Entry)) (Nil (Entry)))) ((TMatchable d t c) (values (Nil (Entry)) (Nil (Entry))))
                        ((TNewtype c) (values (Nil (Entry)) (Nil (Entry)))) ((TErr m) (values (Nil (Entry)) (Nil (Entry))))))
                    (let (many envb0) (many pids) (open-tele (predates _) params (env-set-run-pos (predates _) env (BFalse)) (None (List (Maybe (String)))) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                    (let (many envb) (env-enter-body (predates _) envb0 lvl (subterm-params (predates _) params pids)))
                    (let (many envb2) (many code)
                      (match many isabs (((Env) e) ((Code) c))
                        ((BTrue) (values (elab-absurd (subterm _) k envb body) (CAbsurd)))
                        ((BFalse)
                          (let (many pvars) (tvars-rev (predates _) pids (Nil (Term))))
                          (let (many tele) (instantiate-tele (predates _) pvars rets))
                          (let (many envb1) (many ress) (many code) (elab-body (subterm _) k envb (under-list (predates _) (tele-mults (predates _) rets) mult) body (Some (List (Entry)) tele)))
                          (let (many envb2) (check-results-count (predates _) envb1 rets ress pvars))
                          (values envb2 (match many mult (((Code) c)) ((Erased) (CErased)) ((Many) code))))))
                    (let (many envb3) (many code2) (many delegated) (check-marks (predates _) envb2 (non-erased (predates _) pids envb2) code))
                    (let (many env2) (env-discard (predates _) env envb3))
                    (let (many env3)
                      (match many delegated (((Env) e))
                        ((None c) env2)
                        ((Some c callee)
                          (let (many env3) (many px) (bind (predates _) env2 (None (String)) (Erased) (SDyn) (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) (TVar x) (Cons (Term) (type-of (predates _) env2 callee) (Cons (Term) (TVar callee) (Nil (Term))))))) (None (Term)) coercible-id))
                          env3)))
                    (let (many fn) (MkFunc name x (non-erased (predates _) pids envb3) code2 impl top))
                    (let (many env4) (many fns) (define-fns (subterm _) k env3 hrest xrest lvl top))
                    (values env4 (Cons (Pair (Bin) (Func)) (MkPair (Bin) (Func) x fn) fns)))))))))))

  ; def-adts (sections 12, 19, 27): type constructors bound first, then each type's constructors, Matchable
  ; and Newtype; every constructor returns its own type.
  (many elab-def-adts : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) adts) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many env2) (many headers) (many tys) (elab-adt-headers (subterm _) k env adts))
        (let (many env3) (many tids) (bind-adt-headers (predates _) headers env2 tys))
        (let (many env4) (many consts) (define-adts (subterm _) k env3 headers tids))
        (match many (env-run-pos (predates _) env4) _
          ((BTrue) (values (set-const-states (predates _) consts env4) (SNone)))
          ((BFalse)
            (match many consts _
              ((Nil a) (values env4 (SNone)))
              ((Cons a c rest) (values env4 (SConsts consts)))))))))

  (many elab-adt-headers : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) adts) -> (many (Env) r) (many (List (AdtHeader)) hs) (many (List (Term)) tys)
    (match many fuel _
      ((Zero) (values env (Nil (AdtHeader)) (Nil (Term))))
      ((Succ k)
        (match many adts _
          ((Nil a) (values env (Nil (AdtHeader)) (Nil (Term))))
          ((Cons a adt rest)
            (let (many envl) (env-at (predates _) env (raw-line (predates _) adt)))
            (match many (raw-items (predates _) adt) _
              ((Nil b) (values (env-error (predates _) envl "malformed def-adts entry") (Nil (AdtHeader)) (Nil (Term))))
              ((Cons b nraw items)
                (let (many name) (raw-name (predates _) nraw))
                (let (many env0) (many sg)
                  (match many items (((Env) e) ((List (Raw)) l))
                    ((Nil c) (values (env-error (predates _) envl "malformed def-adts entry") (Nil (Raw))))
                    ((Cons c colon sg) (match many (is-mark (predates _) envl colon (MkColon)) (((Env) e) ((List (Raw)) l)) ((BTrue) (values envl sg)) ((BFalse) (values (env-error (predates _) envl "malformed def-adts entry") sg))))))
                (let (many ps) (many after) (split-arrow (predates _) sg env0))
                (let (many env1) (many tyraws) (many disc) (many nt) (many ext) (many ctors)
                  (match many after (((Env) e) ((List (Raw)) t) ((Disc) d) ((Bool) n) ((Bool) x) ((List (Raw)) cs))
                    ((Nil c) (values (env-error (predates _) env0 "malformed def-adts entry") (Nil (Raw)) (DEnum) (BFalse) (BFalse) (Nil (Raw))))
                    ((Cons c tyraw after2)
                      (match many after2 (((Env) e) ((List (Raw)) t) ((Disc) d) ((Bool) n) ((Bool) x) ((List (Raw)) cs))
                        ((Nil d) (values (env-error (predates _) env0 "malformed def-adts entry") (Nil (Raw)) (DEnum) (BFalse) (BFalse) (Nil (Raw))))
                        ((Cons d draw after3)
                          (let (many env1) (many disc) (disc-of-checked (predates _) env0 draw))
                          (let (many nt) (many ext) (many cs) (take-marks (predates _) after3 env1 (MkNewtypeMark) (MkExtern)))
                          (values env1 (Cons (Raw) tyraw (Nil (Raw))) disc nt ext cs))))))
                (let (many env2) (many ty) (elab-tyctor (subterm _) k env1 ps tyraws))
                (let (many env3) (many hs) (many tys) (elab-adt-headers (subterm _) k (env-back (predates _) env env2) rest))
                (values env3 (Cons (AdtHeader) (MkAdtHeader name ps disc nt ext ctors) hs) (Cons (Term) ty tys)))))))))

  (many define-adts : (subterm many (Nat) fuel) (many (Env) env) (many (List (AdtHeader)) headers) (many (List (Bin)) tids) -> (many (Env) r) (many (List (Pair (Bin) (Value))) consts)
    (match many fuel _
      ((Zero) (values env (Nil (Pair (Bin) (Value)))))
      ((Succ k)
        (match many headers _
          ((Nil a) (values env (Nil (Pair (Bin) (Value)))))
          ((Cons a h hrest)
            (match many tids _
              ((Nil b) (values env (Nil (Pair (Bin) (Value)))))
              ((Cons b tid trest)
                (match many h _
                  ((MkAdtHeader name params disc nt ext ctors)
                    (let (many env2) (many mcpairs) (elab-ctors (subterm _) k env ctors tid))
                    (let (many mctors) (mctors-of (predates _) mcpairs))
                    (let (many ss) (shapes (predates _) mctors env2))
                    (let (many tagged) (tagged-of (predates _) disc ss))
                    (let (many env2b) (match many ext (((Env) e)) ((BTrue) (claim-extern (predates _) env2 name (is-extern-type (predates _) name))) ((BFalse) env2)))
                    (let (many extname) (match many (and (predates _) ext (is-extern-type (predates _) name)) (((Maybe (String)) e)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                    (let (many records) (ctor-records (predates _) (non-phantom (predates _) ss) env2b 0 tagged extname))
                    (let (many adt) (MkAdt name tagged records extname))
                    (let (many cvals) (ctor-values (predates _) records))
                    (let (many env3) (many mid) (bind (predates _) env2b (None (String)) (Many) (SConst (VMatchable adt)) (TMatchable disc (TVar tid) mctors) (None (Term)) coercible-id))
                    (let (many env4)
                      (match many nt (((Env) e))
                        ((BFalse) env3)
                        ((BTrue)
                          (match many (wrapper (predates _) disc ss) (((Env) e))
                            ((None c) (env-error (predates _) env3 (str-cat (predates _) name " is not of newtype shape (section 38)")))
                            ((Some c w) (let (many env4) (many nx) (bind (predates _) env3 (None (String)) (Erased) (SDyn) (TNewtype (TVar w)) (None (Term)) coercible-id)) env4)))))
                    (let (many env5) (many more) (define-adts (subterm _) k env4 hrest trest))
                    (values env5 (list-append (predates _) (Pair (Bin) (Value)) cvals (Cons (Pair (Bin) (Value)) (MkPair (Bin) (Value) mid (VMatchable adt)) more))))))))))))

  (many elab-ctors : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) ctors) (many (Bin) tid) -> (many (Env) r) (many (List (Pair (Mult) (Bin))) cs)
    (match many fuel _
      ((Zero) (values env (Nil (Pair (Mult) (Bin)))))
      ((Succ k)
        (match many ctors _
          ((Nil a) (values env (Nil (Pair (Mult) (Bin)))))
          ((Cons a craw rest)
            (let (many envl) (env-at (predates _) env (raw-line (predates _) craw)))
            (match many (raw-items (predates _) craw) _
              ((Nil b) (values (env-error (predates _) envl "malformed constructor") (Nil (Pair (Mult) (Bin)))))
              ((Cons b mraw items)
                (let (many env0) (many mult) (mult-checked (predates _) envl mraw))
                (let (many env1) (many name) (many sg)
                  (match many items (((Env) e) ((String) n) ((List (Raw)) l))
                    ((Nil c) (values (env-error (predates _) env0 "malformed constructor") "_" (Nil (Raw))))
                    ((Cons c nraw more)
                      (match many more (((Env) e) ((String) n) ((List (Raw)) l))
                        ((Nil d) (values (env-error (predates _) env0 "malformed constructor") (raw-name (predates _) nraw) (Nil (Raw))))
                        ((Cons d colon sg) (match many (is-mark (predates _) env0 colon (MkColon)) (((Env) e) ((String) n) ((List (Raw)) l)) ((BTrue) (values env0 (raw-name (predates _) nraw) sg)) ((BFalse) (values (env-error (predates _) env0 "malformed constructor") (raw-name (predates _) nraw) sg))))))))
                (let (many env2) (many tele) (many ret) (many ty) (elab-valctor (subterm _) k env1 sg))
                (let (many env2b)
                  (match many (type-head (predates _) env2 ret) (((Env) e))
                    ((None c) (env-error (predates _) env2 (str-cat3 (predates _) name " must return an application of " (name-of (predates _) env2 tid))))
                    ((Some c t) (match many (bin-eq (predates _) t tid) (((Env) e)) ((BTrue) env2) ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) name " must return an application of " (name-of (predates _) env2 tid))))))))
                (let (many env2c)
                  (match many (and (predates _) (not (predates _) (mult-is-many (predates _) mult)) (not (predates _) (nat-is-zero (predates _) (many-count (predates _) tele)))) (((Env) e))
                    ((BTrue) (env-warn (predates _) env2b (str-cat3 (predates _) "warning: phantom constructor " name " has a many field")))
                    ((BFalse) env2b)))
                (let (many env3) (env-discard (predates _) env1 env2c))
                (let (many st) (match many mult (((State) s)) ((Erased) (match many (env-run-pos (predates _) env3) (((State) s)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn)))) ((Many) (SDyn))))
                (let (many env4) (many c) (bind (predates _) env3 (Some (String) name) mult st ty (None (Term)) coercible-id))
                (let (many env5) (many cs) (elab-ctors (subterm _) k (env-back (predates _) env env4) rest tid))
                (values env5 (Cons (Pair (Mult) (Bin)) (MkPair (Mult) (Bin) mult c) cs)))))))))


  ; The special forms that are expressions (section 27).
  (many elab-special : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Sp) sp) (many (List (Raw)) args) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (let (many multi) (or (predates _) (sp-eq (predates _) sp (SpExpr (ExValues))) (or (predates _) (sp-eq (predates _) sp (SpExpr (ExMatch))) (or (predates _) (sp-eq (predates _) sp (SpMark (MkTail))) (sp-eq (predates _) sp (SpMark (MkDelegate)))))))
        (let (many env0) (many m)
          (match many multi (((Env) e) ((Mult) m))
            ((BTrue) (values env pos))
            ((BFalse)
              (match many expect (((Env) e) ((Mult) m))
                ((Nil a) (values (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " produces one value")) (Erased)))
                ((Cons a m1 rest) (match many rest (((Env) e) ((Mult) m)) ((Nil b) (values env m1)) ((Cons b m2 rest2) (values (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " produces one value")) m1))))))))
        (match many sp _
          ((SpFormer fo)
            (let (many env1) (match many pos (((Env) e)) ((Many) (env-error (predates _) env0 "a type in a non-erased position")) ((Erased) env0)))
            (let (many env2) (many t) (elab-type-form (subterm _) k env1 sp args))
            (values env2 (Cons (Res) (term-res (predates _) env2 t) (Nil (Res))) (CErased)))
          ((SpStmt st) (values (env-error (predates _) env0 (str-cat (predates _) (sp-name (predates _) sp) " is a statement, not an expression")) (Nil (Res)) (CError "statement as expression")))
          ((SpMark mk)
            (match many mk _
              ((MkTail) (elab-marked (subterm _) k env0 expect args (CCTail) sp))
              ((MkDelegate) (elab-marked (subterm _) k env0 expect args (CCDelegate) sp))
              ((MkErased) (malformed (subterm _) k env0 sp)) ((MkMany) (malformed (subterm _) k env0 sp)) ((MkColon) (malformed (subterm _) k env0 sp))
              ((MkIs) (malformed (subterm _) k env0 sp)) ((MkArrow) (malformed (subterm _) k env0 sp)) ((MkSubterm) (malformed (subterm _) k env0 sp))
              ((MkEnum) (malformed (subterm _) k env0 sp)) ((MkUnion) (malformed (subterm _) k env0 sp)) ((MkPredates) (malformed (subterm _) k env0 sp))
              ((MkAbsurd) (malformed (subterm _) k env0 sp)) ((MkNewtypeMark) (malformed (subterm _) k env0 sp)) ((MkExtern) (malformed (subterm _) k env0 sp))))
          ((SpExpr ex)
            (match many ex _
              ((ExValues)
                (let (many n) (list-length (predates _) (Mult) expect))
                (let (many na) (list-length (predates _) (Raw) args))
                (let (many env1) (match many (nat-eq (predates _) n na) (((Env) e)) ((BTrue) env0) ((BFalse) (count-error (predates _) env0 " values" n na))))
                (let (many env2) (many ress) (many codes) (elab-values (subterm _) k env1 expect args))
                (values env2 ress (code-of-values (predates _) codes pos)))
              ((ExMatch) (elab-match (subterm _) k env0 expect args tele))
              ((ExMatchableOf)
                (let (many env2) (many tid) (named (predates _) env0 (one-arg (predates _) args) "a type constructor"))
                (let (many env3) (many found) (find-matchable (predates _) env2 tid))
                (match many found _
                  ((None a) (values (env-error (predates _) env3 (str-cat (predates _) (name-of (predates _) env3 tid) " has no Matchable in scope")) (Nil (Res)) (CError "no Matchable")))
                  ((Some a info) (match many info _ ((MkMatchInfo mid d cs rank) (values env3 (Cons (Res) (res-of (predates _) env3 mid) (Nil (Res))) (matchable-code (predates _) env3 m mid)))))))
              ((ExNewtypeOf)
                (let (many env2) (many c) (ctor-var (predates _) env0 (one-arg (predates _) args)))
                (match many (find-newtype (predates _) (env-objects (predates _) env2) env2 c) _
                  ((None a) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " has no Newtype in scope")) (Nil (Res)) (CError "no Newtype")))
                  ((Some a x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))
              ((ExNumeralOf)
                (let (many env2) (many e) (elab-term (subterm _) k env0 (one-arg (predates _) args)))
                (let (many ce) (canon-env (predates _) env2 e))
                (match many (find-literal (predates _) (env-lits (predates _) env2) env2 ce) _
                  ((None a) (values (env-error (predates _) env2 (str-cat (predates _) (show-t (predates _) env2 e) " is not a literal")) (Nil (Res)) (CError "numeral-of")))
                  ((Some a hit)
                    (match many hit _
                      ((None b) (values (env-error (predates _) env2 (str-cat (predates _) (show-t (predates _) env2 e) " is a string literal, which carries no Numeral proof")) (Nil (Res)) (CError "numeral-of")))
                      ((Some b p) (values env2 (Cons (Res) (res-of (predates _) env2 p) (Nil (Res))) (CErased)))))))
              ((ExLevelOf)
                (let (many env2) (many f) (elab-term (subterm _) k env0 (one-arg (predates _) args)))
                (let (many fty) (canon-env (predates _) env2 (infer (predates _) f env2)))
                (match many fty _
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
                (let (many env2) (many a) (many b) (elab-two-terms (subterm _) k env0 args))
                (let (many env3) (many r) (prove-subterm (predates _) env2 a b))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExProvePredates)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env0 "malformed prove-predates form") (Nil (Res)) (CError "prove-predates")))
                  ((Cons a xraw rest)
                    (let (many env2) (many x) (var-of-raw (predates _) env0 xraw "a variable"))
                    (let (many env3) (many lt) (elab-term (subterm _) k env2 (one-arg (predates _) rest)))
                    (let (many env4) (many lvl) (level-var-checked (predates _) env3 lt))
                    (let (many env5) (many r) (prove-predates (predates _) env4 x lvl))
                    (values env5 (Cons (Res) r (Nil (Res))) (CErased)))))
              ((ExPredatesTrans)
                (let (many env2) (many pa) (many qa) (two-proofs (subterm _) k env0 args predates-id predates-id))
                (let (many env3) (check (predates _) env2 "value" (nth-term (predates _) qa 1) (nth-term (predates _) pa 2)))
                (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) predates-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Nil (Term))))))))
                (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExSubtermTrans)
                (let (many env2) (many pa) (many qa) (two-proofs (subterm _) k env0 args subterm-id subterm-id))
                (let (many env3) (check (predates _) env2 "value" (nth-term (predates _) qa 1) (nth-term (predates _) pa 3)))
                (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) subterm-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Cons (Term) (nth-term (predates _) qa 3) (Nil (Term)))))))))
                (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleTrans)
                (let (many env2) (many pa) (many qa) (two-proofs (subterm _) k env0 args coercible-id coercible-id))
                (let (many env3) (check (predates _) env2 "value" (nth-term (predates _) qa 1) (nth-term (predates _) pa 3)))
                (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Cons (Term) (nth-term (predates _) qa 3) (Nil (Term)))))))))
                (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExPredatesSubterm)
                (let (many env2) (many pa) (many qa) (two-proofs (subterm _) k env0 args predates-id subterm-id))
                (let (many env3) (check (predates _) env2 "value" (nth-term (predates _) qa 3) (nth-term (predates _) pa 1)))
                (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) predates-id (Cons (Term) (nth-term (predates _) qa 0) (Cons (Term) (nth-term (predates _) qa 1) (Cons (Term) (nth-term (predates _) pa 2) (Nil (Term))))))))
                (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoerce)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env0 "malformed coerce form") (Nil (Res)) (CError "coerce")))
                  ((Cons a araw rest)
                    (let (many env2) (many ar) (many code) (elab-expr1 (subterm _) k env0 m araw))
                    (let (many env3) (many p) (elab-erased (subterm _) k env2 (one-arg (predates _) rest)))
                    (let (many env4) (many pa) (expect-proof (predates _) env3 coercible-id p))
                    (let (many env5) (check (predates _) env4 "value" (res-term (predates _) ar) (nth-term (predates _) pa 1)))
                    (let (many env6) (many x) (bind (predates _) env5 (None (String)) m (SDyn) (nth-term (predates _) pa 2) (Some (Term) (nth-term (predates _) pa 3)) coercible-id))
                    (values env6 (Cons (Res) (res-of (predates _) env6 x) (Nil (Res))) code))))
              ((ExCoercibleRefl)
                (let (many env2) (many e) (elab-term (subterm _) k env0 (one-arg (predates _) args)))
                (let (many ty) (infer (predates _) e env2))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) e (Cons (Term) ty (Cons (Term) e (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleSym)
                (let (many env2) (many p) (elab-erased (subterm _) k env0 (one-arg (predates _) args)))
                (let (many env3) (many pa) (expect-proof (predates _) env2 coercible-id p))
                (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) (nth-term (predates _) pa 2) (Cons (Term) (nth-term (predates _) pa 3) (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Nil (Term)))))))))
                (values env4 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleWrap)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env0 "malformed coercible-wrap form") (Nil (Res)) (CError "coercible-wrap")))
                  ((Cons a craw wargs)
                    (let (many env2) (many c) (ctor-var (predates _) env0 craw))
                    (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
                    (let (many env3)
                      (match many (find-newtype (predates _) (env-objects (predates _) env2) env2 c) (((Env) e))
                        ((None b) (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " has no Newtype in scope: only a marked newtype's wrapping constructor has one")))
                        ((Some b x) env2)))
                    (let (many env4)
                      (match many (nat-eq (predates _) (many-count (predates _) ctele) 1) (((Env) e))
                        ((BTrue) env3)
                        ((BFalse) (env-error (predates _) env3 (str-cat (predates _) (name-of (predates _) env3 c) " is not the wrapping constructor")))))
                    (let (many env5) (many acc) (elab-term-args (subterm _) k env4 ctele wargs (Nil (Term))))
                    (let (many f) (field-at-many-fuel (subterm _) k ctele (list-rev (predates _) (Term) acc)))
                    (let (many env6) (many r) (mint (predates _) env5 (proof-type (predates _) coercible-id (Cons (Term) (infer (predates _) f env5) (Cons (Term) f (Cons (Term) (instantiate (predates _) acc ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) acc)) (Nil (Term)))))))))
                    (values env6 (Cons (Res) r (Nil (Res))) (CErased)))))
              ((ExCoercibleCtor)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env0 "malformed coercible-ctor form") (Nil (Res)) (CError "coercible-ctor")))
                  ((Cons a craw cargs)
                    (let (many env2) (many c) (ctor-var (predates _) env0 craw))
                    (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
                    (let (many env3) (match many (phantom (predates _) env2 c) (((Env) e)) ((BTrue) (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 c) " is phantom"))) ((BFalse) env2)))
                    (let (many env4) (many src) (many tgt) (coercible-ctor-args (subterm _) k env3 ctele cargs (Nil (Term)) (Nil (Term)) c))
                    (let (many env5) (many r) (mint (predates _) env4 (proof-type (predates _) coercible-id (Cons (Term) (instantiate (predates _) src ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) src)) (Cons (Term) (instantiate (predates _) tgt ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) tgt)) (Nil (Term)))))))))
                    (values env5 (Cons (Res) r (Nil (Res))) (CErased)))))
              ((ExCoercibleOf)
                (let (many env2) (many g) (named (predates _) env0 (one-arg (predates _) args) "a function name"))
                (match many (find-coercible (predates _) (env-objects (predates _) env2) env2 g) _
                  ((None a) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 g) " has no delegate proof in scope")) (Nil (Res)) (CError "no delegate proof")))
                  ((Some a x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))))))))

  (many malformed : (subterm many (Nat) fuel) (many (Env) env) (many (Sp) sp) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (values (env-error (predates _) env (str-cat3 (predates _) "malformed " (sp-name (predates _) sp) " form")) (Nil (Res)) (CError "malformed")))

  ; tail and delegate wrap a call (section 9, ASSUMPTIONS 9); the compiled code must be that call.
  (many elab-marked : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) (many (CC) cc) (many (Sp) sp) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many env1) (match many (pos-of (predates _) expect) (((Env) e)) ((Erased) (env-error (predates _) env (str-cat (predates _) (sp-name (predates _) sp) " in an erased position"))) ((Many) env)))
        (match many args _
          ((Nil a) (values (env-error (predates _) env1 (str-cat (predates _) (sp-name (predates _) sp) " marks a function call, not nothing")) (Nil (Res)) (CError "mark")))
          ((Cons a call rest)
            (let (many env2) (many ress) (many code) (elab-expr (subterm _) k env1 expect call (None (List (Entry))) cc))
            (let (many ok)
              (match many code (((Bool) b))
                ((CApp f as cc2) (cc-eq (predates _) cc cc2))
                ((CLet ids rhs body) (match many rhs (((Bool) b)) ((CApp f as cc2) (cc-eq (predates _) cc cc2)) ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CValues cs) (BFalse)) ((CLet i r b2) (BFalse)) ((CLetRec fs b2) (BFalse)) ((CMatch s sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
                ((CVar x) (BFalse)) ((CConst v) (BFalse)) ((CErased) (BFalse)) ((CValues cs) (BFalse)) ((CLetRec fs b2) (BFalse)) ((CMatch s sh bs) (BFalse)) ((CAbsurd) (BFalse)) ((CError m) (BFalse))))
            (match many ok _
              ((BTrue) (values env2 ress code))
              ((BFalse) (values (env-error (predates _) env2 (str-cat3 (predates _) (sp-name (predates _) sp) " marks a function call, not " (show-r (predates _) call))) ress code))))))))

  (many elab-values : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) -> (many (Env) r) (many (List (Res)) ress) (many (List (Code)) codes)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (Nil (Code))))
      ((Succ k)
        (match many expect _
          ((Nil a) (values env (Nil (Res)) (Nil (Code))))
          ((Cons a m mrest)
            (match many args _
              ((Nil b) (values env (Nil (Res)) (Nil (Code))))
              ((Cons b arg arest)
                (let (many env2) (many r) (many code) (elab-expr1 (subterm _) k env m arg))
                (let (many env3) (many ress) (many codes) (elab-values (subterm _) k env2 mrest arest))
                (values env3 (Cons (Res) r ress) (match many m (((List (Code)) l)) ((Many) (Cons (Code) code codes)) ((Erased) codes))))))))))

  (many elab-erased : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many r) (many code) (elab-expr1 (subterm _) k env (Erased) raw))
        (values env2 (res-term (predates _) r)))))

  (many elab-two-terms : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (Term) a) (many (Term) b)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel") (TErr "out of fuel")))
      ((Succ k)
        (match many args _
          ((Nil x) (values (env-error (predates _) env "two arguments expected") (TErr "missing") (TErr "missing")))
          ((Cons x araw rest)
            (match many rest _
              ((Nil y) (values (env-error (predates _) env "two arguments expected") (TErr "missing") (TErr "missing")))
              ((Cons y braw more)
                (let (many env2) (many a) (elab-term (subterm _) k env araw))
                (let (many env3) (many b) (elab-term (subterm _) k env2 braw))
                (values env3 a b))))))))

  ; Two proofs of the given kinds, elaborated erased (ASSUMPTIONS 23).
  (many two-proofs : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) (many (Bin) c1) (many (Bin) c2) -> (many (Env) r) (many (List (Term)) pa) (many (List (Term)) qa)
    (match many fuel _
      ((Zero) (values env (Nil (Term)) (Nil (Term))))
      ((Succ k)
        (match many args _
          ((Nil x) (values (env-error (predates _) env "two proofs expected") (Nil (Term)) (Nil (Term))))
          ((Cons x araw rest)
            (match many rest _
              ((Nil y) (values (env-error (predates _) env "two proofs expected") (Nil (Term)) (Nil (Term))))
              ((Cons y braw more)
                (let (many env2) (many p) (elab-erased (subterm _) k env araw))
                (let (many env3) (many pa) (expect-proof (predates _) env2 c1 p))
                (let (many env4) (many q) (elab-erased (subterm _) k env3 braw))
                (let (many env5) (many qa) (expect-proof (predates _) env4 c2 q))
                (values env5 pa qa))))))))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field, each checked against
  ; the field's type on its side (section 38).
  (many coercible-ctor-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (List (Term)) src) (many (List (Term)) tgt) (many (Bin) c) -> (many (Env) r) (many (List (Term)) src2) (many (List (Term)) tgt2)
    (match many fuel _
      ((Zero) (values env src tgt))
      ((Succ k)
        (match many tele _
          ((Nil a) (match many args _ ((Nil b) (values env src tgt)) ((Cons b x more) (values (env-error (predates _) env (str-cat (predates _) "coercible-ctor: wrong number of arguments for " (name-of (predates _) env c))) src tgt))))
          ((Cons a e rest)
            (match many (entry-mult (predates _) e) _
              ((Erased)
                (match many args _
                  ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "coercible-ctor: wrong number of arguments for " (name-of (predates _) env c))) src tgt))
                  ((Cons b sraw more)
                    (match many more _
                      ((Nil d) (values (env-error (predates _) env (str-cat (predates _) "coercible-ctor: wrong number of arguments for " (name-of (predates _) env c))) src tgt))
                      ((Cons d traw args2)
                        (let (many env2) (many s) (elab-term (subterm _) k env sraw))
                        (let (many env3) (many t) (elab-term (subterm _) k env2 traw))
                        (let (many env4) (check-sg (predates _) env3 (sg-inst (predates _) src (entry-sg (predates _) e)) (term-res (predates _) env3 s)))
                        (let (many env5) (check-sg (predates _) env4 (sg-inst (predates _) tgt (entry-sg (predates _) e)) (term-res (predates _) env4 t)))
                        (coercible-ctor-args (subterm _) k env5 rest args2 (Cons (Term) s src) (Cons (Term) t tgt) c))))))
              ((Many)
                (match many args _
                  ((Nil b) (values (env-error (predates _) env (str-cat (predates _) "coercible-ctor: wrong number of arguments for " (name-of (predates _) env c))) src tgt))
                  ((Cons b praw more)
                    (let (many env2) (many p) (elab-erased (subterm _) k env praw))
                    (let (many env3) (many pa) (expect-proof (predates _) env2 coercible-id p))
                    (let (many s) (nth-term (predates _) pa 1))
                    (let (many t) (nth-term (predates _) pa 3))
                    (let (many env4) (check-sg (predates _) env3 (sg-inst (predates _) src (entry-sg (predates _) e)) (MkRes s (nth-term (predates _) pa 0) (Erased))))
                    (let (many env5) (check-sg (predates _) env4 (sg-inst (predates _) tgt (entry-sg (predates _) e)) (MkRes t (nth-term (predates _) pa 2) (Erased))))
                    (coercible-ctor-args (subterm _) k env5 rest more (Cons (Term) s src) (Cons (Term) t tgt) c))))))))))

  ; match (sections 11, 12, 18): the scrutinee, its Matchable, the annotation, then one branch per
  ; constructor, each refined by its forced facts or refuted by them.
  (many elab-match : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (match many (match-parts (predates _) args) _
          ((None a) (values (env-error (predates _) env "malformed match") (Nil (Res)) (CError "match")))
          ((Some a parts)
            (match many parts _
              ((MkPair s1 t1 mraw more)
                (match many more _
                  ((MkPair s2 t2 scrut more2)
                    (match many more2 _
                      ((MkPair s3 t3 ann branches)
                        (let (many pos) (pos-of (predates _) expect))
                        (let (many env0) (many sm) (mult-checked (predates _) env mraw))
                        (let (many smult) (under (predates _) pos sm))
                        (let (many env2) (many sres) (many scode) (elab-expr1 (subterm _) k env0 smult scrut))
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
                                      (match many (and (predates _) (mult-is-many (predates _) pos) (and (predates _) (mult-is-many (predates _) smult) (not (predates _) (mult-is-many (predates _) (entry-mult-of (predates _) env2b mid))))) (((Env) e))
                                        ((BTrue) (env-error (predates _) env2b (str-cat3 (predates _) "the Matchable for " (name-of (predates _) env2b tid) " is erased, so a non-erased match cannot take a value of it apart")))
                                        ((BFalse) env2b)))
                                    (let (many env3) (many ann-tele)
                                      (match many (is-underscore (predates _) ann) (((Env) e) ((List (Entry)) t))
                                        ((BTrue) (match many tele (((Env) e) ((List (Entry)) t)) ((None f) (values (env-error (predates _) env2c "no telescope to reuse for _") (Nil (Entry)))) ((Some f t) (values env2c t))))
                                        ((BFalse)
                                          (match many ann (((Env) e) ((List (Entry)) t))
                                            ((RList lq aitems)
                                              (let (many env3) (many ids) (many t) (elab-tele (subterm _) k env2c aitems (MMExpect expect) (Nil (Term)) (BFalse)))
                                              (values (env-discard (predates _) env2c env3) t))
                                            ((RAtom lq s) (values (env-error (predates _) env2c "malformed match annotation") (Nil (Entry))))
                                            ((RString lq s) (values (env-error (predates _) env2c "malformed match annotation") (Nil (Entry))))))))
                                    (let (many env3b)
                                      (match many (nat-eq (predates _) (list-length (predates _) (Entry) ann-tele) (list-length (predates _) (Mult) expect)) (((Env) e))
                                        ((BTrue) env3)
                                        ((BFalse) (env-error (predates _) env3 (str-cat3 (predates _) "match annotation has " (nat-str (predates _) (list-length (predates _) (Entry) ann-tele)) (str-cat (predates _) " entries, position needs " (nat-str (predates _) (list-length (predates _) (Mult) expect))))))))
                                    (let (many env4) (many rids) (open-tele (predates _) ann-tele env3b (Some (List (Maybe (String))) (anon-names (predates _) ann-tele)) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                                    (let (many env5) (many real) (many seen) (elab-branches (subterm _) k env4 tid branches sres smult mctors ann-tele expect (Nil (RealBranch)) (Nil (Bin))))
                                    (let (many env6) (check-coverage (predates _) mctors env5 seen))
                                    (let (many env7)
                                      (match many (and (predates _) (mult-is-many (predates _) pos) (and (predates _) (or (predates _) (not (predates _) tagged) (not (predates _) (mult-is-many (predates _) smult))) (nat-lt (predates _) 1 (list-length (predates _) (RealBranch) real)))) (((Env) e))
                                        ((BTrue) (env-error (predates _) env6 "a match without a runtime discriminant can have only one real branch"))
                                        ((BFalse) env6)))
                                    (let (many code)
                                      (match many pos (((Code) c))
                                        ((Erased) (CErased))
                                        ((Many)
                                          (match many real (((Code) c))
                                            ((Nil f) (CAbsurd))
                                            ((Cons f rb more3)
                                              (match many (and (predates _) (not (predates _) (mult-is-many (predates _) smult)) (list-is-empty (predates _) (RealBranch) more3)) (((Code) c))
                                                ((BTrue) (match many rb (((Code) c)) ((MkRealBranch cc fids body) body)))
                                                ((BFalse) (CMatch scode (match-shape (predates _) env7 mid tagged) (real-branches-code (predates _) real ss)))))))))
                                    (values env7 (ress-of (predates _) rids env7) code))))))))))))))))))

  ; Each branch: present, refuted automatically with (absurd C), or absurd by proof (section 12).
  (many elab-branches : (subterm many (Nat) fuel) (many (Env) env) (many (Bin) tid) (many (List (Raw)) branches) (many (Res) sres) (many (Mult) smult) (many (List (MCtor)) mctors) (many (List (Entry)) ann-tele) (many (List (Mult)) expect) (many (List (RealBranch)) acc) (many (List (Bin)) seen) ->
      (many (Env) r) (many (List (RealBranch)) real) (many (List (Bin)) seen2)
    (match many fuel _
      ((Zero) (values env (list-rev (predates _) (RealBranch) acc) seen))
      ((Succ k)
        (match many branches _
          ((Nil a) (values env (list-rev (predates _) (RealBranch) acc) seen))
          ((Cons a braw brest)
            (let (many envl) (env-at (predates _) env (raw-line (predates _) braw)))
            (match many (branch-parts (predates _) envl braw) _
              ((None b) (elab-branches (subterm _) k (env-back (predates _) env (env-error (predates _) envl "malformed branch")) tid brest sres smult mctors ann-tele expect acc seen))
              ((Some b bp)
                (match many bp _
                  ((MkBranchParts kind craw fields body)
                    (let (many env1) (many c) (ctor-var (predates _) envl craw))
                    (let (many env2) (many mk) (marker-checked (predates _) envl tid mctors c))
                    (let (many phantom) (match many mk (((Bool) x)) ((Erased) (BTrue)) ((Many) (BFalse))))
                    (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
                    (let (many env3)
                      (match many (or (predates _) (nat-eq (predates _) kind 1) (nat-eq (predates _) (list-length (predates _) (Raw) fields) (list-length (predates _) (Entry) ctele))) (((Env) e))
                        ((BTrue) env2)
                        ((BFalse) (env-error (predates _) env2 (str-cat3 (predates _) (name-of (predates _) env2 c) " has " (str-cat (predates _) (nat-str (predates _) (list-length (predates _) (Entry) ctele)) " fields"))))))
                    (let (many unreachable) (and (predates _) phantom (mult-is-many (predates _) smult)))
                    (let (many mults) (match many phantom (((List (Mult)) ms)) ((BTrue) (all-erased (predates _) (tele-mults (predates _) ctele))) ((BFalse) (under-list (predates _) (tele-mults (predates _) ctele) smult))))
                    (let (many names) (match many (nat-eq (predates _) kind 1) (((List (Maybe (String))) ns)) ((BTrue) (anon-names (predates _) ctele)) ((BFalse) (raw-names (predates _) fields))))
                    (let (many envb) (many fids) (open-tele (predates _) ctele (env-set-run-pos (predates _) env3 (BFalse)) (Some (List (Maybe (String))) names) (Some (List (Mult)) mults) (None (List (State))) (Nil (Term))))
                    (let (many env4) (many acc2)
                      (match many (refine (predates _) envb sres c fids ret) (((Env) e) ((List (RealBranch)) rs))
                        ((UContra msg)
                          (match many (nat-eq (predates _) kind 1) (((Env) e) ((List (RealBranch)) rs))
                            ((BTrue) (values (env-discard (predates _) env3 envb) acc))
                            ((BFalse) (values (env-error (predates _) (env-discard (predates _) env3 envb) (str-cat3 (predates _) "branch " (name-of (predates _) env3 c) (str-cat3 (predates _) " is refuted; write (absurd " (name-of (predates _) env3 c) ")"))) acc))))
                        ((UOk envb2)
                          (match many kind (((Env) e) ((List (RealBranch)) rs))
                            ((Zero)
                              (let (many envb3) (many ress) (many code) (elab-body (subterm _) k envb2 (match many unreachable (((List (Mult)) ms)) ((BTrue) (all-erased (predates _) expect)) ((BFalse) expect)) body (Some (List (Entry)) ann-tele)))
                              (let (many envb4) (check-results-count (predates _) envb3 ann-tele ress (Nil (Term))))
                              (values (env-discard (predates _) env3 envb4)
                                      (match many unreachable (((List (RealBranch)) rs)) ((BTrue) acc) ((BFalse) (Cons (RealBranch) (MkRealBranch c (non-erased (predates _) fids envb4) code) acc)))))
                            ((Succ k1)
                              (match many k1 (((Env) e) ((List (RealBranch)) rs))
                                ((Zero) (values (env-error (predates _) (env-discard (predates _) env3 envb2) (str-cat3 (predates _) "branch " (name-of (predates _) env3 c) " is not refuted")) acc))
                                ((Succ k2)
                                  (let (many envb3) (elab-absurd (subterm _) k envb2 body))
                                  (values (env-discard (predates _) env3 envb3) acc))))))))
                    (elab-branches (subterm _) k (env-back (predates _) env env4) tid brest sres smult mctors ann-tele expect acc2 (Cons (Bin) c seen)))))))))))

  ; The field at a wrapping constructor's one many position, given the arguments in order.
  (many field-at-many-fuel : (subterm many (Nat) fuel) (many (List (Entry)) tele) (many (List (Term)) args) -> (many (Term) t)
    (match many fuel _
      ((Zero) (TErr "out of fuel"))
      ((Succ k)
        (match many tele _
          ((Nil a) (TErr "no many field"))
          ((Cons a e rest)
            (match many args _
              ((Nil b) (TErr "no many field"))
              ((Cons b t trest)
                (match many (entry-mult (predates _) e) _
                  ((Many) t)
                  ((Erased) (field-at-many-fuel (subterm _) k rest trest)))))))))))


; ---- The top level (section 16): statements run as they are elaborated, the final expression consumed;
; only the last form may be an expression (ASSUMPTIONS 12).

(def-fns _ $ many run-toplevel : (subterm many (List (Raw)) items) (many (Env) env) -> (many (Env) r)
  (match many items _
    ((Nil a) env)
    ((Cons a item rest)
      (let (many env2) (intern-literals (predates _) item (env-at (predates _) env (raw-line (predates _) item))))
      (match many (is-statement (predates _) env2 item) _
        ((BTrue)
          (let (many env3) (many sc) (elab-stmt (predates _) elab-fuel env2 item))
          (run-toplevel (subterm _) rest env3))
        ((BFalse)
          (match many rest _
            ((Cons b x more) (run-toplevel (subterm _) rest (env-error (predates _) env2 "only the last top-level form may be an expression")))
            ((Nil b)
              (let (many env3) (many ress) (many code) (elab-expr (predates _) elab-fuel env2 (Cons (Mult) (Many) (Nil (Mult))) item (None (List (Entry))) (CCPlain)))
              (match many (env-errors (predates _) env3) _
                ((Cons c e es) env3)
                ((Nil c)
                  (let (many v) (first-value (predates _) (run-code (predates _) env3 code)))
                  (env-push-trace (predates _) env3 (TrFinal v (res-ty (predates _) (first-res (predates _) ress)))))))))))))
