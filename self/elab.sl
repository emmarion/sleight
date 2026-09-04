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
  (match many r _ ((RAtom s) (Some (String) s)) ((RString s) (None (String))) ((RList items) (None (String)))))

(def-fns _ $ many raw-items : (many (Raw) r) -> (many (List (Raw)) items)
  (match many r _ ((RAtom s) (Nil (Raw))) ((RString s) (Nil (Raw))) ((RList items) items)))

(def-fns _ $ many raw-name : (many (Raw) r) -> (many (String) s)
  (match many r _ ((RAtom s) s) ((RString s) "_") ((RList items) "_")))

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
            ((MkEInfo nm mult st)
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

(def-fns _ $ many mult-or : (many (Env) env) (many (Raw) raw) -> (many (Mult) r)
  (match many (mult-of (predates _) env raw) _ ((None a) (Many)) ((Some a m) m)))

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

; ---- Literals (ASSUMPTIONS 51-53, 60): numerals, characters and strings, interned per program

(def-adts $ LitKind : -> Type
  enum
  (many LName : -> (LitKind))
  (many LNumeral : -> (LitKind))
  (many LChar : -> (LitKind))
  (many LString : -> (LitKind)))

(def-fns _ $ many all-digits : (subterm many (String) s) -> (many (Bool) r)
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (predates _) (char-between (predates _) c 48 57) (all-digits (subterm _) rest)))))

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

(def-fns _ $ many hex-digit : (many (Char) c) -> (many (Nat) d)
  (let (many n) (char-code (predates _) c))
  (match many (char-between (predates _) c 48 57) _
    ((BTrue) (nat-sub (predates _) n 48))
    ((BFalse)
      (match many (char-between (predates _) c 97 102) _
        ((BTrue) (nat-sub (predates _) n 87))
        ((BFalse) (nat-sub (predates _) n 55))))))

; The code of #\c, #\space, #\newline, #\tab or #\xHH.
(def-fns _ $ many char-lit-code : (many (String) s) -> (many (Nat) n)
  (let (many body) (match many s (((String) r)) ((SNil) (SNil)) ((SCons c rest) (match many rest (((String) r)) ((SNil) (SNil)) ((SCons c2 rest2) rest2)))))
  (match many (str-eq (predates _) body "space") _
    ((BTrue) 32)
    ((BFalse)
      (match many (str-eq (predates _) body "newline") _
        ((BTrue) 10)
        ((BFalse)
          (match many (str-eq (predates _) body "tab") _
            ((BTrue) 9)
            ((BFalse)
              (match many body _
                ((SNil) 0)
                ((SCons c rest)
                  (match many rest _
                    ((SNil) (char-code (predates _) c))
                    ((SCons h1 rest2)
                      (match many rest2 _
                        ((SNil) 0)
                        ((SCons h2 rest3)
                          (let (many hi) (hex-digit (predates _) h1))
                          (nat-add (predates _) (nat-add (predates _) (nat-add (predates _) hi hi) (nat-add (predates _) hi hi))
                            (nat-add (predates _) (nat-add (predates _) (nat-add (predates _) hi hi) (nat-add (predates _) hi hi))
                              (nat-add (predates _) (nat-add (predates _) (nat-add (predates _) hi hi) (nat-add (predates _) hi hi))
                                (nat-add (predates _) (nat-add (predates _) (nat-add (predates _) hi hi) (nat-add (predates _) hi hi))
                                  (hex-digit (predates _) h2))))))))))))))))))

(def-fns _ $ many prelude-type : (many (Env) env) (many (String) name) -> (many (Term) t)
  (match many (lookup (predates _) env name) _
    ((None a) (TErr (str-cat (predates _) "prelude type missing: " name)))
    ((Some a x) (TApp (TVar x) (Nil (Term))))))

; Interns a literal: a Const entry outside the scope, found by its text (Env.literals), typed by the prelude.
(def-fns _ $ many intern : (many (Env) env) (many (String) key) (many (LitKind) kind) -> (many (Env) r)
  (match many (nm-get (predates _) (Bin) key (env-literals (predates _) env)) _
    ((Some a x) env)
    ((None a)
      (let (many ty) (many v)
        (match many kind (((Term) t) ((Value) v))
          ((LNumeral) (values (prelude-type (predates _) env "Nat") (vnat (predates _) (parse-nat (predates _) key 0))))
          ((LChar) (values (prelude-type (predates _) env "Char") (VExt u8-adt (PU8 (nat-to-u8 (predates _) (char-lit-code (predates _) key))))))
          ((LString) (values (prelude-type (predates _) env "String")
                             (VExt str-adt (PStr (match many key (((String) s)) ((SNil) (SNil)) ((SCons q rest) rest))))))
          ((LName) (values (TErr "not a literal") (VError "not a literal")))))
      (let (many env2) (many x) (bind (predates _) env (None (String)) (Many) (SConst v) ty (None (Term)) coercible-id))
      (let (many env3) (env-set-literals (predates _) env2 (nm-set (predates _) (Bin) key x (env-literals (predates _) env2))))
      (env-push-trace (predates _) env3 (TrConst x v)))))

(def-fns _
  (many intern-literals : (subterm many (Raw) raw) (many (Env) env) -> (many (Env) r)
    (match many raw _
      ((RAtom s)
        (match many (classify (predates _) s) _
          ((LName) env)
          ((LNumeral) (intern (predates _) env s (LNumeral)))
          ((LChar) (intern (predates _) env s (LChar)))
          ((LString) env)))
      ((RString s) (intern (predates _) env (SCons #\x22 s) (LString)))
      ((RList items) (intern-literals-list (subterm _) items env))))
  (many intern-literals-list : (subterm many (List (Raw)) rs) (many (Env) env) -> (many (Env) r)
    (match many rs _
      ((Nil a) env)
      ((Cons a r rest) (intern-literals-list (subterm _) rest (intern-literals (subterm _) r env))))))

; The entry an atom names: a literal's, or the newest of that name in scope; id zero, which nothing binds,
; stands for an error already recorded.
(def-fns _ $ many var : (many (Env) env) (many (String) n) -> (many (Env) r) (many (Bin) x)
  (match many (classify (predates _) n) _
    ((LName)
      (match many (lookup (predates _) env n) _
        ((Some a x) (values env x))
        ((None a) (values (env-error (predates _) env (str-cat (predates _) "unbound name " n)) (BZ)))))
    ((LNumeral) (match many (nm-get (predates _) (Bin) n (env-literals (predates _) env)) _ ((Some a x) (values env x)) ((None a) (values (env-error (predates _) env (str-cat (predates _) "literal not interned: " n)) (BZ)))))
    ((LChar) (match many (nm-get (predates _) (Bin) n (env-literals (predates _) env)) _ ((Some a x) (values env x)) ((None a) (values (env-error (predates _) env (str-cat (predates _) "literal not interned: " n)) (BZ)))))
    ((LString) (values (env-error (predates _) env "internal: string as name") (BZ)))))

(def-fns _ $ many var-of-raw : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Bin) x)
  (match many raw _
    ((RAtom s) (var (predates _) env s))
    ((RString s)
      (match many (nm-get (predates _) (Bin) (SCons #\x22 s) (env-literals (predates _) env)) _
        ((Some a x) (values env x))
        ((None a) (values (env-error (predates _) env "string literal not interned") (BZ)))))
    ((RList items) (values (env-error (predates _) env "expected a name, got a list") (BZ)))))

; A name read through its alias (ASSUMPTIONS 78).
(def-fns _ $ many named : (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Bin) x)
  (let (many env2) (many x) (var-of-raw (predates _) env raw))
  (values env2 (resolve (predates _) env2 x)))

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

(def-fns _ $ many disc-of : (many (Env) env) (many (Raw) d) -> (many (Disc) r)
  (match many (is-mark (predates _) env d (MkUnion)) _ ((BTrue) (DUnion)) ((BFalse) (DEnum))))

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

(def-fns _ $ many find-matchable : (many (Env) env) (many (Bin) tid) -> (many (Maybe (MatchInfo)) r)
  (find-matchable-in (predates _) (env-objects (predates _) env) env tid (None (MatchInfo))))

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
                  ((TVar g2) (and (predates _) (bin-eq (predates _) g2 g) (match many (entry (predates _) env x) (((Bool) b)) ((MkEInfo n m s) (match many n (((Bool) b)) ((None c) (BTrue)) ((Some c nm) (BFalse)))))))
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

(def-fns _ $ many phantom : (many (Env) env) (many (Bin) c) -> (many (Bool) r)
  (match many (find-matchable (predates _) env (tid-of (predates _) env c)) _
    ((None a) (BFalse))
    ((Some a info) (match many info _ ((MkMatchInfo mid d cs rank) (match many (marker (predates _) cs c) _ ((Erased) (BTrue)) ((Many) (BFalse))))))))

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

(def-fns _ $ many mint-level : (many (Env) env) (many (Maybe (String)) name) -> (many (Env) r) (many (Bin) x)
  (let (many st) (match many (env-run-pos (predates _) env) (((State) s)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn))))
  (bind (predates _) env name (Erased) st level-term (None (Term)) coercible-id))

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
(def-fns _ $ many refine : (many (Env) env) (many (Res) scrut) (many (Bin) c) (many (List (Bin)) fids) (many (Term) ret) -> (many (Env) r)
  (let (many fvars) (tvars-rev (predates _) fids (Nil (Term))))
  (let (many env2) (unify-env (predates _) env (res-term (predates _) scrut) (TApp (TVar c) (list-rev (predates _) (Term) fvars))))
  (unify-env (predates _) env2 (res-ty (predates _) scrut) (instantiate (predates _) fvars ret)))

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

(let (many elab-fuel) 100000)

(def-fns _
  ; An expression of the given size and erasures; [tele] is the telescope a bare _ annotation reuses.
  (many elab-expr : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Raw) raw) (many (Maybe (List (Entry))) tele) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values (env-error (predates _) env "out of fuel") (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (match many raw _
          ((RAtom n)
            (let (many env2) (many x) (var (predates _) env n))
            (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
          ((RString s)
            (let (many env2) (many x) (var-of-raw (predates _) env raw))
            (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (match many pos (((Code) c)) ((Many) (CVar x)) ((Erased) (CErased)))))
          ((RList items)
            (match many items _
              ((Nil a) (values (env-error (predates _) env "empty form") (Nil (Res)) (CError "empty form")))
              ((Cons a head args)
                (match many (special-of (predates _) env head) _
                  ((Some b sp) (elab-special (subterm _) k env expect sp args tele))
                  ((None b)
                    (let (many env2) (many h) (many hcode)
                      (match many head (((Env) e) ((Res) r) ((Code) c))
                        ((RAtom n) (let (many env2) (many x) (var (predates _) env n)) (values env2 (res-of (predates _) env2 x) (CVar x)))
                        ((RString s) (let (many env2) (many x) (var-of-raw (predates _) env head)) (values env2 (res-of (predates _) env2 x) (CVar x)))
                        ((RList hitems)
                          (let (many env2) (many ress) (many hcode) (elab-expr (subterm _) k env (Cons (Mult) pos (Nil (Mult))) head (None (List (Entry))) (CCPlain)))
                          (values env2 (first-res (predates _) ress) hcode))))
                    (match many (canon-env (predates _) env2 (res-ty (predates _) h)) _
                      ((TTyCtor ttele)
                        (let (many env3) (many acc) (elab-term-args (subterm _) k env2 ttele args (Nil (Term))))
                        (values env3 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) type-term (Erased)) (Nil (Res))) (CErased)))
                      ((TValCtor ctele ret)
                        (let (many env3) (many acc) (many codes) (check-args (subterm _) k env2 ctele args pos (Nil (Term)) (Nil (Code))))
                        (let (many code) (match many pos (((Code) c)) ((Erased) (CErased)) ((Many) (CApp hcode codes (CCCtor)))))
                        (values env3 (Cons (Res) (MkRes (TApp (res-term (predates _) h) (list-rev (predates _) (Term) acc)) (instantiate (predates _) acc ret) pos) (Nil (Res))) code))
                      ((TFn lv params rets) (elab-call (subterm _) k env2 expect h hcode params rets args cc))
                      ((TVar x) (values (env-error (predates _) env2 (str-cat (predates _) "not applicable: " (raw-name (predates _) head))) (Nil (Res)) (CError "not applicable")))
                      ((TBound j) (values (env-error (predates _) env2 "not applicable") (Nil (Res)) (CError "not applicable")))
                      ((TApp h2 a2) (values (env-error (predates _) env2 (str-cat (predates _) "not applicable: " (raw-name (predates _) head))) (Nil (Res)) (CError "not applicable")))
                      ((TMatchable d t c) (values (env-error (predates _) env2 "not applicable") (Nil (Res)) (CError "not applicable")))
                      ((TNewtype c) (values (env-error (predates _) env2 "not applicable") (Nil (Res)) (CError "not applicable")))
                      ((TErr m) (values (env-error (predates _) env2 (str-cat (predates _) "head type error: " m)) (Nil (Res)) (CError m)))))))))))))

  (many elab-expr1 : (subterm many (Nat) fuel) (many (Env) env) (many (Mult) mult) (many (Raw) raw) -> (many (Env) r) (many (Res) res) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (MkRes (TErr "out of fuel") (TErr "out of fuel") (Erased)) (CError "out of fuel")))
      ((Succ k)
        (let (many env2) (many ress) (many code) (elab-expr (subterm _) k env (Cons (Mult) mult (Nil (Mult))) raw (None (List (Entry))) (CCPlain)))
        (values env2 (first-res (predates _) ress) code))))

  ; Arguments against a telescope, each at the position's multiplicity; returns the terms innermost first
  ; and the code of the many ones in order.
  (many check-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (Mult) pos) (many (List (Term)) acc) (many (List (Code)) codes) ->
      (many (Env) r) (many (List (Term)) acc2) (many (List (Code)) codes2)
    (match many fuel _
      ((Zero) (values env acc (Nil (Code))))
      ((Succ k)
        (match many tele _
          ((Nil a) (values env acc (list-rev (predates _) (Code) codes)))
          ((Cons a e rest)
            (match many args _
              ((Nil b) (values (env-error (predates _) env "too few arguments") acc (list-rev (predates _) (Code) codes)))
              ((Cons b arg arest)
                (let (many m) (entry-mult (predates _) e))
                (let (many env2) (many r) (many code) (elab-expr1 (subterm _) k env (under (predates _) pos m) arg))
                (check-args (subterm _) k env2 rest arest pos (Cons (Term) (res-term (predates _) r) acc)
                  (match many m (((List (Code)) l)) ((Many) (Cons (Code) code codes)) ((Erased) codes))))))))))

  (many elab-term-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (List (Term)) acc) -> (many (Env) r) (many (List (Term)) acc2)
    (match many fuel _
      ((Zero) (values env acc))
      ((Succ k)
        (match many tele _
          ((Nil a) (values env acc))
          ((Cons a e rest)
            (match many args _
              ((Nil b) (values (env-error (predates _) env "too few arguments") acc))
              ((Cons b arg arest)
                (let (many env2) (many t) (elab-term (subterm _) k env arg))
                (elab-term-args (subterm _) k env2 rest arest (Cons (Term) t acc)))))))))

  ; A function call (section 9); the annotations are stripped, the call being trusted.
  (many elab-call : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Res) callee) (many (Code) hcode) (many (List (Entry)) params) (many (List (Entry)) rets) (many (List (Raw)) rawargs) (many (CC) cc) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (let (many args) (strip-annotations (predates _) rawargs env))
        (let (many env2) (many acc) (many codes) (check-args (subterm _) k env params args pos (Nil (Term)) (Nil (Code))))
        (let (many rmults) (tele-mults (predates _) rets))
        (let (many env3) (many ids) (open-tele (predates _) rets env2 (Some (List (Maybe (String))) (anon-names (predates _) rets)) (Some (List (Mult)) (under-list (predates _) rmults pos)) (None (List (State))) acc))
        (let (many call) (CApp hcode codes cc))
        (let (many env4) (many code)
          (match many pos (((Env) e) ((Code) c))
            ((Erased) (values env3 (CErased)))
            ((Many)
              (match many (and (predates _) (nat-eq (predates _) (list-length (predates _) (Mult) expect) (list-length (predates _) (Entry) rets)) (needs-projection (predates _) expect rmults)) (((Env) e) ((Code) c))
                ((BFalse) (values env3 call))
                ((BTrue)
                  (let (many env4) (many bound) (many kept) (projection (predates _) expect rmults env3))
                  (values env4 (CLet bound call (CValues kept))))))))
        (values env4 (ress-of (predates _) ids env4) code))))

  ; Grammar expressions (section 5): variables and constructor applications and type formers.
  (many elab-term : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (match many raw _
          ((RAtom n) (let (many env2) (many x) (var (predates _) env n)) (values env2 (TVar x)))
          ((RString s) (let (many env2) (many x) (var-of-raw (predates _) env raw)) (values env2 (TVar x)))
          ((RList items)
            (match many items _
              ((Nil a) (values (env-error (predates _) env "empty form in a type") (TErr "empty form")))
              ((Cons a head args)
                (match many (special-of (predates _) env head) _
                  ((Some b sp) (elab-type-form (subterm _) k env sp args))
                  ((None b)
                    (let (many env2) (many x) (var-of-raw (predates _) env head))
                    (let (many h) (TVar x))
                    (match many (canon-env (predates _) env2 (infer (predates _) h env2)) _
                      ((TTyCtor ttele)
                        (let (many env3) (many acc) (elab-term-args (subterm _) k env2 ttele args (Nil (Term))))
                        (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                      ((TValCtor ctele ret)
                        (let (many env3) (many acc) (elab-term-args (subterm _) k env2 ctele args (Nil (Term))))
                        (values env3 (TApp h (list-rev (predates _) (Term) acc))))
                      ((TVar y) (values (env-error (predates _) env2 (str-cat (predates _) "not applicable in a type: " (raw-name (predates _) head))) (TErr "not applicable")))
                      ((TBound j) (values env2 (TErr "not applicable")))
                      ((TApp h2 a2) (values (env-error (predates _) env2 (str-cat (predates _) "not applicable in a type: " (raw-name (predates _) head))) (TErr "not applicable")))
                      ((TFn l p r) (values (env-error (predates _) env2 "a function cannot be applied in a type") (TErr "function in type")))
                      ((TMatchable d t c) (values env2 (TErr "not applicable")))
                      ((TNewtype c) (values env2 (TErr "not applicable")))
                      ((TErr m) (values (env-error (predates _) env2 (str-cat (predates _) "type error: " m)) (TErr m)))))))))))))

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
                    (let (many ps) (many rs) (split-arrow (predates _) rest env2))
                    (elab-fn-type (subterm _) k env2 lv ps rs))))
              ((FoTyCtor)
                (let (many ps) (many ret) (split-arrow (predates _) args env))
                (elab-tyctor (subterm _) k env ps))
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
                        (let (many env2) (many tid) (named (predates _) env t))
                        (let (many env3) (many mcs) (elab-mctors (subterm _) k env2 cs))
                        (values env3 (TMatchable (disc-of (predates _) env d) (TVar tid) mcs)))))))
              ((FoNewtype)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed Newtype") (TErr "malformed Newtype")))
                  ((Cons a c rest)
                    (let (many env2) (many cid) (named (predates _) env c))
                    (values env2 (TNewtype (TVar cid))))))))
          ((SpStmt s) (values (env-error (predates _) env "a statement cannot appear in a type") (TErr "statement in type")))
          ((SpExpr e) (values (env-error (predates _) env "this form cannot appear in a type") (TErr "expression in type")))
          ((SpMark m) (values (env-error (predates _) env "a mark cannot appear in a type") (TErr "mark in type")))))))

  (many elab-mctors : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) cs) -> (many (Env) r) (many (List (MCtor)) mcs)
    (match many fuel _
      ((Zero) (values env (Nil (MCtor))))
      ((Succ k)
        (match many cs _
          ((Nil a) (values env (Nil (MCtor))))
          ((Cons a c rest)
            (let (many m) (many craw)
              (match many (raw-items (predates _) c) (((Mult) m) ((Raw) r))
                ((Nil b) (values (Many) c))
                ((Cons b mraw more) (values (mult-or (predates _) env mraw) (match many more (((Raw) r)) ((Nil d) c) ((Cons d cr more2) cr))))))
            (let (many env2) (many cid) (named (predates _) env craw))
            (let (many env3) (many mcs) (elab-mctors (subterm _) k env2 rest))
            (values env3 (Cons (MCtor) (MkMCtor m (TVar cid)) mcs)))))))

  (many elab-fn-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) lv) (many (List (Raw)) ps) (many (List (Raw)) rs) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many ids) (many params) (elab-tele (subterm _) k env ps (MMDeclared) (Nil (Term))))
        (let (many env3) (many ids2) (many rets) (elab-tele (subterm _) k env2 rs (MMDeclared) (tvars-rev (predates _) ids (Nil (Term)))))
        (values (env-discard (predates _) env env3) (TFn lv params rets)))))

  (many elab-tyctor : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) ps) -> (many (Env) r) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel")))
      ((Succ k)
        (let (many env2) (many ids) (many tele) (elab-tele (subterm _) k env ps (MMErased) (Nil (Term))))
        (values (env-discard (predates _) env env2) (TTyCtor tele)))))

  ; Returns the environment with the fields in scope, the telescope, the return type over them, and the
  ; closed ValCtor type.
  (many elab-valctor : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) items) -> (many (Env) r) (many (List (Entry)) tele) (many (Term) ret) (many (Term) t)
    (match many fuel _
      ((Zero) (values env (Nil (Entry)) (TErr "out of fuel") (TErr "out of fuel")))
      ((Succ k)
        (let (many ps) (many rets) (split-arrow (predates _) items env))
        (let (many env2) (many ids) (many tele) (elab-tele (subterm _) k env ps (MMDeclared) (Nil (Term))))
        (let (many env3) (many ret)
          (match many rets (((Env) e) ((Term) t))
            ((Nil a) (values (env-error (predates _) env2 "a constructor returns one type") (TErr "no return")))
            ((Cons a r more) (elab-term (subterm _) k env2 r))))
        (values env3 tele ret (TValCtor tele (abstract (predates _) (list-rev (predates _) (Bin) ids) ret))))))

  ; Source entries into a closed telescope, each name bound for the entries after it (section 30).
  ; [ids]: binders already in force, innermost first.
  (many elab-tele : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) entries) (many (MultsMode) mode) (many (List (Term)) ids) -> (many (Env) r) (many (List (Bin)) bound) (many (List (Entry)) tele)
    (match many fuel _
      ((Zero) (values env (Nil (Bin)) (Nil (Entry))))
      ((Succ k) (elab-src-entries (subterm _) k env (parse-entries (predates _) entries env) mode ids (Nil (Bin))))))

  (many elab-src-entries : (subterm many (Nat) fuel) (many (Env) env) (many (List (SrcEntry)) entries) (many (MultsMode) mode) (many (List (Term)) ids) (many (List (Bin)) bound) -> (many (Env) r) (many (List (Bin)) bound2) (many (List (Entry)) tele)
    (match many fuel _
      ((Zero) (values env bound (Nil (Entry))))
      ((Succ k)
        (match many entries _
          ((Nil a) (values env (list-rev (predates _) (Bin) bound) (Nil (Entry))))
          ((Cons a e rest)
            (match many e _
              ((MkSrcEntry sub smult ssg name)
                (let (many mult) (many mode2)
                  (match many mode (((Mult) m) ((MultsMode) md))
                    ((MMDeclared) (values (match many smult (((Mult) m)) ((None b) (Many)) ((Some b m) m)) mode))
                    ((MMErased) (values (Erased) mode))
                    ((MMExpect ms) (match many ms (((Mult) m) ((MultsMode) md)) ((Nil b) (values (Erased) mode)) ((Cons b m more) (values m (MMExpect more)))))))
                (let (many env2) (many sg)
                  (match many ssg (((Env) e) ((Sg) s))
                    ((None b) (values (env-error (predates _) env (str-cat (predates _) "entry needs a type: " name)) (SgTy (TErr "no type"))))
                    ((Some b s)
                      (match many s (((Env) e) ((Sg) s))
                        ((SrcTy r) (let (many env2) (many t) (elab-term (subterm _) k env r)) (values env2 (SgTy t)))
                        ((SrcIs r) (let (many env2) (many t) (elab-term (subterm _) k env r)) (values env2 (SgIs t)))))))
                (let (many ty) (many rule) (fact-of (predates _) env2 sg))
                (let (many nm) (name-or-anon (predates _) name))
                (let (many env3) (many x) (bind (predates _) env2 nm mult (SDyn) ty rule coercible-id))
                (let (many entry) (MkEntry nm sub mult (abstract-sg (predates _) (bin-ids-of (predates _) ids) sg)))
                (let (many env4) (many bound2) (many tele) (elab-src-entries (subterm _) k env3 rest mode2 (Cons (Term) (TVar x) ids) (Cons (Bin) x bound)))
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

  (many elab-stmt : (subterm many (Nat) fuel) (many (Env) env) (many (Raw) raw) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many items) (raw-items (predates _) raw))
        (match many items _
          ((Nil a) (values (env-error (predates _) env "not a statement") (SNone)))
          ((Cons a head args)
            (match many (stmt-of (predates _) env raw) _
              ((None b) (values (env-error (predates _) env (str-cat (predates _) "not a statement: " (raw-name (predates _) head))) (SNone)))
              ((Some b st)
                (match many st _
                  ((StLet) (elab-let (subterm _) k env args))
                  ((StDefLvl)
                    (let (many nm) (match many args (((Maybe (String)) n)) ((Nil c) (None (String))) ((Cons c n more) (name-or-anon (predates _) (raw-name (predates _) n)))))
                    (let (many env2) (many x) (mint-level (predates _) env nm))
                    (values env2 (SNone)))
                  ((StDefFns) (elab-def-fns (subterm _) k env args))
                  ((StDefAdts) (elab-def-adts (subterm _) k env args))
                  ((StComptimeMatch) (elab-comptime-match (subterm _) k env args))))))))))

  ; let (section 9): binders, then the right-hand side; run at once in run position (section 34).
  (many elab-let : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (let (many braws) (many rhs) (split-returns (predates _) args env))
        (let (many binders) (parse-entries (predates _) braws env))
        (let (many expect) (src-mults (predates _) binders))
        (let (many inner) (many ress) (many code) (elab-body (subterm _) k env expect rhs (None (List (Entry)))))
        (let (many run) (env-run-pos (predates _) env))
        (let (many vals)
          (match many (and (predates _) run (mult-is-many (predates _) (pos-of (predates _) expect))) (((List (Value)) vs))
            ((BTrue) (run-code (predates _) inner code))
            ((BFalse) (Nil (Value)))))
        (let (many env2) (many ids) (bind-let (subterm _) k (env-restore (predates _) env inner) binders ress (spread (predates _) expect vals) run (Nil (Bin))))
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
                (let (many st)
                  (match many run (((State) s))
                    ((BTrue) (SConst v))
                    ((BFalse)
                      (match many (res-term (predates _) r) (((State) s))
                        ((TVar y) (entry-state (predates _) env y))
                        ((TBound j) (SDyn)) ((TApp h as) (SDyn)) ((TFn l p rr) (SDyn)) ((TTyCtor p) (SDyn)) ((TValCtor p rr) (SDyn))
                        ((TMatchable d t c) (SDyn)) ((TNewtype c) (SDyn)) ((TErr m) (SDyn))))))
                (let (many env2) (many x) (bind (predates _) env (name-or-anon (predates _) name) mult st (res-ty (predates _) r) (Some (Term) (res-term (predates _) r)) coercible-id))
                (let (many env3)
                  (match many (and (predates _) run (mult-is-many (predates _) mult)) (((Env) e))
                    ((BTrue) (env-push-trace (predates _) env2 (TrConst x v)))
                    ((BFalse) env2)))
                (bind-let (subterm _) k env3 brest rrest vrest run (Cons (Bin) x acc)))))))))

  ; comptime-match (section 15): the value's fields bound Const, the facts refined as a branch would.
  (many elab-comptime-match : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (StmtCode) sc)
    (match many fuel _
      ((Zero) (values env (SNone)))
      ((Succ k)
        (match many args _
          ((Nil a) (values (env-error (predates _) env "malformed comptime-match") (SNone)))
          ((Cons a xraw rest)
            (match many rest _
              ((Nil b) (values (env-error (predates _) env "malformed comptime-match") (SNone)))
              ((Cons b pat more)
                (match many (raw-items (predates _) pat) _
                  ((Nil c) (values (env-error (predates _) env "malformed comptime-match pattern") (SNone)))
                  ((Cons c craw fields)
                    (let (many env2) (many x) (var-of-raw (predates _) env xraw))
                    (let (many value) (match many (entry-state (predates _) env2 x) (((Value) v)) ((SConst v) v) ((SDyn) (VError "comptime-match on a Dyn"))))
                    (let (many env3) (many c) (named (predates _) env2 craw))
                    (let (many tele) (many ret) (ctor-type (predates _) env3 c))
                    (let (many i) (many vs)
                      (match many (ctor-of (predates _) env3 c) (((Nat) i) ((List (Value)) vs))
                        ((None d) (values 0 (Nil (Value))))
                        ((Some d ct) (destruct (predates _) ct value))))
                    (let (many env4)
                      (match many (ctor-of (predates _) env3 c) (((Env) e))
                        ((None d) (env-error (predates _) env3 "comptime-match: not a run-position constructor"))
                        ((Some d ct)
                          (match many (nat-eq (predates _) i (ctor-index (predates _) ct)) (((Env) e))
                            ((BTrue) env3)
                            ((BFalse) (env-error (predates _) env3 (str-cat (predates _) "comptime-match: expected " (name-of (predates _) env3 c))))))))
                    (let (many states) (states-of (predates _) (spread (predates _) (tele-mults (predates _) tele) vs)))
                    (let (many env5) (many fids) (open-tele (predates _) tele env4 (Some (List (Maybe (String))) (raw-names (predates _) fields)) (None (List (Mult))) (Some (List (State)) states) (Nil (Term))))
                    (let (many env6) (trace-many-fields (subterm _) k env5 fids))
                    (values (refine (predates _) env6 (res-of (predates _) env6 x) c fids ret) (SNone)))))))))))

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

  ; def-fns (sections 7, 27): headers bound Dyn, each body elaborated at the block's level, closures minted
  ; Const in run position.
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
                ((BFalse) (let (many env2) (many t) (elab-term (subterm _) k env lvraw)) (values env2 (level-var (predates _) env2 t)))))
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
            (match many (raw-items (predates _) f) _
              ((Nil b) (values (env-error (predates _) env "malformed function definition") (Nil (Header))))
              ((Cons b mraw items)
                (let (many mult) (mult-or (predates _) env mraw))
                (let (many isabs) (many isext) (many items2) (take-marks (predates _) items env (MkAbsurd) (MkExtern)))
                (match many items2 _
                  ((Nil c) (values (env-error (predates _) env "malformed function header") (Nil (Header))))
                  ((Cons c nraw items3)
                    (let (many name) (raw-name (predates _) nraw))
                    (let (many sg) (match many items3 (((List (Raw)) l)) ((Nil d) (Nil (Raw))) ((Cons d colon sg) sg)))
                    (let (many ps) (many after) (split-arrow (predates _) sg env))
                    (let (many rs) (many body) (split-returns (predates _) after env))
                    (let (many env2) (many ty) (elab-fn-type (subterm _) k env (TVar lvl) ps rs))
                    (let (many impl) (match many (and (predates _) isext (is-extern-fn (predates _) name)) (((Maybe (String)) i)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                    (let (many env3) (many hs) (elab-headers (subterm _) k env2 rest lvl))
                    (values env3 (Cons (Header) (MkHeader name mult isabs impl ty body) hs)))))))))))

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
                    (let (many envb) (many pids) (open-tele (predates _) params (env-set-run-pos (predates _) env (BFalse)) (None (List (Maybe (String)))) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                    (let (many envb2) (many code)
                      (match many isabs (((Env) e) ((Code) c))
                        ((BTrue) (values envb (CAbsurd)))
                        ((BFalse)
                          (let (many pvars) (tvars-rev (predates _) pids (Nil (Term))))
                          (let (many tele) (instantiate-tele (predates _) pvars rets))
                          (let (many envb2) (many ress) (many code) (elab-body (subterm _) k envb (under-list (predates _) (tele-mults (predates _) rets) mult) body (Some (List (Entry)) tele)))
                          (values envb2 (match many mult (((Code) c)) ((Erased) (CErased)) ((Many) code))))))
                    (let (many code2) (normalize (predates _) code))
                    (let (many env2) (env-discard (predates _) env envb2))
                    (let (many env3)
                      (match many (find-delegate (predates _) code2) (((Env) e))
                        ((None c) env2)
                        ((Some c callee)
                          (let (many env3) (many px) (bind (predates _) env2 (None (String)) (Erased) (SDyn) (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) (TVar x) (Cons (Term) (type-of (predates _) env2 callee) (Cons (Term) (TVar callee) (Nil (Term))))))) (None (Term)) coercible-id))
                          env3)))
                    (let (many fn) (MkFunc name x (non-erased (predates _) pids envb2) code2 impl top))
                    (let (many env4) (many fns) (define-fns (subterm _) k env3 hrest xrest lvl top))
                    (values env4 (Cons (Pair (Bin) (Func)) (MkPair (Bin) (Func) x fn) fns)))))))))))

  ; def-adts (sections 12, 19, 27): type constructors bound first, then each type's constructors,
  ; Matchable and Newtype.
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
            (match many (raw-items (predates _) adt) _
              ((Nil b) (values (env-error (predates _) env "malformed def-adts entry") (Nil (AdtHeader)) (Nil (Term))))
              ((Cons b nraw items)
                (let (many name) (raw-name (predates _) nraw))
                (let (many sg) (match many items (((List (Raw)) l)) ((Nil c) (Nil (Raw))) ((Cons c colon sg) sg)))
                (let (many ps) (many after) (split-arrow (predates _) sg env))
                (let (many disc) (many nt) (many ext) (many ctors)
                  (match many after (((Disc) d) ((Bool) n) ((Bool) e) ((List (Raw)) cs))
                    ((Nil c) (values (DEnum) (BFalse) (BFalse) (Nil (Raw))))
                    ((Cons c tyraw after2)
                      (match many after2 (((Disc) d) ((Bool) n) ((Bool) e) ((List (Raw)) cs))
                        ((Nil d) (values (DEnum) (BFalse) (BFalse) (Nil (Raw))))
                        ((Cons d draw after3)
                          (let (many nt) (many ext) (many cs) (take-marks (predates _) after3 env (MkNewtypeMark) (MkExtern)))
                          (values (disc-of (predates _) env draw) nt ext cs))))))
                (let (many env2) (many ty) (elab-tyctor (subterm _) k env ps))
                (let (many env3) (many hs) (many tys) (elab-adt-headers (subterm _) k env2 rest))
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
                    (let (many extname) (match many (and (predates _) ext (is-extern-type (predates _) name)) (((Maybe (String)) e)) ((BTrue) (Some (String) name)) ((BFalse) (None (String)))))
                    (let (many records) (ctor-records (predates _) (non-phantom (predates _) ss) env2 0 tagged extname))
                    (let (many adt) (MkAdt name tagged records extname))
                    (let (many cvals) (ctor-values (predates _) records))
                    (let (many env3) (many mid) (bind (predates _) env2 (None (String)) (Many) (SConst (VMatchable adt)) (TMatchable disc (TVar tid) mctors) (None (Term)) coercible-id))
                    (let (many env4)
                      (match many nt (((Env) e))
                        ((BFalse) env3)
                        ((BTrue)
                          (match many (wrapper (predates _) disc ss) (((Env) e))
                            ((None c) (env-error (predates _) env3 (str-cat (predates _) name " is not of newtype shape")))
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
            (match many (raw-items (predates _) craw) _
              ((Nil b) (values (env-error (predates _) env "malformed constructor") (Nil (Pair (Mult) (Bin)))))
              ((Cons b mraw items)
                (let (many mult) (mult-or (predates _) env mraw))
                (let (many name) (many sg) (match many items (((String) n) ((List (Raw)) l)) ((Nil c) (values "_" (Nil (Raw)))) ((Cons c nraw more) (values (raw-name (predates _) nraw) (match many more (((List (Raw)) l)) ((Nil d) (Nil (Raw))) ((Cons d colon sg) sg))))))
                (let (many env2) (many tele) (many ret) (many ty) (elab-valctor (subterm _) k env items))
                (let (many env3) (env-discard (predates _) env env2))
                (let (many st) (match many mult (((State) s)) ((Erased) (match many (env-run-pos (predates _) env3) (((State) s)) ((BTrue) (SConst (VToken))) ((BFalse) (SDyn)))) ((Many) (SDyn))))
                (let (many env4) (many c) (bind (predates _) env3 (Some (String) name) mult st ty (None (Term)) coercible-id))
                (let (many env5) (many cs) (elab-ctors (subterm _) k env4 rest tid))
                (values env5 (Cons (Pair (Mult) (Bin)) (MkPair (Mult) (Bin) mult c) cs)))))))))

  ; The special forms that are expressions (section 27).
  (many elab-special : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (Sp) sp) (many (List (Raw)) args) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (let (many pos) (pos-of (predates _) expect))
        (let (many m) (match many expect (((Mult) m)) ((Nil a) (Erased)) ((Cons a m1 rest) m1)))
        (match many sp _
          ((SpFormer fo)
            (let (many env2) (many t) (elab-type-form (subterm _) k env sp args))
            (values env2 (Cons (Res) (term-res (predates _) env2 t) (Nil (Res))) (CErased)))
          ((SpStmt st) (values (env-error (predates _) env "a statement is not an expression") (Nil (Res)) (CError "statement as expression")))
          ((SpMark mk)
            (match many mk _
              ((MkTail) (elab-marked (subterm _) k env expect args (CCTail)))
              ((MkDelegate) (elab-marked (subterm _) k env expect args (CCDelegate)))
              ((MkErased) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkMany) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkColon) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkIs) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkArrow) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkSubterm) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkEnum) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkUnion) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkPredates) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkAbsurd) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkNewtypeMark) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))
              ((MkExtern) (values (env-error (predates _) env "malformed form") (Nil (Res)) (CError "malformed")))))
          ((SpExpr ex)
            (match many ex _
              ((ExValues)
                (let (many env2) (many ress) (many codes) (elab-values (subterm _) k env expect args))
                (values env2 ress (code-of-values (predates _) codes pos)))
              ((ExMatch) (elab-match (subterm _) k env expect args tele))
              ((ExMatchableOf)
                (let (many env2) (many tid) (named (predates _) env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (match many (find-matchable (predates _) env2 tid) _
                  ((None a) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 tid) " has no Matchable in scope")) (Nil (Res)) (CError "no Matchable")))
                  ((Some a info) (match many info _ ((MkMatchInfo mid d cs rank) (values env2 (Cons (Res) (res-of (predates _) env2 mid) (Nil (Res))) (matchable-code (predates _) env2 m mid)))))))
              ((ExNewtypeOf)
                (let (many env2) (many c) (named (predates _) env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (match many (find-newtype (predates _) (env-objects (predates _) env2) env2 c) _
                  ((None a) (values (env-error (predates _) env2 "no Newtype in scope") (Nil (Res)) (CError "no Newtype")))
                  ((Some a x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))
              ((ExNumeralOf)
                (let (many env2) (many r) (mint (predates _) env (TErr "numeral-of is not modelled")))
                (values env2 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExLevelOf)
                (let (many env2) (many f) (elab-term (subterm _) k env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (match many (canon-env (predates _) env2 (infer (predates _) f env2)) _
                  ((TFn lv ps rs) (values env2 (Cons (Res) (MkRes lv level-term (Erased)) (Nil (Res))) (CErased)))
                  ((TVar y) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TBound j) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TApp h as) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TTyCtor p) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TValCtor p r) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TMatchable d t c) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TNewtype c) (values (env-error (predates _) env2 "level-of: not a function") (Nil (Res)) (CError "level-of")))
                  ((TErr msg) (values (env-error (predates _) env2 (str-cat (predates _) "level-of: " msg)) (Nil (Res)) (CError "level-of")))))
              ((ExProveSubterm)
                (let (many env2) (many a) (many b) (elab-two-terms (subterm _) k env args))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) subterm-id (Cons (Term) (infer (predates _) a env2) (Cons (Term) a (Cons (Term) (infer (predates _) b env2) (Cons (Term) b (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExProvePredates)
                (let (many env2) (many a) (many b) (elab-two-terms (subterm _) k env args))
                (let (many x) (level-var (predates _) env2 a))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) predates-id (Cons (Term) (type-of (predates _) env2 x) (Cons (Term) (TVar x) (Cons (Term) b (Nil (Term))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExPredatesTrans)
                (let (many env2) (many p) (many q) (elab-two-erased (subterm _) k env args))
                (let (many pa) (proof-args (predates _) env2 p))
                (let (many qa) (proof-args (predates _) env2 q))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) predates-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Nil (Term))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExSubtermTrans)
                (let (many env2) (many p) (many q) (elab-two-erased (subterm _) k env args))
                (let (many pa) (proof-args (predates _) env2 p))
                (let (many qa) (proof-args (predates _) env2 q))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) subterm-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Cons (Term) (nth-term (predates _) qa 3) (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleTrans)
                (let (many env2) (many p) (many q) (elab-two-erased (subterm _) k env args))
                (let (many pa) (proof-args (predates _) env2 p))
                (let (many qa) (proof-args (predates _) env2 q))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) coercible-id (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Cons (Term) (nth-term (predates _) qa 2) (Cons (Term) (nth-term (predates _) qa 3) (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExPredatesSubterm)
                (let (many env2) (many p) (many q) (elab-two-erased (subterm _) k env args))
                (let (many pa) (proof-args (predates _) env2 p))
                (let (many qa) (proof-args (predates _) env2 q))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) predates-id (Cons (Term) (nth-term (predates _) qa 0) (Cons (Term) (nth-term (predates _) qa 1) (Cons (Term) (nth-term (predates _) pa 2) (Nil (Term))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoerce)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed coerce") (Nil (Res)) (CError "coerce")))
                  ((Cons a araw rest)
                    (let (many env2) (many ar) (many code) (elab-expr1 (subterm _) k env m araw))
                    (let (many env3) (many p) (match many rest (((Env) e) ((Term) t)) ((Nil b) (values env2 (TErr "missing proof"))) ((Cons b praw more) (elab-erased (subterm _) k env2 praw))))
                    (let (many pa) (proof-args (predates _) env3 p))
                    (let (many env4) (many x) (bind (predates _) env3 (None (String)) m (SDyn) (nth-term (predates _) pa 2) (Some (Term) (nth-term (predates _) pa 3)) coercible-id))
                    (values env4 (Cons (Res) (res-of (predates _) env4 x) (Nil (Res))) code))))
              ((ExCoercibleRefl)
                (let (many env2) (many e) (elab-term (subterm _) k env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (let (many ty) (infer (predates _) e env2))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) coercible-id (Cons (Term) ty (Cons (Term) e (Cons (Term) ty (Cons (Term) e (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleSym)
                (let (many env2) (many p) (elab-erased (subterm _) k env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (let (many pa) (proof-args (predates _) env2 p))
                (let (many env3) (many r) (mint (predates _) env2 (proof-type (predates _) coercible-id (Cons (Term) (nth-term (predates _) pa 2) (Cons (Term) (nth-term (predates _) pa 3) (Cons (Term) (nth-term (predates _) pa 0) (Cons (Term) (nth-term (predates _) pa 1) (Nil (Term)))))))))
                (values env3 (Cons (Res) r (Nil (Res))) (CErased)))
              ((ExCoercibleWrap)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed coercible-wrap") (Nil (Res)) (CError "coercible-wrap")))
                  ((Cons a craw wargs)
                    (let (many env2) (many c) (named (predates _) env craw))
                    (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
                    (let (many env3) (many acc) (elab-term-args (subterm _) k env2 ctele wargs (Nil (Term))))
                    (let (many f) (field-at-many-fuel (subterm _) k ctele (list-rev (predates _) (Term) acc)))
                    (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) (infer (predates _) f env3) (Cons (Term) f (Cons (Term) (instantiate (predates _) acc ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) acc)) (Nil (Term)))))))))
                    (values env4 (Cons (Res) r (Nil (Res))) (CErased)))))
              ((ExCoercibleCtor)
                (match many args _
                  ((Nil a) (values (env-error (predates _) env "malformed coercible-ctor") (Nil (Res)) (CError "coercible-ctor")))
                  ((Cons a craw cargs)
                    (let (many env2) (many c) (named (predates _) env craw))
                    (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
                    (let (many env3) (many src) (many tgt) (coercible-ctor-args (subterm _) k env2 ctele cargs (Nil (Term)) (Nil (Term))))
                    (let (many env4) (many r) (mint (predates _) env3 (proof-type (predates _) coercible-id (Cons (Term) (instantiate (predates _) src ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) src)) (Cons (Term) (instantiate (predates _) tgt ret) (Cons (Term) (TApp (TVar c) (list-rev (predates _) (Term) tgt)) (Nil (Term)))))))))
                    (values env4 (Cons (Res) r (Nil (Res))) (CErased)))))
              ((ExCoercibleOf)
                (let (many env2) (many g) (named (predates _) env (match many args (((Raw) r)) ((Nil a) (RAtom "_")) ((Cons a t rest) t))))
                (match many (find-coercible (predates _) (env-objects (predates _) env2) env2 g) _
                  ((None a) (values (env-error (predates _) env2 (str-cat (predates _) (name-of (predates _) env2 g) " has no delegate proof in scope")) (Nil (Res)) (CError "no delegate proof")))
                  ((Some a x) (values env2 (Cons (Res) (res-of (predates _) env2 x) (Nil (Res))) (CErased)))))))))))

  (many elab-marked : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) (many (CC) cc) -> (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (match many args _
          ((Nil a) (values (env-error (predates _) env "a mark needs a call") (Nil (Res)) (CError "mark")))
          ((Cons a call rest) (elab-expr (subterm _) k env expect call (None (List (Entry))) cc))))))

  (many elab-values : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) -> (many (Env) r) (many (List (Res)) ress) (many (List (Code)) codes)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (Nil (Code))))
      ((Succ k)
        (match many expect _
          ((Nil a) (values env (Nil (Res)) (Nil (Code))))
          ((Cons a m mrest)
            (match many args _
              ((Nil b) (values (env-error (predates _) env "too few values") (Nil (Res)) (Nil (Code))))
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

  (many elab-two-erased : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) args) -> (many (Env) r) (many (Term) a) (many (Term) b)
    (match many fuel _
      ((Zero) (values env (TErr "out of fuel") (TErr "out of fuel")))
      ((Succ k)
        (match many args _
          ((Nil x) (values (env-error (predates _) env "two proofs expected") (TErr "missing") (TErr "missing")))
          ((Cons x araw rest)
            (match many rest _
              ((Nil y) (values (env-error (predates _) env "two proofs expected") (TErr "missing") (TErr "missing")))
              ((Cons y braw more)
                (let (many env2) (many a) (elab-erased (subterm _) k env araw))
                (let (many env3) (many b) (elab-erased (subterm _) k env2 braw))
                (values env3 a b))))))))

  ; coercible-ctor's arguments: two terms per erased field, one proof per many field (section 38).
  (many coercible-ctor-args : (subterm many (Nat) fuel) (many (Env) env) (many (List (Entry)) tele) (many (List (Raw)) args) (many (List (Term)) src) (many (List (Term)) tgt) -> (many (Env) r) (many (List (Term)) src2) (many (List (Term)) tgt2)
    (match many fuel _
      ((Zero) (values env src tgt))
      ((Succ k)
        (match many tele _
          ((Nil a) (values env src tgt))
          ((Cons a e rest)
            (match many (entry-mult (predates _) e) _
              ((Erased)
                (let (many env2) (many s) (many t) (elab-two-terms (subterm _) k env args))
                (let (many args2) (match many args (((List (Raw)) l)) ((Nil b) args) ((Cons b x more) (match many more (((List (Raw)) l)) ((Nil c) more) ((Cons c y more2) more2)))))
                (coercible-ctor-args (subterm _) k env2 rest args2 (Cons (Term) s src) (Cons (Term) t tgt)))
              ((Many)
                (match many args _
                  ((Nil b) (values (env-error (predates _) env "coercible-ctor: too few arguments") src tgt))
                  ((Cons b praw more)
                    (let (many env2) (many p) (elab-erased (subterm _) k env praw))
                    (let (many pa) (proof-args (predates _) env2 p))
                    (coercible-ctor-args (subterm _) k env2 rest more (Cons (Term) (nth-term (predates _) pa 1) src) (Cons (Term) (nth-term (predates _) pa 3) tgt)))))))))))

  ; match (sections 11, 12): the scrutinee, its Matchable, the annotation, then one branch per constructor.
  (many elab-match : (subterm many (Nat) fuel) (many (Env) env) (many (List (Mult)) expect) (many (List (Raw)) args) (many (Maybe (List (Entry))) tele) ->
      (many (Env) r) (many (List (Res)) ress) (many (Code) code)
    (match many fuel _
      ((Zero) (values env (Nil (Res)) (CError "out of fuel")))
      ((Succ k)
        (match many args _
          ((Nil a) (values (env-error (predates _) env "malformed match") (Nil (Res)) (CError "match")))
          ((Cons a mraw rest)
            (match many rest _
              ((Nil b) (values (env-error (predates _) env "malformed match") (Nil (Res)) (CError "match")))
              ((Cons b scrut rest2)
                (match many rest2 _
                  ((Nil c) (values (env-error (predates _) env "malformed match") (Nil (Res)) (CError "match")))
                  ((Cons c ann branches)
                    (let (many pos) (pos-of (predates _) expect))
                    (let (many smult) (under (predates _) pos (mult-or (predates _) env mraw)))
                    (let (many env2) (many sres) (many scode) (elab-expr1 (subterm _) k env smult scrut))
                    (let (many tid) (match many (type-head (predates _) env2 (res-ty (predates _) sres)) (((Bin) t)) ((None d) (BZ)) ((Some d t) t)))
                    (match many (find-matchable (predates _) env2 tid) _
                      ((None d) (values (env-error (predates _) env2 (str-cat (predates _) "cannot match: no Matchable for the type of " (str-cat (predates _) (raw-name (predates _) scrut) (str-cat (predates _) " : " (rope-str (predates _) (show-term (predates _) (res-ty (predates _) sres) env2)))))) (Nil (Res)) (CError "no Matchable")))
                      ((Some d info)
                        (match many info _
                          ((MkMatchInfo mid disc mctors rank)
                            (let (many ss) (shapes (predates _) mctors env2))
                            (let (many tagged) (tagged-of (predates _) disc ss))
                            (let (many env3) (many ann-tele)
                              (match many (is-underscore (predates _) ann) (((Env) e) ((List (Entry)) t))
                                ((BTrue) (values env2 (match many tele (((List (Entry)) t)) ((None e) (Nil (Entry))) ((Some e t) t))))
                                ((BFalse)
                                  (let (many env3) (many ids) (many t) (elab-tele (subterm _) k env2 (raw-items (predates _) ann) (MMExpect expect) (Nil (Term))))
                                  (values (env-discard (predates _) env2 env3) t))))
                            (let (many env4) (many rids) (open-tele (predates _) ann-tele env3 (Some (List (Maybe (String))) (anon-names (predates _) ann-tele)) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                            (let (many env5) (many real) (elab-branches (subterm _) k env4 branches sres smult mctors ann-tele expect (Nil (RealBranch))))
                            (let (many code)
                              (match many pos (((Code) c))
                                ((Erased) (CErased))
                                ((Many)
                                  (match many real (((Code) c))
                                    ((Nil e) (CAbsurd))
                                    ((Cons e rb more)
                                      (match many (and (predates _) (not (predates _) (mult-is-many (predates _) smult)) (list-is-empty (predates _) (RealBranch) more)) (((Code) c))
                                        ((BTrue) (match many rb (((Code) c)) ((MkRealBranch cc fids body) body)))
                                        ((BFalse) (CMatch scode (match-shape (predates _) env5 mid tagged) (real-branches-code (predates _) real ss)))))))))
                            (values env5 (ress-of (predates _) rids env5) code))))))))))))))

  (many elab-branches : (subterm many (Nat) fuel) (many (Env) env) (many (List (Raw)) branches) (many (Res) sres) (many (Mult) smult) (many (List (MCtor)) mctors) (many (List (Entry)) ann-tele) (many (List (Mult)) expect) (many (List (RealBranch)) acc) ->
      (many (Env) r) (many (List (RealBranch)) real)
    (match many fuel _
      ((Zero) (values env (list-rev (predates _) (RealBranch) acc)))
      ((Succ k)
        (match many branches _
          ((Nil a) (values env (list-rev (predates _) (RealBranch) acc)))
          ((Cons a braw brest)
            (let (many items) (raw-items (predates _) braw))
            (let (many kind) (many pat) (many body)
              (match many items (((Nat) kind) ((Raw) p) ((List (Raw)) b))
                ((Nil b) (values 0 (RAtom "_") (Nil (Raw))))
                ((Cons b first more)
                  (match many (is-mark (predates _) env first (MkAbsurd)) (((Nat) kind) ((Raw) p) ((List (Raw)) b))
                    ((BFalse) (values 0 first more))
                    ((BTrue)
                      (match many more (((Nat) kind) ((Raw) p) ((List (Raw)) b))
                        ((Nil c) (values 1 (RAtom "_") (Nil (Raw))))
                        ((Cons c pat body2)
                          (match many body2 (((Nat) kind) ((Raw) p) ((List (Raw)) b))
                            ((Nil d) (values 1 pat (Nil (Raw))))
                            ((Cons d x y) (values 2 pat body2))))))))))
            (let (many craw) (many fields) (match many pat (((Raw) c) ((List (Raw)) f)) ((RAtom s) (values pat (Nil (Raw)))) ((RString s) (values pat (Nil (Raw)))) ((RList pitems) (match many pitems (((Raw) c) ((List (Raw)) f)) ((Nil b) (values pat (Nil (Raw)))) ((Cons b c f) (values c f))))))
            (let (many env2) (many c) (named (predates _) env craw))
            (let (many phantom) (match many (marker (predates _) mctors c) (((Bool) b)) ((Erased) (BTrue)) ((Many) (BFalse))))
            (let (many ctele) (many ret) (ctor-type (predates _) env2 c))
            (let (many unreachable) (and (predates _) phantom (mult-is-many (predates _) smult)))
            (let (many skip) (or (predates _) unreachable (not (predates _) (nat-is-zero (predates _) kind))))
            (match many skip _
              ((BTrue) (elab-branches (subterm _) k env2 brest sres smult mctors ann-tele expect acc))
              ((BFalse)
                (let (many mults) (match many phantom (((List (Mult)) ms)) ((BTrue) (all-erased (predates _) (tele-mults (predates _) ctele))) ((BFalse) (under-list (predates _) (tele-mults (predates _) ctele) smult))))
                (let (many envb) (many fids) (open-tele (predates _) ctele (env-set-run-pos (predates _) env2 (BFalse)) (Some (List (Maybe (String))) (raw-names (predates _) fields)) (Some (List (Mult)) mults) (None (List (State))) (Nil (Term))))
                (let (many envb2) (refine (predates _) envb sres c fids ret))
                (let (many envb3) (many ress) (many code) (elab-body (subterm _) k envb2 expect body (Some (List (Entry)) ann-tele)))
                (let (many env3) (env-discard (predates _) env2 envb3))
                (elab-branches (subterm _) k env3 brest sres smult mctors ann-tele expect (Cons (RealBranch) (MkRealBranch c (non-erased (predates _) fids envb3) code) acc)))))))))

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

; ---- The top level (section 16): statements run as they are elaborated, the final expression consumed.

(def-fns _ $ many run-toplevel : (subterm many (List (Raw)) items) (many (Env) env) -> (many (Env) r)
  (match many items _
    ((Nil a) env)
    ((Cons a item rest)
      (let (many env2) (intern-literals (predates _) item env))
      (match many (and (predates _) (list-is-empty (predates _) (Raw) rest) (not (predates _) (is-statement (predates _) env2 item))) _
        ((BTrue)
          (let (many env3) (many ress) (many code) (elab-expr (predates _) elab-fuel env2 (Cons (Mult) (Many) (Nil (Mult))) item (None (List (Entry))) (CCPlain)))
          (let (many v) (first-value (predates _) (run-code (predates _) env3 code)))
          (env-push-trace (predates _) env3 (TrFinal v (res-ty (predates _) (first-res (predates _) ress)))))
        ((BFalse)
          (let (many env3) (many sc) (elab-stmt (predates _) elab-fuel env2 item))
          (run-toplevel (subterm _) rest env3))))))
