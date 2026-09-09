; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code, bounded by a fuel that decreases along the call stack so the checker
; accepts it. Extern functions run as the host's own (section 41).

(let (many nat-adt) $ MkAdt "Nat" (BTrue) (Nil _) $ Some _ "Nat")
(let (many dec-adt) $ MkAdt "Dec" (BTrue) (Nil _) $ Some _ "Dec")
(let (many str-adt) $ MkAdt "String" (BTrue) (Nil _) $ Some _ "String")

(def-fns _ $ many vnat : (many (Nat) n) -> (many (Value) v)
  (VExt nat-adt $ PNat n))

(def-fns _ $ many arg-at : (many (List $ Value) args) (many (Nat) i) -> (many (Value) v)
  (match many (list-nth _ args i) _
    ((None a) (VError "extern arity"))
    ((Some a v) v)))

(def-fns _ $ many is-extern-fn : (many (String) name) -> (many (Bool) r)
  (or (str-eq name "nat-add")
    (or (str-eq name "lt-dec")
      (or (str-eq name "u8-add")
        $ or (str-eq name "bin-to-nat") $ str-eq name "trim"))))

(def-fns _ $ many is-extern-type : (many (String) name) -> (many (Bool) r)
  (or (str-eq name "Nat")
    (or (str-eq name "Bin")
      $ or (str-eq name "String") $ str-eq name "Dec")))

; A U8 is its Nat at runtime (section 38), so the prelude's u8-add takes both back under the modulus first.
(def-fns _ $ many u8-add-value : (many (Nat) a) (many (Nat) b) -> (many (Value) v)
  (match many (lt-dec a u8-modulus) _
    ((No x y q) (VError "u8-add: not a U8"))
    ((Yes x y pa)
      (match many (lt-dec b u8-modulus) _
        ((No x2 y2 q2) (VError "u8-add: not a U8"))
        ((Yes x2 y2 pb)
          (let (many s) $ u8-add (MkU8 a pa) $ MkU8 b pb)
          (let-match many s (MkU8 sn sq))
          (vnat sn))))))

(def-fns _ $ many apply-extern : (many (String) name) (many (List $ Value) args) -> (many (List $ Value) r)
  (let (many a) $ arg-at args 0)
  (let (many b) $ arg-at args 1)
  (match many (str-eq name "nat-add") _
    ((BTrue) (Cons _ (vnat $ nat-add (value-nat a) $ value-nat b) $ Nil _))
    ((BFalse)
      (match many (str-eq name "lt-dec") _
        ((BTrue) (Cons _ (VExt dec-adt $ PDec $ match many (nat-lt (value-nat a) $ value-nat b) (((Nat) i)) ((BTrue) 0) ((BFalse) 1)) $ Nil _))
        ((BFalse)
          (match many (str-eq name "u8-add") _
            ((BTrue) (Cons _ (u8-add-value (value-nat a) $ value-nat b) $ Nil _))
            ((BFalse)
              (match many (str-eq name "bin-to-nat") _
                ((BTrue)
                  (let (many n) (erased pf) $ bin-to-nat $ value-bin a)
                  (Cons _ (vnat n) $ Nil _))
                ((BFalse) (Cons _ (VExt str-adt $ PStr $ trim $ value-str a) $ Nil _))))))))))

(def-fns _ $ many venv-bind : (subterm many (List $ Bin) ids) (many (List $ Value) vs) (many (IdMap $ Value) env) -> (many (IdMap $ Value) r)
  (match many ids _
    ((Nil a) env)
    ((Cons a x rest)
      (match many vs _
        ((Nil b) (idmap-set _ x (VError "arity mismatch") env))
        ((Cons b v vrest) (venv-bind rest vrest $ idmap-set _ x v env))))))

; Adds the closures of a def-fns group to [env]; each closure re-closes the whole group when applied.
(def-fns _ $ many close-fns : (subterm many (List $ Pair (Bin) $ Func) group) (many (List $ Pair (Bin) $ Func) whole) (many (IdMap $ Value) env) -> (many (List $ Pair (Bin) $ Value) r)
  (match many group _
    ((Nil a) (Nil _))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (let (many v) $ VFn $ MkClosure fn whole env)
          (Cons _ (MkPair _ _ id v) $ close-fns rest whole $ idmap-set _ id v env))))))

(def-fns _ $ many venv-set-all : (subterm many (List $ Pair (Bin) $ Value) vs) (many (IdMap $ Value) env) -> (many (IdMap $ Value) r)
  (match many vs _
    ((Nil a) env)
    ((Cons a p rest) (match many p _ ((MkPair x y id v) (venv-set-all rest $ idmap-set _ id v env))))))

(def-fns _ $ many close-group : (many (List $ Pair (Bin) $ Func) group) (many (List $ Pair (Bin) $ Func) whole) (many (IdMap $ Value) env) -> (many (IdMap $ Value) r)
  (venv-set-all (close-fns group whole env) env))

(def-fns _ $ many find-branch : (subterm many (List $ Branch) bs) (many (Nat) i) -> (many (Maybe $ Branch) r)
  (match many bs _
    ((Nil a) (None _))
    ((Cons a b rest)
      (match many b _
        ((MkBranch d ids body)
          (match many (nat-eq d i) _
            ((BTrue) (Some _ b))
            ((BFalse) (find-branch rest i))))))))

(def-fns _ $ many first-value : (many (List $ Value) vs) -> (many (Value) v)
  (match many vs _
    ((Nil a) (VError "expected one value"))
    ((Cons a v rest) v)))

(def-fns _ $ many has-branch : (subterm many (List $ Branch) bs) (many (Nat) i) -> (many (Bool) r)
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch d ids body) (or (nat-eq d i) $ has-branch rest i))))))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (subterm many (Code) code) (many (IdMap $ Value) env) -> (many (List $ Value) vs)
    (match many code _
      ((CVar x)
        (match many (idmap-get _ x env) _
          ((None a) (Cons _ (VError $ str-cat "unbound at runtime: " $ bin-str x) $ Nil _))
          ((Some a v) (Cons _ v $ Nil _))))
      ((CConst v) (Cons _ v $ Nil _))
      ((CErased) (Cons _ (VToken) $ Nil _))
      ((CValues cs) (eval-list fuel cs env))
      ((CApp f args cc)
        (let (many fv) $ first-value $ eval fuel f env)
        (let (many avs) $ eval-list fuel args env)
        (match many fuel _
          ((Zero) (Cons _ (VError "out of fuel") $ Nil _))
          ((Succ k) (apply k fv avs))))
      ((CLet ids rhs rest)
        (let (many vs) $ eval fuel rhs env)
        (eval fuel rest $ venv-bind ids vs env))
      ((CLetRec fns rest) (eval fuel rest $ close-group fns fns env))
      ((CMatch scrut shape branches dfl)
        (let (many v) $ first-value $ eval fuel scrut env)
        (let (many read)
          (match many shape (((Maybe $ Pair (Nat) $ List $ Value) r))
            ((ShKnown adt) (dispatch (adt-ext adt) (adt-tagged adt) v))
            ((ShHeld mcode tags)
              (match many (first-value $ eval fuel mcode env) (((Maybe $ Pair (Nat) $ List $ Value) r))
                ((VMatchable a) (dispatch (adt-ext a) tags v)) (else (None $ Pair (Nat) $ List $ Value))))))
        (match many read _
          ((Some a p)
            (match many p _
              ((MkPair x y i fields)
                (match many (has-branch branches i) _
                  ((BTrue) (eval-branch fuel branches i fields env))
                  ((BFalse) (match many dfl _ ((Some b d) (eval fuel d env)) ((None b) (eval-branch fuel branches i fields env))))))))
          ((None a)
            (match many branches _
              ((Nil b) (match many dfl _ ((Some c d) (eval fuel d env)) ((None c) (Cons _ (VError "no branch") $ Nil _))))
              ((Cons b br rest)
                (match many br _
                  ((MkBranch d ids body) (eval fuel body $ venv-bind ids (untuple (list-length _ ids) v) env))))))))
      ((CAbsurd) (Cons _ (VError "absurd code reached") $ Nil _))
      ((CError m) (Cons _ (VError m) $ Nil _))))
  (many eval-list : (subterm many (Nat) fuel) (subterm many (List $ Code) cs) (many (IdMap $ Value) env) -> (many (List $ Value) vs)
    (match many cs _
      ((Nil a) (Nil _))
      ((Cons a c rest) (Cons _ (first-value $ eval fuel c env) $ eval-list fuel rest env))))
  (many eval-branch : (subterm many (Nat) fuel) (subterm many (List $ Branch) bs) (many (Nat) i) (many (List $ Value) fields) (many (IdMap $ Value) env) -> (many (List $ Value) vs)
    (match many bs _
      ((Nil a) (Cons _ (VError $ str-cat "no branch for discriminant " $ nat-str i) $ Nil _))
      ((Cons a b rest)
        (match many b _
          ((MkBranch d ids body)
            (match many (nat-eq d i) _
              ((BTrue) (eval fuel body $ venv-bind ids fields env))
              ((BFalse) (eval-branch fuel rest i fields env))))))))
  (many apply : (subterm many (Nat) fuel) (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
    (match many f _
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many fn _
              ((MkFunc name id params body impl top)
                (let (many ext) $ match many impl (((Bool) b)) ((None a) (BFalse)) ((Some a n) (is-extern-fn n)))
                (match many ext _
                  ((BTrue) (apply-extern (match many impl (((String) s)) ((None a) (SNil)) ((Some a n) n)) args))
                  ((BFalse)
                    (match many fuel _
                      ((Zero) (Cons _ (VError "out of fuel") $ Nil _))
                      ((Succ k) (eval k body $ venv-bind params args $ close-group group group cenv))))))))))
      ((VCtorFn c) (Cons _ (construct c args) $ Nil _))
      ((VCtor c fs) (Cons _ (VError "cannot apply a constructor value") $ Nil _))
      ((VTuple fs) (Cons _ (VError "cannot apply a tuple") $ Nil _))
      ((VExt a p) (Cons _ (VError "cannot apply an extern value") $ Nil _))
      ((VMatchable a) (Cons _ (VError "cannot apply a Matchable") $ Nil _))
      ((VToken) (Cons _ (VError "cannot apply the token") $ Nil _))
      ((VError m) (Cons _ (VError m) $ Nil _)))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (many (Env) env) (many (Code) code) -> (many (List $ Value) vs)
  (eval eval-fuel code $ env-values env))

(def-fns _ $ many apply-value : (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
  (apply eval-fuel f args))
