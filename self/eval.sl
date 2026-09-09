; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code, bounded by a fuel that decreases along the call stack so the checker
; accepts it. Extern functions run as the host's own (section 41).

(let (many nat-adt) $ MkAdt "Nat" (BTrue) (Nil _) $ Some _ "Nat")
(let (many cmp-adt) $ MkAdt "Cmp" (BTrue) (Nil _) $ Some _ "Cmp")
(let (many str-adt) $ MkAdt "String" (BTrue) (Nil _) $ Some _ "String")

(def-fns _ $ many vnat : (many (Nat) n) -> (many (Value) v)
  (VExt nat-adt $ PNat n))

(def-fns _ $ many arg-at : (many (List $ Value) args) (many (Nat) i) -> (many (Value) v)
  (match many (list-nth _ args i) _
    ((NthMiss nt nl ni np) (VError "extern arity"))
    ((NthHit nt nl ni v np) v)))

(def-fns _ $ many is-extern-fn : (many (String) name) -> (many (Bool) r)
  (or (str-eq name "add")
    (or (str-eq name "nat-cmp")
      (or (str-eq name "nat-mod")
        $ or (str-eq name "bin-to-nat") $ str-eq name "trim"))))

(def-fns _ $ many is-extern-type : (many (String) name) -> (many (Bool) r)
  (or (str-eq name "Nat")
    (or (str-eq name "Bin")
      $ or (str-eq name "String") $ str-eq name "Cmp")))

(def-fns _ $ many nat-mod-value : (many (Nat) s) (many (Nat) c) -> (many (Value) v)
  (match many (lt-dec (Zero) c) _
    ((Yes x y pos)
      (let (many m) (erased p) (erased q) $ nat-mod s c pos)
      (vnat m))
    ((No x y q) (VError "nat-mod: zero modulus"))))

(def-fns _ $ many apply-extern : (many (String) name) (many (List $ Value) args) -> (many (List $ Value) r)
  (let (many a) $ arg-at args 0)
  (let (many b) $ arg-at args 1)
  (match many (str-cmp name "add") _
    ((CEq eq-t eq-r eq-x) (Cons _ (vnat $ nat-add (value-nat a) $ value-nat b) $ Nil _))
    (else
      (match many (str-cmp name "nat-cmp") _
        ((CEq eq-t eq-r eq-x)
          (let (many x) $ value-nat a)
          (let (many y) $ value-nat b)
          (Cons _ (VExt cmp-adt $ PDec $ match many (nat-lt x y) (((Nat) i)) ((BTrue) 0) ((BFalse) (match many (nat-lt y x) _ ((BTrue) 2) ((BFalse) 1)))) $ Nil _))
        (else
          (match many (str-cmp name "nat-mod") _
            ((CEq eq-t eq-r eq-x) (Cons _ (nat-mod-value (value-nat a) $ value-nat b) $ Nil _))
            (else
              (match many (str-cmp name "bin-to-nat") _
                ((CEq eq-t eq-r eq-x)
                  (let (many n) (erased pf) $ bin-to-nat $ value-bin a)
                  (Cons _ (vnat n) $ Nil _))
                (else (Cons _ (VExt str-adt $ PStr $ trim $ value-str a) $ Nil _))))))))))

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
          (match many (nat-cmp d i) _
            ((CEq eq-t eq-r eq-x) (Some _ b))
            (else (find-branch rest i))))))))

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
          ((Miss lt lk lm lp) (Cons _ (VError $ str-cat "unbound at runtime: " $ bin-str x) $ Nil _))
          ((Hit lt lk lm v lp) (Cons _ v $ Nil _))))
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
        (let (many (Maybe $ Pair (Nat) $ List $ Value) read)
          (match many shape _
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
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x) (eval fuel body $ venv-bind ids fields env))
              (else (eval-branch fuel rest i fields env))))))))
  (many apply : (subterm many (Nat) fuel) (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
    (match many f _
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many fn _
              ((MkFunc name id params body impl top)
                (let (many (Bool) ext) $ match many impl _ ((None a) (BFalse)) ((Some a n) (is-extern-fn n)))
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
