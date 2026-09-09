; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code, bounded by a fuel that decreases along the call stack so the checker
; accepts it. Extern functions run as the host's own (section 41).

(let (many nat-adt) $ MkAdt "Nat" (BTrue) (Nil _) $ Some _ "Nat")
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
        $ or (str-eq name "bin-to-nat") $ or (str-eq name "trim") $ or (str-eq name "append") $ str-eq name "flatten"))))

(def-fns _ $ many is-extern-type : (many (String) name) -> (many (Bool) r)
  (or (str-eq name "Nat")
    (or (str-eq name "Bin")
      $ str-eq name "String")))

(def-fns _ $ many nat-mod-value : (many (Nat) s) (many (Nat) c) -> (many (Value) v)
  (match many (lt-dec (Zero) c) _
    ((Yes x y pos)
      (let (many m) (erased p) (erased q) $ nat-mod s c pos)
      (vnat m))
    ((No x y q) (VError "nat-mod: zero modulus"))))

(def-fns _ $ many value-rope : (subterm many (Value) v) -> (many (Rope) r)
  (match many v _
    ((VCtor c fields)
      (match many fields _
        ((Nil a) (REmpty))
        ((Cons a f rest)
          (match many rest _
            ((Nil b)
              (match many f _
                ((VExt adt p) (match many p _ ((PStr s) (RStr s)) ((PNat n) (RChar $ char-of-code n)) (else (REmpty))))
                (else (REmpty))))
            ((Cons b g rest2) (RCat (value-rope f) $ value-rope g))))))
    (else (REmpty))))

(def-fns _ $ many flatten-value : (many (Value) v) -> (many (String) s)
  (let (many s) (erased p) $ flatten $ value-rope v)
  s)

(def-fns _ $ many apply-extern : (many (String) name) (many (List $ Value) args) -> (many (List $ Value) r)
  (let (many a) $ arg-at args 0)
  (let (many b) $ arg-at args 1)
  (match many (str-cmp name "add") _
    ((CEq eq-t eq-r eq-x) (Cons _ (vnat $ nat-add (value-nat a) $ value-nat b) $ Nil _))
    (else
      (match many (str-cmp name "nat-cmp") _
        ((CEq eq-t eq-r eq-x) (Cons _ (VError "nat-cmp runs as its model at compile time") $ Nil _))
        (else
          (match many (str-cmp name "nat-mod") _
            ((CEq eq-t eq-r eq-x) (Cons _ (nat-mod-value (value-nat a) $ value-nat b) $ Nil _))
            (else
              (match many (str-cmp name "bin-to-nat") _
                ((CEq eq-t eq-r eq-x)
                  (let (many n) (erased pf) $ bin-to-nat $ value-bin a)
                  (Cons _ (vnat n) $ Nil _))
                (else
                  (match many (str-cmp name "trim") _
                    ((CEq eq-t eq-r eq-x) (Cons _ (VExt str-adt $ PStr $ trim $ value-str a) $ Nil _))
                    (else
                      (match many (str-cmp name "append") _
                        ((CEq eq-t eq-r eq-x) (Cons _ (VExt str-adt $ PStr $ str-append (value-str a) $ value-str b) $ Nil _))
                        (else (Cons _ (VExt str-adt $ PStr $ flatten-value a) $ Nil _))))))))))))))

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

(def-fns _ $ many vals-of : (subterm many (List $ Mult) ms) (many (Value) v) -> (many (Vals ms) r)
  (match many ms _
    ((Nil a) (ValsNil))
    ((Cons a m rest) (match many m _ ((Many) (ValsMany _ v $ vals-of rest v)) ((Erased) (ValsErased _ $ vals-of rest v))))))

(def-fns _ $ many vals-fit : (subterm many (List $ Mult) ms) (many (List $ Value) vs) -> (many (Vals ms) r)
  (match many ms _
    ((Nil a) (ValsNil))
    ((Cons a m rest)
      (match many m _
        ((Erased) (ValsErased _ $ vals-fit rest vs))
        ((Many)
          (match many vs _
            ((Nil b) (ValsMany _ (VError "arity mismatch") $ vals-fit rest vs))
            ((Cons b v vrest) (ValsMany _ v $ vals-fit rest vrest))))))))

(def-fns _ $ many vals-list : (erased (List $ Mult) ms) (subterm many (Vals ms) vs) -> (many (List $ Value) r)
  (match many vs _
    ((ValsNil) (Nil _))
    ((ValsMany m v rest) (Cons _ v $ vals-list _ rest))
    ((ValsErased m rest) (vals-list _ rest))))

(def-fns _ $ many vals-spread : (erased (List $ Mult) ms) (subterm many (Vals ms) vs) -> (many (List $ Value) r) (erased (Lockstep (Mult) (Value) ms r) lock)
  (match many vs _
    ((ValsNil) (values (Nil _) (LsNil _ _)))
    ((ValsMany m v rest)
      (let (many r) (erased p) $ vals-spread _ rest)
      (values (Cons _ v r) (LsCons _ _ (Many) v m r p)))
    ((ValsErased m rest)
      (let (many r) (erased p) $ vals-spread _ rest)
      (values (Cons _ (VToken) r) (LsCons _ _ (Erased) (VToken) m r p)))))

(def-fns _ $ many vals-one : (many (Vals many-one) vs) -> (many (Value) v)
  (match many vs _ ((ValsMany m v rest) v)))

(def-fns _ $ many venv-bind-picked : (erased (List $ Mult) ms) (many (List $ Bin) ids) (erased (Picked (Bin) ms ids) pk) (subterm many (Vals ms) vs) (many (IdMap $ Value) env) -> (many (IdMap $ Value) r)
  (match many vs _
    ((ValsNil) env)
    ((ValsMany m v rest)
      (match erased pk _
        ((PkMany ta ms2 x xs p) (match many ids _ ((Cons a y idrest) (venv-bind-picked _ idrest p rest $ idmap-set _ y v env))))))
    ((ValsErased m rest)
      (match erased pk _
        ((PkErased ta ms2 xs p) (venv-bind-picked _ ids p rest env))))))

(def-fns _ $ many has-branch : (erased (List $ Mult) ns) (subterm many (List $ Branch ns) bs) (many (Nat) i) -> (many (Bool) r)
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch n0 d ids body) (or (nat-eq d i) $ has-branch _ rest i))))))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (erased (List $ Mult) ms) (subterm many (Code ms) code) (many (IdMap $ Value) env) -> (many (Vals ms) vs)
    (match many code _
      ((CVar x)
        (match many (idmap-get _ x env) _
          ((Miss lt lk lm lp) (ValsMany _ (VError $ str-cat "unbound at runtime: " $ bin-str x) $ ValsNil))
          ((Hit lt lk lm v lp) (ValsMany _ v $ ValsNil))))
      ((CConst v) (ValsMany _ v $ ValsNil))
      ((CErased ms2) (vals-of ms2 $ VToken))
      ((CValues ms2 cs pk) (eval-picked fuel cs ms2 pk env))
      ((CApp ms2 f args cc)
        (let (many fv) $ vals-one $ eval fuel _ f env)
        (let (many avs) $ eval-list fuel args env)
        (match many fuel _
          ((Zero) (vals-of ms2 $ VError "out of fuel"))
          ((Succ k) (vals-fit ms2 $ apply k fv avs))))
      ((CLet ms2 ns ids pk rhs rest)
        (let (many vs) $ eval fuel _ rhs env)
        (eval fuel _ rest $ venv-bind-picked _ ids pk vs env))
      ((CLetRec ns fns rest) (eval fuel _ rest $ close-group fns fns env))
      ((CMatch ns scrut shape branches dfl)
        (let (many v) $ vals-one $ eval fuel _ scrut env)
        (let (many (Maybe $ Pair (Nat) $ List $ Value) read)
          (match many shape _
            ((ShKnown adt) (dispatch (adt-ext adt) (adt-tagged adt) v))
            ((ShHeld mcode tags)
              (match many (vals-one $ eval fuel _ mcode env) (((Maybe $ Pair (Nat) $ List $ Value) r))
                ((VMatchable a) (dispatch (adt-ext a) tags v)) (else (None $ Pair (Nat) $ List $ Value))))))
        (match many read _
          ((Some a p)
            (match many p _
              ((MkPair x y i fields)
                (match many (has-branch _ branches i) _
                  ((BTrue) (eval-branch fuel ns branches i fields env))
                  ((BFalse) (match many dfl _ ((Some b d) (eval fuel _ d env)) ((None b) (eval-branch fuel ns branches i fields env))))))))
          ((None a)
            (match many branches _
              ((Nil b) (match many dfl _ ((Some c d) (eval fuel _ d env)) ((None c) (vals-of ns $ VError "no branch"))))
              ((Cons b br rest)
                (match many br _
                  ((MkBranch n0 d ids body) (eval fuel _ body $ venv-bind ids (untuple (list-length _ ids) v) env))))))))
      ((CAbsurd ms2) (vals-of ms2 $ VError "absurd code reached"))
      ((CError ms2 m) (vals-of ms2 $ VError m))))
  (many eval-list : (subterm many (Nat) fuel) (subterm many (List $ Code many-one) cs) (many (IdMap $ Value) env) -> (many (List $ Value) vs)
    (match many cs _
      ((Nil a) (Nil _))
      ((Cons a c rest) (Cons _ (vals-one $ eval fuel _ c env) $ eval-list fuel rest env))))
  (many eval-picked : (subterm many (Nat) fuel) (subterm many (List $ Code many-one) cs) (subterm many (List $ Mult) ms) (erased (Picked (Code many-one) ms cs) pk) (many (IdMap $ Value) env) -> (many (Vals ms) vs)
    (match many ms _
      ((Nil a) (ValsNil))
      ((Cons a m rest)
        (match many m _
          ((Many)
            (match erased pk _
              ((PkMany ta ms2 c0 cs2 p)
                (match many cs _
                  ((Cons b c crest) (ValsMany _ (vals-one $ eval fuel _ c env) $ eval-picked fuel crest rest p env))))))
          ((Erased)
            (match erased pk _
              ((PkErased ta ms2 cs2 p) (ValsErased _ $ eval-picked fuel cs rest p env))))))))
  (many eval-branch : (subterm many (Nat) fuel) (many (List $ Mult) ns) (subterm many (List $ Branch ns) bs) (many (Nat) i) (many (List $ Value) fields) (many (IdMap $ Value) env) -> (many (Vals ns) vs)
    (match many bs _
      ((Nil a) (vals-of ns $ VError $ str-cat "no branch for discriminant " $ nat-str i))
      ((Cons a b rest)
        (match many b _
          ((MkBranch n0 d ids body)
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x) (eval fuel _ body $ venv-bind ids fields env))
              (else (eval-branch fuel ns rest i fields env))))))))
  (many apply : (subterm many (Nat) fuel) (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
    (match many f _
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many fn _
              ((MkFunc rets name id params body impl top)
                (let (many (Bool) ext) $ match many impl _ ((None a) (BFalse)) ((Some a n) (and (is-extern-fn n) $ not $ str-eq n "nat-cmp")))
                (match many ext _
                  ((BTrue) (apply-extern (match many impl (((String) s)) ((None a) (SNil)) ((Some a n) n)) args))
                  ((BFalse)
                    (match many fuel _
                      ((Zero) (Cons _ (VError "out of fuel") $ Nil _))
                      ((Succ k) (vals-list _ $ eval k _ body $ venv-bind params args $ close-group group group cenv))))))))))
      ((VCtorFn c) (Cons _ (construct c args) $ Nil _))
      ((VCtor c fs) (Cons _ (VError "cannot apply a constructor value") $ Nil _))
      ((VTuple fs) (Cons _ (VError "cannot apply a tuple") $ Nil _))
      ((VExt a p) (Cons _ (VError "cannot apply an extern value") $ Nil _))
      ((VMatchable a) (Cons _ (VError "cannot apply a Matchable") $ Nil _))
      ((VToken) (Cons _ (VError "cannot apply the token") $ Nil _))
      ((VError m) (Cons _ (VError m) $ Nil _)))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (many (Env) env) (erased (List $ Mult) ms) (many (Code ms) code) -> (many (Vals ms) vs)
  (eval eval-fuel _ code $ env-values env))

(def-fns _ $ many apply-value : (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
  (apply eval-fuel f args))
