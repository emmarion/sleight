; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code, bounded by a fuel that decreases along the call stack so the checker
; accepts it. Extern functions run as the host's own (section 41).

(let (many nat-adt) (MkAdt "Nat" (BTrue) (Nil (Ctor)) (Some (String) "Nat")))
(let (many u8-adt) (MkAdt "U8" (BFalse) (Nil (Ctor)) (Some (String) "U8")))
(let (many dec-adt) (MkAdt "Dec" (BTrue) (Nil (Ctor)) (Some (String) "Dec")))
(let (many str-adt) (MkAdt "String" (BTrue) (Nil (Ctor)) (Some (String) "String")))

(def-fns _ $ many vnat : (many (Nat) n) -> (many (Value) v)
  (VExt nat-adt (PNat n)))

(def-fns _ $ many arg-at : (many (List (Value)) args) (many (Nat) i) -> (many (Value) v)
  (match many (list-nth (predates _) (Value) args i) _
    ((None a) (VError "extern arity"))
    ((Some a v) v)))

(def-fns _ $ many is-extern-fn : (many (String) name) -> (many (Bool) r)
  (or (predates _) (str-eq (predates _) name "nat-add")
    (or (predates _) (str-eq (predates _) name "lt-dec")
      (or (predates _) (str-eq (predates _) name "u8-add")
        (or (predates _) (str-eq (predates _) name "nat-to-u8")
          (or (predates _) (str-eq (predates _) name "u8-to-nat")
            (or (predates _) (str-eq (predates _) name "bin-to-nat") (str-eq (predates _) name "trim"))))))))

(def-fns _ $ many is-extern-type : (many (String) name) -> (many (Bool) r)
  (or (predates _) (str-eq (predates _) name "Nat")
    (or (predates _) (str-eq (predates _) name "U8")
      (or (predates _) (str-eq (predates _) name "Bin")
        (or (predates _) (str-eq (predates _) name "String") (str-eq (predates _) name "Dec"))))))

(def-fns _ $ many apply-extern : (many (String) name) (many (List (Value)) args) -> (many (List (Value)) r)
  (let (many a) (arg-at (predates _) args 0))
  (let (many b) (arg-at (predates _) args 1))
  (match many (str-eq (predates _) name "nat-add") _
    ((BTrue) (Cons (Value) (vnat (predates _) (nat-add (predates _) (value-nat (predates _) a) (value-nat (predates _) b))) (Nil (Value))))
    ((BFalse)
      (match many (str-eq (predates _) name "lt-dec") _
        ((BTrue) (Cons (Value) (VExt dec-adt (PDec (match many (nat-lt (predates _) (value-nat (predates _) a) (value-nat (predates _) b)) (((Nat) i)) ((BTrue) 0) ((BFalse) 1)))) (Nil (Value))))
        ((BFalse)
          (match many (str-eq (predates _) name "u8-add") _
            ((BTrue) (Cons (Value) (VExt u8-adt (PU8 (u8-add (predates _) (value-u8 (predates _) a) (value-u8 (predates _) b)))) (Nil (Value))))
            ((BFalse)
              (match many (str-eq (predates _) name "nat-to-u8") _
                ((BTrue) (Cons (Value) (VExt u8-adt (PU8 (nat-to-u8 (predates _) (value-nat (predates _) a)))) (Nil (Value))))
                ((BFalse)
                  (match many (str-eq (predates _) name "u8-to-nat") _
                    ((BTrue) (Cons (Value) (vnat (predates _) (u8-to-nat (predates _) (value-u8 (predates _) a))) (Nil (Value))))
                    ((BFalse)
                      (match many (str-eq (predates _) name "bin-to-nat") _
                        ((BTrue)
                          (let (many n) (erased pf) (bin-to-nat (predates _) (value-bin (predates _) a)))
                          (Cons (Value) (vnat (predates _) n) (Nil (Value))))
                        ((BFalse) (Cons (Value) (VExt str-adt (PStr (trim (predates _) (value-str (predates _) a)))) (Nil (Value))))))))))))))))

(def-fns _ $ many venv-bind : (subterm many (List (Bin)) ids) (many (List (Value)) vs) (many (IdMap (Value)) env) -> (many (IdMap (Value)) r)
  (match many ids _
    ((Nil a) env)
    ((Cons a x rest)
      (match many vs _
        ((Nil b) (idmap-set (predates _) (Value) x (VError "arity mismatch") env))
        ((Cons b v vrest) (venv-bind (subterm _) rest vrest (idmap-set (predates _) (Value) x v env)))))))

; Adds the closures of a def-fns group to [env]; each closure re-closes the whole group when applied.
(def-fns _ $ many close-group : (subterm many (List (Pair (Bin) (Func))) group) (many (List (Pair (Bin) (Func))) whole) (many (IdMap (Value)) env) -> (many (IdMap (Value)) r)
  (match many group _
    ((Nil a) env)
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn) (close-group (subterm _) rest whole (idmap-set (predates _) (Value) id (VFn (MkClosure fn whole env)) env)))))))

(def-fns _ $ many find-branch : (subterm many (List (Branch)) bs) (many (Nat) i) -> (many (Maybe (Branch)) r)
  (match many bs _
    ((Nil a) (None (Branch)))
    ((Cons a b rest)
      (match many b _
        ((MkBranch d ids body)
          (match many (nat-eq (predates _) d i) _
            ((BTrue) (Some (Branch) b))
            ((BFalse) (find-branch (subterm _) rest i))))))))

(def-fns _ $ many first-value : (many (List (Value)) vs) -> (many (Value) v)
  (match many vs _
    ((Nil a) (VError "expected one value"))
    ((Cons a v rest) v)))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (subterm many (Code) code) (many (IdMap (Value)) env) -> (many (List (Value)) vs)
    (match many code _
      ((CVar x)
        (match many (idmap-get (predates _) (Value) x env) _
          ((None a) (Cons (Value) (VError (str-cat (predates _) "unbound at runtime: " (bin-str (predates _) x))) (Nil (Value))))
          ((Some a v) (Cons (Value) v (Nil (Value))))))
      ((CConst v) (Cons (Value) v (Nil (Value))))
      ((CErased) (Cons (Value) (VToken) (Nil (Value))))
      ((CValues cs) (eval-list fuel (subterm _) cs env))
      ((CApp f args cc)
        (let (many fv) (first-value (predates _) (eval fuel (subterm _) f env)))
        (let (many avs) (eval-list fuel (subterm _) args env))
        (match many fuel _
          ((Zero) (Cons (Value) (VError "out of fuel") (Nil (Value))))
          ((Succ k) (apply (subterm _) k fv avs))))
      ((CLet ids rhs rest)
        (let (many vs) (eval fuel (subterm _) rhs env))
        (eval fuel (subterm _) rest (venv-bind (predates _) ids vs env)))
      ((CLetRec fns rest) (eval fuel (subterm _) rest (close-group (predates _) fns fns env)))
      ((CMatch scrut shape branches)
        (let (many v) (first-value (predates _) (eval fuel (subterm _) scrut env)))
        (let (many read)
          (match many shape (((Maybe (Pair (Nat) (List (Value)))) r))
            ((ShKnown adt) (dispatch (predates _) (adt-ext (predates _) adt) (adt-tagged (predates _) adt) v))
            ((ShHeld mcode tags)
              (match many (first-value (predates _) (eval fuel (subterm _) mcode env)) (((Maybe (Pair (Nat) (List (Value)))) r))
                ((VMatchable a) (dispatch (predates _) (adt-ext (predates _) a) tags v))
                ((VCtor c fs) (None (Pair (Nat) (List (Value))))) ((VTuple fs) (None (Pair (Nat) (List (Value)))))
                ((VExt a p) (None (Pair (Nat) (List (Value))))) ((VCtorFn c) (None (Pair (Nat) (List (Value)))))
                ((VFn cl) (None (Pair (Nat) (List (Value))))) ((VToken) (None (Pair (Nat) (List (Value)))))
                ((VError m) (None (Pair (Nat) (List (Value)))))))))
        (match many read _
          ((Some a p)
            (match many p _
              ((MkPair x y i fields) (eval-branch fuel (subterm _) branches i fields env))))
          ((None a)
            (match many branches _
              ((Nil b) (Cons (Value) (VError "no branch") (Nil (Value))))
              ((Cons b br rest)
                (match many br _
                  ((MkBranch d ids body) (eval fuel (subterm _) body (venv-bind (predates _) ids (untuple (predates _) (list-length (predates _) (Bin) ids) v) env)))))))))
      ((CAbsurd) (Cons (Value) (VError "absurd code reached") (Nil (Value))))
      ((CError m) (Cons (Value) (VError m) (Nil (Value))))))
  (many eval-list : (subterm many (Nat) fuel) (subterm many (List (Code)) cs) (many (IdMap (Value)) env) -> (many (List (Value)) vs)
    (match many cs _
      ((Nil a) (Nil (Value)))
      ((Cons a c rest) (Cons (Value) (first-value (predates _) (eval fuel (subterm _) c env)) (eval-list fuel (subterm _) rest env)))))
  (many eval-branch : (subterm many (Nat) fuel) (subterm many (List (Branch)) bs) (many (Nat) i) (many (List (Value)) fields) (many (IdMap (Value)) env) -> (many (List (Value)) vs)
    (match many bs _
      ((Nil a) (Cons (Value) (VError (str-cat (predates _) "no branch for discriminant " (nat-str (predates _) i))) (Nil (Value))))
      ((Cons a b rest)
        (match many b _
          ((MkBranch d ids body)
            (match many (nat-eq (predates _) d i) _
              ((BTrue) (eval fuel (subterm _) body (venv-bind (predates _) ids fields env)))
              ((BFalse) (eval-branch fuel (subterm _) rest i fields env))))))))
  (many apply : (subterm many (Nat) fuel) (many (Value) f) (many (List (Value)) args) -> (many (List (Value)) vs)
    (match many f _
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many fn _
              ((MkFunc name id params body impl top)
                (let (many ext) (match many impl (((Bool) b)) ((None a) (BFalse)) ((Some a n) (is-extern-fn (predates _) n))))
                (match many ext _
                  ((BTrue) (apply-extern (predates _) (match many impl (((String) s)) ((None a) (SNil)) ((Some a n) n)) args))
                  ((BFalse)
                    (match many fuel _
                      ((Zero) (Cons (Value) (VError "out of fuel") (Nil (Value))))
                      ((Succ k) (eval (subterm _) k body (venv-bind (predates _) params args (close-group (predates _) group group cenv))))))))))))
      ((VCtorFn c) (Cons (Value) (construct (predates _) c args) (Nil (Value))))
      ((VCtor c fs) (Cons (Value) (VError "cannot apply a constructor value") (Nil (Value))))
      ((VTuple fs) (Cons (Value) (VError "cannot apply a tuple") (Nil (Value))))
      ((VExt a p) (Cons (Value) (VError "cannot apply an extern value") (Nil (Value))))
      ((VMatchable a) (Cons (Value) (VError "cannot apply a Matchable") (Nil (Value))))
      ((VToken) (Cons (Value) (VError "cannot apply the token") (Nil (Value))))
      ((VError m) (Cons (Value) (VError m) (Nil (Value)))))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (many (Env) env) (many (Code) code) -> (many (List (Value)) vs)
  (eval (predates _) eval-fuel code (env-values (predates _) env)))

(def-fns _ $ many apply-value : (many (Value) f) (many (List (Value)) args) -> (many (List (Value)) vs)
  (apply (predates _) eval-fuel f args))
