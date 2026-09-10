; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code, bounded by a fuel that decreases along the call stack so the checker
; accepts it. Extern functions run as the host's own (section 41).

(let (many nat-adt) $ MkAdt "Nat" (BTrue) (Nil _) $ Some _ $ ExtNat)
(let (many str-adt) $ MkAdt "String" (BTrue) (Nil _) $ Some _ $ ExtString)

(def-fns _ $ many vnat : (many (Nat) n) -> (many (Value) v)
  (VExt nat-adt $ PNat n))

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

; An extern function over its arguments, or None where the model runs instead: nat-cmp builds a plain
; ADT (ASSUMPTIONS 120). The arguments are counted against the arity here, the call having been checked
; against the model's telescope.
(def-fns _ $ many apply-extern : (erased (Nat) n) (many (Extern n) e) (many (List $ Value) args) -> (many (Maybe $ List $ Value) r)
  (let (many (Maybe $ Value) a1) (many (Maybe $ Value) a2)
    (match many args _
      ((Nil x) (values (None _) (None _)))
      ((Cons x a rest) (values (Some _ a) $ match many rest (((Maybe $ Value) m)) ((Nil y) (None _)) ((Cons y b rest2) (Some _ b))))))
  (let (many (Value) a) $ match many a1 _ ((None x) (VError "extern arity")) ((Some x v) v))
  (let (many (Value) b) $ match many a2 _ ((None x) (VError "extern arity")) ((Some x v) v))
  (match many e _
    ((ExAdd) (Some _ $ Cons _ (vnat $ nat-add (value-nat a) $ value-nat b) $ Nil _))
    ((ExNatCmp) (None _))
    ((ExNatMod) (Some _ $ Cons _ (nat-mod-value (value-nat a) $ value-nat b) $ Nil _))
    ((ExBinToNat)
      (let (many n2) (erased pf) $ bin-to-nat $ value-bin a)
      (Some _ $ Cons _ (vnat n2) $ Nil _))
    ((ExTrim) (Some _ $ Cons _ (VExt str-adt $ PStr $ trim $ value-str a) $ Nil _))
    ((ExAppend) (Some _ $ Cons _ (VExt str-adt $ PStr $ str-append (value-str a) $ value-str b) $ Nil _))
    ((ExFlatten) (Some _ $ Cons _ (VExt str-adt $ PStr $ flatten-value a) $ Nil _))))

; The closures of a group over [env], each re-closing the whole group when applied, as the frame the group binds.
(def-fns _ $ many close-fns : (erased (List $ Bin) gids) (erased (List $ List $ Bin) ctx) (subterm many (List $ Pair (Bin) $ Func gids ctx) fns) (many (Group gids ctx) whole) (many (VEnv ctx) env) ->
    (many (List $ Value) vs) (erased (Lockstep (Pair (Bin) $ Func gids ctx) (Value) fns vs) lk)
  (match many fns _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a p rest)
      (let (many vs) (erased lk) $ close-fns _ _ rest whole env)
      (match many p _
        ((MkPair x y id fn)
          (let (many v) $ VFn $ MkClosure _ _ fn whole env)
          (values (Cons _ v vs) (LsCons _ _ p v rest vs lk)))))))

(def-fns _ $ many close-group : (erased (List $ Bin) gids) (erased (List $ List $ Bin) ctx) (many (Group gids ctx) g) (many (VEnv ctx) env) -> (many (VEnv (Cons (List (Bin)) gids ctx)) r)
  (match many g _
    ((MkGroup c ids fns lk)
      (let (many vs) (erased lv) $ close-fns _ _ fns g env)
      (VFrame _ ids vs (lockstep-trans _ _ _ _ _ _ lk lv) env))))

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

; The many values of [vs] as the frame of the ids picked from the same positions.
(def-fns _ $ many vals-frame : (erased (List $ Mult) ms) (erased (List $ Bin) ids) (erased (Picked (Bin) ms ids) pk) (subterm many (Vals ms) vs) -> (many (List $ Value) r) (erased (Lockstep (Bin) (Value) ids r) lk)
  (match many vs _
    ((ValsNil) (match erased pk _ ((PkNil a) (values (Nil _) (LsNil _ _)))))
    ((ValsMany m v rest)
      (match erased pk _
        ((PkMany ta ms2 x xs p)
          (let (many r) (erased lk) $ vals-frame _ _ p rest)
          (values (Cons _ v r) (LsCons _ _ x v xs r lk)))))
    ((ValsErased m rest)
      (match erased pk _
        ((PkErased ta ms2 xs p) (vals-frame _ _ p rest))))))

; A branch's fields bound to its ids, cut or padded to their count.
(def-fns _ $ many bind-frame : (erased (List $ List $ Bin) ctx) (many (List $ Bin) ids) (many (List $ Value) fields) (many (VEnv ctx) env) -> (many (VEnv (Cons (List (Bin)) ids ctx)) r)
  (let (many vs) (erased lk) $ list-fit _ _ ids fields $ VError "arity mismatch")
  (VFrame _ ids vs lk env))

(def-fns _ $ many has-branch : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) -> (many (Bool) r)
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch c n0 d ids body) (or (nat-eq d i) $ has-branch _ _ rest i))))))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (VEnv ctx) env) -> (many (Vals ms) vs)
    (match many code _
      ((CVar c x p) (ValsMany _ (venv-get _ _ p env) $ ValsNil))
      ((CConst c x v) (ValsMany _ v $ ValsNil))
      ((CValue c v) (ValsMany _ v $ ValsNil))
      ((CErased c ms2) (vals-of ms2 $ VToken))
      ((CValues c ms2 cs pk) (eval-picked fuel _ cs ms2 pk env))
      ((CApp c ms2 f args cc)
        (let (many fv) $ vals-one $ eval fuel _ _ f env)
        (let (many avs) $ eval-list fuel _ args env)
        (match many fuel _
          ((Zero) (vals-of ms2 $ VError "out of fuel"))
          ((Succ k) (vals-fit ms2 $ apply k fv avs))))
      ((CLet c ms2 ns ids pk rhs rest)
        (let (many vs) (erased lk) $ vals-frame _ _ pk $ eval fuel _ _ rhs env)
        (eval fuel _ _ rest $ VFrame _ ids vs lk env))
      ((CLetRec c ns gids g rest) (eval fuel _ _ rest $ close-group _ _ g env))
      ((CMatch c ns scrut shape branches dfl)
        (let (many v) $ vals-one $ eval fuel _ _ scrut env)
        (let (many (Maybe $ Pair (Nat) $ List $ Value) read)
          (match many shape _
            ((ShKnown c2 adt) (dispatch (adt-ext adt) (adt-tagged adt) v))
            ((ShNone c2) (None _))
            ((ShHeld c2 mcode tags)
              (match many (vals-one $ eval fuel _ _ mcode env) (((Maybe $ Pair (Nat) $ List $ Value) r))
                ((VMatchable a) (dispatch (adt-ext a) tags v)) (else (None $ Pair (Nat) $ List $ Value))))))
        (match many read _
          ((Some a p)
            (match many p _
              ((MkPair x y i fields)
                (match many (has-branch _ _ branches i) _
                  ((BTrue) (eval-branch fuel _ ns branches i fields env))
                  ((BFalse) (match many dfl _ ((Some b d) (eval fuel _ _ d $ VFrame _ (Nil _) (Nil _) (LsNil _ _) env)) ((None b) (eval-branch fuel _ ns branches i fields env))))))))
          ((None a)
            (match many branches _
              ((Nil b) (match many dfl _ ((Some c2 d) (eval fuel _ _ d $ VFrame _ (Nil _) (Nil _) (LsNil _ _) env)) ((None c2) (vals-of ns $ VError "no branch"))))
              ((Cons b br rest)
                (match many br _
                  ((MkBranch c2 n0 d ids body) (eval fuel _ _ body $ bind-frame _ ids (untuple (list-length _ ids) v) env))))))))
      ((CAbsurd c ms2) (vals-of ms2 $ VError "absurd code reached"))
      ((CError c ms2 m) (vals-of ms2 $ VError m))))
  (many eval-list : (subterm many (Nat) fuel) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) (many (VEnv ctx) env) -> (many (List $ Value) vs)
    (match many cs _
      ((Nil a) (Nil _))
      ((Cons a c rest) (Cons _ (vals-one $ eval fuel _ _ c env) $ eval-list fuel _ rest env))))
  (many eval-picked : (subterm many (Nat) fuel) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) (subterm many (List $ Mult) ms) (erased (Picked (Code ctx many-one) ms cs) pk) (many (VEnv ctx) env) -> (many (Vals ms) vs)
    (match many ms _
      ((Nil a) (ValsNil))
      ((Cons a m rest)
        (match many m _
          ((Many)
            (match erased pk _
              ((PkMany ta ms2 c0 cs2 p)
                (match many cs _
                  ((Cons b c crest) (ValsMany _ (vals-one $ eval fuel _ _ c env) $ eval-picked fuel _ crest rest p env))))))
          ((Erased)
            (match erased pk _
              ((PkErased ta ms2 cs2 p) (ValsErased _ $ eval-picked fuel _ cs rest p env))))))))
  (many eval-branch : (subterm many (Nat) fuel) (erased (List $ List $ Bin) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) (many (List $ Value) fields) (many (VEnv ctx) env) -> (many (Vals ns) vs)
    (match many bs _
      ((Nil a) (vals-of ns $ VError $ str-cat "no branch for discriminant " $ nat-str i))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c n0 d ids body)
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x) (eval fuel _ _ body $ bind-frame _ ids fields env))
              (else (eval-branch fuel _ ns rest i fields env))))))))
  (many apply : (subterm many (Nat) fuel) (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
    (match many f _
      ((VFn cl)
        (match many cl _
          ((MkClosure gids ctx fn group cenv)
            (match many fn _
              ((MkFunc g c rets name id params body impl top)
                (let (many (Maybe $ List $ Value) done) $ match many impl _ ((None a) (None _)) ((Some a se) (match many se (((Maybe $ List $ Value) r)) ((MkSomeExtern n e) (apply-extern _ e args)))))
                (match many done _
                  ((Some a r) r)
                  ((None a)
                    (match many fuel _
                      ((Zero) (Cons _ (VError "out of fuel") $ Nil _))
                      ((Succ k) (vals-list _ $ eval k _ _ body $ bind-frame _ params args $ close-group _ _ group cenv))))))))))
      ((VCtorFn c) (Cons _ (construct c args) $ Nil _))
      ((VCtor c fs) (Cons _ (VError "cannot apply a constructor value") $ Nil _))
      ((VTuple fs) (Cons _ (VError "cannot apply a tuple") $ Nil _))
      ((VExt a p) (Cons _ (VError "cannot apply an extern value") $ Nil _))
      ((VMatchable a) (Cons _ (VError "cannot apply a Matchable") $ Nil _))
      ((VToken) (Cons _ (VError "cannot apply the token") $ Nil _))
      ((VError m) (Cons _ (VError m) $ Nil _)))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (erased (List $ Mult) ms) (many (Code (Nil (List (Bin))) ms) code) -> (many (Vals ms) vs)
  (eval eval-fuel _ _ code $ VNil))

(def-fns _ $ many apply-value : (many (Value) f) (many (List $ Value) args) -> (many (List $ Value) vs)
  (apply eval-fuel f args))
