; self/emit.sl -- OCaml extraction of the traced program (self/README.md; lib/extract.ml): every run-position
; def-fns group becomes a let rec over the one runtime type v of self/runtime.ml, every Const the
; elaborator minted is embedded as data at its trace position, closures met inside data are hoisted with
; their captured values, and each final value is consumed as lib/program.ml would.

(def-adts $ EmitSt : -> Type
  enum
  (many MkEmitSt : (many (Bin) counter) (many (List $ Rope) defs) (many (IdMap $ String) names) -> (EmitSt)))

; [top]: the final environment's Const values, named at top level; [capture]: the environment of the
; closure being hoisted, or empty inside a run-position function.
(def-adts $ EmitCx : -> Type
  enum
  (many MkEmitCx : (many (Env) env) (many (IdMap $ Value) top) -> (EmitCx)))

(def-fns _ $ many cx-env : (many (EmitCx) cx) -> (many (Env) e) (match many cx _ ((MkEmitCx env top) env)))
(def-fns _ $ many cx-top : (many (EmitCx) cx) -> (many (IdMap $ Value) e) (match many cx _ ((MkEmitCx env top) top)))

(def-fns _ $ many st-names : (many (EmitSt) st) -> (many (IdMap $ String) r) (match many st _ ((MkEmitSt c d n) n)))
(def-fns _ $ many st-with-names : (many (EmitSt) st) (many (IdMap $ String) n) -> (many (EmitSt) r) (match many st _ ((MkEmitSt c d n0) (MkEmitSt c d n))))
(def-fns _ $ many st-push-def : (many (EmitSt) st) (many (Rope) d) -> (many (EmitSt) r) (match many st _ ((MkEmitSt c ds n) (MkEmitSt c (Cons _ d ds) n))))
(def-fns _ $ many st-fresh : (many (EmitSt) st) -> (many (EmitSt) r) (many (Bin) x)
  (match many st _ ((MkEmitSt c ds n) (values (MkEmitSt (bin-succ c) ds n) c))))
(def-fns _ $ many st-take-defs : (many (EmitSt) st) -> (many (EmitSt) r) (many (Rope) defs)
  (match many st _ ((MkEmitSt c ds n) (values (MkEmitSt c (Nil _) n) $ rlist $ list-rev _ ds))))

(def-fns _ $ many top-name : (many (Env) env) (many (Bin) x) -> (many (String) s)
  (str-cat "v" $ str-cat (bin-str x) $ str-cat "_" $ sanitize $ name-of env x))

(def-fns _ $ many quoted : (many (String) s) -> (many (Rope) r)
  (rcat3 (RStr "\"") (RStr $ ocaml-escape s) $ RStr "\""))

(def-fns _ $ many nat-rope : (many (Nat) n) -> (many (Rope) r)
  (RStr $ nat-str n))

(def-fns _ $ many bracketed : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (rcat3 (RStr "[") (rjoin rs "; ") $ RStr "]"))

(def-fns _ $ many names-of-ids : (subterm many (List $ Bin) ids) (many (Env) env) -> (many (List $ Rope) r)
  (match many ids _
    ((Nil a) (Nil _))
    ((Cons a x rest) (Cons _ (RStr $ top-name env x) $ names-of-ids rest env))))

; An OCaml pattern binding the ids: a list pattern of their names.
(def-fns _ $ many ids-pattern : (many (List $ Bin) ids) (many (Env) env) -> (many (Rope) r)
  (bracketed $ names-of-ids ids env))

; A tuple of values as the runtime keeps it: none is U, one is bare, more a Tup.
(def-fns _ $ many tuple-rope : (many (List $ Rope) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (RStr "U"))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (rcat3 (RStr "(Tup ") (bracketed rs) $ RStr ")"))))))

; Binding the ids to a value of that shape.
(def-fns _ $ many untuple-rope : (many (List $ Bin) ids) (many (Rope) e) (many (Rope) body) (many (Env) env) -> (many (Rope) r)
  (match many ids _
    ((Nil a) (rcat5 (RStr "(let _ = ") e (RStr " in ") body $ RStr ")"))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (rcat3 (RStr "(let ") (RStr $ top-name env x) $ RStr " = ") e (RStr " in ") body $ RStr ")"))
        ((Cons b y rest2) (rcat5 (RStr "(match ") e (rcat3 (RStr " with Tup ") (ids-pattern ids env) $ RStr " -> ") body $ RStr " | _ -> absurd ())"))))))

; Constructing a value from a constructor and the code of its many fields.
(def-fns _ $ many build-rope : (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (RStr "(con_") (RStr e) (rcat3 (RStr " ") (nat-rope index) $ RStr " ") (bracketed args) $ RStr ")"))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat5 (RStr "(Tag (") (nat-rope index) (RStr ", ") (bracketed args) $ RStr "))"))
            ((BFalse) (tuple-rope args))))))))

(def-fns _ $ many ctor-fn-rope : (many (Ctor) c) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (RStr "(Fn (con_") (RStr e) (RStr " ") (nat-rope index) $ RStr "))"))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat3 (RStr "(Fn (fun args -> Tag (") (nat-rope index) $ RStr ", args)))"))
            ((BFalse) (RStr "(Fn tuple)"))))))))

(def-fns _ $ many matchable-rope : (many (Adt) adt) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat3 (RStr "(Mat (fun _ v -> des_") (RStr e) $ RStr " v))"))
        ((None a)
          (match many tagged _
            ((BTrue) (RStr "(Mat (fun _ v -> des_tag v))"))
            ((BFalse) (RStr "(Mat (fun n v -> (0, untuple n v)))"))))))))

; The destructor a known shape reads a value through: the FFI's, the tag's, or the fields themselves.
(def-fns _ $ many des-rope : (many (Adt) adt) (many (Rope) scrut) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat4 (RStr "(des_") (RStr e) (RStr " ") $ rcat scrut $ RStr ")"))
        ((None a) (rcat3 (RStr "(des_tag ") scrut $ RStr ")"))))))

(def-fns _ $ many adt-untagged : (many (Adt) adt) -> (many (Bool) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _ ((Some a e) (BFalse)) ((None a) (not tagged))))))

(def-fns _ $ many payload-rope : (many (Payload) p) -> (many (Rope) r)
  (match many p _
    ((PNat n) (rcat3 (RStr "(Nat (Z.of_string \"") (nat-rope n) $ RStr "\"))"))
    ((PBin b)
      (let (many n) (erased pf) $ bin-to-nat b)
      (rcat3 (RStr "(Nat (Z.of_string \"") (nat-rope n) $ RStr "\"))"))
    ((PStr s) (rcat5 (RStr "(Str (") (quoted s) (RStr ", 0, ") (nat-rope $ str-length s) $ RStr "))"))
    ((PDec i) (rcat3 (RStr "(Nat (Z.of_string \"") (nat-rope i) $ RStr "\"))"))))

(def-fns _ $ many is-top : (many (EmitCx) cx) (many (Bin) x) -> (many (Bool) r)
  (idmap-mem _ x $ cx-top cx))

; A constructor a code names statically: a Const entry holding it, or the constant itself.
(def-fns _ $ many static-ctor : (many (EmitCx) cx) (many (Code) f) -> (many (Maybe $ Ctor) r)
  (match many f _
    ((CVar x)
      (match many (idmap-get _ x $ cx-top cx) _
        ((Miss lt lk lm lp) (None _))
        ((Hit lt lk lm v lp)
          (match many v _
            ((VCtorFn c) (Some _ c)) (else (None $ Ctor))))))
    ((CConst v)
      (match many v _
        ((VCtorFn c) (Some _ c)) (else (None $ Ctor)))) (else (None $ Ctor))))

; The closure whose code is being emitted is the recursion's first measure, and the code being emitted
; comes with a proof that it lies inside that closure: a captured variable's value is a subterm of the
; closure, a constant's value a subterm of the code, and a closure met inside a value a subterm of that
; value. A run-position group is emitted under a closure built around it, which captures nothing.
(let (many show-fuel) 100000)

; Gives each member of a group about to be hoisted its closure name.
(def-fns _ $ many name-group : (subterm many (List $ Pair (Bin) $ Func) group) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Bool) ok)
  (match many group _
    ((Nil a) (values st $ BTrue))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (let (many st2) (many n) $ st-fresh st)
          (let (many name) $ str-cat "cl" $ str-cat (bin-str n) $ str-cat "_" $ sanitize $ func-name fn)
          (name-group rest $ st-with-names st2 $ idmap-set _ id name $ st-names st2))))))

(def-fns _
  (many emit-code : (subterm many (Closure) cl) (subterm many (Code) code) (erased (Subterm (Code) code (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many code _
      ; A variable: a top-level Const or function by its name, a captured value embedded once under a fresh
      ; name, a hoisted group member by its closure name, or a local.
      ((CVar x)
        (match many (is-top cx x) _
          ((BTrue) (values st $ RStr $ top-name (cx-env cx) x))
          ((BFalse)
            (match many (idmap-get _ x $ st-names st) _
              ((Hit lt lk lm name lp) (values st $ RStr name))
              ((Miss lt lk lm lp)
                (match many cl _
                  ((MkClosure fn group cenv)
                    (match many (idmap-get _ x cenv) _
                      ((Miss lt2 lk2 lm2 lp2) (values st $ RStr $ top-name (cx-env cx) x))
                      ((Hit lt2 lk2 lm2 v mp)
                        (let (many st2) (many n) $ st-fresh st)
                        (let (many name) $ str-cat "c" $ str-cat (bin-str n) $ str-cat "_" $ top-name (cx-env cx) x)
                        (let (erased q) $ subterm-trans (mapsto-subterm _ _ _ _ mp) $ prove-subterm cenv cl)
                        (let (many st3) (many vr) $ emit-value (subterm q) v cx st2)
                        (let (many st4) $ st-push-def st3 $ rcat4 (RStr "let ") (RStr name) (RStr " = ") $ rcat vr $ RStr "\n")
                        (values (st-with-names st4 $ idmap-set _ x name $ st-names st4) $ RStr name))))))))))
      ((CConst v)
        (let (erased q) $ subterm-trans (prove-subterm v code) w)
        (emit-value (subterm q) v cx st))
      ((CErased) (values st $ RStr "U"))
      ((CValues cs)
        (let (many st2) (many rs) $ emit-codes cl cs (subterm-trans (prove-subterm cs code) w) cx st)
        (values st2 $ tuple-rope rs))
      ((CApp f args cc)
        (let (many st2) (many rs) $ emit-codes cl args (subterm-trans (prove-subterm args code) w) cx st)
        (match many (static-ctor cx f) _
          ((Some a c) (values st2 $ build-rope c rs))
          ((None a)
            (let (many st3) (many fr) $ emit-code cl f (subterm-trans (prove-subterm f code) w) cx st2)
            (values st3 $ rcat5 (RStr "(app ") fr (RStr " ") (bracketed rs) $ RStr ")"))))
      ((CLet ids rhs rest)
        (let (many st2) (many rr) $ emit-code cl rhs (subterm-trans (prove-subterm rhs code) w) cx st)
        (let (many st3) (many br) $ emit-code cl rest (subterm-trans (prove-subterm rest code) w) cx st2)
        (values st3 $ untuple-rope ids rr br $ cx-env cx))
      ((CLetRec fns rest)
        (let (many st2) (many fr) $ emit-group cl fns (subterm-trans (prove-subterm fns code) w) cx st $ BFalse)
        (let (many st3) (many br) $ emit-code cl rest (subterm-trans (prove-subterm rest code) w) cx st2)
        (values st3 $ rcat5 (RStr "(let rec ") fr (RStr " in ") br $ RStr ")"))
      ((CMatch scrut shape branches dfl)
        (let (many st2) (many sr) $ emit-code cl scrut (subterm-trans (prove-subterm scrut code) w) cx st)
        (let (many (Nat) arity) $ match many branches _ ((Nil a) 0) ((Cons a b rest) (match many b (((Nat) n)) ((MkBranch d ids body) (list-length _ ids)))))
        (let (many (EmitSt) st2b) (many (Rope) dr)
          (match many dfl _
            ((None a) (values st2 $ RStr "absurd ()"))
            ((Some a d) (emit-code cl d (subterm-trans (prove-subterm d code) w) cx st2))))
        (let (many fallthrough) $ rcat3 (RStr " | _ -> ") dr $ RStr ")")
        (match many shape _
          ((ShKnown adt)
            (match many (adt-untagged adt) _
              ((BTrue)
                (match many branches _
                  ((Nil a) (values st2b $ rcat3 (RStr "(") dr $ RStr ")"))
                  ((Cons a b rest)
                    (match many b _
                      ((MkBranch d ids body)
                        (let (many st3) (many br) $ emit-code cl body (subterm-trans (prove-subterm body code) w) cx st2b)
                        (values st3 $ untuple-rope ids sr br $ cx-env cx))))))
              ((BFalse)
                (let (many st3) (many arms) $ emit-branches cl branches (subterm-trans (prove-subterm branches code) w) cx st2b)
                (values st3 $ rcat4 (RStr "(match ") (des-rope adt sr) (rcat (RStr " with ") arms) fallthrough))))
          ((ShHeld mcode tags)
            (let (many st3) (many mr) $ emit-code cl mcode (subterm-trans (prove-subterm mcode code) w) cx st2b)
            (let (many st4) (many arms) $ emit-branches cl branches (subterm-trans (prove-subterm branches code) w) cx st3)
            (values st4 $ rcat5 (RStr "(match (app_mat ") mr (rcat4 (RStr " ") (nat-rope arity) (RStr " ") sr) (rcat (RStr ") with ") arms) fallthrough))))
      ((CAbsurd) (values st $ RStr "(absurd ())"))
      ((CError m) (values st $ rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

  (many emit-codes : (subterm many (Closure) cl) (subterm many (List $ Code) cs) (erased (Subterm (List $ Code) cs (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (List $ Rope) rs)
    (match many cs _
      ((Nil a) (values st $ Nil _))
      ((Cons a c rest)
        (let (many st2) (many r) $ emit-code cl c (subterm-trans (prove-subterm c cs) w) cx st)
        (let (many st3) (many rs) $ emit-codes cl rest (subterm-trans (prove-subterm rest cs) w) cx st2)
        (values st3 $ Cons _ r rs))))

  (many emit-branches : (subterm many (Closure) cl) (subterm many (List $ Branch) bs) (erased (Subterm (List $ Branch) bs (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many bs _
      ((Nil a) (values st $ REmpty))
      ((Cons a b rest)
        (match many b _
          ((MkBranch d ids body)
            (let (many st2) (many br) $ emit-code cl body (subterm-trans (prove-subterm body bs) w) cx st)
            (let (many st3) (many more) $ emit-branches cl rest (subterm-trans (prove-subterm rest bs) w) cx st2)
            (values st3 $ rcat5 (RStr "| (") (nat-rope d) (rcat3 (RStr ", ") (ids-pattern ids $ cx-env cx) $ RStr ") -> ") br more))))))

  (many emit-value : (subterm many (Value) v) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many v _
      ((VCtor c fields)
        (let (many st2) (many rs) $ emit-values fields cx st)
        (values st2 $ build-rope c rs))
      ((VTuple fields)
        (let (many st2) (many rs) $ emit-values fields cx st)
        (values st2 $ tuple-rope rs))
      ((VExt adt p) (values st $ payload-rope p))
      ((VCtorFn c) (values st $ ctor-fn-rope c))
      ((VMatchable adt) (values st $ matchable-rope adt))
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many (func-top fn) _
              ((BTrue) (values st $ RStr $ top-name (cx-env cx) $ func-id fn))
              ((BFalse)
                (let (many saved) $ st-names st)
                (let (many st2) (many named) $ name-group group $ st-with-names st $ MEmpty _)
                (let (many st3) (many text) $ emit-group cl group (prove-subterm group cl) cx st2 $ BTrue)
                (let (many st4) $ st-push-def st3 $ rcat3 (RStr "let rec ") text $ RStr "\n")
                (let (many (String) mine) $ match many (idmap-get _ (func-id fn) $ st-names st4) _ ((Miss lt lk lm lp) "(failwith \"closure missing\")") ((Hit lt lk lm s lp) s))
                (values (st-with-names st4 saved) $ RStr mine))))))
      ((VToken) (values st $ RStr "U"))
      ((VError m) (values st $ rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

  (many emit-values : (subterm many (List $ Value) vs) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (List $ Rope) rs)
    (match many vs _
      ((Nil a) (values st $ Nil _))
      ((Cons a v rest)
        (let (many st2) (many r) $ emit-value v cx st)
        (let (many st3) (many rs) $ emit-values rest cx st2)
        (values st3 $ Cons _ r rs))))

  ; The definitions of a group, joined by and; hoisted groups are named through the state, local ones
  ; and run-position ones by their entries.
  (many emit-group : (subterm many (Closure) cl) (subterm many (List $ Pair (Bin) $ Func) fns) (erased (Subterm (List $ Pair (Bin) $ Func) fns (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) (many (Bool) hoisted) -> (many (EmitSt) st2) (many (Rope) r)
    (match many fns _
      ((Nil a) (values st $ REmpty))
      ((Cons a p rest)
        (match many p _
          ((MkPair x y id fn)
            (let (many (String) name)
              (match many hoisted _
                ((BFalse) (top-name (cx-env cx) id))
                ((BTrue) (match many (idmap-get _ id $ st-names st) (((String) s)) ((Miss lt lk lm lp) (top-name (cx-env cx) id)) ((Hit lt lk lm s lp) s)))))
            (let (many st2) (many body) $ emit-fn cl fn (subterm-trans (prove-subterm fn fns) w) cx st)
            (let (many st3) (many more) $ emit-group cl rest (subterm-trans (prove-subterm rest fns) w) cx st2 hoisted)
            (let (many (Rope) sep) $ match many rest _ ((Nil b) (REmpty)) ((Cons b q rest2) (RStr "\nand ")))
            (values st3 $ rcat5 (RStr name) (RStr " = ") body sep more))))))

  (many emit-fn : (subterm many (Closure) cl) (subterm many (Func) fn) (erased (Subterm (Func) fn (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many fn _
      ((MkFunc name id params body impl top)
        (let (many (Bool) ext) $ match many impl _ ((None a) (BFalse)) ((Some a n) (is-extern-fn n)))
        (match many ext _
          ((BTrue) (values st $ rcat3 (RStr "Fn ext_") (RStr $ sanitize $ match many impl (((String) s)) ((None a) "") ((Some a n) n)) $ REmpty))
          ((BFalse)
            (let (many st2) (many br) $ emit-code cl body (subterm-trans (prove-subterm body fn) w) cx st)
            (values st2 $ rcat5 (RStr "Fn (fun args -> match args with ") (ids-pattern params $ cx-env cx) (RStr " -> ") br $ RStr " | _ -> absurd ())")))))))

; A run-position group, emitted under a closure built around it.
(def-fns _ $ many emit-top-group : (many (List $ Pair (Bin) $ Func) fns) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
  (let (many (Func) f0) $ match many fns _ ((Nil a) (MkFunc "" (BZ) (Nil _) (CErased) (None _) $ BTrue)) ((Cons a p rest) (match many p (((Func) f)) ((MkPair x y id fn) fn))))
  (let (many cl) $ MkClosure f0 fns $ MEmpty _)
  (emit-group cl fns (prove-subterm fns cl) cx st $ BFalse))

; ---- Finals (lib/program.ml): what the driver does with a file's final value

(def-adts $ Final : -> Type
  enum
  (many FMain : -> (Final))
  (many FIo : -> (Final))
  (many FThunk : (many (Term) ty) -> (Final))
  (many FPlain : -> (Final)))

(def-fns _ $ many is-string-type : (many (Env) env) (many (Term) ty) -> (many (Bool) r)
  (match many (type-head env ty) _
    ((None a) (BFalse))
    ((Some a t) (str-eq (name-of env t) "String"))))

(def-fns _ $ many classify-final : (many (Env) env) (many (Term) ty) -> (many (Final) f)
  (match many (canon-env env ty) _
    ((TFn lv ps rs)
      (match many ps _
        ((Nil a)
          (match many rs _
            ((Cons b r more)
              (match many more _
                ((Nil c) (match many r _ ((MkEntry n s m sg) (match many m _ ((Many) (FThunk $ sg-term sg)) ((Erased) (FPlain))))))
                ((Cons c r2 more2) (FPlain))))
            ((Nil b) (FPlain))))
        ((Cons a p more)
          (match many more _
            ((Cons b p2 more2) (FPlain))
            ((Nil b)
              (match many rs _
                ((Nil c) (FPlain))
                ((Cons c r more3)
                  (match many more3 _
                    ((Cons d r2 more4) (FPlain))
                    ((Nil d)
                      (match many (and (is-string-type env $ sg-term $ entry-sg p)
                                    (and (is-string-type env $ sg-term $ entry-sg r)
                                      $ and (mult-is-many $ entry-mult p) $ mult-is-many $ entry-mult r)) _
                        ((BTrue) (FMain))
                        ((BFalse) (FPlain))))))))))))
    ((TApp h args)
      (match many (type-head env ty) _
        ((None a) (FPlain))
        ((Some a t) (match many (str-cmp (name-of env t) "IO") _ ((CEq eq-t eq-r eq-x) (FIo)) (else (FPlain)))))) (else (FPlain))))

; The chunks of a rope as OCaml string literals, for printing a value computed at compile time.
(def-fns _ $ many rope-literals : (subterm many (Rope) r) (many (Rope) acc) -> (many (Rope) out)
  (match many r _
    ((REmpty) acc)
    ((RStr s) (rcat3 (quoted s) (RStr "; ") acc))
    ((RCat a b) (rope-literals a $ rope-literals b acc))))

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ ShowMemo : -> Type
  enum
  (many MkShowMemo : (many (Nat) count) (many (List $ Pair (Term) $ String) known) (many (List $ Rope) defs) -> (ShowMemo)))

(def-fns _ $ many memo-find : (subterm many (List $ Pair (Term) $ String) known) (many (Env) env) (many (Term) ty) -> (many (Maybe $ String) r)
  (match many known _
    ((Nil a) (None _))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y t name)
          (match many (term-eq t ty) _
            ((BTrue) (Some _ name))
            ((BFalse) (memo-find rest env ty))))))))

(def-fns _ $ many spaced : (subterm many (List $ Rope) parts) -> (many (Rope) r)
  (match many parts _
    ((Nil a) (RStr "\"\""))
    ((Cons a p rest)
      (match many rest _
        ((Nil b) p)
        ((Cons b q rest2) (rcat3 p (RStr " ^ \" \" ^ ") $ spaced rest))))))

(def-fns _ $ many field-names : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Rope) r)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat "f" $ nat-str i) $ field-names k $ Succ i))))

(def-fns _ $ many adt-untagged-ext : (many (Maybe $ String) ext) (many (Bool) tagged) -> (many (Bool) r)
  (match many ext _ ((Some a e) (BFalse)) ((None a) (not tagged))))

(def-fns _ $ many untuple-rope-names : (many (List $ Rope) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r)
  (match many names _
    ((Nil a) body)
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (RStr "(let ") x (RStr " = ") (rcat3 e (RStr " in ") body) $ RStr ")"))
        ((Cons b y rest2) (rcat5 (RStr "(match ") e (rcat3 (RStr " with Tup ") (bracketed names) $ RStr " -> ") body $ RStr " | _ -> absurd ())"))))))

(def-fns _
  (many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) -> (many (ShowMemo) memo2) (many (String) name)
    (match many fuel _
      ((Zero) (values memo "show_any"))
      ((Succ k)
        (let (many ty) $ canon-env env ty0)
        (match many memo _
          ((MkShowMemo count known defs)
            (match many (memo-find known env ty) _
              ((Some a name) (values memo name))
              ((None a)
                (let (many name) $ str-cat "show_" $ nat-str count)
                (let (many memo1) $ MkShowMemo (Succ count) (Cons _ (MkPair _ _ ty name) known) defs)
                (let (many (ShowMemo) memo2) (many (Rope) body)
                  (match many ty _
                    ((TApp h args)
                      (match many (type-head env ty) (((ShowMemo) m) ((Rope) r))
                        ((None b) (values memo1 $ RStr "\"?\""))
                        ((Some b tid)
                          (let (many envf) (many foundm) $ find-matchable env tid)
                          (match many foundm (((ShowMemo) m) ((Rope) r))
                            ((None c) (values memo1 $ RStr "\"?\""))
                            ((Some c info)
                              (match many info (((ShowMemo) m) ((Rope) r))
                                ((MkMatchInfo mid disc mctors rank)
                                  (match many (adt-of env mid) (((ShowMemo) m) ((Rope) r))
                                    ((None d) (values memo1 $ RStr "\"?\""))
                                    ((Some d adt)
                                      (match many adt (((ShowMemo) m) ((Rope) r))
                                        ((MkAdt aname tagged ctors ext)
                                          (let (many memo3) (many arms) $ show-arms k env ty ctors memo1 $ adt-untagged-ext ext tagged)
                                          (match many (adt-untagged-ext ext tagged) (((ShowMemo) m) ((Rope) r))
                                            ((BTrue) (values memo3 arms))
                                            ((BFalse) (values memo3 $ rcat3 (rcat (RStr "match ") $ des-rope adt $ RStr "v") (rcat (RStr " with ") arms) $ RStr " | _ -> \"?\""))))))))))))))
                    ((TFn l ps rs) (values memo1 $ RStr "\"<function ?>\""))
                    ((TValCtor ps r) (values memo1 $ RStr "\"<constructor ?>\"")) (else (values memo1 $ RStr "\"?\""))))
                (match many memo2 _
                  ((MkShowMemo count2 known2 defs2)
                    (values (MkShowMemo count2 known2 $ Cons _ (rcat4 (RStr name) (RStr " (v : v) : string = ") body $ REmpty) defs2) name))))))))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, its fields shown
  ; only then, as the reference's exception skips them; an untagged type has one arm reading the fields as they stand.
  (many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List $ Ctor) ctors) (many (ShowMemo) memo) (many (Bool) untagged) -> (many (ShowMemo) memo2) (many (Rope) arms)
    (match many fuel _
      ((Zero) (values memo $ REmpty))
      ((Succ k)
        (match many ctors _
          ((Nil a) (values memo $ REmpty))
          ((Cons a c rest)
            (match many c _
              ((MkCtor cname cid index arity tagged ext)
                (let (many ctele) (many ret) $ ctor-type env cid)
                (let (many envb) (many fids) $ open-tele ctele env (None _) (None _) (None _) (Nil _) $ BFalse)
                (let (many (Env) envb2) (many (Bool) live)
                  (match many (unify-env envb (instantiate (tvars-rev fids $ Nil _) ret) ty $ BTrue) _
                    ((UOk e2) (values e2 $ BTrue))
                    ((UContra msg) (values envb $ BFalse))))
                (let (many (ShowMemo) memo2) (many (List $ Rope) shown)
                  (match many live _
                    ((BTrue) (show-fields k envb2 (non-erased fids envb2) memo 0))
                    ((BFalse) (values memo $ Nil _))))
                (let (many fnames) $ field-names arity 0)
                (let (many (Rope) text)
                  (match many untagged _
                    ((BTrue) (match many shown (((Rope) r)) ((Nil b) (RStr "\"_\"")) ((Cons b s more) (match many more (((Rope) r)) ((Nil d) s) ((Cons d s2 more2) (rcat3 (RStr "\"(\" ^ ") (spaced shown) $ RStr " ^ \")\""))))))
                    ((BFalse) (rcat3 (RStr "\"(\" ^ ") (spaced $ Cons _ (quoted cname) shown) $ RStr " ^ \")\""))))
                (let (many (Rope) arm)
                  (match many untagged _
                    ((BTrue) (untuple-rope-names fnames (RStr "v") text))
                    ((BFalse) (rcat5 (RStr "| (") (nat-rope index) (rcat3 (RStr ", ") (bracketed fnames) $ RStr ") -> ") text $ REmpty))))
                (let (many memo3) (many more) $ show-arms k env ty rest memo2 untagged)
                (values memo3 $ match many live (((Rope) r)) ((BTrue) (rcat3 arm (RStr " ") more)) ((BFalse) more)))))))))

  (many show-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Bin) fids) (many (ShowMemo) memo) (many (Nat) i) -> (many (ShowMemo) memo2) (many (List $ Rope) shown)
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many fids _
          ((Nil a) (values memo $ Nil _))
          ((Cons a x rest)
            (let (many memo2) (many name) $ show-type k env (type-of env x) memo)
            (let (many memo3) (many more) $ show-fields k env rest memo2 $ Succ i)
            (values memo3 $ Cons _ (rcat3 (RStr name) (RStr " f") $ nat-rope i) more)))))))

(def-fns _ $ many show-defs : (many (ShowMemo) memo) -> (many (Rope) r)
  (match many memo _
    ((MkShowMemo count known defs)
      (match many defs _
        ((Nil a) (REmpty))
        ((Cons a d rest) (rcat3 (RStr "let rec ") (rjoin (list-rev _ defs) "\nand ") $ RStr "\n"))))))

(def-fns _ $ many emit-final : (many (Value) v) (many (Term) ty) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
  (match many (classify-final (cx-env cx) ty) _
    ((FMain)
      (let (many st2) (many vr) $ emit-value v cx st)
      (values st2 $ rcat3 (RStr "let () = run_main ") vr $ RStr "\n"))
    ((FIo)
      (let (many st2) (many vr) $ emit-value v cx st)
      (values st2 $ rcat3 (RStr "let () = exit (run_io ") vr $ RStr ")\n"))
    ((FThunk t)
      (let (many st2) (many vr) $ emit-value v cx st)
      (let (many memo) (many name) $ show-type show-fuel (cx-env cx) t $ MkShowMemo 0 (Nil _) $ Nil _)
      (values st2 $ rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " (app ") vr $ RStr " []))") $ RStr "\n"))
    ((FPlain)
      (values st $ rcat3 (RStr "let () = List.iter print_string [") (rope-literals (show-value v) $ REmpty) $ RStr "]; print_newline ()\n"))))

(def-fns _ $ many emit-items : (subterm many (List $ Trace) items) (many (EmitCx) cx) (many (EmitSt) st) -> (many (Rope) out)
  (match many items _
    ((Nil a) (REmpty))
    ((Cons a item rest)
      (let (many (EmitSt) st2) (many (Rope) text)
        (match many item _
          ((TrFns fns)
            (let (many st2) (many g) $ emit-top-group fns cx st)
            (values st2 $ rcat3 (RStr "let rec ") g $ RStr "\n"))
          ((TrConst x v)
            (let (many st2) (many vr) $ emit-value v cx st)
            (values st2 $ rcat4 (RStr "let ") (RStr $ top-name (cx-env cx) x) (RStr " = ") $ rcat vr $ RStr "\n"))
          ((TrFinal v ty) (emit-final v ty cx st))))
      (let (many st3) (many defs) $ st-take-defs st2)
      (rcat3 defs text $ emit-items rest cx st3))))

(def-fns _ $ many header-rope : (subterm many (List $ String) lines) -> (many (Rope) r)
  (match many lines _
    ((Nil a) (REmpty))
    ((Cons a l rest) (rcat3 (RStr l) (RStr "\n") $ header-rope rest))))

(def-fns _ $ many emit-program : (many (Env) env) -> (many (Rope) r)
  (let (many cx) $ MkEmitCx env $ env-values env)
  (let (many st) $ MkEmitSt (BZ) (Nil _) $ MEmpty _)
  (rcat (header-rope runtime-header) $ emit-items (list-rev _ $ env-trace env) cx st))
