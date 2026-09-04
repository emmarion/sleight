; self/emit.sl -- OCaml extraction of the traced program (self/README.md; lib/extract.ml): every run-position
; def-fns group becomes a let rec over the one runtime type v of self/runtime.ml, every Const the
; elaborator minted is embedded as data at its trace position, closures met inside data are hoisted with
; their captured values, and each final value is consumed as lib/program.ml would.

(def-adts $ EmitSt : -> Type
  enum
  (many MkEmitSt : (many (Bin) counter) (many (List (Rope)) defs) (many (IdMap (String)) names) -> (EmitSt)))

; [top]: the final environment's Const values, named at top level; [capture]: the environment of the
; closure being hoisted, or empty inside a run-position function.
(def-adts $ EmitCx : -> Type
  enum
  (many MkEmitCx : (many (Env) env) (many (IdMap (Value)) top) -> (EmitCx)))

(def-fns _ $ many cx-env : (many (EmitCx) cx) -> (many (Env) e) (match many cx _ ((MkEmitCx env top) env)))
(def-fns _ $ many cx-top : (many (EmitCx) cx) -> (many (IdMap (Value)) e) (match many cx _ ((MkEmitCx env top) top)))

(def-fns _ $ many st-names : (many (EmitSt) st) -> (many (IdMap (String)) r) (match many st _ ((MkEmitSt c d n) n)))
(def-fns _ $ many st-with-names : (many (EmitSt) st) (many (IdMap (String)) n) -> (many (EmitSt) r) (match many st _ ((MkEmitSt c d n0) (MkEmitSt c d n))))
(def-fns _ $ many st-push-def : (many (EmitSt) st) (many (Rope) d) -> (many (EmitSt) r) (match many st _ ((MkEmitSt c ds n) (MkEmitSt c (Cons (Rope) d ds) n))))
(def-fns _ $ many st-fresh : (many (EmitSt) st) -> (many (EmitSt) r) (many (Bin) x)
  (match many st _ ((MkEmitSt c ds n) (values (MkEmitSt (bin-succ (predates _) c) ds n) c))))
(def-fns _ $ many st-take-defs : (many (EmitSt) st) -> (many (EmitSt) r) (many (Rope) defs)
  (match many st _ ((MkEmitSt c ds n) (values (MkEmitSt c (Nil (Rope)) n) (rlist (predates _) (list-rev (predates _) (Rope) ds))))))

(def-fns _ $ many top-name : (many (Env) env) (many (Bin) x) -> (many (String) s)
  (str-cat (predates _) "v" (str-cat (predates _) (bin-str (predates _) x) (str-cat (predates _) "_" (sanitize (predates _) (name-of (predates _) env x))))))

(def-fns _ $ many quoted : (many (String) s) -> (many (Rope) r)
  (rcat3 (predates _) (RStr "\"") (RStr (ocaml-escape (predates _) s)) (RStr "\"")))

(def-fns _ $ many nat-rope : (many (Nat) n) -> (many (Rope) r)
  (RStr (nat-str (predates _) n)))

(def-fns _ $ many bracketed : (subterm many (List (Rope)) rs) -> (many (Rope) r)
  (rcat3 (predates _) (RStr "[") (rjoin (predates _) rs "; ") (RStr "]")))

(def-fns _ $ many names-of-ids : (subterm many (List (Bin)) ids) (many (Env) env) -> (many (List (Rope)) r)
  (match many ids _
    ((Nil a) (Nil (Rope)))
    ((Cons a x rest) (Cons (Rope) (RStr (top-name (predates _) env x)) (names-of-ids (subterm _) rest env)))))

; An OCaml pattern binding the ids: a list pattern of their names.
(def-fns _ $ many ids-pattern : (many (List (Bin)) ids) (many (Env) env) -> (many (Rope) r)
  (bracketed (predates _) (names-of-ids (predates _) ids env)))

; A tuple of values as the runtime keeps it: none is U, one is bare, more a Tup.
(def-fns _ $ many tuple-rope : (many (List (Rope)) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (RStr "U"))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (rcat3 (predates _) (RStr "(Tup ") (bracketed (predates _) rs) (RStr ")")))))))

; Binding the ids to a value of that shape.
(def-fns _ $ many untuple-rope : (many (List (Bin)) ids) (many (Rope) e) (many (Rope) body) (many (Env) env) -> (many (Rope) r)
  (match many ids _
    ((Nil a) (rcat5 (predates _) (RStr "(let _ = ") e (RStr " in ") body (RStr ")")))
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (predates _) (rcat3 (predates _) (RStr "(let ") (RStr (top-name (predates _) env x)) (RStr " = ")) e (RStr " in ") body (RStr ")")))
        ((Cons b y rest2) (rcat5 (predates _) (RStr "(match ") e (rcat3 (predates _) (RStr " with Tup ") (ids-pattern (predates _) ids env) (RStr " -> ")) body (RStr " | _ -> absurd ())")))))))

; Constructing a value from a constructor and the code of its many fields.
(def-fns _ $ many build-rope : (many (Ctor) c) (many (List (Rope)) args) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (predates _) (RStr "(con_") (RStr e) (rcat3 (predates _) (RStr " ") (nat-rope (predates _) index) (RStr " ")) (bracketed (predates _) args) (RStr ")")))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat5 (predates _) (RStr "(Tag (") (nat-rope (predates _) index) (RStr ", ") (bracketed (predates _) args) (RStr "))")))
            ((BFalse) (tuple-rope (predates _) args))))))))

(def-fns _ $ many ctor-fn-rope : (many (Ctor) c) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext)
      (match many ext _
        ((Some a e) (rcat5 (predates _) (RStr "(Fn (con_") (RStr e) (RStr " ") (nat-rope (predates _) index) (RStr "))")))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat3 (predates _) (RStr "(Fn (fun args -> Tag (") (nat-rope (predates _) index) (RStr ", args)))")))
            ((BFalse) (RStr "(Fn tuple)"))))))))

(def-fns _ $ many matchable-rope : (many (Adt) adt) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat3 (predates _) (RStr "(Mat (fun _ v -> des_") (RStr e) (RStr " v))")))
        ((None a)
          (match many tagged _
            ((BTrue) (RStr "(Mat (fun _ v -> des_tag v))"))
            ((BFalse) (RStr "(Mat (fun n v -> (0, untuple n v)))"))))))))

; The destructor a known shape reads a value through: the FFI's, the tag's, or the fields themselves.
(def-fns _ $ many des-rope : (many (Adt) adt) (many (Rope) scrut) -> (many (Rope) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _
        ((Some a e) (rcat4 (predates _) (RStr "(des_") (RStr e) (RStr " ") (rcat (predates _) scrut (RStr ")"))))
        ((None a) (rcat3 (predates _) (RStr "(des_tag ") scrut (RStr ")")))))))

(def-fns _ $ many adt-untagged : (many (Adt) adt) -> (many (Bool) r)
  (match many adt _
    ((MkAdt name tagged ctors ext)
      (match many ext _ ((Some a e) (BFalse)) ((None a) (not (predates _) tagged))))))

(def-fns _ $ many payload-rope : (many (Payload) p) -> (many (Rope) r)
  (match many p _
    ((PNat n) (rcat3 (predates _) (RStr "(Nat (Z.of_string \"") (nat-rope (predates _) n) (RStr "\"))")))
    ((PU8 u) (rcat3 (predates _) (RStr "(Nat (Z.of_string \"") (nat-rope (predates _) (u8-to-nat (predates _) u)) (RStr "\"))")))
    ((PBin b)
      (let (many n) (erased pf) (bin-to-nat (predates _) b))
      (rcat3 (predates _) (RStr "(Nat (Z.of_string \"") (nat-rope (predates _) n) (RStr "\"))")))
    ((PStr s) (rcat5 (predates _) (RStr "(Str (") (quoted (predates _) s) (RStr ", 0, ") (nat-rope (predates _) (str-length (predates _) s)) (RStr "))")))
    ((PDec i) (rcat3 (predates _) (RStr "(Nat (Z.of_string \"") (nat-rope (predates _) i) (RStr "\"))")))))

(def-fns _ $ many is-top : (many (EmitCx) cx) (many (Bin) x) -> (many (Bool) r)
  (idmap-mem (predates _) (Value) x (cx-top (predates _) cx)))

; A constructor a code names statically: a Const entry holding it, or the constant itself.
(def-fns _ $ many static-ctor : (many (EmitCx) cx) (many (Code) f) -> (many (Maybe (Ctor)) r)
  (match many f _
    ((CVar x)
      (match many (idmap-get (predates _) (Value) x (cx-top (predates _) cx)) _
        ((None a) (None (Ctor)))
        ((Some a v)
          (match many v _
            ((VCtorFn c) (Some (Ctor) c))
            ((VCtor c fs) (None (Ctor))) ((VTuple fs) (None (Ctor))) ((VExt ad p) (None (Ctor))) ((VMatchable ad) (None (Ctor)))
            ((VFn cl) (None (Ctor))) ((VToken) (None (Ctor))) ((VError m) (None (Ctor)))))))
    ((CConst v)
      (match many v _
        ((VCtorFn c) (Some (Ctor) c))
        ((VCtor c fs) (None (Ctor))) ((VTuple fs) (None (Ctor))) ((VExt ad p) (None (Ctor))) ((VMatchable ad) (None (Ctor)))
        ((VFn cl) (None (Ctor))) ((VToken) (None (Ctor))) ((VError m) (None (Ctor)))))
    ((CErased) (None (Ctor))) ((CValues cs) (None (Ctor))) ((CApp g a c) (None (Ctor))) ((CLet i r b) (None (Ctor)))
    ((CLetRec fs b) (None (Ctor))) ((CMatch s sh bs) (None (Ctor))) ((CAbsurd) (None (Ctor))) ((CError m) (None (Ctor)))))

; The closure whose code is being emitted is the recursion's first measure, and the code being emitted
; comes with a proof that it lies inside that closure: a captured variable's value is a subterm of the
; closure, a constant's value a subterm of the code, and a closure met inside a value a subterm of that
; value. A run-position group is emitted under a closure built around it, which captures nothing.
(let (many show-fuel) 100000)

; Gives each member of a group about to be hoisted its closure name.
(def-fns _ $ many name-group : (subterm many (List (Pair (Bin) (Func))) group) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Bool) ok)
  (match many group _
    ((Nil a) (values st (BTrue)))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y id fn)
          (let (many st2) (many n) (st-fresh (predates _) st))
          (let (many name) (str-cat (predates _) "cl" (str-cat (predates _) (bin-str (predates _) n) (str-cat (predates _) "_" (sanitize (predates _) (func-name (predates _) fn))))))
          (name-group (subterm _) rest (st-with-names (predates _) st2 (idmap-set (predates _) (String) id name (st-names (predates _) st2)))))))))

(def-fns _
  (many emit-code : (subterm many (Closure) cl) (subterm many (Code) code) (erased (Subterm (Code) code (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many code _
      ; A variable: a top-level Const or function by its name, a captured value embedded once under a fresh
      ; name, a hoisted group member by its closure name, or a local.
      ((CVar x)
        (match many (is-top (predates _) cx x) _
          ((BTrue) (values st (RStr (top-name (predates _) (cx-env (predates _) cx) x))))
          ((BFalse)
            (match many (idmap-get (predates _) (String) x (st-names (predates _) st)) _
              ((Some a name) (values st (RStr name)))
              ((None a)
                (match many cl _
                  ((MkClosure fn group cenv)
                    (match many (idmap-get-sub (predates _) (Value) x cenv) _
                      ((None b) (values st (RStr (top-name (predates _) (cx-env (predates _) cx) x))))
                      ((Some b hit)
                        (match many hit _
                          ((MkMapHit c d v p)
                            (let (many st2) (many n) (st-fresh (predates _) st))
                            (let (many name) (str-cat (predates _) "c" (str-cat (predates _) (bin-str (predates _) n) (str-cat (predates _) "_" (top-name (predates _) (cx-env (predates _) cx) x)))))
                            (let (erased q) (subterm-trans p (prove-subterm cenv cl)))
                            (let (many st3) (many vr) (emit-value (subterm q) v cx st2))
                            (let (many st4) (st-push-def (predates _) st3 (rcat4 (predates _) (RStr "let ") (RStr name) (RStr " = ") (rcat (predates _) vr (RStr "\n")))))
                            (values (st-with-names (predates _) st4 (idmap-set (predates _) (String) x name (st-names (predates _) st4))) (RStr name)))))))))))))
      ((CConst v)
        (let (erased q) (subterm-trans (prove-subterm v code) w))
        (emit-value (subterm q) v cx st))
      ((CErased) (values st (RStr "U")))
      ((CValues cs)
        (let (many st2) (many rs) (emit-codes cl (subterm _) cs (subterm-trans (prove-subterm cs code) w) cx st))
        (values st2 (tuple-rope (predates _) rs)))
      ((CApp f args cc)
        (let (many st2) (many rs) (emit-codes cl (subterm _) args (subterm-trans (prove-subterm args code) w) cx st))
        (match many (static-ctor (predates _) cx f) _
          ((Some a c) (values st2 (build-rope (predates _) c rs)))
          ((None a)
            (let (many st3) (many fr) (emit-code cl (subterm _) f (subterm-trans (prove-subterm f code) w) cx st2))
            (values st3 (rcat5 (predates _) (RStr "(app ") fr (RStr " ") (bracketed (predates _) rs) (RStr ")"))))))
      ((CLet ids rhs rest)
        (let (many st2) (many rr) (emit-code cl (subterm _) rhs (subterm-trans (prove-subterm rhs code) w) cx st))
        (let (many st3) (many br) (emit-code cl (subterm _) rest (subterm-trans (prove-subterm rest code) w) cx st2))
        (values st3 (untuple-rope (predates _) ids rr br (cx-env (predates _) cx))))
      ((CLetRec fns rest)
        (let (many st2) (many fr) (emit-group cl (subterm _) fns (subterm-trans (prove-subterm fns code) w) cx st (BFalse)))
        (let (many st3) (many br) (emit-code cl (subterm _) rest (subterm-trans (prove-subterm rest code) w) cx st2))
        (values st3 (rcat5 (predates _) (RStr "(let rec ") fr (RStr " in ") br (RStr ")"))))
      ((CMatch scrut shape branches)
        (let (many st2) (many sr) (emit-code cl (subterm _) scrut (subterm-trans (prove-subterm scrut code) w) cx st))
        (let (many arity) (match many branches (((Nat) n)) ((Nil a) 0) ((Cons a b rest) (match many b (((Nat) n)) ((MkBranch d ids body) (list-length (predates _) (Bin) ids))))))
        (match many shape _
          ((ShKnown adt)
            (match many (adt-untagged (predates _) adt) _
              ((BTrue)
                (match many branches _
                  ((Nil a) (values st2 (RStr "(absurd ())")))
                  ((Cons a b rest)
                    (match many b _
                      ((MkBranch d ids body)
                        (let (many st3) (many br) (emit-code cl (subterm _) body (subterm-trans (prove-subterm body code) w) cx st2))
                        (values st3 (untuple-rope (predates _) ids sr br (cx-env (predates _) cx))))))))
              ((BFalse)
                (let (many st3) (many arms) (emit-branches cl (subterm _) branches (subterm-trans (prove-subterm branches code) w) cx st2))
                (values st3 (rcat4 (predates _) (RStr "(match ") (des-rope (predates _) adt sr) (rcat (predates _) (RStr " with ") arms) (RStr " | _ -> absurd ())"))))))
          ((ShHeld mcode tags)
            (let (many st3) (many mr) (emit-code cl (subterm _) mcode (subterm-trans (prove-subterm mcode code) w) cx st2))
            (let (many st4) (many arms) (emit-branches cl (subterm _) branches (subterm-trans (prove-subterm branches code) w) cx st3))
            (values st4 (rcat5 (predates _) (RStr "(match (app_mat ") mr (rcat4 (predates _) (RStr " ") (nat-rope (predates _) arity) (RStr " ") sr) (rcat (predates _) (RStr ") with ") arms) (RStr " | _ -> absurd ())"))))))
      ((CAbsurd) (values st (RStr "(absurd ())")))
      ((CError m) (values st (rcat3 (predates _) (RStr "(failwith ") (quoted (predates _) m) (RStr ")"))))))

  (many emit-codes : (subterm many (Closure) cl) (subterm many (List (Code)) cs) (erased (Subterm (List (Code)) cs (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (List (Rope)) rs)
    (match many cs _
      ((Nil a) (values st (Nil (Rope))))
      ((Cons a c rest)
        (let (many st2) (many r) (emit-code cl (subterm _) c (subterm-trans (prove-subterm c cs) w) cx st))
        (let (many st3) (many rs) (emit-codes cl (subterm _) rest (subterm-trans (prove-subterm rest cs) w) cx st2))
        (values st3 (Cons (Rope) r rs)))))

  (many emit-branches : (subterm many (Closure) cl) (subterm many (List (Branch)) bs) (erased (Subterm (List (Branch)) bs (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many bs _
      ((Nil a) (values st (REmpty)))
      ((Cons a b rest)
        (match many b _
          ((MkBranch d ids body)
            (let (many st2) (many br) (emit-code cl (subterm _) body (subterm-trans (prove-subterm body bs) w) cx st))
            (let (many st3) (many more) (emit-branches cl (subterm _) rest (subterm-trans (prove-subterm rest bs) w) cx st2))
            (values st3 (rcat5 (predates _) (RStr "| (") (nat-rope (predates _) d) (rcat3 (predates _) (RStr ", ") (ids-pattern (predates _) ids (cx-env (predates _) cx)) (RStr ") -> ")) br more)))))))

  (many emit-value : (subterm many (Value) v) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many v _
      ((VCtor c fields)
        (let (many st2) (many rs) (emit-values (subterm _) fields cx st))
        (values st2 (build-rope (predates _) c rs)))
      ((VTuple fields)
        (let (many st2) (many rs) (emit-values (subterm _) fields cx st))
        (values st2 (tuple-rope (predates _) rs)))
      ((VExt adt p) (values st (payload-rope (predates _) p)))
      ((VCtorFn c) (values st (ctor-fn-rope (predates _) c)))
      ((VMatchable adt) (values st (matchable-rope (predates _) adt)))
      ((VFn cl)
        (match many cl _
          ((MkClosure fn group cenv)
            (match many (func-top (predates _) fn) _
              ((BTrue) (values st (RStr (top-name (predates _) (cx-env (predates _) cx) (func-id (predates _) fn)))))
              ((BFalse)
                (let (many saved) (st-names (predates _) st))
                (let (many st2) (many named) (name-group (predates _) group (st-with-names (predates _) st (MEmpty (String)))))
                (let (many st3) (many text) (emit-group (subterm _) cl group (prove-subterm group cl) cx st2 (BTrue)))
                (let (many st4) (st-push-def (predates _) st3 (rcat3 (predates _) (RStr "let rec ") text (RStr "\n"))))
                (let (many mine) (match many (idmap-get (predates _) (String) (func-id (predates _) fn) (st-names (predates _) st4)) (((String) s)) ((None a) "(failwith \"closure missing\")") ((Some a s) s)))
                (values (st-with-names (predates _) st4 saved) (RStr mine)))))))
      ((VToken) (values st (RStr "U")))
      ((VError m) (values st (rcat3 (predates _) (RStr "(failwith ") (quoted (predates _) m) (RStr ")"))))))

  (many emit-values : (subterm many (List (Value)) vs) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (List (Rope)) rs)
    (match many vs _
      ((Nil a) (values st (Nil (Rope))))
      ((Cons a v rest)
        (let (many st2) (many r) (emit-value (subterm _) v cx st))
        (let (many st3) (many rs) (emit-values (subterm _) rest cx st2))
        (values st3 (Cons (Rope) r rs)))))

  ; The definitions of a group, joined by and; hoisted groups are named through the state, local ones
  ; and run-position ones by their entries.
  (many emit-group : (subterm many (Closure) cl) (subterm many (List (Pair (Bin) (Func))) fns) (erased (Subterm (List (Pair (Bin) (Func))) fns (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) (many (Bool) hoisted) -> (many (EmitSt) st2) (many (Rope) r)
    (match many fns _
      ((Nil a) (values st (REmpty)))
      ((Cons a p rest)
        (match many p _
          ((MkPair x y id fn)
            (let (many name)
              (match many hoisted (((String) s))
                ((BFalse) (top-name (predates _) (cx-env (predates _) cx) id))
                ((BTrue) (match many (idmap-get (predates _) (String) id (st-names (predates _) st)) (((String) s)) ((None b) (top-name (predates _) (cx-env (predates _) cx) id)) ((Some b s) s)))))
            (let (many st2) (many body) (emit-fn cl (subterm _) fn (subterm-trans (prove-subterm fn fns) w) cx st))
            (let (many st3) (many more) (emit-group cl (subterm _) rest (subterm-trans (prove-subterm rest fns) w) cx st2 hoisted))
            (let (many sep) (match many rest (((Rope) r)) ((Nil b) (REmpty)) ((Cons b q rest2) (RStr "\nand "))))
            (values st3 (rcat5 (predates _) (RStr name) (RStr " = ") body sep more)))))))

  (many emit-fn : (subterm many (Closure) cl) (subterm many (Func) fn) (erased (Subterm (Func) fn (Closure) cl) w) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
    (match many fn _
      ((MkFunc name id params body impl top)
        (let (many ext) (match many impl (((Bool) b)) ((None a) (BFalse)) ((Some a n) (is-extern-fn (predates _) n))))
        (match many ext _
          ((BTrue) (values st (rcat3 (predates _) (RStr "Fn ext_") (RStr (sanitize (predates _) (match many impl (((String) s)) ((None a) "") ((Some a n) n)))) (REmpty))))
          ((BFalse)
            (let (many st2) (many br) (emit-code cl (subterm _) body (subterm-trans (prove-subterm body fn) w) cx st))
            (values st2 (rcat5 (predates _) (RStr "Fn (fun args -> match args with ") (ids-pattern (predates _) params (cx-env (predates _) cx)) (RStr " -> ") br (RStr " | _ -> absurd ())")))))))))

; A run-position group, emitted under a closure built around it.
(def-fns _ $ many emit-top-group : (many (List (Pair (Bin) (Func))) fns) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
  (let (many f0) (match many fns (((Func) f)) ((Nil a) (MkFunc "" (BZ) (Nil (Bin)) (CErased) (None (String)) (BTrue))) ((Cons a p rest) (match many p (((Func) f)) ((MkPair x y id fn) fn)))))
  (let (many cl) (MkClosure f0 fns (MEmpty (Value))))
  (emit-group (predates _) cl fns (prove-subterm fns cl) cx st (BFalse)))

; ---- Finals (lib/program.ml): what the driver does with a file's final value

(def-adts $ Final : -> Type
  enum
  (many FMain : -> (Final))
  (many FIo : -> (Final))
  (many FThunk : (many (Term) ty) -> (Final))
  (many FPlain : -> (Final)))

(def-fns _ $ many is-string-type : (many (Env) env) (many (Term) ty) -> (many (Bool) r)
  (match many (type-head (predates _) env ty) _
    ((None a) (BFalse))
    ((Some a t) (str-eq (predates _) (name-of (predates _) env t) "String"))))

(def-fns _ $ many classify-final : (many (Env) env) (many (Term) ty) -> (many (Final) f)
  (match many (canon-env (predates _) env ty) _
    ((TFn lv ps rs)
      (match many ps _
        ((Nil a)
          (match many rs _
            ((Cons b r more)
              (match many more _
                ((Nil c) (match many r _ ((MkEntry n s m sg) (match many m _ ((Many) (FThunk (sg-term (predates _) sg))) ((Erased) (FPlain))))))
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
                      (match many (and (predates _) (is-string-type (predates _) env (sg-term (predates _) (entry-sg (predates _) p)))
                                    (and (predates _) (is-string-type (predates _) env (sg-term (predates _) (entry-sg (predates _) r)))
                                      (and (predates _) (mult-is-many (predates _) (entry-mult (predates _) p)) (mult-is-many (predates _) (entry-mult (predates _) r))))) _
                        ((BTrue) (FMain))
                        ((BFalse) (FPlain))))))))))))
    ((TApp h args)
      (match many (type-head (predates _) env ty) _
        ((None a) (FPlain))
        ((Some a t) (match many (str-eq (predates _) (name-of (predates _) env t) "IO") _ ((BTrue) (FIo)) ((BFalse) (FPlain))))))
    ((TVar x) (FPlain)) ((TBound k) (FPlain)) ((TTyCtor p) (FPlain)) ((TValCtor p r) (FPlain)) ((TMatchable d t c) (FPlain)) ((TNewtype c) (FPlain)) ((TErr m) (FPlain))))

; The chunks of a rope as OCaml string literals, for printing a value computed at compile time.
(def-fns _ $ many rope-literals : (subterm many (Rope) r) (many (Rope) acc) -> (many (Rope) out)
  (match many r _
    ((REmpty) acc)
    ((RStr s) (rcat3 (predates _) (quoted (predates _) s) (RStr "; ") acc))
    ((RCat a b) (rope-literals (subterm _) a (rope-literals (subterm _) b acc)))))

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ ShowMemo : -> Type
  enum
  (many MkShowMemo : (many (Nat) count) (many (List (Pair (Term) (String))) known) (many (List (Rope)) defs) -> (ShowMemo)))

(def-fns _ $ many memo-find : (subterm many (List (Pair (Term) (String))) known) (many (Env) env) (many (Term) ty) -> (many (Maybe (String)) r)
  (match many known _
    ((Nil a) (None (String)))
    ((Cons a p rest)
      (match many p _
        ((MkPair x y t name)
          (match many (term-eq (predates _) t ty) _
            ((BTrue) (Some (String) name))
            ((BFalse) (memo-find (subterm _) rest env ty))))))))

(def-fns _ $ many spaced : (subterm many (List (Rope)) parts) -> (many (Rope) r)
  (match many parts _
    ((Nil a) (RStr "\"\""))
    ((Cons a p rest)
      (match many rest _
        ((Nil b) p)
        ((Cons b q rest2) (rcat3 (predates _) p (RStr " ^ \" \" ^ ") (spaced (subterm _) rest)))))))

(def-fns _ $ many field-names : (subterm many (Nat) n) (many (Nat) i) -> (many (List (Rope)) r)
  (match many n _
    ((Zero) (Nil (Rope)))
    ((Succ k) (Cons (Rope) (RStr (str-cat (predates _) "f" (nat-str (predates _) i))) (field-names (subterm _) k (Succ i))))))

(def-fns _ $ many adt-untagged-ext : (many (Maybe (String)) ext) (many (Bool) tagged) -> (many (Bool) r)
  (match many ext _ ((Some a e) (BFalse)) ((None a) (not (predates _) tagged))))

(def-fns _ $ many untuple-rope-names : (many (List (Rope)) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r)
  (match many names _
    ((Nil a) body)
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (predates _) (RStr "(let ") x (RStr " = ") (rcat3 (predates _) e (RStr " in ") body) (RStr ")")))
        ((Cons b y rest2) (rcat5 (predates _) (RStr "(match ") e (rcat3 (predates _) (RStr " with Tup ") (bracketed (predates _) names) (RStr " -> ")) body (RStr " | _ -> absurd ())")))))))

(def-fns _
  (many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) -> (many (ShowMemo) memo2) (many (String) name)
    (match many fuel _
      ((Zero) (values memo "show_any"))
      ((Succ k)
        (let (many ty) (canon-env (predates _) env ty0))
        (match many memo _
          ((MkShowMemo count known defs)
            (match many (memo-find (predates _) known env ty) _
              ((Some a name) (values memo name))
              ((None a)
                (let (many name) (str-cat (predates _) "show_" (nat-str (predates _) count)))
                (let (many memo1) (MkShowMemo (Succ count) (Cons (Pair (Term) (String)) (MkPair (Term) (String) ty name) known) defs))
                (let (many memo2) (many body)
                  (match many ty (((ShowMemo) m) ((Rope) r))
                    ((TApp h args)
                      (match many (type-head (predates _) env ty) (((ShowMemo) m) ((Rope) r))
                        ((None b) (values memo1 (RStr "\"?\"")))
                        ((Some b tid)
                          (let (many envf) (many foundm) (find-matchable (predates _) env tid))
                          (match many foundm (((ShowMemo) m) ((Rope) r))
                            ((None c) (values memo1 (RStr "\"?\"")))
                            ((Some c info)
                              (match many info (((ShowMemo) m) ((Rope) r))
                                ((MkMatchInfo mid disc mctors rank)
                                  (match many (adt-of (predates _) env mid) (((ShowMemo) m) ((Rope) r))
                                    ((None d) (values memo1 (RStr "\"?\"")))
                                    ((Some d adt)
                                      (match many adt (((ShowMemo) m) ((Rope) r))
                                        ((MkAdt aname tagged ctors ext)
                                          (let (many memo3) (many arms) (show-arms (subterm _) k env ty ctors memo1 (adt-untagged-ext (predates _) ext tagged)))
                                          (match many (adt-untagged-ext (predates _) ext tagged) (((ShowMemo) m) ((Rope) r))
                                            ((BTrue) (values memo3 arms))
                                            ((BFalse) (values memo3 (rcat3 (predates _) (rcat (predates _) (RStr "match ") (des-rope (predates _) adt (RStr "v"))) (rcat (predates _) (RStr " with ") arms) (RStr " | _ -> \"?\""))))))))))))))))
                    ((TFn l ps rs) (values memo1 (RStr "\"<function ?>\"")))
                    ((TValCtor ps r) (values memo1 (RStr "\"<constructor ?>\"")))
                    ((TVar x) (values memo1 (RStr "\"?\""))) ((TBound j) (values memo1 (RStr "\"?\""))) ((TTyCtor ps) (values memo1 (RStr "\"?\"")))
                    ((TMatchable d t c) (values memo1 (RStr "\"?\""))) ((TNewtype c) (values memo1 (RStr "\"?\""))) ((TErr m) (values memo1 (RStr "\"?\"")))))
                (match many memo2 _
                  ((MkShowMemo count2 known2 defs2)
                    (values (MkShowMemo count2 known2 (Cons (Rope) (rcat4 (predates _) (RStr name) (RStr " (v : v) : string = ") body (REmpty)) defs2)) name))))))))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, its fields shown
  ; only then, as the reference's exception skips them; an untagged type has one arm reading the fields as they stand.
  (many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List (Ctor)) ctors) (many (ShowMemo) memo) (many (Bool) untagged) -> (many (ShowMemo) memo2) (many (Rope) arms)
    (match many fuel _
      ((Zero) (values memo (REmpty)))
      ((Succ k)
        (match many ctors _
          ((Nil a) (values memo (REmpty)))
          ((Cons a c rest)
            (match many c _
              ((MkCtor cname cid index arity tagged ext)
                (let (many ctele) (many ret) (ctor-type (predates _) env cid))
                (let (many envb) (many fids) (open-tele (predates _) ctele env (None (List (Maybe (String)))) (None (List (Mult))) (None (List (State))) (Nil (Term))))
                (let (many envb2) (many live)
                  (match many (unify-env (predates _) envb (instantiate (predates _) (tvars-rev (predates _) fids (Nil (Term))) ret) ty) (((Env) e) ((Bool) b))
                    ((UOk e2) (values e2 (BTrue)))
                    ((UContra msg) (values envb (BFalse)))))
                (let (many memo2) (many shown)
                  (match many live (((ShowMemo) m) ((List (Rope)) r))
                    ((BTrue) (show-fields (subterm _) k envb2 (non-erased (predates _) fids envb2) memo 0))
                    ((BFalse) (values memo (Nil (Rope))))))
                (let (many fnames) (field-names (predates _) arity 0))
                (let (many text)
                  (match many untagged (((Rope) r))
                    ((BTrue) (match many shown (((Rope) r)) ((Nil b) (RStr "\"_\"")) ((Cons b s more) (match many more (((Rope) r)) ((Nil d) s) ((Cons d s2 more2) (rcat3 (predates _) (RStr "\"(\" ^ ") (spaced (predates _) shown) (RStr " ^ \")\"")))))))
                    ((BFalse) (rcat3 (predates _) (RStr "\"(\" ^ ") (spaced (predates _) (Cons (Rope) (quoted (predates _) cname) shown)) (RStr " ^ \")\"")))))
                (let (many arm)
                  (match many untagged (((Rope) r))
                    ((BTrue) (untuple-rope-names (predates _) fnames (RStr "v") text))
                    ((BFalse) (rcat5 (predates _) (RStr "| (") (nat-rope (predates _) index) (rcat3 (predates _) (RStr ", ") (bracketed (predates _) fnames) (RStr ") -> ")) text (REmpty)))))
                (let (many memo3) (many more) (show-arms (subterm _) k env ty rest memo2 untagged))
                (values memo3 (match many live (((Rope) r)) ((BTrue) (rcat3 (predates _) arm (RStr " ") more)) ((BFalse) more))))))))))

  (many show-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List (Bin)) fids) (many (ShowMemo) memo) (many (Nat) i) -> (many (ShowMemo) memo2) (many (List (Rope)) shown)
    (match many fuel _
      ((Zero) (values memo (Nil (Rope))))
      ((Succ k)
        (match many fids _
          ((Nil a) (values memo (Nil (Rope))))
          ((Cons a x rest)
            (let (many memo2) (many name) (show-type (subterm _) k env (type-of (predates _) env x) memo))
            (let (many memo3) (many more) (show-fields (subterm _) k env rest memo2 (Succ i)))
            (values memo3 (Cons (Rope) (rcat3 (predates _) (RStr name) (RStr " f") (nat-rope (predates _) i)) more))))))))

(def-fns _ $ many show-defs : (many (ShowMemo) memo) -> (many (Rope) r)
  (match many memo _
    ((MkShowMemo count known defs)
      (match many defs _
        ((Nil a) (REmpty))
        ((Cons a d rest) (rcat3 (predates _) (RStr "let rec ") (rjoin (predates _) (list-rev (predates _) (Rope) defs) "\nand ") (RStr "\n")))))))

(def-fns _ $ many emit-final : (many (Value) v) (many (Term) ty) (many (EmitCx) cx) (many (EmitSt) st) -> (many (EmitSt) st2) (many (Rope) r)
  (match many (classify-final (predates _) (cx-env (predates _) cx) ty) _
    ((FMain)
      (let (many st2) (many vr) (emit-value (predates _) v cx st))
      (values st2 (rcat3 (predates _) (RStr "let () = run_main ") vr (RStr "\n"))))
    ((FIo)
      (let (many st2) (many vr) (emit-value (predates _) v cx st))
      (values st2 (rcat3 (predates _) (RStr "let () = exit (run_io ") vr (RStr ")\n"))))
    ((FThunk t)
      (let (many st2) (many vr) (emit-value (predates _) v cx st))
      (let (many memo) (many name) (show-type (predates _) show-fuel (cx-env (predates _) cx) t (MkShowMemo 0 (Nil (Pair (Term) (String))) (Nil (Rope)))))
      (values st2 (rcat5 (predates _) (show-defs (predates _) memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (predates _) (RStr " (app ") vr (RStr " []))")) (RStr "\n"))))
    ((FPlain)
      (values st (rcat3 (predates _) (RStr "let () = List.iter print_string [") (rope-literals (predates _) (show-value (predates _) v) (REmpty)) (RStr "]; print_newline ()\n"))))))

(def-fns _ $ many emit-items : (subterm many (List (Trace)) items) (many (EmitCx) cx) (many (EmitSt) st) -> (many (Rope) out)
  (match many items _
    ((Nil a) (REmpty))
    ((Cons a item rest)
      (let (many st2) (many text)
        (match many item (((EmitSt) s) ((Rope) r))
          ((TrFns fns)
            (let (many st2) (many g) (emit-top-group (predates _) fns cx st))
            (values st2 (rcat3 (predates _) (RStr "let rec ") g (RStr "\n"))))
          ((TrConst x v)
            (let (many st2) (many vr) (emit-value (predates _) v cx st))
            (values st2 (rcat4 (predates _) (RStr "let ") (RStr (top-name (predates _) (cx-env (predates _) cx) x)) (RStr " = ") (rcat (predates _) vr (RStr "\n")))))
          ((TrFinal v ty) (emit-final (predates _) v ty cx st))))
      (let (many st3) (many defs) (st-take-defs (predates _) st2))
      (rcat3 (predates _) defs text (emit-items (subterm _) rest cx st3)))))

(def-fns _ $ many header-rope : (subterm many (List (String)) lines) -> (many (Rope) r)
  (match many lines _
    ((Nil a) (REmpty))
    ((Cons a l rest) (rcat3 (predates _) (RStr l) (RStr "\n") (header-rope (subterm _) rest)))))

(def-fns _ $ many emit-program : (many (Env) env) -> (many (Rope) r)
  (let (many cx) (MkEmitCx env (env-values (predates _) env)))
  (let (many st) (MkEmitSt (BZ) (Nil (Rope)) (MEmpty (String))))
  (rcat (predates _) (header-rope (predates _) runtime-header) (emit-items (predates _) (list-rev (predates _) (Trace) (env-trace (predates _) env)) cx st)))
