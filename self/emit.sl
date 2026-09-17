; self/emit.sl -- OCaml extraction of the elaborated program (self/README.md; lib/extract.ml): every block of
; the store that a Const or a final value reaches becomes one let in address order, so that sharing is the
; store's; a group's block is a top-level let rec over its members; and each final value is consumed as
; lib/program.ml would.

(def-fns _ $ many top-name : (many (Env) env) (many (Nat) x) -> (many (String) s)
  (str-cat "v" $ str-cat (nat-str x) $ str-cat "_" $ sanitize $ name-of env x))

(let (many show-fuel) 100000)

(def-fns _ $ many quoted : (many (String) s) -> (many (Rope) r)
  (rcat3 (RStr "\"") (ocaml-escape s) $ RStr "\""))

(def-fns _ $ many nat-rope : (many (Nat) n) -> (many (Rope) r)
  (RStr $ nat-str n))

(def-fns _ $ many nat-literal : (many (Nat) n) -> (many (Rope) r)
  (rcat3 (RStr "(Obj.repr (Z.of_string \"") (nat-rope n) $ RStr "\"))"))

(def-fns _ $ many bracketed : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (rcat3 (RStr "[") (rjoin rs "; ") $ RStr "]"))

(def-fns _ $ many commas : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (rjoin rs ", "))

(def-fns _ $ many names-of-ids : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Rope) r)
  (match many ids _
    ((Nil a) (Nil _))
    ((Cons a x rest) (Cons _ (RStr $ top-name env x) $ names-of-ids rest env))))

(def-fns _ $ many field-names : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Rope) r)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat "f" $ nat-str i) $ field-names k $ Succ i))))

(def-fns _ $ many nat-range : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Nat) r)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ i $ nat-range k $ Succ i))))

; A tuple of values as the runtime keeps it: none is unit, one is bare, more an OCaml tuple.
(def-fns _ $ many tuple-rope : (many (List $ Rope) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (RStr "(Obj.repr ())"))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (rcat3 (RStr "(Obj.repr (") (commas rs) $ RStr "))"))))))

(def-fns _ $ many obj-tuple : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (REmpty))
    ((Cons a r rest) (match many rest _ ((Nil b) (RStr "Obj.t")) ((Cons b r2 rest2) (rcat (RStr "Obj.t * ") $ obj-tuple rest))))))

; Binding the names to a value of that shape.
(def-fns _ $ many untuple-rope : (many (List $ Rope) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r)
  (match many names _
    ((Nil a) body)
    ((Cons a x rest)
      (match many rest _
        ((Nil b) (rcat5 (RStr "(let ") x (RStr " = ") (rcat3 e (RStr " in ") body) $ RStr ")"))
        ((Cons b y rest2) (rcat5 (RStr "(let (") (commas names) (rcat5 (RStr ") = (Obj.obj ") e (RStr " : ") (obj-tuple names) $ RStr ") in ") body $ RStr ")"))))))

(def-fns _ $ many params-rope : (many (List $ Rope) ps) -> (many (Rope) r)
  (match many ps _
    ((Nil a) (RStr "()"))
    ((Cons a p rest) (rcat3 (RStr "(") (rjoin ps " : Obj.t) (") $ RStr " : Obj.t)"))))

(def-fns _ $ many arrows-tail : (subterm many (List $ Rope) args) -> (many (Rope) r)
  (match many args _
    ((Nil a) (RStr "Obj.t"))
    ((Cons a x rest) (rcat (RStr "Obj.t -> ") $ arrows-tail rest))))

(def-fns _ $ many arrows-rope : (many (List $ Rope) args) -> (many (Rope) r)
  (match many args _
    ((Nil a) (RStr "unit -> Obj.t"))
    ((Cons a x rest) (arrows-tail args))))

(def-fns _ $ many args-rope : (many (List $ Rope) args) -> (many (Rope) r)
  (match many args _
    ((Nil a) (RStr "()"))
    ((Cons a x rest) (rjoin args " "))))

; A call of a value whose OCaml name is unknown: the closure coerced to the call's arity.
(def-fns _ $ many dyn-call : (many (Rope) f) (many (List $ Rope) args) -> (many (Rope) r)
  (rcat5 (RStr "((Obj.obj ") f (rcat3 (RStr " : ") (arrows-rope args) $ RStr ") ") (args-rope args) $ RStr ")"))

(def-fns _ $ many lambda-rope : (many (List $ Rope) ps) (many (Rope) body) -> (many (Rope) r)
  (rcat5 (RStr "(fun ") (params-rope ps) (RStr " -> ") body $ RStr ")"))

; ---- The declarations a program needs (lib/extract.ml's shape table): the tagged shapes met, numbered by
; first sight, and the phantom-index copies narrowing a shape to a match's live constructors.

(def-adts $ Narrow : -> Type
  enum
  (many MkNarrow : (many (List $ Nat) shape) (many (List $ Nat) live) -> (Narrow)))

; ---- Extraction templates (lib/ffi_templates.txt, ASSUMPTIONS 133): an extern type's matches and builds as
; OCaml text with holes, embedded as header.sl's extern-templates; a type without one is taken apart and
; built through its view as before.

(def-adts $ Hole : -> Type
  enum
  (many HScrut : -> (Hole))
  (many HBody : (many (Nat) i) -> (Hole))
  (many HField : (many (Nat) i) (many (Nat) j) -> (Hole))
  (many HArg : (many (Nat) i) -> (Hole))
  (many HTemp : (many (Nat) k) -> (Hole)))

(def-adts $ Piece : -> Type
  enum
  (many PLit : (many (String) s) -> (Piece))
  (many PHole : (many (Hole) h) -> (Piece)))

(def-adts $ Template : -> Type
  enum
  (many MkTemplate : (many (Bool) building) (many (String) type) (many (Nat) index) (many (List $ Piece) pieces) -> (Template)))

(def-fns _ $ many str-until-onto : (many (Rope) acc) (subterm many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after)
  (match many s _
    ((SNil) (values (rope-str acc) (None _)))
    ((SCons c rest)
      (match many (char-is c code) _
        ((BTrue) (values (rope-str acc) (Some _ rest)))
        ((BFalse) (tail (str-until-onto (RCat acc $ RChar c) rest code)))))))

(def-fns _ $ many str-until : (many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after)
  (str-until-onto (REmpty) s code))

(def-fns _ $ many str-split-fuel : (subterm many (Nat) fuel) (many (String) s) (many (Nat) code) -> (many (List $ String) r)
  (let (many b) (many a) (str-until s code))
  (match many a _
    ((None t) (Cons _ b $ Nil _))
    ((Some t rest)
      (match many fuel _
        ((Zero) (Cons _ b $ Nil _))
        ((Succ f) (Cons _ b $ str-split-fuel f rest code))))))

(def-fns _ $ many split-on : (many (String) s) (many (Nat) code) -> (many (List $ String) r)
  (let (many n) (erased p) (str-length s))
  (str-split-fuel n s code))

(def-fns _ $ many digits-of : (many (String) s) -> (many (Maybe $ Nat) r)
  (match many (and (not $ str-is-empty s) $ all-digits s) _
    ((BTrue) (Some _ $ parse-nat s 0))
    ((BFalse) (None _))))

(def-fns _ $ many parse-hole : (many (String) h) -> (many (Maybe $ Hole) r)
  (match many h _
    ((SNil) (None _))
    ((SCons c rest)
      (match many (char-is c 115) _
        ((BTrue) (match many (str-is-empty rest) _ ((BTrue) (Some _ $ HScrut)) ((BFalse) (None _))))
        ((BFalse)
          (match many (char-is c 102) _
            ((BTrue)
              (match many (split-on rest 46) _
                ((Cons a i more)
                  (match many more _
                    ((Cons b j none)
                      (match many none _
                        ((Nil d)
                          (match many (digits-of i) _
                            ((Some e ni) (match many (digits-of j) _ ((Some g nj) (Some _ $ HField ni nj)) ((None g) (None _))))
                            ((None e) (None _))))
                        ((Cons d z w) (None _))))
                    ((Nil b) (None _))))
                ((Nil a) (None _))))
            ((BFalse)
              (match many (digits-of rest) _
                ((None a) (None _))
                ((Some a n)
                  (match many (char-is c 98) _
                    ((BTrue) (Some _ $ HBody n))
                    ((BFalse)
                      (match many (char-is c 97) _
                        ((BTrue) (Some _ $ HArg n))
                        ((BFalse) (match many (char-is c 116) _ ((BTrue) (Some _ $ HTemp n)) ((BFalse) (None _))))))))))))))))

; The pieces of a template's text, accumulated in reverse; a malformed hole stays as text for the OCaml
; compiler to refuse.
(def-fns _ $ many parse-pieces : (subterm many (Nat) fuel) (many (String) s) (many (List $ Piece) acc) -> (many (List $ Piece) r)
  (let (many lit) (many after) (str-until s 123))
  (let (many (List $ Piece) acc1) $ match many (str-is-empty lit) _ ((BTrue) acc) ((BFalse) (Cons _ (PLit lit) acc)))
  (match many after _
    ((None t) (list-rev _ acc1))
    ((Some t rest)
      (let (many name) (many after2) (str-until rest 125))
      (let (many (Piece) piece) $ match many (parse-hole name) _ ((Some u h) (PHole h)) ((None u) (PLit $ str-cat3 "{" name "}")))
      (match many after2 _
        ((None u) (list-rev _ $ Cons _ piece acc1))
        ((Some u rest2)
          (match many fuel _
            ((Zero) (list-rev _ $ Cons _ piece acc1))
            ((Succ f) (parse-pieces f rest2 $ Cons _ piece acc1))))))))

(def-fns _ $ many parse-template : (many (String) line) -> (many (Maybe $ Template) r)
  (let (many head) (many after) (str-until line 58))
  (match many after _
    ((None t) (None _))
    ((Some t text)
      (let (many n) (erased p) (str-length text))
      (let (many pieces) $ parse-pieces n text $ Nil _)
      (match many (split-on head 32) _
        ((Cons a kind more)
          (match many more _
            ((Cons b type rest)
              (match many (str-eq kind "match") _
                ((BTrue) (Some _ $ MkTemplate (BFalse) type 0 pieces))
                ((BFalse)
                  (match many rest _
                    ((Cons c i none)
                      (match many (digits-of i) _
                        ((Some e n) (match many (str-eq kind "build") _ ((BTrue) (Some _ $ MkTemplate (BTrue) type n pieces)) ((BFalse) (None _))))
                        ((None e) (None _))))
                    ((Nil c) (None _))))))
            ((Nil b) (None _))))
        ((Nil a) (None _))))))

(def-fns _ $ many parse-templates : (subterm many (List $ String) lines) -> (many (List $ Template) r)
  (match many lines _
    ((Nil a) (Nil _))
    ((Cons a line rest)
      (match many (parse-template line) _
        ((Some b t) (Cons _ t $ parse-templates rest))
        ((None b) (parse-templates rest))))))

(def-fns _ $ many same-bool : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) b) ((BFalse) (not b))))

(def-fns _ $ many find-template : (subterm many (List $ Template) ts) (many (Bool) building) (many (String) type) (many (Nat) index) -> (many (Maybe $ List $ Piece) r)
  (match many ts _
    ((Nil a) (None _))
    ((Cons a t rest)
      (match many t _
        ((MkTemplate b ty i ps)
          (match many (and (same-bool b building) $ and (str-eq ty type) $ nat-eq i index) _
            ((BTrue) (Some _ ps))
            ((BFalse) (find-template rest building type index))))))))

(def-fns _ $ many str-is-name : (subterm many (String) s) -> (many (Bool) r)
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (or (char-is c 95) $ or (char-is c 39) $ or (char-between c 48 57) $ or (char-between c 97 122) $ char-between c 65 90) $ str-is-name rest))))

(def-fns _ $ many rope-is-name : (many (Rope) r) -> (many (Bool) b)
  (let (many s) $ rope-str r)
  (and (not $ str-is-empty s) $ str-is-name s))

(def-adts $ Decls : -> Type
  enum
  (many MkDecls : (many (List $ List $ Nat) shapes) (many (List $ Narrow) narrows) (many (List $ Template) templates) -> (Decls)))

(def-fns _ $ many decl-templates : (many (Decls) d) -> (many (List $ Template) ts)
  (match many d _ ((MkDecls shapes narrows ts) ts)))

(def-fns _ $ many shape-index : (subterm many (List $ List $ Nat) ss) (many (List $ Nat) s) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many ss _
    ((Nil t) (None _))
    ((Cons t x rest) (match many (nat-list-eq x s) _ ((BTrue) (Some _ i)) ((BFalse) (shape-index rest s $ Succ i))))))

(def-fns _ $ many narrow-index : (subterm many (List $ Narrow) ns) (many (List $ Nat) s) (many (List $ Nat) live) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many ns _
    ((Nil t) (None _))
    ((Cons t n rest)
      (match many n _
        ((MkNarrow s2 live2) (match many (and (nat-list-eq s2 s) $ nat-list-eq live2 live) _ ((BTrue) (Some _ i)) ((BFalse) (narrow-index rest s live $ Succ i))))))))

(def-fns _ $ many index-str : (many (Maybe $ Nat) i) -> (many (String) s)
  (match many i _ ((Some a n) (nat-str n)) ((None a) "missing")))

(def-fns _ $ many shape-name : (many (Decls) d) (many (List $ Nat) s) -> (many (String) r)
  (match many d _ ((MkDecls shapes narrows ts) (str-cat "t" $ index-str $ shape-index shapes s 0))))

(def-fns _ $ many ctor-name-at : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) -> (many (String) r)
  (match many d _ ((MkDecls shapes narrows ts) (str-cat3 "K" (index-str $ shape-index shapes s 0) $ str-cat "_" $ nat-str i))))

(def-fns _ $ many narrow-name : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (String) r)
  (match many d _ ((MkDecls shapes narrows ts) (str-cat3 (shape-name d s) "_n" $ index-str $ narrow-index narrows s live 0))))

(def-fns _ $ many add-shape : (many (List $ List $ Nat) ss) (many (List $ Nat) s) -> (many (List $ List $ Nat) r)
  (match many (shape-index ss s 0) _
    ((Some a i) ss)
    ((None a) (let (many r) (erased p) $ list-append _ ss $ Cons _ s $ Nil _) r)))

(def-fns _ $ many decl-shape : (many (Decls) d) (many (List $ Nat) s) -> (many (Decls) r)
  (match many d _ ((MkDecls shapes narrows ts) (MkDecls (add-shape shapes s) narrows ts))))

(def-fns _ $ many decl-narrow : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (Decls) r)
  (match many d _
    ((MkDecls shapes narrows ts)
      (match many (narrow-index narrows s live 0) _
        ((Some a i) d)
        ((None a)
          (let (many r) (erased p) $ list-append _ narrows $ Cons _ (MkNarrow s live) $ Nil _)
          (MkDecls (add-shape shapes s) r ts))))))

(def-fns _ $ many nat-insert : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r)
  (match many xs _
    ((Nil a) (Cons _ x $ Nil _))
    ((Cons a y rest)
      (match many (nat-cmp x y) _
        ((CLt lt-t lt-r lt-x lt-y lt-p) (Cons _ x xs))
        ((CEq eq-t eq-r eq-x) xs)
        ((CGt gt-t gt-r gt-x gt-y gt-p) (Cons _ y $ nat-insert x rest))))))

; The key of a narrowing: the live discriminants sorted, each once.
(def-fns _ $ many live-key : (subterm many (List $ Nat) live) -> (many (List $ Nat) r)
  (match many live _
    ((Nil a) (Nil _))
    ((Cons a x rest) (nat-insert x $ live-key rest))))

(def-fns _ $ many adt-shape : (many (Adt) adt) -> (many (List $ Nat) r)
  (ctor-arities $ adt-ctors adt))

; Whether the live set leaves a constructor out, so the match is on a narrowed copy of the shape.
(def-fns _ $ many narrowed : (many (Adt) adt) (many (List $ Nat) live) -> (many (Bool) r)
  (nat-lt (list-length _ $ live-key live) $ list-length _ $ adt-ctors adt))

; ---- Constructing, taking apart, and the runtime forms of constructors and Matchables

(def-fns _ $ many pattern-rope : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) (many (List $ Rope) fs) -> (many (Rope) r)
  (match many fs _
    ((Nil a) (RStr $ ctor-name-at d s i))
    ((Cons a f rest) (rcat3 (RStr $ str-cat (ctor-name-at d s i) " (") (commas fs) $ RStr ")"))))

(def-adts $ Arm : -> Type
  enum
  (many MkArm : (many (Nat) d) (many (List $ Rope) fs) (many (Rope) body) -> (Arm)))

; A template filled: the scrutinee's name, the prefix of this instantiation's temporaries (the nesting
; depth, distinct along any path since a body sits in tail position and every other hole is a name), the
; arms and live set, the default's text, and the build arguments' names.
(def-adts $ Filling : -> Type
  enum
  (many MkFilling : (many (String) scrut) (many (String) prefix) (many (List $ Arm) arms) (many (List $ Nat) live) (many (Rope) dflt) (many (List $ Rope) args) -> (Filling)))

(def-fns _ $ many arm-at : (subterm many (List $ Arm) arms) (many (Nat) i) -> (many (Maybe $ Arm) r)
  (match many arms _
    ((Nil a) (None _))
    ((Cons a arm rest) (match many arm _ ((MkArm d fs body) (match many (nat-eq d i) _ ((BTrue) (Some _ arm)) ((BFalse) (arm-at rest i))))))))

(def-fns _ $ many nat-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest) (or (nat-eq x y) $ nat-mem rest x))))

(def-fns _ $ many fill-hole : (many (Filling) f) (many (Hole) h) -> (many (Rope) r)
  (match many f _
    ((MkFilling scrut prefix arms live dflt args)
      (match many h _
        ((HScrut) (RStr scrut))
        ((HTemp k) (RStr $ str-cat3 prefix "_t" $ nat-str k))
        ((HArg i) (list-nth-or _ args i $ RStr "(absurd ())"))
        ((HBody i)
          (match many (arm-at arms i) _
            ((Some a arm) (match many arm _ ((MkArm d fs body) body)))
            ((None a) (match many (nat-mem live i) _ ((BTrue) dflt) ((BFalse) (RStr "(absurd ())"))))))
        ((HField i j)
          (match many (arm-at arms i) _
            ((Some a arm) (match many arm _ ((MkArm d fs body) (list-nth-or _ fs j $ RStr "_"))))
            ((None a) (RStr $ str-cat3 prefix "_f" $ str-cat3 (nat-str i) "_" $ nat-str j))))))))

(def-fns _ $ many fill-pieces : (subterm many (List $ Piece) ps) (many (Filling) f) -> (many (Rope) r)
  (match many ps _
    ((Nil a) (REmpty))
    ((Cons a p rest)
      (rcat (match many p (((Rope) r)) ((PLit s) (RStr s)) ((PHole h) (fill-hole f h))) $ fill-pieces rest f))))

; Each build argument as the name the template reads: its own when it is one, else a temporary bound to it.
(def-fns _ $ many bind-args : (many (String) prefix) (subterm many (List $ Rope) args) (many (Nat) i) -> (many (List $ Rope) names) (many (List $ Rope) binds)
  (match many args _
    ((Nil a) (values (Nil _) (Nil _)))
    ((Cons a arg rest)
      (let (many names) (many binds) (bind-args prefix rest (Succ i)))
      (match many (rope-is-name arg) _
        ((BTrue) (values (Cons _ arg names) binds))
        ((BFalse)
          (let (many x) $ str-cat3 prefix "_a" $ nat-str i)
          (values (Cons _ (RStr x) names) $ Cons _ (rcat (RStr $ str-cat x " = ") arg) binds))))))

(def-fns _ $ many templated-build : (many (List $ Piece) ps) (many (Nat) depth) (many (List $ Rope) args) -> (many (Rope) r)
  (let (many prefix) $ str-cat "x" $ nat-str depth)
  (let (many names) (many binds) (bind-args prefix args 0))
  (let (many text) $ fill-pieces ps $ MkFilling "" prefix (Nil _) (Nil _) (REmpty) names)
  (match many binds _
    ((Nil a) (rcat3 (RStr "(") text $ RStr ")"))
    ((Cons a b rest) (rcat5 (RStr "(let ") (rjoin binds " and ") (RStr " in ") text $ RStr ")"))))

; How many of the constructors from i on the default stands for: those live with no arm of their own.
(def-fns _ $ many count-defaulted : (subterm many (Nat) n) (many (Nat) i) (many (List $ Arm) arms) (many (List $ Nat) live) -> (many (Nat) r)
  (match many n _
    ((Zero) 0)
    ((Succ k)
      (let (many rest) $ count-defaulted k (Succ i) arms live)
      (match many (and (nat-mem live i) $ match many (arm-at arms i) (((Bool) b)) ((None a) (BTrue)) ((Some a x) (BFalse))) _
        ((BTrue) (Succ rest))
        ((BFalse) rest)))))

; A match through its template: the scrutinee bound to a name unless it is one, a default filling more
; than one arm bound once as a thunk so its text is written once, and each arm's body in place.
(def-fns _ $ many templated-dispatch : (many (List $ Piece) ps) (many (Nat) depth) (many (Nat) ctors) (many (List $ Nat) live) (many (Rope) scrut0) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r)
  (let (many prefix) $ str-cat "x" $ nat-str depth)
  (let (many (Rope) dr) (many (Rope) open) (many (Rope) close)
    (match many dflt _
      ((None a) (values (RStr "(absurd ())") (REmpty) (REmpty)))
      ((Some a d)
        (match many (nat-lt 1 $ count-defaulted ctors 0 arms live) _
          ((BTrue) (values (RStr $ str-cat3 "(" prefix "_d ())") (rcat3 (RStr $ str-cat3 "(let " prefix "_d () = ") d $ RStr " in ") (RStr ")")))
          ((BFalse) (values d (REmpty) (REmpty)))))))
  (let (many (String) name) (many (Rope) bind-open) (many (Rope) bind-close)
    (match many (rope-is-name scrut0) _
      ((BTrue) (values (rope-str scrut0) (REmpty) (REmpty)))
      ((BFalse) (values prefix (rcat3 (RStr $ str-cat3 "(let " prefix " = ") scrut0 $ RStr " in ") (RStr ")")))))
  (let (many text) $ fill-pieces ps $ MkFilling name prefix arms live dr (Nil _))
  (rcat5 bind-open open (rcat3 (RStr "(") text $ RStr ")") close bind-close))

(def-fns _ $ many build-rope : (many (Decls) d) (many (Nat) depth) (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r)
  (match many c _
    ((MkCtor name id index arity tagged ext shape)
      (match many ext _
        ((Some a e)
          (match many (find-template (decl-templates d) (BTrue) (ext-type-name e) index) _
            ((Some b ps) (templated-build ps depth args))
            ((None b) (rcat3 (RStr $ str-cat3 "(con_" (ext-type-name e) " (Obj.repr (") (pattern-rope d shape index args) $ RStr ")))"))))
        ((None a)
          (match many tagged _
            ((BTrue) (rcat3 (RStr "(Obj.repr (") (pattern-rope d shape index args) $ RStr "))"))
            ((BFalse) (tuple-rope args))))))))

; A first-class constructor is its curried builder; a constant one is the constant.
(def-fns _ $ many ctor-fn-rope : (many (Decls) d) (many (Ctor) c) -> (many (Rope) r)
  (let (many fs) $ field-names (ctor-arity c) 0)
  (match many fs _
    ((Nil a) (build-rope d 0 c fs))
    ((Cons a f rest) (rcat5 (RStr "(Obj.repr (fun ") (params-rope fs) (RStr " : Obj.t -> ") (build-rope d 0 c fs) $ RStr "))"))))

(def-fns _ $ many tagged-arms : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Arm) arms) -> (many (Rope) r)
  (match many arms _
    ((Nil a) (REmpty))
    ((Cons a arm rest) (match many arm _ ((MkArm i fs body) (rcat5 (RStr "| ") (pattern-rope d s i fs) (RStr " -> ") body $ rcat (RStr " ") $ tagged-arms d s rest))))))

(def-fns _ $ many default-rope : (many (Maybe $ Rope) dflt) -> (many (Rope) r)
  (match many dflt _ ((Some a d) d) ((None a) (RStr "(absurd ())"))))

; A match over an ADT's constructors (lib/extract.ml's dispatch): an extern value unwrapped one level first;
; a direct match for a tagged type, on the copy narrowed to the live constructors when some are refuted, so
; that OCaml tests nothing for them; the fields as they stand for an untagged one.
(def-fns _ $ many dispatch-rope : (many (Decls) d) (many (Nat) depth) (many (Adt) adt) (many (List $ Nat) live) (many (Rope) scrut0) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r)
  (match many (match many (adt-ext adt) (((Maybe $ List $ Piece) t)) ((None a) (None _)) ((Some a e) (find-template (decl-templates d) (BFalse) (ext-type-name e) 0))) _
    ((Some t ps) (templated-dispatch ps depth (list-length _ $ adt-ctors adt) live scrut0 arms dflt))
    ((None t)
  (let (many (Rope) scrut) $ match many (adt-ext adt) _ ((None a) scrut0) ((Some a e) (rcat3 (RStr $ str-cat3 "(des_" (ext-type-name e) " ") scrut0 $ RStr ")")))
  (match many (adt-tagged adt) _
    ((BTrue)
      (let (many s) $ adt-shape adt)
      (let (many (String) ty) $ match many (narrowed adt live) _ ((BTrue) (str-cat "yes " $ narrow-name d s $ live-key live)) ((BFalse) (shape-name d s)))
      (let (many (Rope) inner)
        (match many arms _
          ((Nil b) (match many dflt _ ((None c) (RStr "| _ -> .")) ((Some c dr) (rcat (RStr "| _ -> ") dr))))
          ((Cons b arm rest) (rcat (tagged-arms d s arms) $ match many dflt (((Rope) r)) ((None c) (REmpty)) ((Some c dr) (rcat (RStr "| _ -> ") dr))))))
      (rcat5 (RStr "(match (Obj.obj ") scrut (RStr $ str-cat3 " : " ty ") with ") inner $ RStr ")"))
    ((BFalse)
      (match many arms _
        ((Nil b) (default-rope dflt))
        ((Cons b arm rest) (match many arm _ ((MkArm i fs body) (untuple-rope fs scrut body))))))))))

; What an arm over a whole ADT does with a constructor's fields: wraps them in Some for one constructor and
; None for the rest, takes the first, or makes the driver's request of them.
(def-adts $ ArmKind : -> Type
  enum
  (many AkOption : (many (String) cname) -> (ArmKind))
  (many AkField : -> (ArmKind))
  (many AkRequest : -> (ArmKind)))

(def-fns _ $ many arm-body : (many (Decls) d) (many (ArmKind) k) (many (Ctor) c) (many (List $ Rope) fs) -> (many (Rope) r)
  (match many k _
    ((AkOption cname)
      (match many (str-cmp (ctor-name c) cname) _
        ((CEq eq-t eq-r eq-x) (rcat3 (RStr "(Some (") (commas fs) $ RStr "))"))
        (else (RStr "None"))))
    ((AkField) (match many fs _ ((Nil a) (RStr "(absurd ())")) ((Cons a f rest) f)))
    ((AkRequest) (rcat3 (RStr $ str-cat3 "(Driver_core." (ctor-name c) " (") (commas fs) $ RStr "))"))))

(def-fns _ $ many ctor-arms : (many (Decls) d) (subterm many (List $ Ctor) cs) (many (ArmKind) k) -> (many (List $ Arm) r)
  (match many cs _
    ((Nil a) (Nil _))
    ((Cons a c rest)
      (let (many fs) $ field-names (ctor-arity c) 0)
      (Cons _ (MkArm (ctor-index c) fs $ arm-body d k c fs) $ ctor-arms d rest k))))

(def-fns _ $ many all-live : (many (Adt) adt) -> (many (List $ Nat) r)
  (nat-range (list-length _ $ adt-ctors adt) 0))

; A Matchable at runtime: the identity for a plain type, for an extern type the FFI's unwrap into the shape
; its constructors describe, which a held match then matches on directly.
(def-fns _ $ many matchable-rope : (many (Adt) adt) -> (many (Rope) r)
  (match many (adt-ext adt) _
    ((None a) (RStr "m_plain"))
    ((Some a e) (RStr $ str-cat3 "(Obj.repr des_" (ext-type-name e) ")"))))

(def-fns _ $ many payload-rope : (many (Payload) p) -> (many (Rope) r)
  (match many p _
    ((PNat n) (nat-literal n))
    ((PHalf n) (nat-literal n))
    ((PStr s)
      (let (many n) (erased p) (str-length s))
      (rcat5 (RStr "(Obj.repr ((") (quoted s) (RStr ", 0, ") (nat-rope n) $ RStr ") : Ffi_core.slice))"))))

; ---- Names for the frames code binds: one per id, in step with the frames (ASSUMPTIONS 127); a function
; bound by a group is named, so a call of it is direct, a value use its closure.

(def-adts $ Named : -> Type
  enum
  (many NmVal : (many (Rope) r) -> (Named))
  (many NmFn : (many (String) name) -> (Named)))

(def-fns _ $ many named-rope : (many (Named) n) -> (many (Rope) r)
  (match many n _
    ((NmVal r) r)
    ((NmFn name) (RStr $ str-cat3 "(Obj.repr " name ")"))))

(def-adts $ Names : ((List $ List $ Nat) ctx) -> Type
  enum
  (many NmNil : -> (Names (Nil (List (Nat)))))
  (many NmFrame : (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) f rs) lk) (many (Names ctx) rest) -> (Names (Cons (List (Nat)) f ctx))))

(def-fns _ $ many names-depth : (erased (List $ List $ Nat) ctx) (subterm many (Names ctx) ns) -> (many (Nat) n)
  (match many ns _
    ((NmNil) 0)
    ((NmFrame c f rs lk rest) (Succ $ names-depth _ rest))))

(def-fns _ $ many names-get : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (many (Names ctx) ns) -> (many (Named) r)
  (match many p _
    ((MHere y f c q) (match many ns _ ((NmFrame c2 f2 rs lk rest) (let (many r) (erased sq) $ at-get _ _ _ q rs lk) r)))
    ((MThere y f c q) (match many ns _ ((NmFrame c2 f2 rs lk rest) (names-get _ _ q rest))))))

(def-fns _ $ many addr-str : (erased (Hist Block) a) (many (Ref Block a) at) -> (many (String) r)
  (str-cat "a" $ nat-str $ ref-pos Block _ at))

(def-fns _ $ many addr-rope : (erased (Hist Block) a) (many (Ref Block a) at) -> (many (Rope) r)
  (RStr $ addr-str _ at))

; The OCaml name of a group's member: its entry's name qualified by the group's address, since a group
; allocated twice is emitted twice.
(def-fns _ $ many member-name : (erased (Hist Block) a) (many (Env) env) (many (Nat) id) (many (Ref Block a) g) -> (many (String) r)
  (str-cat3 (top-name env id) "_" $ addr-str _ g))

(def-fns _ $ many top-names : (subterm many (List $ Nat) ids) (many (Env) env) (many (Maybe $ String) suffix) -> (many (List $ Named) r) (erased (Lockstep (Nat) (Named) ids r) lk)
  (match many ids _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (let (many rs) (erased lk) $ top-names rest env suffix)
      (let (many (Named) r) $ match many suffix _ ((None b) (NmVal $ RStr $ top-name env x)) ((Some b s) (NmFn $ str-cat (top-name env x) s)))
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ many push-names : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (Env) env) (many (Names ctx) ns) -> (many (Names (Cons (List (Nat)) ids ctx)) r)
  (let (many rs) (erased lk) $ top-names ids env $ None _)
  (NmFrame _ ids rs lk ns))

(def-fns _ $ many push-fn-names : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (Env) env) (many (String) suffix) (many (Names ctx) ns) -> (many (Names (Cons (List (Nat)) ids ctx)) r)
  (let (many rs) (erased lk) $ top-names ids env $ Some _ suffix)
  (NmFrame _ ids rs lk ns))

(def-fns _ $ many addr-ropes : (erased (Hist Block) a) (subterm many (List $ Ref Block a) vs) -> (many (List $ Rope) rs)
  (match many vs _
    ((Nil t) (Nil _))
    ((Cons t v rest) (Cons _ (addr-rope _ v) $ addr-ropes _ rest))))

(def-fns _ $ many const-rope : (many (Env) env) (many (Nat) x) -> (many (Rope) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store env)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) (RStr "(failwith \"unbound constant\")"))
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me) (match many s _ ((SDyn z2) (RStr "(failwith \"a Dyn constant\")")) ((SConst z2 v) (addr-rope _ v))))))))

; The names of a group block's captured frames: an address's block by name, a group's members by theirs.
(def-fns _ $ many frame-named : (erased (Hist Block) a) (erased (List $ Nat) f) (subterm many (List $ Ref Block a) vs) (erased (Lockstep (Nat) (Ref Block a) f vs) lk) -> (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) f rs) lk2)
  (match many vs _
    ((Nil t) (match erased lk _ ((LsNil ta tb) (values (Nil _) (LsNil _ _)))))
    ((Cons t v rest)
      (match erased lk _
        ((LsCons ta tb x y xs ys p)
          (let (many rs) (erased lk2) $ frame-named _ _ rest p)
          (let (many r) $ NmVal $ addr-rope _ v)
          (values (Cons _ r rs) (LsCons _ _ x r xs rs lk2)))))))

(def-fns _ $ many member-named : (erased (Hist Block) a) (subterm many (List $ Nat) gids) (many (Env) env) (many (Ref Block a) g) -> (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) gids rs) lk)
  (match many gids _
    ((Nil t) (values (Nil _) (LsNil _ _)))
    ((Cons t x rest)
      (let (many rs) (erased lk) $ member-named _ rest env g)
      (let (many r) $ NmFn $ member-name _ env x g)
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ many frame-names : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (subterm many (Frames (Ref Block a) ctx) fr) (many (Env) env) -> (many (Names ctx) r)
  (match many fr _
    ((FrNil z) (NmNil))
    ((FrVals z c f vs lk rest)
      (let (many rs) (erased lk2) $ frame-named _ _ vs lk)
      (NmFrame _ f rs lk2 $ frame-names _ _ rest env))
    ((FrGroup z c gids g rest)
      (let (many rs) (erased lk2) $ member-named _ gids env g)
      (NmFrame _ gids rs lk2 $ frame-names _ _ rest env))))

; ---- The head of a call: a constructor the elaborator saw, a function with an OCaml name, or a value.

(def-adts $ Head : -> Type
  enum
  (many HCtor : (many (Ctor) c) -> (Head))
  (many HFn : (many (String) name) -> (Head))
  (many HDyn : -> (Head)))

(def-fns _ $ many block-head : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Env) env) -> (many (Head) h)
  (match many b _
    ((BCtorFn z c) (HCtor c))
    ((BFn z g i id) (HFn $ member-name _ env id g))
    (else (HDyn))))

(def-fns _ $ many head-of : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) f) (many (Env) env) (many (Names ctx) ns) -> (many (Head) h)
  (match many f _
    ((CVar c0 x p) (match many (names-get _ _ p ns) _ ((NmFn name) (HFn name)) ((NmVal r) (HDyn))))
    ((CConst c0 x)
      (let (erased a) (many blk) $ env-block env x)
      (match many blk _ ((None t) (HDyn)) ((Some t b) (block-head _ b env))))
    ((CValue c0 v) (block-head _ v env))
    (else (HDyn))))

; The prelude's ADT of a type name.
; The prelude's names are found in its scope, as lib/program.ml's driver finds them, however the program
; shadows them.
(def-fns _ $ many prelude-adt : (many (Env) env) (many (String) name) -> (many (Maybe $ Adt) r)
  (let (many env2) (many ty) $ prelude-type (env-set-scope env $ env-prelude env) name)
  (type-adt env2 ty))

; flatten views a Rope through the identity, its nodes being the program's own values.
(def-fns _ $ many flatten-extra : (many (String) name) -> (many (Rope) r)
  (match many (str-cmp name "flatten") _
    ((CEq eq-t eq-r eq-x) (RStr "~rope:Obj.obj ~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr "))
    (else (REmpty))))

(def-fns _ $ many objs : (subterm many (List $ Rope) ps) -> (many (List $ Rope) r)
  (match many ps _
    ((Nil a) (Nil _))
    ((Cons a p rest) (Cons _ (rcat3 (RStr "(Obj.obj ") p $ RStr ")") $ objs rest))))

; ---- Code and blocks as OCaml; every piece recurses on the piece it writes.

(def-fns _
  (many emit-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (Rope) r)
    (match many code _
      ((CVar c0 x p) (named-rope $ names-get _ _ p ns))
      ((CConst c0 x) (const-rope env x))
      ((CValue c0 v) (block-rope _ v env d))
      ((CErased c0 ms2) (RStr "(Obj.repr ())"))
      ((CValues c0 ms2 cs pk) (tuple-rope $ emit-codes _ cs env ns d))
      ((CApp c0 ms2 f args cc)
        (let (many ars) $ emit-codes _ args env ns d)
        (match many (head-of _ f env ns) _
          ((HCtor c) (build-rope d (names-depth _ ns) c ars))
          ((HFn name) (rcat3 (RStr $ str-cat "(" name) (rcat (RStr " ") $ args-rope ars) $ RStr ")"))
          ((HDyn)
            (let (many fr) $ emit-code _ _ f env ns d)
            (match many ars _
              ((Nil a) (match many cc _ ((CCCtor) fr) (else (dyn-call fr ars))))
              ((Cons a r rest) (dyn-call fr ars))))))
      ((CLet c0 ms2 ns2 ids pk rhs rest)
        (let (many rr) $ emit-code _ _ rhs env ns d)
        (let (many body) $ emit-code _ _ rest env (push-names _ ids env ns) d)
        (match many ids _
          ((Nil a) (rcat5 (RStr "(let _ = ") rr (RStr " in ") body $ RStr ")"))
          ((Cons a x more) (untuple-rope (names-of-ids ids env) rr body))))
      ((CLetRec c0 ns2 gids g rest)
        (match many g _
          ((MkGroup c1 ids fns lk)
            (let (many ns2) $ push-fn-names _ ids env "" ns)
            (rcat5 (RStr "(let rec ") (emit-group _ _ fns env ns2 d "") (RStr " in ") (emit-code _ _ rest env ns2 d) $ RStr ")"))))
      ((CMatch c0 ns2 scrut shape branches dfl live)
        (let (many sr) $ emit-code _ _ scrut env ns d)
        (let (many (Maybe $ Rope) dr) (match many dfl _ ((None a) (None _)) ((Some a dd) (Some _ $ emit-code _ _ dd env (push-names _ (Nil _) env ns) d))))
        (let (many arms) $ emit-arms _ _ branches env ns d)
        (match many shape _
          ((ShKnown c1 adt) (dispatch-rope d (names-depth _ ns) adt live sr arms dr))
          ((ShHeld c1 mcode adt)
            (let (many mr) $ emit-code _ _ mcode env ns d)
            (let (many (Rope) sr2) $ match many (adt-tagged adt) _ ((BTrue) (rcat5 (RStr "((Obj.obj ") mr (RStr " : Obj.t -> Obj.t) ") sr $ RStr ")")) ((BFalse) sr))
            (dispatch-rope d (names-depth _ ns) adt live sr2 arms dr))
          ((ShNone c1) (default-rope dr))))
      ((CAbsurd c0 ms2) (RStr "(absurd ())"))
      ((CError c0 ms2 m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

  (many emit-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (List $ Rope) rs)
    (match many cs _
      ((Nil a) (Nil _))
      ((Cons a c rest) (Cons _ (emit-code _ _ c env ns d) $ emit-codes _ rest env ns d))))

  (many emit-arms : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (List $ Arm) r)
    (match many bs _
      ((Nil a) (Nil _))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c1 n0 disc ids body)
            (Cons _ (MkArm disc (names-of-ids ids env) $ emit-code _ _ body env (push-names _ ids env ns) d) $ emit-arms _ _ rest env ns d))))))

  ; The definitions of a group, joined by and, each named by its entry and the suffix.
  (many emit-group : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Env) env) (many (Names (Cons (List (Nat)) gids ctx)) ns) (many (Decls) d) (many (String) suffix) -> (many (Rope) r)
    (match many fns _
      ((Nil a) (REmpty))
      ((Cons a p rest)
        (match many p _
          ((MkPair x y id fn)
            (let (many (Rope) sep) $ match many rest _ ((Nil b) (REmpty)) ((Cons b q rest2) (RStr "\nand ")))
            (rcat5 (RStr $ str-cat (top-name env id) suffix) (RStr " ") (emit-fn _ _ fn env ns d) sep $ emit-group _ _ rest env ns d suffix))))))

  ; A function's parameters and body; an extern one is the host's, over its parameters unboxed.
  (many emit-fn : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (Func gids ctx) fn) (many (Env) env) (many (Names (Cons (List (Nat)) gids ctx)) ns) (many (Decls) d) -> (many (Rope) r)
    (match many fn _
      ((MkFunc g c rets name id params body impl top)
        (let (many ps) $ names-of-ids params env)
        (let (many (Rope) b)
          (match many impl _
            ((Some a im) (match many im (((Rope) r)) ((MkImpl se ecs) (match many se (((Rope) r)) ((MkSomeExtern n e) (rcat5 (RStr "(Obj.repr (Ffi_core.") (RStr $ sanitize $ ext-name _ e) (rcat (RStr " ") $ flatten-extra $ ext-name _ e) (rjoin (objs ps) " ") $ RStr "))"))))))
            ((None a) (emit-code _ _ body env (push-names _ params env ns) d))))
        (rcat3 (params-rope ps) (RStr " : Obj.t = ") b))))

  ; A block as one OCaml value, its addresses by name; a function value is its member's closure.
  (many block-rope : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Rope) r)
    (match many b _
      ((BTag z c fields) (build-rope d 0 c $ addr-ropes _ fields))
      ((BTup z fields) (tuple-rope $ addr-ropes _ fields))
      ((BExt z p) (payload-rope p))
      ((BCtorFn z c) (ctor-fn-rope d c))
      ((BMat z adt) (matchable-rope adt))
      ((BGroup z gids ctx g env2) (RStr "(failwith \"a group as a closed value\")"))
      ((BFn z g i id) (RStr $ str-cat3 "(Obj.repr " (member-name _ env id g) ")"))
      ((BToken z) (RStr "(Obj.repr ())"))
      ((BError z m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")")))))

; ---- The declarations: found by a walk over every block of the store and the code it holds, then written
; ahead of the blocks; the narrowed copies come before the shapes, so a bare constructor names the shape's.

(def-fns _ $ many collect-ctor : (many (Ctor) c) (many (Decls) d) -> (many (Decls) r)
  (match many c _
    ((MkCtor name id index arity tagged ext shape) (match many tagged _ ((BTrue) (decl-shape d shape)) ((BFalse) d)))))

; An extern type's shape is declared too, as the target of its Matchable's unwrap.
(def-fns _ $ many collect-adt : (many (Adt) adt) (many (Decls) d) -> (many (Decls) r)
  (match many (adt-tagged adt) _ ((BTrue) (decl-shape d $ adt-shape adt)) ((BFalse) d)))

(def-fns _ $ many collect-match : (many (Adt) adt) (many (List $ Nat) live) (many (Decls) d) -> (many (Decls) r)
  (match many (adt-tagged adt) _
    ((BFalse) d)
    ((BTrue)
      (match many (narrowed adt live) _
        ((BTrue) (decl-narrow d (adt-shape adt) $ live-key live))
        ((BFalse) (decl-shape d $ adt-shape adt))))))

(def-fns _ $ many nat-list-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest) (or (nat-eq x y) $ nat-list-mem rest x))))

(def-fns _
  (many collect-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
    (match many code _
      ((CValue c0 v) (collect-block _ v env d))
      ((CValues c0 ms2 cs pk) (collect-codes _ cs env d))
      ((CApp c0 ms2 f args cc) (collect-codes _ args env $ collect-code _ _ f env d))
      ((CLet c0 ms2 ns2 ids pk rhs rest) (collect-code _ _ rest env $ collect-code _ _ rhs env d))
      ((CLetRec c0 ns2 gids g rest) (match many g _ ((MkGroup c1 ids fns lk) (collect-code _ _ rest env $ collect-group _ _ fns env d))))
      ((CMatch c0 ns2 scrut shape branches dfl live)
        (let (many d1) $ collect-code _ _ scrut env d)
        (let (many (Decls) d2)
          (match many shape _
            ((ShKnown c1 adt) (collect-match adt live d1))
            ((ShHeld c1 mcode adt) (collect-match adt live $ collect-code _ _ mcode env d1))
            ((ShNone c1) d1)))
        (let (many d3) $ collect-branches _ _ branches env d2)
        (match many dfl _ ((None a) d3) ((Some a dd) (collect-code _ _ dd env d3))))
      (else d)))

  (many collect-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
    (match many cs _
      ((Nil a) d)
      ((Cons a c rest) (collect-codes _ rest env $ collect-code _ _ c env d))))

  (many collect-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
    (match many bs _
      ((Nil a) d)
      ((Cons a b rest) (match many b _ ((MkBranch c1 n0 disc ids body) (collect-branches _ _ rest env $ collect-code _ _ body env d))))))

  (many collect-group : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
    (match many fns _
      ((Nil a) d)
      ((Cons a p rest)
        (match many p _
          ((MkPair x y id fn)
            (match many fn _
              ((MkFunc g c rets name fid params body impl top)
                (let (many (Decls) d1)
                  (match many impl _
                    ((None b) (collect-code _ _ body env d))
                    ((Some b se) d)))
                (collect-group _ _ rest env d1))))))))

  (many collect-block : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
    (match many b _
      ((BTag z c fields) (collect-ctor c d))
      ((BCtorFn z c) (collect-ctor c d))
      ((BMat z adt) (collect-adt adt d))
      ((BGroup z gids ctx g env2) (match many g _ ((MkGroup c1 ids fns lk) (collect-group _ _ fns env d))))
      (else d))))



(def-fns _ $ many ctor-decls : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (Rope) r)
  (match many arities _
    ((Nil a) (REmpty))
    ((Cons a n rest)
      (let (many (Rope) sep) $ match many rest _ ((Nil b) (REmpty)) ((Cons b m rest2) (RStr " | ")))
      (let (many (Rope) fields) $ match many n _ ((Zero) (REmpty)) ((Succ k) (rcat (RStr " of ") $ obj-tuple $ field-names n 0)))
      (rcat4 (RStr $ ctor-name-at d s i) fields sep $ ctor-decls d s rest $ Succ i))))

(def-fns _ $ many shape-decls : (many (Decls) d) (subterm many (List $ List $ Nat) ss) (many (Bool) first) -> (many (Rope) r)
  (match many ss _
    ((Nil a) (REmpty))
    ((Cons a s rest)
      (rcat5 (RStr $ match many first (((String) x)) ((BTrue) "type ") ((BFalse) "and ")) (RStr $ shape-name d s) (RStr " = ") (ctor-decls d s s 0) $ rcat (RStr "\n") $ shape-decls d rest $ BFalse))))

(def-fns _ $ many narrow-ctors : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) (many (String) name) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (Rope) r)
  (match many arities _
    ((Nil a) (REmpty))
    ((Cons a n rest)
      (let (many (Rope) sep) $ match many rest _ ((Nil b) (REmpty)) ((Cons b m rest2) (RStr " | ")))
      (let (many (String) idx) $ match many (nat-list-mem live i) _ ((BTrue) "yes ") ((BFalse) "no "))
      (let (many (Rope) fields) $ match many n _ ((Zero) (REmpty)) ((Succ k) (rcat (obj-tuple $ field-names n 0) $ RStr " -> ")))
      (rcat5 (RStr $ str-cat (ctor-name-at d s i) " : ") fields (RStr $ str-cat idx name) sep $ narrow-ctors d s live name rest $ Succ i))))

(def-fns _ $ many narrow-decls : (many (Decls) d) (subterm many (List $ Narrow) ns) -> (many (Rope) r)
  (match many ns _
    ((Nil a) (REmpty))
    ((Cons a n rest)
      (match many n _
        ((MkNarrow s live)
          (let (many name) $ narrow-name d s live)
          (rcat4 (RStr $ str-cat3 "type _ " name " = ") (narrow-ctors d s live name s 0) (RStr "\n") $ narrow-decls d rest))))))

(def-fns _ $ many decls-rope : (many (Decls) d) -> (many (Rope) r)
  (match many d _
    ((MkDecls shapes narrows ts) (rcat (narrow-decls d narrows) $ shape-decls d shapes $ BTrue))))

; ---- The walk from the roots: what a Const or a final reaches, each value once. The worklist is
; tail recursive, which the seen set pays for: a stamp is below the store's next stamp, the trie
; holds at most that many keys (base.sl's bounded-le), so the keys it still lacks is a measure that
; strictly drops every time a fresh value is enqueued. That measure and the worklist are the two
; components of the decrease, in that order.

(def-fns _ $ many frames-refs : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx)
    (subterm many (Frames (Ref Block a) ctx) fr) (many (List $ Ref Block a) acc) -> (many (List $ Ref Block a) r)
  (match many fr _
    ((FrNil z) acc)
    ((FrVals z c f vs lk rest) (tail (frames-refs _ _ rest (rev-onto _ vs acc))))
    ((FrGroup z c gids g rest) (tail (frames-refs _ _ rest (Cons _ g acc))))))

(def-fns _ $ many block-refs : (erased (Hist Block) a) (many (Block (Ref Block a)) b) -> (many (List $ Ref Block a) r)
  (match many b _
    ((BTag z c fields) fields)
    ((BTup z fields) fields)
    ((BFn z g i id) (Cons _ g $ Nil _))
    ((BGroup z gids ctx g fr) (frames-refs _ _ fr (Nil _)))
    (else (Nil _))))

(def-fns _ $ many roots-of-entries : (erased (Hist Block) hs) (subterm many (IdMap $ EInfo hs) en)
    (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r)
  (match many en _
    ((MEmpty t) acc)
    ((MNode t here one two)
      (let (many acc1)
        (match many here (((List $ Ref Block hs) r))
          ((None u) acc)
          ((Some u info)
            (match many info (((List $ Ref Block hs) r))
              ((MkEInfo z n mu st mi me)
                (match many st (((List $ Ref Block hs) r))
                  ((SDyn z2) acc)
                  ((SConst z2 v) (Cons _ v acc))))))))
      (roots-of-entries _ two (roots-of-entries _ one acc1)))))

(def-fns _ $ many roots-of-finals : (erased (Hist Block) hs) (subterm many (List $ Pair (Ref Block hs) $ Term) fs)
    (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r)
  (match many fs _
    ((Nil t) acc)
    ((Cons t p rest) (match many p _ ((MkPair x y v ty) (tail (roots-of-finals _ rest (Cons _ v acc))))))))

; [rest] the stamps the seen set still lacks, [work] the worklist; the call in each branch decreases
; the first of those two that it can.
(def-fns _ $ many trace-loop : (erased (Hist Block) hs) (erased (Nat) bound) (erased (Len Block hs bound) lb)
    (erased (Nat) size) (subterm erased (Nat) rest) (erased (Add size rest bound) sum)
    (many (IdMap $ Unit) seen) (erased (Bounded (Unit) seen size bound) bd)
    (subterm many (List $ Ref Block hs) work) (many (List $ Ref Block hs) acc)
    (many (Env) env) (many (Decls) d) -> (many (List $ Ref Block hs) acc2) (many (Decls) d2)
  (match many work _
    ((Nil t) (values acc d))
    ((Cons t at wrest)
      (let (many k) (erased lk) (ref-key Block _ bound lb at))
      (match many (idmap-get _ k seen) _
        ((Hit t2 k2 m2 u p) (tail (trace-loop _ bound lb size rest sum seen bd wrest acc env d)))
        ((Miss t2 k2 m2 ab)
          (let (many seen2) (erased rest2) (erased bd2) (erased sum2) (erased less)
            (seen-add (Unit) k (MkUnit) seen size rest bound bd sum ab lk))
          (let-match many at (MkRef _ _ rs rv rp))
          (let-match many rv (MkValue _ _ pos lp blk))
          (let (erased tsf) (ref-suffix _ _ rs rv rp))
          (let (many kids) (block-refs _ blk))
          (let (erased kids2) (erased pk) (refs-widen Block rs hs tsf kids))
          (tail (trace-loop _ bound lb (Succ size) (subterm (lt-subterm rest2 rest less)) rest2 sum2 seen2 bd2
                  (rev-onto _ (coerce kids pk) wrest) (Cons _ at acc) env (collect-block _ blk env d))))))))

; A group's block is its members' top-level let rec over the names of the frames it closed over.
(def-fns _ $ many block-let : (erased (Hist Block) hs) (many (Ref Block hs) at) (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Rope) r)
  (match many b _
    ((BGroup z gids ctx g env2)
      (match many g _
        ((MkGroup c1 ids fns lk)
          (let (many suffix) $ str-cat "_" $ addr-str _ at)
          (rcat3 (RStr "let rec ") (emit-group _ _ fns env (push-fn-names _ ids env suffix $ frame-names _ _ env2 env) d suffix) $ RStr "\n"))))
    (else (rcat5 (RStr "let ") (addr-rope _ at) (RStr " : Obj.t = ") (block-rope _ b env d) $ RStr "\n"))))

; The traced set is written in stamp order, which orders every dependency: a block's own references
; and the Consts its code names were all allocated before it. The comparison's level is minted here
; so the factory can be built here, the comparison itself closing over the history in emit-program.
(def-lvl REF-CMP)

(let (erased REF-SORT-L) (many ref-sort) (sort-factory REF-CMP))

(def-fns _ $ many emit-blocks : (erased (Hist Block) hs) (subterm many (List $ Ref Block hs) order)
    (many (Env) env) (many (Decls) d) (many (Rope) acc) -> (many (Rope) r)
  (match many order _
    ((Nil t) acc)
    ((Cons t at rest)
      (let-match many at (MkRef _ _ rs rv rp))
      (let-match many rv (MkValue _ _ pos lp blk))
      (tail (emit-blocks _ rest env d $ rcat acc $ block-let _ at _ blk env d)))))

; ---- The driver (lib/driver_core.ml): its operations on the prelude's values, each a direct build or match

(def-fns _ $ many prelude-ctor : (many (Env) env) (many (String) name) -> (many (Maybe $ Ctor) r)
  (let (many env2) (many x) $ prelude-id (env-set-scope env $ env-prelude env) name)
  (ctor-of env2 x))

(def-fns _ $ many driver-make : (many (Decls) d) (many (Env) env) (many (String) name) -> (many (Rope) r)
  (match many (prelude-ctor env name) _
    ((None a) (RStr "(absurd ())"))
    ((Some a c)
      (let (many fs) $ field-names (ctor-arity c) 0)
      (match many fs _
        ((Nil b) (build-rope d 0 c fs))
        ((Cons b f rest) (lambda-rope fs $ build-rope d 0 c fs))))))

(def-fns _ $ many driver-un : (many (Decls) d) (many (Env) env) (many (String) tname) (many (ArmKind) k) -> (many (Rope) r)
  (match many (prelude-adt env tname) _
    ((None a) (RStr "(absurd ())"))
    ((Some a adt) (lambda-rope (Cons _ (RStr "v") $ Nil _) $ dispatch-rope d 0 adt (all-live adt) (RStr "v") (ctor-arms d (adt-ctors adt) k) $ None _))))

(def-fns _ $ many driver-op : (many (String) field) (many (Rope) r) -> (many (Rope) r2)
  (rcat3 (RStr $ str-cat3 "Driver_core." field " = ") r $ RStr "; "))

(def-fns _ $ many driver-rope : (many (Decls) d) (many (Env) env) -> (many (Rope) r)
  (rcat5 (RStr "let driver = Driver_core.make ~of_host:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~to_host:(fun v -> let s, o, l = (Obj.obj v : Ffi_core.slice) in String.sub s o l) { ")
    (rcat5 (driver-op "zero" $ driver-make d env "Zero") (driver-op "succ" $ driver-make d env "Succ") (driver-op "pred" $ driver-un d env "Nat" $ AkOption "Succ")
      (driver-op "u8" $ driver-make d env "MkU8") $ driver-op "un_u8" $ driver-un d env "U8" $ AkField)
    (rcat5 (driver-op "char" $ driver-make d env "MkChar") (driver-op "un_char" $ driver-un d env "Char" $ AkField) (driver-op "snil" $ driver-make d env "SNil")
      (driver-op "scons" $ driver-make d env "SCons") $ driver-op "un_str" $ driver-un d env "String" $ AkOption "SCons")
    (rcat5 (driver-op "some" $ driver-make d env "Some") (driver-op "none" $ driver-make d env "None") (driver-op "ok" $ driver-make d env "Ok")
      (driver-op "fail" $ driver-make d env "Fail") $ driver-op "unit" $ driver-make d env "MkUnit")
    (rcat5 (driver-op "cons" $ driver-make d env "Cons") (driver-op "nil" $ driver-make d env "Nil")
      (rcat5 (driver-op "pair" $ driver-make d env "MkPair") (driver-op "is_file" $ driver-make d env "IsFile")
        (driver-op "is_dir" $ driver-make d env "IsDir") (driver-op "is_other" $ driver-make d env "IsOther")
        $ driver-op "missing" $ driver-make d env "Missing")
      (rcat3 (driver-op "changed" $ driver-make d env "Changed") (driver-op "unchanged" $ driver-make d env "Unchanged")
        $ driver-op "request" $ driver-un d env "IO" $ AkRequest)
      (rcat3 (RStr "Driver_core.apply = (fun (k : Obj.t) (x : Obj.t) -> (Obj.obj k : Obj.t -> Obj.t) x); ")
        (RStr "Driver_core.apply0 = (fun (k : Obj.t) -> (Obj.obj k : unit -> Obj.t) ())")
        $ RStr " }\n"))))

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

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ ShowMemo : -> Type
  enum
  (many MkShowMemo : (many (Nat) fresh) (many (Nat) count) (many (List $ Pair (Term) $ String) known) (many (List $ Rope) defs) -> (ShowMemo)))

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

(def-fns _
  (many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) (many (Decls) d) -> (many (ShowMemo) memo2) (many (String) name)
    (match many fuel _
      ((Zero) (values memo "show_any"))
      ((Succ k)
        (let (many ty) $ canon-env env ty0)
        (match many memo _
          ((MkShowMemo fresh count known defs)
            (let (many key) $ mapv ty (OpWild fresh) 0)
            (match many (memo-find known env key) _
              ((Some a name) (values memo name))
              ((None a)
                (let (many name) $ str-cat "show_" $ nat-str count)
                (let (many memo1) $ MkShowMemo fresh (Succ count) (Cons _ (MkPair _ _ key name) known) defs)
                (let (many (ShowMemo) memo2) (many (Rope) body)
                  (match many ty _
                    ((TApp h args)
                      (match many (type-adt env ty) (((ShowMemo) m) ((Rope) r))
                        ((None b) (values memo1 $ RStr "\"?\""))
                        ((Some b adt)
                          (let (many memo3) (many arms) $ show-arms k env ty (adt-ctors adt) memo1 (adt-tagged adt) d)
                          (values memo3 $ dispatch-rope d 0 adt (all-live adt) (RStr "v") arms $ Some _ $ RStr "\"?\""))))
                    ((TFn l ps rs) (values memo1 $ RStr "\"<function ?>\""))
                    ((TValCtor ps r) (values memo1 $ RStr "\"<constructor ?>\"")) (else (values memo1 $ RStr "\"?\""))))
                (match many memo2 _
                  ((MkShowMemo fresh2 count2 known2 defs2)
                    (values (MkShowMemo fresh2 count2 known2 $ Cons _ (rcat4 (RStr name) (RStr " (v : Obj.t) : string = ") body $ REmpty) defs2) name))))))))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, the opened objects
  ; merged as entering a branch does, its fields shown only then, as the reference's exception skips them.
  (many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List $ Ctor) ctors) (many (ShowMemo) memo) (many (Bool) tagged) (many (Decls) d) -> (many (ShowMemo) memo2) (many (List $ Arm) arms)
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many ctors _
          ((Nil a) (values memo $ Nil _))
          ((Cons a c rest)
            (match many c _
              ((MkCtor cname cid index arity ctagged ext shape)
                (let (many ctele) (many ret) $ ctor-type env cid)
                (let (many envb) (many fids) (erased lock) $ open-tele ctele env (None _) (None _) (Nil _) $ BFalse)
                (let (many (Env) envb2) (many (Bool) live)
                  (match many (merge-all $ unify-force (Forcing envb) (instantiate (tvars-rev fids $ Nil _) ret) ty) _
                    ((UOk e2) (values e2 $ BTrue))
                    ((UContra msg) (values envb $ BFalse))))
                (let (many (ShowMemo) memo2) (many (List $ Rope) shown)
                  (match many live _
                    ((BTrue) (show-fields k envb2 (non-erased fids envb2) memo 0 d))
                    ((BFalse) (values memo $ Nil _))))
                (let (many (Rope) text)
                  (match many tagged _
                    ((BFalse) (match many shown (((Rope) r)) ((Nil b) (RStr "\"_\"")) ((Cons b s more) (match many more (((Rope) r)) ((Nil e) s) ((Cons e s2 more2) (rcat3 (RStr "\"(\" ^ ") (spaced shown) $ RStr " ^ \")\""))))))
                    ((BTrue) (rcat3 (RStr "\"(\" ^ ") (spaced $ Cons _ (quoted cname) shown) $ RStr " ^ \")\""))))
                (let (many memo3) (many more) $ show-arms k env ty rest memo2 tagged d)
                (values memo3 $ match many live (((List $ Arm) r)) ((BTrue) (Cons _ (MkArm index (field-names arity 0) text) more)) ((BFalse) more)))))))))

  (many show-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Nat) fids) (many (ShowMemo) memo) (many (Nat) i) (many (Decls) d) -> (many (ShowMemo) memo2) (many (List $ Rope) shown)
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many fids _
          ((Nil a) (values memo $ Nil _))
          ((Cons a x rest)
            (let (many memo2) (many name) $ show-type k env (type-of env x) memo d)
            (let (many memo3) (many more) $ show-fields k env rest memo2 (Succ i) d)
            (values memo3 $ Cons _ (rcat3 (RStr name) (RStr " f") $ nat-rope i) more)))))))

(def-fns _ $ many show-defs : (many (ShowMemo) memo) -> (many (Rope) r)
  (match many memo _
    ((MkShowMemo fresh count known defs)
      (match many defs _
        ((Nil a) (REmpty))
        ((Cons a d rest) (rcat3 (RStr "let rec ") (rjoin (list-rev _ defs) "\nand ") $ RStr "\n"))))))

; A final that is a function or a constructor prints its name, as the reference does.
(def-fns _ $ many named-final : (erased (Hist Block) hs) (many (Ref Block hs) v) (many (Env) env) -> (many (Maybe $ String) r)
  (let-match many v (MkRef _ _ ns nv np))
  (let-match many nv (MkValue _ _ npos nlp b))
  (match many b _
    ((BFn z g i id) (Some _ $ str-cat3 "<function " (name-of env id) ">"))
    ((BCtorFn z c) (Some _ $ str-cat3 "<constructor " (ctor-name c) ">"))
    (else (None $ String))))

(def-fns _ $ many final-rope : (many (Env) env) (erased (Hist Block) hs) (many (Ref Block hs) v) (many (Term) ty) (many (Decls) d) -> (many (Rope) r)
  (let (many vr) $ addr-rope _ v)
  (match many (classify-final env ty) _
    ((FMain) (rcat3 (RStr "let () = driver.run_main world ") vr $ RStr "\n"))
    ((FIo) (rcat3 (RStr "let () = exit (driver.run_io world ") vr $ RStr ")\n"))
    ((FThunk t)
      (let (many memo) (many name) $ show-type show-fuel env t (MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _) d)
      (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " ((Obj.obj ") vr $ RStr " : unit -> Obj.t) ()))") $ RStr "\n"))
    ((FPlain)
      (match many (named-final _ v env) _
        ((Some a text) (rcat3 (RStr "let () = print_endline ") (quoted text) $ RStr "\n"))
        ((None a)
          (let (many memo) (many name) $ show-type show-fuel env ty (MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _) d)
          (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " ") vr $ RStr ")") $ RStr "\n"))))))

(def-fns _ $ many emit-finals : (erased (Hist Block) hs) (subterm many (List $ Pair (Ref Block hs) $ Term) fs) (many (Env) env) (many (Decls) d) -> (many (Rope) r)
  (match many fs _
    ((Nil t) (REmpty))
    ((Cons t p rest) (match many p _ ((MkPair x y v ty) (rcat (final-rope env _ v ty d) $ emit-finals _ rest env d))))))

; The prelude's types the driver and any printer may name, declared whether or not the program reaches them.
(def-fns _ $ many collect-prelude : (subterm many (List $ String) names) (many (Env) env) (many (Decls) d) -> (many (Decls) r)
  (match many names _
    ((Nil a) d)
    ((Cons a n rest) (collect-prelude rest env $ match many (prelude-adt env n) (((Decls) r)) ((None b) d) ((Some b adt) (collect-adt adt d))))))

(def-fns _ $ many emit-program : (many (Bool) templates) (many (Env) env) -> (many (Rope) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store env)
  (let (many d0) $ collect-prelude (Cons _ "Nat" $ Cons _ "String" $ Cons _ "IO" $ Cons _ "Maybe" $ Cons _ "Result" $ Cons _ "List" $ Cons _ "Pair" $ Cons _ "EntryKind" $ Cons _ "Change" $ Nil _) env $ MkDecls (Nil _) (Nil _) $ match many templates (((List $ Template) ts)) ((BTrue) (parse-templates $ split-on (rope-str extern-templates) 10)) ((BFalse) (Nil _)))
  (let-match many hp (MkStore _ _ bound lb))
  (let (many roots) $ roots-of-finals _ fi (roots-of-entries _ en (Nil _)))
  (let (many acc2) (many d2)
    $ trace-loop _ bound lb (Zero) bound (AddZero bound) (MEmpty _) (BdEmpty _ bound) roots (Nil _) env d0)
  (def-fns REF-CMP $ many ref-le : (many (Ref Block hs) x) (many (Ref Block hs) y) -> (many (Bool) b)
    (nat-lt (ref-pos Block _ x) (ref-pos Block _ y)))
  (let (many order) $ ref-sort (Ref Block hs) ref-le acc2)
  (rcat5 runtime-header (decls-rope d2) (emit-blocks _ order env d2 (REmpty)) (driver-rope d2 env) $ emit-finals _ (list-rev _ fi) env d2))
