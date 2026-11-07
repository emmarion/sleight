(def-fns _ $ (many top-name : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (str-cat "v" $ str-cat (nat-str x) $ str-cat "_" $ sanitize $ name-of env x))

(let ((many show-fuel)) 100000)

(def-fns _ $ (many quoted : (many (String) s) -> (many (Rope) r))
  (RStr $ lit-string s))

(def-fns _ $ (many nat-rope : (many (Nat) n) -> (many (Rope) r))
  (RStr $ nat-str n))

(def-fns _ $ (many nat-literal : (many (Nat) n) -> (many (Rope) r))
  (match many (nat-lt n 4611686018427387904) _
    ((BTrue) (rcat3 (RStr "(Obj.repr ") (nat-rope n) $ RStr ")"))
    ((BFalse) (rcat3 (RStr "(Obj.repr (Z.of_string \"") (nat-rope n) $ RStr "\"))"))))

(def-fns _ $ (many bracketed : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (rcat3 (RStr "[") (rjoin rs "; ") $ RStr "]"))

(def-fns _ $ (many quoted-all : (subterm many (List $ String) ss) -> (many (List $ Rope) r))
  (match many ss _
    ((Nil _) (Nil _))
    ((Cons _ s rest) (Cons _ (quoted s) $ notail $ quoted-all rest))))

(def-fns _ $ (many commas : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (rjoin rs ", "))

(def-fns _ $ (many names-of-ids : (subterm many (List $ Nat) ids) (many (Env) env) -> (many (List $ Rope) r))
  (match many ids _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (Cons _ (RStr $ top-name env x) $ notail $ names-of-ids rest env))))

(def-fns _ $ (many field-names : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Rope) r))
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat "f" $ nat-str i) $ notail $ field-names k $ Succ i))))

(def-fns _ $ (many nat-range : (subterm many (Nat) n) (many (Nat) i) -> (many (List $ Nat) r))
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ i $ notail $ nat-range k $ Succ i))))

; A tuple of values as the runtime keeps it: none is unit, one is bare, more an OCaml tuple.
(def-fns _ $ (many tuple-rope : (many (List $ Rope) rs) -> (many (Rope) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (RStr "(Obj.repr ())")))
  (match many rest _
    ((Nil _) r)
    ((Cons _ _ _) (rcat3 (RStr "(Obj.repr (") (commas rs) $ RStr "))"))))

(def-fns _ $ (many obj-tuple : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (let-match many rs (Cons _ _ rest)
    ((Nil _) (REmpty)))
  (match many rest _ ((Nil _) (RStr "Obj.t")) ((Cons _ _ _) (rcat (RStr "Obj.t * ") $ notail $ obj-tuple rest))))

; Binding the names to a value of that shape.
(def-fns _ $ (many untuple-rope : (many (List $ Rope) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r))
  (let-match many names (Cons _ x rest) ((Nil _) body))
  (match many rest _
    ((Nil _) (rcat5 (RStr "(let ") x (RStr " = ") (rcat3 e (RStr " in ") body) $ RStr ")"))
    ((Cons _ _ _) (rcat5 (RStr "(let (") (commas names) (rcat5 (RStr ") = (Obj.obj ") e (RStr " : ") (obj-tuple names) $ RStr ") in ") body $ RStr ")"))))

(def-fns _ $ (many params-rope : (many (List $ Rope) ps) -> (many (Rope) r))
  (match many ps _
    ((Nil _) (RStr "()"))
    ((Cons _ _ _) (rcat3 (RStr "(") (rjoin ps " : Obj.t) (") $ RStr " : Obj.t)"))))

(def-fns _ $ (many arrows-tail : (subterm many (List $ Rope) args) -> (many (Rope) r))
  (match many args _
    ((Nil _) (RStr "Obj.t"))
    ((Cons _ _ rest) (rcat (RStr "Obj.t -> ") $ notail $ arrows-tail rest))))

(def-fns _ $ (many arrows-rope : (many (List $ Rope) args) -> (many (Rope) r))
  (match many args _
    ((Nil _) (RStr "unit -> Obj.t"))
    ((Cons _ _ _) (arrows-tail args))))

(def-fns _ $ (many args-rope : (many (List $ Rope) args) -> (many (Rope) r))
  (match many args _
    ((Nil _) (RStr "()"))
    ((Cons _ _ _) (rjoin args " "))))

; A call of a value whose OCaml name is unknown: the closure coerced to the call's arity.
(def-fns _ $ (many dyn-call : (many (Rope) f) (many (List $ Rope) args) -> (many (Rope) r))
  (rcat5 (RStr "((Obj.obj ") f (rcat3 (RStr " : ") (arrows-rope args) $ RStr ") ") (args-rope args) $ RStr ")"))

(def-fns _ $ (many lambda-rope : (many (List $ Rope) ps) (many (Rope) body) -> (many (Rope) r))
  (rcat5 (RStr "(fun ") (params-rope ps) (RStr " -> ") body $ RStr ")"))

; ---- The declarations a program needs (lib/extract.ml's shape table): the tagged shapes met, numbered by
; first sight, and the phantom-index copies narrowing a shape to a match's live constructors.

(def-adts $ (Narrow : -> Type)
  enum
  (many MkNarrow : (many (List $ Nat) shape) (many (List $ Nat) live) -> (Narrow)))

; ---- Extraction templates (lib/ffi_templates.txt, ASSUMPTIONS 133): an extern type's matches and builds as
; OCaml text with holes, embedded as lib/embed.sl's extern-templates; a type without one is taken apart and
; built through its view as before.

(def-adts $ (Hole : -> Type)
  enum
  (many HScrut : -> (Hole))
  (many HBody : (many (Nat) i) -> (Hole))
  (many HField : (many (Nat) i) (many (Nat) j) -> (Hole))
  (many HArg : (many (Nat) i) -> (Hole))
  (many HTemp : (many (Nat) k) -> (Hole)))

(def-adts $ (Piece : -> Type)
  enum
  (many PLit : (many (String) s) -> (Piece))
  (many PHole : (many (Hole) h) -> (Piece)))

(def-adts $ (Template : -> Type)
  enum
  (many MkTemplate : (many (String) kind) (many (String) type) (many (Nat) index) (many (List $ Piece) pieces) (many (List $ Nat) outcomes) -> (Template)))

(def-fns _ $ (many parse-hole : (many (String) h) -> (many (Maybe $ Hole) r))
  (let-match many h (SCons c rest) ((SNil) (None _)))
  (let-match many (char-eqb c #\s) (BFalse)
    ((BTrue) (match many (str-is-empty rest) _ ((BTrue) (Some _ $ HScrut)) ((BFalse) (None _)))))
  (match many (char-eqb c #\f) _
    ((BTrue)
      (let-match many (split-on rest #\.) (Cons _ i more) ((Nil _) (None _)))
      (let-match many more (Cons _ j none) ((Nil _) (None _)))
      (let-match many none (Nil _) ((Cons _ _ _) (None _)))
      (let-match many (str-nat i) (Some _ ni)
        ((None _) (None _)))
      (match many (str-nat j) _ ((Some _ nj) (Some _ $ HField ni nj)) ((None _) (None _))))
    ((BFalse)
      (let-match many (str-nat rest) (Some _ n) ((None _) (None _)))
      (let-match many (char-eqb c #\b) (BFalse) ((BTrue) (Some _ $ HBody n)))
      (let-match many (char-eqb c #\a) (BFalse)
        ((BTrue) (Some _ $ HArg n)))
      (match many (char-eqb c #\t) _ ((BTrue) (Some _ $ HTemp n)) ((BFalse) (None _))))))

; The pieces of a template's text, accumulated in reverse; a malformed hole stays as text for the OCaml
; compiler to refuse.
(def-fns _ $ (many parse-pieces : (subterm many (Nat) fuel) (many (String) s) (many (List $ Piece) acc) -> (many (List $ Piece) r))
  (let ((many lit) (many after)) (str-until s #\{))
  (let ((many (List $ Piece) acc1)) $ match many (str-is-empty lit) _ ((BTrue) acc) ((BFalse) (Cons _ (PLit lit) acc)))
  (let-match many after (Some _ rest) ((None _) (list-rev _ acc1)))
  (let ((many name) (many after2)) (str-until rest #\}))
  (let ((many (Piece) piece)) $ match many (parse-hole name) _ ((Some _ h) (PHole h)) ((None _) (PLit $ str-cat3 "{" name "}")))
  (let-match many after2 (Some _ rest2) ((None _) (list-rev _ $ Cons _ piece acc1)))
  (match many fuel _
    ((Zero) (list-rev _ $ Cons _ piece acc1))
    ((Succ f) (tail $ parse-pieces f rest2 $ Cons _ piece acc1))))

(def-fns _ $ (many parse-template : (many (String) line) -> (many (Maybe $ Template) r))
  (let ((many head) (many after)) (str-until line #\:))
  (let-match many after (Some _ text) ((None _) (None _)))
  (let ((many n) (erased _)) (str-length text))
  (let ((many pieces)) $ parse-pieces n text $ Nil _)
  (let-match many (split-on head #\space) (Cons _ kind more) ((Nil _) (None _)))
  (let-match many more (Cons _ type rest) ((Nil _) (None _)))
  (let-match many (or (str-eqb kind "match") $ str-eqb kind "fn") (BFalse) ((BTrue) (Some _ $ MkTemplate kind type 0 pieces $ Nil _)))
  (let-match many rest (Cons _ i _) ((Nil _) (None _)))
  (let-match many (str-nat i) (Some _ n2)
    ((None _) (None _)))
  (match many (str-eqb kind "build") _ ((BTrue) (Some _ $ MkTemplate kind type n2 pieces $ Nil _)) ((BFalse) (None _))))

(def-fns _ $ (many parse-templates : (subterm many (List $ String) lines) -> (many (List $ Template) r))
  (let-match many lines (Cons _ line rest) ((Nil _) (Nil _)))
  (match many (parse-template line) _
    ((Some _ t) (Cons _ t $ notail $ parse-templates rest))
    ((None _) (tail $ parse-templates rest))))

(def-fns _ $ (many find-entry : (subterm many (List $ Template) ts) (many (String) kind) (many (String) type) (many (Nat) index) -> (many (Maybe $ Template) r))
  (let-match many ts (Cons _ t rest) ((Nil _) (None _)))
  (let-match many t (MkTemplate b ty i _ _))
  (let ((many hit)) $ match many (nat-eqb i index) (((Bool) _)) ((BFalse) (BFalse)) ((BTrue) (and (str-eqb b kind) $ str-eqb ty type)))
  (match many hit _
    ((BTrue) (Some _ t))
    ((BFalse) (tail $ find-entry rest kind type index))))

(def-fns _ $ (many find-template : (many (List $ Template) ts) (many (String) kind) (many (String) type) (many (Nat) index) -> (many (Maybe $ List $ Piece) r))
  (let-match many (find-entry ts kind type index) (Some _ t) ((None _) (None _)))
  (let-match many t (MkTemplate _ _ _ ps _))
  (Some _ ps))

(def-fns _ $ (many str-is-name : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (or (char-eqb c #\_) $ or (char-eqb c #\') $ or (char-between c #\0 #\9) $ or (char-between c #\a #\z) $ char-between c #\A #\Z) $ tail $ str-is-name rest))))

(def-fns _ $ (many rope-is-name : (many (Rope) r) -> (many (Bool) b))
  (let ((many s)) $ rope-str r)
  (and (not $ str-is-empty s) $ str-is-name s))

(def-adts $ (Decls : -> Type)
  enum
  (many MkDecls : (many (List $ List $ Nat) shape-list) (many (List $ Narrow) narrows) (many (List $ Template) templates) (many (List $ Nat) consts) -> (Decls)))

(def-fns _ $ (many decl-templates : (many (Decls) d) -> (many (List $ Template) ts))
  (match many d _ ((MkDecls _ _ ts _) ts)))

(def-fns _ $ (many decl-call-template : (many (Decls) d) (many (Nat) id) (many (List $ Piece) ps) (many (List $ Nat) outcomes) -> (many (Decls) r))
  (match many d _ ((MkDecls shapes2 narrows ts cs) (MkDecls shapes2 narrows (Cons _ (MkTemplate "call" "" id ps outcomes) ts) cs))))

(def-fns _ $ (many decl-const : (many (Decls) d) (many (Nat) id) -> (many (Decls) r))
  (match many d _ ((MkDecls shapes2 narrows ts cs) (MkDecls shapes2 narrows ts $ Cons _ id cs))))

(def-fns _ $ (many decl-take-consts : (many (Decls) d) -> (many (Decls) r) (many (List $ Nat) cs))
  (match many d _ ((MkDecls shapes2 narrows ts cs) (values (MkDecls shapes2 narrows ts $ Nil _) cs))))

(def-fns _ $ (many decl-shape-index : (subterm many (List $ List $ Nat) ss) (many (List $ Nat) s) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many ss (Cons _ x rest)
    ((Nil _) (None _)))
  (match many (nat-list-eq x s) _ ((BTrue) (Some _ i)) ((BFalse) (tail $ decl-shape-index rest s $ Succ i))))

(def-fns _ $ (many narrow-index : (subterm many (List $ Narrow) ns) (many (List $ Nat) s) (many (List $ Nat) live) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many ns (Cons _ n rest) ((Nil _) (None _)))
  (let-match many n (MkNarrow s2 live2))
  (let ((many hit)) $ match many (nat-list-eq s2 s) (((Bool) _)) ((BTrue) (nat-list-eq live2 live)) ((BFalse) (BFalse)))
  (match many hit _ ((BTrue) (Some _ i)) ((BFalse) (tail $ narrow-index rest s live $ Succ i))))

(def-fns _ $ (many index-str : (many (Maybe $ Nat) i) -> (many (String) s))
  (match many i _ ((Some _ n) (nat-str n)) ((None _) "missing")))

(def-fns _ $ (many shape-name : (many (Decls) d) (many (List $ Nat) s) -> (many (String) r))
  (match many d _ ((MkDecls shapes2 _ _ _) (str-cat "t" $ index-str $ decl-shape-index shapes2 s 0))))

(def-fns _ $ (many ctor-name-at : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) -> (many (String) r))
  (match many d _ ((MkDecls shapes2 _ _ _) (str-cat3 "K" (index-str $ decl-shape-index shapes2 s 0) $ str-cat "_" $ nat-str i))))

(def-fns _ $ (many wide-name : (many (Decls) d) (many (List $ Nat) s) -> (many (String) r))
  (match many d _ ((MkDecls shapes2 _ _ _) (str-cat3 "K" (index-str $ decl-shape-index shapes2 s 0) "_w"))))

(def-fns _ $ (many narrow-name : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (String) r))
  (match many d _ ((MkDecls _ narrows _ _) (str-cat3 (shape-name d s) "_n" $ index-str $ narrow-index narrows s live 0))))

(def-fns _ $ (many add-shape : (many (List $ List $ Nat) ss) (many (List $ Nat) s) -> (many (List $ List $ Nat) r))
  (let-match many (decl-shape-index ss s 0) (None _)
    ((Some _ _) ss))
  (let ((many r) (erased _)) $ list-append _ ss $ Cons _ s $ Nil _)
  r)

(def-fns _ $ (many decl-shape : (many (Decls) d) (many (List $ Nat) s) -> (many (Decls) r))
  (match many d _ ((MkDecls shapes2 narrows ts cs) (MkDecls (add-shape shapes2 s) narrows ts cs))))

(def-fns _ $ (many decl-narrow : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (Decls) r))
  (let-match many d (MkDecls shapes2 narrows ts cs))
  (let-match many (narrow-index narrows s live 0) (None _) ((Some _ _) d))
  (let ((many r) (erased _)) $ list-append _ narrows $ Cons _ (MkNarrow s live) $ Nil _)
  (MkDecls (add-shape shapes2 s) r ts cs))

(def-fns _ $ (many nat-insert : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (Cons _ x $ Nil _)))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ _) (Cons _ x xs))
    ((CEq _ _ _) xs)
    ((CGt _ _ _ _ _) (Cons _ y $ notail $ nat-insert x rest))))

; The key of a narrowing: the live discriminants sorted, each once.
(def-fns _ $ (many live-key : (subterm many (List $ Nat) live) -> (many (List $ Nat) r))
  (match many live _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (nat-insert x $ notail $ live-key rest))))

(def-fns _ $ (many adt-shape : (many (Adt) adt) -> (many (List $ Nat) r))
  (ctor-arities $ adt-ctors adt))

(def-fns _ $ (many filled-count : (subterm many (List $ Nat) s) -> (many (Nat) n))
  (let-match many s (Cons _ a rest) ((Nil _) 0))
  (let ((many k)) $ notail $ filled-count rest)
  (match many a _ ((Zero) k) ((Succ _) (Succ k))))

(def-fns _ $ (many shape-wide : (many (List $ Nat) s) -> (many (Bool) r))
  (nat-lt 244 $ filled-count s))

(def-fns _ $ (many widest : (subterm many (List $ Nat) s) -> (many (Nat) n))
  (let-match many s (Cons _ a rest) ((Nil _) 0))
  (let ((many m)) $ notail $ widest rest)
  (match many (nat-lt a m) _ ((BTrue) m) ((BFalse) a)))

; Whether the live set leaves a constructor out, so the match is on a narrowed copy of the shape.
(def-fns _ $ (many narrowed : (many (Adt) adt) (many (List $ Nat) live) -> (many (Bool) r))
  (and (nat-lt (list-length _ $ live-key live) $ list-length _ $ adt-ctors adt) $ not $ shape-wide $ adt-shape adt))

; ---- Constructing, taking apart, and the runtime forms of constructors and Matchables


(def-fns _ $ (many record-fields : (subterm many (List $ Rope) fs) (many (Nat) i) -> (many (List $ Rope) r))
  (match many fs _
    ((Nil _) (Nil _))
    ((Cons _ f rest) (Cons _ (rcat3 (RStr $ str-cat3 "f" (nat-str i) " = ") f $ REmpty) $ notail $ record-fields rest $ Succ i))))

(def-fns _ $ (many record-types : (subterm many (Nat) count) (many (Nat) i) -> (many (List $ Rope) r))
  (match many count _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat3 "mutable f" (nat-str i) " : Obj.t") $ notail $ record-types k $ Succ i))))

(def-fns _ $ (many padded : (subterm many (Nat) n) (many (List $ Rope) fs) (many (String) fill) -> (many (List $ Rope) r))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (match many fs _
    ((Nil _) (Cons _ (RStr fill) $ notail $ padded k (Nil _) fill))
    ((Cons _ f rest) (Cons _ f $ notail $ padded k rest fill))))

(def-fns _ $ (many pattern-rope : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) (many (List $ Rope) fs) (many (String) fill) -> (many (Rope) r))
  (let-match many fs (Cons _ _ _) ((Nil _) (RStr $ ctor-name-at d s i)))
  (let ((many head) (many all)) $ match many (shape-wide s) (((String) _) ((List $ Rope) _))
    ((BTrue) (values (str-cat3 (wide-name d s) " { d = " $ str-cat (nat-str i) "; ") (padded (widest s) fs fill)))
    ((BFalse) (values (str-cat (ctor-name-at d s i) " { ") fs)))
  (rcat3 (RStr head) (rjoin (record-fields all 0) "; ") $ RStr " }"))

(def-adts $ (Arm : -> Type)
  enum
  (many MkArm : (many (Nat) d) (many (List $ Rope) fs) (many (Rope) body) -> (Arm)))

; A template filled: the scrutinee's name, the prefix of this instantiation's temporaries (the nesting
; depth, distinct along any path since a body sits in tail position and every other hole is a name), the
; arms and live set, the default's text, and the build arguments' names.
(def-adts $ (Filling : -> Type)
  enum
  (many MkFilling : (many (String) scrut) (many (String) prefix) (many (List $ Arm) arms) (many (List $ Nat) live) (many (Rope) dflt) (many (List $ Rope) args) -> (Filling)))

(def-fns _ $ (many arm-at : (subterm many (List $ Arm) arms) (many (Nat) i) -> (many (Maybe $ Arm) r))
  (let-match many arms (Cons _ arm rest)
    ((Nil _) (None _)))
  (let-match many arm (MkArm d _ _))
  (match many (nat-eqb d i) _ ((BTrue) (Some _ arm)) ((BFalse) (tail $ arm-at rest i))))

(def-fns _ $ (many nat-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (match many xs _
    ((Nil _) (BFalse))
    ((Cons _ y rest) (or (nat-eqb x y) $ tail $ nat-mem rest x))))

(def-fns _ $ (many fill-hole : (many (Filling) f) (many (Hole) h) -> (many (Rope) r))
  (let-match many f (MkFilling scrut prefix arms live dflt args))
  (match many h _
    ((HScrut) (RStr scrut))
    ((HTemp k) (RStr $ str-cat3 prefix "_t" $ nat-str k))
    ((HArg i) (list-nth-or _ args i $ RStr "(absurd ())"))
    ((HBody i)
      (match many (arm-at arms i) _
        ((Some _ arm) (match many arm _ ((MkArm _ _ body) body)))
        ((None _) (match many (nat-mem live i) _ ((BTrue) dflt) ((BFalse) (RStr "(absurd ())"))))))
    ((HField i j)
      (let-match many (arm-at arms i) (Some _ arm)
        ((None _) (RStr $ str-cat3 prefix "_f" $ str-cat3 (nat-str i) "_" $ nat-str j)))
      (match many arm _ ((MkArm _ fs _) (list-nth-or _ fs j $ RStr "_"))))))

(def-fns _ $ (many fill-pieces : (subterm many (List $ Piece) ps) (many (Filling) f) -> (many (Rope) r))
  (match many ps _
    ((Nil _) (REmpty))
    ((Cons _ p rest)
      (rcat (match many p (((Rope) _)) ((PLit s) (RStr s)) ((PHole h) (fill-hole f h))) $ notail $ fill-pieces rest f))))

; Each build argument as the name the template reads: its own when it is one, else a temporary bound to it.
(def-fns _ $ (many bind-args : (many (String) prefix) (subterm many (List $ Rope) args) (many (Nat) i) -> (many (List $ Rope) names) (many (List $ Rope) binds))
  (let-match many args (Cons _ arg rest) ((Nil _) (values (Nil _) (Nil _))))
  (let ((many names) (many binds)) (notail $ bind-args prefix rest (Succ i)))
  (let-match many (rope-is-name arg) (BFalse) ((BTrue) (values (Cons _ arg names) binds)))
  (let ((many x)) $ str-cat3 prefix "_a" $ nat-str i)
  (values (Cons _ (RStr x) names) $ Cons _ (rcat (RStr $ str-cat x " = ") arg) binds))

(def-fns _ $ (many let-binds-rope : (many (List $ Rope) binds) (many (Rope) body) -> (many (Rope) r))
  (match many binds _
    ((Nil _) body)
    ((Cons _ _ _) (rcat5 (RStr "(let ") (rjoin binds " in let ") (RStr " in ") body $ RStr ")"))))

; A tuple of values with each entry that is not a name bound first: ocamlopt (4.14.1 here; the issue
; reports 5.x too) fails with `Selection.size_expr` when a call it inlines puts an unused one-field block
; inside a tuple's field, https://github.com/ocaml/ocaml/issues/15154.
(def-fns _ $ (many values-rope : (many (Nat) depth) (many (List $ Rope) rs) -> (many (Rope) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (tuple-rope rs)))
  (let-match many rest (Cons _ _ _) ((Nil _) r))
  (let ((many names) (many binds)) $ bind-args (str-cat "tup" $ nat-str depth) rs 0)
  (let-binds-rope binds $ tuple-rope names))

(def-fns _ $ (many has-outcomes : (subterm many (List $ Piece) ps) -> (many (Bool) r))
  (let-match many ps (Cons _ p rest) ((Nil _) (BFalse)))
  (let-match many p (PHole h) ((PLit _) (tail $ has-outcomes rest)))
  (match many h _ ((HBody _) (BTrue)) (else (tail $ has-outcomes rest))))

(def-fns _ $ (many dummy-fields : (many (String) prefix) (many (Nat) i) (subterm many (Nat) n) (many (Nat) j) -> (many (List $ Rope) r))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (Cons _ (RStr $ str-cat3 prefix "_f" $ str-cat3 (nat-str i) "_" $ nat-str j) $ notail $ dummy-fields prefix i k (Succ j)))

(def-fns _ $ (many tagged-build : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) (many (List $ Rope) fs) -> (many (Rope) r))
  (rcat3 (RStr "(Obj.repr (") (pattern-rope d s i fs "(Obj.repr ())") $ RStr "))"))

(def-fns _ $ (many outcome-builds : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Nat) rest) (many (Nat) i) (many (String) prefix) -> (many (List $ Arm) r))
  (let-match many rest (Cons _ n more) ((Nil _) (Nil _)))
  (let ((many fs)) $ dummy-fields prefix i n 0)
  (Cons _ (MkArm i fs $ tagged-build d s i fs) $ notail $ outcome-builds d s more (Succ i) prefix))

(def-fns _ $ (many templated-fill : (many (List $ Piece) ps) (many (String) prefix) (many (List $ Rope) args) (many (List $ Arm) arms) (many (Rope) open) (many (Rope) close) -> (many (Rope) r))
  (let ((many names) (many binds)) (bind-args prefix args 0))
  (let ((many text)) $ fill-pieces ps $ MkFilling "" prefix arms (Nil _) (REmpty) names)
  (let-binds-rope binds $ rcat5 open (RStr "(") text (RStr ")") close))

(def-fns _ $ (many templated-build : (many (Decls) d) (many (List $ Piece) ps) (many (List $ Nat) outcomes) (many (Nat) depth) (many (List $ Rope) args) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "x" $ nat-str depth)
  (templated-fill ps prefix args (outcome-builds d outcomes outcomes 0 prefix) (REmpty) (REmpty)))

; How many of the constructors from i on the default stands for: those live with no arm of their own.
(def-fns _ $ (many count-defaulted : (subterm many (Nat) n) (many (Nat) i) (many (List $ Arm) arms) (many (List $ Nat) live) -> (many (Nat) r))
  (let-match many n (Succ k) ((Zero) 0))
  (let ((many rest)) $ notail $ count-defaulted k (Succ i) arms live)
  (match many (and (nat-mem live i) $ match many (arm-at arms i) (((Bool) _)) ((None _) (BTrue)) ((Some _ _) (BFalse))) _
    ((BTrue) (Succ rest))
    ((BFalse) rest)))

(def-fns _ $ (many fused-arms : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Nat) rest) (many (Nat) i) (many (String) prefix) (many (Rope) x) (many (List $ Arm) arms) (many (List $ Nat) live) (many (Maybe $ Rope) dflt) (many (Bool) shared) -> (many (List $ Arm) r))
  (let-match many rest (Cons _ n more) ((Nil _) (Nil _)))
  (let ((many later)) $ notail $ fused-arms d s more (Succ i) prefix x arms live dflt shared)
  (let-match many (arm-at arms i) (None _)
    ((Some _ arm) (match many arm _ ((MkArm _ fs body) (Cons _ (MkArm i fs $ untuple-rope (Cons _ x $ Nil _) (tagged-build d s i fs) body) later)))))
  (let-match many dflt (Some _ dd) ((None _) later))
  (let-match many (nat-mem live i) (BTrue) ((BFalse) later))
  (let ((many fs)) $ dummy-fields prefix i n 0)
  (let ((many v)) $ tagged-build d s i fs)
  (Cons _ (MkArm i fs $ match many shared (((Rope) _)) ((BTrue) (rcat3 (RStr $ str-cat3 "(" prefix "_d ") v $ RStr ")")) ((BFalse) (untuple-rope (Cons _ x $ Nil _) v dd))) later))

(def-fns _ $ (many templated-fused : (many (Decls) d) (many (List $ Piece) ps) (many (Nat) depth) (many (List $ Rope) args) (many (List $ Nat) s) (many (List $ Nat) live) (many (Rope) x) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "x" $ nat-str depth)
  (let ((many shared)) $ nat-lt 1 $ count-defaulted (list-length _ s) 0 arms live)
  (let ((many (Rope) open) (many (Rope) close))
    (match many dflt _
      ((Some _ dd) (match many shared _ ((BTrue) (values (rcat5 (RStr $ str-cat3 "(let " prefix "_d ") x (RStr " = ") dd $ RStr " in ") (RStr ")"))) ((BFalse) (values (REmpty) (REmpty)))))
      ((None _) (values (REmpty) (REmpty)))))
  (templated-fill ps prefix args (fused-arms d s s 0 prefix x arms live dflt shared) open close))

; A match through its template: the scrutinee bound to a name unless it is one, a default filling more
; than one arm bound once as a thunk so its text is written once, and each arm's body in place.
(def-fns _ $ (many templated-dispatch : (many (List $ Piece) ps) (many (Nat) depth) (many (Nat) ctors) (many (List $ Nat) live) (many (Rope) scrut0) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "x" $ nat-str depth)
  (let ((many (Rope) dr) (many (Rope) open) (many (Rope) close))
    (match many dflt _
      ((None _) (values (RStr "(absurd ())") (REmpty) (REmpty)))
      ((Some _ d)
        (match many (nat-lt 1 $ count-defaulted ctors 0 arms live) _
          ((BTrue) (values (RStr $ str-cat3 "(" prefix "_d ())") (rcat3 (RStr $ str-cat3 "(let " prefix "_d () = ") d $ RStr " in ") (RStr ")")))
          ((BFalse) (values d (REmpty) (REmpty)))))))
  (let ((many (String) name) (many (Rope) let-open) (many (Rope) let-close))
    (match many (rope-is-name scrut0) _
      ((BTrue) (values (rope-str scrut0) (REmpty) (REmpty)))
      ((BFalse) (values prefix (rcat3 (RStr $ str-cat3 "(let " prefix " = ") scrut0 $ RStr " in ") (RStr ")")))))
  (let ((many text)) $ fill-pieces ps $ MkFilling name prefix arms live dr (Nil _))
  (rcat5 let-open open (rcat3 (RStr "(") text $ RStr ")") close let-close))

(def-fns _ $ (many block-build : (many (Decls) d) (many (List $ Rope) fields) -> (many (Rope) r))
  (rcat3 (RStr "(Obj.repr (") (pattern-rope d (Cons _ (list-length _ fields) $ Nil _) 0 fields "_") $ RStr "))"))

(def-fns _ $ (many plain-build : (many (Decls) d) (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r))
  (let-match many (ctor-newtype c) (BFalse) ((BTrue) (tuple-rope args)))
  (match many (ctor-tagged c) _
    ((BTrue) (tagged-build d (ctor-shape c) (ctor-index c) args))
    ((BFalse) (block-build d args))))

(def-fns _ $ (many build-rope : (many (Decls) d) (many (Nat) depth) (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r))
  (let-match many c (MkCtor _ _ index _ _ ext shape _))
  (let-match many ext (Some _ e)
    ((None _)
      (plain-build d c args)))
  (match many (find-template (decl-templates d) "build" (ext-type-name e) index) _
    ((Some _ ps) (templated-build d ps (Nil _) depth args))
    ((None _) (rcat3 (RStr $ str-cat3 "(con_" (ext-type-name e) " (Obj.repr (") (pattern-rope d shape index args "_") $ RStr ")))"))))

(def-fns _ $ (many ctor-fn-rope : (many (Decls) d) (many (Ctor) c) -> (many (Rope) r))
  (let ((many fs)) $ field-names (ctor-arity c) 0)
  (rcat5 (RStr "(Obj.repr (fun ") (params-rope fs) (RStr " -> ") (build-rope d 0 c fs) $ RStr "))"))

(def-fns _ $ (many tagged-arms : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Arm) arms) -> (many (Rope) r))
  (let-match many arms (Cons _ arm rest)
    ((Nil _) (REmpty)))
  (match many arm _ ((MkArm i fs body) (rcat5 (RStr "| ") (pattern-rope d s i fs "_") (RStr " -> ") body $ rcat (RStr " ") $ notail $ tagged-arms d s rest))))

(def-fns _ $ (many default-rope : (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (match many dflt _ ((Some _ d) d) ((None _) (RStr "(absurd ())"))))

; A match over an ADT's constructors (lib/extract.ml's dispatch): an extern value unwrapped one level first;
; a direct match for a tagged type, on the copy narrowed to the live constructors when some are refuted, so
; that OCaml tests nothing for them; the fields as they stand for an untagged one.
(def-fns _ $ (many block-dispatch : (many (Decls) d) (many (Rope) scrut) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (let-match many arms (Cons _ arm _) ((Nil _) (default-rope dflt)))
  (let-match many arm (MkArm _ fs body))
  (let ((many shape)) $ Cons _ (list-length _ fs) $ Nil _)
  (rcat5 (RStr "(match (Obj.obj ") scrut (RStr $ str-cat3 " : " (shape-name d shape) ") with ")
    (rcat3 (pattern-rope d shape 0 fs "_") (RStr " -> ") body) $ RStr ")"))

(def-fns _ $ (many dispatch-rope : (many (Decls) d) (many (Nat) depth) (many (Adt) adt) (many (List $ Nat) live) (many (Rope) scrut0) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (let-match many (match many (adt-ext adt) (((Maybe $ List $ Piece) _)) ((None _) (None _)) ((Some _ e) (find-template (decl-templates d) "match" (ext-type-name e) 0))) (None _)
    ((Some _ ps) (templated-dispatch ps depth (list-length _ $ adt-ctors adt) live scrut0 arms dflt)))
  (let ((many scrut)) $ match many (adt-ext adt) (((Rope) _)) ((None _) scrut0) ((Some _ e) (rcat3 (RStr $ str-cat3 "(des_" (ext-type-name e) " ") scrut0 $ RStr ")")))
  (match many (and (adt-tagged adt) $ not $ adt-newtype adt) _
    ((BTrue)
      (let ((many shape)) $ adt-shape adt)
      (let ((many ty)) $ match many (narrowed adt live) (((String) _)) ((BTrue) (str-cat "yes " $ narrow-name d shape $ live-key live)) ((BFalse) (shape-name d shape)))
      (let ((many dflt2)) $ match many (shape-wide shape) (((Maybe $ Rope) _)) ((BTrue) (Some _ $ default-rope dflt)) ((BFalse) dflt))
      (let ((many inner))
        (match many arms (((Rope) _))
          ((Nil _) (match many dflt2 (((Rope) _)) ((None _) (RStr "| _ -> .")) ((Some _ dr) (rcat (RStr "| _ -> ") dr))))
          ((Cons _ _ _) (rcat (tagged-arms d shape arms) $ match many dflt2 (((Rope) _)) ((None _) (REmpty)) ((Some _ dr) (rcat (RStr "| _ -> ") dr))))))
      (rcat5 (RStr "(match (Obj.obj ") scrut (RStr $ str-cat3 " : " ty ") with ") inner $ RStr ")"))
    ((BFalse)
      (let-match many (adt-newtype adt) (BTrue)
        ((BFalse) (block-dispatch d scrut arms dflt)))
      (let-match many arms (Cons _ arm _) ((Nil _) (default-rope dflt)))
      (match many arm _ ((MkArm _ fs body) (untuple-rope fs scrut body))))))

; What an arm over a whole ADT does with a constructor's fields: wraps them in Some for one constructor and
; None for the rest, takes the first, or makes the driver's request of them.
(def-adts $ (ArmKind : -> Type)
  enum
  (many AkOption : (many (String) cname) -> (ArmKind))
  (many AkField : -> (ArmKind))
  (many AkVariant : -> (ArmKind))
  (many AkTuple : -> (ArmKind))
  (many AkIs : (many (String) cname) -> (ArmKind))
  (many AkIndex : -> (ArmKind)))

(def-fns _ $ (many bool-ml : (many (Bool) b) -> (many (String) s))
  (match many b _ ((BTrue) "true") ((BFalse) "false")))

(def-fns _ $ (many arm-body : (many (ArmKind) k) (many (Ctor) c) (many (List $ Rope) fs) -> (many (Rope) r))
  (let-match many k (AkOption cname)
    ((AkField) (match many fs _ ((Nil _) (RStr "(absurd ())")) ((Cons _ f _) f)))
    ((AkVariant) (match many fs _
      ((Nil _) (RStr $ str-cat3 "(Driver_core." (ctor-name c) ")"))
      (else (rcat3 (RStr $ str-cat3 "(Driver_core." (ctor-name c) " (") (commas fs) $ RStr "))"))))
    ((AkTuple) (rcat3 (RStr "(") (commas fs) $ RStr ")"))
    ((AkIs n) (RStr $ bool-ml $ str-eqb n $ ctor-name c))
    ((AkIndex) (RStr $ str-cat "print_int " $ nat-str $ ctor-index c)))
  (match many (str-cmp (ctor-name c) cname) _
    ((CEq _ _ _) (rcat3 (RStr "(Some (") (commas fs) $ RStr "))"))
    (else (RStr "None"))))

(def-fns _ $ (many ctor-arms : (many (Decls) d) (subterm many (List $ Ctor) cs) (many (ArmKind) k) -> (many (List $ Arm) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let ((many fs)) $ field-names (ctor-arity c) 0)
  (Cons _ (MkArm (ctor-index c) fs $ arm-body k c fs) $ notail $ ctor-arms d rest k))

(def-fns _ $ (many all-live : (many (Adt) adt) -> (many (List $ Nat) r))
  (nat-range (list-length _ $ adt-ctors adt) 0))

; A Matchable at runtime: the identity for a plain type, for an extern type the FFI's unwrap into the shape
; its constructors describe, which a held match then matches on directly.
(def-fns _ $ (many held-arms : (subterm many (List $ Ctor) cs) (many (Decls) d) -> (many (List $ Arm) r))
  (let-match many cs (Cons _ c rest) ((Nil _) (Nil _)))
  (let ((many fs)) $ field-names (ctor-arity c) 0)
  (Cons _ (MkArm (ctor-index c) fs $ plain-build d c fs) $ notail $ held-arms rest d))

(def-fns _ $ (many matchable-rope : (many (Adt) adt) (many (Decls) d) -> (many (Rope) r))
  (match many (adt-ext adt) _
    ((None _) (RStr "m_plain"))
    ((Some _ _) (rcat3 (RStr "(Obj.repr (fun held -> ") (dispatch-rope d 0 adt (all-live adt) (RStr "held") (held-arms (adt-ctors adt) d) $ None _) $ RStr "))"))))

(def-fns _ $ (many z-rope : (many (Nat) n) -> (many (Rope) r))
  (rcat3 (RStr "(Z.of_string \"") (nat-rope n) $ RStr "\")"))

(def-fns _ $ (many spot-rope : (many (String) file) (many (Spot) p) -> (many (Rope) r))
  (let-match many (spot-pos file p) (MkPos f l c) ((NoPos) (RStr "Ffi_core.NoLoc")))
  (rcat3 (rcat3 (RStr "(Ffi_core.At { file = ") (quoted f) $ RStr "; line = ") (rcat3 (z-rope l) (RStr "; col = ") (z-rope c)) $ RStr " })"))

(def-fns _ $ (many addr-str : (erased (Hist Block) a) (many (Ref Block a) addr) -> (many (String) r))
  (str-cat "a" $ nat-str $ ref-pos Block _ addr))

(def-fns _ $ (many addr-rope : (erased (Hist Block) a) (many (Ref Block a) addr) -> (many (Rope) r))
  (RStr $ addr-str _ addr))

; The OCaml name of a group's member: its entry's name qualified by the group's address, since a group
; allocated twice is emitted twice.
(def-fns _ $ (many member-name : (erased (Hist Block) a) (many (Env) env) (many (Nat) id) (many (Ref Block a) g) -> (many (String) r))
  (str-cat3 (top-name env id) "_" $ addr-str _ g))

(def-fns _ $ (many addr-ropes : (erased (Hist Block) a) (subterm many (List $ Ref Block a) vs) -> (many (List $ Rope) rs))
  (match many vs _
    ((Nil _) (Nil _))
    ((Cons _ v rest) (Cons _ (addr-rope _ v) $ notail $ addr-ropes _ rest))))

(def-fns _ $ (many handle-decl : (many (Decls) d) (many (Nat) x) (many (Multiplicity) m) -> (many (Decls) r))
  (match many m _ ((Many) (decl-const d x)) (else d)))

(def-fns _
  ((many syn-handle-decl : (many (Decls) d) (subterm many (Syn) r) -> (many (Decls) o))
    (let-match many r (RAtom _ s)
      ((RList _ xs) (tail $ syn-handle-decls d xs))
      (else d))
    (let-match many s (NHandle x _ m _) (else d))
    (handle-decl d x m))
  ((many syn-handle-decls : (many (Decls) d) (subterm many (List $ Syn) xs) -> (many (Decls) o))
    (let-match many xs (Cons _ x rest) ((Nil _) d))
    (tail $ syn-handle-decls (notail $ syn-handle-decl d x) rest)))

(def-fns _ $ (many const-rope : (many (Env) env) (many (Nat) x) -> (many (Rope) r))
  (let ((erased _) (many _) (many en) (many _)) $ env-store env)
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (RStr "(failwith \"unbound constant\")")))
  (let-match many info (MkEInfo _ _ _ s _ _ _ _))
  (match many s _ ((SHypothetical _) (RStr "(failwith \"a Hypothetical constant\")")) ((SSettled _ v _) (addr-rope _ v))))

(def-fns _ $ (many reading-rope : (many (Reading) rd) -> (many (Rope) r))
  (RStr $ match many rd _ ((MintedIs) "Ffi_core.MintedIs") ((MintedType) "Ffi_core.MintedType")))

(def-fns _ $ (many handle-rope : (many (Env) env) (many (Nat) x) (many (Reading) rd) (many (Multiplicity) m) -> (many (Rope) r))
  (rcat5 (RStr "(") (nat-rope x) (RStr "), ") (reading-rope rd) $ rcat4 (RStr ", Ffi_core.") (RStr $ match many m _ ((Erased) "Erased") ((Many) "Many") ((Once) "Unique")) (RStr ", ") $
    match many m _ ((Many) (const-rope env x)) (else (RStr "(Obj.repr ())"))))

(def-fns _
  ((many syn-rope : (many (Env) env) (many (String) file) (subterm many (Syn) r) -> (many (Rope) o))
    (let ((many loc)) $ spot-rope file $ raw-pos r)
    (let ((many (String) k) (many (Rope) x))
      (match many r (((String) _) ((Rope) _))
        ((RAtom _ s) (match many s (((String) _) ((Rope) _))
          ((NSrc t) (values "Atom" $ rcat (RStr "Ffi_core.Src ") $ quoted t))
          ((NGen n t) (values "Atom" $ rcat5 (RStr "Ffi_core.Gen (") (z-rope n) (RStr ", ") (quoted t) $ RStr ")"))
          ((NHandle x rd m _) (values "Handle" $ handle-rope env x rd m)))) ((RNat _ n) (values "Nat" $ z-rope n)) ((RChr _ c) (values "Char" $ nat-rope $ char-code c))
        ((RString _ s) (values "Str" $ quoted s)) ((RWild _) (values "Wild" $ REmpty))
        ((RList _ xs) (values "List" $ bracketed $ notail $ syns-rope env file xs))))
    (match many r (((Rope) _))
      ((RWild _) (rcat3 (RStr "(Ffi_core.Wild ") loc $ RStr ")"))
      (else (rcat5 (RStr "(Ffi_core.") (RStr k) (RStr " (") loc $ rcat3 (RStr ", ") x $ RStr "))"))))
  ((many syns-rope : (many (Env) env) (many (String) file) (subterm many (List $ Syn) xs) -> (many (List $ Rope) r))
    (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (notail $ syn-rope env file x) $ notail $ syns-rope env file rest)))))

(def-fns _ $ (many payload-rope : (many (Env) env) (many (Payload) p) -> (many (Rope) r))
  (let-match many p (PStr s) ((PNat n) (nat-literal n)) ((PHalf n) (nat-literal n))
    ((PBytes b) (rcat3 (RStr "(Obj.repr (Bytes.of_string ") (quoted b) $ RStr "))"))
    ((PRaw f r) (rcat3 (RStr "(Obj.repr ") (syn-rope env f r) $ RStr ")"))
    ((PHandle x rd m _) (rcat3 (RStr "(Obj.repr (") (handle-rope env x rd m) $ RStr "))")))
  (let ((many n) (erased _)) (str-length s))
  (rcat5 (RStr "(Obj.repr ((") (quoted s) (RStr ", 0, ") (nat-rope n) $ RStr ") : Ffi_core.slice))"))

; The prelude's ADT of a type name.
; The prelude's names are found in its scope, as lib/program.ml's driver finds them, however the program
; shadows them.
(def-fns _ $ (many prelude-adt : (many (Env) env) (many (String) name) -> (many (Maybe $ Adt) r))
  (let ((many env2) (many ty)) $ prelude-type env name)
  (type-adt env2 ty))

(def-fns _ $ (many prelude-ctor : (many (Env) env) (many (String) name) -> (many (Maybe $ Ctor) r))
  (let ((many env2) (many x)) $ prelude-id env name)
  (ctor-of env2 x))

(def-fns _ $ (many ffi-arms : (subterm many (List $ Ctor) ctors) -> (many (List $ Arm) r))
  (let-match many ctors (Cons _ ctor rest) ((Nil _) (Nil _)))
  (let ((many fields)) $ field-names (ctor-arity ctor) 0)
  (let ((many body)) $ match many fields (((Rope) _)) ((Nil _) (RStr $ str-cat "Ffi_core." $ ctor-name ctor)) ((Cons _ _ _) (rcat3 (RStr $ str-cat3 "(Ffi_core." (ctor-name ctor) " (") (commas fields) $ RStr "))")))
  (Cons _ (MkArm (ctor-index ctor) fields body) $ notail $ ffi-arms rest))

(def-fns _ $ (many ffi-view : (many (String) label) (many (String) tname) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many (prelude-adt env tname) _
    ((None _) (REmpty))
    ((Some _ adt)
      (rcat5 (RStr "~") (RStr label) (RStr ":(fun v -> ") (dispatch-rope d 0 adt (all-live adt) (RStr "v") (ffi-arms $ adt-ctors adt) $ None _) $ RStr ") "))))

(def-fns _ $ (many ffi-extra : (many (String) name) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (let-match many (str-eqb name "flatten") (BFalse)
    ((BTrue) (rcat (ffi-view "rope" "Rope" env d) $ RStr "~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr ")))
  (let-match many (str-eqb name "list-to-array") (BFalse)
    ((BTrue) (ffi-view "list" "List" env d)))
  (match many (str-eqb name "array-new") _ ((BTrue) (RStr "~blank:(Obj.repr ()) ")) ((BFalse) (REmpty))))

(def-fns _ $ (many objs : (subterm many (List $ Rope) ps) -> (many (List $ Rope) r))
  (match many ps _
    ((Nil _) (Nil _))
    ((Cons _ p rest) (Cons _ (rcat3 (RStr "(Obj.obj ") p $ RStr ")") $ notail $ objs rest))))

(def-fns _ $ (many outcomes-of : (many (String) name) (many (List $ Piece) ps) -> (many (List $ Nat) s))
  (let-match many (has-outcomes ps) (BTrue) ((BFalse) (Nil _)))
  (let-match many (extern-of name) (Some _ se) ((None _) (Nil _)))
  (let-match many se (MkSomeExtern _ e))
  (match many (ext-result-shape _ e) _ ((Some _ s) s) ((None _) (Nil _))))

(def-fns _ $ (many ffi-call : (many (String) name) (many (List $ Rope) params) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many (find-template (decl-templates d) "fn" name 0) _
    ((Some _ ps) (templated-build d ps (outcomes-of name ps) 0 params))
    ((None _) (rcat5 (RStr "(Obj.repr (Ffi_core.") (RStr $ sanitize name) (rcat (RStr " ") $ ffi-extra name env d) (match many params _ ((Nil _) (RStr "()")) (else (rjoin (objs params) " "))) $ RStr "))"))))



(def-fns _ $ (many cell-narrowed : (many (List $ Nat) shape) -> (many (Bool) r))
  (and (nat-lt (Succ (Zero)) $ list-length _ shape) $ not $ shape-wide shape))

(def-fns _ $ (many cell-view : (many (Decls) d) (many (Ctor) c) -> (many (String) ty) (many (String) k) (many (String) rest))
  (match many (ctor-tagged c) _
    ((BTrue)
      (let ((many shape)) $ ctor-shape c)
      (let-match many (shape-wide shape) (BFalse) ((BTrue) (values (shape-name d shape) (wide-name d shape) " | _ -> absurd ()")))
      (let ((many k)) $ ctor-name-at d shape $ ctor-index c)
      (match many (cell-narrowed shape) (((String) _) ((String) k2) ((String) _))
        ((BTrue) (values (str-cat "yes " $ narrow-name d shape $ live-key $ Cons _ (ctor-index c) $ Nil _) k ""))
        ((BFalse) (values (shape-name d shape) k ""))))
    ((BFalse)
      (let ((many shape)) $ Cons _ (ctor-arity c) $ Nil _)
      (values (shape-name d shape) (ctor-name-at d shape (Zero)) ""))))

(def-fns _ $ (many field-writes : (subterm many (List $ Nat) indices) (many (List $ Rope) args) (many (String) r) -> (many (List $ Rope) ws))
  (let-match many indices (Cons _ i rest) ((Nil _) (Nil _)))
  (match many args _
    ((Nil _) (Nil _))
    ((Cons _ arg more)
      (Cons _ (rcat3 (RStr $ str-cat3 r ".f" $ nat-str i) (RStr " <- ") arg) $ notail $ field-writes rest more r))))

(def-fns _ $ (many field-match-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (String) r) (many (Rope) body) -> (many (Rope) w))
  (let ((many ty) (many k) (many rest)) $ cell-view d c)
  (rcat5 (RStr "(match (Obj.obj ") target (RStr $ str-cat3 " : " ty $ str-cat3 ") with " k $ str-cat3 " " r " -> ") body $ RStr $ str-cat rest ")"))

(def-fns _ $ (many field-store-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (List $ Nat) indices) (many (List $ Rope) args) (many (String) r) -> (many (Rope) w))
  (field-match-rope d c target r $ rjoin (field-writes indices args r) "; "))

(def-fns _ $ (many field-read-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (Nat) index) (many (String) r) -> (many (Rope) w))
  (field-match-rope d c target r $ RStr $ str-cat3 r ".f" $ nat-str index))

(def-fns _ $ (many written-or : (many (Nat) i) (subterm many (List $ Nat) indices) (many (List $ Rope) names) (many (Rope) dflt) -> (many (Rope) w))
  (let-match many indices (Cons _ j rest) ((Nil _) dflt))
  (let-match many names (Cons _ x more) ((Nil _) dflt))
  (match many (nat-eqb i j) _ ((BTrue) x) ((BFalse) (tail $ written-or i rest more dflt))))

(def-fns _ $ (many copied-fields : (many (String) r) (subterm many (Nat) n) (many (Nat) i) (many (List $ Nat) indices) (many (List $ Rope) names) -> (many (List $ Rope) fs))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (Cons _ (written-or i indices names $ RStr $ str-cat3 r ".f" $ nat-str i) $ notail $ copied-fields r k (Succ i) indices names))

; A fresh block holding [target]'s fields with the written ones in their place (lib/extract.ml's field_copy): a
; `cell-write` or an invocation on a cell at `many`.
(def-fns _ $ (many field-copy-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (List $ Nat) indices) (many (List $ Rope) args) (many (Nat) depth) -> (many (Rope) w))
  (let-match many (ctor-arity c) (Succ _) ((Zero) (plain-build d c $ Nil _)))
  (let ((many prefix)) $ str-cat "copy" $ nat-str depth)
  (let ((many names) (many binds)) $ bind-args prefix args 0)
  (let ((many r)) $ str-cat prefix "_r")
  (rcat5 (RStr $ str-cat3 "(let " prefix " = ") target (RStr " in ")
    (let-binds-rope binds $ field-match-rope d c (RStr prefix) r $ plain-build d c $ copied-fields r (ctor-arity c) 0 indices names) $ RStr ")"))

(def-fns _ $ (many split-imm : (many (List $ Nat) imms) (subterm many (List $ Nat) indices) (many (List $ Rope) names) ->
    (many (List $ Nat) bi) (many (List $ Rope) bn) (many (List $ Nat) ii) (many (List $ Rope) iname))
  (let-match many indices (Cons _ i rest) ((Nil _) (values (Nil _) (Nil _) (Nil _) $ Nil _)))
  (let-match many names (Cons _ n more) ((Nil _) (values (Nil _) (Nil _) (Nil _) $ Nil _)))
  (let ((many bi) (many bn) (many ii) (many iname)) $ notail $ split-imm imms rest more)
  (match many (nat-mem imms i) _
    ((BTrue) (values bi bn (Cons _ i ii) $ Cons _ n iname))
    ((BFalse) (values (Cons _ i bi) (Cons _ n bn) ii iname))))

(def-fns _ $ (many imm-stores : (many (Rope) cell) (many (Bool) wide) (subterm many (List $ Nat) indices) (many (List $ Rope) names) -> (many (List $ Rope) ss))
  (let-match many indices (Cons _ i rest) ((Nil _) (Nil _)))
  (let-match many names (Cons _ n more) ((Nil _) (Nil _)))
  (let ((many k)) $ match many wide (((Nat) _)) ((BTrue) (Succ i)) ((BFalse) i))
  (Cons _ (rcat5 (RStr "Array.unsafe_set (Obj.obj ") cell (RStr $ str-cat3 " : int array) " (nat-str k) " (Obj.obj ") n $ RStr " : int)")
    (notail $ imm-stores cell wide rest more)))

(def-fns _ $ (many cell-write-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) cell) (many (List $ Nat) indices) (many (List $ Rope) args) (many (List $ Nat) imms) (many (Nat) depth) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "cell" $ nat-str depth)
  (let ((many cr)) $ RStr prefix)
  (let ((many names) (many binds)) $ bind-args prefix args 0)
  (let ((many bi) (many bn) (many ii) (many iname)) $ split-imm imms indices names)
  (let ((many barred)) $ match many bi (((List $ Rope) _)) ((Nil _) (Nil _)) ((Cons _ _ _) (Cons _ (field-store-rope d c cr bi bn $ str-cat prefix "_r") $ Nil _)))
  (let ((many stores) (erased _)) $ list-append _ barred $ imm-stores cr (and (ctor-tagged c) $ shape-wide $ ctor-shape c) ii iname)
  (let ((many body)) $ let-binds-rope binds $ match many stores (((Rope) _)) ((Nil _) cr) ((Cons _ _ _) (rcat3 (rjoin stores "; ") (RStr "; ") cr)))
  (rcat5 (RStr "(let ") cr (rcat3 (RStr " = ") cell $ RStr " in ") body $ RStr ")"))

(def-fns _ $ (many let-rope : (many (List $ Rope) xs) (many (Rope) rr) (many (Rope) body) -> (many (Rope) r))
  (match many xs _
    ((Nil _) (rcat5 (RStr "(let _ = ") rr (RStr " in ") body $ RStr ")"))
    ((Cons _ _ _) (untuple-rope xs rr body))))

; ---- The declarations: found by a walk over every block of the store and the code it holds, then written
; ahead of the blocks; the narrowed copies come before the shapes, so a bare constructor names the shape's.

(def-fns _ $ (many collect-ctor : (many (Ctor) c) (many (Decls) d) -> (many (Decls) r))
  (let-match many (ctor-tagged c) (BFalse) ((BTrue) (decl-shape d $ ctor-shape c)))
  (match many (ctor-newtype c) _
    ((BTrue) d)
    ((BFalse) (decl-shape d $ Cons _ (ctor-arity c) $ Nil _))))

(def-fns _ $ (many collect-cell : (many (Ctor) c) (many (Decls) d) -> (many (Decls) r))
  (let-match many (ctor-tagged c) (BTrue) ((BFalse) (collect-ctor c d)))
  (let ((many shape)) $ ctor-shape c)
  (match many (cell-narrowed shape) (((Decls) _))
    ((BTrue) (decl-narrow d shape $ live-key $ Cons _ (ctor-index c) $ Nil _))
    ((BFalse) (decl-shape d shape))))

(def-fns _ $ (many collect-ctors : (subterm many (List $ Ctor) cs) (many (Decls) d) -> (many (Decls) r))
  (match many cs _
    ((Nil _) d)
    ((Cons _ c rest) (tail $ collect-ctors rest $ collect-ctor c d))))

; An extern type's shape is declared too, as the target of its Matchable's unwrap.
(def-fns _ $ (many collect-adt : (many (Adt) adt) (many (Decls) d) -> (many (Decls) r))
  (match many (adt-tagged adt) _ ((BTrue) (decl-shape d $ adt-shape adt)) ((BFalse) (collect-ctors (adt-ctors adt) d))))

(def-fns _ $ (many collect-match : (many (Adt) adt) (many (List $ Nat) live) (many (Decls) d) -> (many (Decls) r))
  (let-match many (adt-tagged adt) (BTrue) ((BFalse) (collect-adt adt d)))
  (match many (narrowed adt live) _
    ((BTrue) (decl-narrow d (adt-shape adt) $ live-key live))
    ((BFalse) (decl-shape d $ adt-shape adt))))

(def-fns _ $ (many nat-list-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (match many xs _
    ((Nil _) (BFalse))
    ((Cons _ y rest) (or (nat-eqb x y) $ tail $ nat-list-mem rest x))))

(def-fns _
  ((many collect-code : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (let-match many code (CMatch _ _ scrut shape branches dfl live)
      ((CValue _ v) (tail $ collect-block _ v env d))
      ((CValues _ _ cs _) (tail $ collect-codes _ cs env d))
      ((CApp _ _ f args _) (tail $ collect-codes _ args env $ notail $ collect-code _ _ f env d))
      ((CCellAlloc _ ctor slots) (tail $ collect-codes _ slots env $ collect-ctor ctor d))
      ((CCellWrite _ k2 cell slots _) (tail $ collect-slots _ slots env $ notail $ collect-code _ _ cell env $ collect-cell k2 d))
      ((CCellCopy _ k2 cell slots) (tail $ collect-slots _ slots env $ notail $ collect-code _ _ cell env $ collect-cell k2 $ collect-ctor k2 d))
      ((CCellRead _ k2 _ cell) (tail $ collect-code _ _ cell env $ collect-cell k2 d))
      ((CWorldDo _ req) (tail $ collect-code _ _ req env d))
      ((CPrim _ _ _ args) (tail $ collect-codes _ args env d))
      ((CLet _ _ _ _ _ rhs rest) (tail $ collect-code _ _ rest env $ notail $ collect-code _ _ rhs env d))
      ((CLetRec _ _ _ g rest) (match many g _ ((MkGroup _ _ fns _) (tail $ collect-code _ _ rest env $ notail $ collect-group _ _ fns env d))))
      ((CConst _ x) (decl-const d x))
      (else d))
    (let ((many d1)) $ notail $ collect-code _ _ scrut env d)
    (let ((many (Decls) d2))
      (match many shape _
        ((ShKnown _ adt) (collect-match adt live d1))
        ((ShHeld _ mcode adt) (collect-match adt live $ notail $ collect-code _ _ mcode env d1))
        ((ShNone _) d1)))
    (let ((many d3)) $ notail $ collect-branches _ _ branches env d2)
    (match many dfl _ ((None _) d3) ((Some _ dd) (tail $ collect-code _ _ dd env d3))))

  ((many collect-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many cs _
      ((Nil _) d)
      ((Cons _ c rest) (tail $ collect-codes _ rest env $ notail $ collect-code _ _ c env d))))


  ((many collect-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (let-match many slots (Cons _ slot rest)
      ((Nil _) d))
    (match many slot _ ((MkPair _ _ _ code) (tail $ collect-slots _ rest env $ notail $ collect-code _ _ code env d))))

  ((many collect-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (let-match many bs (Cons _ b rest)
      ((Nil _) d))
    (match many b _ ((MkBranch _ _ _ _ body) (tail $ collect-branches _ _ rest env $ notail $ collect-code _ _ body env d))))

  ((many collect-group : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (let-match many fns (Cons _ p rest) ((Nil _) d))
    (let-match many p (MkPair _ _ _ fn))
    (let-match many fn (MkFunc _ _ _ _ fid _ body impl _) ((MkAlias _ _ _ _ target) (tail $ collect-group _ _ rest env $ notail $ collect-code _ _ target env d)))
    (let ((many (Decls) d1))
      (match many impl _
        ((None _) (notail $ collect-code _ _ body env d))
        ((Some _ im)
          (let-match many im (MkImpl se _))
          (let-match many se (MkSomeExtern _ e))
          (match many (find-template (decl-templates d) "fn" (ext-name _ e) 0) _
            ((Some _ ps) (decl-call-template d fid ps $ outcomes-of (ext-name _ e) ps))
            ((None _) d)))))
    (tail $ collect-group _ _ rest env d1))

  ((many collect-block : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (let-match many b (BGroup _ _ _ g _)
      ((BTag _ c _) (collect-cell c d))
      ((BCtorFn _ c) (collect-ctor c d))
      ((BMat _ adt) (collect-adt adt d))
      ((BExt _ p) (match many p _ ((PHandle x _ m _) (handle-decl d x m)) ((PRaw _ r) (syn-handle-decl d r)) (else d)))
      (else d))
    (match many g _ ((MkGroup _ _ fns _) (tail $ collect-group _ _ fns env d)))))



(def-fns _ $ (many ctor-decls : (many (Decls) d) (many (List $ Nat) s) (many (Bool) wide) (many (List $ Rope) last) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (List $ Rope) r))
  (let-match many arities (Cons _ n rest) ((Nil _) last))
  (let ((many more)) $ notail $ ctor-decls d s wide last rest $ Succ i)
  (let-match many n (Succ _) ((Zero) (Cons _ (RStr $ ctor-name-at d s i) more)))
  (match many wide _
    ((BTrue) more)
    ((BFalse) (Cons _ (rcat3 (RStr $ str-cat (ctor-name-at d s i) " of { ") (rjoin (record-types n 0) "; ") $ RStr " }") more))))

(def-fns _ $ (many shape-decls : (many (Decls) d) (subterm many (List $ List $ Nat) ss) (many (Bool) first) -> (many (Rope) r))
  (let-match many ss (Cons _ s rest) ((Nil _) (REmpty)))
  (let ((many wide)) $ shape-wide s)
  (let ((many shared)) $ match many wide (((List $ Rope) _))
    ((BTrue) (Cons _ (rcat3 (RStr $ str-cat (wide-name d s) " of { d : int; ") (rjoin (record-types (widest s) 0) "; ") $ RStr " }") $ Nil _))
    ((BFalse) (Nil _)))
  (rcat5 (RStr $ match many first (((String) _)) ((BTrue) "type ") ((BFalse) "and ")) (RStr $ shape-name d s) (RStr " = ") (rjoin (ctor-decls d s wide shared s 0) " | ") $ rcat (RStr "\n") $ notail $ shape-decls d rest $ BFalse))

(def-fns _ $ (many narrow-ctors : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) (many (String) name) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (Rope) r))
  (let-match many arities (Cons _ n rest) ((Nil _) (REmpty)))
  (let ((many (Rope) sep)) $ match many rest _ ((Nil _) (REmpty)) ((Cons _ _ _) (RStr " | ")))
  (let ((many (String) idx)) $ match many (nat-list-mem live i) _ ((BTrue) "yes ") ((BFalse) "no "))
  (let ((many (Rope) fields)) $ match many n _ ((Zero) (REmpty)) ((Succ _) (rcat3 (RStr "{ ") (rjoin (record-types n 0) "; ") $ RStr " } -> ")))
  (rcat5 (RStr $ str-cat (ctor-name-at d s i) " : ") fields (RStr $ str-cat idx name) sep $ notail $ narrow-ctors d s live name rest $ Succ i))

(def-fns _ $ (many narrow-decls : (many (Decls) d) (subterm many (List $ Narrow) ns) -> (many (Rope) r))
  (let-match many ns (Cons _ n rest) ((Nil _) (REmpty)))
  (let-match many n (MkNarrow s live))
  (let ((many name)) $ narrow-name d s live)
  (rcat4 (RStr $ str-cat3 "type _ " name " = ") (narrow-ctors d s live name s 0) (RStr "\n") $ notail $ narrow-decls d rest))

(def-fns _ $ (many decls-rope : (many (Decls) d) -> (many (Rope) r))
  (match many d _
    ((MkDecls shapes2 narrows _ _) (rcat (narrow-decls d narrows) $ shape-decls d shapes2 $ BTrue))))

(def-fns _ $ (many prim-rope : (many (Env) env) (many (Sp) p) (many (List $ Rope) hs) -> (many (Rope) r))
  (let-match many hs (Cons _ h hidden) ((Nil _) (rcat3 (RStr "(failwith ") (quoted $ no-macro-world p) $ RStr ")")))
  (let ((many no-ctors)) (RStr "(failwith \"`slot-eq` with no constructors\")"))
  (let-match many (sp-eq p $ SpExpr $ ExSlotEq) (BFalse)
    ((BTrue)
      (let-match many hidden (Cons _ b q1) ((Nil _) no-ctors))
      (let-match many q1 (Cons _ none q2) ((Nil _) no-ctors))
      (let-match many q2 (Cons _ some _) ((Nil _) no-ctors))
      (rcat5 (rcat3 (RStr "(if ") h $ RStr " == ") b (RStr " then ") some $ rcat3 (RStr " else ") none $ RStr ")")))
  (let-match many (sp-eq p $ SpExpr $ ExSettledValue) (BFalse) ((BTrue) (rcat3 (RStr "(let (_, _, _, v) = (Obj.obj ") h $ RStr " : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in v)")))
  (let-match many (sp-eq p $ SpExpr $ ExSettledErase) (BFalse)
    ((BTrue) (rcat3 (RStr "(Obj.repr (let (x, r, _, _) = (Obj.obj ") h $ RStr " : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in (x, r, Ffi_core.Erased, Obj.repr ())))")))
  (let-match many (sp-eq p $ SpExpr $ ExSettledType) (BFalse)
    ((BTrue) (rcat5 (RStr "(Obj.repr (match (Obj.obj ") h (RStr " : int * Ffi_core.reading * Ffi_core.mult * Obj.t) with (x, Ffi_core.MintedIs, _, _) -> (x, Ffi_core.MintedType, Ffi_core.Erased, Obj.repr ()) | _ -> (") (handle-rope env type-id (MintedIs) (Erased)) $ RStr ")))")))
  (let-match many (sp-eq p $ SpExpr $ ExSettledMult) (BTrue) ((BFalse) (rcat3 (RStr "(failwith ") (quoted $ no-macro-world p) $ RStr ")")))
  (let-match many hidden (Cons _ ce r1) ((Nil _) (RStr "(failwith \"`settled-mult` with no constructors\")")))
  (let-match many r1 (Cons _ cm r2) ((Nil _) (RStr "(failwith \"`settled-mult` with no constructors\")")))
  (let-match many r2 (Cons _ cu _) ((Nil _) (RStr "(failwith \"`settled-mult` with no constructors\")")))
  (rcat5 (rcat3 (RStr "(match (Obj.obj ") h $ RStr " : int * Ffi_core.reading * Ffi_core.mult * Obj.t) with (_, _, Ffi_core.Erased, _) -> ") ce (RStr " | (_, _, Ffi_core.Many, _) -> ") cm $ rcat3 (RStr " | _ -> ") cu $ RStr ")"))

(def-fns _ $ (many block-rope : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many b _
    ((BTag _ c fields) (build-rope d 0 c $ addr-ropes _ fields))
    ((BTup _ fields) (tuple-rope $ addr-ropes _ fields))
    ((BExt _ p) (payload-rope env p))
    ((BArray _ n es) (rcat3 (RStr "(Obj.repr [|") (rjoin (addr-ropes _ $ idmap-prefix _ es n $ Nil _) "; ") $ RStr "|])"))
    ((BSlots _ n ks _) (rcat3 (RStr "(Obj.repr (let t = Ffi_core.slots_new () in List.iter (fun k -> ignore (Ffi_core.slots_add t k)) [ ") (rjoin (addr-ropes _ $ idmap-prefix _ ks n $ Nil _) "; ") $ RStr " ]; t))"))
    ((BCtorFn _ c) (ctor-fn-rope d c))
    ((BMat _ adt) (matchable-rope adt d))
    ((BGroup _ _ _ _ _) (RStr "(failwith \"a group as a closed value\")"))
    ((BFn _ g _ id) (RStr $ str-cat3 "(Obj.repr " (member-name _ env id g) ")"))
    ((BToken _) (RStr "(Obj.repr ())"))
    ((BError _ m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

(def-adts $ (Key : -> Type)
  enum
  (many KVal : (many (Nat) x) -> (Key))
  (many KFn : (many (Nat) m) -> (Key)))

(def-fns _ $ (many key-id : (many (Key) k) -> (many (Nat) x))
  (match many k _ ((KVal x) x) ((KFn x) x)))

(def-fns _ $ (many key-lt : (many (Key) a) (many (Key) b) -> (many (Bool) r))
  (match many a _
    ((KVal x) (match many b _ ((KVal y) (nat-lt x y)) ((KFn _) (BTrue))))
    ((KFn x) (match many b _ ((KVal _) (BFalse)) ((KFn y) (nat-lt x y))))))

(def-fns _ $ (many key-eqb : (many (Key) a) (many (Key) b) -> (many (Bool) r))
  (and (not $ key-lt a b) $ not $ key-lt b a))

(def-fns _ $ (many key-insert : (many (Key) k) (subterm many (List $ Key) ks) -> (many (List $ Key) r))
  (let-match many ks (Cons _ h rest) ((Nil _) (Cons _ k $ Nil _)))
  (let-match many (key-lt k h) (BFalse) ((BTrue) (Cons _ k ks)))
  (match many (key-eqb k h) _ ((BTrue) ks) ((BFalse) (Cons _ h $ notail $ key-insert k rest))))

(def-fns _ $ (many keys-eqb : (subterm many (List $ Key) a) (many (List $ Key) b) -> (many (Bool) r))
  (let-match many a (Cons _ x rest) ((Nil _) (list-is-empty _ b)))
  (let-match many b (Cons _ y more) ((Nil _) (BFalse)))
  (and (key-eqb x y) $ tail $ keys-eqb rest more))

(def-fns _ $ (many keys-own : (many (List $ Nat) ids) (subterm many (List $ Key) ks) -> (many (Bool) r))
  (let-match many ks (Cons _ k rest) ((Nil _) (BTrue)))
  (match many k _
    ((KVal _) (BFalse))
    ((KFn m) (and (nat-list-mem ids m) $ tail $ keys-own ids rest))))

(def-fns _ $ (many fac-caps : (many (List $ Nat) ids) (subterm many (List $ Key) ks) -> (many (List $ Key) r))
  (let-match many ks (Cons _ k rest) ((Nil _) (Nil _)))
  (let ((many (Bool) own)) $ match many k _ ((KFn m) (nat-list-mem ids m)) ((KVal _) (BFalse)))
  (match many own _ ((BTrue) (tail $ fac-caps ids rest)) ((BFalse) (Cons _ k $ notail $ fac-caps ids rest))))

(def-adts $ (Target : -> Type)
  enum
  (many TgVar : (many (Nat) x) -> (Target))
  (many TgConst : (many (Nat) x) -> (Target))
  (many TgNone : -> (Target)))

(def-fns _ $ (many target-of : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) c) -> (many (Target) t))
  (match many c _ ((CVar _ x _) (TgVar x)) ((CConst _ x) (TgConst x)) (else (TgNone))))

(def-adts $ (GInfo : -> Type)
  enum
  (many MkGInfo : (many (List $ Nat) ids) (many (List $ Nat) arities) (many (List $ Nat) uses) (many (List $ Pair (Nat) (Nat)) heads)
    (many (IdMap $ Unit) binders) (many (IdMap $ Unit) inner) (many (List $ Nat) consts) (many (Maybe $ Nat) parent) (many (List $ Key) caps) (many (Bool) top) -> (GInfo)))

(def-adts $ (SomeGroup : -> Type)
  enum
  (many MkSomeGroup : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Group gids ctx) g) -> (SomeGroup)))

(def-adts $ (Reg : -> Type)
  enum
  (many MkReg : (many (IdMap $ GInfo) infos) (many (IdMap $ SomeGroup) codes) (many (IdMap $ Nat) owner) (many (IdMap $ Target) aliases) (many (List $ Nat) keys) (many (IdMap $ List $ Nat) rets) -> (Reg)))

(def-adts $ (Acc : -> Type)
  enum
  (many MkAcc : (many (List $ Nat) uses) (many (List $ Pair (Nat) (Nat)) heads) (many (IdMap $ Unit) binders) (many (IdMap $ Unit) inner) (many (List $ Nat) consts) -> (Acc)))

(let ((many acc-empty)) (MkAcc (Nil _) (Nil _) (MEmpty _) (MEmpty _) (Nil _)))
(let ((many reg-empty)) (MkReg (MEmpty _) (MEmpty _) (MEmpty _) (MEmpty _) (Nil _) (MEmpty _)))

(def-fns _ $ (many set-add-all : (subterm many (List $ Nat) xs) (many (IdMap $ Unit) s) -> (many (IdMap $ Unit) r))
  (let-match many xs (Cons _ x rest) ((Nil _) s))
  (tail $ set-add-all rest $ idmap-set _ x (MkUnit) s))

(def-fns _ $ (many pair-keys : (erased Type V) (subterm many (List $ Pair (Nat) V) ps) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many ps (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ k _))
  (tail $ pair-keys _ rest $ Cons _ k acc))

(def-fns _ $ (many set-union : (many (IdMap $ Unit) a) (many (IdMap $ Unit) b) -> (many (IdMap $ Unit) r))
  (set-add-all (pair-keys _ (idmap-pairs _ b 1 0 $ Nil _) $ Nil _) a))

(def-fns _ $ (many acc-use : (many (Nat) x) (many (Acc) a) -> (many (Acc) r))
  (match many a _ ((MkAcc us hs bs ins cs) (MkAcc (Cons _ x us) hs bs ins cs))))

(def-fns _ $ (many acc-head : (many (Nat) x) (many (Nat) n) (many (Acc) a) -> (many (Acc) r))
  (match many a _ ((MkAcc us hs bs ins cs) (MkAcc us (Cons _ (MkPair _ _ x n) hs) bs ins cs))))

(def-fns _ $ (many acc-bind : (many (Bool) binding) (many (List $ Nat) xs) (many (Acc) a) -> (many (Acc) r))
  (let-match many binding (BTrue) ((BFalse) a))
  (match many a _ ((MkAcc us hs bs ins cs) (MkAcc us hs (set-add-all xs bs) ins cs))))

(def-fns _ $ (many acc-const : (many (Nat) x) (many (Acc) a) -> (many (Acc) r))
  (match many a _ ((MkAcc us hs bs ins cs) (MkAcc us hs bs ins $ Cons _ x cs))))

(def-fns _ $ (many acc-merge : (many (Bool) binding) (many (GInfo) g) (many (Acc) a) -> (many (Acc) r))
  (let-match many g (MkGInfo ids _ us2 hs2 bs2 is2 cs2 _ _ _))
  (let-match many a (MkAcc us hs bs ins cs))
  (MkAcc (rev-onto _ us2 us) (rev-onto _ hs2 hs) (match many binding (((IdMap $ Unit) _)) ((BTrue) (set-union bs bs2)) ((BFalse) bs)) (set-add-all ids $ set-union ins is2) (rev-onto _ cs2 cs)))

(def-fns _ $ (many reg-get : (many (Reg) r) (many (Nat) key) -> (many (Maybe $ GInfo) i))
  (let-match many r (MkReg infos _ _ _ _ _))
  (match many (idmap-get _ key infos) _ ((Hit _ _ _ i _) (Some _ i)) ((Miss _ _ _ _) (None _))))

(def-fns _ $ (many reg-put : (many (Reg) r) (many (Nat) key) (many (GInfo) i) -> (many (Reg) r2))
  (match many r _ ((MkReg infos codes owner aliases keys rets) (MkReg (idmap-set _ key i infos) codes owner aliases keys rets))))

(def-fns _ $ (many reg-owner : (many (Reg) r) (many (Nat) x) -> (many (Maybe $ Nat) k))
  (let-match many r (MkReg _ _ owner _ _ _))
  (match many (idmap-get _ x owner) _ ((Hit _ _ _ k _) (Some _ k)) ((Miss _ _ _ _) (None _))))

(def-fns _ $ (many reg-caps : (many (Reg) r) (many (Nat) key) -> (many (List $ Key) caps))
  (let-match many (reg-get r key) (Some _ i) ((None _) (Nil _)))
  (let-match many i (MkGInfo _ _ _ _ _ _ _ _ cs _))
  cs)

(def-fns _ $ (many reg-members : (many (Reg) r) (many (Nat) key) -> (many (List $ Nat) ids))
  (let-match many (reg-get r key) (Some _ i) ((None _) (Nil _)))
  (let-match many i (MkGInfo ids _ _ _ _ _ _ _ _ _))
  ids)

(def-fns _ $ (many reg-closed : (many (Reg) r) (many (Nat) key) -> (many (Bool) b))
  (list-is-empty _ $ reg-caps r key))

(def-fns _ $ (many reg-ret : (many (Reg) r) (many (Nat) key) -> (many (List $ Nat) ids))
  (let-match many r (MkReg _ _ _ _ _ rets))
  (match many (idmap-get _ key rets) _ ((Hit _ _ _ ids _) ids) ((Miss _ _ _ _) (Nil _))))

(def-fns _ $ (many reg-code-of : (many (Reg) r) (many (Nat) key) -> (many (Maybe $ SomeGroup) g))
  (let-match many r (MkReg _ codes _ _ _ _))
  (match many (idmap-get _ key codes) _ ((Hit _ _ _ g _) (Some _ g)) ((Miss _ _ _ _) (None _))))

(def-fns _ $ (many reg-resolve-n : (subterm many (Nat) fuel) (many (Reg) r) (many (Nat) x) -> (many (Target) t))
  (let-match many r (MkReg _ _ _ aliases _ _))
  (let-match many (idmap-get _ x aliases) (Hit _ _ _ t _) ((Miss _ _ _ _) (TgVar x)))
  (let-match many t (TgVar y) (else t))
  (match many fuel _ ((Zero) t) ((Succ k) (tail $ reg-resolve-n k r y))))

(def-fns _ $ (many reg-resolve : (many (Reg) r) (many (Nat) x) -> (many (Target) t))
  (reg-resolve-n 16 r x))

(def-fns _ $ (many nat-index : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (None _)))
  (match many (nat-eqb x y) _ ((BTrue) (Some _ i)) ((BFalse) (tail $ nat-index rest x $ Succ i))))

(def-fns _ $ (many reg-arity : (many (Reg) r) (many (Nat) key) (many (Nat) x) -> (many (Nat) n))
  (let-match many (reg-get r key) (Some _ i) ((None _) 0))
  (let-match many i (MkGInfo ids ars _ _ _ _ _ _ _ _))
  (let-match many (nat-index ids x 0) (Some _ k) ((None _) 0))
  (list-nth-or _ ars k 0))

(def-fns _ $ (many owner-set : (subterm many (List $ Nat) ids) (many (Nat) key) (many (IdMap $ Nat) owner) -> (many (IdMap $ Nat) r))
  (let-match many ids (Cons _ x rest) ((Nil _) owner))
  (tail $ owner-set rest key $ idmap-set _ x key owner))

(def-fns _ $ (many reg-insert : (many (Reg) r) (many (Nat) key) (many (SomeGroup) sg) (many (List $ Nat) ids) (many (List $ Nat) ars) (many (Acc) a) (many (Maybe $ Nat) parent) (many (Bool) top) -> (many (GInfo) info) (many (Reg) r2))
  (let-match many a (MkAcc us hs bs ins cs))
  (let ((many info)) $ MkGInfo ids ars us hs bs ins cs parent (Nil _) top)
  (let-match many r (MkReg infos codes owner aliases keys rets))
  (values info $ MkReg (idmap-set _ key info infos) (idmap-set _ key sg codes) (owner-set ids key owner) aliases (Cons _ key keys) rets))

(def-fns _ $ (many reg-parent : (many (Reg) r) (many (Nat) key) (many (Nat) parent) -> (many (Reg) r2))
  (let-match many (reg-get r key) (Some _ i) ((None _) r))
  (let-match many i (MkGInfo ids ars us hs bs ins cs p caps top))
  (match many p _ ((Some _ _) r) ((None _) (reg-put r key $ MkGInfo ids ars us hs bs ins cs (Some _ parent) caps top))))

(def-fns _ $ (many reg-alias : (many (Reg) r) (many (Nat) x) (many (Target) t) -> (many (Reg) r2))
  (match many r _ ((MkReg infos codes owner aliases keys rets) (MkReg infos codes owner (idmap-set _ x t aliases) keys rets))))

(def-fns _ $ (many group-key : (many (List $ Nat) gids) -> (many (Nat) k))
  (list-nth-or _ gids 0 0))

(def-fns _
  ((many reg-code : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) (many (Nat) key) (many (Bool) binding) (many (Acc) a) (many (Reg) r) -> (many (Acc) a2) (many (Reg) r2))
    (match many code _
      ((CVar _ x _) (values (acc-use x a) r))
      ((CConst _ x) (values (acc-const x a) r))
      ((CValues _ _ cs _) (tail $ reg-codes _ cs key binding a r))
      ((CApp _ _ f args _)
        (let ((many (Acc) a1) (many (Reg) r1))
          (match many f _
            ((CVar _ x _) (values (acc-head x (list-length _ args) a) r))
            (else (notail $ reg-code _ _ f key binding a r))))
        (tail $ reg-codes _ args key binding a1 r1))
      ((CLet _ _ _ ids _ rhs rest)
        (let ((many a1) (many r1)) $ notail $ reg-code _ _ rhs key binding (acc-bind binding ids a) r)
        (tail $ reg-code _ _ rest key binding a1 r1))
      ((CLetRec _ _ _ g rest)
        (let-match many g (MkGroup _ gids fns _))
        (let ((many key2)) $ group-key gids)
        (let ((many (GInfo) info) (many (Reg) r1))
          (match many (reg-get r key2) _
            ((Some _ i) (values i $ reg-parent r key2 key))
            ((None _)
              (let ((many a1) (many ids) (many ars) (many r2)) $ notail $ reg-fns _ _ fns key2 (BTrue) acc-empty r)
              (reg-insert r2 key2 (MkSomeGroup _ _ g) ids ars a1 (Some _ key) $ BFalse))))
        (tail $ reg-code _ _ rest key binding (acc-merge binding info a) r1))
      ((CMatch _ _ scrut shape branches dfl _)
        (let ((many a1) (many r1)) $ notail $ reg-code _ _ scrut key binding a r)
        (let ((many (Acc) a2) (many (Reg) r2)) $ match many shape _ ((ShHeld _ mcode _) (notail $ reg-code _ _ mcode key binding a1 r1)) (else (values a1 r1)))
        (let ((many a3) (many r3)) $ notail $ reg-branches _ _ branches key binding a2 r2)
        (match many dfl _ ((None _) (values a3 r3)) ((Some _ dd) (tail $ reg-code _ _ dd key binding a3 r3))))
      ((CCellAlloc _ _ slots) (tail $ reg-codes _ slots key binding a r))
      ((CCellWrite _ _ cell slots _)
        (let ((many a1) (many r1)) $ notail $ reg-code _ _ cell key binding a r)
        (tail $ reg-slots _ slots key binding a1 r1))
      ((CCellCopy _ _ cell slots)
        (let ((many a1) (many r1)) $ notail $ reg-code _ _ cell key binding a r)
        (tail $ reg-slots _ slots key binding a1 r1))
      ((CCellRead _ _ _ cell) (tail $ reg-code _ _ cell key binding a r))
      ((CWorldDo _ req) (tail $ reg-code _ _ req key binding a r))
      ((CPrim _ _ _ args) (tail $ reg-codes _ args key binding a r))
      (else (values a r))))

  ((many reg-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Nat) key) (many (Bool) binding) (many (Acc) a) (many (Reg) r) -> (many (Acc) a2) (many (Reg) r2))
    (let-match many cs (Cons _ c rest) ((Nil _) (values a r)))
    (let ((many a1) (many r1)) $ notail $ reg-code _ _ c key binding a r)
    (tail $ reg-codes _ rest key binding a1 r1))

  ((many reg-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Nat) key) (many (Bool) binding) (many (Acc) a) (many (Reg) r) -> (many (Acc) a2) (many (Reg) r2))
    (let-match many slots (Cons _ slot rest) ((Nil _) (values a r)))
    (let-match many slot (MkPair _ _ _ c))
    (let ((many a1) (many r1)) $ notail $ reg-code _ _ c key binding a r)
    (tail $ reg-slots _ rest key binding a1 r1))

  ((many reg-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) key) (many (Bool) binding) (many (Acc) a) (many (Reg) r) -> (many (Acc) a2) (many (Reg) r2))
    (let-match many bs (Cons _ b rest) ((Nil _) (values a r)))
    (let-match many b (MkBranch _ _ _ ids body))
    (let ((many a1) (many r1)) $ notail $ reg-code _ _ body key binding (acc-bind binding ids a) r)
    (tail $ reg-branches _ _ rest key binding a1 r1))

  ((many reg-fns : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Nat) key) (many (Bool) binding) (many (Acc) a) (many (Reg) r) -> (many (Acc) a2) (many (List $ Nat) ids) (many (List $ Nat) ars) (many (Reg) r2))
    (let-match many fns (Cons _ p rest) ((Nil _) (values a (Nil _) (Nil _) r)))
    (let-match many p (MkPair _ _ _ fn))
    (let ((many a1) (many ids) (many ars) (many r1)) $ notail $ reg-fns _ _ rest key binding a r)
    (let-match many fn (MkFunc _ _ _ _ fid params body impl _)
      ((MkAlias _ _ _ aid target) (values a1 ids ars $ reg-alias r1 aid $ target-of _ target)))
    (let ((many ab)) $ acc-bind binding params a1)
    (let ((many (Acc) a2) (many (Reg) r2)) $ match many impl _ ((None _) (notail $ reg-code _ _ body key binding ab r1)) ((Some _ _) (values ab r1)))
    (values a2 (Cons _ fid ids) (Cons _ (list-length _ params) ars) r2)))

(def-fns _ $ (many reg-block : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Reg) r) -> (many (Reg) r2))
  (let-match many b (BGroup _ _ _ g fr) (else r))
  (let-match many g (MkGroup _ gids fns _))
  (let ((many key)) $ group-key gids)
  (let-match many (reg-get r key) (None _) ((Some _ _) r))
  (let ((many (Bool) top)) $ match many fr _ ((FrNil _) (BTrue)) (else (BFalse)))
  (let ((many a1) (many ids) (many ars) (many r1)) $ reg-fns _ _ fns key (not top) acc-empty r)
  (let ((many _) (many r2)) $ reg-insert r1 key (MkSomeGroup _ _ g) ids ars a1 (None _) top)
  r2)

(def-fns _ $ (many caps-onto : (many (IdMap $ Unit) bs) (many (IdMap $ Unit) inner) (subterm many (List $ Key) ks) (many (List $ Key) raw) -> (many (List $ Key) r))
  (let-match many ks (Cons _ k rest) ((Nil _) raw))
  (let ((many (Bool) skip)) $ match many k _ ((KVal y) (idmap-mem _ y bs)) ((KFn y) (idmap-mem _ y inner)))
  (tail $ caps-onto bs inner rest $ match many skip (((List $ Key) _)) ((BTrue) raw) ((BFalse) (key-insert k raw))))

(def-fns _ $ (many cap-refer : (many (Reg) r) (many (Nat) key) (many (GInfo) info) (many (Nat) x0) (many (Bool) value) (many (List $ Key) raw) -> (many (List $ Key) r2))
  (let-match many info (MkGInfo _ _ _ _ bs inner _ _ _ _))
  (let-match many (idmap-mem _ x0 bs) (BFalse) ((BTrue) raw))
  (let-match many (reg-resolve r x0) (TgVar x) (else raw))
  (let-match many (reg-owner r x) (Some _ hk) ((None _) (key-insert (KVal x) raw)))
  (let-match many (idmap-mem _ x inner) (BFalse) ((BTrue) raw))
  (let ((many hcaps)) $ reg-caps r hk)
  (let ((many (List $ Key) raw1)) $ match many (and value $ not $ list-is-empty _ hcaps) _ ((BTrue) (key-insert (KFn x) raw)) ((BFalse) raw))
  (match many (nat-eqb hk key) _ ((BTrue) raw1) ((BFalse) (caps-onto bs inner hcaps raw1))))

(def-fns _ $ (many cap-uses : (many (Reg) r) (many (Nat) key) (many (GInfo) info) (subterm many (List $ Nat) xs) (many (List $ Key) raw) -> (many (List $ Key) r2))
  (let-match many xs (Cons _ x rest) ((Nil _) raw))
  (tail $ cap-uses r key info rest $ cap-refer r key info x (BTrue) raw))

(def-fns _ $ (many head-valued : (many (Reg) r) (many (Nat) x) (many (Nat) n) -> (many (Bool) b))
  (let-match many (reg-resolve r x) (TgVar y) (else (BFalse)))
  (match many (reg-owner r y) _ ((Some _ hk) (not $ nat-eqb n $ reg-arity r hk y)) ((None _) (BFalse))))

(def-fns _ $ (many cap-heads : (many (Reg) r) (many (Nat) key) (many (GInfo) info) (subterm many (List $ Pair (Nat) (Nat)) hs) (many (List $ Key) raw) -> (many (List $ Key) r2))
  (let-match many hs (Cons _ h rest) ((Nil _) raw))
  (let-match many h (MkPair _ _ x n))
  (tail $ cap-heads r key info rest $ cap-refer r key info x (head-valued r x n) raw))

(def-fns _ $ (many analyse-one : (many (Reg) r) (many (Nat) key) -> (many (List $ Key) caps))
  (let-match many (reg-get r key) (Some _ info) ((None _) (Nil _)))
  (let-match many info (MkGInfo ids _ us hs _ _ _ _ _ top))
  (let-match many top (BFalse) ((BTrue) (Nil _)))
  (let ((many raw)) $ cap-heads r key info hs $ cap-uses r key info us $ Nil _)
  (match many (keys-own ids raw) _ ((BTrue) (Nil _)) ((BFalse) raw)))

(def-fns _ $ (many reg-set-caps : (many (Reg) r) (many (Nat) key) (many (List $ Key) caps) -> (many (Reg) r2))
  (let-match many (reg-get r key) (Some _ i) ((None _) r))
  (let-match many i (MkGInfo ids ars us hs bs ins cs p _ top))
  (reg-put r key $ MkGInfo ids ars us hs bs ins cs p caps top))

(def-fns _ $ (many analyse-round : (many (Reg) r) (subterm many (List $ Nat) keys) (many (Bool) changed) -> (many (Reg) r2) (many (Bool) c2))
  (let-match many keys (Cons _ key rest) ((Nil _) (values r changed)))
  (let ((many caps)) $ analyse-one r key)
  (match many (keys-eqb caps $ reg-caps r key) _
    ((BTrue) (tail $ analyse-round r rest changed))
    ((BFalse) (tail $ analyse-round (reg-set-caps r key caps) rest $ BTrue))))

(def-fns _ $ (many analyse : (subterm many (Nat) fuel) (many (Reg) r) -> (many (Reg) r2))
  (let-match many fuel (Succ k) ((Zero) r))
  (let-match many r (MkReg _ _ _ _ keys _))
  (let ((many r1) (many changed)) $ analyse-round r keys $ BFalse)
  (match many changed _ ((BTrue) (tail $ analyse k r1)) ((BFalse) r1)))

(def-fns _ $ (many list-map-names : (many (Env) env) (subterm many (List $ Nat) ids) -> (many (List $ Rope) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (RStr $ str-cat (top-name env x) "_l") $ notail $ list-map-names env rest))

(def-fns _ $ (many list-map-obj : (many (Env) env) (subterm many (List $ Nat) ids) -> (many (List $ Rope) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (RStr $ str-cat3 "Obj.repr " (top-name env x) "_l") $ notail $ list-map-obj env rest))

(def-fns _ $ (many list-map-valued : (many (Env) env) (subterm many (List $ Nat) ids) -> (many (List $ Rope) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (Nil _)))
  (Cons _ (RStr $ str-cat (top-name env x) "_v") $ notail $ list-map-valued env rest))

(def-fns _ $ (many cap-slots : (many (Nat) i) (subterm many (List $ Key) ks) -> (many (List $ Rope) r))
  (let-match many ks (Cons _ _ rest) ((Nil _) (Nil _)))
  (Cons _ (RStr $ str-cat3 "c.(" (nat-str i) ")") $ notail $ cap-slots (Succ i) rest))

(def-adts $ (Ectx : -> Type)
  enum
  (many MkEctx : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (Nat) cur) (many (Bool) fac) (many (IdMap $ Rope) nm) -> (Ectx)))

(def-fns _ $ (many names-onto : (subterm many (List $ Nat) ids) (many (List $ Rope) rs) (many (IdMap $ Rope) nm) -> (many (IdMap $ Rope) r))
  (let-match many ids (Cons _ x rest) ((Nil _) nm))
  (let-match many rs (Cons _ r more) ((Nil _) nm))
  (tail $ names-onto rest more $ idmap-set _ x r nm))

(def-fns _ $ (many ex-bind : (many (Ectx) cx) (many (List $ Nat) ids) (many (List $ Rope) rs) -> (many (Ectx) r))
  (match many cx _ ((MkEctx env d reg cur fac nm) (MkEctx env d reg cur fac $ names-onto ids rs nm))))

(def-fns _ $ (many frame-name : (many (Ectx) cx) (many (Nat) x) -> (many (Rope) r))
  (let-match many cx (MkEctx env _ _ _ _ nm))
  (match many (idmap-get _ x nm) _ ((Hit _ _ _ r _) r) ((Miss _ _ _ _) (RStr $ top-name env x))))

(def-fns _ $ (many lifted-name : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (str-cat (top-name env x) "_l"))

(def-fns _ $ (many valued-name : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (str-cat (top-name env x) "_v"))

(def-fns _ $ (many maker-name : (many (Env) env) (many (Nat) key) -> (many (String) s))
  (str-cat "mk_" $ top-name env key))

(def-fns _ $ (many obj-repr : (many (String) s) -> (many (Rope) r))
  (RStr $ str-cat3 "(Obj.repr " s ")"))

(def-fns _ $ (many member-value : (many (Ectx) cx) (many (Nat) hk) (many (Nat) m) -> (many (Rope) r) (many (List $ Nat) w))
  (let-match many cx (MkEctx env _ reg cur fac _))
  (let-match many (and fac $ nat-eqb hk cur) (BFalse) ((BTrue) (values (obj-repr $ top-name env m) $ Nil _)))
  (match many (reg-closed reg hk) _
    ((BTrue) (values (obj-repr $ lifted-name env m) $ Nil _))
    ((BFalse) (values (RStr $ valued-name env m) $ Cons _ m $ Nil _))))

(def-fns _ $ (many key-value : (many (Ectx) cx) (many (Key) k) -> (many (Rope) r) (many (List $ Nat) w))
  (let-match many cx (MkEctx env _ reg _ _ _))
  (let-match many k (KFn m) ((KVal x) (values (frame-name cx x) $ Nil _)))
  (match many (reg-owner reg m) _ ((Some _ hk) (member-value cx hk m)) ((None _) (values (RStr $ valued-name env m) $ Nil _))))

(def-fns _ $ (many keys-values : (many (Ectx) cx) (subterm many (List $ Key) ks) -> (many (List $ Rope) rs) (many (List $ Nat) w))
  (let-match many ks (Cons _ k rest) ((Nil _) (values (Nil _) $ Nil _)))
  (let ((many r) (many w1)) $ key-value cx k)
  (let ((many rs) (many w2)) $ notail $ keys-values cx rest)
  (values (Cons _ r rs) $ rev-onto _ w1 w2))

(def-fns _ $ (many key-params : (many (Env) env) (subterm many (List $ Key) ks) -> (many (List $ Rope) rs))
  (let-match many ks (Cons _ k rest) ((Nil _) (Nil _)))
  (let ((many (String) name)) $ match many k _ ((KVal x) (top-name env x)) ((KFn m) (valued-name env m)))
  (Cons _ (RStr $ str-cat3 "(" name " : Obj.t)") $ notail $ key-params env rest))

(def-adts $ (ConstKind : -> Type)
  enum
  (many CkInline : (many (Rope) r) -> (ConstKind))
  (many CkCtor : (many (Ctor) c) (many (Nat) pos) -> (ConstKind))
  (many CkFn : (many (Nat) hk) (many (Nat) id) -> (ConstKind))
  (many CkData : (many (Nat) pos) -> (ConstKind)))

(def-fns _ $ (many plain-ctor : (many (Ctor) c) -> (many (Bool) b))
  (let-match many c (MkCtor _ _ _ _ _ ext _ _))
  (and (not $ ctor-newtype c) $ match many ext _ ((None _) (BTrue)) ((Some _ _) (BFalse))))

(def-fns _ $ (many block-kind : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Nat) pos) (many (Decls) d) (many (Reg) reg) -> (many (ConstKind) k))
  (match many b _
    ((BExt _ p) (match many p _ ((PNat n) (CkInline $ nat-literal n)) ((PHalf n) (CkInline $ nat-literal n)) (else (CkData pos))))
    ((BToken _) (CkInline $ RStr "(Obj.repr ())"))
    ((BCtorFn _ c) (CkCtor c pos))
    ((BMat _ adt) (CkInline $ matchable-rope adt d))
    ((BTag _ c fs) (match many (and (list-is-empty _ fs) $ plain-ctor c) _ ((BTrue) (CkInline $ build-rope d 0 c $ Nil _)) ((BFalse) (CkData pos))))
    ((BFn _ _ _ id)
      (let-match many (reg-owner reg id) (Some _ hk) ((None _) (CkData pos)))
      (match many (reg-closed reg hk) _ ((BTrue) (CkFn hk id)) ((BFalse) (CkData pos))))
    (else (CkData pos))))

(def-fns _ $ (many const-kind : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (Nat) x) -> (many (ConstKind) k))
  (let ((erased hs) (many hp) (many en) (many _)) $ env-store env)
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (CkInline $ RStr "(failwith \"unbound constant\")")))
  (let-match many info (MkEInfo _ _ _ s _ _ _ _))
  (let-match many s (SSettled _ v _) ((SHypothetical _) (CkInline $ RStr "(failwith \"a Hypothetical constant\")")))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (block-kind _ b (ref-pos Block _ v) d reg))

(def-fns _ $ (many data-name : (many (Nat) pos) -> (many (String) s))
  (str-cat "c" $ nat-str pos))

(def-fns _ $ (many const-value : (many (Ectx) cx) (many (Nat) x) -> (many (Rope) r) (many (List $ Nat) w))
  (let-match many cx (MkEctx env d reg _ _ _))
  (match many (const-kind env d reg x) _
    ((CkInline r) (values r $ Nil _))
    ((CkCtor _ pos) (values (RStr $ data-name pos) $ Nil _))
    ((CkFn hk id) (member-value cx hk id))
    ((CkData pos) (values (RStr $ data-name pos) $ Nil _))))

(def-fns _ $ (many var-value : (many (Ectx) cx) (many (Nat) x0) -> (many (Rope) r) (many (List $ Nat) w))
  (let-match many cx (MkEctx _ _ reg _ _ _))
  (let-match many (reg-resolve reg x0) (TgVar x)
    ((TgConst y) (const-value cx y))
    ((TgNone) (values (RStr "(failwith \"internal: an alias with no target\")") $ Nil _)))
  (match many (reg-owner reg x) _ ((Some _ hk) (member-value cx hk x)) ((None _) (values (frame-name cx x) $ Nil _))))

(def-adts $ (Head : -> Type)
  enum
  (many HCtor : (many (Ctor) c) -> (Head))
  (many HKnown : (many (Nat) hk) (many (Nat) id) -> (Head))
  (many HDyn : -> (Head)))

(def-fns _ $ (many const-head : (many (Ectx) cx) (many (Nat) x) -> (many (Head) h))
  (let-match many cx (MkEctx env d reg _ _ _))
  (match many (const-kind env d reg x) _ ((CkCtor c _) (HCtor c)) ((CkFn hk id) (HKnown hk id)) (else (HDyn))))

(def-fns _ $ (many head-of : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) f) (many (Ectx) cx) -> (many (Head) h))
  (let-match many cx (MkEctx _ _ reg _ _ _))
  (match many f _
    ((CVar _ x0 _)
      (let-match many (reg-resolve reg x0) (TgVar x) ((TgConst y) (const-head cx y)) ((TgNone) (HDyn)))
      (match many (reg-owner reg x) _ ((Some _ hk) (HKnown hk x)) ((None _) (HDyn))))
    ((CConst _ x) (const-head cx x))
    ((CValue _ v) (match many v _ ((BCtorFn _ c) (HCtor c)) (else (HDyn))))
    (else (HDyn))))

(def-fns _ $ (many known-call : (many (Ectx) cx) (many (Nat) depth) (many (Nat) hk) (many (Nat) id) (many (List $ Rope) ars) -> (many (Rope) r) (many (List $ Nat) w))
  (let-match many cx (MkEctx env d reg cur fac _))
  (let-match many (find-entry (decl-templates d) "call" "" id) (None _)
    ((Some _ t)
      (let-match many t (MkTemplate _ _ _ ps outcomes))
      (values (templated-build d ps outcomes depth ars) $ Nil _)))
  (let-match many (nat-eqb (list-length _ ars) $ reg-arity reg hk id) (BTrue)
    ((BFalse)
      (let ((many fr) (many w)) $ member-value cx hk id)
      (values (dyn-call fr ars) w)))
  (let-match many (and fac $ nat-eqb hk cur) (BFalse)
    ((BTrue) (values (rcat3 (RStr $ str-cat "(" $ top-name env id) (rcat (RStr " ") $ args-rope ars) $ RStr ")") $ Nil _)))
  (let ((many caps) (many w)) $ keys-values cx $ reg-caps reg hk)
  (values (rcat3 (RStr $ str-cat "(" $ lifted-name env id) (rcat (RStr " ") $ rjoin (rev-onto _ (list-rev _ caps) $ Cons _ (args-rope ars) $ Nil _) " ") $ RStr ")") w))

(def-fns _ $ (many split-wanted : (many (List $ Nat) ids) (subterm many (List $ Nat) w) (many (List $ Nat) here) (many (List $ Nat) others) -> (many (List $ Nat) h) (many (List $ Nat) o))
  (let-match many w (Cons _ x rest) ((Nil _) (values here others)))
  (match many (nat-list-mem ids x) _
    ((BTrue) (tail $ split-wanted ids rest (match many (nat-list-mem here x) (((List $ Nat) _)) ((BTrue) here) ((BFalse) (Cons _ x here))) others))
    ((BFalse) (tail $ split-wanted ids rest here $ Cons _ x others))))

(def-fns _ $ (many site-names : (many (Env) env) (subterm many (List $ Nat) rets) (many (List $ Nat) here) -> (many (List $ Rope) r))
  (let-match many rets (Cons _ m rest) ((Nil _) (Nil _)))
  (Cons _ (RStr $ match many (nat-list-mem here m) _ ((BTrue) (valued-name env m)) ((BFalse) "_")) $ notail $ site-names env rest here))

(def-fns _ $ (many tuple-of : (many (List $ Rope) rs) -> (many (Rope) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (RStr "()")))
  (match many rest _ ((Nil _) r) ((Cons _ _ _) (rcat3 (RStr "(") (commas rs) $ RStr ")"))))

(def-fns _ $ (many site-wrap : (many (Ectx) cx) (many (Nat) key) (many (Rope) body) (many (List $ Nat) w) -> (many (Rope) r) (many (List $ Nat) w2))
  (let-match many cx (MkEctx env _ reg _ _ _))
  (let ((many ids)) $ reg-members reg key)
  (let ((many here) (many others)) $ split-wanted ids w (Nil _) $ Nil _)
  (let-match many here (Cons _ _ _) ((Nil _) (values body w)))
  (let ((many caps) (many w2)) $ keys-values cx $ fac-caps ids $ reg-caps reg key)
  (let ((many pat)) $ tuple-of $ site-names env (reg-ret reg key) here)
  (values (rcat5 (RStr "(let ") pat (RStr " = ") (rcat3 (RStr $ maker-name env key) (RStr " ") $ args-rope caps) (rcat3 (RStr " in ") body $ RStr ")")) $ rev-onto _ w2 others))

(def-fns _ $ (many fusing : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (Code ctx many-one) f)
    (many (Code (Cons (List (Nat)) ids ctx) many-one) scrut) (many (Shape (Cons (List (Nat)) ids ctx)) shape) (many (Ectx) cx) ->
    (many (Maybe $ Template) r))
  (let-match many cx (MkEctx _ d _ _ _ _))
  (let-match many ids (Cons _ x more) ((Nil _) (None _)))
  (let-match many more (Nil _) ((Cons _ _ _) (None _)))
  (let-match many scrut (CVar _ y _) (else (None _)))
  (let-match many shape (ShKnown _ adt) (else (None _)))
  (let-match many (head-of _ f cx) (HKnown _ id) (else (None _)))
  (let-match many (find-entry (decl-templates d) "call" "" id) (Some _ t) ((None _) (None _)))
  (let-match many t (MkTemplate _ _ _ _ outcomes))
  (match many (and (nat-eqb x y) $ and (not $ list-is-empty _ outcomes) $ nat-list-eq outcomes $ adt-shape adt) _
    ((BTrue) (Some _ t))
    ((BFalse) (None _))))

(def-fns _
  ((many emit-code : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ms) (subterm many (Code ctx ms) code) (many (Ectx) cx) (many (Nat) depth) -> (many (Rope) r) (many (List $ Nat) w))
    (let-match many cx (MkEctx env d _ _ _ _))
    (match many code _
      ((CVar _ x _) (var-value cx x))
      ((CConst _ x) (const-value cx x))
      ((CValue _ v) (values (block-rope _ v env d) $ Nil _))
      ((CErased _ _) (values (RStr "(Obj.repr ())") $ Nil _))
      ((CValues _ _ cs _)
        (let ((many rs) (many w)) $ notail $ emit-codes _ cs cx depth)
        (values (values-rope depth rs) w))
      ((CApp _ _ f args _)
        (let ((many ars) (many w1)) $ notail $ emit-codes _ args cx depth)
        (match many (head-of _ f cx) _
          ((HCtor c) (values (build-rope d depth c ars) w1))
          ((HKnown hk id)
            (let ((many r) (many w2)) $ known-call cx depth hk id ars)
            (values r $ rev-onto _ w2 w1))
          ((HDyn)
            (let ((many fr) (many w2)) $ notail $ emit-code _ _ f cx depth)
            (values (dyn-call fr ars) $ rev-onto _ w2 w1))))
      ((CLet _ _ _ ids _ rhs rest)
        (let ((many rr) (many w1)) $ notail $ emit-code _ _ rhs cx depth)
        (let ((many xs)) $ names-of-ids ids env)
        (let ((many (Maybe $ Template) fz))
          (match many rhs _
            ((CApp _ _ f _ _) (match many rest _ ((CMatch _ _ scrut shape _ _ _) (fusing _ ids f scrut shape cx)) (else (None _))))
            (else (None _))))
        (let ((many cxr)) $ ex-bind cx ids xs)
        (let-match many fz (Some _ t)
          ((None _)
            (let ((many br) (many w2)) $ notail $ emit-code _ _ rest cxr $ Succ depth)
            (values (let-rope xs rr br) $ rev-onto _ w2 w1)))
        (let-match many t (MkTemplate _ _ _ ps outcomes))
        (let-match many rhs (CApp _ _ _ args _) (else (values rr w1)))
        (let-match many rest (CMatch _ _ _ _ branches dfl live) (else (values rr w1)))
        (let ((many ars) (many w2)) $ notail $ emit-codes _ args cx depth)
        (let ((many arms) (many w3)) $ notail $ emit-arms _ _ branches cxr $ Succ depth)
        (let ((many (Maybe $ Rope) dr) (many (List $ Nat) w4))
          (match many dfl _
            ((None _) (values (None _) $ Nil _))
            ((Some _ dd)
              (let ((many r4) (many w5)) $ notail $ emit-code _ _ dd cxr $ Succ $ Succ depth)
              (values (Some _ r4) w5))))
        (values (templated-fused d ps depth ars outcomes live (list-nth-or _ xs 0 $ RStr "_") arms dr) $ rev-onto _ w1 $ rev-onto _ w2 $ rev-onto _ w3 w4))
      ((CLetRec _ _ _ g rest)
        (let-match many g (MkGroup _ gids _ _))
        (let ((many br) (many w1)) $ notail $ emit-code _ _ rest cx $ Succ depth)
        (site-wrap cx (group-key gids) br w1))
      ((CMatch _ _ scrut shape branches dfl live)
        (let ((many sr) (many w1)) $ notail $ emit-code _ _ scrut cx depth)
        (let ((many (Maybe $ Rope) dr) (many (List $ Nat) w2))
          (match many dfl _
            ((None _) (values (None _) $ Nil _))
            ((Some _ dd)
              (let ((many r4) (many w5)) $ notail $ emit-code _ _ dd cx $ Succ depth)
              (values (Some _ r4) w5))))
        (let ((many arms) (many w3)) $ notail $ emit-arms _ _ branches cx depth)
        (let ((many w4)) $ rev-onto _ w1 $ rev-onto _ w2 w3)
        (let-match many shape (ShHeld _ mcode adt)
          ((ShKnown _ adt) (values (dispatch-rope d depth adt live sr arms dr) w4))
          ((ShNone _) (values (default-rope dr) w4)))
        (let ((many mr) (many w5)) $ notail $ emit-code _ _ mcode cx depth)
        (values (dispatch-rope d depth adt live (rcat5 (RStr "((Obj.obj ") mr (RStr " : Obj.t -> Obj.t) ") sr $ RStr ")") arms dr) $ rev-onto _ w5 w4))
      ((CCellAlloc _ ctor slots)
        (let ((many rs) (many w)) $ notail $ emit-codes _ slots cx depth)
        (values (plain-build d ctor rs) w))
      ((CCellWrite _ k2 cell slots imms)
        (let ((many indices) (many args) (many w1)) $ notail $ emit-slots _ slots cx depth)
        (let ((many cr) (many w2)) $ notail $ emit-code _ _ cell cx depth)
        (values (cell-write-rope d k2 cr indices args imms depth) $ rev-onto _ w2 w1))
      ((CCellCopy _ k2 cell slots)
        (let ((many indices) (many args) (many w1)) $ notail $ emit-slots _ slots cx depth)
        (let ((many cr) (many w2)) $ notail $ emit-code _ _ cell cx depth)
        (values (field-copy-rope d k2 cr indices args depth) $ rev-onto _ w2 w1))
      ((CCellRead _ k2 index cell)
        (let ((many cr) (many w)) $ notail $ emit-code _ _ cell cx depth)
        (values (field-read-rope d k2 cr index $ str-cat3 "cell" (nat-str depth) "_r") w))
      ((CWorldDo _ req)
        (let ((many rr) (many w)) $ notail $ emit-code _ _ req cx depth)
        (values (rcat3 (RStr "(driver.Driver_core.perform world ") rr $ RStr ")") w))
      ((CPrim _ _ p args)
        (let ((many hs) (many w)) $ notail $ emit-codes _ args cx depth)
        (values (prim-rope env p hs) w))
      ((CAbsurd _ _) (values (RStr "(absurd ())") $ Nil _))
      ((CError _ _ m) (values (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")") $ Nil _))))

  ((many emit-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Ectx) cx) (many (Nat) depth) -> (many (List $ Rope) rs) (many (List $ Nat) w))
    (let-match many cs (Cons _ c rest) ((Nil _) (values (Nil _) $ Nil _)))
    (let ((many r) (many w1)) $ notail $ emit-code _ _ c cx depth)
    (let ((many rs) (many w2)) $ notail $ emit-codes _ rest cx depth)
    (values (Cons _ r rs) $ rev-onto _ w1 w2))

  ((many emit-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Ectx) cx) (many (Nat) depth) -> (many (List $ Nat) indices) (many (List $ Rope) args) (many (List $ Nat) w))
    (let-match many slots (Cons _ slot rest) ((Nil _) (values (Nil _) (Nil _) $ Nil _)))
    (let-match many slot (MkPair _ _ index c))
    (let ((many indices) (many args) (many w1)) $ notail $ emit-slots _ rest cx depth)
    (let ((many r) (many w2)) $ notail $ emit-code _ _ c cx depth)
    (values (Cons _ index indices) (Cons _ r args) $ rev-onto _ w2 w1))

  ((many emit-arms : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Ectx) cx) (many (Nat) depth) -> (many (List $ Arm) r) (many (List $ Nat) w))
    (let-match many cx (MkEctx env _ _ _ _ _))
    (let-match many bs (Cons _ b rest) ((Nil _) (values (Nil _) $ Nil _)))
    (let-match many b (MkBranch _ _ disc ids body))
    (let ((many xs)) $ names-of-ids ids env)
    (let ((many br) (many w1)) $ notail $ emit-code _ _ body (ex-bind cx ids xs) $ Succ depth)
    (let ((many arms) (many w2)) $ notail $ emit-arms _ _ rest cx depth)
    (values (Cons _ (MkArm disc xs br) arms) $ rev-onto _ w1 w2)))

(def-fns _ $ (many fn-body : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (many (Func gids ctx) fn) (many (Ectx) cx) -> (many (Rope) r))
  (let-match many cx (MkEctx env d _ _ _ _))
  (let-match many fn (MkFunc _ _ _ _ _ params body impl _) ((MkAlias _ _ _ _ _) (REmpty)))
  (match many impl _
    ((Some _ im)
      (let-match many im (MkImpl se _))
      (match many se _ ((MkSomeExtern _ e) (ffi-call (ext-name _ e) (names-of-ids params env) env d))))
    ((None _) (let ((many r) (many _)) $ emit-code _ _ body (ex-bind cx params $ names-of-ids params env) 0) r)))

(def-fns _ $ (many fn-defs : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Ectx) cx) (many (List $ Rope) caps) (many (Bool) local) -> (many (List $ Rope) r))
  (let-match many fns (Cons _ p rest) ((Nil _) (Nil _)))
  (let-match many p (MkPair _ _ _ fn))
  (let ((many more)) $ notail $ fn-defs _ _ rest cx caps local)
  (let-match many fn (MkFunc _ _ _ _ fid params _ _ _) ((MkAlias _ _ _ _ _) more))
  (let-match many cx (MkEctx env _ _ _ _ _))
  (let ((many (String) name)) $ match many local _ ((BTrue) (top-name env fid)) ((BFalse) (lifted-name env fid)))
  (let ((many ps)) $ rjoin (rev-onto _ (list-rev _ caps) $ Cons _ (params-rope $ names-of-ids params env) $ Nil _) " ")
  (Cons _ (rcat5 (RStr name) (RStr " ") ps (RStr " : Obj.t = ") $ fn-body _ _ fn cx) more))

(def-fns _ $ (many factory-ret : (many (Env) env) (subterm many (List $ Nat) rets) -> (many (List $ Rope) r))
  (let-match many rets (Cons _ m rest) ((Nil _) (Nil _)))
  (Cons _ (obj-repr $ top-name env m) $ notail $ factory-ret env rest))

(def-fns _ $ (many group-defs : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (Nat) key) -> (many (List $ Rope) defs) (many (List $ Rope) names))
  (let-match many (reg-code-of reg key) (Some _ sg) ((None _) (values (Nil _) $ Nil _)))
  (let-match many sg (MkSomeGroup _ _ g))
  (let-match many g (MkGroup _ _ fns _))
  (let ((many ids)) $ reg-members reg key)
  (let ((many caps)) $ reg-caps reg key)
  (let ((many lifted)) $ fn-defs _ _ fns (MkEctx env d reg key (BFalse) $ MEmpty _) (key-params env caps) $ BFalse)
  (let ((many lnames)) $ list-map-names env ids)
  (let ((many rets)) $ reg-ret reg key)
  (let-match many (and (not $ list-is-empty _ caps) $ not $ list-is-empty _ rets) (BTrue) ((BFalse) (values lifted lnames)))
  (let ((many (List $ Rope) fps)) $ match many (fac-caps ids caps) _ ((Nil _) (Cons _ (RStr "()") $ Nil _)) ((Cons _ k ks) (key-params env $ Cons _ k ks)))
  (let ((many locals)) $ fn-defs _ _ fns (MkEctx env d reg key (BTrue) $ MEmpty _) (Nil _) $ BTrue)
  (let ((many fac)) $ rcat5 (RStr $ maker-name env key) (RStr " ") (rjoin fps " ") (rcat3 (RStr " =\n  let rec ") (rjoin locals "\n  and ") $ RStr " in\n  ") $ tuple-of $ factory-ret env rets)
  (values (Cons _ fac lifted) $ Cons _ (RStr $ maker-name env key) lnames))

(def-fns _ $ (many frame-ref : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (subterm many (Frames (Ref Block a) ctx) fr) (many (Nat) x) -> (many (Maybe $ Ref Block a) r))
  (match many fr _
    ((FrNil _) (None _))
    ((FrVals _ _ f vs _ rest)
      (let-match many (nat-index f x 0) (Some _ i) ((None _) (tail $ frame-ref _ _ rest x)))
      (match many (list-nth _ vs i) _ ((NthHit _ _ _ v _) (Some _ v)) ((NthMiss _ _ _ _) (None _))))
    ((FrGroup _ _ gids g _ rest) (match many (nat-list-mem gids x) _ ((BTrue) (Some _ g)) ((BFalse) (tail $ frame-ref _ _ rest x))))))

(def-fns _ $ (many caps-refs : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (Frames (Ref Block a) ctx) fr) (subterm many (List $ Key) ks) (many (List $ Ref Block a) acc) -> (many (List $ Ref Block a) r))
  (let-match many ks (Cons _ k rest) ((Nil _) acc))
  (tail $ caps-refs _ _ fr rest $ match many (frame-ref _ _ fr $ key-id k) (((List $ Ref Block a) _)) ((Some _ v) (Cons _ v acc)) ((None _) acc)))

(def-fns _ $ (many group-refs : (erased (Hist Block) a) (erased (List $ Nat) gids0) (erased (List $ List $ Nat) ctx) (many (Group gids0 ctx) g) (many (Frames (Ref Block a) ctx) fr) (many (Reg) reg) -> (many (List $ Ref Block a) r))
  (let-match many g (MkGroup _ gids _ _))
  (let ((many key)) $ group-key gids)
  (caps-refs _ _ fr (fac-caps (reg-members reg key) $ reg-caps reg key) $ Nil _))

(def-fns _ $ (many want-add : (many (Nat) m) (many (Reg) r) (many (IdMap $ List $ Nat) want) -> (many (IdMap $ List $ Nat) w2))
  (let-match many (reg-resolve r m) (TgVar y) (else want))
  (let-match many (reg-owner r y) (Some _ hk) ((None _) want))
  (let ((many (List $ Nat) cur)) $ match many (idmap-get _ hk want) _ ((Hit _ _ _ l _) l) ((Miss _ _ _ _) (Nil _)))
  (idmap-set _ hk (Cons _ y cur) want))

(def-fns _ $ (many want-uses : (many (Reg) r) (subterm many (List $ Nat) xs) (many (IdMap $ List $ Nat) want) -> (many (IdMap $ List $ Nat) w2))
  (let-match many xs (Cons _ x rest) ((Nil _) want))
  (tail $ want-uses r rest $ want-add x r want))

(def-fns _ $ (many want-heads : (many (Reg) r) (subterm many (List $ Pair (Nat) (Nat)) hs) (many (IdMap $ List $ Nat) want) -> (many (IdMap $ List $ Nat) w2))
  (let-match many hs (Cons _ h rest) ((Nil _) want))
  (let-match many h (MkPair _ _ x n))
  (tail $ want-heads r rest $ match many (head-valued r x n) (((IdMap $ List $ Nat) _)) ((BTrue) (want-add x r want)) ((BFalse) want)))

(def-fns _ $ (many want-caps : (many (Reg) r) (subterm many (List $ Key) ks) (many (IdMap $ List $ Nat) want) -> (many (IdMap $ List $ Nat) w2))
  (let-match many ks (Cons _ k rest) ((Nil _) want))
  (tail $ want-caps r rest $ match many k (((IdMap $ List $ Nat) _)) ((KFn m) (want-add m r want)) ((KVal _) want)))

(def-fns _ $ (many want-pass : (many (Reg) r) (subterm many (List $ Nat) keys) (many (IdMap $ List $ Nat) want) -> (many (IdMap $ List $ Nat) w2))
  (let-match many keys (Cons _ key rest) ((Nil _) want))
  (let-match many (reg-get r key) (Some _ info) ((None _) (tail $ want-pass r rest want)))
  (let-match many info (MkGInfo _ _ us hs _ _ _ _ caps _))
  (tail $ want-pass r rest $ want-caps r caps $ want-heads r hs $ want-uses r us want))

(def-fns _ $ (many held-pass : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (Reg) r) (many (IdMap $ List $ Nat) held) -> (many (IdMap $ List $ Nat) out))
  (let-match many refs (Cons _ v rest) ((Nil _) held))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (tail $ held-pass _ hp rest r $ match many b (((IdMap $ List $ Nat) _)) ((BFn _ _ _ id) (want-add id r held)) (else held)))

(def-fns _ $ (many map-list : (many (IdMap $ List $ Nat) m) (many (Nat) k) -> (many (List $ Nat) l))
  (match many (idmap-get _ k m) _ ((Hit _ _ _ l _) l) ((Miss _ _ _ _) (Nil _))))

(def-fns _ $ (many rets-of : (subterm many (List $ Nat) ids) (many (List $ Nat) held) (many (List $ Nat) want) (many (Bool) closed) -> (many (List $ Nat) r))
  (let-match many ids (Cons _ m rest) ((Nil _) (Nil _)))
  (let ((many more)) $ notail $ rets-of rest held want closed)
  (match many (or (nat-list-mem held m) $ and (not closed) $ nat-list-mem want m) _ ((BTrue) (Cons _ m more)) ((BFalse) more)))

(def-fns _ $ (many set-rets : (many (Reg) r) (subterm many (List $ Nat) keys) (many (IdMap $ List $ Nat) held) (many (IdMap $ List $ Nat) want) -> (many (Reg) r2))
  (let-match many keys (Cons _ key rest) ((Nil _) r))
  (let ((many ids)) $ rets-of (reg-members r key) (map-list held key) (map-list want key) $ reg-closed r key)
  (let-match many r (MkReg infos codes owner aliases ks rets))
  (tail $ set-rets (MkReg infos codes owner aliases ks $ idmap-set _ key ids rets) rest held want))

(def-fns _ $ (many owners-of : (many (Reg) r) (subterm many (List $ Nat) xs) (many (List $ Nat) acc) -> (many (List $ Nat) out))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (let ((many (List $ Nat) acc1)) $ match many (reg-resolve r x) _ ((TgVar y) (match many (reg-owner r y) _ ((Some _ k) (Cons _ k acc)) ((None _) acc))) (else acc))
  (tail $ owners-of r rest acc1))

(def-fns _ $ (many head-ids : (subterm many (List $ Pair (Nat) (Nat)) hs) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many hs (Cons _ h rest) ((Nil _) acc))
  (let-match many h (MkPair _ _ x _))
  (tail $ head-ids rest $ Cons _ x acc))

(def-fns _ $ (many reach : (subterm many (Nat) fuel) (many (Reg) r) (many (List $ Nat) work) (many (IdMap $ Unit) seen) -> (many (IdMap $ Unit) out))
  (let-match many fuel (Succ k) ((Zero) seen))
  (let-match many work (Cons _ key rest) ((Nil _) seen))
  (let-match many (idmap-mem _ key seen) (BFalse) ((BTrue) (tail $ reach k r rest seen)))
  (let-match many (reg-get r key) (Some _ info) ((None _) (tail $ reach k r rest seen)))
  (let-match many info (MkGInfo _ _ us hs _ inner _ _ _ _))
  (let ((many more)) $ owners-of r us $ owners-of r (head-ids hs $ Nil _) $ owners-of r (pair-keys _ (idmap-pairs _ inner 1 0 $ Nil _) $ Nil _) rest)
  (tail $ reach k r more $ idmap-set _ key (MkUnit) seen))

(def-fns _ $ (many instance-keys : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many refs (Cons _ v rest) ((Nil _) acc))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (tail $ instance-keys _ hp rest $ match many b (((List $ Nat) _)) ((BGroup _ _ _ g _) (match many g _ ((MkGroup _ gids _ _) (Cons _ (group-key gids) acc)))) (else acc)))

(def-fns _ $ (many reached-consts : (many (Reg) r) (subterm many (List $ Nat) keys) (many (List $ Nat) acc) -> (many (List $ Nat) out))
  (let-match many keys (Cons _ key rest) ((Nil _) acc))
  (let-match many (reg-get r key) (Some _ info) ((None _) (tail $ reached-consts r rest acc)))
  (let-match many info (MkGInfo _ _ _ _ _ _ cs _ _ _))
  (tail $ reached-consts r rest $ rev-onto _ cs acc))

(def-fns _ $ (many collect-reached : (many (Reg) r) (subterm many (List $ Nat) keys) (many (Env) env) (many (Decls) d) -> (many (Decls) d2))
  (let-match many keys (Cons _ key rest) ((Nil _) d))
  (let-match many (reg-code-of r key) (Some _ sg) ((None _) (tail $ collect-reached r rest env d)))
  (let-match many sg (MkSomeGroup _ _ g))
  (let-match many g (MkGroup _ _ fns _))
  (tail $ collect-reached r rest env $ collect-group _ _ fns env d))

(def-fns _ $ (many root-of : (subterm many (Nat) fuel) (many (Reg) r) (many (IdMap $ Unit) reached) (many (Nat) key) -> (many (Nat) root))
  (let-match many (reg-get r key) (Some _ i) ((None _) key))
  (let-match many i (MkGInfo _ _ _ _ _ _ _ p _ _))
  (let-match many p (Some _ pk) ((None _) key))
  (let-match many (idmap-mem _ pk reached) (BTrue) ((BFalse) key))
  (match many fuel _ ((Zero) key) ((Succ k) (tail $ root-of k r reached pk))))

(def-fns _ $ (many tree-map : (many (Reg) r) (many (IdMap $ Unit) reached) (subterm many (List $ Nat) keys) (many (IdMap $ List $ Nat) trees) (many (IdMap $ Nat) roots) -> (many (IdMap $ List $ Nat) t) (many (IdMap $ Nat) rs))
  (let-match many keys (Cons _ key rest) ((Nil _) (values trees roots)))
  (let ((many root)) $ root-of 100000 r reached key)
  (tail $ tree-map r reached rest (idmap-set _ root (Cons _ key $ map-list trees root) trees) $ idmap-set _ key root roots))

(def-adts $ (Kind : -> Type)
  enum
  (many CNone : -> (Kind))
  (many CBlank : (many (Nat) tag) (many (Nat) size) -> (Kind))
  (many CLeaf : -> (Kind))
  (many CInst : (many (Nat) key) -> (Kind))
  (many CExpr : -> (Kind)))

(def-fns _ $ (many small-nat : (many (Nat) n) -> (many (Bool) b))
  (nat-lt n 4611686018427387904))

(def-fns _ $ (many count-filled : (subterm many (List $ Nat) s) (many (Nat) i) (many (Bool) zeros) (many (Nat) acc) -> (many (Nat) n))
  (let-match many s (Cons _ a rest) ((Nil _) acc))
  (let-match many i (Succ k) ((Zero) acc))
  (let ((many (Bool) z)) $ nat-eqb a 0)
  (let ((many (Bool) hit)) $ match many zeros _ ((BTrue) z) ((BFalse) (not z)))
  (tail $ count-filled rest k zeros $ match many hit (((Nat) _)) ((BTrue) (Succ acc)) ((BFalse) acc)))

(def-fns _ $ (many nullary-word : (many (Ctor) c) -> (many (Nat) n))
  (match many (ctor-tagged c) _ ((BTrue) (count-filled (ctor-shape c) (ctor-index c) (BTrue) 0)) ((BFalse) 0)))

(def-fns _ $ (many cell-of : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Reg) reg) -> (many (Kind) c))
  (match many b _
    ((BTag _ c fs)
      (let ((many n)) $ list-length _ fs)
      (let-match many (plain-ctor c) (BTrue) ((BFalse) (CExpr)))
      (let-match many n (Succ _) ((Zero) (CNone)))
      (let-match many (ctor-tagged c) (BTrue) ((BFalse) (CBlank 0 n)))
      (let ((many s)) $ ctor-shape c)
      (match many (shape-wide s) _ ((BTrue) (CBlank 0 $ Succ $ widest s)) ((BFalse) (CBlank (count-filled s (ctor-index c) (BFalse) 0) n))))
    ((BTup _ fs)
      (let-match many fs (Cons _ _ more) ((Nil _) (CNone)))
      (match many more _ ((Nil _) (CNone)) ((Cons _ _ _) (CBlank 0 $ list-length _ fs))))
    ((BArray _ n _) (CBlank 0 n))
    ((BSlots _ _ _ _) (CLeaf))
    ((BExt _ p) (match many p _ ((PNat n) (match many (small-nat n) _ ((BTrue) (CNone)) ((BFalse) (CLeaf)))) ((PHalf n) (match many (small-nat n) _ ((BTrue) (CNone)) ((BFalse) (CLeaf)))) ((PHandle _ _ _ _) (CBlank 0 4)) ((PRaw _ _) (CExpr)) (else (CLeaf))))
    ((BCtorFn _ _) (CLeaf))
    ((BMat _ _) (CLeaf))
    ((BGroup _ _ _ g _)
      (let-match many g (MkGroup _ gids _ _))
      (let ((many key)) $ group-key gids)
      (match many (reg-ret reg key) _ ((Nil _) (CNone)) (else (CInst key))))
    ((BError _ _) (CExpr))
    (else (CNone))))

(def-fns _ $ (many assign-pass : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (Reg) reg) (many (Bool) third) (many (Nat) next) (many (IdMap $ Nat) slots) -> (many (Nat) n) (many (IdMap $ Nat) s))
  (let-match many refs (Cons _ v rest) ((Nil _) (values next slots)))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (let ((many (Nat) size))
    (match many (cell-of _ b reg) _
      ((CBlank _ _) (match many third _ ((BTrue) 0) ((BFalse) 1)))
      ((CLeaf) (match many third _ ((BTrue) 0) ((BFalse) 1)))
      ((CInst key) (match many third _ ((BTrue) (list-length _ $ reg-ret reg key)) ((BFalse) 0)))
      ((CExpr) (match many third _ ((BTrue) 1) ((BFalse) 0)))
      ((CNone) 0)))
  (let ((many (IdMap $ Nat) s2)) $ match many size _ ((Zero) slots) (else (idmap-set _ (ref-pos Block _ v) next slots)))
  (tail $ assign-pass _ hp rest reg third (nat-add next size) s2))

(def-fns _ $ (many slot-tok : (many (IdMap $ Nat) slots) (many (Nat) pos) -> (many (String) t))
  (match many (idmap-get _ pos slots) _ ((Hit _ _ _ k _) (nat-str k)) ((Miss _ _ _ _) "x")))

(def-fns _ $ (many pos-tok : (many (IdMap $ String) toks) (many (Nat) pos) -> (many (String) t))
  (match many (idmap-get _ pos toks) _ ((Hit _ _ _ t _) t) ((Miss _ _ _ _) "x")))

(def-fns _ $ (many member-tok : (many (Reg) reg) (many (IdMap $ Nat) slots) (many (Nat) gpos) (many (Nat) id) -> (many (String) t))
  (let-match many (reg-owner reg id) (Some _ hk) ((None _) "x"))
  (let-match many (nat-index (reg-ret reg hk) id 0) (Some _ i) ((None _) "x"))
  (match many (idmap-get _ gpos slots) _ ((Hit _ _ _ k _) (nat-str $ nat-add k i)) ((Miss _ _ _ _) "x")))

(def-fns _ $ (many tok-pass : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (Reg) reg) (many (IdMap $ Nat) slots) (many (IdMap $ String) toks) -> (many (IdMap $ String) t))
  (let-match many refs (Cons _ v rest) ((Nil _) toks))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (let ((many pos)) $ ref-pos Block _ v)
  (let ((many here)) $ slot-tok slots pos)
  (let ((many (String) t))
    (match many b _
      ((BExt _ p) (match many p _ ((PNat n) (match many (small-nat n) _ ((BTrue) (str-cat "i" $ nat-str n)) ((BFalse) here))) ((PHalf n) (match many (small-nat n) _ ((BTrue) (str-cat "i" $ nat-str n)) ((BFalse) here))) (else here)))
      ((BToken _) "i0")
      ((BTag _ c fs) (match many (and (list-is-empty _ fs) $ plain-ctor c) _ ((BTrue) (str-cat "i" $ nat-str $ nullary-word c)) ((BFalse) here)))
      ((BTup _ fs)
        (let-match many fs (Cons _ x more) ((Nil _) "i0"))
        (match many more _ ((Nil _) (pos-tok toks $ ref-pos Block _ x)) ((Cons _ _ _) here)))
      ((BFn _ g _ id) (member-tok reg slots (ref-pos Block _ g) id))
      (else here)))
  (tail $ tok-pass _ hp rest reg slots $ idmap-set _ pos t toks))

(def-fns _ $ (many toks-of : (erased (Hist Block) a) (many (IdMap $ String) toks) (subterm many (List $ Ref Block a) vs) -> (many (List $ String) r))
  (let-match many vs (Cons _ v rest) ((Nil _) (Nil _)))
  (Cons _ (pos-tok toks $ ref-pos Block _ v) $ notail $ toks-of _ toks rest))

(def-fns _ $ (many tok-expr : (many (String) t) -> (many (Rope) r))
  (let-match many t (SCons c rest) ((SNil) (RStr "(Obj.repr ())")))
  (match many (char-eqb c #\i) _
    ((BTrue) (RStr $ str-cat3 "(Obj.repr (" rest "))"))
    ((BFalse) (RStr $ str-cat3 "(rt_get " t ")"))))

(def-fns _ $ (many tok-exprs : (subterm many (List $ String) ts) -> (many (List $ Rope) r))
  (let-match many ts (Cons _ t rest) ((Nil _) (Nil _)))
  (Cons _ (tok-expr t) $ notail $ tok-exprs rest))

(def-fns _ $ (many toks-rope : (subterm many (List $ String) ts) -> (many (Rope) r))
  (let-match many ts (Cons _ t rest) ((Nil _) (REmpty)))
  (rcat3 (RStr t) (RStr " ") $ notail $ toks-rope rest))

(def-fns _ $ (many settled-pos : (many (Env) env) (many (Nat) x) -> (many (Maybe $ Nat) p))
  (let ((erased _) (many _) (many en) (many _)) $ env-store env)
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (None _)))
  (let-match many info (MkEInfo _ _ _ s _ _ _ _))
  (match many s _ ((SSettled _ v _) (Some _ $ ref-pos Block _ v)) ((SHypothetical _) (None _))))

(def-fns _ $ (many settled-tok : (many (Env) env) (many (IdMap $ String) toks) (many (Nat) x) -> (many (String) t))
  (match many (settled-pos env x) _ ((Some _ p) (pos-tok toks p)) ((None _) "i0")))

(def-fns _ $ (many text-op : (many (String) op) (many (String) s) -> (many (Rope) r))
  (let ((many n) (erased _)) $ str-length s)
  (rcat5 (RStr op) (nat-rope n) (RStr ":") (RStr s) $ RStr " "))

(def-fns _ $ (many fill-op : (many (Nat) slot) (many (List $ String) ts) -> (many (Rope) r))
  (rcat5 (RStr "f") (nat-rope slot) (RStr " ") (nat-rope $ list-length _ ts) $ rcat (RStr " ") $ toks-rope ts))

(def-adts $ (P2 : -> Type)
  enum
  (many MkP2 : (many (Rope) allocs) (many (Rope) fills) (many (List $ Rope) globals) (many (Nat) count) (many (IdMap $ Nat) ctors) -> (P2)))

(def-fns _ $ (many p2-alloc : (many (P2) p) (many (Rope) a) (many (Rope) f) -> (many (P2) r))
  (match many p _ ((MkP2 al fi gs n cs) (MkP2 (rcat al a) (rcat fi f) gs n cs))))

(def-fns _ $ (many p2-global : (many (P2) p) (many (Rope) g) -> (many (P2) r))
  (match many p _ ((MkP2 al fi gs n cs) (MkP2 (rcat3 al (RStr "g") $ rcat (nat-rope n) $ RStr " ") fi (Cons _ g gs) (Succ n) cs))))

(def-fns _ $ (many p2-ctor : (many (P2) p) (many (Decls) d) (many (Ctor) c) -> (many (P2) r))
  (let-match many p (MkP2 al fi gs n cs))
  (match many (idmap-get _ (ctor-id c) cs) _
    ((Hit _ _ _ i _) (MkP2 (rcat3 al (RStr "g") $ rcat (nat-rope i) $ RStr " ") fi gs n cs))
    ((Miss _ _ _ _) (MkP2 (rcat3 al (RStr "g") $ rcat (nat-rope n) $ RStr " ") fi (Cons _ (ctor-fn-rope d c) gs) (Succ n) $ idmap-set _ (ctor-id c) n cs))))

(def-fns _ $ (many mult-tok : (many (Multiplicity) m) -> (many (String) t))
  (match many m _ ((Erased) "i0") ((Many) "i1") ((Once) "i2")))

(def-fns _ $ (many pass2 : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (IdMap $ Nat) slots) (many (IdMap $ String) toks) (many (P2) acc) -> (many (P2) r))
  (let-match many refs (Cons _ v rest) ((Nil _) acc))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (let ((many (Nat) slot)) $ match many (idmap-get _ (ref-pos Block _ v) slots) _ ((Hit _ _ _ k _) k) ((Miss _ _ _ _) 0))
  (let ((many (P2) acc1))
    (match many (cell-of _ b reg) _
      ((CBlank t n)
        (let ((many al)) $ rcat5 (RStr "b") (nat-rope t) (RStr ".") (nat-rope n) $ RStr " ")
        (let ((many (List $ String) ts))
          (match many b _
            ((BTag _ c fs)
              (let ((many fts)) $ toks-of _ toks fs)
              (match many (and (ctor-tagged c) $ shape-wide $ ctor-shape c) _ ((BTrue) (Cons _ (str-cat "i" $ nat-str $ ctor-index c) fts)) ((BFalse) fts)))
            ((BTup _ fs) (toks-of _ toks fs))
            ((BArray _ n2 es) (toks-of _ toks $ idmap-prefix _ es n2 $ Nil _))
            ((BExt _ p) (match many p _ ((PHandle x rd m _) (Cons _ (str-cat "i" $ nat-str x) $ Cons _ (match many rd _ ((MintedIs) "i0") ((MintedType) "i1")) $ Cons _ (mult-tok m) $ Cons _ (match many m _ ((Many) (settled-tok env toks x)) (else "i0")) $ Nil _)) (else (Nil _))))
            (else (Nil _))))
        (p2-alloc acc al $ fill-op slot ts))
      ((CLeaf)
        (let-match many b (BSlots _ n2 ks _)
          ((BExt _ p) (p2-alloc acc (match many p _ ((PStr s) (text-op "s" s)) ((PBytes s) (text-op "y" s)) ((PNat n) (text-op "z" $ nat-str n)) ((PHalf n) (text-op "z" $ nat-str n)) (else (RStr "x "))) $ REmpty))
          ((BCtorFn _ c) (p2-ctor acc d c))
          ((BMat _ adt) (p2-global acc $ matchable-rope adt d))
          (else acc))
        (let ((many ts)) $ toks-of _ toks $ idmap-prefix _ ks n2 $ Nil _)
        (p2-alloc acc (RStr "t0 ") $ rcat5 (RStr "k") (nat-rope slot) (RStr " ") (nat-rope $ list-length _ ts) $ rcat (RStr " ") $ toks-rope ts))
      (else acc)))
  (tail $ pass2 _ hp rest env d reg slots toks acc1))

(def-fns _ $ (many const-binds : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (IdMap $ String) toks) (subterm many (List $ Nat) xs) (many (IdMap $ Rope) acc) -> (many (IdMap $ Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (let ((many (Maybe $ Nat) found)) $ match many (const-kind env d reg x) _ ((CkData p) (Some _ p)) ((CkCtor _ p) (Some _ p)) (else (None _)))
  (let-match many found (Some _ pos) ((None _) (tail $ const-binds env d reg toks rest acc)))
  (let-match many (idmap-get _ pos toks) (Hit _ _ _ t _) ((Miss _ _ _ _) (tail $ const-binds env d reg toks rest acc)))
  (tail $ const-binds env d reg toks rest $ idmap-set _ pos (rcat3 (RStr $ data-name pos) (RStr " = ") $ tok-expr t) acc))

(def-fns _ $ (many pair-values : (erased Type V) (subterm many (List $ Pair (Nat) V) ps) (many (List V) acc) -> (many (List V) r))
  (let-match many ps (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ _ v))
  (tail $ pair-values _ rest $ Cons _ v acc))

(def-fns _ $ (many tree-parts : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (IdMap $ String) toks) (subterm many (List $ Nat) keys) (many (List $ Rope) defs) (many (List $ Rope) names) (many (IdMap $ Rope) binds) -> (many (List $ Rope) defs2) (many (List $ Rope) names2) (many (IdMap $ Rope) binds2))
  (let-match many keys (Cons _ key rest) ((Nil _) (values defs names binds)))
  (let ((many ds) (many ns)) $ group-defs env d reg key)
  (let ((many (List $ Nat) cs)) $ match many (reg-get reg key) _ ((Some _ i) (match many i _ ((MkGInfo _ _ _ _ _ _ cs0 _ _ _) cs0))) ((None _) (Nil _)))
  (tail $ tree-parts env d reg toks rest (rev-onto _ ds defs) (rev-onto _ ns names) $ const-binds env d reg toks cs binds))

(def-fns _ $ (many adapter-text : (many (Env) env) (many (Reg) reg) (many (Nat) key) (many (Nat) i) -> (many (Rope) r))
  (let ((many rets)) $ reg-ret reg key)
  (let ((many head)) $ rcat3 (RStr "let () = (!rt_adapters).(") (nat-rope i) $ RStr ") <- ")
  (let-match many (reg-closed reg key) (BFalse)
    ((BTrue) (rcat4 head (RStr "(fun _ -> [| ") (rjoin (list-map-obj env rets) "; ") $ RStr " |])\n")))
  (let ((many vs)) $ list-map-valued env rets)
  (let ((many caps)) $ cap-slots 0 $ fac-caps (reg-members reg key) $ reg-caps reg key)
  (rcat5 head (RStr "(fun c -> let ") (tuple-of vs) (rcat5 (RStr " = ") (RStr $ maker-name env key) (RStr " ") (args-rope caps) $ RStr " in [| ") $ rcat (rjoin vs "; ") $ RStr " |])\n"))

(def-adts $ (P3 : -> Type)
  enum
  (many MkP3 : (many (Rope) out) (many (Rope) seg) (many (Bool) open) (many (List $ Nat) pending) (many (Nat) ads) (many (IdMap $ Nat) adm) -> (P3)))

(def-adts $ (Px : -> Type)
  enum
  (many MkPx : (many (Env) env) (many (Decls) d) (many (Reg) reg) (many (IdMap $ Nat) slots) (many (IdMap $ String) toks) (many (IdMap $ List $ Nat) trees) (many (IdMap $ Nat) roots) -> (Px)))

(def-fns _ $ (many p3-flush : (many (P3) st) -> (many (P3) r))
  (let-match many st (MkP3 out seg open pending ads adm))
  (match many open _
    ((BFalse) st)
    ((BTrue) (MkP3 (rcat3 out (rcat (RStr "let () = rt_run ") $ quoted $ rope-str seg) $ RStr "\n") (REmpty) (BFalse) pending ads adm))))

(def-fns _ $ (many tree-adapters : (many (Env) env) (many (Reg) reg) (subterm many (List $ Nat) keys) (many (Rope) out) (many (Nat) ads) (many (IdMap $ Nat) adm) -> (many (Rope) o) (many (Nat) a) (many (IdMap $ Nat) m))
  (let-match many keys (Cons _ key rest) ((Nil _) (values out ads adm)))
  (match many (reg-ret reg key) _
    ((Nil _) (tail $ tree-adapters env reg rest out ads adm))
    (else (tail $ tree-adapters env reg rest (rcat out $ adapter-text env reg key ads) (Succ ads) $ idmap-set _ key ads adm))))

(def-fns _ $ (many tree-text : (many (Px) px) (many (Nat) root) -> (many (Rope) r) (many (List $ Nat) keys))
  (let-match many px (MkPx env d reg _ toks trees _))
  (let ((many keys)) $ map-list trees root)
  (let ((many defs) (many names) (many binds)) $ tree-parts env d reg toks keys (Nil _) (Nil _) $ MEmpty _)
  (let-match many defs (Cons _ _ _) ((Nil _) (values (REmpty) keys)))
  (let ((many bs)) $ pair-values _ (idmap-pairs _ binds 1 0 $ Nil _) $ Nil _)
  (let ((many rec)) $ rcat (RStr "let rec ") $ rjoin defs "\nand ")
  (let-match many bs (Cons _ _ _) ((Nil _) (values (rcat rec $ RStr "\n") keys)))
  (let ((many ns)) $ commas names)
  (values (rcat5 (RStr "let ") ns (rcat3 (RStr " =\n  let ") (rjoin bs " and ") $ RStr " in\n  ") (rcat rec $ RStr " in\n  ") $ rcat ns $ RStr "\n") keys))

(def-fns _ $ (many flush-trees : (many (Px) px) (many (Maybe $ Nat) upto) (subterm many (List $ Nat) pending) (many (P3) st) -> (many (P3) r))
  (let-match many pending (Cons _ root rest) ((Nil _) (match many st _ ((MkP3 out seg open _ ads adm) (MkP3 out seg open (Nil _) ads adm)))))
  (let ((many (Bool) go)) $ match many upto _ ((None _) (BTrue)) ((Some _ u) (not $ nat-lt u root)))
  (let-match many go (BTrue) ((BFalse) (match many st _ ((MkP3 out seg open _ ads adm) (MkP3 out seg open pending ads adm)))))
  (let-match many px (MkPx env _ reg _ _ _ _))
  (let-match many (p3-flush st) (MkP3 out seg open _ ads adm))
  (let ((many text) (many keys)) $ tree-text px root)
  (let ((many out2) (many ads2) (many adm2)) $ tree-adapters env reg keys (rcat out text) ads adm)
  (tail $ flush-trees px upto rest $ MkP3 out2 seg open rest ads2 adm2))

(def-fns _ $ (many inst-caps : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (Frames (Ref Block a) ctx) fr) (many (Reg) reg) (many (IdMap $ Nat) slots) (many (IdMap $ String) toks) (subterm many (List $ Key) ks) -> (many (List $ String) r))
  (let-match many ks (Cons _ k rest) ((Nil _) (Nil _)))
  (let ((many (String) t))
    (match many (frame-ref _ _ fr $ key-id k) _
      ((None _) "x")
      ((Some _ v) (match many k _ ((KVal _) (pos-tok toks $ ref-pos Block _ v)) ((KFn m) (member-tok reg slots (ref-pos Block _ v) m))))))
  (Cons _ t $ notail $ inst-caps _ _ fr reg slots toks rest))

(def-fns _ $ (many raw-binds : (many (Env) env) (many (IdMap $ String) toks) (subterm many (List $ Nat) ids) -> (many (Rope) r))
  (let-match many ids (Cons _ x rest) ((Nil _) (REmpty)))
  (let-match many (settled-pos env x) (Some _ p) ((None _) (tail $ raw-binds env toks rest)))
  (rcat5 (RStr "let a") (nat-rope p) (RStr " = ") (tok-expr $ pos-tok toks p) $ rcat (RStr "\n") $ notail $ raw-binds env toks rest))

(def-fns _ $ (many pass3 : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) refs) (many (Px) px) (many (P3) st) -> (many (P3) r))
  (let-match many refs (Cons _ v rest) ((Nil _) (flush-trees px (None _) (match many st _ ((MkP3 _ _ _ p _ _) p)) $ p3-flush st)))
  (let-match many px (MkPx env d reg slots toks _ roots))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (let ((many (P3) st1))
    (match many (cell-of _ b reg) _
      ((CInst key)
        (let ((many (Nat) root)) $ match many (idmap-get _ key roots) _ ((Hit _ _ _ r0 _) r0) ((Miss _ _ _ _) key))
        (let-match many (flush-trees px (Some _ root) (match many st _ ((MkP3 _ _ _ p _ _) p)) st) (MkP3 out seg _ pending ads adm))
        (let ((many (Nat) a)) $ match many (idmap-get _ key adm) _ ((Hit _ _ _ i _) i) ((Miss _ _ _ _) 0))
        (let-match many b (BGroup _ _ _ _ fr) (else st))
        (let ((many cs)) $ inst-caps _ _ fr reg slots toks $ fac-caps (reg-members reg key) $ reg-caps reg key)
        (MkP3 out (rcat5 seg (RStr "c") (nat-rope a) (RStr " ") $ rcat3 (nat-rope $ list-length _ cs) (RStr " ") $ toks-rope cs) (BTrue) pending ads adm))
      ((CExpr)
        (let-match many (p3-flush st) (MkP3 out seg open pending ads adm))
        (let ((many (Rope) pre) (many (Rope) e))
          (match many b _
            ((BTag _ c fs) (values (REmpty) $ build-rope d 0 c $ tok-exprs $ toks-of _ toks fs))
            ((BExt _ p)
              (let-match many p (PRaw f r) (else (values (REmpty) $ RStr "(Obj.repr ())")))
              (let ((many _) (many ids)) $ decl-take-consts $ syn-handle-decl (MkDecls (Nil _) (Nil _) (Nil _) (Nil _)) r)
              (values (raw-binds env toks ids) $ rcat3 (RStr "(Obj.repr ") (syn-rope env f r) $ RStr ")"))
            ((BError _ m) (values (REmpty) $ rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))
            (else (values (REmpty) $ RStr "(Obj.repr ())"))))
        (MkP3 (rcat4 out pre (rcat3 (RStr "let () = rt_push (") e $ RStr ")\n") $ REmpty) seg open pending ads adm))
      (else st)))
  (tail $ pass3 _ hp rest px st1))

; ---- The walk from the roots: what a Settled or a final reaches, each value once. The worklist is
; tail recursive, which the seen set pays for: a stamp is below the store's next stamp, the trie
; holds at most that many keys (base.sl's bounded-le), so the keys it still lacks is a measure that
; strictly drops every time a fresh value is enqueued. That measure and the worklist are the two
; components of the decrease, in that order.

(def-fns _ $ (many frames-refs : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx)
    (subterm many (Frames (Ref Block a) ctx) fr) (many (List $ Ref Block a) acc) -> (many (List $ Ref Block a) r))
  (match many fr _
    ((FrNil _) acc)
    ((FrVals _ _ _ vs _ rest) (tail (frames-refs _ _ rest (rev-onto _ vs acc))))
    ((FrGroup _ _ _ g _ rest) (tail (frames-refs _ _ rest (Cons _ g acc))))))

(def-fns _ $ (many settled-refs : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (List $ Nat) ids)
    (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r))
  (let-match many ids (Cons _ x rest) ((Nil _) acc))
  (let ((many acc1))
    (match many (idmap-get _ x en) (((List $ Ref Block hs) _))
      ((Miss _ _ _ _) acc)
      ((Hit _ _ _ info _)
        (let-match many info (MkEInfo _ _ _ st _ _ _ _))
        (match many st (((List $ Ref Block hs) _))
          ((SHypothetical _) acc)
          ((SSettled _ v _) (Cons _ v acc))))))
  (tail $ settled-refs _ en rest acc1))

(def-fns _ $ (many block-refs : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Maybe $ Reg) reg) -> (many (List $ Ref Block a) r))
  (let-match many b (BGroup _ _ _ g fr)
    ((BTag _ _ fields) fields)
    ((BArray _ n es) (idmap-prefix _ es n $ Nil _))
    ((BSlots _ n ks _) (idmap-prefix _ ks n $ Nil _))
    ((BTup _ fields) fields)
    ((BFn _ g _ _) (Cons _ g $ Nil _))
    (else (Nil _)))
  (match many reg _ ((None _) (frames-refs _ _ fr (Nil _))) ((Some _ rg) (group-refs _ _ _ g fr rg))))

(def-fns _ $ (many trace-step : (erased (Hist Block) a) (many (Block (Ref Block a)) blk) (many (Env) env) (many (Decls) d) (many (Maybe $ Reg) mode) (many (Reg) r) -> (many (Decls) d2) (many (List $ Nat) cids) (many (Reg) r2))
  (let-match many blk (BGroup _ _ _ g _)
    ((BExt _ _)
      (let ((many d3) (many cids)) $ decl-take-consts $ collect-block _ blk env d)
      (values d3 cids r))
    (else
      (let-match many mode (None _) ((Some _ _) (values d (Nil _) r)))
      (let ((many d3) (many cids)) $ decl-take-consts $ collect-block _ blk env d)
      (values d3 cids r)))
  (let-match many g (MkGroup _ gids _ _))
  (let ((many (Reg) r2)) $ match many mode _ ((None _) (reg-block _ blk r)) ((Some _ _) r))
  (let-match many (reg-get r2 $ group-key gids) (Some _ info) ((None _) (values d (Nil _) r2)))
  (let-match many info (MkGInfo _ _ _ _ _ _ cs _ _ _))
  (values d cs r2))

(def-fns _ $ (many trace-loop : (erased (Hist Block) hs) (erased (Nat) bound) (erased (Len Block hs bound) lb) (many (Store Block hs) hp)
    (erased (Nat) size) (subterm erased (Nat) rest) (erased (Add size rest bound) sum)
    (many (IdMap $ Unit) seen) (erased (Bounded (Unit) seen size bound) bd)
    (subterm many (List $ Ref Block hs) work) (many (List $ Ref Block hs) acc)
    (many (Env) env) (many (IdMap $ EInfo hs) en) (many (Decls) d) (many (Maybe $ Reg) reg) (many (Reg) rg) -> (many (List $ Ref Block hs) acc2) (many (Decls) d2) (many (Reg) rg2))
  (let-match many work (Cons _ at2 wrest) ((Nil _) (values acc d rg)))
  (let ((many k) (erased lk)) (ref-key Block _ bound lb at2))
  (let-match many (idmap-get _ k seen) (Miss _ _ _ ab)
    ((Hit _ _ _ _ _) (tail (trace-loop _ bound lb hp size rest sum seen bd wrest acc env en d reg rg))))
  (let ((many seen2) (erased rest2) (erased bd2) (erased sum2) (erased less))
    (seen-add (Unit) k (MkUnit) seen size rest bound bd sum ab lk))
  (let ((erased rs) (many blk) (erased tsf)) $ store-read Block hs hp at2)
  (let ((many kids)) (block-refs _ blk reg))
  (let ((erased _) (erased pk)) (refs-widen Block rs hs tsf kids))
  (let ((many d3) (many cids) (many rg3)) $ trace-step _ blk env d reg rg)
  (tail (trace-loop _ bound lb hp (Succ size) (subterm (lt-subterm rest2 rest less)) rest2 sum2 seen2 bd2
          (rev-onto _ (coerce kids pk) $ settled-refs _ en cids wrest) (Cons _ at2 acc) env en d3 reg rg3)))

(def-lvl REF-CMP)

(let ((erased REF-SORT-L) (many ref-sort)) (sort-factory REF-CMP))

; ---- The driver (lib/driver_core.ml): its operations on the prelude's values, each a direct build or match



(def-fns _ $ (many driver-make : (many (Decls) d) (many (Env) env) (many (String) name) -> (many (Rope) r))
  (let-match many (prelude-ctor env name) (Some _ c) ((None _) (RStr "(absurd ())")))
  (let ((many fs)) $ field-names (ctor-arity c) 0)
  (match many fs _
    ((Nil _) (build-rope d 0 c fs))
    ((Cons _ _ _) (lambda-rope fs $ build-rope d 0 c fs))))

(def-fns _ $ (many driver-un : (many (Decls) d) (many (Env) env) (many (String) tname) (many (ArmKind) k) -> (many (Rope) r))
  (match many (prelude-adt env tname) _
    ((None _) (RStr "(absurd ())"))
    ((Some _ adt) (lambda-rope (Cons _ (RStr "v") $ Nil _) $ dispatch-rope d 0 adt (all-live adt) (RStr "v") (ctor-arms d (adt-ctors adt) k) $ None _))))

(def-fns _ $ (many driver-op : (many (String) field) (many (Rope) r) -> (many (Rope) r2))
  (rcat3 (RStr $ str-cat3 "Driver_core." field " = ") r $ RStr "; "))

(def-fns _ $ (many driver-rope-of : (many (Decls) d) (many (Env) env) -> (many (Rope) r))
  (rcat5 (RStr "let driver = Driver_core.make ~str_of_host:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~str_to_slice:(fun v -> (Obj.obj v : Ffi_core.slice)) ~nat_to_z:(fun v -> (Obj.obj v : Z.t)) ~nat_of_z:Obj.repr { ")
    (rcat5 (driver-op "zero" $ driver-make d env "Zero") (driver-op "succ" $ driver-make d env "Succ") (driver-op "pred" $ driver-un d env "Nat" $ AkOption "Succ")
      (driver-op "u8" $ driver-make d env "MkU8") $ driver-op "un_u8" $ driver-un d env "U8" $ AkField)
    (rcat5 (driver-op "char" $ driver-make d env "MkChar") (driver-op "un_char" $ driver-un d env "Char" $ AkField) (driver-op "snil" $ driver-make d env "SNil")
      (driver-op "scons" $ driver-make d env "SCons") $ rcat (driver-op "un_str" $ driver-un d env "String" $ AkOption "SCons") $ rcat3 (driver-op "un_list" $ driver-un d env "List" $ AkOption "Cons") (driver-op "un_pair" $ driver-un d env "Pair" $ AkTuple) $ driver-op "un_some" $ driver-un d env "Maybe" $ AkOption "Some")
    (rcat5 (driver-op "some" $ driver-make d env "Some") (driver-op "none" $ driver-make d env "None") (driver-op "ok" $ driver-make d env "Ok")
      (driver-op "fail" $ driver-make d env "Fail") $ driver-op "unit" $ driver-make d env "MkUnit")
    (rcat5 (driver-op "cons" $ driver-make d env "Cons") (driver-op "nil" $ driver-make d env "Nil")
      (rcat5 (driver-op "pair" $ driver-make d env "MkPair") (driver-op "is_file" $ driver-make d env "IsFile")
        (driver-op "is_dir" $ driver-make d env "IsDir") (driver-op "is_other" $ driver-make d env "IsOther")
        $ driver-op "missing" $ driver-make d env "Missing")
      (rcat4 (driver-op "changed" $ driver-make d env "Changed") (driver-op "unchanged" $ driver-make d env "Unchanged")
        (rcat (driver-op "mk_usage" $ rcat3 (RStr "(Obj.repr ") (driver-make d env "MkUsage") $ RStr ")") $ rcat3 (driver-op "mk_exited" $ rcat3 (RStr "(Obj.repr ") (driver-make d env "MkExited") $ RStr ")")
          (driver-op "un_job" $ driver-un d env "ExecJob" $ AkTuple) $ driver-op "exec_results" $ driver-make d env "MkExecResults")
        $ rcat3 (driver-op "request" $ driver-un d env "Request" $ AkVariant) (driver-op "step" $ driver-un d env "Program" $ AkVariant)
        $ driver-op "is_start" $ driver-un d env "Stopwatch" $ AkIs "Start")
      $ RStr "Driver_core.apply = (fun (k : Obj.t) xs -> if xs = [] then (Obj.obj k : unit -> Obj.t) () else List.fold_left (fun f (x : Obj.t) -> (Obj.obj f : Obj.t -> Obj.t) x) k xs) }\n")))

(def-fns _ $ (many driver-rope : (many (Decls) d) (many (Env) env) (many (List $ String) reads) (many (List $ String) writes) (many (Maybe $ String) bytes) (many (Bool) with-env) (many (Bool) with-exec) -> (many (Rope) r))
  (match many (prelude-ctor env "Exit") _
    ((None _) (REmpty))
    ((Some _ _) (rcat5 (driver-rope-of d env) (RStr "let world = Driver_core.start ") (rcat3 (bracketed $ quoted-all reads) (RStr " ") (bracketed $ quoted-all writes))
      (match many bytes _ ((None _) (RStr " None")) ((Some _ b) (rcat3 (RStr " (Some ") (quoted b) $ RStr ")")))
      $ RStr $ str-cat3 " " (bool-ml with-env) $ str-cat3 " " (bool-ml with-exec) " world\nlet print_final = Driver_core.print world\n"))))

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ (ShowMemo : -> Type)
  enum
  (many MkShowMemo : (many (Nat) fresh) (many (Nat) count) (many (List $ Pair (Term) $ String) known) (many (List $ Rope) defs) (many (Decls) decls) -> (ShowMemo)))

(def-fns _ $ (many memo-match : (many (ShowMemo) memo) (many (Adt) adt) -> (many (ShowMemo) r))
  (match many memo _ ((MkShowMemo fresh count known defs d) (MkShowMemo fresh count known defs $ collect-match adt (all-live adt) d))))

(def-fns _ $ (many memo-decls : (many (ShowMemo) memo) -> (many (Decls) d))
  (match many memo _ ((MkShowMemo _ _ _ _ d) d)))

(def-fns _ $ (many memo-decl-const : (many (ShowMemo) memo) (many (Nat) y) -> (many (ShowMemo) r))
  (match many memo _ ((MkShowMemo fresh count known defs d) (MkShowMemo fresh count known defs $ decl-const d y))))

(def-fns _ $ (many memo-find : (subterm many (List $ Pair (Term) $ String) known) (many (Env) env) (many (Term) ty) -> (many (Maybe $ String) r))
  (let-match many known (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPair _ _ t name))
  (match many (term-eq t ty) _
    ((BTrue) (Some _ name))
    ((BFalse) (tail $ memo-find rest env ty))))

(def-fns _ $ (many spaced : (subterm many (List $ Rope) parts) -> (many (Rope) r))
  (let-match many parts (Cons _ p rest) ((Nil _) (RStr "\"\"")))
  (match many rest _
    ((Nil _) p)
    ((Cons _ _ _) (rcat3 p (RStr " ^ \" \" ^ ") $ notail $ spaced rest))))

; A literal type's printer, which prints the literal its value reads back from: the emitted OCaml spells it
; through Ffi_core (lib/extract.ml's literal_show). slc always compiles against the FFI, so a Nat is its
; integer and a String its slice; a Char and a U8 are their Nat (section 33), unwrapped by neither.
(def-fns _ $ (many lit-show : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Rope) r))
  (let-match many (prelude-nullary env ty "Slot") (BFalse) ((BTrue) (Some _ $ RStr "\"_\"")))
  (let-match many (prelude-nullary env ty "Nat") (BFalse) ((BTrue) (Some _ $ RStr "(Z.to_string (Obj.obj v : Z.t))")))
  (let-match many (prelude-nullary env ty "Char") (BFalse)
    ((BTrue) (Some _ $ RStr "(Ffi_core.lit_char (Z.to_int (Obj.obj v : Z.t)))")))
  (match many (prelude-nullary env ty "String") (((Maybe $ Rope) _))
    ((BTrue) (Some _ $ RStr "(let (s, o, l) = (Obj.obj v : Ffi_core.slice) in Ffi_core.lit_string (String.sub s o l))"))
    ((BFalse) (None $ Rope))))

(def-fns _ $ (many block-word : (many (Env) env) (many (Maybe $ Term) place) (many (Nat) i) (many (List $ Rope) words) (many (ShowMemo) memo) -> (many (Rope) w) (many (Nat) i2) (many (ShowMemo) memo2))
  (let-match many place (Some _ p) ((None _) (values (RCat (RStr "f") $ nat-rope i) (Succ i) memo)))
  (let ((many (Rope) constant) (many (ShowMemo) memoc)) $ match many (at-constant (env-words env) env p) _ ((Some _ y) (values (const-rope env y) $ memo-decl-const memo y)) ((None _) (values (RStr "(Obj.repr ())") memo)))
  (let-match many p (TSlotOf c) (else (values constant i memoc)))
  (let-match many c (TBound k) (else (values constant i memoc)))
  (match many (list-nth _ words k) _ ((NthHit _ _ _ w _) (values w i memo)) ((NthMiss _ _ _ _) (values (RStr "(Obj.repr ())") i memo))))

(def-fns _
  ((many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) -> (many (ShowMemo) memo2) (many (String) name))
    (let-match many fuel (Succ k) ((Zero) (values memo "show_any")))
    (let ((many ty)) $ canon-env env ty0)
    (let-match many memo (MkShowMemo fresh count known defs ds))
    (let ((many key)) $ mapv ty (OpWild fresh) 0)
    (let-match many (memo-find known env key) (None _) ((Some _ name) (values memo name)))
    (let ((many name)) $ str-cat "show_" $ nat-str count)
    (let ((many memo1)) $ MkShowMemo fresh (Succ count) (Cons _ (MkPair _ _ key name) known) defs ds)
    (let ((many (ShowMemo) memo2) (many (Rope) body))
      (match many (lit-show env ty) (((ShowMemo) _) ((Rope) r0))
        ((Some _ text) (values memo1 text))
        ((None _)
          (let-match many ty (TApp _ _)
            ((TFn _ _ _ _) (values memo1 $ RStr "\"_\""))
            ((TCell _ _) (values memo1 $ RStr "\"_\""))
            ((TValCtor _ _) (values memo1 $ RStr "\"_\"")) (else (values memo1 $ RStr "\"_\"")))
          (let-match many (type-adt env ty) (Some _ adt)
            ((None _) (values memo1 $ RStr "\"_\"")))
          ; the tag where there is one, else the sole non-phantom constructor; a union with
          ; several has no way to choose and prints `_` (section 45)
          (let ((many usable))
            (match many (adt-tagged adt) (((List $ Ctor) _))
              ((BTrue) (adt-ctors adt))
              ((BFalse) (match many (lone-ctor adt) (((List $ Ctor) _))
                          ((None _) (Nil _))
                          ((Some _ c) (Cons _ c $ Nil _))))))
          (let ((many memo3) (many arms)) $ notail $ show-arms k env ty usable (memo-match memo1 adt) $ adt-tagged adt)
          (match many arms (((ShowMemo) _) ((Rope) r2))
            ((Nil _) (values memo3 $ RStr "\"_\""))
            ((Cons _ _ _)
              (values memo3 $ dispatch-rope (memo-decls memo3) 0 adt (all-live adt) (RStr "v") arms $ Some _ $ RStr "\"_\""))))))
    (match many memo2 _
      ((MkShowMemo fresh2 count2 known2 defs2 ds2)
        (values (MkShowMemo fresh2 count2 known2 (Cons _ (rcat4 (RStr name) (RStr " (v : Obj.t) : string = ") body $ REmpty) defs2) ds2) name))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, the opened objects
  ; merged as entering a branch does, its fields shown only then, as the reference's exception skips them.
  ((many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List $ Ctor) ctors) (many (ShowMemo) memo) (many (Bool) tagged) -> (many (ShowMemo) memo2) (many (List $ Arm) arms))
    (let-match many fuel (Succ k) ((Zero) (values memo $ Nil _)))
    (let-match many ctors (Cons _ c rest) ((Nil _) (values memo $ Nil _)))
    (let-match many c (MkCtor cname cid index arity _ _ _ _))
    (let ((many ctele) (many ret)) $ ctor-type env $ listed-entry env ty cid)
    (let ((many envb) (many fids) (erased _)) $ open-tele ctele env (None _) (None _) (None _) (Nil _) $ BFalse)
    (let ((many (Env) envb2) (many (Bool) live))
      (match many (merge-all $ unify-force (Forcing envb) (instantiate (tvars-rev fids $ Nil _) ret) ty) _
        ((UOk e2) (values e2 $ BTrue))
        ((UContra _) (values envb $ BFalse))))
    (let ((many (ShowMemo) memo2) (many (List $ Rope) shown))
      (match many live _
        ((BTrue) (notail $ show-block-fields k envb2 ctele fids memo 0 $ Nil _))
        ((BFalse) (values memo $ Nil _))))
    ; Ffi_core.show_app is the one definition the interpreter, an extracted program and this
    ; output share, so `$` is not decided again here (section 45)
    (let ((many (Rope) text))
      (rcat4 (RStr "(Ffi_core.show_app ") (quoted cname) (rwrap " [ " (rjoin shown "; ") " ])") $ REmpty))
    (let ((many memo3) (many more)) $ notail $ show-arms k env ty rest memo2 tagged)
    (values memo3 $ match many live (((List $ Arm) _)) ((BTrue) (Cons _ (MkArm index (field-names arity 0) text) more)) ((BFalse) more)))

  ((many show-block-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Entry) tele) (many (List $ Nat) fids) (many (ShowMemo) memo) (many (Nat) i) (many (List $ Rope) words) -> (many (ShowMemo) memo2) (many (List $ Rope) shown))
    (let-match many fuel (Succ k) ((Zero) (values memo $ Nil _)))
    (let-match many fids (Cons _ x rest) ((Nil _) (values memo $ Nil _)))
    (let ((many (Maybe $ Term) place) (many (List $ Entry) trest)) $ match many tele _ ((Nil _) (values (None _) $ Nil _)) ((Cons _ e er) (values (entry-place e) er)))
    (match many (entry-mult-of env x) (((ShowMemo) _) ((List $ Rope) rs))
      ((Erased)
        (let ((many memo3) (many more)) $ notail $ show-block-fields k env trest rest memo i $ Cons _ (RStr "(Obj.repr ())") words)
        (values memo3 $ Cons _ (RStr "\"_\"") more))
      (else
        (let ((many memo2) (many name)) $ notail $ show-type k env (type-of env x) memo)
        (let ((many fw) (many i2) (many memo2b)) $ block-word env place i words memo2)
        (let ((many memo3) (many more)) $ notail $ show-block-fields k env trest rest memo2b i2 $ Cons _ fw words)
        (values memo3 $ Cons _ (rcat3 (RStr name) (RStr " ") fw) more)))))

(def-fns _ $ (many show-defs : (many (ShowMemo) memo) -> (many (Rope) r))
  (let-match many memo (MkShowMemo _ _ _ defs _))
  (match many defs _
    ((Nil _) (REmpty))
    ((Cons _ _ _) (rcat3 (RStr "let rec ") (rjoin (list-rev _ defs) "\nand ") $ RStr "\n"))))

; A final that is a constructor prints `_`, as the reference does (section 45).
(def-fns _ $ (many named-final : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) -> (many (Maybe $ String) r))
  (let ((erased _) (many b) (erased _)) $ store-read Block hs hp v)
  (let-match many b (BCtorFn _ _) (else (None $ String)))
  (Some _ "_"))

(def-fns _ $ (many final-rope : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) (many (Term) ty) (many (Maybe $ Adt) native) (many (Nat) idx) (many (Decls) d) -> (many (Decls) d2) (many (Rope) r))
  (let ((many vr)) $ addr-rope _ v)
  (let-match many native (None _)
    ((Some _ adt)
      (let ((many d1)) $ collect-match adt (all-live adt) d)
      (values d1 $ rcat4 (rcat3 (RStr "let () = if Sys.argv.(1) = \"") (RStr $ nat-str idx) $ RStr "\" then let v = (Obj.obj ") vr (RStr " : unit -> Obj.t) () in ") $ rcat (dispatch-rope d1 0 adt (all-live adt) (RStr "v") (ctor-arms d1 (adt-ctors adt) $ AkIndex) $ None _) $ RStr "\n")))
  (match many (classify-final env ty) _
    ((FMain) (values d $ rcat3 (RStr "let () = driver.run_main world ") vr $ RStr "\n"))
    ((FProgram) (values d $ rcat3 (RStr "let () = exit (driver.run_program world ") vr $ RStr ")\n"))
    ((FThunk t)
      (let ((many memo) (many name)) $ show-type show-fuel env t $ MkShowMemo (env-fresh-bound env) 0 (Nil _) (Nil _) d)
      (values (memo-decls memo) $ rcat5 (show-defs memo) (RStr "let () = print_final (") (RStr name) (rcat3 (RStr " ((Obj.obj ") vr $ RStr " : unit -> Obj.t) ()))") $ RStr "\n"))
    ((FPlain)
      (let-match many (named-final _ hp v) (None _)
        ((Some _ text) (values d $ rcat3 (RStr "let () = print_final ") (quoted text) $ RStr "\n")))
      (let ((many memo) (many name)) $ show-type show-fuel env ty $ MkShowMemo (env-fresh-bound env) 0 (Nil _) (Nil _) d)
      (values (memo-decls memo) $ rcat5 (show-defs memo) (RStr "let () = print_final (") (RStr name) (rcat3 (RStr " ") vr $ RStr ")") $ RStr "\n"))))

(def-fns _ $ (many emit-finals : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Pair (Ref Block hs) $ Term) fs) (many (Env) env) (many (List $ Adt) natives) (many (Nat) idx) (many (Decls) d) -> (many (Decls) d2) (many (Rope) r))
  (let-match many fs (Cons _ p rest)
    ((Nil _) (values d $ REmpty)))
  (let-match many p (MkPair _ _ v ty))
  (let ((many native) (many nrest)) $ match many natives (((Maybe $ Adt) _) ((List $ Adt) _)) ((Cons _ a more) (values (Some _ a) more)) ((Nil _) (values (None _) $ Nil _)))
  (let ((many d1) (many r1)) $ final-rope env _ hp v ty native idx d)
  (let ((many d2) (many r2)) $ notail $ emit-finals _ hp rest env nrest (Succ idx) d1)
  (values d2 $ rcat r1 r2))

; The prelude's types the driver and any printer may name, declared whether or not the program reaches them.
(def-fns _ $ (many collect-prelude : (subterm many (List $ String) names) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
  (match many names _
    ((Nil _) d)
    ((Cons _ n rest) (tail $ collect-prelude rest env $ match many (prelude-adt env n) (((Decls) _)) ((None _) d) ((Some _ adt) (collect-adt adt d))))))

(def-fns _ $ (many roots-of-finals : (erased (Hist Block) hs) (subterm many (List $ Pair (Ref Block hs) $ Term) fs)
    (many (Env) env) (many (IdMap $ EInfo hs) en) (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r))
  (let-match many fs (Cons _ p rest)
    ((Nil _) acc))
  (match many p _ ((MkPair _ _ v _) (tail (roots-of-finals _ rest env en $ Cons _ v acc)))))

(def-lvl NAT-CMP)

(def-fns NAT-CMP $ (many nat-leq : (many (Nat) x) (many (Nat) y) -> (many (Bool) b))
  (not $ nat-lt y x))

(let ((erased NAT-SORT-L) (many nat-sort)) (sort-factory NAT-CMP))

(def-fns _ $ (many trace-from : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Maybe $ Reg) reg) (many (List $ Ref Block hs) roots) (many (Env) env) (many (IdMap $ EInfo hs) en) (many (Decls) d) (many (Reg) rg) -> (many (List $ Ref Block hs) acc) (many (Decls) d2) (many (Reg) rg2))
  (let-match many hp (MkStore _ _ bound lb _))
  (trace-loop _ bound lb hp (Zero) bound (AddZero bound) (MEmpty _) (BdEmpty _ bound) roots (Nil _) env en d reg rg))

(def-fns _ $ (many pos-set : (erased (Hist Block) a) (subterm many (List $ Ref Block a) vs) (many (IdMap $ Unit) acc) -> (many (IdMap $ Unit) r))
  (let-match many vs (Cons _ v rest) ((Nil _) acc))
  (tail $ pos-set _ rest $ idmap-set _ (ref-pos Block _ v) (MkUnit) acc))

(def-fns _ $ (many all-traced : (erased (Hist Block) a) (subterm many (List $ Ref Block a) vs) (many (IdMap $ Unit) seen) -> (many (Bool) r))
  (let-match many vs (Cons _ v rest) ((Nil _) (BTrue)))
  (and (idmap-mem _ (ref-pos Block _ v) seen) $ tail $ all-traced _ rest seen))

(def-fns _ $ (many exact : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Reg) reg) (many (List $ Ref Block hs) roots) (many (Env) env) (many (IdMap $ EInfo hs) en) (many (Decls) d) -> (many (List $ Ref Block hs) acc) (many (Decls) d2) (many (IdMap $ Unit) reached))
  (let ((many acc) (many d1) (many _)) $ trace-from _ hp (Some _ reg) roots env en d reg)
  (let ((many reached)) $ reach 100000000 reg (instance-keys _ hp acc $ Nil _) $ MEmpty _)
  (let ((many extra)) $ settled-refs _ en (reached-consts reg (pair-keys _ (idmap-pairs _ reached 1 0 $ Nil _) $ Nil _) $ Nil _) $ Nil _)
  (let-match many fuel (Succ k) ((Zero) (values acc d1 reached)))
  (match many (all-traced _ extra $ pos-set _ acc $ MEmpty _) _
    ((BTrue) (values acc d1 reached))
    ((BFalse) (tail $ exact k _ hp reg (rev-onto _ extra roots) env en d))))

(def-fns _ $ (many final-binds : (erased (Hist Block) hs) (subterm many (List $ Pair (Ref Block hs) $ Term) fs) (many (IdMap $ String) toks) -> (many (Rope) r))
  (let-match many fs (Cons _ p rest) ((Nil _) (REmpty)))
  (let-match many p (MkPair _ _ v _))
  (let ((many pos)) $ ref-pos Block _ v)
  (rcat5 (RStr "let a") (nat-rope pos) (RStr " = ") (tok-expr $ pos-tok toks pos) $ rcat (RStr "\n") $ notail $ final-binds _ rest toks))

(def-fns _ $ (many emit-program : (many (Bool) templates) (many (List $ String) reads) (many (List $ String) writes) (many (Maybe $ String) bytes) (many (Bool) with-env) (many (Bool) with-exec) (many (Env) env) (many (List $ Adt) natives) -> (many (Rope) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store env)
  (let ((many d0)) $ collect-prelude (Cons _ "Array" $ Cons _ "Nat" $ Cons _ "String" $ Cons _ "Program" $ Cons _ "Request" $ Cons _ "Stopwatch" $ Cons _ "Maybe" $ Cons _ "Result" $ Cons _ "List" $ Cons _ "Pair" $ Cons _ "EntryKind" $ Cons _ "Change" $ Cons _ "Unit" $ Cons _ "Usage" $ Cons _ "Exited" $ Cons _ "ExecJob" $ Cons _ "ExecResults" $ Nil _) env $ MkDecls (Nil _) (Nil _) (match many templates (((List $ Template) _)) ((BTrue) (parse-templates $ split-on extern-templates #\newline)) ((BFalse) (Nil _))) (Nil _))
  (let ((many d0b) (many _)) $ emit-finals _ hp (list-rev _ fi) env natives (Zero) d0)
  (let ((many d0c) (many cids)) $ decl-take-consts d0b)
  (let ((many roots)) $ settled-refs _ en cids $ roots-of-finals _ fi env en (Nil _))
  (let ((many _) (many d1) (many reg0)) $ trace-from _ hp (None _) roots env en d0c reg-empty)
  (let ((many reg1)) $ analyse 100000 reg0)
  (let ((many acc2) (many d2) (many reached)) $ exact 8 _ hp reg1 roots env en d1)
  (let ((many keys)) $ pair-keys _ (idmap-pairs _ reached 1 0 $ Nil _) $ Nil _)
  (let ((many d3) (many _)) $ decl-take-consts $ collect-reached reg1 keys env d2)
  (def-fns REF-CMP $ (many ref-le : (many (Ref Block hs) x) (many (Ref Block hs) y) -> (many (Bool) b))
    (nat-lt (ref-pos Block _ x) (ref-pos Block _ y)))
  (let ((many order)) $ ref-sort (Ref Block hs) ref-le acc2)
  (let ((many reg)) $ set-rets reg1 keys (held-pass _ hp order reg1 $ MEmpty _) $ want-pass reg1 keys $ MEmpty _)
  (let ((many trees) (many rootmap)) $ tree-map reg reached keys (MEmpty _) $ MEmpty _)
  (let ((many n2) (many slots2)) $ assign-pass _ hp order reg (BFalse) 0 $ MEmpty _)
  (let ((many n3) (many slots)) $ assign-pass _ hp order reg (BTrue) n2 slots2)
  (let ((many toks)) $ tok-pass _ hp order reg slots $ MEmpty _)
  (let-match many (pass2 _ hp order env d3 reg slots toks $ MkP2 (REmpty) (REmpty) (Nil _) 0 $ MEmpty _) (MkP2 allocs fills globals _ _))
  (let ((many sorted)) $ nat-sort (Nat) nat-leq $ pair-keys _ (idmap-pairs _ trees 1 0 $ Nil _) $ Nil _)
  (let-match many (pass3 _ hp order (MkPx env d3 reg slots toks trees rootmap) $ MkP3 (REmpty) (REmpty) (BFalse) sorted 0 $ MEmpty _) (MkP3 p3 _ _ _ ads _))
  (let ((many d4) (many finals)) $ emit-finals _ hp (list-rev _ fi) env natives (Zero) d3)
  (let ((many d5) (many scids)) $ decl-take-consts d4)
  (let ((many data))
    (rcat5 (rcat5 (RStr "let () = rt_data := Array.make ") (nat-rope n3) (RStr " (Obj.magic 0 : Ffi_core.word); rt_adapters := Array.make ") (nat-rope ads) $ RStr " (fun _ -> [||])\n")
      (rcat3 (RStr "let () = rt_globals := [| ") (rjoin (list-rev _ globals) "; ") $ RStr " |]\n")
      (rcat3 (RStr "let () = rt_run ") (quoted $ rope-str allocs) $ RStr "\n")
      p3
      (rcat3 (RStr "let () = rt_run ") (quoted $ rope-str fills) $ RStr "\n")))
  (rcat5 (RStr runtime-header) (decls-rope d5) (driver-rope d5 env reads writes bytes with-env with-exec) data
    (rcat4 (final-binds _ fi toks) (raw-binds env toks $ pair-keys _ (idmap-pairs _ (set-add-all scids $ MEmpty _) 1 0 $ Nil _) $ Nil _) (RStr "let () = rt_data := [||]; rt_globals := [||]; rt_adapters := [||]\n") finals)))
