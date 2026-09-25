(def-fns _ $ (many top-name : (many (Env) env) (many (Nat) x) -> (many (String) s))
  (str-cat "v" $ str-cat (nat-str x) $ str-cat "_" $ sanitize $ name-of env x))

(let ((many show-fuel)) 100000)

(def-fns _ $ (many quoted : (many (String) s) -> (many (Rope) r))
  (rcat3 (RStr "\"") (ocaml-escape s) $ RStr "\""))

(def-fns _ $ (many nat-rope : (many (Nat) n) -> (many (Rope) r))
  (RStr $ nat-str n))

(def-fns _ $ (many nat-literal : (many (Nat) n) -> (many (Rope) r))
  (match many (nat-lt n 4611686018427387904) _
    ((BTrue) (rcat3 (RStr "(Obj.repr ") (nat-rope n) $ RStr ")"))
    ((BFalse) (rcat3 (RStr "(Obj.repr (Z.of_string \"") (nat-rope n) $ RStr "\"))"))))

(def-fns _ $ (many bracketed : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (rcat3 (RStr "[") (rjoin rs "; ") $ RStr "]"))

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
  (match many rs _
    ((Nil _) (RStr "(Obj.repr ())"))
    ((Cons _ r rest)
      (match many rest _
        ((Nil _) r)
        ((Cons _ _ _) (rcat3 (RStr "(Obj.repr (") (commas rs) $ RStr "))"))))))

(def-fns _ $ (many obj-tuple : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (match many rs _
    ((Nil _) (REmpty))
    ((Cons _ _ rest) (match many rest _ ((Nil _) (RStr "Obj.t")) ((Cons _ _ _) (rcat (RStr "Obj.t * ") $ notail $ obj-tuple rest))))))

; Binding the names to a value of that shape.
(def-fns _ $ (many untuple-rope : (many (List $ Rope) names) (many (Rope) e) (many (Rope) body) -> (many (Rope) r))
  (match many names _
    ((Nil _) body)
    ((Cons _ x rest)
      (match many rest _
        ((Nil _) (rcat5 (RStr "(let ") x (RStr " = ") (rcat3 e (RStr " in ") body) $ RStr ")"))
        ((Cons _ _ _) (rcat5 (RStr "(let (") (commas names) (rcat5 (RStr ") = (Obj.obj ") e (RStr " : ") (obj-tuple names) $ RStr ") in ") body $ RStr ")"))))))

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
; OCaml text with holes, embedded as header.sl's extern-templates; a type without one is taken apart and
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
  (many MkTemplate : (many (String) kind) (many (String) type) (many (Nat) index) (many (List $ Piece) pieces) -> (Template)))

(def-fns _ $ (many str-until-onto : (many (Rope) acc) (subterm many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (match many s _
    ((SNil) (values (rope-str acc) (None _)))
    ((SCons c rest)
      (match many (char-is c code) _
        ((BTrue) (values (rope-str acc) (Some _ rest)))
        ((BFalse) (tail (str-until-onto (RCat acc $ RChar c) rest code)))))))

(def-fns _ $ (many str-until : (many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (str-until-onto (REmpty) s code))

(def-fns _ $ (many str-split-fuel : (subterm many (Nat) fuel) (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many b) (many a)) (str-until s code))
  (match many a _
    ((None _) (Cons _ b $ Nil _))
    ((Some _ rest)
      (match many fuel _
        ((Zero) (Cons _ b $ Nil _))
        ((Succ f) (Cons _ b $ notail $ str-split-fuel f rest code))))))

(def-fns _ $ (many split-on : (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many n) (erased p)) (str-length s))
  (str-split-fuel n s code))

(def-fns _ $ (many digits-of : (many (String) s) -> (many (Maybe $ Nat) r))
  (match many (and (not $ str-is-empty s) $ all-digits s) _
    ((BTrue) (Some _ $ parse-nat s 0))
    ((BFalse) (None _))))

(def-fns _ $ (many parse-hole : (many (String) h) -> (many (Maybe $ Hole) r))
  (match many h _
    ((SNil) (None _))
    ((SCons c rest)
      (match many (char-is c 115) _
        ((BTrue) (match many (str-is-empty rest) _ ((BTrue) (Some _ $ HScrut)) ((BFalse) (None _))))
        ((BFalse)
          (match many (char-is c 102) _
            ((BTrue)
              (match many (split-on rest 46) _
                ((Cons _ i more)
                  (match many more _
                    ((Cons _ j none)
                      (match many none _
                        ((Nil _)
                          (match many (digits-of i) _
                            ((Some _ ni) (match many (digits-of j) _ ((Some _ nj) (Some _ $ HField ni nj)) ((None _) (None _))))
                            ((None _) (None _))))
                        ((Cons _ _ _) (None _))))
                    ((Nil _) (None _))))
                ((Nil _) (None _))))
            ((BFalse)
              (match many (digits-of rest) _
                ((None _) (None _))
                ((Some _ n)
                  (match many (char-is c 98) _
                    ((BTrue) (Some _ $ HBody n))
                    ((BFalse)
                      (match many (char-is c 97) _
                        ((BTrue) (Some _ $ HArg n))
                        ((BFalse) (match many (char-is c 116) _ ((BTrue) (Some _ $ HTemp n)) ((BFalse) (None _))))))))))))))))

; The pieces of a template's text, accumulated in reverse; a malformed hole stays as text for the OCaml
; compiler to refuse.
(def-fns _ $ (many parse-pieces : (subterm many (Nat) fuel) (many (String) s) (many (List $ Piece) acc) -> (many (List $ Piece) r))
  (let ((many lit) (many after)) (str-until s 123))
  (let ((many (List $ Piece) acc1)) $ match many (str-is-empty lit) _ ((BTrue) acc) ((BFalse) (Cons _ (PLit lit) acc)))
  (match many after _
    ((None _) (list-rev _ acc1))
    ((Some _ rest)
      (let ((many name) (many after2)) (str-until rest 125))
      (let ((many (Piece) piece)) $ match many (parse-hole name) _ ((Some _ h) (PHole h)) ((None _) (PLit $ str-cat3 "{" name "}")))
      (match many after2 _
        ((None _) (list-rev _ $ Cons _ piece acc1))
        ((Some _ rest2)
          (match many fuel _
            ((Zero) (list-rev _ $ Cons _ piece acc1))
            ((Succ f) (tail $ parse-pieces f rest2 $ Cons _ piece acc1))))))))

(def-fns _ $ (many parse-template : (many (String) line) -> (many (Maybe $ Template) r))
  (let ((many head) (many after)) (str-until line 58))
  (match many after _
    ((None _) (None _))
    ((Some _ text)
      (let ((many n) (erased p)) (str-length text))
      (let ((many pieces)) $ parse-pieces n text $ Nil _)
      (match many (split-on head 32) _
        ((Cons _ kind more)
          (match many more _
            ((Cons _ type rest)
              (match many (or (str-eq kind "match") $ str-eq kind "fn") _
                ((BTrue) (Some _ $ MkTemplate kind type 0 pieces))
                ((BFalse)
                  (match many rest _
                    ((Cons _ i _)
                      (match many (digits-of i) _
                        ((Some _ n2) (match many (str-eq kind "build") _ ((BTrue) (Some _ $ MkTemplate kind type n2 pieces)) ((BFalse) (None _))))
                        ((None _) (None _))))
                    ((Nil _) (None _))))))
            ((Nil _) (None _))))
        ((Nil _) (None _))))))

(def-fns _ $ (many parse-templates : (subterm many (List $ String) lines) -> (many (List $ Template) r))
  (match many lines _
    ((Nil _) (Nil _))
    ((Cons _ line rest)
      (match many (parse-template line) _
        ((Some _ t) (Cons _ t $ notail $ parse-templates rest))
        ((None _) (tail $ parse-templates rest))))))

(def-fns _ $ (many find-template : (subterm many (List $ Template) ts) (many (String) kind) (many (String) type) (many (Nat) index) -> (many (Maybe $ List $ Piece) r))
  (match many ts _
    ((Nil _) (None _))
    ((Cons _ t rest)
      (match many t _
        ((MkTemplate b ty i ps)
          (match many (and (str-eq b kind) $ and (str-eq ty type) $ nat-eq i index) _
            ((BTrue) (Some _ ps))
            ((BFalse) (tail $ find-template rest kind type index))))))))

(def-fns _ $ (many str-is-name : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (or (char-is c 95) $ or (char-is c 39) $ or (char-between c 48 57) $ or (char-between c 97 122) $ char-between c 65 90) $ notail $ str-is-name rest))))

(def-fns _ $ (many rope-is-name : (many (Rope) r) -> (many (Bool) b))
  (let ((many s)) $ rope-str r)
  (and (not $ str-is-empty s) $ str-is-name s))

(def-adts $ (Decls : -> Type)
  enum
  (many MkDecls : (many (List $ List $ Nat) shape-list) (many (List $ Narrow) narrows) (many (List $ Template) templates) -> (Decls)))

(def-fns _ $ (many decl-templates : (many (Decls) d) -> (many (List $ Template) ts))
  (match many d _ ((MkDecls _ _ ts) ts)))

(def-fns _ $ (many decl-call-template : (many (Decls) d) (many (Nat) id) (many (List $ Piece) ps) -> (many (Decls) r))
  (match many d _ ((MkDecls shapes2 narrows ts) (MkDecls shapes2 narrows $ Cons _ (MkTemplate "call" "" id ps) ts))))

(def-fns _ $ (many decl-shape-index : (subterm many (List $ List $ Nat) ss) (many (List $ Nat) s) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (match many ss _
    ((Nil _) (None _))
    ((Cons _ x rest) (match many (nat-list-eq x s) _ ((BTrue) (Some _ i)) ((BFalse) (tail $ decl-shape-index rest s $ Succ i))))))

(def-fns _ $ (many narrow-index : (subterm many (List $ Narrow) ns) (many (List $ Nat) s) (many (List $ Nat) live) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (match many ns _
    ((Nil _) (None _))
    ((Cons _ n rest)
      (match many n _
        ((MkNarrow s2 live2) (match many (and (nat-list-eq s2 s) $ nat-list-eq live2 live) _ ((BTrue) (Some _ i)) ((BFalse) (tail $ narrow-index rest s live $ Succ i))))))))

(def-fns _ $ (many index-str : (many (Maybe $ Nat) i) -> (many (String) s))
  (match many i _ ((Some _ n) (nat-str n)) ((None _) "missing")))

(def-fns _ $ (many shape-name : (many (Decls) d) (many (List $ Nat) s) -> (many (String) r))
  (match many d _ ((MkDecls shapes2 _ _) (str-cat "t" $ index-str $ decl-shape-index shapes2 s 0))))

(def-fns _ $ (many ctor-name-at : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) -> (many (String) r))
  (match many d _ ((MkDecls shapes2 _ _) (str-cat3 "K" (index-str $ decl-shape-index shapes2 s 0) $ str-cat "_" $ nat-str i))))

(def-fns _ $ (many narrow-name : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (String) r))
  (match many d _ ((MkDecls _ narrows _) (str-cat3 (shape-name d s) "_n" $ index-str $ narrow-index narrows s live 0))))

(def-fns _ $ (many add-shape : (many (List $ List $ Nat) ss) (many (List $ Nat) s) -> (many (List $ List $ Nat) r))
  (match many (decl-shape-index ss s 0) _
    ((Some _ _) ss)
    ((None _) (let ((many r) (erased p)) $ list-append _ ss $ Cons _ s $ Nil _) r)))

(def-fns _ $ (many decl-shape : (many (Decls) d) (many (List $ Nat) s) -> (many (Decls) r))
  (match many d _ ((MkDecls shapes2 narrows ts) (MkDecls (add-shape shapes2 s) narrows ts))))

(def-fns _ $ (many decl-narrow : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) -> (many (Decls) r))
  (match many d _
    ((MkDecls shapes2 narrows ts)
      (match many (narrow-index narrows s live 0) _
        ((Some _ _) d)
        ((None _)
          (let ((many r) (erased p)) $ list-append _ narrows $ Cons _ (MkNarrow s live) $ Nil _)
          (MkDecls (add-shape shapes2 s) r ts))))))

(def-fns _ $ (many nat-insert : (many (Nat) x) (subterm many (List $ Nat) xs) -> (many (List $ Nat) r))
  (match many xs _
    ((Nil _) (Cons _ x $ Nil _))
    ((Cons _ y rest)
      (match many (nat-cmp x y) _
        ((CLt _ _ _ _ _) (Cons _ x xs))
        ((CEq _ _ _) xs)
        ((CGt _ _ _ _ _) (Cons _ y $ notail $ nat-insert x rest))))))

; The key of a narrowing: the live discriminants sorted, each once.
(def-fns _ $ (many live-key : (subterm many (List $ Nat) live) -> (many (List $ Nat) r))
  (match many live _
    ((Nil _) (Nil _))
    ((Cons _ x rest) (nat-insert x $ notail $ live-key rest))))

(def-fns _ $ (many adt-shape : (many (Adt) adt) -> (many (List $ Nat) r))
  (ctor-arities $ adt-ctors adt))

; Whether the live set leaves a constructor out, so the match is on a narrowed copy of the shape.
(def-fns _ $ (many narrowed : (many (Adt) adt) (many (List $ Nat) live) -> (many (Bool) r))
  (nat-lt (list-length _ $ live-key live) $ list-length _ $ adt-ctors adt))

; ---- Constructing, taking apart, and the runtime forms of constructors and Matchables


(def-fns _ $ (many record-fields : (subterm many (List $ Rope) fs) (many (Nat) i) -> (many (List $ Rope) r))
  (match many fs _
    ((Nil _) (Nil _))
    ((Cons _ f rest) (Cons _ (rcat3 (RStr $ str-cat3 "f" (nat-str i) " = ") f $ REmpty) $ notail $ record-fields rest $ Succ i))))

(def-fns _ $ (many record-types : (subterm many (Nat) count) (many (Nat) i) -> (many (List $ Rope) r))
  (match many count _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (RStr $ str-cat3 "mutable f" (nat-str i) " : Obj.t") $ notail $ record-types k $ Succ i))))

(def-fns _ $ (many pattern-rope : (many (Decls) d) (many (List $ Nat) s) (many (Nat) i) (many (List $ Rope) fs) -> (many (Rope) r))
  (match many fs _
    ((Nil _) (RStr $ ctor-name-at d s i))
    ((Cons _ _ _) (rcat3 (RStr $ str-cat (ctor-name-at d s i) " { ") (rjoin (record-fields fs 0) "; ") $ RStr " }"))))

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
  (match many arms _
    ((Nil _) (None _))
    ((Cons _ arm rest) (match many arm _ ((MkArm d _ _) (match many (nat-eq d i) _ ((BTrue) (Some _ arm)) ((BFalse) (tail $ arm-at rest i))))))))

(def-fns _ $ (many nat-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (match many xs _
    ((Nil _) (BFalse))
    ((Cons _ y rest) (or (nat-eq x y) $ notail $ nat-mem rest x))))

(def-fns _ $ (many fill-hole : (many (Filling) f) (many (Hole) h) -> (many (Rope) r))
  (match many f _
    ((MkFilling scrut prefix arms live dflt args)
      (match many h _
        ((HScrut) (RStr scrut))
        ((HTemp k) (RStr $ str-cat3 prefix "_t" $ nat-str k))
        ((HArg i) (list-nth-or _ args i $ RStr "(absurd ())"))
        ((HBody i)
          (match many (arm-at arms i) _
            ((Some _ arm) (match many arm _ ((MkArm _ _ body) body)))
            ((None _) (match many (nat-mem live i) _ ((BTrue) dflt) ((BFalse) (RStr "(absurd ())"))))))
        ((HField i j)
          (match many (arm-at arms i) _
            ((Some _ arm) (match many arm _ ((MkArm _ fs _) (list-nth-or _ fs j $ RStr "_"))))
            ((None _) (RStr $ str-cat3 prefix "_f" $ str-cat3 (nat-str i) "_" $ nat-str j))))))))

(def-fns _ $ (many fill-pieces : (subterm many (List $ Piece) ps) (many (Filling) f) -> (many (Rope) r))
  (match many ps _
    ((Nil _) (REmpty))
    ((Cons _ p rest)
      (rcat (match many p (((Rope) _)) ((PLit s) (RStr s)) ((PHole h) (fill-hole f h))) $ notail $ fill-pieces rest f))))

; Each build argument as the name the template reads: its own when it is one, else a temporary bound to it.
(def-fns _ $ (many bind-args : (many (String) prefix) (subterm many (List $ Rope) args) (many (Nat) i) -> (many (List $ Rope) names) (many (List $ Rope) binds))
  (match many args _
    ((Nil _) (values (Nil _) (Nil _)))
    ((Cons _ arg rest)
      (let ((many names) (many binds)) (notail $ bind-args prefix rest (Succ i)))
      (match many (rope-is-name arg) _
        ((BTrue) (values (Cons _ arg names) binds))
        ((BFalse)
          (let ((many x)) $ str-cat3 prefix "_a" $ nat-str i)
          (values (Cons _ (RStr x) names) $ Cons _ (rcat (RStr $ str-cat x " = ") arg) binds))))))

(def-fns _ $ (many templated-build : (many (List $ Piece) ps) (many (Nat) depth) (many (List $ Rope) args) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "x" $ nat-str depth)
  (let ((many names) (many binds)) (bind-args prefix args 0))
  (let ((many text)) $ fill-pieces ps $ MkFilling "" prefix (Nil _) (Nil _) (REmpty) names)
  (match many binds _
    ((Nil _) (rcat3 (RStr "(") text $ RStr ")"))
    ((Cons _ _ _) (rcat5 (RStr "(let ") (rjoin binds " in let ") (RStr " in ") text $ RStr ")"))))

; How many of the constructors from i on the default stands for: those live with no arm of their own.
(def-fns _ $ (many count-defaulted : (subterm many (Nat) n) (many (Nat) i) (many (List $ Arm) arms) (many (List $ Nat) live) -> (many (Nat) r))
  (match many n _
    ((Zero) 0)
    ((Succ k)
      (let ((many rest)) $ notail $ count-defaulted k (Succ i) arms live)
      (match many (and (nat-mem live i) $ match many (arm-at arms i) (((Bool) _)) ((None _) (BTrue)) ((Some _ _) (BFalse))) _
        ((BTrue) (Succ rest))
        ((BFalse) rest)))))

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
  (let ((many (String) name) (many (Rope) bind-open) (many (Rope) bind-close))
    (match many (rope-is-name scrut0) _
      ((BTrue) (values (rope-str scrut0) (REmpty) (REmpty)))
      ((BFalse) (values prefix (rcat3 (RStr $ str-cat3 "(let " prefix " = ") scrut0 $ RStr " in ") (RStr ")")))))
  (let ((many text)) $ fill-pieces ps $ MkFilling name prefix arms live dr (Nil _))
  (rcat5 bind-open open (rcat3 (RStr "(") text $ RStr ")") close bind-close))

(def-fns _ $ (many block-build : (many (Decls) d) (many (List $ Rope) fields) -> (many (Rope) r))
  (rcat3 (RStr "(Obj.repr (") (pattern-rope d (Cons _ (list-length _ fields) $ Nil _) 0 fields) $ RStr "))"))

(def-fns _ $ (many plain-build : (many (Decls) d) (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r))
  (match many (ctor-newtype c) _
    ((BTrue) (tuple-rope args))
    ((BFalse) (match many (ctor-tagged c) _
      ((BTrue) (rcat3 (RStr "(Obj.repr (") (pattern-rope d (ctor-shape c) (ctor-index c) args) $ RStr "))"))
      ((BFalse) (block-build d args))))))

(def-fns _ $ (many build-rope : (many (Decls) d) (many (Nat) depth) (many (Ctor) c) (many (List $ Rope) args) -> (many (Rope) r))
  (match many c _
    ((MkCtor _ _ index _ _ ext shape _)
      (match many ext _
        ((Some _ e)
          (match many (find-template (decl-templates d) "build" (ext-type-name e) index) _
            ((Some _ ps) (templated-build ps depth args))
            ((None _) (rcat3 (RStr $ str-cat3 "(con_" (ext-type-name e) " (Obj.repr (") (pattern-rope d shape index args) $ RStr ")))"))))
        ((None _)
          (plain-build d c args))))))

(def-fns _ $ (many ctor-fn-rope : (many (Decls) d) (many (Ctor) c) -> (many (Rope) r))
  (let ((many fs)) $ field-names (ctor-arity c) 0)
  (rcat5 (RStr "(Obj.repr (fun ") (params-rope fs) (RStr " -> ") (build-rope d 0 c fs) $ RStr "))"))

(def-fns _ $ (many tagged-arms : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Arm) arms) -> (many (Rope) r))
  (match many arms _
    ((Nil _) (REmpty))
    ((Cons _ arm rest) (match many arm _ ((MkArm i fs body) (rcat5 (RStr "| ") (pattern-rope d s i fs) (RStr " -> ") body $ rcat (RStr " ") $ notail $ tagged-arms d s rest))))))

(def-fns _ $ (many default-rope : (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (match many dflt _ ((Some _ d) d) ((None _) (RStr "(absurd ())"))))

; A match over an ADT's constructors (lib/extract.ml's dispatch): an extern value unwrapped one level first;
; a direct match for a tagged type, on the copy narrowed to the live constructors when some are refuted, so
; that OCaml tests nothing for them; the fields as they stand for an untagged one.
(def-fns _ $ (many block-dispatch : (many (Decls) d) (many (Rope) scrut) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (match many arms _
    ((Nil _) (default-rope dflt))
    ((Cons _ arm _)
      (match many arm _
        ((MkArm _ fs body)
          (let ((many shape)) $ Cons _ (list-length _ fs) $ Nil _)
          (rcat5 (RStr "(match (Obj.obj ") scrut (RStr $ str-cat3 " : " (shape-name d shape) ") with ")
            (rcat3 (pattern-rope d shape 0 fs) (RStr " -> ") body) $ RStr ")"))))))

(def-fns _ $ (many dispatch-rope : (many (Decls) d) (many (Nat) depth) (many (Adt) adt) (many (List $ Nat) live) (many (Rope) scrut0) (many (List $ Arm) arms) (many (Maybe $ Rope) dflt) -> (many (Rope) r))
  (match many (match many (adt-ext adt) (((Maybe $ List $ Piece) _)) ((None _) (None _)) ((Some _ e) (find-template (decl-templates d) "match" (ext-type-name e) 0))) _
    ((Some _ ps) (templated-dispatch ps depth (list-length _ $ adt-ctors adt) live scrut0 arms dflt))
    ((None _)
      (let ((many scrut)) $ match many (adt-ext adt) (((Rope) _)) ((None _) scrut0) ((Some _ e) (rcat3 (RStr $ str-cat3 "(des_" (ext-type-name e) " ") scrut0 $ RStr ")")))
      (match many (and (adt-tagged adt) $ not $ adt-newtype adt) _
        ((BTrue)
          (let ((many shape)) $ adt-shape adt)
          (let ((many ty)) $ match many (narrowed adt live) (((String) _)) ((BTrue) (str-cat "yes " $ narrow-name d shape $ live-key live)) ((BFalse) (shape-name d shape)))
          (let ((many inner))
            (match many arms (((Rope) _))
              ((Nil _) (match many dflt (((Rope) _)) ((None _) (RStr "| _ -> .")) ((Some _ dr) (rcat (RStr "| _ -> ") dr))))
              ((Cons _ _ _) (rcat (tagged-arms d shape arms) $ match many dflt (((Rope) _)) ((None _) (REmpty)) ((Some _ dr) (rcat (RStr "| _ -> ") dr))))))
          (rcat5 (RStr "(match (Obj.obj ") scrut (RStr $ str-cat3 " : " ty ") with ") inner $ RStr ")"))
        ((BFalse)
          (match many (adt-newtype adt) _
            ((BFalse) (block-dispatch d scrut arms dflt))
            ((BTrue) (match many arms _ ((Nil _) (default-rope dflt)) ((Cons _ arm _) (match many arm _ ((MkArm _ fs body) (untuple-rope fs scrut body))))))))))))

; What an arm over a whole ADT does with a constructor's fields: wraps them in Some for one constructor and
; None for the rest, takes the first, or makes the driver's request of them.
(def-adts $ (ArmKind : -> Type)
  enum
  (many AkOption : (many (String) cname) -> (ArmKind))
  (many AkField : -> (ArmKind))
  (many AkRequest : -> (ArmKind)))

(def-fns _ $ (many arm-body : (many (Decls) d) (many (ArmKind) k) (many (Ctor) c) (many (List $ Rope) fs) -> (many (Rope) r))
  (match many k _
    ((AkOption cname)
      (match many (str-cmp (ctor-name c) cname) _
        ((CEq _ _ _) (rcat3 (RStr "(Some (") (commas fs) $ RStr "))"))
        (else (RStr "None"))))
    ((AkField) (match many fs _ ((Nil _) (RStr "(absurd ())")) ((Cons _ f _) f)))
    ((AkRequest) (rcat3 (RStr $ str-cat3 "(Driver_core." (ctor-name c) " (") (commas fs) $ RStr "))"))))

(def-fns _ $ (many ctor-arms : (many (Decls) d) (subterm many (List $ Ctor) cs) (many (ArmKind) k) -> (many (List $ Arm) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest)
      (let ((many fs)) $ field-names (ctor-arity c) 0)
      (Cons _ (MkArm (ctor-index c) fs $ arm-body d k c fs) $ notail $ ctor-arms d rest k))))

(def-fns _ $ (many all-live : (many (Adt) adt) -> (many (List $ Nat) r))
  (nat-range (list-length _ $ adt-ctors adt) 0))

; A Matchable at runtime: the identity for a plain type, for an extern type the FFI's unwrap into the shape
; its constructors describe, which a held match then matches on directly.
(def-fns _ $ (many held-arms : (subterm many (List $ Ctor) cs) (many (Decls) d) -> (many (List $ Arm) r))
  (match many cs _
    ((Nil _) (Nil _))
    ((Cons _ c rest)
      (let ((many fs)) $ field-names (ctor-arity c) 0)
      (Cons _ (MkArm (ctor-index c) fs $ plain-build d c fs) $ notail $ held-arms rest d))))

(def-fns _ $ (many matchable-rope : (many (Adt) adt) (many (Decls) d) -> (many (Rope) r))
  (match many (adt-ext adt) _
    ((None _) (RStr "m_plain"))
    ((Some _ _) (rcat3 (RStr "(Obj.repr (fun held -> ") (dispatch-rope d 0 adt (all-live adt) (RStr "held") (held-arms (adt-ctors adt) d) $ None _) $ RStr "))"))))

(def-fns _ $ (many payload-rope : (many (Payload) p) -> (many (Rope) r))
  (match many p _
    ((PNat n) (nat-literal n))
    ((PHalf n) (nat-literal n))
    ((PStr s)
      (let ((many n) (erased _)) (str-length s))
      (rcat5 (RStr "(Obj.repr ((") (quoted s) (RStr ", 0, ") (nat-rope n) $ RStr ") : Ffi_core.slice))"))))

; ---- Names for the frames code binds: one per id, in step with the frames (ASSUMPTIONS 127); a function
; bound by a group is named, so a call of it is direct, a value use its closure.

(def-adts $ (Named : -> Type)
  enum
  (many NmVal : (many (Rope) r) -> (Named))
  (many NmFn : (many (String) name) (many (Nat) id) -> (Named))
  (many NmConst : (many (Nat) id) -> (Named)))

(def-adts $ (Names : ((List $ List $ Nat) ctx) -> Type)
  enum
  (many NmNil : -> (Names (Nil (List (Nat)))))
  (many NmFrame : (erased (List $ List $ Nat) ctx) (many (List $ Nat) f) (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) f rs) lk) (many (Names ctx) rest) -> (Names (Cons (List (Nat)) f ctx))))

(def-fns _ $ (many names-depth : (erased (List $ List $ Nat) ctx) (subterm many (Names ctx) ns) -> (many (Nat) n))
  (match many ns _
    ((NmNil) 0)
    ((NmFrame _ _ _ _ rest) (Succ $ notail $ names-depth _ rest))))

(def-fns _ $ (many names-get : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (many (Names ctx) ns) -> (many (Named) r))
  (match many p _
    ((MHere _ _ _ q)
      (let-match many ns (NmFrame c2 f2 rs lk rest))
      (let ((many r) (erased sq)) $ at-get _ _ _ q rs lk) r)
    ((MThere _ _ _ q)
      (let-match many ns (NmFrame c2 f2 rs lk rest))
      (tail $ names-get _ _ q rest))))

(def-fns _ $ (many target-named : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) c) (many (Names ctx) ns) -> (many (Named) r))
  (match many c _
    ((CVar _ _ p) (names-get _ _ p ns))
    ((CConst _ t) (NmConst t))
    (else (NmVal $ RStr "(failwith \"internal: an alias with no target\")"))))

(def-fns _ $ (many alias-named : (erased (List $ List $ Nat) ctx) (erased (List $ Nat) all) (many (Names (Cons (List (Nat)) all ctx)) whole) (erased (List $ Nat) f) (subterm many (List $ Named) rs) (erased (Lockstep (Nat) (Named) f rs) lk) (many (List $ Pair (Nat) $ Func all ctx) fns) -> (many (List $ Named) rs2) (erased (Lockstep (Nat) (Named) f rs2) lk2))
  (match many rs _
    ((Nil _)
      (let-match erased lk (LsNil ta tb))
      (values (Nil _) (LsNil _ _)))
    ((Cons _ r rest)
      (let-match erased lk (LsCons ta tb x y xs ys p))
      (let ((many (Named) r2) (many (List $ Pair (Nat) $ Func all ctx) more))
        (match many fns _
          ((Nil _) (values r fns))
          ((Cons _ pr fr)
            (match many pr _
              ((MkPair _ _ _ fn)
                (match many fn _
                  ((MkFunc _ _ _ _ _ _ _ _ _) (values r fr))
                  ((MkAlias _ _ _ _ target) (values (target-named _ target whole) fr))))))))
      (let ((many rs3) (erased lk3)) $ notail $ alias-named _ _ whole _ rest p more)
      (values (Cons _ r2 rs3) (LsCons _ _ x r2 xs rs3 lk3)))))

(def-fns _ $ (many group-names : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (List $ Pair (Nat) $ Func ids ctx) fns) (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) ids rs) lk) (many (Names ctx) rest) -> (many (Names (Cons (List (Nat)) ids ctx)) r))
  (let ((many rs2) (erased lk2)) $ alias-named _ _ (NmFrame _ ids rs lk rest) _ rs lk fns)
  (NmFrame _ ids rs2 lk2 rest))

(def-fns _ $ (many addr-str : (erased (Hist Block) a) (many (Ref Block a) addr) -> (many (String) r))
  (str-cat "a" $ nat-str $ ref-pos Block _ addr))

(def-fns _ $ (many addr-rope : (erased (Hist Block) a) (many (Ref Block a) addr) -> (many (Rope) r))
  (RStr $ addr-str _ addr))

; The OCaml name of a group's member: its entry's name qualified by the group's address, since a group
; allocated twice is emitted twice.
(def-fns _ $ (many member-name : (erased (Hist Block) a) (many (Env) env) (many (Nat) id) (many (Ref Block a) g) -> (many (String) r))
  (str-cat3 (top-name env id) "_" $ addr-str _ g))

(def-fns _ $ (many top-names : (subterm many (List $ Nat) ids) (many (Env) env) (many (Maybe $ String) suffix) -> (many (List $ Named) r) (erased (Lockstep (Nat) (Named) ids r) lk))
  (match many ids _
    ((Nil _) (values (Nil _) (LsNil _ _)))
    ((Cons _ x rest)
      (let ((many rs) (erased lk)) $ notail $ top-names rest env suffix)
      (let ((many (Named) r)) $ match many suffix _ ((None _) (NmVal $ RStr $ top-name env x)) ((Some _ s) (NmFn (str-cat (top-name env x) s) x)))
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ (many push-names : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (Env) env) (many (Names ctx) ns) -> (many (Names (Cons (List (Nat)) ids ctx)) r))
  (let ((many rs) (erased lk)) $ top-names ids env $ None _)
  (NmFrame _ ids rs lk ns))

(def-fns _ $ (many push-fn-names : (erased (List $ List $ Nat) ctx) (many (List $ Nat) ids) (many (List $ Pair (Nat) $ Func ids ctx) fns) (many (Env) env) (many (String) suffix) (many (Names ctx) ns) -> (many (Names (Cons (List (Nat)) ids ctx)) r))
  (let ((many rs) (erased lk)) $ top-names ids env $ Some _ suffix)
  (group-names _ ids fns rs lk ns))

(def-fns _ $ (many addr-ropes : (erased (Hist Block) a) (subterm many (List $ Ref Block a) vs) -> (many (List $ Rope) rs))
  (match many vs _
    ((Nil _) (Nil _))
    ((Cons _ v rest) (Cons _ (addr-rope _ v) $ notail $ addr-ropes _ rest))))

(def-fns _ $ (many const-rope : (many (Env) env) (many (Nat) x) -> (many (Rope) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store env)
  (match many (idmap-get _ x en) _
    ((Miss _ _ _ _) (RStr "(failwith \"unbound constant\")"))
    ((Hit _ _ _ info _)
      (match many info _
        ((MkEInfo _ _ _ s _ _ _) (match many s _ ((SDyn _) (RStr "(failwith \"a Dyn constant\")")) ((SConst _ v) (addr-rope _ v))))))))

(def-fns _ $ (many named-rope : (many (Named) n) (many (Env) env) -> (many (Rope) r))
  (match many n _
    ((NmVal r) r)
    ((NmFn name _) (RStr $ str-cat3 "(Obj.repr " name ")"))
    ((NmConst x) (const-rope env x))))

; The names of a group block's captured frames: an address's block by name, a group's members by theirs.
(def-fns _ $ (many frame-named : (erased (Hist Block) a) (erased (List $ Nat) f) (subterm many (List $ Ref Block a) vs) (erased (Lockstep (Nat) (Ref Block a) f vs) lk) -> (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) f rs) lk2))
  (match many vs _
    ((Nil _)
      (let-match erased lk (LsNil ta tb))
      (values (Nil _) (LsNil _ _)))
    ((Cons _ v rest)
      (let-match erased lk (LsCons ta tb x y xs ys p))
      (let ((many rs) (erased lk2)) $ notail $ frame-named _ _ rest p)
      (let ((many r)) $ NmVal $ addr-rope _ v)
      (values (Cons _ r rs) (LsCons _ _ x r xs rs lk2)))))

(def-fns _ $ (many member-named : (erased (Hist Block) a) (subterm many (List $ Nat) gids) (many (Env) env) (many (Ref Block a) g) -> (many (List $ Named) rs) (erased (Lockstep (Nat) (Named) gids rs) lk))
  (match many gids _
    ((Nil _) (values (Nil _) (LsNil _ _)))
    ((Cons _ x rest)
      (let ((many rs) (erased lk)) $ notail $ member-named _ rest env g)
      (let ((many r)) $ NmFn (member-name _ env x g) x)
      (values (Cons _ r rs) (LsCons _ _ x r rest rs lk)))))

(def-fns _ $ (many frame-names : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (subterm many (Frames (Ref Block a) ctx) fr) (many (Env) env) -> (many (Names ctx) r))
  (match many fr _
    ((FrNil _) (NmNil))
    ((FrVals _ _ f vs lk rest)
      (let ((many rs) (erased lk2)) $ frame-named _ _ vs lk)
      (NmFrame _ f rs lk2 $ notail $ frame-names _ _ rest env))
    ((FrGroup _ _ gids g grp rest)
      (let ((many rs) (erased lk2)) $ member-named _ gids env g)
      (match many grp _ ((MkGroup _ _ fns _) (group-names _ gids fns rs lk2 $ notail $ frame-names _ _ rest env))))))

; ---- The head of a call: a constructor the elaborator saw, a function with an OCaml name, or a value.

(def-adts $ (Head : -> Type)
  enum
  (many HCtor : (many (Ctor) c) -> (Head))
  (many HFn : (many (String) name) (many (Nat) id) -> (Head))
  (many HDyn : -> (Head)))

(def-fns _ $ (many block-head : (erased (Hist Block) a) (many (Block (Ref Block a)) b) (many (Env) env) -> (many (Head) h))
  (match many b _
    ((BCtorFn _ c) (HCtor c))
    ((BFn _ g _ id) (HFn (member-name _ env id g) id))
    (else (HDyn))))

(def-fns _ $ (many const-head : (many (Env) env) (many (Nat) x) -> (many (Head) h))
  (let ((erased a) (many blk)) $ env-block env x)
  (match many blk _ ((None _) (HDyn)) ((Some _ b) (block-head _ b env))))

(def-fns _ $ (many head-of : (erased (List $ List $ Nat) ctx) (many (Code ctx many-one) f) (many (Env) env) (many (Names ctx) ns) -> (many (Head) h))
  (match many f _
    ((CVar _ _ p) (match many (names-get _ _ p ns) _ ((NmFn name id) (HFn name id)) ((NmConst x) (const-head env x)) ((NmVal _) (HDyn))))
    ((CConst _ x) (const-head env x))
    ((CValue _ v) (block-head _ v env))
    (else (HDyn))))

; The prelude's ADT of a type name.
; The prelude's names are found in its scope, as lib/program.ml's driver finds them, however the program
; shadows them.
(def-fns _ $ (many prelude-adt : (many (Env) env) (many (String) name) -> (many (Maybe $ Adt) r))
  (let ((many env2) (many ty)) $ prelude-type (env-set-scope env $ env-prelude env) name)
  (type-adt env2 ty))

(def-fns _ $ (many prelude-ctor : (many (Env) env) (many (String) name) -> (many (Maybe $ Ctor) r))
  (let ((many env2) (many x)) $ prelude-id (env-set-scope env $ env-prelude env) name)
  (ctor-of env2 x))

(def-fns _ $ (many ffi-arms : (subterm many (List $ Ctor) ctors) -> (many (List $ Arm) r))
  (match many ctors _
    ((Nil _) (Nil _))
    ((Cons _ ctor rest)
      (let ((many fields)) $ field-names (ctor-arity ctor) 0)
      (let ((many body)) $ match many fields (((Rope) _)) ((Nil _) (RStr $ str-cat "Ffi_core." $ ctor-name ctor)) ((Cons _ _ _) (rcat3 (RStr $ str-cat3 "(Ffi_core." (ctor-name ctor) " (") (commas fields) $ RStr "))")))
      (Cons _ (MkArm (ctor-index ctor) fields body) $ notail $ ffi-arms rest))))

(def-fns _ $ (many ffi-view : (many (String) label) (many (String) tname) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many (prelude-adt env tname) _
    ((None _) (REmpty))
    ((Some _ adt)
      (rcat5 (RStr "~") (RStr label) (RStr ":(fun v -> ") (dispatch-rope d 0 adt (all-live adt) (RStr "v") (ffi-arms $ adt-ctors adt) $ None _) $ RStr ") "))))

(def-fns _ $ (many ffi-extra : (many (String) name) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many (str-eq name "flatten") _
    ((BTrue) (rcat (ffi-view "rope" "Rope" env d) $ RStr "~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr "))
    ((BFalse)
      (match many (str-eq name "list-to-array") _
        ((BTrue) (ffi-view "list" "List" env d))
        ((BFalse) (match many (str-eq name "array-new") _ ((BTrue) (RStr "~blank:(Obj.repr ()) ")) ((BFalse) (REmpty))))))))

(def-fns _ $ (many objs : (subterm many (List $ Rope) ps) -> (many (List $ Rope) r))
  (match many ps _
    ((Nil _) (Nil _))
    ((Cons _ p rest) (Cons _ (rcat3 (RStr "(Obj.obj ") p $ RStr ")") $ notail $ objs rest))))

(def-fns _ $ (many ffi-call : (many (String) name) (many (List $ Rope) params) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many (find-template (decl-templates d) "fn" name 0) _
    ((Some _ ps) (templated-build ps 0 params))
    ((None _) (rcat5 (RStr "(Obj.repr (Ffi_core.") (RStr $ sanitize name) (rcat (RStr " ") $ ffi-extra name env d) (rjoin (objs params) " ") $ RStr "))"))))



(def-fns _ $ (many cell-view : (many (Decls) d) (many (Ctor) c) -> (many (String) ty) (many (String) k))
  (match many (ctor-tagged c) _
    ((BTrue)
      (let ((many shape)) $ ctor-shape c)
      (let ((many k)) $ ctor-name-at d shape $ ctor-index c)
      (match many (nat-lt (Succ (Zero)) $ list-length _ shape) (((String) _) ((String) k2))
        ((BTrue) (values (str-cat "yes " $ narrow-name d shape $ live-key $ Cons _ (ctor-index c) $ Nil _) k))
        ((BFalse) (values (shape-name d shape) k))))
    ((BFalse)
      (let ((many shape)) $ Cons _ (ctor-arity c) $ Nil _)
      (values (shape-name d shape) $ ctor-name-at d shape (Zero)))))

(def-fns _ $ (many field-writes : (subterm many (List $ Nat) indices) (many (List $ Rope) args) (many (String) r) -> (many (List $ Rope) ws))
  (match many indices _
    ((Nil _) (Nil _))
    ((Cons _ i rest)
      (match many args _
        ((Nil _) (Nil _))
        ((Cons _ arg more)
          (Cons _ (rcat3 (RStr $ str-cat3 r ".f" $ nat-str i) (RStr " <- ") arg) $ notail $ field-writes rest more r))))))

(def-fns _ $ (many field-match-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (String) r) -> (many (Rope) w))
  (let ((many ty) (many k)) $ cell-view d c)
  (rcat3 (RStr "(match (Obj.obj ") target $ RStr $ str-cat3 " : " ty $ str-cat3 ") with " k $ str-cat3 " " r " -> "))

(def-fns _ $ (many field-store-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (List $ Nat) indices) (many (List $ Rope) args) (many (String) r) -> (many (Rope) w))
  (rcat3 (field-match-rope d c target r) (rjoin (field-writes indices args r) "; ") $ RStr ")"))

(def-fns _ $ (many field-read-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) target) (many (Nat) index) (many (String) r) -> (many (Rope) w))
  (rcat3 (field-match-rope d c target r) (RStr $ str-cat3 r ".f" $ nat-str index) $ RStr ")"))

(def-fns _ $ (many cell-write-rope : (many (Decls) d) (many (Ctor) c) (many (Rope) cell) (many (List $ Nat) indices) (many (List $ Rope) args) (many (Nat) depth) -> (many (Rope) r))
  (let ((many prefix)) $ str-cat "cell" $ nat-str depth)
  (let ((many cr)) $ RStr prefix)
  (let ((many names) (many binds)) $ bind-args prefix args 0)
  (let ((many stores)) $ match many indices (((Rope) _))
    ((Nil _) cr)
    ((Cons _ _ _) (rcat3 (field-store-rope d c cr indices names $ str-cat prefix "_r") (RStr "; ") cr)))
  (let ((many body)) $ match many binds (((Rope) _)) ((Nil _) stores) ((Cons _ _ _) (rcat5 (RStr "(let ") (rjoin binds " in let ") (RStr " in ") stores $ RStr ")")))
  (rcat5 (RStr "(let ") cr (rcat3 (RStr " = ") cell $ RStr " in ") body $ RStr ")"))

; ---- Code and blocks as OCaml; every piece recurses on the piece it writes.

(def-fns _
  ((many emit-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (Rope) r))
    (match many code _
      ((CVar _ _ p) (named-rope (names-get _ _ p ns) env))
      ((CConst _ x) (const-rope env x))
      ((CValue _ v) (tail $ block-rope _ v env d))
      ((CErased _ _) (RStr "(Obj.repr ())"))
      ((CValues _ _ cs _) (tuple-rope $ notail $ emit-codes _ cs env ns d))
      ((CApp _ _ f args _)
        (let ((many ars)) $ notail $ emit-codes _ args env ns d)
        (match many (head-of _ f env ns) _
          ((HCtor c) (build-rope d (names-depth _ ns) c ars))
          ((HFn name id)
            (match many (find-template (decl-templates d) "call" "" id) _
              ((Some _ ps) (templated-build ps (names-depth _ ns) ars))
              ((None _) (rcat3 (RStr $ str-cat "(" name) (rcat (RStr " ") $ args-rope ars) $ RStr ")"))))
          ((HDyn)
            (let ((many fr)) $ notail $ emit-code _ _ f env ns d)
            (dyn-call fr ars))))
      ((CLet _ _ _ ids _ rhs rest)
        (let ((many rr)) $ notail $ emit-code _ _ rhs env ns d)
        (let ((many body)) $ notail $ emit-code _ _ rest env (push-names _ ids env ns) d)
        (match many ids _
          ((Nil _) (rcat5 (RStr "(let _ = ") rr (RStr " in ") body $ RStr ")"))
          ((Cons _ _ _) (untuple-rope (names-of-ids ids env) rr body))))
      ((CLetRec _ ns2 _ g rest)
        (match many g _
          ((MkGroup _ ids fns _)
            (let ((many ns3)) $ push-fn-names _ ids fns env "" ns)
            (match many (notail $ emit-group _ _ fns env ns3 d "") _
              ((Nil _) (tail $ emit-code _ _ rest env ns3 d))
              ((Cons _ f1 more) (rcat5 (RStr "(let rec ") (rjoin (Cons _ f1 more) "\nand ") (RStr " in ") (notail $ emit-code _ _ rest env ns3 d) $ RStr ")"))))))
      ((CMatch _ _ scrut shape branches dfl live)
        (let ((many sr)) $ notail $ emit-code _ _ scrut env ns d)
        (let ((many (Maybe $ Rope) dr)) (match many dfl _ ((None _) (None _)) ((Some _ dd) (Some _ $ notail $ emit-code _ _ dd env (push-names _ (Nil _) env ns) d))))
        (let ((many arms)) $ notail $ emit-arms _ _ branches env ns d)
        (match many shape _
          ((ShKnown _ adt) (dispatch-rope d (names-depth _ ns) adt live sr arms dr))
          ((ShHeld _ mcode adt)
            (let ((many mr)) $ notail $ emit-code _ _ mcode env ns d)
            (let ((many sr2)) $ rcat5 (RStr "((Obj.obj ") mr (RStr " : Obj.t -> Obj.t) ") sr $ RStr ")")
            (dispatch-rope d (names-depth _ ns) adt live sr2 arms dr))
          ((ShNone _) (default-rope dr))))

      ((CCellAlloc _ ctor slots) (plain-build d ctor $ notail $ emit-codes _ slots env ns d))
      ((CCellWrite _ k2 cell slots)
        (let ((many indices) (many args)) $ notail $ emit-slots _ slots env ns d)
        (cell-write-rope d k2 (notail $ emit-code _ _ cell env ns d) indices args $ names-depth _ ns))
      ((CCellRead _ k2 index cell)
        (field-read-rope d k2 (notail $ emit-code _ _ cell env ns d) index $ str-cat3 "cell" (nat-str $ names-depth _ ns) "_r"))
      ((CAbsurd _ _) (RStr "(absurd ())"))
      ((CError _ _ m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")"))))

  ((many emit-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (List $ Rope) rs))
    (match many cs _
      ((Nil _) (Nil _))
      ((Cons _ c rest) (Cons _ (notail $ emit-code _ _ c env ns d) $ notail $ emit-codes _ rest env ns d))))


  ((many emit-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (List $ Nat) indices) (many (List $ Rope) args))
    (match many slots _
      ((Nil _) (values (Nil _) $ Nil _))
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ index code)
        (let ((many indices) (many args)) $ notail $ emit-slots _ rest env ns d)
        (values (Cons _ index indices) $ Cons _ (notail $ emit-code _ _ code env ns d) args))))))

  ((many emit-arms : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Names ctx) ns) (many (Decls) d) -> (many (List $ Arm) r))
    (match many bs _
      ((Nil _) (Nil _))
      ((Cons _ b rest)
        (match many b _
          ((MkBranch _ _ disc ids body)
            (Cons _ (MkArm disc (names-of-ids ids env) $ notail $ emit-code _ _ body env (push-names _ ids env ns) d) $ notail $ emit-arms _ _ rest env ns d))))))

  ; The definitions of a group, each named by its entry and the suffix.
  ((many emit-group : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Env) env) (many (Names (Cons (List (Nat)) gids ctx)) ns) (many (Decls) d) (many (String) suffix) -> (many (List $ Rope) r))
    (match many fns _
      ((Nil _) (Nil _))
      ((Cons _ p rest)
        (let ((many more)) $ notail $ emit-group _ _ rest env ns d suffix)
        (match many p _
          ((MkPair _ _ id fn)
            (match many fn _
              ((MkFunc _ _ _ _ _ _ _ _ _) (Cons _ (rcat3 (RStr $ str-cat (top-name env id) suffix) (RStr " ") $ notail $ emit-fn _ _ fn env ns d) more))
              ((MkAlias _ _ _ _ _) more)))))))

  ; A function's parameters and body; an extern one is the host's, over its parameters unboxed.
  ((many emit-fn : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (Func gids ctx) fn) (many (Env) env) (many (Names (Cons (List (Nat)) gids ctx)) ns) (many (Decls) d) -> (many (Rope) r))
    (match many fn _
      ((MkFunc _ _ _ _ _ params body impl _)
        (let ((many ps)) $ names-of-ids params env)
        (let ((many (Rope) b))
          (match many impl _
            ((Some _ im) (match many im (((Rope) _)) ((MkImpl se _) (match many se (((Rope) _)) ((MkSomeExtern _ e) (ffi-call (ext-name _ e) ps env d))))))
            ((None _) (notail $ emit-code _ _ body env (push-names _ params env ns) d))))
        (rcat3 (params-rope ps) (RStr " : Obj.t = ") b))
      ((MkAlias _ _ _ _ _) (REmpty))))

  ; A block as one OCaml value, its addresses by name; a function value is its member's closure.
  ((many block-rope : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
    (match many b _
      ((BTag _ c fields) (build-rope d 0 c $ addr-ropes _ fields))
      ((BTup _ fields) (tuple-rope $ addr-ropes _ fields))
      ((BExt _ p) (payload-rope p))
      ((BArray _ fields) (rcat3 (RStr "(Obj.repr [|") (rjoin (addr-ropes _ fields) "; ") $ RStr "|])"))
      ((BCtorFn _ c) (ctor-fn-rope d c))
      ((BMat _ adt) (matchable-rope adt d))
      ((BGroup _ _ _ _ _) (RStr "(failwith \"a group as a closed value\")"))
      ((BFn _ g _ id) (RStr $ str-cat3 "(Obj.repr " (member-name _ env id g) ")"))
      ((BToken _) (RStr "(Obj.repr ())"))
      ((BError _ m) (rcat3 (RStr "(failwith ") (quoted m) $ RStr ")")))))

; ---- The declarations: found by a walk over every block of the store and the code it holds, then written
; ahead of the blocks; the narrowed copies come before the shapes, so a bare constructor names the shape's.

(def-fns _ $ (many collect-ctor : (many (Ctor) c) (many (Decls) d) -> (many (Decls) r))
  (match many (ctor-tagged c) _
    ((BTrue) (decl-shape d $ ctor-shape c))
    ((BFalse) (match many (ctor-newtype c) _
      ((BTrue) d)
      ((BFalse) (decl-shape d $ Cons _ (ctor-arity c) $ Nil _))))))

(def-fns _ $ (many collect-cell : (many (Ctor) c) (many (Decls) d) -> (many (Decls) r))
  (match many (ctor-tagged c) _
    ((BTrue)
      (let ((many shape)) $ ctor-shape c)
      (match many (nat-lt (Succ (Zero)) $ list-length _ shape) (((Decls) _))
        ((BTrue) (decl-narrow d shape $ live-key $ Cons _ (ctor-index c) $ Nil _))
        ((BFalse) (decl-shape d shape))))
    ((BFalse) (collect-ctor c d))))

(def-fns _ $ (many collect-ctors : (subterm many (List $ Ctor) cs) (many (Decls) d) -> (many (Decls) r))
  (match many cs _
    ((Nil _) d)
    ((Cons _ c rest) (tail $ collect-ctors rest $ collect-ctor c d))))

; An extern type's shape is declared too, as the target of its Matchable's unwrap.
(def-fns _ $ (many collect-adt : (many (Adt) adt) (many (Decls) d) -> (many (Decls) r))
  (match many (adt-tagged adt) _ ((BTrue) (decl-shape d $ adt-shape adt)) ((BFalse) (collect-ctors (adt-ctors adt) d))))

(def-fns _ $ (many collect-match : (many (Adt) adt) (many (List $ Nat) live) (many (Decls) d) -> (many (Decls) r))
  (match many (adt-tagged adt) _
    ((BFalse) (collect-adt adt d))
    ((BTrue)
      (match many (narrowed adt live) _
        ((BTrue) (decl-narrow d (adt-shape adt) $ live-key live))
        ((BFalse) (decl-shape d $ adt-shape adt))))))

(def-fns _ $ (many nat-list-mem : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (match many xs _
    ((Nil _) (BFalse))
    ((Cons _ y rest) (or (nat-eq x y) $ notail $ nat-list-mem rest x))))

(def-fns _
  ((many collect-code : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many code _
      ((CValue _ v) (tail $ collect-block _ v env d))
      ((CValues _ _ cs _) (tail $ collect-codes _ cs env d))
      ((CApp _ _ f args _) (tail $ collect-codes _ args env $ notail $ collect-code _ _ f env d))
      ((CCellAlloc _ ctor slots) (tail $ collect-codes _ slots env $ collect-ctor ctor d))
      ((CCellWrite _ k2 cell slots) (tail $ collect-slots _ slots env $ notail $ collect-code _ _ cell env $ collect-cell k2 d))
      ((CCellRead _ k2 _ cell) (tail $ collect-code _ _ cell env $ collect-cell k2 d))
      ((CLet _ _ _ _ _ rhs rest) (tail $ collect-code _ _ rest env $ notail $ collect-code _ _ rhs env d))
      ((CLetRec _ _ _ g rest) (match many g _ ((MkGroup _ _ fns _) (tail $ collect-code _ _ rest env $ notail $ collect-group _ _ fns env d))))
      ((CMatch _ _ scrut shape branches dfl live)
        (let ((many d1)) $ notail $ collect-code _ _ scrut env d)
        (let ((many (Decls) d2))
          (match many shape _
            ((ShKnown _ adt) (collect-match adt live d1))
            ((ShHeld _ mcode adt) (collect-match adt live $ notail $ collect-code _ _ mcode env d1))
            ((ShNone _) d1)))
        (let ((many d3)) $ notail $ collect-branches _ _ branches env d2)
        (match many dfl _ ((None _) d3) ((Some _ dd) (tail $ collect-code _ _ dd env d3))))
      (else d)))

  ((many collect-codes : (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many cs _
      ((Nil _) d)
      ((Cons _ c rest) (tail $ collect-codes _ rest env $ notail $ collect-code _ _ c env d))))


  ((many collect-slots : (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many slots _
      ((Nil _) d)
      ((Cons _ slot rest) (match many slot _ ((MkPair _ _ _ code) (tail $ collect-slots _ rest env $ notail $ collect-code _ _ code env d))))))

  ((many collect-branches : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns2) (subterm many (List $ Branch ctx ns2) bs) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many bs _
      ((Nil _) d)
      ((Cons _ b rest) (match many b _ ((MkBranch _ _ _ _ body) (tail $ collect-branches _ _ rest env $ notail $ collect-code _ _ body env d))))))

  ((many collect-group : (erased (List $ Nat) gids) (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Func gids ctx) fns) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many fns _
      ((Nil _) d)
      ((Cons _ p rest)
        (match many p _
          ((MkPair _ _ _ fn)
            (match many fn _
              ((MkFunc _ _ _ _ fid _ body impl _)
                (let ((many (Decls) d1))
                  (match many impl _
                    ((None _) (notail $ collect-code _ _ body env d))
                    ((Some _ im)
                      (match many im _
                        ((MkImpl se _)
                          (match many se _
                            ((MkSomeExtern _ e)
                              (match many (find-template (decl-templates d) "fn" (ext-name _ e) 0) _
                                ((Some _ ps) (decl-call-template d fid ps))
                                ((None _) d)))))))))
                (tail $ collect-group _ _ rest env d1))
              ((MkAlias _ _ _ _ _) (tail $ collect-group _ _ rest env d))))))))

  ((many collect-block : (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
    (match many b _
      ((BTag _ c _) (collect-cell c d))
      ((BCtorFn _ c) (collect-ctor c d))
      ((BMat _ adt) (collect-adt adt d))
      ((BGroup _ _ _ g _) (match many g _ ((MkGroup _ _ fns _) (tail $ collect-group _ _ fns env d))))
      (else d))))



(def-fns _ $ (many ctor-decls : (many (Decls) d) (many (List $ Nat) s) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (Rope) r))
  (match many arities _
    ((Nil _) (REmpty))
    ((Cons _ n rest)
      (let ((many (Rope) sep)) $ match many rest _ ((Nil _) (REmpty)) ((Cons _ _ _) (RStr " | ")))
      (let ((many (Rope) fields)) $ match many n _ ((Zero) (REmpty)) ((Succ _) (rcat3 (RStr " of { ") (rjoin (record-types n 0) "; ") $ RStr " }")))
      (rcat4 (RStr $ ctor-name-at d s i) fields sep $ notail $ ctor-decls d s rest $ Succ i))))

(def-fns _ $ (many shape-decls : (many (Decls) d) (subterm many (List $ List $ Nat) ss) (many (Bool) first) -> (many (Rope) r))
  (match many ss _
    ((Nil _) (REmpty))
    ((Cons _ s rest)
      (rcat5 (RStr $ match many first (((String) _)) ((BTrue) "type ") ((BFalse) "and ")) (RStr $ shape-name d s) (RStr " = ") (ctor-decls d s s 0) $ rcat (RStr "\n") $ notail $ shape-decls d rest $ BFalse))))

(def-fns _ $ (many narrow-ctors : (many (Decls) d) (many (List $ Nat) s) (many (List $ Nat) live) (many (String) name) (subterm many (List $ Nat) arities) (many (Nat) i) -> (many (Rope) r))
  (match many arities _
    ((Nil _) (REmpty))
    ((Cons _ n rest)
      (let ((many (Rope) sep)) $ match many rest _ ((Nil _) (REmpty)) ((Cons _ _ _) (RStr " | ")))
      (let ((many (String) idx)) $ match many (nat-list-mem live i) _ ((BTrue) "yes ") ((BFalse) "no "))
      (let ((many (Rope) fields)) $ match many n _ ((Zero) (REmpty)) ((Succ _) (rcat3 (RStr "{ ") (rjoin (record-types n 0) "; ") $ RStr " } -> ")))
      (rcat5 (RStr $ str-cat (ctor-name-at d s i) " : ") fields (RStr $ str-cat idx name) sep $ notail $ narrow-ctors d s live name rest $ Succ i))))

(def-fns _ $ (many narrow-decls : (many (Decls) d) (subterm many (List $ Narrow) ns) -> (many (Rope) r))
  (match many ns _
    ((Nil _) (REmpty))
    ((Cons _ n rest)
      (match many n _
        ((MkNarrow s live)
          (let ((many name)) $ narrow-name d s live)
          (rcat4 (RStr $ str-cat3 "type _ " name " = ") (narrow-ctors d s live name s 0) (RStr "\n") $ notail $ narrow-decls d rest))))))

(def-fns _ $ (many decls-rope : (many (Decls) d) -> (many (Rope) r))
  (match many d _
    ((MkDecls shapes2 narrows _) (rcat (narrow-decls d narrows) $ shape-decls d shapes2 $ BTrue))))

; ---- The walk from the roots: what a Const or a final reaches, each value once. The worklist is
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

(def-fns _ $ (many block-refs : (erased (Hist Block) a) (many (Block (Ref Block a)) b) -> (many (List $ Ref Block a) r))
  (match many b _
    ((BTag _ _ fields) fields)
    ((BArray _ fields) fields)
    ((BTup _ fields) fields)
    ((BFn _ g _ _) (Cons _ g $ Nil _))
    ((BGroup _ _ _ _ fr) (frames-refs _ _ fr (Nil _)))
    (else (Nil _))))

(def-fns _ $ (many roots-of-entries : (erased (Hist Block) hs) (subterm many (IdMap $ EInfo hs) en)
    (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r))
  (match many en _
    ((MEmpty _) acc)
    ((MNode _ here one two)
      (let ((many acc1))
        (match many here (((List $ Ref Block hs) _))
          ((None _) acc)
          ((Some _ info)
            (match many info (((List $ Ref Block hs) _))
              ((MkEInfo _ _ _ st _ _ _)
                (match many st (((List $ Ref Block hs) _))
                  ((SDyn _) acc)
                  ((SConst _ v) (Cons _ v acc))))))))
      (tail $ roots-of-entries _ two (notail $ roots-of-entries _ one acc1)))))

(def-fns _ $ (many roots-of-finals : (erased (Hist Block) hs) (subterm many (List $ Pair (Ref Block hs) $ Term) fs)
    (many (List $ Ref Block hs) acc) -> (many (List $ Ref Block hs) r))
  (match many fs _
    ((Nil _) acc)
    ((Cons _ p rest) (match many p _ ((MkPair _ _ v _) (tail (roots-of-finals _ rest (Cons _ v acc))))))))

; [rest] the stamps the seen set still lacks, [work] the worklist; the call in each branch decreases
; the first of those two that it can.
(def-fns _ $ (many trace-loop : (erased (Hist Block) hs) (erased (Nat) bound) (erased (Len Block hs bound) lb) (many (Store Block hs) hp)
    (erased (Nat) size) (subterm erased (Nat) rest) (erased (Add size rest bound) sum)
    (many (IdMap $ Unit) seen) (erased (Bounded (Unit) seen size bound) bd)
    (subterm many (List $ Ref Block hs) work) (many (List $ Ref Block hs) acc)
    (many (Env) env) (many (Decls) d) -> (many (List $ Ref Block hs) acc2) (many (Decls) d2))
  (match many work _
    ((Nil _) (values acc d))
    ((Cons _ at2 wrest)
      (let ((many k) (erased lk)) (ref-key Block _ bound lb at2))
      (match many (idmap-get _ k seen) _
        ((Hit _ _ _ _ _) (tail (trace-loop _ bound lb hp size rest sum seen bd wrest acc env d)))
        ((Miss _ _ _ ab)
          (let ((many seen2) (erased rest2) (erased bd2) (erased sum2) (erased less))
            (seen-add (Unit) k (MkUnit) seen size rest bound bd sum ab lk))
          (let ((erased rs) (many blk) (erased tsf)) $ store-read Block hs hp at2)
          (let ((many kids)) (block-refs _ blk))
          (let ((erased kids2) (erased pk)) (refs-widen Block rs hs tsf kids))
          (tail (trace-loop _ bound lb hp (Succ size) (subterm (lt-subterm rest2 rest less)) rest2 sum2 seen2 bd2
                  (rev-onto _ (coerce kids pk) wrest) (Cons _ at2 acc) env (collect-block _ blk env d))))))))

; A group's block is its members' top-level let rec over the names of the frames it closed over.
(def-fns _ $ (many block-let : (erased (Hist Block) hs) (many (Ref Block hs) addr) (erased (Hist Block) a) (subterm many (Block (Ref Block a)) b) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many b _
    ((BGroup _ _ _ g env2)
      (match many g _
        ((MkGroup _ ids fns _)
          (let ((many suffix)) $ str-cat "_" $ addr-str _ addr)
          (match many (emit-group _ _ fns env (push-fn-names _ ids fns env suffix $ frame-names _ _ env2 env) d suffix) _
            ((Nil _) (REmpty))
            ((Cons _ f1 more) (rcat3 (RStr "let rec ") (rjoin (Cons _ f1 more) "\nand ") $ RStr "\n"))))))
    (else (rcat5 (RStr "let ") (addr-rope _ addr) (RStr " : Obj.t = ") (block-rope _ b env d) $ RStr "\n"))))

(def-lvl REF-CMP)

(let ((erased REF-SORT-L) (many ref-sort)) (sort-factory REF-CMP))

(def-fns _ $ (many blank-words : (subterm many (Nat) n) -> (many (List $ Rope) r))
  (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ (RStr "(Obj.repr ())") $ notail $ blank-words k))))

(def-fns _ $ (many block-stores : (erased (Hist Block) hs) (many (Decls) d) (many (Ctor) c) (subterm many (List $ Ref Block hs) fields) (many (Rope) dest) (many (Nat) index) -> (many (Rope) r))
  (match many fields _
    ((Nil _) (REmpty))
    ((Cons _ f rest)
      (rcat3 (RStr "let () = ")
        (field-store-rope d c dest (Cons _ index $ Nil _) (Cons _ (addr-rope _ f) $ Nil _) "bf")
        $ rcat (RStr "\n") $ notail $ block-stores _ d c rest dest $ Succ index))))

(def-fns _ $ (many array-stores : (erased (Hist Block) hs) (subterm many (List $ Ref Block hs) fields) (many (Rope) dest) (many (Nat) index) -> (many (Rope) r))
  (match many fields _
    ((Nil _) (REmpty))
    ((Cons _ f rest)
      (rcat5 (RStr "let () = Array.unsafe_set (Obj.obj ") dest (rcat3 (RStr " : Ffi_core.word array) ") (nat-rope index) $ RStr " (Obj.obj ") (addr-rope _ f) $ rcat (RStr " : Ffi_core.word)\n") $ notail $ array-stores _ rest dest $ Succ index))))

(def-fns _ $ (many emit-blocks : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) order)
    (many (Env) env) (many (Decls) d) -> (many (Rope) skeletons) (many (Rope) defs) (many (Rope) fills))
  (match many order _
    ((Nil _) (values (REmpty) (REmpty) $ REmpty))
    ((Cons _ at2 rest)
      (let ((erased rs) (many blk) (erased sf)) $ store-read Block hs hp at2)
      (let ((many before) (many middle) (many after)) $ notail $ emit-blocks _ hp rest env d)
      (match many blk _
        ((BTag _ c fields)
          (let ((many skeleton)) $ rcat5 (RStr "let ") (addr-rope _ at2) (RStr " : Obj.t = ") (plain-build d c $ blank-words $ list-length _ fields) $ RStr "\n")
          (values (rcat skeleton before) middle $ rcat (block-stores _ d c fields (addr-rope _ at2) 0) after))
        ((BArray _ fields)
          (let ((many skeleton)) $ rcat5 (RStr "let ") (addr-rope _ at2) (RStr " : Obj.t = Obj.repr (Array.make ") (nat-rope $ list-length _ fields) $ RStr " (Obj.repr ()))\n")
          (values (rcat skeleton before) middle $ rcat (array-stores _ fields (addr-rope _ at2) 0) after))
        (else (values before (rcat (block-let _ at2 _ blk env d) middle) after))))))

; ---- The driver (lib/driver_core.ml): its operations on the prelude's values, each a direct build or match



(def-fns _ $ (many driver-make : (many (Decls) d) (many (Env) env) (many (String) name) -> (many (Rope) r))
  (match many (prelude-ctor env name) _
    ((None _) (RStr "(absurd ())"))
    ((Some _ c)
      (let ((many fs)) $ field-names (ctor-arity c) 0)
      (match many fs _
        ((Nil _) (build-rope d 0 c fs))
        ((Cons _ _ _) (lambda-rope fs $ build-rope d 0 c fs))))))

(def-fns _ $ (many driver-un : (many (Decls) d) (many (Env) env) (many (String) tname) (many (ArmKind) k) -> (many (Rope) r))
  (match many (prelude-adt env tname) _
    ((None _) (RStr "(absurd ())"))
    ((Some _ adt) (lambda-rope (Cons _ (RStr "v") $ Nil _) $ dispatch-rope d 0 adt (all-live adt) (RStr "v") (ctor-arms d (adt-ctors adt) k) $ None _))))

(def-fns _ $ (many driver-op : (many (String) field) (many (Rope) r) -> (many (Rope) r2))
  (rcat3 (RStr $ str-cat3 "Driver_core." field " = ") r $ RStr "; "))

(def-fns _ $ (many driver-rope-of : (many (Decls) d) (many (Env) env) -> (many (Rope) r))
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

(def-fns _ $ (many driver-rope : (many (Decls) d) (many (Env) env) -> (many (Rope) r))
  (match many (prelude-ctor env "Exit") _
    ((None _) (REmpty))
    ((Some _ _) (driver-rope-of d env))))

; ---- Finals (lib/program.ml): what the driver does with a file's final value

(def-adts $ (FinalKind : -> Type)
  enum
  (many FMain : -> (FinalKind))
  (many FIo : -> (FinalKind))
  (many FThunk : (many (Term) ty) -> (FinalKind))
  (many FPlain : -> (FinalKind)))

(def-fns _ $ (many is-string-type : (many (Env) env) (many (Term) ty) -> (many (Bool) r))
  (match many (type-head env ty) _
    ((None _) (BFalse))
    ((Some _ t) (str-eq (name-of env t) "String"))))

(def-fns _ $ (many classify-final : (many (Env) env) (many (Term) ty) -> (many (FinalKind) f))
  (match many (canon-env env ty) _
    ((TFn unique2 _ ps rs)
      (match many unique2 _
        ((BTrue) (FPlain))
        ((BFalse)
          (match many ps _
            ((Nil _)
              (match many rs _
                ((Cons _ r more)
                  (match many more _
                    ((Nil _) (match many r _ ((MkEntry _ _ m sg _ _) (match many m _ ((Many) (FThunk $ sg-term sg)) ((Once) (FThunk $ sg-term sg)) ((Erased) (FPlain))))))
                    ((Cons _ _ _) (FPlain))))
                ((Nil _) (FPlain))))
            ((Cons _ p more)
              (match many more _
                ((Cons _ _ _) (FPlain))
                ((Nil _)
                  (match many rs _
                    ((Nil _) (FPlain))
                    ((Cons _ r more3)
                      (match many more3 _
                        ((Cons _ _ _) (FPlain))
                        ((Nil _)
                          (match many (and (is-string-type env $ sg-term $ entry-sg p)
                                        (and (is-string-type env $ sg-term $ entry-sg r)
                                          $ and (and (mult-is-many $ entry-mult p) $ not $ mult-is-once $ entry-mult p) $ and (mult-is-many $ entry-mult r) $ not $ mult-is-once $ entry-mult r)) _
                            ((BTrue) (FMain))
                            ((BFalse) (FPlain))))))))))))))
    ((TApp _ _)
      (match many (type-head env ty) _
        ((None _) (FPlain))
        ((Some _ t) (match many (str-cmp (name-of env t) "IO") _ ((CEq _ _ _) (FIo)) (else (FPlain)))))) (else (FPlain))))

; ---- A printer per type for a final function's result (lib/extract.ml's show): each constructor's return
; type is unified with the type to find its many fields' types, as entering a branch does.

(def-adts $ (ShowMemo : -> Type)
  enum
  (many MkShowMemo : (many (Nat) fresh) (many (Nat) count) (many (List $ Pair (Term) $ String) known) (many (List $ Rope) defs) -> (ShowMemo)))

(def-fns _ $ (many memo-find : (subterm many (List $ Pair (Term) $ String) known) (many (Env) env) (many (Term) ty) -> (many (Maybe $ String) r))
  (match many known _
    ((Nil _) (None _))
    ((Cons _ p rest)
      (match many p _
        ((MkPair _ _ t name)
          (match many (term-eq t ty) _
            ((BTrue) (Some _ name))
            ((BFalse) (tail $ memo-find rest env ty))))))))

(def-fns _ $ (many spaced : (subterm many (List $ Rope) parts) -> (many (Rope) r))
  (match many parts _
    ((Nil _) (RStr "\"\""))
    ((Cons _ p rest)
      (match many rest _
        ((Nil _) p)
        ((Cons _ _ _) (rcat3 p (RStr " ^ \" \" ^ ") $ notail $ spaced rest))))))

; A literal type's printer, which prints the literal its value reads back from: the emitted OCaml spells it
; through Ffi_core (lib/extract.ml's literal_show). slc always compiles against the FFI, so a Nat is its
; integer and a String its slice; a Char and a U8 are their Nat (section 38), unwrapped by neither.
(def-fns _ $ (many lit-show : (many (Env) env) (many (Term) ty) -> (many (Maybe $ Rope) r))
  (match many (prelude-nullary env ty "Slot") _
    ((BTrue) (Some _ $ RStr "\"_\""))
    ((BFalse)
      (match many (prelude-nullary env ty "Nat") (((Maybe $ Rope) _))
        ((BTrue) (Some _ $ RStr "(Z.to_string (Obj.obj v : Z.t))"))
        ((BFalse)
          (match many (prelude-nullary env ty "Char") (((Maybe $ Rope) _))
            ((BTrue) (Some _ $ RStr "(Ffi_core.lit_char (Z.to_int (Obj.obj v : Z.t)))"))
            ((BFalse)
              (match many (prelude-nullary env ty "String") (((Maybe $ Rope) _))
                ((BTrue) (Some _ $ RStr "(let (s, o, l) = (Obj.obj v : Ffi_core.slice) in Ffi_core.lit_string (String.sub s o l))"))
                ((BFalse) (None $ Rope))))))))))

(def-fns _
  ((many show-type : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty0) (many (ShowMemo) memo) (many (Decls) d) -> (many (ShowMemo) memo2) (many (String) name))
    (match many fuel _
      ((Zero) (values memo "show_any"))
      ((Succ k)
        (let ((many ty)) $ canon-env env ty0)
        (match many memo _
          ((MkShowMemo fresh count known defs)
            (let ((many key)) $ mapv ty (OpWild fresh) 0)
            (match many (memo-find known env key) _
              ((Some _ name) (values memo name))
              ((None _)
                (let ((many name)) $ str-cat "show_" $ nat-str count)
                (let ((many memo1)) $ MkShowMemo fresh (Succ count) (Cons _ (MkPair _ _ key name) known) defs)
                (let ((many (ShowMemo) memo2) (many (Rope) body))
                  (match many (lit-show env ty) (((ShowMemo) _) ((Rope) r0))
                    ((Some _ text) (values memo1 text))
                    ((None _)
                      (match many ty _
                        ((TApp _ _)
                          (match many (type-adt env ty) (((ShowMemo) _) ((Rope) r))
                            ((None _) (values memo1 $ RStr "\"_\""))
                            ((Some _ adt)
                              ; the tag where there is one, else the sole non-phantom constructor; a union with
                              ; several has no way to choose and prints `_` (ASSUMPTIONS 184)
                              (let ((many usable))
                                (match many (adt-tagged adt) (((List $ Ctor) _))
                                  ((BTrue) (adt-ctors adt))
                                  ((BFalse) (match many (lone-ctor adt) (((List $ Ctor) _))
                                              ((None _) (Nil _))
                                              ((Some _ c) (Cons _ c $ Nil _))))))
                              (let ((many memo3) (many arms)) $ notail $ show-arms k env ty usable memo1 (adt-tagged adt) d)
                              (match many arms (((ShowMemo) _) ((Rope) r2))
                                ((Nil _) (values memo3 $ RStr "\"_\""))
                                ((Cons _ _ _)
                                  (values memo3 $ dispatch-rope d 0 adt (all-live adt) (RStr "v") arms $ Some _ $ RStr "\"_\""))))))
                        ((TFn _ _ _ _) (values memo1 $ RStr "\"_\""))
                        ((TCell _ _) (values memo1 $ RStr "\"_\""))
                        ((TValCtor _ _) (values memo1 $ RStr "\"_\"")) (else (values memo1 $ RStr "\"_\""))))))
                (match many memo2 _
                  ((MkShowMemo fresh2 count2 known2 defs2)
                    (values (MkShowMemo fresh2 count2 known2 $ Cons _ (rcat4 (RStr name) (RStr " (v : Obj.t) : string = ") body $ REmpty) defs2) name))))))))))

  ; One arm per non-phantom constructor whose return type the instance does not refute, the opened objects
  ; merged as entering a branch does, its fields shown only then, as the reference's exception skips them.
  ((many show-arms : (subterm many (Nat) fuel) (many (Env) env) (many (Term) ty) (many (List $ Ctor) ctors) (many (ShowMemo) memo) (many (Bool) tagged) (many (Decls) d) -> (many (ShowMemo) memo2) (many (List $ Arm) arms))
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many ctors _
          ((Nil _) (values memo $ Nil _))
          ((Cons _ c rest)
            (match many c _
              ((MkCtor cname cid index arity _ _ _ _)
                (let ((many ctele) (many ret)) $ ctor-type env cid)
                (let ((many envb) (many fids) (erased lock)) $ open-tele ctele env (None _) (None _) (None _) (Nil _) $ BFalse)
                (let ((many (Env) envb2) (many (Bool) live))
                  (match many (merge-all $ unify-force (Forcing envb) (instantiate (tvars-rev fids $ Nil _) ret) ty) _
                    ((UOk e2) (values e2 $ BTrue))
                    ((UContra _) (values envb $ BFalse))))
                (let ((many (ShowMemo) memo2) (many (List $ Rope) shown))
                  (match many live _
                    ((BTrue) (notail $ show-block-fields k envb2 fids memo 0 d))
                    ((BFalse) (values memo $ Nil _))))
                ; Ffi_core.show_app is the one definition the interpreter, an extracted program and this
                ; output share, so `$` is not decided again here (ASSUMPTIONS 184)
                (let ((many (Rope) text))
                  (rcat4 (RStr "(Ffi_core.show_app ") (quoted cname) (rwrap " [ " (rjoin shown "; ") " ])") $ REmpty))
                (let ((many memo3) (many more)) $ notail $ show-arms k env ty rest memo2 tagged d)
                (values memo3 $ match many live (((List $ Arm) _)) ((BTrue) (Cons _ (MkArm index (field-names arity 0) text) more)) ((BFalse) more)))))))))

  ((many show-block-fields : (subterm many (Nat) fuel) (many (Env) env) (many (List $ Nat) fids) (many (ShowMemo) memo) (many (Nat) i) (many (Decls) d) -> (many (ShowMemo) memo2) (many (List $ Rope) shown))
    (match many fuel _
      ((Zero) (values memo $ Nil _))
      ((Succ k)
        (match many fids _
          ((Nil _) (values memo $ Nil _))
          ((Cons _ x rest)
            (match many (entry-mult-of env x) (((ShowMemo) _) ((List $ Rope) rs))
              ((Erased)
                (let ((many memo3) (many more)) $ notail $ show-block-fields k env rest memo i d)
                (values memo3 $ Cons _ (RStr "\"_\"") more))
              (else
                (let ((many memo2) (many name)) $ notail $ show-type k env (type-of env x) memo d)
                (let ((many memo3) (many more)) $ notail $ show-block-fields k env rest memo2 (Succ i) d)
                (values memo3 $ Cons _ (rcat3 (RStr name) (RStr " f") $ nat-rope i) more)))))))))

(def-fns _ $ (many show-defs : (many (ShowMemo) memo) -> (many (Rope) r))
  (match many memo _
    ((MkShowMemo _ _ _ defs)
      (match many defs _
        ((Nil _) (REmpty))
        ((Cons _ _ _) (rcat3 (RStr "let rec ") (rjoin (list-rev _ defs) "\nand ") $ RStr "\n"))))))

; A final that is a function or a constructor prints `_`, as the reference does (ASSUMPTIONS 184).
(def-fns _ $ (many named-final : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) (many (Env) env) -> (many (Maybe $ String) r))
  (let ((erased ns) (many b) (erased sf)) $ store-read Block hs hp v)
  (match many b _
    ((BFn _ _ _ _) (Some _ "_"))
    ((BCtorFn _ _) (Some _ "_"))
    (else (None $ String))))

(def-fns _ $ (many final-captured-word : (subterm many (List $ Nat) ids) (many (Env) env)
    (many (Term) place) -> (many (Rope) r))
  (match many ids _
    ((Nil _) (RStr "(failwith \"no captured word for final at-return\")"))
    ((Cons _ id rest)
      (match many (and (is-const env id) (at-equal env place (TVar id))) _
        ((BTrue) (const-rope env id))
        ((BFalse) (tail $ final-captured-word rest env place))))))

(def-fns _ $ (many final-at-source : (many (Env) env) (many (Term) place) (many (Bool) argument) -> (many (Rope) r))
  (match many place _
    ((TBound n)
      (match many (and argument (nat-is-zero n)) _
        ((BTrue) (RStr "_at_final_arg"))
        ((BFalse) (RStr "(failwith \"invalid final at-return parameter\")"))))
    ((TVar id)
      (match many (is-const env id) _
        ((BTrue) (const-rope env id))
        ((BFalse) (final-captured-word (env-words env) env place))))
    (else (final-captured-word (env-words env) env place))))

(def-fns _ $ (many adapt-final-rope : (many (Env) env) (many (Term) ty) (many (Rope) callable)
    (many (Bool) argument) -> (many (Rope) adapted))
  (match many (canon-env env ty) _
    ((TFn _ _ _ rets)
      (match many rets _
        ((Nil _) callable)
        ((Cons _ entry2 _)
          (match many (entry-place entry2) _
            ((None _) callable)
            ((Some _ slot)
              (match many slot _
                ((TSlotHolds place)
                  (let ((many source)) (final-at-source env place argument))
                  (match many argument _
                    ((BTrue)
                      (rcat5 (RStr "(Obj.repr (fun (_at_final_arg : Obj.t) -> let () = (Obj.obj ") callable
                        (RStr " : Obj.t -> unit) _at_final_arg in ") source (RStr "))")))
                    ((BFalse)
                      (rcat5 (RStr "(Obj.repr (fun () -> let () = (Obj.obj ") callable
                        (RStr " : unit -> unit) () in ") source (RStr "))")))))
                (else callable)))))))
    (else callable)))

(def-fns _ $ (many final-rope : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) (many (Term) ty) (many (Decls) d) -> (many (Rope) r))
  (let ((many vr)) $ addr-rope _ v)
  (match many (classify-final env ty) _
    ((FMain) (rcat3 (RStr "let () = driver.run_main world ") (adapt-final-rope env ty vr (BTrue)) $ RStr "\n"))
    ((FIo) (rcat3 (RStr "let () = exit (driver.run_io world ") vr $ RStr ")\n"))
    ((FThunk t)
      (let ((many adapted)) (adapt-final-rope env ty vr (BFalse)))
      (let ((many memo) (many name)) $ show-type show-fuel env t (MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _) d)
      (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " ((Obj.obj ") adapted $ RStr " : unit -> Obj.t) ()))") $ RStr "\n"))
    ((FPlain)
      (match many (named-final _ hp v env) _
        ((Some _ text) (rcat3 (RStr "let () = print_endline ") (quoted text) $ RStr "\n"))
        ((None _)
          (let ((many memo) (many name)) $ show-type show-fuel env ty (MkShowMemo (env-fresh-bound env) 0 (Nil _) $ Nil _) d)
          (rcat5 (show-defs memo) (RStr "let () = print_endline (") (RStr name) (rcat3 (RStr " ") vr $ RStr ")") $ RStr "\n"))))))

(def-fns _ $ (many emit-finals : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Pair (Ref Block hs) $ Term) fs) (many (Env) env) (many (Decls) d) -> (many (Rope) r))
  (match many fs _
    ((Nil _) (REmpty))
    ((Cons _ p rest) (match many p _ ((MkPair _ _ v ty) (rcat (final-rope env _ hp v ty d) $ notail $ emit-finals _ hp rest env d))))))

; The prelude's types the driver and any printer may name, declared whether or not the program reaches them.
(def-fns _ $ (many collect-prelude : (subterm many (List $ String) names) (many (Env) env) (many (Decls) d) -> (many (Decls) r))
  (match many names _
    ((Nil _) d)
    ((Cons _ n rest) (tail $ collect-prelude rest env $ match many (prelude-adt env n) (((Decls) _)) ((None _) d) ((Some _ adt) (collect-adt adt d))))))

(def-fns _ $ (many emit-program : (many (Bool) templates) (many (Env) env) -> (many (Rope) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store env)
  (let ((many d0)) $ collect-prelude (Cons _ "Array" $ Cons _ "Nat" $ Cons _ "String" $ Cons _ "IO" $ Cons _ "Maybe" $ Cons _ "Result" $ Cons _ "List" $ Cons _ "Pair" $ Cons _ "EntryKind" $ Cons _ "Change" $ Nil _) env $ MkDecls (Nil _) (Nil _) $ match many templates (((List $ Template) _)) ((BTrue) (parse-templates $ split-on (rope-str extern-templates) 10)) ((BFalse) (Nil _)))
  (let-match many hp (MkStore _ _ bound lb writes))
  (let ((many roots)) $ roots-of-finals _ fi (roots-of-entries _ en (Nil _)))
  (let ((many acc2) (many d2))
    $ trace-loop _ bound lb hp (Zero) bound (AddZero bound) (MEmpty _) (BdEmpty _ bound) roots (Nil _) env d0)
  (def-fns REF-CMP $ (many ref-le : (many (Ref Block hs) x) (many (Ref Block hs) y) -> (many (Bool) b))
    (nat-lt (ref-pos Block _ x) (ref-pos Block _ y)))
  (let ((many order)) $ ref-sort (Ref Block hs) ref-le acc2)
  (let ((many skeletons) (many defs) (many fills)) $ emit-blocks _ hp order env d2)
  (rcat5 runtime-header (decls-rope d2) (rcat3 skeletons defs fills) (driver-rope d2 env) $ emit-finals _ hp (list-rev _ fi) env d2))
