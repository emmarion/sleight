; self/interp.sl -- the compiler's --interpret mode: a program's final values performed by slc itself in
; place of being written out as OCaml (lib/program.ml's consume). A final Program is walked one step at a
; time: each Continue becomes a step of slc's own Program, which applies the program's continuation with
; self/eval.sl's apply to slc's own world, a world-do the evaluator meets performing its request with it and
; putting the answer into the compile-time store; a plain value, a thunk's result and a String -> String
; function's output are printed through the compile-time printer. The interpreted program's arguments follow
; a "--" among slc's own.


; ---- Reading a value out: a String or a U8's Nat held under the FFI, the printed form of any value, and the
; message of an error block, which the interpreter returns where the reference raises (self/README.md).

(def-fns _ $ (many final-text : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) v) (many (Env) env) (many (Term) ty) -> (many (String) s))
  (let-match many (named-final _ (heap-store _ hp) v env) (None _) ((Some _ text) text))
  (let ((many body) (many app)) (show-at _ hp v 100000 env ty))
  (rope-str (match many app (((Rope) _)) ((BTrue) (rwrap "(" body ")")) ((BFalse) body))))

; ---- The compiler's command-line flags (self/main.sl).
; The flags slc takes alone, and those taking the argument after them.
(def-fns _ $ (many switches : -> (many (List $ String) r))
  (Cons _ "--no-prelude" $ Cons _ "--no-templates" $ Cons _ "--interpret" $ Cons _ "--no-env" $ Cons _ "--first-error" $ Cons _ "--no-shape-note" $ Cons _ "--warnings-as-errors" $ Cons _ "--warn-unused" $ Nil _))

(def-fns _ $ (many valued : -> (many (List $ String) r))
  (Cons _ "--confine-dir" $ Cons _ "--confine-output-bytes" $ Cons _ "--hints" $ Cons _ "--eval-fuel" $ Nil _))

; The flags among the arguments, in any order, the last given first and a switch's value "", and the files in order.
(def-fns _ $ (many read-flags : (subterm many (List $ String) args) (many (List $ Pair (String) $ String) flags) (many (List $ String) files)
    -> (many (Result $ Pair (List $ Pair (String) $ String) $ List $ String) r))
  (let-match many args (Cons _ a rest) ((Nil _) (Ok _ $ MkPair _ _ flags $ list-rev _ files)))
  (let-match many (list-mem-str (switches) a) (BFalse) ((BTrue) (tail $ read-flags rest (Cons _ (MkPair _ _ a "") flags) files)))
  (let-match many (list-mem-str (valued) a) (BFalse)
    ((BTrue) (match many rest _
      ((Nil _) (Fail _ $ str-cat a " needs a value"))
      ((Cons _ v more) (tail $ read-flags more (Cons _ (MkPair _ _ a v) flags) files)))))
  (let-match many (str-starts "--" a) (BFalse) ((BTrue) (Fail _ $ str-cat "unknown flag " a)))
  (tail $ read-flags rest flags $ Cons _ a files))

(def-fns _ $ (many flag-value : (subterm many (List $ Pair (String) $ String) flags) (many (String) f) -> (many (Maybe $ String) r))
  (let-match many flags (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkPair _ _ g v))
  (match many (str-eq f g) _ ((BTrue) (Some _ v)) ((BFalse) (tail $ flag-value rest f))))

(def-fns _ $ (many has-flag : (many (List $ Pair (String) $ String) flags) (many (String) f) -> (many (Bool) r))
  (is-some _ $ flag-value flags f))

; ---- The levels of the compiler's own Program (self/main.sl), and the codes it exits with.

(def-fns _ $ (many say-to : (many (Bool) err) (many (String) s) (unique (World) w) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w $ match many err (((Request $ Unit) _)) ((BTrue) (WriteErr s)) ((BFalse) (WriteOut s))))
  w1)

(def-lvl util-lvl)
(def-lvl interp-lvl)
(def-lvl finals-lvl)
(def-lvl run-lvl)
(def-lvl compile-lvl)
(def-lvl slc-lvl)
(def-lvl start-lvl)
(def-lvl io-lvl)

(let ((many zero-below-modulus)) $ lt-dec 0 u8-modulus)
(comptime-match many zero-below-modulus (Yes ok-a ok-b ok-lt))
(let ((many exit-ok)) $ MkU8 0 ok-lt)
(let ((many one-below-modulus)) $ lt-dec 1 u8-modulus)
(comptime-match many one-below-modulus (Yes fail-a fail-b fail-lt))
(let ((many exit-fail)) $ MkU8 1 fail-lt)

(def-fns util-lvl $ (many runtime-error : (many (String) m) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (values (say-to (BTrue) (str-cat3 "slc: runtime error: " m "\n") w) (Exit _ exit-fail)))

(def-fns util-lvl $ (many heap-crash : (erased (Hist Block) hs) (many (Heap hs) hp) -> (many (Maybe $ String) m))
  (match many hp _ ((MkHeap _ _ _ _ c) c)))

(def-fns util-lvl $ (many answer-ctors : (many (Env) env) (subterm many (List $ String) names) -> (many (List $ Ctor) cs))
  (let-match many names (Cons _ n rest) ((Nil _) (Nil _)))
  (let ((many more)) (notail $ answer-ctors env rest))
  (let-match many (prelude-adt env n) (Some _ a) ((None _) more))
  (let ((many cs) (erased p)) (list-append _ (adt-ctors a) more))
  cs)

; ---- The Program walk: each Continue step of the program becomes one of slc's, applying the program's
; continuation with self/eval.sl's apply to slc's own world, which a world-do it meets performs.

(def-fns interp-lvl $ (many interp-program : (many (Nat) fuel) (many (List $ Ctor) pcs) (many (Performer $ World) pf) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) v) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let-match many (heap-crash _ hp) (None _) ((Some _ m) (runtime-error m w)))
  (let ((erased h1) (many hp1) (erased le1) (many i) (many fields)) (destruct _ hp (pctor pcs "Exit") v))
  (let ((many f0)) (field-at _ fields 0 (widen-ref _ _ le1 v)))
  (let-match many (nat-eq i $ ctor-index $ pctor pcs "Continue") (BTrue)
    ((BFalse)
      (let ((many n)) (heap-nat _ hp1 f0))
      (match many (lt-dec n u8-modulus) _
        ((Yes _ _ p) (values w (Exit _ (MkU8 n p))))
        ((No _ _ _) (values w (Exit _ exit-fail))))))
  (def-unique io-lvl $ (unique step : (unique (World) u) -> (unique (World) u2 at u) (unique (Program io-lvl) next))
    (let ((erased h2) (many hp2) (erased le2) (many token)) $ halloc _ hp1 $ BToken _)
    (let ((erased h3) (many hp3) (erased le3) (many vs) (erased pk) (unique (World) u1)) (apply fuel _ hp2 (widen-ref _ _ le2 f0) (Cons _ token $ Nil _) many-one _ pf u))
    (tail $ interp-program fuel pcs pf _ hp3 (vals-one _ vs pk) u1))
  (values w (Continue _ step)))

; ---- The finals in order, each as lib/program.ml's consume has it; the finals stay at the history they were
; recorded at and each is widened to the current one as it is reached, so the walk is structural.

(def-fns finals-lvl $ (many interp-finals : (many (Env) env) (many (List $ String) pargs) (many (Bool) with-env) (erased (Hist Block) hs0) (subterm many (List $ Pair (Ref Block hs0) $ Term) fi) (erased (Hist Block) hs) (many (Heap hs) hp) (erased (Suffix Block hs hs0) le) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let-match many fi (Cons _ f rest) ((Nil _) (values w (Exit _ exit-ok))))
  (let-match many f (MkPair _ _ v0 ty))
  (let ((many v)) (widen-ref _ _ le v0))
  (let ((unique (Unit) u)) (MkUnit))
  (match many (classify-final env ty) _
    ((FProgram)
      (let ((many pcs)) $ answer-ctors env $ Cons _ "Program" $ Cons _ "Stopwatch" $ Cons _ "Unit" $ Cons _ "Maybe" $ Cons _ "Result" $ Cons _ "List" $ Cons _ "Pair" $ Cons _ "EntryKind" $ Cons _ "Change" $ Cons _ "Usage" $ Cons _ "Request" $ Nil _)
      (let ((unique w1) (many base)) (world-do _ w (Measure (Stop))))
      (let ((many rq)) $ match many (prelude-adt env "Request") (((List $ Ctor) _)) ((Some _ a) (adt-ctors a)) ((None _) (Nil _)))
      (def-fns perform-lvl $ (many perform : (erased (Hist Block) h) (many (Heap h) hq) (many (Ref Block h) req) (unique (World) wo) ->
          (erased (Hist Block) h2) (many (Heap h2) hq2) (erased (Suffix Block h2 h) lq) (many (Ref Block h2) r) (unique (World) wo2 at wo))
        (let-match many hq (MkHeap _ _ _ _ crash))
        (let-match many crash (None _)
          ((Some _ m) (let ((erased hl2) (many hq2) (erased sf2) (many e)) $ halloc _ hq $ BError _ m) (values hl2 hq2 sf2 e wo)))
        (perform-request pcs rq pargs with-env base _ hq req wo))
      (def-fns perform-lvl $ (many world-prim : (erased (Hist Block) h) (many (Heap h) hq) (many (Sp) prim) (many (List $ Ref Block h) args) (unique (World) wo) ->
          (erased (Hist Block) h2) (many (Heap h2) hq2) (erased (Suffix Block h2 h) lq) (many (List $ Ref Block h2) r) (unique (World) wo2 at wo))
        (let ((erased hl2) (many hq2) (erased sf2) (many e)) $ halloc _ hq $ BError _ $ no-macro-world prim)
        (values hl2 hq2 sf2 (Cons _ e $ Nil _) wo))
      (tail $ interp-program (env-fuel env) pcs (MkPerformer (World) perform world-prim) _ hp v w1))
    ((FPlain) (tail $ interp-finals env pargs with-env _ rest _ hp le $ say-to (BFalse) (str-cat (final-text _ hp v env ty) "\n") w))
    ((FThunk t)
      (let ((erased h1) (many hp1) (erased le1) (many vs) (erased pk) (unique (Unit) u1)) (apply (env-fuel env) _ hp v (Nil _) many-one _ compile-time u))
      (let ((many r)) (vals-one _ vs pk))
      (let-match many (heap-crash _ hp1) (None _) ((Some _ m) (runtime-error m w)))
      (tail $ interp-finals env pargs with-env _ rest _ hp1 (hist-le-trans _ _ _ le le1) $ say-to (BFalse) (str-cat (final-text _ hp1 r env t) "\n") w))
    ((FMain)
      (let ((unique w1) (many input)) (world-do _ w (ReadRemaining)))
      (let ((erased h1) (many hp1) (erased le1) (many s)) (alloc-ext _ hp (PStr input)))
      (let ((erased h2) (many hp2) (erased le2) (many vs) (erased pk) (unique (Unit) u1)) (apply (env-fuel env) _ hp1 (widen-ref _ _ le1 v) (Cons _ s (Nil _)) many-one _ compile-time u))
      (let ((erased le12)) (hist-le-trans _ _ _ le1 le2))
      (let ((many r)) (vals-one _ vs pk))
      (let-match many (heap-crash _ hp2) (None _) ((Some _ m) (runtime-error m w1)))
      (tail $ interp-finals env pargs with-env _ rest _ hp2 (hist-le-trans _ _ _ le le12) $ say-to (BFalse) (heap-str _ hp2 r) w1))))
