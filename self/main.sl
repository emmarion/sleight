; self/main.sl -- the compiler's entry point: a Program (DESIGN.md section 42) reading the files named on its
; command line, elaborating them in one scope in order after the prelude (embedded as lib/embed.sl's
; prelude-source), and writing the extracted OCaml to stdout as one string, or under --interpret performing
; the program itself (self/interp.sl); elaboration errors go to stderr with exit code 1. The levels are
; minted in self/interp.sl.

(def-fns util-lvl $ (many write-lines : (subterm many (List $ String) es) (unique (World) w) -> (unique (World) w2 at w))
  (let-match many es (Cons _ e rest) ((Nil _) w))
  (tail $ write-lines rest $ say-to (BTrue) "\n" $ say-to (BTrue) e w))

; Each source with its path, which the messages name; a syntax error ends that file's reading. The first
; source is the prelude, whose scope the generated forms of unary elaborate in (lib/builtin.ml).
(def-fns util-lvl $ (many run-files : (unique (ElabWorld) ew) (many (Bool) notes) (subterm many (List $ Pair (String) $ String) srcs) (many (Env) env) (many (Bool) first) -> (unique (ElabWorld) ewr at ew) (many (Env) r))
  (let-match many srcs (Cons _ ps rest) ((Nil _) (values ew env)))
  (let-match many ps (MkPair _ _ path src))
  (let ((many env1)) $ env-at-loc env $ MkLoc path $ MkSpot 1 1)
  (let ((many ws)) $ indent-warnings notes path src)
  (let ((many envw)) $ env-warn-all env1 ws)
  (let ((many items) (many err) (many regions)) $ parse src)
  (let ((unique ew1) (many (Env) env2))
    (match many err (((ElabWorld) _ at ew) ((Env) env2))
      ((Some _ e)
        (let-match many e (MkSynErr pos m paren note))
        (let ((many shape)) $ match many (and notes $ and paren $ list-is-empty _ ws) (((List $ String) _)) ((BTrue) (Cons _ (shape-note path) $ Nil _)) ((BFalse) (Nil _)))
        (let ((many lines)) $ match many note (((List $ String) _))
          ((None _) shape)
          ((Some _ pn) (match many pn _ ((MkPair _ _ np nm) (Cons _ (located (env-at envw np) ": note: " nm) shape)))))
        (values ew (env-fail envw $ join-strs (Cons _ (located (env-at envw pos) ": syntax error: " m) lines) "\n")))
      ((None _) (let ((unique ew2) (many envt)) $ run-toplevel ew expansion-limit items 0 first $ env-set-regions envw regions) (values ew2 (end-file envt)))))
  (tail $ run-files ew1 notes rest (match many first (((Env) _)) ((BTrue) (env-set-externs (env-set-prelude env2 $ env-scope env2) $ BFalse)) ((BFalse) env2)) $ BFalse))

(def-fns util-lvl $ (many src-paths : (subterm many (List $ Pair (String) $ String) srcs) -> (many (List $ String) r))
  (let-match many srcs (Cons _ ps rest) ((Nil _) (Nil _)))
  (let-match many ps (MkPair _ _ path _))
  (Cons _ path $ notail $ src-paths rest))

(def-fns util-lvl $ (many shown : (many (Bool) first-only) (subterm many (List $ Said) ss) (many (Bool) seen) (many (List $ MsgMeta) table) -> (many (List $ String) r))
  (let-match many ss (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many lo) (many text) (many err)) $ match many x (((Loc) _) ((Maybe $ String) _) ((Bool) _))
    ((SaidWarning sl t) (values sl (Some _ t) $ BFalse))
    ((SaidError sl t) (values sl (Some _ t) $ BTrue))
    (else (values (MkLoc "" $ MkSpot 0 0) (None _) $ BFalse)))
  (let-match many text (Some _ t) ((None _) (tail $ shown first-only rest seen table)))
  (let-match many (and first-only seen) (BFalse) ((BTrue) (Cons _ "slc: stopped at the first error (--first-error)" $ Nil _)))
  (let ((many t2) (many table2)) $ resolve-marks lo t table)
  (Cons _ t2 $ notail $ shown first-only rest (or seen err) table2))

(def-fns util-lvl $ (many failed : (many (String) m) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (values (say-to (BTrue) (str-cat3 "slc: " m "\n") w) (Exit _ exit-fail)))

(def-fns run-lvl $ (many usage : (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (failed "usage: slc [--no-prelude] [--no-templates] [--interpret] [--confine-dir dir] [--confine-output-bytes n] [--eval-fuel n] [--no-env] [--first-error] [--warnings-as-errors] [--warn-unused] [--fn-same] [--no-shape-note] [--hints file] file.sl ... [-- arg ...] > out.ml" w))

(def-fns run-lvl $ (many run-program : (many (Env) env) (many (List $ String) pargs) (many (Bool) with-env) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let ((erased hs) (many h)) (env-heap env))
  (interp-finals env pargs with-env _ (list-rev _ $ heap-finals _ h) _ h (le-refl hs) w))

(def-fns compile-lvl $ (many compile : (many (List $ Pair (String) $ String) flags) (many (List $ String) pargs) (many (String) help) (many (List $ Pair (String) $ String) srcs) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let ((many prelude)) $ not $ has-flag flags "--no-prelude")
  (let ((many with-env)) $ not $ has-flag flags "--no-env")
  (let ((many bytes)) $ flag-value flags "--confine-output-bytes")
  (let ((many fence)) $ match many (flag-value flags "--confine-dir") (((String) _)) ((Some _ d) d) ((None _) "/"))
  (let ((many sources)) $ list-drop _ (match many prelude (((Nat) _)) ((BTrue) 1) ((BFalse) 0)) $ src-paths srcs)
  (let ((many fuel)) $ flag-value flags "--eval-fuel")
  (let-match many (match many fuel (((Bool) _)) ((Some _ f) (and (not $ str-eq f "") (all-digits f))) ((None _) (BTrue))) (BTrue) ((BFalse) (failed "--eval-fuel takes a number of steps" w)))
  (let ((many base-env)) (env-set-sources (env-set-help (env-place-at (make-builtins) null-id $ TVar null-id) help) sources))
  (let ((many builtins)) $ env-set-fn-same (match many fuel (((Env) _)) ((Some _ f) (env-set-fuel base-env $ parse-nat f $ Zero)) ((None _) base-env)) $ has-flag flags "--fn-same")
  (let ((unique ew)) (MkElabWorld w))
  (let ((unique ew1) (many env)) $ run-files ew (not $ has-flag flags "--no-shape-note") srcs (env-set-warn-unused (env-set-externs (match many prelude (((Env) _)) ((BTrue) builtins) ((BFalse) (env-set-prelude builtins $ env-scope builtins))) $ BTrue) $ has-flag flags "--warn-unused") prelude)
  (let-match unique ew1 (MkElabWorld w0))
  (let ((many by-warnings)) $ and (has-flag flags "--warnings-as-errors") $ and (not $ env-failed env) $ said-failed (BTrue) $ env-said env)
  (let ((unique w1)) $ write-lines (match many by-warnings (((List $ String) _)) ((BTrue) (Cons _ "slc: warnings are treated as errors (--warnings-as-errors)" $ Nil _)) ((BFalse) (Nil _)))
    $ write-lines (shown (has-flag flags "--first-error") (list-rev _ $ env-said env) (BFalse) $ Nil _) w0)
  (let-match many (or (env-failed env) by-warnings) (BFalse) ((BTrue) (values w1 (Exit _ exit-fail))))
  (let-match many (has-flag flags "--interpret") (BTrue)
    ((BFalse)
      (let ((many out) (erased _)) $ flatten $ emit-program (not $ has-flag flags "--no-templates") fence bytes with-env env)
      (values (say-to (BFalse) out w1) (Exit _ exit-ok))))
  (let ((unique w2) (many confined)) (world-do _ w1 (ConfineDir fence)))
  (let-match many confined (Ok _ _) ((Fail _ m) (failed m w2)))
  (let-match many bytes (Some _ b) ((None _) (run-program env pargs with-env w2)))
  (let-match many (and (not $ str-eq b "") (all-digits b)) (BTrue) ((BFalse) (failed (str-cat b ": not a number of bytes") w2)))
  (let ((unique w3) (many limited)) (world-do _ w2 (ConfineOutputBytes $ parse-nat b $ Zero)))
  (let-match many limited (Ok _ _) ((Fail _ m) (failed m w3)))
  (run-program env pargs with-env w3))

(def-fns slc-lvl $ (many read-files : (many (List $ Pair (String) $ String) flags) (many (List $ String) pargs) (many (String) help) (subterm many (List $ String) paths) (many (List $ Pair (String) $ String) acc) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let-match many paths (Cons _ path rest) ((Nil _) (compile flags pargs help (list-rev _ acc) w)))
  (let ((unique w1) (many r)) (world-do _ w (ReadFile path)))
  (let-match many r (Ok _ src) ((Fail _ m) (failed m w1)))
  (tail $ read-files flags pargs help rest (Cons _ (MkPair _ _ path src) acc) w1))

; The files up to a "--", and the interpreted program's own arguments after it.
(def-fns util-lvl $ (many split-args : (subterm many (List $ String) args) -> (many (List $ String) files) (many (List $ String) pargs))
  (let-match many args (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many (str-eq p "--") (BFalse) ((BTrue) (values (Nil _) rest)))
  (let ((many files) (many pargs)) (notail $ split-args rest))
  (values (Cons _ p files) pargs))

; Without --no-prelude the embedded prelude goes ahead of the files, under the path the reference names it
; by (lib/builtin.ml).
(def-fns start-lvl $ (many start-with : (many (List $ String) args) (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let ((many before) (many pargs)) (split-args args))
  (let-match many (read-flags before (Nil _) (Nil _)) (Ok _ read) ((Fail _ m) (failed m w)))
  (let-match many read (MkPair _ _ flags files))
  (let-match many (list-is-empty _ files) (BFalse) ((BTrue) (usage w)))
  (let ((many srcs)) $ match many (has-flag flags "--no-prelude") (((List $ Pair (String) $ String) _))
    ((BTrue) (Nil _))
    ((BFalse) (Cons _ (MkPair _ _ "lib/prelude.sl" prelude-source) $ Nil _)))
  (let-match many (flag-value flags "--hints") (Some _ h) ((None _) (read-files flags pargs specials-help files srcs w)))
  (let ((unique w1) (many r)) (world-do _ w (ReadFile h)))
  (let-match many r (Ok _ text) ((Fail _ m) (failed m w1)))
  (read-files flags pargs text files srcs w1))

(def-unique io-lvl $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program io-lvl) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (start-with args w1))

(Continue _ start)
