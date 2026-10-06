; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, elaborating them in one scope in order after the prelude (embedded as header.sl's
; prelude-source), and writing the extracted OCaml to stdout as one string, or under --interpret performing
; the program itself (self/interp.sl); elaboration errors go to stderr with exit code 1. The levels are
; minted in self/interp.sl.

(def-fns util-lvl $ (many write-lines : (subterm many (List $ String) es) (unique (IO io-lvl) next) -> (unique (IO io-lvl) io))
  (match many es _
    ((Nil _) next)
    ((Cons _ e rest)
      (WriteErr _ e $ unique-thunk _ _ $ WriteErr _ "\n" $ unique-thunk _ _ $ notail $ write-lines rest next))))

; Each source with its path, which the messages name; a syntax error ends that file's reading. The first
; source is the prelude, whose scope the generated forms of unary and distinct elaborate in (lib/builtin.ml).
(def-fns util-lvl $ (many run-files : (subterm many (List $ Pair (String) $ String) srcs) (many (Env) env) (many (Bool) first) -> (many (Env) r))
  (let-match many srcs (Cons _ ps rest) ((Nil _) env))
  (let-match many ps (MkPair _ _ path src))
  (let ((many env1)) $ env-at-loc env $ MkLoc path $ MkPos 1 1)
  (let ((many ws)) $ indent-warnings path src)
  (let ((many envw)) $ env-warn-all env1 ws)
  (let ((many items) (many err) (many regions)) $ parse src)
  (let ((many (Env) env2))
    (match many err _
      ((Some _ e) (match many e (((Env) _)) ((MkSynErr pos m paren note)
        (let ((many shape)) $ match many (and paren $ list-is-empty _ ws) (((List $ String) _)) ((BTrue) (Cons _ (shape-note path) $ Nil _)) ((BFalse) (Nil _)))
        (let ((many lines)) $ match many note (((List $ String) _))
          ((None _) shape)
          ((Some _ pn) (match many pn _ ((MkPair _ _ np nm) (Cons _ (located (env-at envw np) ": note: " nm) shape)))))
        (env-fail envw $ join-strs (Cons _ (located (env-at envw pos) ": syntax error: " m) lines) "\n"))))
      ((None _) (end-file $ run-toplevel items $ env-set-regions envw regions))))
  (tail $ run-files rest (match many first (((Env) _)) ((BTrue) (env-set-prelude env2 $ env-scope env2)) ((BFalse) env2)) $ BFalse))

(def-fns util-lvl $ (many shown : (many (Bool) first-only) (subterm many (List $ Said) ss) (many (Bool) seen) (many (List $ MsgMeta) table) -> (many (List $ String) r))
  (let-match many ss (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many lo) (many text) (many err)) $ match many x (((Loc) _) ((Maybe $ String) _) ((Bool) _))
    ((SaidWarning sl t) (values sl (Some _ t) $ BFalse))
    ((SaidError sl t) (values sl (Some _ t) $ BTrue))
    ((SaidSilenced _) (values (MkLoc "" $ MkPos 0 0) (None _) $ BFalse)))
  (let-match many text (Some _ t) ((None _) (tail $ shown first-only rest seen table)))
  (let-match many (and first-only seen) (BFalse) ((BTrue) (Cons _ "slc: stopped at the first error (--first-error)" $ Nil _)))
  (let ((many t2) (many table2)) $ resolve-marks lo t table)
  (Cons _ t2 $ notail $ shown first-only rest (or seen err) table2))

(def-fns util-lvl $ (many failed : (many (String) m) -> (unique (IO io-lvl) io))
  (WriteErr _ (str-cat3 "slc: " m "\n") (unique-thunk _ _ (Exit _ exit-fail))))

(def-fns util-lvl $ (many usage : -> (unique (IO io-lvl) io))
  (WriteErr _ "usage: slc [--no-prelude] [--no-templates] [--interpret] [--confine-dir dir] [--confine-output-bytes n] [--no-env] [--first-error] [--hints file] file.sl ... [-- arg ...] > out.ml\n"
    (unique-thunk _ _ (Exit _ exit-fail))))

(def-fns run-lvl $ (many run-program : (many (Env) env) (many (List $ String) pargs) (many (Bool) with-env) -> (unique (IO io-lvl) io))
  (let ((erased hs) (many hp) (many en) (many fi)) (env-store env))
  (interp-finals env pargs with-env _ (list-rev _ fi) _ hp en (le-refl hs)))

(def-fns compile-lvl $ (many compile : (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (String) fence) (many (Maybe $ String) bytes) (many (Bool) with-env) (many (Bool) first-only) (many (String) help) (many (List $ Pair (String) $ String) srcs) -> (unique (IO io-lvl) io))
  (let ((many builtins)) (env-set-help (make-builtins) help))
  (let ((many env)) $ run-files srcs (match many prelude (((Env) _)) ((BTrue) builtins) ((BFalse) (env-set-prelude builtins $ env-scope builtins))) prelude)
  (write-lines (shown first-only (list-rev _ $ env-said env) (BFalse) $ Nil _)
    (match many (env-failed env) (((IO io-lvl) _))
      ((BTrue) (Exit _ exit-fail))
      ((BFalse)
        (match many interpreting (((IO io-lvl) _))
          ((BTrue)
            (def-unique io-lvl $ (unique limited : (many (Result $ Unit) r) -> (unique (IO io-lvl) next))
              (let-match many r (Fail _ m) ((Ok _ _) (run-program env pargs with-env)))
              (failed m))
            (def-unique io-lvl $ (unique confined : (many (Result $ Unit) r) -> (unique (IO io-lvl) next))
              (let-match many r (Fail _ m) ((Ok _ _)
                (let-match many bytes (Some _ b) ((None _) (run-program env pargs with-env)))
                (let-match many (and (not $ str-eq b "") (all-digits b)) (BTrue) ((BFalse) (failed $ str-cat b ": not a number of bytes")))
                (ConfineOutputBytes _ (parse-nat b (Zero)) limited)))
              (failed m))
            (ConfineDir _ fence confined))
          ((BFalse)
            (let ((many out) (erased flat)) $ flatten $ emit-program templates fence bytes with-env env)
            (WriteOut _ out $ unique-thunk _ _ $ Exit _ exit-ok)))))))

(def-fns slc-lvl $ (many read-files : (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (String) dir) (many (Maybe $ String) bytes) (many (Bool) with-env) (many (Bool) first-only) (many (String) help) (many (List $ String) paths) (many (List $ Pair (String) $ String) acc) -> (unique (IO io-lvl) io))
  (let-match many paths (Cons _ path rest) ((Nil _) (compile prelude templates interpreting pargs dir bytes with-env first-only help $ list-rev _ acc)))
  (def-unique io-lvl $ (unique after-read : (many (Result $ String) r) -> (unique (IO io-lvl) next))
    (let-match many r (Fail _ m)
      ((Ok _ src) (read-files prelude templates interpreting pargs dir bytes with-env first-only help rest $ Cons _ (MkPair _ _ path src) acc)))
    (failed m))
  (ReadFile _ path after-read))

; The files up to a "--", and the interpreted program's own arguments after it.
(def-fns util-lvl $ (many split-args : (subterm many (List $ String) args) -> (many (List $ String) files) (many (List $ String) pargs))
  (let-match many args (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many (str-eq p "--") (BFalse) ((BTrue) (values (Nil _) rest)))
  (let ((many files) (many pargs)) (notail $ split-args rest))
  (values (Cons _ p files) pargs))

; The flags, in any order, then the files: --no-prelude, --no-templates, --interpret, --confine-dir dir, --confine-output-bytes n, --no-env, --first-error and --hints file.
; Without --no-prelude the embedded prelude goes ahead of the files, under the path the reference names it
; by (lib/builtin.ml).
(def-fns start-lvl $ (many start-with : (subterm many (List $ String) args) (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) (many (String) dir) (many (Maybe $ String) bytes) (many (Bool) with-env) (many (Bool) first-only) (many (String) help) -> (unique (IO io-lvl) io))
  (match many args _
    ((Nil _) (usage))
    ((Cons _ p rest)
      (let-match many (str-eq p "--no-prelude") (BFalse) ((BTrue) (tail $ start-with rest (BFalse) templates interpreting dir bytes with-env first-only help)))
      (let-match many (str-eq p "--no-templates") (BFalse) ((BTrue) (tail $ start-with rest prelude (BFalse) interpreting dir bytes with-env first-only help)))
      (let-match many (str-eq p "--interpret") (BFalse) ((BTrue) (tail $ start-with rest prelude templates (BTrue) dir bytes with-env first-only help)))
      (let-match many (str-eq p "--confine-dir") (BFalse)
        ((BTrue) (match many rest _ ((Nil _) (usage)) ((Cons _ d more) (tail $ start-with more prelude templates interpreting d bytes with-env first-only help)))))
      (let-match many (str-eq p "--confine-output-bytes") (BFalse)
        ((BTrue) (match many rest _ ((Nil _) (usage)) ((Cons _ b more) (tail $ start-with more prelude templates interpreting dir (Some _ b) with-env first-only help)))))
      (let-match many (str-eq p "--no-env") (BFalse) ((BTrue) (tail $ start-with rest prelude templates interpreting dir bytes (BFalse) first-only help)))
      (let-match many (str-eq p "--first-error") (BFalse) ((BTrue) (tail $ start-with rest prelude templates interpreting dir bytes with-env (BTrue) help)))
      (let-match many (str-eq p "--hints") (BFalse)
        ((BTrue) (match many rest _ ((Nil _) (usage)) ((Cons _ h more)
          (def-unique io-lvl $ (unique after-hints : (many (Result $ String) r) -> (unique (IO io-lvl) next))
            (let-match many r (Ok _ text) ((Fail _ m) (failed m)))
            (start-with more prelude templates interpreting dir bytes with-env first-only text))
          (ReadFile _ h after-hints)))))
      (let ((many files) (many pargs)) (split-args args))
      (read-files prelude templates interpreting pargs dir bytes with-env first-only help files $ match many prelude _
        ((BTrue) (Cons _ (MkPair _ _ "lib/prelude.sl" prelude-source) $ Nil _))
        ((BFalse) (Nil _))))))

(def-unique io-lvl $ (unique start : (many (List $ String) args) -> (unique (IO io-lvl) io))
  (start-with args (BTrue) (BTrue) (BFalse) "/" (None _) (BTrue) (BFalse) specials-help))

(GetArgs _ start)
