; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, prelude first, elaborating them in one scope in order, and writing the extracted OCaml to
; stdout as one string, or under --interpret performing the program itself (self/interp.sl); elaboration
; errors go to stderr with exit code 1. The levels are minted in self/interp.sl.

(let ((erased th-util)) (prove-predates thunk-lvl util-lvl))
(let ((erased th-compile)) (prove-predates thunk-lvl compile-lvl))
(let ((erased th-io)) (prove-predates thunk-lvl io-lvl))

(def-fns util-lvl $ (many write-lines : (subterm many (List $ String) es) (unique (IO io-lvl) next) -> (unique (IO io-lvl) io))
  (match many es _
    ((Nil a) next)
    ((Cons a e rest)
      (WriteErr _ e $ unique-thunk (predates th-util) _ _ $ WriteErr _ "\n" $ unique-thunk (predates th-util) _ _ $ write-lines rest next))))

; Each source with its path, which the messages name; a syntax error ends that file's reading. The first
; file is the prelude, whose scope the generated forms of unary and distinct elaborate in (lib/builtin.ml).
(def-fns util-lvl $ (many run-files : (subterm many (List $ Pair (String) $ String) srcs) (many (Env) env) (many (Bool) first) -> (many (Env) r))
  (match many srcs _
    ((Nil a) env)
    ((Cons a ps rest)
      (match many ps _
        ((MkPair s t path src)
          (let ((many env1)) $ env-at-loc env $ MkLoc path 1)
          (let ((many envw)) $ env-warn-all env1 $ indent-warnings path src)
          (let ((many items) (many err)) $ parse src)
          (let ((many (Env) env2))
            (match many err _
              ((Some b e) (match many e (((Env) e)) ((MkSynErr line m) (env-report envw $ located (env-at envw line) ": syntax error: " m))))
              ((None b) (run-toplevel items envw))))
          (run-files rest (match many first (((Env) e)) ((BTrue) (env-set-prelude env2 $ env-scope env2)) ((BFalse) env2)) $ BFalse))))))

(def-fns compile-lvl $ (many compile : (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ Pair (String) $ String) srcs) -> (unique (IO io-lvl) io))
  (let ((many env)) $ run-files srcs (make-builtins) $ BTrue)
  ; A warning stands whether or not the program is refused, so it is written ahead of either outcome, in the
  ; order elaboration minted it, as the reference writes one where it meets it.
  (write-lines (list-rev _ $ env-warnings env)
    (match many (env-errors env) (((IO io-lvl) io))
      ((Cons a e rest) (write-lines (list-rev _ $ env-errors env) $ Exit _ exit-fail))
      ((Nil a)
        (match many interpreting (((IO io-lvl) io))
          ((BTrue)
            (let ((erased hs) (many hp) (many en) (many fi)) (env-store env))
            (interp-finals env pargs _ (list-rev _ fi) _ hp en (le-refl hs)))
          ((BFalse)
            (let ((many out) (erased flat)) $ flatten $ emit-program templates env)
            (WriteOut _ out $ unique-thunk (predates th-compile) _ _ $ Exit _ exit-ok)))))))

(def-fns slc-lvl $ (many read-files : (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ String) paths) (many (List $ Pair (String) $ String) acc) -> (unique (IO io-lvl) io))
  (match many paths _
    ((Nil a) (compile templates interpreting pargs $ list-rev _ acc))
    ((Cons a path rest)
      (def-unique io-lvl $ (unique after-read : (many (Result $ String) r) -> (unique (IO io-lvl) next))
        (match many r _
          ((Fail b m)
            (WriteErr _ "slc: " $ unique-thunk (predates th-io) _ _ $ WriteErr _ m $ unique-thunk (predates th-io) _ _
              $ WriteErr _ "\n" $ unique-thunk (predates th-io) _ _ $ Exit _ exit-fail))
          ((Ok b src) (read-files templates interpreting pargs rest $ Cons _ (MkPair _ _ path src) acc))))
      (ReadFile _ path after-read))))

; The files up to a "--", and the interpreted program's own arguments after it.
(def-fns util-lvl $ (many split-args : (subterm many (List $ String) args) -> (many (List $ String) files) (many (List $ String) pargs))
  (match many args _
    ((Nil a) (values (Nil _) (Nil _)))
    ((Cons a p rest)
      (match many (str-eq p "--") _
        ((BTrue) (values (Nil _) rest))
        ((BFalse)
          (let ((many files) (many pargs)) (split-args rest))
          (values (Cons _ p files) pargs))))))

; The flags, in any order, then the files: --no-templates and --interpret.
(def-fns start-lvl $ (many start-with : (subterm many (List $ String) args) (many (Bool) templates) (many (Bool) interpreting) -> (unique (IO io-lvl) io))
  (match many args _
    ((Nil a)
      (WriteErr _ "usage: slc -- [--no-templates] [--interpret] prelude.sl file.sl ... [-- arg ...] > out.ml\n"
        $ unique-thunk _ _ $ Exit _ exit-fail))
    ((Cons a p rest)
      (match many (str-eq p "--no-templates") _
        ((BTrue) (start-with rest (BFalse) interpreting))
        ((BFalse)
          (match many (str-eq p "--interpret") _
            ((BTrue) (start-with rest templates (BTrue)))
            ((BFalse)
              (let ((many files) (many pargs)) (split-args args))
              (read-files templates interpreting pargs files $ Nil _))))))))

(def-unique io-lvl $ (unique start : (many (List $ String) args) -> (unique (IO io-lvl) io))
  (start-with args (BTrue) (BFalse)))

(GetArgs _ start)
