; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, prelude first, elaborating them in one scope in order, and writing the extracted OCaml to
; stdout as one string, or under --interpret performing the program itself (self/interp.sl); elaboration
; errors go to stderr with exit code 1. The levels are minted in self/interp.sl.

(let ((erased th-util)) (prove-predates thunk-lvl util-lvl))
(let ((erased th-compile)) (prove-predates thunk-lvl compile-lvl))
(let ((erased th-io)) (prove-predates thunk-lvl io-lvl))

(def-fns util-lvl $ (many write-lines : (subterm many (List $ String) es) (unique (IO io-lvl) next) -> (unique (IO io-lvl) io))
  (match many es _
    ((Nil _) next)
    ((Cons _ e rest)
      (WriteErr _ e $ unique-thunk (predates th-util) _ _ $ WriteErr _ "\n" $ unique-thunk (predates th-util) _ _ $ write-lines rest next))))

; Each source with its path, which the messages name; a syntax error ends that file's reading. The first
; file is the prelude, whose scope the generated forms of unary and distinct elaborate in (lib/builtin.ml).
(def-fns util-lvl $ (many run-files : (subterm many (List $ Pair (String) $ String) srcs) (many (Env) env) (many (Bool) first) -> (many (Env) r))
  (match many srcs _
    ((Nil _) env)
    ((Cons _ ps rest)
      (match many ps _
        ((MkPair _ _ path src)
          (let ((many env1)) $ env-at-loc env $ MkLoc path $ MkPos 1 1)
          (let ((many ws)) $ indent-warnings path src)
          (let ((many envw)) $ env-warn-all env1 ws)
          (let ((many items) (many err)) $ parse src)
          (let ((many (Env) env2))
            (match many err _
              ((Some _ e) (match many e (((Env) _)) ((MkSynErr pos m paren)
                (let ((many enve)) $ env-report envw $ located (env-at envw pos) ": syntax error: " m)
                (match many (and paren $ list-is-empty _ ws) _ ((BTrue) (env-report enve $ shape-note path)) ((BFalse) enve)))))
              ((None _) (run-toplevel items envw))))
          (run-files rest (match many first (((Env) _)) ((BTrue) (env-set-prelude env2 $ env-scope env2)) ((BFalse) env2)) $ BFalse))))))

(def-fns compile-lvl $ (many compile : (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ Pair (String) $ String) srcs) -> (unique (IO io-lvl) io))
  (let ((many env)) $ run-files srcs (make-builtins) $ BTrue)
  ; A warning stands whether or not the program is refused, so it is written ahead of either outcome, in the
  ; order elaboration minted it, as the reference writes one where it meets it.
  (write-lines (list-rev _ $ env-warnings env)
    (match many (env-errors env) (((IO io-lvl) _))
      ((Cons _ _ _) (write-lines (list-rev _ $ env-errors env) $ Exit _ exit-fail))
      ((Nil _)
        (match many interpreting (((IO io-lvl) _))
          ((BTrue)
            (let ((erased hs) (many hp) (many en) (many fi)) (env-store env))
            (interp-finals env pargs _ (list-rev _ fi) _ hp en (le-refl hs)))
          ((BFalse)
            (let ((many out) (erased flat)) $ flatten $ emit-program templates env)
            (WriteOut _ out $ unique-thunk (predates th-compile) _ _ $ Exit _ exit-ok)))))))

(def-fns slc-lvl $ (many read-files : (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ String) paths) (many (List $ Pair (String) $ String) acc) -> (unique (IO io-lvl) io))
  (match many paths _
    ((Nil _) (compile templates interpreting pargs $ list-rev _ acc))
    ((Cons _ path rest)
      (def-unique io-lvl $ (unique after-read : (many (Result $ String) r) -> (unique (IO io-lvl) next))
        (match many r _
          ((Fail _ m)
            (WriteErr _ "slc: " $ unique-thunk (predates th-io) _ _ $ WriteErr _ m $ unique-thunk (predates th-io) _ _
              $ WriteErr _ "\n" $ unique-thunk (predates th-io) _ _ $ Exit _ exit-fail))
          ((Ok _ src) (read-files templates interpreting pargs rest $ Cons _ (MkPair _ _ path src) acc))))
      (ReadFile _ path after-read))))

; The files up to a "--", and the interpreted program's own arguments after it.
(def-fns util-lvl $ (many split-args : (subterm many (List $ String) args) -> (many (List $ String) files) (many (List $ String) pargs))
  (match many args _
    ((Nil _) (values (Nil _) (Nil _)))
    ((Cons _ p rest)
      (match many (str-eq p "--") _
        ((BTrue) (values (Nil _) rest))
        ((BFalse)
          (let ((many files) (many pargs)) (split-args rest))
          (values (Cons _ p files) pargs))))))

; The flags, in any order, then the files: --no-templates and --interpret.
(def-fns start-lvl $ (many start-with : (subterm many (List $ String) args) (many (Bool) templates) (many (Bool) interpreting) -> (unique (IO io-lvl) io))
  (match many args _
    ((Nil _)
      (WriteErr _ "usage: slc -- [--no-templates] [--interpret] prelude.sl file.sl ... [-- arg ...] > out.ml\n"
        $ unique-thunk _ _ $ Exit _ exit-fail))
    ((Cons _ p rest)
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
