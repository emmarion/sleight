; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, elaborating them in one scope in order after the prelude (embedded as header.sl's
; prelude-source), and writing the extracted OCaml to stdout as one string, or under --interpret performing
; the program itself (self/interp.sl); elaboration errors go to stderr with exit code 1. The levels are
; minted in self/interp.sl.

(let ((erased th-util)) (prove-predates thunk-lvl util-lvl))
(let ((erased th-compile)) (prove-predates thunk-lvl compile-lvl))
(let ((erased th-io)) (prove-predates thunk-lvl io-lvl))

(def-fns util-lvl $ (many write-lines : (subterm many (List $ String) es) (unique (IO io-lvl) next) -> (unique (IO io-lvl) io))
  (match many es _
    ((Nil _) next)
    ((Cons _ e rest)
      (WriteErr _ e $ unique-thunk (predates th-util) _ _ $ WriteErr _ "\n" $ unique-thunk (predates th-util) _ _ $ notail $ write-lines rest next))))

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
        (let ((many enve0)) $ env-report envw $ located (env-at envw pos) ": syntax error: " m)
        (let ((many enve)) $ match many note (((Env) _))
          ((None _) enve0)
          ((Some _ pn) (match many pn _ ((MkPair _ _ np nm) (env-report enve0 $ located (env-at envw np) ": note: " nm)))))
        (match many (and paren $ list-is-empty _ ws) _ ((BTrue) (env-report enve $ shape-note path)) ((BFalse) enve)))))
      ((None _) (end-file $ run-toplevel items $ env-set-regions envw regions))))
  (tail $ run-files rest (match many first (((Env) _)) ((BTrue) (env-set-prelude env2 $ env-scope env2)) ((BFalse) env2)) $ BFalse))

(def-fns compile-lvl $ (many compile : (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ Pair (String) $ String) srcs) -> (unique (IO io-lvl) io))
  (let ((many builtins)) (make-builtins))
  (let ((many env)) $ run-files srcs (match many prelude (((Env) _)) ((BTrue) builtins) ((BFalse) (env-set-prelude builtins $ env-scope builtins))) prelude)
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

(def-fns slc-lvl $ (many read-files : (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) (many (List $ String) pargs) (many (List $ String) paths) (many (List $ Pair (String) $ String) acc) -> (unique (IO io-lvl) io))
  (let-match many paths (Cons _ path rest) ((Nil _) (compile prelude templates interpreting pargs $ list-rev _ acc)))
  (def-unique io-lvl $ (unique after-read : (many (Result $ String) r) -> (unique (IO io-lvl) next))
    (let-match many r (Fail _ m)
      ((Ok _ src) (read-files prelude templates interpreting pargs rest $ Cons _ (MkPair _ _ path src) acc)))
    (WriteErr _ "slc: " $ unique-thunk (predates th-io) _ _ $ WriteErr _ m $ unique-thunk (predates th-io) _ _
      $ WriteErr _ "\n" $ unique-thunk (predates th-io) _ _ $ Exit _ exit-fail))
  (ReadFile _ path after-read))

; The files up to a "--", and the interpreted program's own arguments after it.
(def-fns util-lvl $ (many split-args : (subterm many (List $ String) args) -> (many (List $ String) files) (many (List $ String) pargs))
  (let-match many args (Cons _ p rest) ((Nil _) (values (Nil _) (Nil _))))
  (let-match many (str-eq p "--") (BFalse) ((BTrue) (values (Nil _) rest)))
  (let ((many files) (many pargs)) (notail $ split-args rest))
  (values (Cons _ p files) pargs))

; The flags, in any order, then the files: --no-prelude, --no-templates and --interpret. Without --no-prelude
; the embedded prelude goes ahead of the files, under the path the reference names it by (lib/builtin.ml).
(def-fns start-lvl $ (many start-with : (subterm many (List $ String) args) (many (Bool) prelude) (many (Bool) templates) (many (Bool) interpreting) -> (unique (IO io-lvl) io))
  (match many args _
    ((Nil _)
      (WriteErr _ "usage: slc [--no-prelude] [--no-templates] [--interpret] file.sl ... [-- arg ...] > out.ml\n"
        $ unique-thunk _ _ $ Exit _ exit-fail))
    ((Cons _ p rest)
      (let-match many (str-eq p "--no-prelude") (BFalse) ((BTrue) (tail $ start-with rest (BFalse) templates interpreting)))
      (let-match many (str-eq p "--no-templates") (BFalse) ((BTrue) (tail $ start-with rest prelude (BFalse) interpreting)))
      (let-match many (str-eq p "--interpret") (BFalse) ((BTrue) (tail $ start-with rest prelude templates (BTrue))))
      (let ((many files) (many pargs)) (split-args args))
      (read-files prelude templates interpreting pargs files $ match many prelude _
        ((BTrue) (Cons _ (MkPair _ _ "lib/prelude.sl" prelude-source) $ Nil _))
        ((BFalse) (Nil _))))))

(def-unique io-lvl $ (unique start : (many (List $ String) args) -> (unique (IO io-lvl) io))
  (start-with args (BTrue) (BTrue) (BFalse)))

(GetArgs _ start)
