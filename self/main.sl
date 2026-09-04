; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, prelude first, elaborating them in one scope in order, and writing the extracted OCaml to
; stdout; elaboration errors go to stderr with exit code 1.

(def-lvl util-lvl)
(def-lvl compile-lvl)
(def-lvl slc-lvl)
(def-lvl io-lvl)

(let (many exit-ok) (nat-to-u8 0))
(let (many exit-fail) (nat-to-u8 1))

(def-fns util-lvl $ many write-errors : (subterm many (List (String)) es) (many (IO io-lvl) next) -> (many (IO io-lvl) io)
  (match many es _
    ((Nil a) next)
    ((Cons a e rest) (WriteErr io-lvl e (WriteErr io-lvl "\n" (write-errors (subterm _) rest next))))))

; Each source with its path, which the messages name; a syntax error ends that file's reading.
(def-fns util-lvl $ many run-files : (subterm many (List (Pair (String) (String))) srcs) (many (Env) env) -> (many (Env) r)
  (match many srcs _
    ((Nil a) env)
    ((Cons a ps rest)
      (match many ps _
        ((MkPair s t path src)
          (let (many env1) (env-at-loc (predates _) env (MkLoc path 1)))
          (let (many items) (many err) (parse (predates _) src))
          (match many err _
            ((Some b e) (match many e _ ((MkSynErr line m) (run-files (subterm _) rest (env-report (predates _) env1 (located (predates _) (env-at (predates _) env1 line) ": syntax error: " m))))))
            ((None b) (run-files (subterm _) rest (run-toplevel (predates _) items env1)))))))))

(def-fns compile-lvl $ many compile : (many (List (Pair (String) (String))) srcs) -> (many (IO io-lvl) io)
  (let (many env) (run-files (predates _) srcs (make-builtins (predates _))))
  (match many (env-errors (predates _) env) _
    ((Cons a e rest) (write-errors (predates _) (list-rev (predates _) (String) (env-errors (predates _) env)) (Exit io-lvl exit-fail)))
    ((Nil a) (rope-io (predates _) io-lvl (emit-program (predates _) env) (Exit io-lvl exit-ok)))))

(def-fns slc-lvl $ many read-files : (many (List (String)) paths) (many (List (Pair (String) (String))) acc) -> (many (IO io-lvl) io)
  (match many paths _
    ((Nil a) (compile (predates _) (list-rev (predates _) (Pair (String) (String)) acc)))
    ((Cons a path rest)
      (def-fns io-lvl $ many after-read : (many (Result (String)) r) -> (many (IO io-lvl) next)
        (match many r _
          ((Fail b m) (WriteErr io-lvl "slc: " (WriteErr io-lvl m (WriteErr io-lvl "\n" (Exit io-lvl exit-fail)))))
          ((Ok b src) (read-files (predates _) rest (Cons (Pair (String) (String)) (MkPair (String) (String) path src) acc)))))
      (ReadFile io-lvl path after-read))))

(def-fns io-lvl $ many start : (many (List (String)) args) -> (many (IO io-lvl) io)
  (match many args _
    ((Nil a) (WriteErr io-lvl "usage: slc -- prelude.sl file.sl ... > out.ml\n" (Exit io-lvl exit-fail)))
    ((Cons a p rest) (read-files (predates _) args (Nil (Pair (String) (String)))))))

(GetArgs io-lvl start)
