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
    ((Cons a e rest) (WriteErr io-lvl "slc: error: " (WriteErr io-lvl e (WriteErr io-lvl "\n" (write-errors (subterm _) rest next)))))))

(def-fns util-lvl $ many run-files : (subterm many (List (String)) srcs) (many (Env) env) -> (many (Env) r)
  (match many srcs _
    ((Nil a) env)
    ((Cons a src rest) (run-files (subterm _) rest (run-toplevel (predates _) (parse (predates _) src) env)))))

(def-fns compile-lvl $ many compile : (many (List (String)) srcs) -> (many (IO io-lvl) io)
  (let (many env) (run-files (predates _) srcs (make-builtins (predates _))))
  (match many (env-errors (predates _) env) _
    ((Cons a e rest) (write-errors (predates _) (list-rev (predates _) (String) (env-errors (predates _) env)) (Exit io-lvl exit-fail)))
    ((Nil a) (rope-io (predates _) io-lvl (emit-program (predates _) env) (Exit io-lvl exit-ok)))))

(def-fns slc-lvl $ many read-files : (many (List (String)) paths) (many (List (String)) acc) -> (many (IO io-lvl) io)
  (match many paths _
    ((Nil a) (compile (predates _) (list-rev (predates _) (String) acc)))
    ((Cons a path rest)
      (def-fns io-lvl $ many after-read : (many (Result (String)) r) -> (many (IO io-lvl) next)
        (match many r _
          ((Fail b m) (WriteErr io-lvl "slc: " (WriteErr io-lvl m (WriteErr io-lvl "\n" (Exit io-lvl exit-fail)))))
          ((Ok b src) (read-files (predates _) rest (Cons (String) src acc)))))
      (ReadFile io-lvl path after-read))))

(def-fns io-lvl $ many start : (many (List (String)) args) -> (many (IO io-lvl) io)
  (match many args _
    ((Nil a) (WriteErr io-lvl "usage: slc -- prelude.sl file.sl ... > out.ml\n" (Exit io-lvl exit-fail)))
    ((Cons a p rest) (read-files (predates _) args (Nil (String))))))

(GetArgs io-lvl start)
