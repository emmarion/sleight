; self/main.sl -- the compiler's entry point: an IO program (ASSUMPTIONS 56) reading the files named on its
; command line, prelude first, elaborating them in one scope in order, and writing the extracted OCaml to
; stdout; elaboration errors go to stderr with exit code 1.

(def-lvl util-lvl)
(def-lvl compile-lvl)
(def-lvl slc-lvl)
(def-lvl io-lvl)

(let (many zero-below-modulus) (lt-dec 0 u8-modulus))
(comptime-match zero-below-modulus (Yes ok-a ok-b ok-lt))
(let (many exit-ok) (MkU8 0 ok-lt))
(let (many one-below-modulus) (lt-dec 1 u8-modulus))
(comptime-match one-below-modulus (Yes fail-a fail-b fail-lt))
(let (many exit-fail) (MkU8 1 fail-lt))

(def-fns util-lvl $ many write-errors : (subterm many (List (String)) es) (many (IO io-lvl) next) -> (many (IO io-lvl) io)
  (match many es _
    ((Nil a) next)
    ((Cons a e rest) (WriteErr io-lvl e (WriteErr io-lvl "\n" (write-errors rest next))))))

; Each source with its path, which the messages name; a syntax error ends that file's reading. The first
; file is the prelude, whose scope the generated forms of unary and distinct elaborate in (lib/builtin.ml).
(def-fns util-lvl $ many run-files : (subterm many (List (Pair (String) (String))) srcs) (many (Env) env) (many (Bool) first) -> (many (Env) r)
  (match many srcs _
    ((Nil a) env)
    ((Cons a ps rest)
      (match many ps _
        ((MkPair s t path src)
          (let (many env1) (env-at-loc env (MkLoc path 1)))
          (let (many items) (many err) (parse src))
          (let (many env2)
            (match many err (((Env) e))
              ((Some b e) (match many e (((Env) e)) ((MkSynErr line m) (env-report env1 (located (env-at env1 line) ": syntax error: " m)))))
              ((None b) (run-toplevel items env1))))
          (run-files rest (match many first (((Env) e)) ((BTrue) (env-set-prelude env2 (env-scope env2))) ((BFalse) env2)) (BFalse)))))))

(def-fns compile-lvl $ many compile : (many (List (Pair (String) (String))) srcs) -> (many (IO io-lvl) io)
  (let (many env) (run-files srcs (make-builtins) (BTrue)))
  (match many (env-errors env) _
    ((Cons a e rest) (write-errors (list-rev (String) (env-errors env)) (Exit io-lvl exit-fail)))
    ((Nil a) (rope-io io-lvl (emit-program env) (Exit io-lvl exit-ok)))))

(def-fns slc-lvl $ many read-files : (many (List (String)) paths) (many (List (Pair (String) (String))) acc) -> (many (IO io-lvl) io)
  (match many paths _
    ((Nil a) (compile (list-rev (Pair (String) (String)) acc)))
    ((Cons a path rest)
      (def-fns io-lvl $ many after-read : (many (Result (String)) r) -> (many (IO io-lvl) next)
        (match many r _
          ((Fail b m) (WriteErr io-lvl "slc: " (WriteErr io-lvl m (WriteErr io-lvl "\n" (Exit io-lvl exit-fail)))))
          ((Ok b src) (read-files rest (Cons (Pair (String) (String)) (MkPair (String) (String) path src) acc)))))
      (ReadFile io-lvl path after-read))))

(def-fns io-lvl $ many start : (many (List (String)) args) -> (many (IO io-lvl) io)
  (match many args _
    ((Nil a) (WriteErr io-lvl "usage: slc -- prelude.sl file.sl ... > out.ml\n" (Exit io-lvl exit-fail)))
    ((Cons a p rest) (read-files args (Nil (Pair (String) (String)))))))

(GetArgs io-lvl start)
