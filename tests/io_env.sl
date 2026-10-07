; env: SL_B=two
; env: SL_A=one
; expect: one
; expect: absent
; expect: SL_A=one
; expect: SL_B=two
; GetEnv answers with Maybe; GetEnvs lists the whole environment sorted by name, whatever order it was given in.

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((erased str-pa)) (prove-predates str-lvl PA))
(let ((erased str-p)) (prove-predates str-lvl P))
(let ((erased pa-p)) (prove-predates PA P))
(let ((erased thunk-p)) (prove-predates thunk-lvl P))
(let ((erased thunk-pa)) (prove-predates thunk-lvl PA))
; Why PWD is dropped: under OCaml 5.5.1 (and perhaps other 5.x releases), ocamlc builds a bytecode executable
; whose first line is `#!/usr/bin/sh`, a shell-script launcher that finds ocamlrun and execs it. Both test
; harnesses compile extracted programs that way and run them under `env -i` with only the variables the
; directives above give, but the launching shell sets PWD itself, so GetEnvs saw PWD as well and the listing
; gained a line. Removing it keeps the expected output the same under every compiler.
(def-fns PA $ (many drop-pwd : (subterm many (List (Pair (String) (String))) vars) -> (many (List (Pair (String) (String))) r)) (let-match many vars (Cons a v rest) ((Nil a) vars)) (let-match many v (MkPair b c name value)) (match many (str-cmp name "PWD") _ ((CEq x y z) (tail $ drop-pwd rest)) (else (Cons _ v (notail $ drop-pwd rest)))))
(def-fns PA $ (many show-vars : (subterm many (List (Pair (String) (String))) vars) -> (unique (IO P) next))
  (let-match many vars (Cons a v rest) ((Nil a) (Exit P code0)))
  (let-match many v (MkPair b c name value))
  (WriteOut P
    (str-append (predates str-pa) name (str-append (predates str-pa) "=" (str-append (predates str-pa) value "\n")))
    (unique-thunk (predates thunk-pa) _ _ (notail $ show-vars (subterm _) rest))))

(def-unique P $ (unique after-envs : (many (List (Pair (String) (String))) vars) -> (unique (IO P) next))
  (show-vars (predates pa-p) (drop-pwd vars)))

(def-unique P $ (unique after-absent : (many (Maybe (String)) value) -> (unique (IO P) next))
  (match many value _
    ((None a) (WriteOut P "absent\n" (unique-thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))
    ((Some a s) (WriteOut P "present\n" (unique-thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))))

(def-unique P $ (unique after-a : (many (Maybe (String)) value) -> (unique (IO P) next))
  (match many value _
    ((None a) (WriteOut P "absent\n" (unique-thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))
    ((Some a s) (WriteOut P (str-append (predates str-p) s "\n") (unique-thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))))

(GetEnv P "SL_A" after-a)
; warns: tests/io_env.sl:29:86: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:29:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:29:17: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:30:63: warning: unnecessary `(subterm _)`; drop it
; warns: tests/io_env.sl:30:19: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:33:14: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:37:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:38:55: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:42:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:43:41: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_env.sl:43:80: warning: unnecessary `(predates _)`; drop it
