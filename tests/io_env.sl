; env: SL_B=two
; env: SL_A=one
; expect: one
; expect: absent
; expect: SL_A=one
; expect: SL_B=two
; GetEnv answers with Maybe; GetEnvs lists the whole environment sorted by name, whatever order it was given in.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
; Why PWD and SHLVL are dropped: under OCaml 5.5 (seen with 5.5.0 and 5.5.1, perhaps other 5.x releases), ocamlc
; builds a bytecode executable whose first line is a `#!/bin/sh`-style shell-script launcher that finds ocamlrun
; and execs it. Both test harnesses compile extracted programs that way and run them under `env -i` with only the
; variables the directives above give, but the launching shell seems to set variables of its own (PWD on one
; machine, SHLVL=0 under macOS's /bin/sh), so GetEnvs saw them too. Removing them keeps the expected output the same.
(def-fns _ $ (many drop-shell-vars : (subterm many (List (Pair (String) (String))) vars) -> (many (List (Pair (String) (String))) r)) (let-match many vars (Cons _ v rest) ((Nil _) vars)) (let-match many v (MkPair _ _ name _)) (match many (str-cmp name "PWD") _ ((CEq _ _ _) (tail $ drop-shell-vars rest)) (else (match many (str-cmp name "SHLVL") _ ((CEq _ _ _) (tail $ drop-shell-vars rest)) (else (Cons _ v (notail $ drop-shell-vars rest)))))))
(def-fns _ $ (many show-vars : (subterm many (List (Pair (String) (String))) vars) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let-match many vars (Cons _ v rest) ((Nil _) w))
  (let-match many v (MkPair _ _ name value))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut (str-append name (str-append "=" (str-append value "\n"))))))
  (tail $ show-vars rest w1))

(def-fns _ $ (many show-value : (many (Maybe (String)) value) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut $ match many value (((String) _)) ((None _) "absent\n") ((Some _ s) (str-append s "\n")))))
  w1)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many a)) (world-do _ w (GetEnv "SL_A")))
  (let ((unique w2) (many none)) (world-do _ (show-value a w1) (GetEnv "SL_NONE")))
  (let ((unique w3) (many vars)) (world-do _ (show-value none w2) (GetEnvs)))
  (values (show-vars (drop-shell-vars vars) w3) (Exit P code0)))

(Continue P start)
