; env: SL_B=two
; env: SL_A=one
; no-env: yes
; expect: absent
; expect: absent
; Under --no-env the program sees an empty environment, whatever the host holds: GetEnv answers None and GetEnvs Nil.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many show-vars : (subterm many (List (Pair (String) (String))) vars) (unique (World) w) -> (unique (World) w2 at w))
  (let-match many vars (Cons a v rest) ((Nil a) w))
  (let-match many v (MkPair b c name value))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut (str-append name (str-append "=" (str-append value "\n"))))))
  (tail $ show-vars rest w1))

(def-fns _ $ (many show-value : (many (Maybe (String)) value) (unique (World) w) -> (unique (World) w2 at w))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut $ match many value (((String) _)) ((None a) "absent\n") ((Some a s) (str-append s "\n")))))
  w1)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many a)) (world-do _ w (GetEnv "SL_A")))
  (let ((unique w2) (many none)) (world-do _ (show-value a w1) (GetEnv "SL_NONE")))
  (let ((unique w3) (many vars)) (world-do _ (show-value none w2) (GetEnvs)))
  (values (show-vars vars w3) (Exit P code0)))

(Continue P start)
