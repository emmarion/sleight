; env: SL_B=two
; env: SL_A=one
; no-env: yes
; expect: absent
; expect: absent
; Under --no-env the program sees an empty environment, whatever the host holds: GetEnv answers None and GetEnvs Nil.

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

(def-fns PA $ (many show-vars : (subterm many (List (Pair (String) (String))) vars) -> (unique (IO P) next))
  (let-match many vars (Cons a v rest) ((Nil a) (Exit P code0)))
  (let-match many v (MkPair b c name value))
  (WriteOut P
    (str-append (predates str-pa) name (str-append (predates str-pa) "=" (str-append (predates str-pa) value "\n")))
    (unique-thunk (predates thunk-pa) _ _ (notail $ show-vars (subterm _) rest))))

(def-unique P $ (unique after-envs : (many (List (Pair (String) (String))) vars) -> (unique (IO P) next))
  (show-vars (predates pa-p) vars))

(def-unique P $ (unique after-absent : (many (Maybe (String)) value) -> (unique (IO P) next))
  (match many value _
    ((None a) (WriteOut P "absent\n" (unique-thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))
    ((Some a s) (WriteOut P "present\n" (unique-thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))))

(def-unique P $ (unique after-a : (many (Maybe (String)) value) -> (unique (IO P) next))
  (match many value _
    ((None a) (WriteOut P "absent\n" (unique-thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))
    ((Some a s) (WriteOut P (str-append (predates str-p) s "\n") (unique-thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))))

(GetEnv P "SL_A" after-a)
; warns: tests/io_no_env.sl:23:86: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:23:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:23:17: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:24:63: warning: unnecessary `(subterm _)`; drop it
; warns: tests/io_no_env.sl:24:19: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:27:14: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:31:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:32:55: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:36:52: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:37:41: warning: unnecessary `(predates _)`; drop it
; warns: tests/io_no_env.sl:37:80: warning: unnecessary `(predates _)`; drop it
