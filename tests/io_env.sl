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

(def-fns PA $ (many show-vars : (subterm many (List (Pair (String) (String))) vars) -> (unique (IO P) next))
  (let-match many vars (Cons a v rest) ((Nil a) (Exit P code0)))
  (match many v _
    ((MkPair b c name value)
      (WriteOut P
        (str-append (predates str-pa) name (str-append (predates str-pa) "=" (str-append (predates str-pa) value "\n")))
        (unique-thunk (predates thunk-pa) _ _ (notail $ show-vars (subterm _) rest))))))

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
