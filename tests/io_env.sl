; env: SL_B=two
; env: SL_A=one
; expect: one
; expect: absent
; expect: SL_A=one
; expect: SL_B=two
; GetEnv answers with Maybe; GetEnvs lists the whole environment sorted by name, whatever order it was given in.

(def-lvl P0)
(def-lvl P)
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (erased str-p0) (prove-predates str-lvl P0))
(let (erased str-p) (prove-predates str-lvl P))
(let (erased p0-p) (prove-predates P0 P))
(let (erased thunk-p) (prove-predates thunk-lvl P))
(let (erased thunk-p0) (prove-predates thunk-lvl P0))

(def-fns P0 $ many show-vars : (subterm many (List (Pair (String) (String))) vars) -> (many (IO P) next)
  (match many vars _
    ((Nil a) (Exit P code0))
    ((Cons a v rest)
      (match many v _
        ((MkPair b c name value)
          (WriteOut P
            (str-append (predates str-p0) name (str-append (predates str-p0) "=" (str-append (predates str-p0) value "\n")))
            (thunk (predates thunk-p0) _ _ (show-vars (subterm _) rest))))))))

(def-fns P $ many after-envs : (many (List (Pair (String) (String))) vars) -> (many (IO P) next)
  (show-vars (predates p0-p) vars))

(def-fns P $ many after-absent : (many (Maybe (String)) value) -> (many (IO P) next)
  (match many value _
    ((None a) (WriteOut P "absent\n" (thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))
    ((Some a s) (WriteOut P "present\n" (thunk (predates thunk-p) _ _ (GetEnvs P after-envs))))))

(def-fns P $ many after-a : (many (Maybe (String)) value) -> (many (IO P) next)
  (match many value _
    ((None a) (WriteOut P "absent\n" (thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))
    ((Some a s) (WriteOut P (str-append (predates str-p) s "\n") (thunk (predates thunk-p) _ _ (GetEnv P "SL_NONE" after-absent))))))

(GetEnv P "SL_A" after-a)
