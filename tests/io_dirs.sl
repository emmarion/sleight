; expect: made
; expect: again
; expect: a.txt
; expect: b.txt
; expect: not empty
; expect: cleaned
; expect: absent
; MkDir reports Changed the first time and Unchanged the second; DeleteDir refuses a directory that still
; holds entries and reports Unchanged for one that was never there; ListDir sorts and drops "." and "..".

(def-lvl P0)
(def-lvl P)
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (many d1) (lt-dec 1 u8-modulus))
(comptime-match d1 (Yes za1 zb1 zp1))
(let (many code1) (MkU8 1 zp1))
(let (erased str-p0) (prove-predates str-lvl P0))
(let (erased p0-p) (prove-predates P0 P))
(let (erased thunk-p) (prove-predates thunk-lvl P))
(let (erased thunk-p0) (prove-predates thunk-lvl P0))

(def-fns P $ many gone-again : (many (Result (Change)) o) -> (many (IO P) next)
  (match many o _
    ((Ok a c)
      (match many c _
        ((Changed) (WriteOut P "deleted twice\n" (thunk (predates thunk-p) _ _ (Exit P code1))))
        ((Unchanged) (WriteOut P "absent\n" (thunk (predates thunk-p) _ _ (Exit P code0))))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many dir-gone : (many (Result (Change)) o) -> (many (IO P) next)
  (match many o _
    ((Ok a c)
      (match many c _
        ((Changed) (WriteOut P "cleaned\n" (thunk (predates thunk-p) _ _ (DeleteFile P "io-dir-test/a.txt" gone-again))))
        ((Unchanged) (WriteOut P "never made\n" (thunk (predates thunk-p) _ _ (Exit P code1))))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many drop-b : (many (Result (Change)) o) -> (many (IO P) next)
  (DeleteDir P "io-dir-test" dir-gone))

(def-fns P $ many drop-a : (many (Result (Change)) o) -> (many (IO P) next)
  (DeleteFile P "io-dir-test/b.txt" drop-b))

(def-fns P $ many full-dir : (many (Result (Change)) o) -> (many (IO P) next)
  (match many o _
    ((Ok a c) (WriteOut P "removed a full directory\n" (thunk (predates thunk-p) _ _ (Exit P code1))))
    ((Fail a m) (WriteOut P "not empty\n" (thunk (predates thunk-p) _ _ (DeleteFile P "io-dir-test/a.txt" drop-a))))))

(def-fns P0 $ many show-entries : (subterm many (List (String)) es) -> (many (IO P) next)
  (match many es _
    ((Nil a) (DeleteDir P "io-dir-test" full-dir))
    ((Cons a e rest)
      (WriteOut P (str-append (predates str-p0) e "\n") (thunk (predates thunk-p0) _ _ (show-entries (subterm _) rest))))))

(def-fns P $ many listed : (many (Result (List (String))) r) -> (many (IO P) next)
  (match many r _
    ((Ok a es) (show-entries (predates p0-p) es))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many wrote-a : (many (Result (Unit)) o) -> (many (IO P) next)
  (ListDir P "io-dir-test" listed))

(def-fns P $ many wrote-b : (many (Result (Unit)) o) -> (many (IO P) next)
  (WriteFile P "io-dir-test/a.txt" "" wrote-a))

(def-fns P $ many made-twice : (many (Result (Change)) o) -> (many (IO P) next)
  (match many o _
    ((Ok a c)
      (match many c _
        ((Changed) (WriteOut P "made twice\n" (thunk (predates thunk-p) _ _ (Exit P code1))))
        ((Unchanged) (WriteOut P "again\n" (thunk (predates thunk-p) _ _ (WriteFile P "io-dir-test/b.txt" "" wrote-b))))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many made-once : (many (Result (Change)) o) -> (many (IO P) next)
  (match many o _
    ((Ok a c)
      (match many c _
        ((Changed) (WriteOut P "made\n" (thunk (predates thunk-p) _ _ (MkDir P "io-dir-test" made-twice))))
        ((Unchanged) (WriteOut P "already there\n" (thunk (predates thunk-p) _ _ (Exit P code1))))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many swept-dir : (many (Result (Change)) o) -> (many (IO P) next)
  (MkDir P "io-dir-test" made-once))

(def-fns P $ many swept-b : (many (Result (Change)) o) -> (many (IO P) next)
  (DeleteDir P "io-dir-test" swept-dir))

(def-fns P $ many swept-a : (many (Result (Change)) o) -> (many (IO P) next)
  (DeleteFile P "io-dir-test/b.txt" swept-b))

(DeleteFile P "io-dir-test/a.txt" swept-a)
