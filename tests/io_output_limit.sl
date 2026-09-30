; confine-output-bytes: 10000
; expect: mkdir ok
; expect: write new ok
; expect: rewrite ok
; expect: raise refused
; expect: lower ok
; expect: delete file ok
; expect: delete dir ok
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 12383 bytes, over its limit of 9000
; exit: 1

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((erased str-pa)) (prove-predates str-lvl PA))
(let ((erased pa-p)) (prove-predates PA P))
(let ((erased thunk-pa)) (prove-predates thunk-lvl PA))

(def-fns PA $ (many report : (erased Type A) (many (String) label) (many (Result A) r) (unique (IO P) next) -> (unique (IO P) io))
  (WriteOut P (str-append (predates str-pa) label $ match many r (((String) _)) ((Ok a x) " ok\n") ((Fail a m) " refused\n"))
    (unique-thunk (predates thunk-pa) _ _ next)))

(def-unique P $ (unique s9 : (many (Result (Change)) r) -> (unique (IO P) next))
  (Exit P code0))

(def-unique P $ (unique s8 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "delete dir" r (MkDir P "io-output-limit-test" s9)))

(def-unique P $ (unique s7 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "delete file" r (DeleteDir P "io-output-limit-test" s8)))

(def-unique P $ (unique s6 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "lower" r (DeleteFile P "io-output-limit-test/a.txt" s7)))

(def-unique P $ (unique s4 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "raise" r (ConfineOutputBytes P 9000 s6)))

(def-unique P $ (unique s3 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "rewrite" r (ConfineOutputBytes P 20000 s4)))

(def-unique P $ (unique s2 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "write new" r (WriteFile P "io-output-limit-test/a.txt" "hello" s3)))

(def-unique P $ (unique s1 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "mkdir" r (WriteFile P "io-output-limit-test/a.txt" "hello" s2)))

(MkDir P "io-output-limit-test" s1)
