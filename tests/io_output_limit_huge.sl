; externs: only
; expect: huge unlimited ok
; expect: lower ok
; expect: huge refused
; stderr: runtime error: output limit exceeded: this request would bring the program's approximate output to 71 bytes, over its limit of 50
; exit: 1

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns PA $ (many report : (erased Type A) (many (String) label) (many (Result A) r) (unique (IO P) next) -> (unique (IO P) io))
  (WriteOut P (str-append label $ match many r (((String) _)) ((Ok a x) " ok\n") ((Fail a m) " refused\n"))
    (unique-thunk _ _ next)))

(def-unique P $ (unique s3 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report _ "huge" r (report _ "this line does not fit" r (Exit P code0))))

(def-unique P $ (unique s2 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report _ "lower" r (ConfineOutputBytes P 1180591620717411303424 s3)))

(def-unique P $ (unique s1 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report _ "huge unlimited" r (ConfineOutputBytes P 50 s2)))

(ConfineOutputBytes P 1180591620717411303424 s1)
