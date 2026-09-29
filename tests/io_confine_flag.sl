; confine: .
; expect: stat cwd ok
; expect: list parent refused
; expect: confine cwd ok
; expect: confine parent refused
; expect: read outside refused
; The driver starts confined to the directory the command line names, here the one the program runs in.

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

(def-unique P $ (unique s4 : (many (Result (String)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "read outside" r (Exit P code0)))

(def-unique P $ (unique s3 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "confine parent" r (ReadFile P "../io-confine-flag.txt" s4)))

(def-unique P $ (unique s2 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "confine cwd" r (Confine P ".." s3)))

(def-unique P $ (unique s1 : (many (Result (List (String))) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "list parent" r (Confine P "." s2)))

(def-unique P $ (unique s0 : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "stat cwd" r (ListDir P ".." s1)))

(Stat P "." s0)
