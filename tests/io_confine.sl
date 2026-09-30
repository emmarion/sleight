; expect: mkdir ok
; expect: confine ok
; expect: widen refused
; expect: mkdir in ok
; expect: same fence ok
; expect: write ok
; expect: read ok
; expect: stat absent ok
; expect: stat parent refused
; expect: list cwd refused
; expect: write outside refused
; expect: confine file refused
; expect: delete file ok
; expect: delete in ok
; expect: delete fence ok
; A program confines itself to a directory it made: a path the fence admits behaves as it would unconfined,
; one it does not is refused whether it names something or not, the fence only narrows, and the fence's own
; directory is inside it, so the test removes all it made.

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

(def-unique P $ (unique s14 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "delete fence" r (Exit P code0)))

(def-unique P $ (unique s13 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "delete in" r (DeleteDir P "io-confine-test" s14)))

(def-unique P $ (unique s12 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "delete file" r (DeleteDir P "io-confine-test/in" s13)))

(def-unique P $ (unique s11 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "confine file" r (DeleteFile P "io-confine-test/in/a.txt" s12)))

(def-unique P $ (unique s10 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "write outside" r (ConfineDir P "io-confine-test/in/a.txt" s11)))

(def-unique P $ (unique s9 : (many (Result (List (String))) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "list cwd" r (WriteFile P "io-confine-test/../io-confine-escape.txt" "x" s10)))

(def-unique P $ (unique s8 : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "stat parent" r (ListDir P "." s9)))

(def-unique P $ (unique s7 : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "stat absent" r (Stat P "io-confine-test/.." s8)))

(def-unique P $ (unique s6 : (many (Result (String)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "read" r (Stat P "io-confine-test/nope" s7)))

(def-unique P $ (unique s5 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "write" r (ReadFile P "io-confine-test/in/../in/a.txt" s6)))

(def-unique P $ (unique s4 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "same fence" r (WriteFile P "io-confine-test/in/a.txt" "hi" s5)))

(def-unique P $ (unique s3 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "mkdir in" r (ConfineDir P "io-confine-test/in/.." s4)))

(def-unique P $ (unique s2 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "widen" r (MkDir P "io-confine-test/in" s3)))

(def-unique P $ (unique s1 : (many (Result (Unit)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "confine" r (ConfineDir P "." s2)))

(def-unique P $ (unique s0 : (many (Result (Change)) r) -> (unique (IO P) next))
  (report (predates pa-p) _ "mkdir" r (ConfineDir P "io-confine-test" s1)))

(MkDir P "io-confine-test" s0)
