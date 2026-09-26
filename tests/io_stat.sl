; expect: onetwo
; expect: file
; expect: missing
; expect: cwd: dir
; AppendFile adds to what WriteFile left; Stat names what a path holds, Missing being an ordinary answer.
; GetCwd's value is the machine's, so the test asks Stat what it names rather than printing it.

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(let ((erased str-p)) (prove-predates str-lvl P))
(let ((erased pa-p)) (prove-predates PA P))
(let ((erased thunk-p)) (prove-predates thunk-lvl P))

(def-fns PA $ (many kind-name : (many (EntryKind) k) -> (many (String) s))
  (match many k _
    ((IsFile) "file")
    ((IsDir) "dir")
    ((IsOther) "other")
    ((Missing) "missing")))

(def-unique P $ (unique cleaned : (many (Result (Change)) o) -> (unique (IO P) next))
  (Exit P code0))

(def-unique P $ (unique cwd-kind : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (let-match many r (Ok a k) ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code1)))))
  (WriteOut P (str-append (predates str-p) "cwd: " (str-append (predates str-p) (kind-name (predates pa-p) k) "\n"))
    (unique-thunk (predates thunk-p) _ _ (DeleteFile P "io-stat-test.txt" cleaned))))

(def-unique P $ (unique got-cwd : (many (String) path) -> (unique (IO P) next))
  (Stat P path cwd-kind))

(def-unique P $ (unique none-kind : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a k) (WriteOut P (str-append (predates str-p) (kind-name (predates pa-p) k) "\n") (unique-thunk (predates thunk-p) _ _ (GetCwd P got-cwd))))
    ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-unique P $ (unique file-kind : (many (Result (EntryKind)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a k) (WriteOut P (str-append (predates str-p) (kind-name (predates pa-p) k) "\n") (unique-thunk (predates thunk-p) _ _ (Stat P "io-stat-test-none" none-kind))))
    ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-unique P $ (unique read-back : (many (Result (String)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a s) (WriteOut P (str-append (predates str-p) s "\n") (unique-thunk (predates thunk-p) _ _ (Stat P "io-stat-test.txt" file-kind))))
    ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-unique P $ (unique appended : (many (Result (Unit)) o) -> (unique (IO P) next))
  (ReadFile P "io-stat-test.txt" read-back))

(def-unique P $ (unique wrote : (many (Result (Unit)) o) -> (unique (IO P) next))
  (AppendFile P "io-stat-test.txt" "two" appended))

(def-unique P $ (unique swept : (many (Result (Change)) o) -> (unique (IO P) next))
  (WriteFile P "io-stat-test.txt" "one" wrote))

(DeleteFile P "io-stat-test.txt" swept)
