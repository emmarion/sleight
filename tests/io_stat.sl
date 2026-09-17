; expect: onetwo
; expect: file
; expect: missing
; expect: cwd: dir
; AppendFile adds to what WriteFile left; Stat names what a path holds, Missing being an ordinary answer.
; GetCwd's value is the machine's, so the test asks Stat what it names rather than printing it.

(def-lvl P0)
(def-lvl P)
(let (many d0) (lt-dec 0 u8-modulus))
(comptime-match d0 (Yes za0 zb0 zp0))
(let (many code0) (MkU8 0 zp0))
(let (many d1) (lt-dec 1 u8-modulus))
(comptime-match d1 (Yes za1 zb1 zp1))
(let (many code1) (MkU8 1 zp1))
(let (erased str-p) (prove-predates str-lvl P))
(let (erased p0-p) (prove-predates P0 P))
(let (erased thunk-p) (prove-predates thunk-lvl P))

(def-fns P0 $ many kind-name : (many (EntryKind) k) -> (many (String) s)
  (match many k _
    ((IsFile) "file")
    ((IsDir) "dir")
    ((IsOther) "other")
    ((Missing) "missing")))

(def-fns P $ many cleaned : (many (Result (Change)) o) -> (many (IO P) next)
  (Exit P code0))

(def-fns P $ many cwd-kind : (many (Result (EntryKind)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a k)
      (WriteOut P (str-append (predates str-p) "cwd: " (str-append (predates str-p) (kind-name (predates p0-p) k) "\n"))
        (thunk (predates thunk-p) _ _ (DeleteFile P "io-stat-test.txt" cleaned))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many got-cwd : (many (String) path) -> (many (IO P) next)
  (Stat P path cwd-kind))

(def-fns P $ many none-kind : (many (Result (EntryKind)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a k) (WriteOut P (str-append (predates str-p) (kind-name (predates p0-p) k) "\n") (thunk (predates thunk-p) _ _ (GetCwd P got-cwd))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many file-kind : (many (Result (EntryKind)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a k) (WriteOut P (str-append (predates str-p) (kind-name (predates p0-p) k) "\n") (thunk (predates thunk-p) _ _ (Stat P "io-stat-test-none" none-kind))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many read-back : (many (Result (String)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a s) (WriteOut P (str-append (predates str-p) s "\n") (thunk (predates thunk-p) _ _ (Stat P "io-stat-test.txt" file-kind))))
    ((Fail a m) (WriteErr P m (thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-fns P $ many appended : (many (Result (Unit)) o) -> (many (IO P) next)
  (ReadFile P "io-stat-test.txt" read-back))

(def-fns P $ many wrote : (many (Result (Unit)) o) -> (many (IO P) next)
  (AppendFile P "io-stat-test.txt" "two" appended))

(def-fns P $ many swept : (many (Result (Change)) o) -> (many (IO P) next)
  (WriteFile P "io-stat-test.txt" "one" wrote))

(DeleteFile P "io-stat-test.txt" swept)
