; args: x y
; expect: file contents
; stderr: x
; stderr: y
; Writes a file, reads it back to stdout, then lists the arguments on stderr. A recursive helper over
; the argument list sits at a level below the IO level, since a continuation's type fixes its level and
; a same-level call would need a subterm proof; each request wraps the next step in a fresh continuation.

(def-lvl P0)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))
(let ((many d2)) (lt-dec 2 u8-modulus))
(comptime-match many d2 (Yes za2 zb2 zp2))
(let ((many code2)) (MkU8 2 zp2))
(let ((erased str-p0)) (prove-predates str-lvl P0))
(let ((erased p0-p)) (prove-predates P0 P))
(let ((erased thunk-p)) (prove-predates thunk-lvl P))
(let ((erased thunk-p0)) (prove-predates thunk-lvl P0))

(def-fns P0 $ (many list-args : (subterm many (List (String)) args) -> (unique (IO P) next))
  (match many args _
    ((Nil a) (Exit P code0))
    ((Cons a x rest) (WriteErr P (str-append (predates str-p0) x "\n") (unique-thunk (predates thunk-p0) _ _ (list-args (subterm _) rest))))))

(def-unique P $ (unique all-args : (many (List (String)) args) -> (unique (IO P) next))
  (list-args (predates p0-p) args))

(def-unique P $ (unique after-read : (many (Result (String)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a s) (WriteOut P s (unique-thunk (predates thunk-p) _ _ (GetArgs P all-args))))
    ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code1))))))

(def-unique P $ (unique after-write : (many (Result (Unit)) r) -> (unique (IO P) next))
  (match many r _
    ((Ok a u) (ReadFile P "io-test.txt" after-read))
    ((Fail a m) (WriteErr P m (unique-thunk (predates thunk-p) _ _ (Exit P code2))))))

(WriteFile P "io-test.txt" "file contents\n" after-write)
