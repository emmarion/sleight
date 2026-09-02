; args: x y
; expect: file contents
; stderr: x
; stderr: y
; Writes a file, reads it back to stdout, then lists the arguments on stderr. A recursive helper over
; the argument list sits at a level below the IO level, since a continuation's type fixes its level and
; a same-level call would need a subterm proof; it references the P-level echo only as a value.

(def-lvl P0)
(def-lvl P)
(let (erased u8-p) (prove-predates u8-lvl P))
(let (erased u8-p0) (prove-predates u8-lvl P0))
(let (erased str-p0) (prove-predates str-lvl P0))
(let (erased p0-p) (prove-predates P0 P))

(def-fns P0 $ many list-args : (subterm many (List (String)) args) -> (many (IO P) next)
  (match many args _
    ((Nil a) (Exit P (nat-to-u8 (predates u8-p0) 0)))
    ((Cons a x rest) (WriteErr P (str-append (predates str-p0) x "\n") (list-args (subterm _) rest)))))

(def-fns P $ many all-args : (many (List (String)) args) -> (many (IO P) next)
  (list-args (predates p0-p) args))

(def-fns P $ many after-read : (many (Result (String)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a s) (WriteOut P s (GetArgs P all-args)))
    ((Fail a m) (WriteErr P m (Exit P (nat-to-u8 (predates u8-p) 1))))))

(def-fns P $ many after-write : (many (Result (Unit)) r) -> (many (IO P) next)
  (match many r _
    ((Ok a u) (ReadFile P "io-test.txt" after-read))
    ((Fail a m) (WriteErr P m (Exit P (nat-to-u8 (predates u8-p) 2))))))

(WriteFile P "io-test.txt" "file contents\n" after-write)
