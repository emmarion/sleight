; expect: (MkOut 4 (B2 $ B1 $ BZ) "bac")
; Extern matches and builds nested every way the extraction templates must handle (ASSUMPTIONS 133): a
; match in scrutinee position, an else standing for two constructors of a three-constructor type, a build
; whose argument is a build, and matches under matches on a String, all inside a thunk so the extracted
; program does the work.

(def-adts $ (Out : -> Type)
  enum
  (many MkOut : (many (Nat) n) (many (Bin) b) (many (String) s) -> (Out)))

(def-lvl X)
(def-fns X $ (many twice-pred : (many (Nat) n) -> (many (Nat) r))
  (match many (match many n (((Nat) m)) ((Zero) (Zero)) ((Succ k) k)) _
    ((Zero) (Zero))
    ((Succ k) k)))

(def-fns X $ (many bin-kind : (many (Bin) b) -> (many (Bin) r))
  (match many b _
    ((B1 rest) (B2 (B1 rest)))
    (else (B1 (B1 b)))))

(def-fns X $ (many bin-all : (many (Bin) b) -> (many (Nat) n))
  (match many b _ ((BZ) 0) ((B1 _) 1) ((B2 _) 2)))

(def-fns X $ (many str-swap : (many (String) s) -> (many (String) t))
  (match many s _
    ((SNil) (SCons #\x (SNil)))
    ((SCons c rest)
      (match many rest _
        ((SNil) (SCons c (SCons c (SNil))))
        ((SCons d rest2) (SCons d (SCons c rest2)))))))

(def-lvl Y)
(let ((erased xy)) (prove-predates X Y))
(def-fns Y $ (many run : -> (many (Out) o))
  (MkOut (nat-add (twice-pred (predates xy) 5) (bin-all (predates xy) (bin-kind (predates xy) (B2 (BZ)))))
         (bin-kind (predates xy) (B1 (BZ)))
         (str-swap (predates xy) "abc")))

run
; warns: tests/extern_nested.sl:27:14: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:959:1: note: `;! warn` for `SCons` is here
; warns: tests/extern_nested.sl:30:18: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:959:1: note: `;! warn` for `SCons` is here
; warns: tests/extern_nested.sl:30:27: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:959:1: note: `;! warn` for `SCons` is here
; warns: tests/extern_nested.sl:31:27: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:959:1: note: `;! warn` for `SCons` is here
; warns: tests/extern_nested.sl:31:36: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:959:1: note: `;! warn` for `SCons` is here
; warns: tests/extern_nested.sl:26:4: warning: lopsided `match`; flatten it with a `let-match` on `SCons`
; warns: tests/extern_nested.sl:36:31: warning: unnecessary `(predates _)`; drop it
; warns: tests/extern_nested.sl:36:81: warning: unnecessary `(predates _)`; drop it
; warns: tests/extern_nested.sl:36:57: warning: unnecessary `(predates _)`; drop it
; warns: tests/extern_nested.sl:37:20: warning: unnecessary `(predates _)`; drop it
; warns: tests/extern_nested.sl:38:20: warning: unnecessary `(predates _)`; drop it
