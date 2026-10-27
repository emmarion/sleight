; error: tests/native_compute_crash_bad.sl:7:56: error: `native-compute`: the compiled function exited with code 2
; host-path: yes
; externs: only
(def-adts $ (B : -> Type) enum (many T : -> (B)) (many F : -> (B)))
(def-fns _ $ (many fine : -> (many (B) r)) (T))
(def-fns _ $ (many huge : -> (many (B) r)) (let ((erased _) (unique _) (erased _)) (array-new (Nat) 1152921504606846976)) (T))
(let ((many a) (many b) (many c)) (native-compute fine huge fine))
