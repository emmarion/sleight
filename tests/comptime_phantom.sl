; needs: list absurd
; error: F is phantom
; comptime-match may not assert a phantom constructor: the value is never headed by one, and its erased fields would be forged.

(def-adts $ (Opt : -> Type)
  enum
  (many T : (many (Nat) n) -> (Opt))
  (erased F : (erased (False) f) -> (Opt)))

(def-lvl W)
(def-fns W $ (many id : (many (Opt) m) -> (many (Opt) r)) m)
(let ((many x)) (id (T (Zero))))
(comptime-match many x (F f))
f
