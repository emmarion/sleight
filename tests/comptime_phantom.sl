; needs: list absurd
; error: F is phantom
; comptime-match may not assert a phantom constructor: the value is never headed by one, and its erased fields would be forged.

(def-adts $ (Maybe : -> Type)
  enum
  (many T : (many (Nat) n) -> (Maybe))
  (erased F : (erased (False) f) -> (Maybe)))

(def-lvl W)
(def-fns W $ (many id : (many (Maybe) m) -> (many (Maybe) r)) m)
(let ((many x)) (id (T (Zero))))
(comptime-match many x (F f))
f
