; needs: list
; error: needs a (predates p) annotation

(def-lvl L0)
(def-fns L0 $ many f : (many (Nat) n) -> (many (Nat) m) n)
(def-lvl L1)
(def-fns L1 $ many g : (many (Nat) n) -> (many (Nat) m) (f n))
