; error: of `g` does not satisfy `at` `(slot-of #\c)`
(def-fns _ $ (many g : (many (Char) a) (many (Nat) b at a) -> (many (Nat) r)) b)
(g #\c 99)
