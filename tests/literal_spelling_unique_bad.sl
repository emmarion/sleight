; error: #\x61, a literal and so many, used at unique
(def-fns _ ((many f : (unique (Char) x) -> (many (Char) y)) (share x)))
(f #\x61)
