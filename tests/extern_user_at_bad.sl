; error: only the prelude may mark a definition `extern`
(def-fns _ $ (many extern at keep : (many (Nat) x) -> (many (Nat) r at x)) x)
