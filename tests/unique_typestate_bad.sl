; needs: unique_typestate
; error: expected `(Conn (Opened))`, got `(Conn (Closed))`
; The protocol's order is what the index enforces: skipping do-open leaves a (Closed) handle where
; do-send declares an (Opened) one. unique_double_bad.sl is the other half, a handle used twice.

(def-fns _ $ (many skip-open : -> (many (Nat) n))
  (let ((unique (Conn (Closed)) c)) (MkConn (Closed) 0))
  (let ((unique c2)) (do-send c 1))
  (do-close c2))
skip-open
