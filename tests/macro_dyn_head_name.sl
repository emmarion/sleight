; needs: ../std/macro macro_lib
; error: `em` is a macro, expanded only where its head is constant-known
(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let ((many em)) (MkMacro _ swap-fn))
  (em nat-add a b))
