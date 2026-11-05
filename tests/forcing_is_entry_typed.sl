(def-lvl L)
(def-adts $ (Wrap : (Type F) -> Type) enum
  (many MkW : -> (Wrap (Fn L -> (many 5 is y)))))
(def-fns _ $ (many f : (erased (Bool) j) (many (Wrap (Fn L -> (many j is y))) w) -> (many (Nat) n))
  (match many w _))
(Zero)

; expect: 0
; warns: tests/forcing_is_entry_typed.sl:5:3: warning: a non-erased `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function `absurd` instead
