(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P))
  (many MkQ : -> (P))
  (many MkR : (many (Nat) d) -> (P)))
(def-fns _ $ (many f : (many (P) p) -> (many (Nat) q))
  (match many p _
    ((MkP a b c) a)))
; error: tests/msg_missing_branches_bad.sl:7:3: error: this `match` is missing a branch for the following unrefuted constructors:
; error: tests/msg_missing_branches_bad.sl:4:3: note: value constructor `MkQ`, which is declared here
; error: tests/msg_missing_branches_bad.sl:5:3: note: value constructor `MkR`, which is declared here
