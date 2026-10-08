; `dump-context` after a run-position `def-fns`: its erased function and the `Delegate` proof it binds are Const.
(def-fns _ $ (erased refl-nat : (erased (Nat) n) -> (erased (Eq (Nat) n n) e))
  (Refl _ _))
(def-fns _ $ (many plus at nat-add : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (delegate (nat-add a b)))
(dump-context)
; error: tests/dump_context_erased_fns.sl:6:1: error: `dump-context` stops elaboration here and reports what the checker knows
; error: (delegate-of plus) : (Delegate (Shared) (Fn (level-of plus) (many (Nat) a) (many (Nat) b) -> (many (Nat) c)) plus (Shared) (Fn nat-lvl (many (Nat) a) (many (Nat) b) -> (many (Nat) c)) nat-add)  [erased, Const, proof, anonymous, minted by the elaborator]
; error: refl-nat : (Fn (level-of refl-nat) (erased (Nat) n) -> (erased (Eq (Nat) n n) e))  [erased, Const, function, bound at tests/dump_context_erased_fns.sl:2:14]
