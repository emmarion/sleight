; `dump-context` as a statement inside an erased function's body: nothing is expected of it, and the position is
; erased throughout, so a unique parameter is neither consumed nor counted.
(def-fns _ $ (erased ghost : (unique (List (Nat)) xs) (erased (Nat) n) -> (erased (Nat) r))
  (let ((many ys)) (share xs))
  (dump-context)
  n)
; error: tests/dump_context_stmt.sl:5:3: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: none; `dump-context` stands as a statement here, so nothing is expected of it
; error: erased context: nothing here counts as a use, so no unique binder is consumed or shared by this code
; error: ys : (List (Nat))  [many, Dyn, value, bound at tests/dump_context_stmt.sl:4:9]
; error: is xs
; error: xs : (List (Nat))  [unique, Dyn, value, bound at tests/dump_context_stmt.sl:3:30]
; error: unique: live, neither consumed nor shared on this path
; error: ghost : (Fn (level-of ghost) (unique (List (Nat)) xs) (erased (Nat) n) -> (erased (Nat) r))  [erased, Dyn, function, bound at tests/dump_context_stmt.sl:3:14]
; error: at-database, the entries at one location: {xs, ys}
