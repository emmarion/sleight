; `dump-context` as a top-level statement: no goal, run position, Const values shown, a `unary` rule on a
; numeral, a unique Const already shared, and a shadowed binder.
(def-lvl L)
(let ((many xs)) (Cons (Nat) 1 $ Cons (Nat) 2 $ Nil (Nat)))
(let ((many n)) 5)
(unary 5 3)
(def-fns L $ (many inc : (many (Nat) k) -> (many (Nat) m))
  (Succ k))
(let ((unique u)) (Cons (Nat) 7 (Nil (Nat)))) 
(let ((many s)) (share u))
(let ((many xs)) (Nil (Nat)))
(dump-context)
; warns: tests/dump_context_top.sl:11:7: warning: declaration of `xs` shadows a previous binder
; warns: tests/dump_context_top.sl:4:7: note: shadowed binder is here
; error: tests/dump_context_top.sl:12:1: error: `dump-context` stops elaboration here and reports what the checker knows
; error: goal: none; `dump-context` stands as a statement here, so nothing is expected of it
; error: run position: a statement here runs at once and its binders are Const
; error: level: the top level, above every function's level
; error: s : (List (Nat))  [many, Const, value, bound at tests/dump_context_top.sl:10:7]
; error: is (Cons (Nat) 7 (Nil (Nat)))
; error: = (Cons _ 7 $ Nil _)
; error: u : (List (Nat))  [unique, Const, value, bound at tests/dump_context_top.sl:9:7]
; error: unique: shared at tests/dump_context_top.sl:10:24, so usable at many, written `(share u)`, and never again at unique
; error: inc : (Fn L (many (Nat) k) -> (many (Nat) m))  [many, Const, function, bound at tests/dump_context_top.sl:7:14]
; error: n : (Nat)  [many, Const, value, bound at tests/dump_context_top.sl:5:7]
; error: is (Succ (Succ 3))
; error: = 5
; error: xs : (List (Nat))  [many, Const, value, shadowed by a newer binder of the same name, bound at tests/dump_context_top.sl:4:7]
; error: L : (Level)  [erased, Const, level minted by `def-lvl`, bound at tests/dump_context_top.sl:3:10]
; error: slots, the entries at one slot: {5, n} {u, s}
; error: numerals with rules: 5 is (Succ (Succ 3))
