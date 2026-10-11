(def-fns _ $ (many two : (many (Nat) a) -> (many (Nat) q) (erased (Eq (Nat) q q) p))
  (values a (Refl (Nat) a)))
(def-fns _ $ (many one : (many (Nat) a) -> (many (Nat) q)) a)
(let ((many len) (erased lp)) (two 5))
(let ((many m)) (match many (one 3) (((Nat) r)) ((Zero) 0) ((Succ k) k)))
(let ((many c)) (coerce m (coercible-refl (Shared) m)))
(dump-context)
; error: tests/dump_context_results.sl:7:1: error: `dump-context` stops elaboration here and reports what the checker knows
; error: __1 : (Nat)  [many, Const, value, anonymous, minted by the elaborator]
; error: __2 : (Coercible (Shared) (Nat) c (Shared) (Nat) c)  [erased, Const, proof, anonymous, minted by the elaborator]
; error: __3 : (Nat)  [many, Const, value, anonymous, bound at tests/dump_context_results.sl:5:38]
; error: __4 : (Nat)  [many, Const, value, anonymous, the elaborator's own binder for a head or an argument, minted by the elaborator]
; error: __6 : (Eq (Nat) len len)  [erased, Const, value, anonymous, bound at tests/dump_context_results.sl:4:31]
; error: __7 : (Nat)  [many, Const, value, anonymous, bound at tests/dump_context_results.sl:4:31]
