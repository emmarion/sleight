; `dump-context` shows a stored value by the facts in force where it stands: `v`, of an opaque type at run
; position, is shown as the `Nat` a branch-forced fact makes it.
(def-fns _ $ (many conv : (erased Type A) (many A a) -> (erased Type T) (many T v) (erased (Eq Type T A) p))
  (values A a (Refl _ _)))
(let ((erased _T) (many v) (erased p)) (conv (Nat) 5))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let-match erased p (Refl _ _))
  (dump-context v)
  n)
; error: tests/dump_context_forced_bad.sl:8:3: error: `dump-context` stops elaboration here and reports what the checker knows
; error:       = 5
