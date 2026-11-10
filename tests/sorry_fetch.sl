; A fetch form that yields a tainted entry is tainted, in a type as in an expression: `at-fn-of` and
; `delegate-of` find the anonymous proof a `sorry` left in scope, and what opens or coerces by it does not run.
(def-lvl L)
(def-fns L $ (many keep : (many (Nat) n) -> (many (Nat) m at n))
  n)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns L $ (many show : (many (Nat) n) -> (many (String) s))
  (nat-str n))
(let ((erased _p)) (sorry (((AtFn (Fn L (many (Nat) n) -> (many (Nat) m at n)) keep) q))))
(let ((erased _d)) (sorry (((Delegate (Shared) (Fn L (many (Nat) n) -> (many (Nat) m)) inc (Shared) (Fn L (many (Nat) n) -> (many (String) s)) show) q))))
(def-fns _ $ (many skipped : (many (Nat) n) -> (many (Nat) m))
  (open-at-fn (at-fn-of keep))
  (let ((many r)) (keep n))
  (Succ r))
(def-fns _ $ (many in-type : (many (Nat) n) -> (many (Nat) m))
  (let ((erased e)) (Refl _ (at-fn-of keep)))
  (let-match erased e (Refl _ pr))
  (open-at-fn pr)
  (let ((many r)) (keep n))
  (Succ r))
(def-fns _ $ (many confused : (many (Nat) n) -> (many (String) s))
  (let ((many f)) (coerce inc (coercible-of (delegate-of inc))))
  (f n))
(inc 1)
;! file "sorry/skipped.sl"
(skipped 4)
;! file "sorry/in-type.sl"
(in-type 4)
;! file "sorry/confused.sl"
(confused 4)
; expect: 2
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_fetch.sl:10:20: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
