; A final value is printed, and taken for a function to apply or not, by the facts in force where it stands;
; a fact forced later from a tainted operand changes nothing of it, in an extracted program either.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many conv : (erased Type A) (many A a) -> (erased Type T) (many T v))
  (values A a))
(let ((erased T) (many v)) (conv (Nat) 5))
v
;! file "sorry/final-fact.sl"
(let ((erased e)) (sorry (((Eq Type T (Fn (level-of inc) -> (many (Nat) y))) q))))
(let-match erased e (Refl _ _))
; expect: _
; warns: sorry/final-fact.sl:1:19: warning: this unit uses `sorry` once, here; nothing that depends on it runs
