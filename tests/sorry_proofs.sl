; A proof in an annotation is an operand: a call carrying a `(subterm p)` or `(predates p)` made by `sorry`, and
; a `coerce` whose proof is one, are tainted. `spin` would never return if it ran, and `high` calls a function
; of a level minted after its own.
(def-fns _ $ (many spin : (subterm many (Nat) n) -> (many (Nat) m))
  (let ((erased s)) (sorry (((Subterm (Nat) n (Nat) n) q))))
  (tail $ spin (subterm s) n))
(def-lvl Hi)
(def-lvl Lo)
(def-fns Lo $ (many low : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-fns Hi $ (many high : (many (Nat) n) -> (many (Nat) m))
  (let ((erased p)) (sorry (((Predates (Level) Lo Hi) q))))
  (low (predates p) n))
(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))
(let ((erased c)) (sorry (((Coercible (Shared) (Nat) 3 (Shared) (Meters) (MkMeters 4)) p))))
(low 1)
;! file "sorry/subterm.sl"
(spin 3)
;! file "sorry/predates.sl"
(high 1)
;! file "sorry/coerce.sl"
(coerce 3 c)
; expect: 2
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_proofs.sl:5:21: warning: this unit uses `sorry` 3 times, first here; nothing that depends on it runs
