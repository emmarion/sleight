; needs: absurd
; expect: 1
; A type whose only constructor is phantom: an else standing for it alone is the match's only branch, counts as
; no real branch, is checked erased, and the match compiles to no code. The function is callable at erased only.

(def-adts $ Ghost : -> Type
  enum
  (erased G : -> (Ghost)))

(def-lvl X)

(def-fns X $ many spook : (many (Ghost) g) -> (many (Nat) n)
  (match many g (((Nat) r))
    (else (Zero))))

(let (erased ghost-nat) (spook (G)))

(Succ (Zero))
