; expect: 7
; Functions at different levels in one list built inside a function body: each Pack carries its level erased
; with a proof that the level predates K0, fixed when Packed was declared, and a consumer above K0 composes
; that proof with its own by predates-trans.

(def-lvl L1)
(def-fns L1 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl L2)
(def-fns L2 $ (many dbl : (many (Nat) n) -> (many (Nat) m)) (nat-add (predates (prove-predates nat-lvl L2)) n n))

(def-lvl K0)
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (erased (Level) l) (erased (Predates (Level) l K0) p) (many (Fn l (many (Nat) x) -> (many (Nat) y)) f) -> (Packed)))
(let ((erased p1)) (prove-predates L1 K0))
(let ((erased p2)) (prove-predates L2 K0))

(def-lvl K)
(let ((erased k0k)) (prove-predates K0 K))
(def-fns K $ (many run-all : (subterm many (List (Packed)) ps) (many (Nat) x) -> (many (Nat) y))
  (match many ps _
    ((Nil a) x)
    ((Cons a p rest)
      (match many p _
        ((Pack l q f) (f (predates (predates-trans q k0k)) (notail $ run-all (subterm (prove-subterm rest ps)) rest x)))))))

(def-lvl Z)
(let ((erased kz)) (prove-predates K Z))
(def-fns Z $ (many main : -> (many (Nat) r))
  (run-all (predates kz) (Cons (Packed) (Pack L1 p1 inc) (Cons (Packed) (Pack L2 p2 dbl) (Nil (Packed)))) 3))
main
