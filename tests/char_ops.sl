; expect: (Succ (Succ (Succ (Zero))))
; A Char is its code at runtime, so char-cmp delegates to nat-cmp (section 38): its arguments coerce
; down through both newtypes, and the Coercible carrying the result back up is built by an erased match
; that leaves no code, so the delegate mark still stands. coercible-of then fetches the proof that the
; two are one function, and the coerced char-cmp runs on Nats. Less, equal and greater score 0, 1 and 2.

(let (erased cg) (coercible-of char-cmp))
(let (many (Fn nat-lvl (subterm many (Nat) m) (many (Nat) n) -> (many (Cmp (Nat) Lt m n) c)) g)
  (coerce char-cmp cg))

(def-lvl X)
(let (erased cx) (prove-predates char-lvl X))
(let (erased nx) (prove-predates nat-lvl X))

(def-fns X $ many which : (many (Char) a) (many (Char) b) -> (many (Nat) r)
  (match many (char-cmp (predates cx) a b) (((Nat) r))
    ((CLt t rr x y p) (Zero))
    ((CEq t rr x) (Succ (Zero)))
    ((CGt t rr x y q) (Succ (Succ (Zero))))))

(def-fns X $ many which-nat : (many (Nat) a) (many (Nat) b) -> (many (Nat) r)
  (match many (g (predates nx) a b) (((Nat) r))
    ((CLt t rr x y p) (Zero))
    ((CEq t rr x) (Succ (Zero)))
    ((CGt t rr x y q) (Succ (Succ (Zero))))))

(nat-add (which #\a #\b) (nat-add (which-nat 2 2) (which-nat 3 2)))
