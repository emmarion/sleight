; expect: (Succ (Succ (Succ (Zero))))
; char-cmp compares two characters through their codes, which come back beside the comparison since
; section 5 keeps char-to-nat out of a result type. Less, equal and greater score 0, 1 and 2.

(def-lvl X)
(let (erased cx) (prove-predates char-lvl X))

(def-fns X $ many which : (many (Char) a) (many (Char) b) -> (many (Nat) r)
  (let (erased m) (erased n) (many c) (char-cmp (predates cx) a b))
  (match many c (((Nat) r))
    ((CLt x y p) (Zero))
    ((CEq x y e) (Succ (Zero)))
    ((CGt x y q) (Succ (Succ (Zero))))))

(nat-add (which #\a #\b) (nat-add (which #\b #\b) (which #\c #\b)))
