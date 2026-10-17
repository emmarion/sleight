; expect: 3
; A Char is its code at runtime, so char-cmp delegates to u62-cmp (section 33): its arguments coerce
; down through both newtypes, and the Coercible carrying the result back up is built by an erased match
; that leaves no code, so the delegate mark still stands. delegate-of then fetches the proof that the
; two are one function, coercible-of reads the Coercible off it, and the coerced char-cmp runs on
; Nats below u62-modulus. Less, equal and greater score 0, 1 and 2.

(let ((erased cg)) (coercible-of (delegate-of char-cmp)))
(let ((many g)) (coerce char-cmp cg))

(def-lvl X)
(let ((erased cx)) (prove-predates char-lvl X))

(def-fns X $ (many which : (many (Char) a) (many (Char) b) -> (many (Nat) r))
  (match many (char-cmp (predates cx) a b) (((Nat) r))
    ((CLt _ _ _ _ _) (Zero))
    ((CEq _ _ _) (Succ (Zero)))
    ((CGt _ _ _ _ _) (Succ (Succ (Zero))))))

(let ((erased one-lt))
  (pow2-lt (Zero) sixty-two (Succ (Zero)) u62-modulus
    (lt-trans (Zero) eight sixty-two (LtZ _) (eight-lt-sixty-two)) (P0) u62-modulus-pow2))

(def-fns X $ (many which-nat : (many (Nat) a) (many (Nat) b)
    (erased (Lt a u62-modulus) pa) (erased (Lt b u62-modulus) pb) -> (many (Nat) r))
  (match many (g a b pa pb) (((Nat) r))
    ((CLt _ _ _ _ _) (Zero))
    ((CEq _ _ _) (Succ (Zero)))
    ((CGt _ _ _ _ _) (Succ (Succ (Zero))))))

(nat-add (which #\a #\b)
  (nat-add (which-nat (Zero) (Zero) u62-modulus-pos u62-modulus-pos) (which-nat (Succ (Zero)) (Zero) one-lt u62-modulus-pos)))
; warns: tests/char_ops.sl:15:25: warning: unnecessary `(predates _)`; drop it
