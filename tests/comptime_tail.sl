; expect: (Odd)
; The compile-time counterpart of extern_tail.sl: a tail recursive loop run at elaboration, of a depth
; that overflowed slc's stack before its interpreter reached a call in tail position by a tail call
; (ASSUMPTIONS 150). A regression there needs about 22MB of stack to pass this, against the usual 8MB.
; What decreases is an erased Nat, tied to a non-erased binary counter by the prelude's Numeral and
; stepped by numeral-succ; that is what keeps the 131071 iterations from building a unary Nat, so the
; test costs the same with the extern Nat as without it, where counting a Nat down instead wanted 80MB.
; The count is odd, so a loop that never ran would answer (Even), and the result is a Flip rather than
; the Nat, whose unary spelling the printer would walk.

(def-adts $ (Flip : -> Type)
  enum
  (many Even : -> (Flip))
  (many Odd : -> (Flip)))

; The predecessor of a binary counter, read backwards off the prelude's BinSucc: NoPred's index is BZ,
; so matching it is what tells the loop the counter has run out.
(def-adts $ (Pred : ((Bin) c) -> Type)
  enum
  (many NoPred : -> (Pred (BZ)))
  (many YesPred : (erased (Bin) c) (many (Bin) b) (erased (BinSucc b c) s) -> (Pred c)))

(def-lvl P)

(def-fns P $ (many bin-pred : (subterm many (Bin) c) -> (many (Pred c) r))
  (let-match many c (B1 c0) ((BZ) (NoPred)) ((B2 b) (YesPred _ (B1 b) (BS1 b))))
  (match many (notail $ bin-pred c0) (((Pred c) r))
    ((NoPred) (YesPred _ (BZ) (BSZ)))
    ((YesPred cc b0 s0) (YesPred _ (B2 b0) (BS2 b0 c0 s0)))))

(def-lvl X)

(def-fns X $ (many countdown : (subterm erased (Nat) n) (many (Bin) c) (erased (Numeral c n) v)
    (many (Flip) f) -> (many (Flip) r))
  (let-match many (bin-pred c) (YesPred cc b s) ((NoPred) f))
  (let ((erased m) (erased w)) (bin-to-nat b))
  (let ((erased e)) (numeral-succ b c m n s w v))
  (match erased e (((Flip) r2))
    ((Refl t x)
      (let ((erased p)) (prove-subterm m n))
      (let ((many g)) (match many f (((Flip) r3)) ((Even) (Odd)) ((Odd) (Even))))
      (tail (countdown (subterm p) m b w g)))))

(let ((many start)) (B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ B1 $ BZ))
(let ((erased n0) (erased v0)) (bin-to-nat start))

(countdown n0 start v0 (Even))
