; needs: list
; expect: (SSucc (SZero))
; A field projected by comptime-match serves as a type index afterwards. The stored value is
; never consulted by canonicalization (section 18), so zero needs its own comptime-match.

(def-adts
  (Sing : ((Nat) n) -> Type
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-fns _ $ many id : (many (Nat) n) -> (many (Nat) m) n)
(let (many one) (id (Succ (Zero))))
(comptime-match many one (Succ zero))
(comptime-match many zero (Zero))
(let (many (Sing one) s) (SSucc zero (SZero)))
s
