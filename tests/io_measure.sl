; expect: 5050

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes za zb zp))

(def-fns _ $ (many sum-to : (subterm many (Nat) n) -> (many (Nat) s))
  (let-match many n (Succ m) ((Zero) 0))
  (nat-add n (notail $ sum-to m)))

(def-lvl P)

(def-unique P $ (unique report : (many (Nat) s) (many (Usage) u) -> (unique (IO P) next))
  (WriteOut P (str-append (nat-str s) "\n") (unique-thunk _ _ (Exit P (MkU8 0 zp)))))

(def-unique _ $ (unique work : -> (many (Nat) s))
  (sum-to 100))

(Measure P _ _ work report)
