; expect: 1
; A constructor renamed by a state-forwarding let (section 9) heads a match branch and a comptime-match
; pattern, and is found in the type's Matchable through its alias.

(let (many Z) Zero)
(let (many S) Succ)
(def-lvl X)
(def-fns X $ many pred : (many (Nat) n) -> (many (Nat) m)
  (match many n _
    ((Z) n)
    ((S k) k)))
(let (many two) (S (S (Z))))
(comptime-match many two (S one))
(pred (S one))
