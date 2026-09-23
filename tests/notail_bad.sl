; error: a `notail`-marked call is in tail position
; A notail mark on a call that is in tail position is a hard error, so the mark cannot go stale when an
; edit moves the call.

(def-fns _ $ (many count-onto : (subterm many (List (Nat)) xs) (many (Nat) acc) -> (many (Nat) n))
  (match many xs _
    ((Nil _) acc)
    ((Cons _ _ rest) (notail $ count-onto rest (Succ acc)))))
(Zero)
