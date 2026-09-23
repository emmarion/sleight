; expect: 3
; notail asserts that a call is not in tail position on the post-erasure code, as tail asserts that it
; is: here the recursion sits under Succ, so it is a notail call, and each same-level call carries one
; mark or the other.

(def-fns _ $ (many count : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) (Zero))
    ((Cons _ _ rest) (Succ $ notail $ count rest))))

(def-fns _ $ (many count-onto : (subterm many (List (Nat)) xs) (many (Nat) acc) -> (many (Nat) n))
  (match many xs _
    ((Nil _) acc)
    ((Cons _ _ rest) (tail $ count-onto rest (Succ acc)))))

(let ((many xs)) (Cons (Nat) 1 $ Cons (Nat) 2 $ Nil (Nat)))
(nat-add (count xs) (count-onto (Cons (Nat) 0 $ Nil (Nat)) (Zero)))
