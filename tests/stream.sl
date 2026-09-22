; expect: (Cons _ 0 $ Cons _ 1 $ Cons _ 2 $ Nil _)
; A stream with no coinductive type: its tail is a function at level K, minted after the producer's level P,
; so the thunk's body calls nats-from under Predates P K and is checked like any other body. take unfolds
; three elements under a subterm decrease on its count.

(def-lvl P)
(def-lvl K)
(def-adts $ (Stream : -> Type)
  enum
  (many MkS : (many (Nat) head) (many (Fn K -> (many (Stream) rest)) next) -> (Stream)))
(let ((erased pk)) (prove-predates P K))
(def-fns P $ (many nats-from : (many (Nat) n) -> (many (Stream) s))
  (def-fns K $ (many next : -> (many (Stream) s)) (nats-from (predates pk) (Succ n)))
  (MkS n next))
(def-lvl T)
(let ((erased kt)) (prove-predates K T))
(def-fns T $ (many take : (subterm many (Nat) n) (many (Stream) s) -> (many (List (Nat)) out))
  (match many n _
    ((Zero) (Nil (Nat)))
    ((Succ n1)
      (match many s _
        ((MkS h rest) (Cons (Nat) h (take (subterm (prove-subterm n1 n)) n1 (rest (predates kt)))))))))
(take 3 (nats-from (Zero)))
