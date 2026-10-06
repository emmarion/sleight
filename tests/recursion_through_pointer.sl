; expect: 3
; Self-recursion through a pointer: g receives itself inside Packed, a type with a negative occurrence,
; and calls the pointer at its own level under a subterm decrease, which is what bounds the call.

(def-lvl L)
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (many (Fn L (many (Packed) q) (subterm many (List (Nat)) xs) -> (many (Nat) n)) f) -> (Packed)))

(def-fns L $ (many g : (many (Packed) q) (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (let-match many q (Pack f))
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (notail $ f q (subterm (prove-subterm tl xs)) tl)))))

(g (Pack g) (Cons (Nat) 0 (Cons (Nat) 0 (Cons (Nat) 0 (Nil (Nat))))))
; warns: tests/recursion_through_pointer.sl:14:41: warning: unnecessary `(subterm _)`; drop it
