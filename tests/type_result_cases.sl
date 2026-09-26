; expect: 1
; A call returning a type it cannot name in an is entry returns instead a runtime witness that the type is
; one of a few, beside a value of it: a closed existential. The type is erased and the witness is not, so
; matching the witness forces the type equal to that branch's and the value can be read there; two real
; branches need the runtime tag, which is why the witness is many.

(def-adts $ (Shape : (Type T) -> Type)
  enum
  (many IsNat : -> (Shape (Nat)))
  (many IsList : -> (Shape (List (Nat)))))

(def-lvl T)
(def-fns T $ (many pick : (many (Nat) n) -> (erased Type B) (many (Shape B) s) (many B v))
  (match many n _
    ((Zero) (values (Nat) (IsNat) n))
    ((Succ k) (values (List (Nat)) (IsList) (Cons (Nat) n (Nil (Nat)))))))

(def-lvl U)
(def-fns U $ (many count : (erased Type B) (many (Shape B) s) (many B v) -> (many (Nat) r))
  (let-match many s (IsList) ((IsNat) v))
  (match many v _
    ((Nil a) (Zero))
    ((Cons a hd tl) (Succ (Zero)))))

(let ((erased B) (many s) (many v)) (pick (Succ (Zero))))
(count B s v)
