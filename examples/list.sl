; DESIGN.md sections 31 and 32: List, Nat, length.

(def-adts
  (List : (Type A) -> Type
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) tail) ->
       (List A))))

(def-adts $ Nat : -> Type
  enum
  (many Zero : -> (Nat))
  (many Succ : (many (Nat) pred) -> (Nat)))

(def-lvl L)

(def-fns L $ many length : (erased Type A) (subterm many (List A) xs) ->
    (many (Nat) n)
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (let (erased p) (prove-subterm tl xs))
      (Succ $ length A (subterm p) tl))))

(let (many xs) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(length (Nat) xs)
