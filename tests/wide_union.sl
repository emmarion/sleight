; needs: ../std/macro wide_lib
; expect: (MkPair _ _ (Cons _ 5 $ Cons _ 6 $ Nil _) _)
; Unions with more constructors than OCaml's block tags carry no tag, so none needs one: a union newtype
; is its field, and a plain union is a block of its constructor's fields.
(def-adts $ (Un : -> Type)
  union newtype
  (wide ctors Un Un 247 1 (Nat)))

(def-adts $ (Uu : -> Type)
  union
  (wide ctors Uu Uu 247 3 (Nat)))

(def-fns _ $ (many main : -> (many (Pair (List (Nat)) (Uu)) r))
  (let ((many n)) 5)
  (let ((many u)) (Un246 n))
  (let ((many back)) (coerce u (coercible-sym (coercible-wrap (Shared) Un246 n))))
  (let ((many v)) (Uu245 4 6 7))
  (let-match many v (Uu245 _ m _))
  (MkPair _ _ (Cons _ back $ Cons _ m $ Nil _) v))

main
