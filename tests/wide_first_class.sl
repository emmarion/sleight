; needs: ../std/macro wide_lib
; expect: (Cons _ 12 $ Cons _ 1 $ Cons _ 12 $ Cons _ 1 $ Nil _)
; Constructors past OCaml's block tags reached first class: applied as a value, matched through a held
; Matchable that lists them abstractly, and allocated and invoked as an abstract constructor's cell.
(def-adts $ (Fc : -> Type)
  enum
  (wide ctors Fc Fc 247 2 (Nat)))

(def-fns _ $ (many pick : (erased (TyCtor -> Type) T)
    (wide params T Gc 247 2 (Nat))
    (many (wide matchable T Gc 247 2 (Nat)) m)
    (many (T) x) -> (many (Nat) n))
  (open-adt many m)
  (let ((unique u)) (cell-alloc Gc245))
  (let ((many y)) (share (u 4 5)))
  (let-match many x (Gc245 a b) (else 1))
  (match many y _ ((Gc245 c d) (nat-add (nat-add a b) $ nat-add c d))))

(def-fns _ $ (many pick-fc : (many (Fc) x) -> (many (Nat) n))
  (pick Fc (wide names Fc Fc 247 2 (Nat)) (matchable-of Fc) x))

(def-fns _ $ (many apply2 : (many (ValCtor (many (Nat) _) (many (Nat) _) -> (Fc)) k) -> (many (Fc) r))
  (k 1 2))

(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (Cons _ (pick-fc (Fc245 1 2)) $ Cons _ (pick-fc (Fc0 9))
    $ Cons _ (pick-fc (apply2 Fc245)) $ Cons _ (pick-fc (apply2 Fc1)) $ Nil _))

main
