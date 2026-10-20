; expect: 0
(def-adts $ (N : -> Type) enum
  (many Z : -> (N))
  (many S : (many (N) p) -> (N)))
(def-fns _ $ (many sf : (unique (N) x) (many (Slot) _t at x) (erased (Eq (Slot) (slot-of x) _t) _e) ->
    (unique (N) r at x)) x)
(def-fns _ $ (many k : (many (N) _w) (unique _w is y) -> (unique (N) r at y))
  (let ((many t)) (slot-of y))
  (sf y t (Refl _ t)))
(def-fns _ $ (many km : (many (N) _w) (unique (N) y) (erased (Eq (N) _w y) q) -> (unique (N) r at y))
  (match erased q _ ((Refl _ _) (sf y (slot-of y) (Refl _ (slot-of y))))))
(def-fns _ $ (many kl : (many (N) _w) (unique (N) y) (erased (Eq (N) _w y) q) -> (unique (N) r at y))
  (let-match erased q (Refl _ _))
  (sf y (slot-of y) (Refl _ (slot-of y))))
0
