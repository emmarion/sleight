; error: `at` cannot name `s`, an entry of a constructor's telescope still being written
; A field's function type written `at` its sibling field: `coerce` moves the index across two
; `is`-equal values at different slots, and the call then reads the word of the wrong one.
(def-adts $ (N : -> Type) enum
  (many Z : -> (N))
  (many S : (many (N) p) -> (N)))
(def-adts $ (W : (Type F) -> Type) enum
  (many MkS : (unique (N) s) -> (W (Fn nat-lvl (many (N) j at s) ->))))
(def-fns _ $ (many h : (many (N) a) (many (N) b at a) -> (many b is r)) b)
(def-fns _ $ (many go : -> (many (N) r))
  (let ((erased p)) (coercible-ctor (Unique) MkS (coercible-refl (Unique) (S (Z)))))
  (let-match unique (coerce (MkS (S (Z))) p) (MkS s1))
  (let-match unique (coerce (MkS (S (Z))) p) (MkS s2))
  (let-match unique s1 (S q u))
  (let-match many (h (share s2) (share (u (share s2)))) (S x))
  (let-match many x (S y))
  y)
(go)
