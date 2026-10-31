; externs: only
; expect: (MkPair _ _ (MkU62 0 _) $ MkPair _ _ (MkU62 1 _) $ MkPair _ _ (MkTok _) 1)
(def-adts $ (Tok : -> Type) enum
  (many MkTok : (erased (Nat) n) -> (Tok)))

(def-adts $ (Mark : -> Type) union
  (many MA : -> (Mark))
  (many MB : (erased (Nat) n) -> (Mark)))

(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Mix : (many (Nat) n) -> (Shade))
  (many Green : -> (Shade)))

(let ((erased lt0)) (lt-trans 0 u8-modulus u62-modulus (prove-literal-lt 0 u8-modulus) u8-below-u62))
(let ((erased lt1)) (lt-trans 1 u8-modulus u62-modulus (prove-literal-lt 1 u8-modulus) u8-below-u62))

(def-fns _ $ (many at bool-u62 : (many (Bool) b) -> (many (U62) u at b))
  (match many b (at (((U62) u at b)))
    ((BTrue) (slot-tag b) (MkU62 0 lt0))
    ((BFalse) (slot-tag b) (MkU62 1 lt1))))

(def-fns _ $ (many at mark-tok : (many (Mark) m) -> (many (Tok) t at m))
  (slot-tag m)
  (MkTok 0))

(def-fns _ $ (many at green-one : (unique (Cell Green) u) -> (many (Nat) n at u))
  (slot-tag u)
  1)

(def-fns _ $ (many main : -> (many (Pair (U62) (Pair (U62) (Pair (Tok) (Nat)))) r))
  (let ((unique g)) (cell-alloc Green))
  (MkPair _ _ (bool-u62 (BTrue)) $ MkPair _ _ (bool-u62 (BFalse)) $ MkPair _ _ (mark-tok (MB 3)) (green-one g)))

main
