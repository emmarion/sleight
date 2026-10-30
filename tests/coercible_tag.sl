; externs: only
; expect: (MkPair _ _ (Cons _ 0 $ Cons _ 17 $ Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Nil _) $ MkPair _ _ (MkU62 0 _) $ MkU62 1 _)
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (many Mix : (many (Nat) n) -> (Shade))
  (erased Ghost : -> (Shade))
  (many Green : -> (Shade))
  (many Blue : (erased (Nat) k) -> (Shade)))

(def-adts $ (Side : ((Nat) n) -> Type)
  enum
  (many Lo : -> (Side (Zero)))
  (many Hi : (erased (Nat) k) -> (Side (Succ k))))

(def-fns _ $ (many code : (many (Shade) c) -> (many (Nat) n))
  (match many c _
    ((Red) (coerce c (coercible-tag (Shared) Red)))
    ((Mix n) (nat-add 10 n))
    ((Ghost) (Zero))
    ((Green) (coerce c (coercible-tag (Shared) Green)))
    ((Blue k) (coerce c (coercible-tag (Shared) Blue k)))))

(let ((erased (Coercible (Shared) (Shade) (Green) (Shared) (Nat) 1) _)) (coercible-tag _ Green))
(let ((erased (Coercible (Unique) (Side (Succ 4)) (Hi 4) (Unique) (Nat) 1) _)) (coercible-tag _ Hi 4))

(let ((erased lt0)) (lt-trans 0 u8-modulus u62-modulus (prove-literal-lt 0 u8-modulus) u8-below-u62))
(let ((erased lt1)) (lt-trans 1 u8-modulus u62-modulus (prove-literal-lt 1 u8-modulus) u8-below-u62))

(def-fns _ $ (many bool-u62 : (many (Bool) b) -> (many (U62) u))
  (match many b _
    ((BTrue) (coerce b (coercible-trans (coercible-tag (Shared) BTrue) (coercible-wrap (Shared) MkU62 0 lt0))))
    ((BFalse) (coerce b (coercible-trans (coercible-tag (Shared) BFalse) (coercible-wrap (Shared) MkU62 1 lt1))))))

(let ((many settled)) (coerce 2 (coercible-sym (coercible-tag (Shared) Blue 7))))

(def-fns _ $ (many main : -> (many (Pair (List (Nat)) (Pair (U62) (U62))) r))
  (let ((many back)) (coerce 2 (coercible-sym (coercible-tag (Shared) Blue 7))))
  (MkPair _ _ (Cons _ (code (Red)) $ Cons _ (code (Mix 7)) $ Cons _ (code (Green)) $ Cons _ (code back) $ Cons _ (code settled) $ Nil _)
    (MkPair _ _ (bool-u62 (BTrue)) (bool-u62 (BFalse)))))

main
