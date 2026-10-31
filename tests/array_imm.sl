; needs: ../std/immediate
; expect: (MkPair _ _ (MkU62 99 _) $ MkU62 97 _)
(def-fns _ $ (many char-u62 : (many (Char) c) -> (many (U62) u))
  (let-match erased c (MkChar b))
  (let-match erased b (MkU8 n p))
  (let ((erased q)) (lt-trans n u8-modulus u62-modulus p u8-below-u62))
  (coerce c (coercible-trans
              (coercible-trans (coercible-sym (coercible-wrap (Shared) MkChar b)) (coercible-sym (coercible-wrap (Shared) MkU8 n p)))
              (coercible-wrap (Shared) MkU62 n q))))

(def-fns _ $ (many imm-test : -> (many (Pair (U62) (U62)) result))
  (let ((unique a)) (list-to-array _ (Cons _ (MkCopy _ (char-u62 #\a)) $ Cons _ (MkCopy _ (char-u62 #\b)) $ Nil _)))
  (let ((unique old) (erased _) (unique b) (erased q))
    (array-swap-imm _ _ a (Zero) (MkCopy _ (char-u62 #\c)) _ (NthHere _ _ _) (imm-of _ (ImmCopy _ (ImmU62)) _) (imm-of _ (ImmCopy _ (ImmU62)) _)))
  (let-match erased q (SetHere _ _ _ _))
  (let ((erased _) (unique c) (erased r))
    (array-place-imm _ _ b (Succ (Zero)) old _ (NthThere _ _ _ _ _ (NthHere _ _ _)) (imm-of _ (ImmCopy _ (ImmU62)) _) (imm-of _ (ImmCopy _ (ImmU62)) _)))
  (let-match erased r (SetThere _ _ _ _ _ _ r1))
  (let-match erased r1 (SetHere _ _ _ _))
  (let ((many x) (unique d)) (array-get _ _ c (Zero) _ (NthHere _ _ _)))
  (let ((many y) (unique _)) (array-get _ _ d (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (MkPair _ _ x y))
imm-test
