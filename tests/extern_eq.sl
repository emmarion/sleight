; expect: (Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Cons _ 1 $ Cons _ 0 $ Nil _)
; Decided equality with an apartness witness: nat-eq and str-eq are extern, u62-eq is nat-eq under bounds, and
; char-eq is u62-eq on the codes by a delegate. Each runs once at elaboration and once inside a function, where
; the implementation runs.

(def-fns _ $ (many flag : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
    (many (EqDec T R a b) e) -> (many (Nat) r))
  (match many e _ ((Equal _ _ _) 1) ((Unequal _ _ _ _ _) 0)))

(let ((erased p43)) (lt-trans _ _ _ (prove-literal-lt 43 u8-modulus) u8-below-u62))
(let ((erased p7)) (lt-trans _ _ _ (prove-literal-lt 7 u8-modulus) u8-below-u62))

(let ((many e1)) (flag _ _ _ _ $ nat-eq 43 43))
(let ((many e2)) (flag _ _ _ _ $ nat-eq 300 301))

(def-lvl A)
(def-fns A $ (many eqs : -> (many (List (Nat)) out))
  (let ((many n1)) (flag _ _ _ _ $ nat-eq 300 300))
  (let ((many n2)) (flag _ _ _ _ $ nat-eq 43 7))
  (let ((many u1)) (flag _ _ _ _ $ u62-eq 43 43 p43 p43))
  (let ((many u2)) (flag _ _ _ _ $ u62-eq 43 7 p43 p7))
  (let ((many c1)) (flag _ _ _ _ $ char-eq #\a #\a))
  (let ((many c2)) (flag _ _ _ _ $ char-eq #\a #\b))
  (let ((many s1)) (flag _ _ _ _ $ str-eq "abc" "abd"))
  (let ((many s2)) (flag _ _ _ _ $ str-eq "abc" "abc"))
  (let ((many s3)) (flag _ _ _ _ $ str-eq "ab" "abc"))
  (let ((many s4)) (flag _ _ _ _ $ str-eq "" ""))
  (let ((many s5)) (flag _ _ _ _ $ str-eq "abc" "ab"))
  (Cons _ e1 $ Cons _ e2 $ Cons _ n1 $ Cons _ n2 $ Cons _ u1 $ Cons _ u2 $ Cons _ c1 $ Cons _ c2 $ Cons _ s1 $ Cons _ s2 $ Cons _ s3 $ Cons _ s4 $ Cons _ s5 $ Nil _))

eqs
