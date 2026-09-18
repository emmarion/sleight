; needs: palindrome_relations palindrome_bridge
; expect: (Cons 0 (Cons 1 (Cons 1 (Cons 5 (Cons 4 (Cons 1 (Cons 5 (Cons 7 (Cons 4 (Cons 5 (Cons 6 (Cons 11 (Nil)))))))))))))
; Manacher's algorithm over a List (Nat), with lists alone (two zippers and a
; suffix of the radius list stand in for the arrays), returning the spec's
; LongestPalindrome proof of palindrome_relations.sl. Written by a Claude
; session; the checker, not this comment, is the evidence that it is right.

; --- list relations ---

(def-adts
  (Nth : (Type A) ((Nat) i) ((List A) xs) (A x) -> Type
    enum
    (many NthHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Nth A (Zero) (Cons _ x rest) x))
    (many NthThere : (erased Type A) (erased (Nat) i) (erased A y) (erased (List A) rest) (erased A x)
        (erased (Nth A i rest x) p) -> (Nth A (Succ i) (Cons _ y rest) x)))
  (Drop : (Type A) ((Nat) k) ((List A) xs) ((List A) ys) -> Type
    enum
    (many DropZ : (erased Type A) (erased (List A) xs) -> (Drop A (Zero) xs xs))
    (many DropS : (erased Type A) (erased (Nat) k) (erased A x) (erased (List A) xs) (erased (List A) ys)
        (erased (Drop A k xs ys) p) -> (Drop A (Succ k) (Cons _ x xs) ys)))
  (RevOnto : (Type A) ((Nat) k) ((List A) xs) ((List A) acc) ((List A) res) -> Type
    enum
    (many RevZ : (erased Type A) (erased (List A) xs) (erased (List A) acc) -> (RevOnto A (Zero) xs acc acc))
    (many RevS : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) acc) (erased (List A) res)
        (erased A x) (erased (RevOnto A k xs acc res) p) (erased (Nth A k xs x) n) ->
       (RevOnto A (Succ k) xs acc (Cons _ x res))))
  (Zip : (Type A) ((List A) xs) ((List A) l) ((List A) r) -> Type
    enum
    (many ZipZ : (erased Type A) (erased (List A) xs) -> (Zip A xs (Nil A) xs))
    (many ZipS : (erased Type A) (erased (List A) xs) (erased (List A) l) (erased A x) (erased (List A) r)
        (erased (Zip A xs l (Cons _ x r)) p) -> (Zip A xs (Cons _ x l) r))))

; --- the two arms of a centre agree on their first k elements, or not ---

(def-adts
  (Agree : ((Nat) k) ((List (Nat)) xs) ((List (Nat)) ys) -> Type
    enum
    (many AgreeZ : (erased (List (Nat)) xs) (erased (List (Nat)) ys) -> (Agree (Zero) xs ys))
    (many AgreeS : (erased (Nat) k) (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Agree k xs ys) p) -> (Agree (Succ k) (Cons _ x xs) (Cons _ x ys))))
  (Disagree : ((Nat) k) ((List (Nat)) xs) ((List (Nat)) ys) -> Type
    enum
    (many DisNilL : (erased (Nat) k) (erased (List (Nat)) ys) -> (Disagree (Succ k) (Nil (Nat)) ys))
    (many DisNilR : (erased (Nat) k) (erased (List (Nat)) xs) -> (Disagree (Succ k) xs (Nil (Nat))))
    (many DisHead : (erased (Nat) k) (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (NatApart x y) d) -> (Disagree (Succ k) (Cons _ x xs) (Cons _ y ys)))
    (many DisTail : (erased (Nat) k) (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Disagree k xs ys) p) -> (Disagree (Succ k) (Cons _ x xs) (Cons _ x ys)))))

; --- the middle of a centre: nothing, or one element ---

(def-adts
  (Mid : ((Nat) m) ((List (Nat)) mid) -> Type
    enum
    (many MidEven : -> (Mid (Zero) (Nil (Nat))))
    (many MidOdd : (erased (Nat) z) -> (Mid (Succ (Zero)) (Cons _ z (Nil (Nat)))))))

; --- the window of radius k around a centre, onion style, deepest pair outermost ---

(def-adts
  (Win : ((Nat) k) ((List (Nat)) l) ((List (Nat)) mid) ((List (Nat)) r) ((List (Nat)) w) -> Type
    enum
    (many WinZ : (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) -> (Win (Zero) l mid r mid))
    (many WinS : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r)
        (erased (List (Nat)) w) (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) wy)
        (erased (Win k l mid r w) p) (erased (Nth (Nat) k l x) nx) (erased (Nth (Nat) k r y) ny)
        (erased (Concat (Nat) w (Cons _ y (Nil (Nat))) wy) q) ->
       (Win (Succ k) l mid r (Cons _ x wy)))))

; --- small lemmas ---

(def-fns _ $ erased agree-weaken : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree (Succ k) xs ys) p) -> (erased (Agree k xs ys) q)
  (match erased p _
    ((AgreeS k0 x xs0 ys0 p0)
      (match erased p0 _
        ((AgreeZ a b) (AgreeZ xs ys))
        ((AgreeS k1 x1 xs1 ys1 p1) (AgreeS _ x _ _ (agree-weaken _ _ _ p0)))))))

(def-fns _ $ erased agree-sym : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) -> (erased (Agree k ys xs) q)
  (match erased p _
    ((AgreeZ a b) (AgreeZ ys xs))
    ((AgreeS k0 x xs0 ys0 p0) (AgreeS _ x _ _ (agree-sym _ _ _ p0)))))

(def-fns _ $ erased agree-trans : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (List (Nat)) zs)
    (subterm erased (Agree k xs ys) p) (erased (Agree k ys zs) q) -> (erased (Agree k xs zs) r)
  (match erased p _
    ((AgreeZ a b) (AgreeZ xs zs))
    ((AgreeS k0 x xs0 ys0 p0)
      (match erased q _
        ((AgreeS k1 x1 ys1 zs0 q0) (AgreeS _ x _ _ (agree-trans _ _ _ _ p0 q0)))))))

(def-fns _ $ erased agree-nth : (erased (Nat) i) (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x)
    (subterm erased (Agree k xs ys) p) (erased (Lt i k) lt) (erased (Nth (Nat) i xs x) n) -> (erased (Nth (Nat) i ys x) n2)
  (match erased p _
    ((AgreeZ a b) (match erased lt _))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased n _
        ((NthHere a e r) (NthHere _ x ys0))
        ((NthThere a i1 y r e n1)
          (match erased lt _
            ((LtS l1 l2 lt1) (NthThere _ _ x0 _ _ (agree-nth _ _ _ _ _ p0 lt1 n1)))))))))

(def-fns _ $ erased agree-snoc : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x)
    (subterm erased (Agree k xs ys) p) (erased (Nth (Nat) k xs x) nx) (erased (Nth (Nat) k ys x) ny) -> (erased (Agree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b)
      (match erased nx _
        ((NthHere a1 e1 r1) (match erased ny _ ((NthHere a2 e2 r2) (AgreeS _ x _ _ (AgreeZ r1 r2)))))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased nx _
        ((NthThere a1 i1 y1 r1 e1 n1)
          (match erased ny _
            ((NthThere a2 i2 y2 r2 e2 n2) (AgreeS _ x0 _ _ (agree-snoc _ _ _ _ p0 n1 n2)))))))))

(def-fns _ $ erased disagree-at : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x) (erased (Nat) y)
    (subterm erased (Agree k xs ys) p) (erased (Nth (Nat) k xs x) nx) (erased (Nth (Nat) k ys y) ny) (erased (NatApart x y) d) ->
    (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b)
      (match erased nx _
        ((NthHere a1 e1 r1) (match erased ny _ ((NthHere a2 e2 r2) (DisHead (Zero) _ _ r1 r2 d))))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased nx _
        ((NthThere a1 i1 y1 r1 e1 n1)
          (match erased ny _
            ((NthThere a2 i2 y2 r2 e2 n2) (DisTail _ x0 _ _ (disagree-at _ _ _ _ _ p0 n1 n2 d)))))))))

(def-fns _ $ erased disagree-short : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Drop (Nat) k xs (Nil (Nat))) dr) -> (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b) (match erased dr _ ((DropZ a1 e1) (DisNilL (Zero) ys))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased dr _
        ((DropS a1 k1 x1 xs1 ys1 dr1) (DisTail _ x0 _ _ (disagree-short _ _ _ p0 dr1)))))))

(def-fns _ $ erased disagree-short-r : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Drop (Nat) k ys (Nil (Nat))) dr) -> (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b) (match erased dr _ ((DropZ a1 e1) (DisNilR (Zero) xs))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased dr _
        ((DropS a1 k1 x1 xs1 ys1 dr1) (DisTail _ x0 _ _ (disagree-short-r _ _ _ p0 dr1)))))))

(def-fns _ $ erased drop-nth : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A x) (erased (List A) rest)
    (subterm erased (Drop A k xs (Cons _ x rest)) dr) -> (erased (Nth A k xs x) n) (erased (Drop A (Succ k) xs rest) dr1)
  (match erased dr _
    ((DropZ a e) (values (NthHere _ x rest) (DropS _ _ x _ _ (DropZ _ rest))))
    ((DropS a k1 y xs1 ys1 dr1)
      (let (erased n) (erased d2) (drop-nth _ _ _ _ _ dr1))
      (values (NthThere _ _ y _ _ n) (DropS _ _ y _ _ d2)))))

(def-fns _ $ erased revonto-shift : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A y) (erased (List A) acc) (erased (List A) res)
    (subterm erased (RevOnto A k xs (Cons _ y acc) res) p) -> (erased (RevOnto A (Succ k) (Cons _ y xs) acc res) q)
  (match erased p _
    ((RevZ a e1 e2) (RevS _ _ _ _ _ _ (RevZ _ (Cons _ y xs) acc) (NthHere _ y xs)))
    ((RevS a k1 e1 e2 res1 x p1 n)
      (RevS _ _ _ _ _ _ (revonto-shift _ _ _ _ _ _ p1) (NthThere _ _ y _ _ n)))))


(def-fns _ $ erased nth-fn : (erased Type A) (erased (Nat) i) (erased (List A) xs) (erased A x) (erased A y)
    (subterm erased (Nth A i xs x) p) (erased (Nth A i xs y) q) -> (erased (Eq A x y) e)
  (match erased p _
    ((NthHere a e r) (match erased q _ ((NthHere a2 e2 r2) (Refl _ x))))
    ((NthThere a i1 z r e p1) (match erased q _ ((NthThere a2 i2 z2 r2 e2 q1) (nth-fn _ _ _ _ _ p1 q1))))))

(def-fns _ $ erased concat-total : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (Concat A xs ys zs) p)
  (match erased xs _
    ((Nil a) (values ys (CatNil A ys)))
    ((Cons a x rest)
      (let (erased zs) (erased p) (concat-total _ rest ys))
      (values (Cons _ x zs) (CatCons A x rest ys zs p)))))

(def-fns _ $ erased concat-length-snoc : (erased Type A) (erased (List A) xs) (erased A y) (erased (List A) xy) (erased (Nat) n)
    (subterm erased (Concat A xs (Cons _ y (Nil A)) xy) p) (erased (Length A xs n) l) -> (erased (Length A xy (Succ n)) l2)
  (match erased p _
    ((CatNil a e) (match erased l _ ((LNil a2) (LCons A y (Nil A) (Zero) (LNil A)))))
    ((CatCons a x rest e zs p1)
      (match erased l _
        ((LCons a2 e2 e3 n1 l1) (LCons A x zs (Succ n1) (concat-length-snoc _ _ _ _ _ p1 l1)))))))

(def-fns _ $ erased concat-snoc-shift : (erased Type A) (erased (List A) xs) (erased A y) (erased (List A) xy) (erased (List A) d) (erased (List A) s)
    (subterm erased (Concat A xs (Cons _ y (Nil A)) xy) p) (erased (Concat A xs (Cons _ y d) s) q) -> (erased (Concat A xy d s) r)
  (match erased p _
    ((CatNil a e) (match erased q _ ((CatNil a2 e2) (CatCons A y (Nil A) d d (CatNil A d)))))
    ((CatCons a x rest e zs p1)
      (match erased q _
        ((CatCons a2 x2 rest2 e2 zs2 q1) (CatCons A x zs d zs2 (concat-snoc-shift _ _ _ _ _ _ p1 q1)))))))

(def-fns _ $ erased drop-unstep : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A y) (erased (List A) d)
    (subterm erased (Drop A (Succ k) xs d) dr) (erased (Nth A k xs y) n) -> (erased (Drop A k xs (Cons _ y d)) dr2)
  (match erased dr _
    ((DropS a k1 x0 xs0 e p)
      (match erased n _
        ((NthHere a2 e2 r2) (match erased p _ ((DropZ a3 e3) (DropZ _ xs))))
        ((NthThere a2 i2 z2 r2 e2 n1) (DropS _ _ x0 _ _ (drop-unstep _ _ _ _ _ p n1)))))))

(def-fns _ $ erased apart-irrefl : (erased (Nat) x) (erased (NatApart x x) d) -> (erased (False) f)
  (match erased d _
    ((ApartLt a b lt) (lt-asym _ _ lt (lt-succ x)))
    ((ApartGt a b lt) (lt-asym _ _ lt (lt-succ x)))))

(def-fns _ $ erased disagree-nth : (erased (Nat) p) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x) (erased (Nat) y)
    (subterm erased (Agree p xs ys) ag) (erased (Disagree (Succ p) xs ys) dis) (erased (Nth (Nat) p xs x) nx) (erased (Nth (Nat) p ys y) ny) ->
    (erased (NatApart x y) d)
  (match erased ag _
    ((AgreeZ a b)
      (match erased dis _
        ((DisNilL k e) (match erased nx _))
        ((DisNilR k e) (match erased ny _))
        ((DisHead k x0 y0 xs0 ys0 d0) (match erased nx _ ((NthHere a1 e1 r1) (match erased ny _ ((NthHere a2 e2 r2) d0)))))
        ((DisTail k x0 xs0 ys0 dis0) (match erased dis0 _))))
    ((AgreeS k x0 xs0 ys0 ag0)
      (match erased dis _
        (absurd (DisHead k2 x2 y2 xs2 ys2 d0) (apart-irrefl _ d0))
        ((DisTail k2 x2 xs2 ys2 dis0)
          (match erased nx _
            ((NthThere a i z r e n1) (match erased ny _ ((NthThere a2 i2 z2 r2 e2 n2) (disagree-nth _ _ _ _ _ ag0 dis0 n1 n2))))))))))

(def-fns _ $ erased win-pal : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (subterm erased (Win k l mid r w) win) (erased (Agree k l r) ag) (erased (Palindrome (Nat) mid) pm) -> (erased (Palindrome (Nat) w) p)
  (match erased win _
    ((WinZ a b c) pm)
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (let-match erased (nth-fn _ _ _ _ _ (agree-nth _ _ _ _ _ ag (lt-succ k0) nx) ny) (Refl t e))
      (PalWrap (Nat) x w0 wy (win-pal _ _ _ _ _ win0 (agree-weaken _ _ _ ag) pm) q))))

(def-fns _ $ erased win-notpal : (erased (Nat) k) (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (subterm erased (Win k l mid r w) win) (erased (Agree p l r) ag) (erased (Disagree (Succ p) l r) dis) (erased (Lt p k) lt) -> (erased (NotPalindrome w) np)
  (match erased win _
    ((WinZ a b c) (match erased lt _))
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased (nat-cmp p k0) _
        ((CEq t rr a) (NotPalEnds x y w0 wy q (disagree-nth _ _ _ _ _ ag dis nx ny)))
        (absurd (CGt t rr a b gt) (lt-asym _ _ gt lt))
        ((CLt t rr a b plt)
          (match erased (nat-cmp x y) _
            ((CLt t2 r2 a2 b2 xlt) (NotPalEnds x y w0 wy q (ApartLt x y xlt)))
            ((CGt t2 r2 a2 b2 xgt) (NotPalEnds x y w0 wy q (ApartGt x y xgt)))
            ((CEq t2 r2 a2) (NotPalInner x w0 wy q (win-notpal _ _ _ _ _ _ win0 ag dis plt)))))))))

(def-fns _ $ erased win-inner : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (erased (Nat) x) (erased (List (Nat)) midx)
    (subterm erased (Win k l (Cons _ x midx) r w) win) (erased (Concat (Nat) mid (Cons _ x (Nil (Nat))) midx) cm) ->
    (erased (Win (Succ k) (Cons _ x l) mid (Cons _ x r) w) win2)
  (match erased win _
    ((WinZ a b c)
      (WinS _ _ _ _ _ _ _ _ (WinZ (Cons _ x l) mid (Cons _ x r))
            (NthHere _ x l) (NthHere _ x r) cm))
    ((WinS k0 l0 m0 r0 w0 a b wb win0 na nb q)
      (WinS _ _ _ _ _ _ _ _ (win-inner _ _ _ _ _ _ _ win0 cm)
            (NthThere _ _ x _ _ na) (NthThere _ _ x _ _ nb) q))))

(def-fns _ $ erased agree-win : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) mid)
    (subterm erased (Agree k l r) ag) -> (erased (List (Nat)) w) (erased (Win k l mid r w) win)
  (match erased ag _
    ((AgreeZ a b) (values mid (WinZ l mid r)))
    ((AgreeS k0 x xs ys ag0)
      (let (erased midx) (erased cm) (concat-total _ mid (Cons _ x (Nil (Nat)))))
      (let (erased w) (erased win) (agree-win _ _ _ (Cons _ x midx) ag0))
      (values w (win-inner _ _ _ _ _ _ _ win cm)))))

(def-fns _ $ erased win-length : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (erased (Nat) m) (erased (Nat) kk) (erased (Nat) n)
    (subterm erased (Win k l mid r w) win) (erased (Length (Nat) mid m) lm) (erased (Double k kk) dk) (erased (Add kk m n) ad) ->
    (erased (Length (Nat) w n) lw)
  (match erased win _
    ((WinZ a b c) (match erased dk _ ((D0) (match erased ad _ ((AddZero e) lm)))))
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased dk _
        ((DS a1 kk0 dk0)
          (match erased ad _
            ((AddSucc a2 b2 c2 ad1)
              (match erased ad1 _
                ((AddSucc a3 b3 n0 ad0)
                  (LCons (Nat) x wy (Succ n0) (concat-length-snoc _ _ _ _ _ q (win-length _ _ _ _ _ _ _ _ win0 lm dk0 ad0))))))))))))

(def-fns _ $ erased win-prefix : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (erased (List (Nat)) mr) (erased (List (Nat)) s) (erased (List (Nat)) d)
    (subterm erased (Win k l mid r w) win) (erased (Concat (Nat) mid r mr) cm) (erased (RevOnto (Nat) k l mr s) rv) (erased (Drop (Nat) k r d) dr) ->
    (erased (Concat (Nat) w d s) c)
  (match erased win _
    ((WinZ a b c) (match erased rv _ ((RevZ a2 b2 c2) (match erased dr _ ((DropZ a3 b3) cm)))))
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased rv _
        ((RevS a2 k2 e2 e3 s0 x2 rv0 nx2)
          (let-match erased (nth-fn _ _ _ _ _ nx nx2) (Refl t e))
          (CatCons (Nat) x wy d s0
                (concat-snoc-shift _ _ _ _ _ _ q
                  (win-prefix _ _ _ _ _ _ _ _ win0 cm rv0 (drop-unstep _ _ _ _ _ dr ny)))))))))


(def-fns _ $ erased apart-sym : (erased (Nat) x) (erased (Nat) y) (erased (NatApart x y) d) -> (erased (NatApart y x) d2)
  (match erased d _
    ((ApartLt a b lt) (ApartGt y x lt))
    ((ApartGt a b lt) (ApartLt y x lt))))

(def-fns _ $ erased mid-length : (erased (Nat) m) (erased (List (Nat)) mid) (erased (Mid m mid) md) -> (erased (Length (Nat) mid m) l)
  (match erased md _
    ((MidEven) (LNil (Nat)))
    ((MidOdd z) (LCons (Nat) z (Nil (Nat)) (Zero) (LNil (Nat))))))

(def-fns _ $ erased mid-pal : (erased (Nat) m) (erased (List (Nat)) mid) (erased (Mid m mid) md) -> (erased (Palindrome (Nat) mid) p)
  (match erased md _
    ((MidEven) (PalNil (Nat)))
    ((MidOdd z) (PalOne (Nat) z))))

(def-fns _ $ erased agree-weaken-to : (erased (Nat) k) (erased (Nat) j) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Lt j (Succ k)) le) -> (erased (Agree j xs ys) q)
  (match erased p _
    ((AgreeZ a b) (match erased le _ ((LtZ b1) (AgreeZ xs ys)) ((LtS a1 b1 l1) (match erased l1 _))))
    ((AgreeS k0 x xs0 ys0 p0)
      (match erased j _
        ((Zero) (AgreeZ xs ys))
        ((Succ j1) (match erased le _ ((LtS a1 b1 l1) (AgreeS _ x _ _ (agree-weaken-to _ _ _ _ p0 l1)))))))))

(def-fns _ $ erased agree-nth-ex : (erased (Nat) k) (erased (Nat) i) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Lt i k) lt) -> (erased (Nat) x) (erased (Nth (Nat) i xs x) nx) (erased (Nth (Nat) i ys x) ny)
  (match erased p _
    ((AgreeZ a b) (match erased lt _))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased i _
        ((Zero) (values x0 (NthHere _ x0 xs0) (NthHere _ x0 ys0)))
        ((Succ i1)
          (match erased lt _
            ((LtS a1 b1 l1)
              (let (erased x) (erased nx) (erased ny) (agree-nth-ex _ _ _ _ p0 l1))
              (values x (NthThere _ _ x0 _ _ nx) (NthThere _ _ x0 _ _ ny)))))))))

(def-fns _ $ erased agree-drop : (erased (Nat) p) (erased (Nat) d) (erased (Nat) q) (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (List (Nat)) ld) (erased (List (Nat)) rd)
    (subterm erased (Drop (Nat) d l ld) dl) (erased (Drop (Nat) d r rd) dr) (erased (Add d q p) ad) (erased (Agree p l r) ag) ->
    (erased (Agree q ld rd) ag2)
  (match erased dl _
    ((DropZ a e) (match erased dr _ ((DropZ a2 e2) (match erased ad _ ((AddZero b) ag)))))
    ((DropS a d1 x l1 e dl1)
      (match erased dr _
        ((DropS a2 d2 y r1 e2 dr1)
          (match erased ad _
            ((AddSucc a3 b3 c3 ad1)
              (match erased ag _
                ((AgreeS k0 x0 xs0 ys0 ag0) (agree-drop _ _ _ _ _ _ _ dl1 dr1 ad1 ag0))))))))))

(def-fns _ $ erased nth-concat-after : (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w) (erased (Nat) m) (erased (Nat) e)
    (erased (Nat) s) (erased (Nat) x)
    (subterm erased (Concat (Nat) mid r w) cm) (erased (Length (Nat) mid m) lm) (erased (Add m e s) ad) (erased (Nth (Nat) e r x) n) ->
    (erased (Nth (Nat) s w x) n2)
  (match erased cm _
    ((CatNil a e1) (match erased lm _ ((LNil a2) (match erased ad _ ((AddZero b) n)))))
    ((CatCons a z mid1 e1 w1 cm1)
      (match erased lm _
        ((LCons a2 e2 e3 m1 lm1)
          (match erased ad _
            ((AddSucc a3 b3 s1 ad1) (NthThere _ _ z _ _ (nth-concat-after _ _ _ _ _ _ _ cm1 lm1 ad1 n)))))))))

(def-fns _ $ erased revonto-drop-mid : (erased (Nat) m) (erased (List (Nat)) mid) (erased (Nat) d) (erased (Nat) e) (erased (List (Nat)) l)
    (erased (List (Nat)) w) (erased (List (Nat)) b) (erased (List (Nat)) b2)
    (erased (Mid m mid) md) (erased (Add m e d) ad) (erased (RevOnto (Nat) d l w b) rv) (erased (Drop (Nat) m b b2) dr) ->
    (erased (RevOnto (Nat) e l w b2) rv2)
  (match erased md _
    ((MidEven) (match erased ad _ ((AddZero b1) (match erased dr _ ((DropZ a1 e1) rv)))))
    ((MidOdd z)
      (match erased ad _
        ((AddSucc a1 b1 c1 ad1)
          (match erased ad1 _
            ((AddZero b2)
              (match erased rv _
                ((RevS a2 k2 e2 e3 res x rv1 n)
                  (match erased dr _
                    ((DropS a3 k3 x3 xs3 e4 dr1) (match erased dr1 _ ((DropZ a4 e5) rv1)))))))))))))

; The mirror lemma: inside a palindrome of radius p at (l, r) with middle mid, the left arm of the
; centre e+m steps to the right (RevOnto (e+m) w l a) agrees with the right arm of the centre e+m
; steps to the left (RevOnto e l w b) on the first q elements, q + (e+m) = p.

(def-fns _ $ erased mirror-agree : (erased (Nat) p) (erased (Nat) m) (erased (Nat) e) (erased (Nat) em) (erased (Nat) q)
    (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) mid) (erased (List (Nat)) w) (erased (List (Nat)) a) (erased (List (Nat)) b)
    (erased (Agree p l r) ag) (erased (Mid m mid) md) (erased (Concat (Nat) mid r w) cm)
    (subterm erased (RevOnto (Nat) e l w b) rb) (erased (Add m e em) aem) (erased (RevOnto (Nat) em w l a) ra) (erased (Add em q p) aq) ->
    (erased (Agree q a b) ag2)
  (match erased rb _
    ((RevZ a1 e1 e2)
      (match erased md _
        ((MidEven)
          (match erased aem _
            ((AddZero b1)
              (match erased ra _
                ((RevZ a2 e3 e4) (match erased cm _ ((CatNil a3 e5) (match erased aq _ ((AddZero b2) ag)))))))))
        ((MidOdd z)
          (match erased aem _
            ((AddSucc a1 b1 c1 aem1)
              (match erased aem1 _
                ((AddZero b2)
                  (match erased ra _
                    ((RevS a2 k2 e3 e4 res x ra1 n)
                      (match erased ra1 _
                        ((RevZ a3 e5 e6)
                          (match erased cm _
                            ((CatCons a4 z4 e7 e8 zs cm1)
                              (match erased cm1 _
                                ((CatNil a5 e9)
                                  (match erased n _
                                    ((NthHere a6 e10 e11)
                                      (match erased aq _
                                        ((AddSucc a7 b7 c7 aq1)
                                          (match erased aq1 _
                                            ((AddZero b8)
                                              (match erased q _
                                                ((Zero) (AgreeZ a b))
                                                ((Succ q1)
                                                  (AgreeS _ z _ _ (agree-weaken _ _ _ (agree-weaken _ _ _ ag))))))))))))))))))))))))))
    ((RevS a1 k1 e1 e2 b1 lx rb1 nl)
      (let (erased em1) (erased eem) (erased aem1) (add-succ-right-inv _ _ _ aem))
      (let-match erased eem (Refl t1 r1))
      (match erased ra _
            ((RevS a2 k2 e3 e4 a1 wx ra1 nw)
              (match erased aq _
                ((AddSucc a3 b3 c3 aq1)
                  (let (erased ltk) (lt-le-trans _ _ _ (add-le-left _ _ _ (add-comm _ _ _ aem1)) (LtS _ _ (add-le-left _ _ _ aq1))))
                  (let (erased nr) (agree-nth _ _ _ _ _ ag ltk nl))
                  (let (erased nw2) (nth-concat-after _ _ _ _ _ _ _ cm (mid-length _ _ md) aem1 nr))
                  (let-match erased (nth-fn _ _ _ _ _ nw nw2) (Refl t2 r2))
                  (let (erased ih) (mirror-agree _ _ _ _ _ _ _ _ _ _ _ ag md cm rb1 aem1 ra1 (add-succ-right _ _ _ aq1)))
                      (match erased q _
                        ((Zero) (AgreeZ a b))
                        ((Succ q2) (AgreeS _ lx _ _ (agree-weaken _ _ _ (agree-weaken _ _ _ ih))))))))))))


; A centre's certificate: its radius is exact. Back is the runtime list of radii of the centres
; before a zipper, each with its certificate; Bound says every radius there gives a window no longer than b.

(def-adts
  (Cert : ((Nat) m) ((List (Nat)) l) ((List (Nat)) r) ((Nat) p) -> Type
    enum
    (many MkCert : (erased (Nat) m) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (Nat) p) (erased (List (Nat)) arm)
        (erased (Drop (Nat) m r arm) dr) (erased (Agree p l arm) ag) (erased (Disagree (Succ p) l arm) dis) -> (Cert m l r p))))

(def-adts
  (Back : ((Nat) m) ((List (Nat)) xs) ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many BackZ : (erased (Nat) m) (erased (List (Nat)) xs) -> (Back m xs (Nil (Nat)) xs))
    (many BackS : (erased (Nat) m) (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (Nat) x) (erased (List (Nat)) r) (many (Nat) p)
        (erased (Cert m l (Cons _ x r) p) c) (many (Back m xs l (Cons _ x r)) rest) -> (Back m xs (Cons _ x l) r))))

(def-adts
  (Bound : ((Nat) m) ((Nat) b) ((List (Nat)) xs) ((List (Nat)) l) ((List (Nat)) r) ((Back m xs l r) bk) -> Type
    enum
    (many BoundZ : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) xs) -> (Bound m b xs (Nil (Nat)) xs (BackZ m xs)))
    (many BoundS : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (Nat) x) (erased (List (Nat)) r) (erased (Nat) p)
        (erased (Cert m l (Cons _ x r) p) c) (erased (Back m xs l (Cons _ x r)) rest)
        (erased (Nat) pp) (erased (Nat) n) (erased (Double p pp) dd) (erased (Add pp m n) an) (erased (Lt n (Succ b)) le)
        (erased (Bound m b xs l (Cons _ x r) rest) bd) ->
       (Bound m b xs (Cons _ x l) r (BackS _ _ _ _ _ p c rest)))))

; The mirror gives a certificate for the current centre when the mirror centre's radius p2 falls
; short of the reach q: la/ra are the current arms, lm/rm the mirror's.

(def-fns _ $ erased mirror-cert : (erased (Nat) q) (erased (Nat) p2) (erased (List (Nat)) la) (erased (List (Nat)) ra)
    (erased (List (Nat)) lm) (erased (List (Nat)) rm)
    (erased (Agree q la rm) x1) (erased (Agree q lm ra) x2) (erased (Agree p2 lm rm) ag) (erased (Disagree (Succ p2) lm rm) dis)
    (erased (Lt p2 q) lt) ->
    (erased (Agree p2 la ra) ag2) (erased (Disagree (Succ p2) la ra) dis2)
  (let (erased le) (lt-weaken _ _ lt))
  (let (erased a1) (agree-weaken-to _ _ _ _ x1 le))
  (let (erased a2) (agree-weaken-to _ _ _ _ x2 le))
  (let (erased ag2) (agree-trans _ _ _ _ a1 (agree-trans _ _ _ _ (agree-sym _ _ _ ag) a2)))
  (let (erased x) (erased nlm) (erased nra) (agree-nth-ex _ _ _ _ x2 lt))
  (let (erased y) (erased nla) (erased nrm) (agree-nth-ex _ _ _ _ x1 lt))
  (let (erased d) (disagree-nth _ _ _ _ _ ag dis nlm nrm))
  (values ag2 (disagree-at _ _ _ _ _ ag2 nla nra (apart-sym _ _ d))))

; --- the runtime expansion around a centre ---
; lp is the rest of the left arm below radius k and rp the suffix it was popped into, so (lp, rp) is
; a zipper of the input at the window's left end; rd is the rest of the right arm.

(def-fns _ $ many expand : (many (Nat) k) (subterm many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
    (erased (List (Nat)) l) (erased (List (Nat)) ri) (erased (List (Nat)) r)
    (erased (Drop (Nat) k l lp) dl) (erased (RevOnto (Nat) k l ri rp) rv) (erased (Drop (Nat) k r rd) dr) (erased (Agree k l r) ag) ->
    (many (Nat) p) (many (List (Nat)) lp2) (many (List (Nat)) rp2) (many (List (Nat)) rd2)
    (erased (Drop (Nat) p l lp2) dl2) (erased (RevOnto (Nat) p l ri rp2) rv2) (erased (Drop (Nat) p r rd2) dr2)
    (erased (Agree p l r) ag2) (erased (Disagree (Succ p) l r) dis)
  (match many lp _
    ((Nil a) (values k lp rp rd dl rv dr ag (disagree-short _ _ _ ag dl)))
    ((Cons a x lp1)
      (match many rd _
        ((Nil a2) (values k lp rp rd dl rv dr ag (disagree-short-r _ _ _ ag dr)))
        ((Cons a2 y rd1)
          (let (erased nx) (erased dl1) (drop-nth _ _ _ _ _ dl))
          (let (erased ny) (erased dr1) (drop-nth _ _ _ _ _ dr))
          (match many (nat-cmp x y) _
            ((CLt t rr a3 b3 lt) (values k lp rp rd dl rv dr ag (disagree-at _ _ _ _ _ ag nx ny (ApartLt x y lt))))
            ((CGt t rr a3 b3 gt) (values k lp rp rd dl rv dr ag (disagree-at _ _ _ _ _ ag nx ny (ApartGt x y gt))))
            ((CEq t rr a3)
              (tail (expand (Succ k) lp1 (Cons _ x rp) rd1 _ _ _ dl1 (RevS _ _ _ _ _ _ rv nx) dr1 (agree-snoc _ _ _ _ ag nx ny))))))))))


(def-fns _ $ erased drop-fn : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
    (subterm erased (Drop A k xs ys) p) (erased (Drop A k xs zs) q) -> (erased (Eq (List A) ys zs) e)
  (match erased p _
    ((DropZ a e1) (match erased q _ ((DropZ a2 e2) (Refl _ ys))))
    ((DropS a k1 x xs1 e1 p1) (match erased q _ ((DropS a2 k2 x2 xs2 e2 q1) (drop-fn _ _ _ _ _ p1 q1))))))

(def-fns _ $ erased drop-compose : (erased Type A) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
    (subterm erased (Drop A a xs ys) p) (erased (Drop A b ys zs) q) (erased (Add a b c) ad) -> (erased (Drop A c xs zs) r)
  (match erased p _
    ((DropZ a1 e1) (match erased ad _ ((AddZero b1) q)))
    ((DropS a1 k1 x xs1 e1 p1)
      (match erased ad _
        ((AddSucc a2 b2 c2 ad1) (DropS _ _ x _ _ (drop-compose _ _ _ _ _ _ _ p1 q ad1)))))))

(def-fns _ $ erased drop-split : (erased Type A) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (List A) xs) (erased (List A) zs)
    (subterm erased (Drop A c xs zs) p) (erased (Add a b c) ad) -> (erased (List A) ys) (erased (Drop A a xs ys) q) (erased (Drop A b ys zs) r)
  (match erased ad _
    ((AddZero b1) (values xs (DropZ _ xs) p))
    ((AddSucc a1 b1 c1 ad1)
      (match erased p _
        ((DropS a2 k2 x xs1 e2 p1)
          (let (erased ys) (erased q) (erased r) (drop-split _ _ _ _ _ _ p1 ad1))
          (values ys (DropS _ _ x _ _ q) r))))))

(def-fns _ $ erased drop-swap : (erased (Nat) d) (erased (Nat) m) (erased (List (Nat)) w) (erased (List (Nat)) ri) (erased (List (Nat)) arm) (erased (List (Nat)) armc)
    (erased (Drop (Nat) d w ri) p) (erased (Drop (Nat) m ri arm) q) (erased (Drop (Nat) m w armc) r) -> (erased (Drop (Nat) d armc arm) s)
  (let (erased dm) (erased adm) (add d m))
  (let (erased ys) (erased q2) (erased r2) (drop-split _ _ _ _ _ _ (drop-compose _ _ _ _ _ _ _ p q adm) (add-comm _ _ _ adm)))
  (let-match erased (drop-fn _ _ _ _ _ q2 r) (Refl t e))
  r2)

(def-adts
  (Par : ((Nat) m) -> Type
    enum
    (many PEven : -> (Par (Zero)))
    (many POdd : -> (Par (Succ (Zero))))))

(def-fns _ $ erased mid-of : (erased (Nat) m) (erased (List (Nat)) w) (erased (List (Nat)) arm) (erased (Par m) pr) (erased (Drop (Nat) m w arm) dr) ->
    (erased (List (Nat)) mid) (erased (Mid m mid) md) (erased (Concat (Nat) mid arm w) c)
  (match erased pr _
    ((PEven) (match erased dr _ ((DropZ a e) (values (Nil (Nat)) (MidEven) (CatNil (Nat) w)))))
    ((POdd)
      (match erased dr _
        ((DropS a k x xs e dr1)
          (match erased dr1 _
            ((DropZ a2 e2) (values (Cons _ x (Nil (Nat))) (MidOdd x) (CatCons (Nat) x (Nil (Nat)) xs xs (CatNil (Nat) xs))))))))))

(def-fns _ $ erased drop-nth-head : (erased Type A) (erased (Nat) k) (erased (List A) l) (erased A x) (erased (List A) l0)
    (subterm erased (Drop A k l l0) d) (erased (Nth A k l x) n) -> (erased (List A) l1) (erased (Eq (List A) l0 (Cons _ x l1)) e) (erased (Drop A (Succ k) l l1) d2)
  (match erased d _
    ((DropZ a e1) (match erased n _ ((NthHere a2 e2 rest) (values rest (Refl _ l0) (DropS _ _ x _ _ (DropZ _ rest))))))
    ((DropS a k1 y l2 e1 d1)
      (match erased n _
        ((NthThere a2 i2 y2 r2 e2 n1)
          (let (erased l1) (erased e) (erased d2) (drop-nth-head _ _ _ _ _ d1 n1))
          (values l1 e (DropS _ _ y _ _ d2)))))))

(def-fns _ $ erased zip-back : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) l) (erased (List A) r) (erased (List A) s)
    (subterm erased (RevOnto A k l r s) rv) (erased (Zip A xs l r) z) -> (erased (List A) l0) (erased (Drop A k l l0) d) (erased (Zip A xs l0 s) z2)
  (match erased rv _
    ((RevZ a e1 e2) (values l (DropZ _ l) z))
    ((RevS a k1 e1 e2 s0 x rv1 n)
      (let (erased l0) (erased d) (erased z2) (zip-back _ _ _ _ _ _ rv1 z))
      (let (erased l1) (erased e) (erased d2) (drop-nth-head _ _ _ _ _ d n))
      (let-match erased e (Refl t e3))
      (match erased z2 _
            ((ZipS a2 e4 l2 x2 e5 z3) (values l1 d2 z3))))))

(def-fns _ $ erased zip-has : (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) s) (erased (Nat) n)
    (subterm erased (Zip (Nat) xs l s) z) (erased (HasPalindromeOfLength s n) h) -> (erased (HasPalindromeOfLength xs n) h2)
  (match erased z _
    ((ZipZ a e) h)
    ((ZipS a e l1 x r z1) (zip-has _ _ _ _ z1 (HasThere x s n h)))))

(def-fns _ $ erased concat-take : (erased Type A) (erased (List A) w) (erased (List A) d) (erased (List A) s) (erased (Nat) n)
    (subterm erased (Concat A w d s) c) (erased (Length A w n) l) -> (erased (Take A n s w) t)
  (match erased c _
    ((CatNil a e) (match erased l _ ((LNil a2) (TakeZero A s))))
    ((CatCons a x rest e zs c1)
      (match erased l _ ((LCons a2 e2 e3 n1 l1) (TakeSucc A n1 x zs rest (concat-take _ _ _ _ _ c1 l1)))))))

(def-fns _ $ erased bound-weaken : (erased (Nat) m) (erased (Nat) b) (erased (Nat) b2) (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Back m xs l r) bk) (subterm erased (Bound m b xs l r bk) bd) (erased (Lt b (Succ b2)) le) -> (erased (Bound m b2 xs l r bk) bd2)
  (match erased bd _
    ((BoundZ a e e2) (BoundZ m b2 xs))
    ((BoundS a e e2 l0 x r0 p c rest pp n dd an lt bd1)
      (BoundS _ _ _ _ _ _ _ c _ _ _ dd an (lt-le-trans _ _ _ lt (LtS _ _ le)) (bound-weaken _ _ _ _ _ _ _ bd1 le)))))

(def-fns _ $ erased agree-drop-ex : (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) arm)
    (subterm erased (Agree p l arm) ag) -> (erased (List (Nat)) d) (erased (Drop (Nat) p arm d) dr)
  (match erased ag _
    ((AgreeZ a b) (values arm (DropZ _ arm)))
    ((AgreeS k x xs ys ag0)
      (let (erased d) (erased dr) (agree-drop-ex _ _ _ ag0))
      (values d (DropS _ _ x _ _ dr)))))

(def-fns _ $ erased has-at-centre : (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) ri) (erased (List (Nat)) arm)
    (erased (Nat) m) (erased (Nat) p) (erased (List (Nat)) s) (erased (Nat) pp) (erased (Nat) n)
    (erased (Zip (Nat) xs l ri) z) (erased (Par m) pr) (erased (Drop (Nat) m ri arm) dr) (erased (Agree p l arm) ag)
    (erased (RevOnto (Nat) p l ri s) rv) (erased (Double p pp) dd) (erased (Add pp m n) an) -> (erased (HasPalindromeOfLength xs n) h)
  (let (erased mid) (erased md) (erased cm) (mid-of _ _ _ pr dr))
  (let (erased w) (erased win) (agree-win _ _ _ mid ag))
  (let (erased pal) (win-pal _ _ _ _ _ win ag (mid-pal _ _ md)))
  (let (erased lw) (win-length _ _ _ _ _ _ _ _ win (mid-length _ _ md) dd an))
  (let (erased d) (erased dr2) (agree-drop-ex _ _ _ ag))
  (let (erased pre) (win-prefix _ _ _ _ _ _ _ _ win cm rv dr2))
  (let (erased l0) (erased dl0) (erased z2) (zip-back _ _ _ _ _ _ rv z))
  (zip-has _ _ _ _ z2 (HasHere s n w (concat-take _ _ _ _ _ pre lw) pal)))


; --- the main loop ---
; Reach is what the loop knows about the rightmost palindrome seen so far, at the centre (li, ri): nothing
; (Out), or (In) the palindrome of radius pc at (lc, w), the current centre d steps past it with q more
; steps inside it, and the radius list from the mirror centre (mp).

(def-adts
  (Reach : ((Nat) m) ((List (Nat)) xs) ((List (Nat)) li) ((List (Nat)) ri) ((Nat) q) -> Type
    enum
    (many Out : (erased (Nat) m) (erased (List (Nat)) xs) (erased (List (Nat)) li) (erased (List (Nat)) ri) -> (Reach m xs li ri (Zero)))
    (many In : (erased (Nat) m) (erased (List (Nat)) xs) (erased (List (Nat)) li) (erased (List (Nat)) ri) (erased (Nat) q1)
        (erased (List (Nat)) lc) (erased (List (Nat)) w) (erased (List (Nat)) armc) (erased (Nat) pc) (erased (Nat) d) (erased (Nat) e)
        (erased (Nat) x) (erased (List (Nat)) lm) (erased (List (Nat)) rm1)
        (erased (Drop (Nat) m w armc) drc) (erased (Agree pc lc armc) agc)
        (erased (RevOnto (Nat) d w lc li) rvl) (erased (Drop (Nat) d w ri) drr)
        (erased (Add d (Succ q1) pc) aq) (erased (Add m e d) aem)
        (erased (Drop (Nat) d lc lm) dlm) (erased (RevOnto (Nat) d lc w (Cons _ x rm1)) rvm)
        (many (Back m xs (Cons _ x lm) rm1) mp) ->
       (Reach m xs li ri (Succ q1)))))

(def-adts
  (PredZ : ((Nat) k) ((Nat) qn) -> Type
    enum
    (many PZ : -> (PredZ (Zero) (Zero)))
    (many PS : (erased (Nat) k) -> (PredZ (Succ k) k))))

(def-fns _ $ erased agree-drop-cons : (erased (Nat) p) (erased (Nat) d) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) ld)
    (erased (Agree p l r) ag) (subterm erased (Drop (Nat) d l ld) dr) (erased (Lt d p) lt) ->
    (erased (Nat) y) (erased (List (Nat)) ld2) (erased (Eq (List (Nat)) ld (Cons _ y ld2)) e)
  (match erased dr _
    ((DropZ a e1) (match erased lt _ ((LtZ b) (match erased ag _ ((AgreeS k x xs ys ag0) (values x xs (Refl _ ld)))))))
    ((DropS a k1 x xs e1 dr1)
      (match erased lt _
        ((LtS a2 b2 lt1) (match erased ag _ ((AgreeS k x2 xs2 ys ag0) (agree-drop-cons _ _ _ _ _ ag0 dr1 lt1))))))))

(def-fns _ $ erased next-arm : (erased (Nat) m) (erased (Nat) w) (erased (Nat) y) (erased (List (Nat)) rest2) (erased (List (Nat)) arm)
    (erased (Par m) pr) (erased (Drop (Nat) m (Cons _ w (Cons _ y rest2)) arm) dr) ->
    (erased (Nat) h) (erased (List (Nat)) arm2) (erased (Eq (List (Nat)) arm (Cons _ h arm2)) e) (erased (Drop (Nat) m (Cons _ y rest2) arm2) dr2)
  (match erased pr _
    ((PEven) (match erased dr _ ((DropZ a e1) (values w (Cons _ y rest2) (Refl _ arm) (DropZ _ (Cons _ y rest2))))))
    ((POdd)
      (match erased dr _
        ((DropS a k x xs e1 dr1)
          (match erased dr1 _
            ((DropZ a2 e2) (values y rest2 (Refl _ arm) (DropS _ _ y _ _ (DropZ _ rest2))))))))))

(def-fns _ $ erased par-e : (erased (Nat) m) (erased (Par m) pr) -> (erased (Nat) e) (erased (Add m e (Succ (Zero))) a)
  (match erased pr _
    ((PEven) (values (Succ (Zero)) (AddZero (Succ (Zero)))))
    ((POdd) (values (Zero) (AddSucc _ _ _ (AddZero (Zero)))))))

(def-fns _ $ erased agree-revonto-ex : (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) acc)
    (subterm erased (Agree p l r) ag) -> (erased (List (Nat)) s) (erased (RevOnto (Nat) p l acc s) rv)
  (match erased ag _
    ((AgreeZ a b) (values acc (RevZ _ l acc)))
    ((AgreeS k x xs ys ag0)
      (let (erased s) (erased rv) (agree-revonto-ex _ _ _ (Cons _ x acc) ag0))
      (values s (revonto-shift _ _ _ _ _ _ rv)))))

(def-fns _ $ erased add-lt-succ : (erased (Nat) d) (erased (Nat) k) (erased (Nat) p) (erased (Add d (Succ k) p) a) -> (erased (Lt d p) lt)
  (let (erased c1) (erased e) (erased a1) (add-succ-right-inv _ _ _ a))
  (let-match erased e (Refl t r))
  (add-le-left _ _ _ a1))

(def-fns _
  (many after-expand : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (many (Nat) w) (subterm many (List (Nat)) rest) (subterm erased (Nat) ph) (erased (Eq (Nat) ph (Succ (Succ (Zero)))) eph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m (Cons _ w rest) arm) dra) (erased (Zip (Nat) xs li (Cons _ w rest)) z)
      (many (Nat) p) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) p li lp) dlp) (erased (RevOnto (Nat) p li (Cons _ w rest) rp) rvp) (erased (Drop (Nat) p arm rd) drd)
      (erased (Agree p li arm) ag) (erased (Disagree (Succ p) li arm) dis)
      (many (Back m xs li (Cons _ w rest)) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best xs li (Cons _ w rest) acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m xs lend (Nil (Nat))) accend)
      (erased (Bound m best2 xs lend (Nil (Nat)) accend) bdend)
    (let-match erased eph (Refl t e0))
    (match many p _
          ((Zero)
            (tail (finish _ m pr _ w rest _ (Refl _ (Succ (Zero))) _ dra z p ag dis p lp rp rd dlp rvp drd
                    (Zero) (PZ) (Out m xs (Cons _ w li) rest) acc best has bd)))
          ((Succ p1)
            (match many p1 _
              ((Zero)
                (tail (finish _ m pr _ w rest _ (Refl _ (Succ (Zero))) _ dra z p ag dis p lp rp rd dlp rvp drd
                        p1 (PS p1) (Out m xs (Cons _ w li) rest) acc best has bd)))
              ((Succ p2)
                (match erased ag _
                  ((AgreeS k x lm ys ag0)
                    (let (erased e) (erased aem) (par-e _ pr))
                    (tail (finish _ m pr _ w rest _ (Refl _ (Succ (Zero))) _ dra z p ag dis p lp rp rd dlp rvp drd
                            p1 (PS p1)
                            (In _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                dra ag
                                (RevS _ _ _ _ _ _ (RevZ _ (Cons _ w rest) li) (NthHere _ w rest))
                                (DropS _ _ w _ _ (DropZ _ rest))
                                (AddSucc _ _ _ (AddZero p1)) aem
                                (DropS _ _ x _ _ (DropZ _ lm))
                                (RevS _ _ _ _ _ _ (RevZ _ li (Cons _ w rest)) (NthHere _ x lm))
                                acc)
                            acc best has bd)))))))))

  (many finish : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (many (Nat) w) (subterm many (List (Nat)) rest) (subterm erased (Nat) ph) (erased (Eq (Nat) ph (Succ (Zero))) eph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m (Cons _ w rest) arm) dra) (erased (Zip (Nat) xs li (Cons _ w rest)) z)
      (many (Nat) p) (erased (Agree p li arm) ag) (erased (Disagree (Succ p) li arm) dis)
      (many (Nat) ki) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) ki li lp) dlp) (erased (RevOnto (Nat) ki li (Cons _ w rest) rp) rvp) (erased (Drop (Nat) ki arm rd) drd)
      (many (Nat) qn) (erased (PredZ ki qn) pz) (many (Reach m xs (Cons _ w li) rest qn) reach)
      (many (Back m xs li (Cons _ w rest)) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best xs li (Cons _ w rest) acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m xs lend (Nil (Nat))) accend)
      (erased (Bound m best2 xs lend (Nil (Nat)) accend) bdend)
    (let (many pp) (erased dd) (double p))
    (let (many n) (erased an) (add pp m))
    (let (many best2) (erased has2) (erased le) (erased bd2)
      (match many (lt-dec best n) (((Nat) b2) ((HasPalindromeOfLength xs b2) h2) ((Lt n (Succ b2)) l2) ((Bound m b2 xs li (Cons _ w rest) acc) d2))
        ((Yes a b lt)
          (let (erased s) (erased rvs) (agree-revonto-ex _ _ _ (Cons _ w rest) ag))
          (values n (has-at-centre _ _ _ _ _ _ _ _ _ z pr dra ag rvs dd an) (lt-succ n)
                  (bound-weaken _ _ _ _ _ _ _ bd (lt-weaken _ _ lt))))
        ((No a b ge) (values best has ge bd))))
    (let (many acc2) (BackS _ _ _ _ _ p (MkCert _ _ _ _ _ dra ag dis) acc))
    (let (erased bd3) (BoundS _ _ _ _ _ _ _ (MkCert _ _ _ _ _ dra ag dis) _ _ _ dd an le bd2))
    (let (erased z2) (ZipS _ _ _ _ _ z))
    (let-match erased eph (Refl t e0))
    (match many rest _
          ((Nil a) (values best2 has2 (Cons _ w li) z2 acc2 bd3))
          ((Cons a y rest2)
            (let (erased h) (erased arm2) (erased earm) (erased dra2) (next-arm _ _ _ _ _ pr dra))
            (let-match erased earm (Refl t2 e2))
            (match many ki _
                  ((Zero)
                    (match erased pz _
                      ((PZ)
                        (match erased dlp _
                          ((DropZ a3 e3)
                            (match erased rvp _
                              ((RevZ a4 e4 e5)
                                (match erased drd _
                                  ((DropZ a5 e5b)
                                    (match many rd _
                                      ((Cons a6 h2 rd2)
                                        (tail (scan _ m pr _ rest (Zero) _ dra2 z2 (Zero) (Cons _ w lp) rest rd2
                                              (DropZ _ (Cons _ w li)) (RevZ _ (Cons _ w li) rest) (DropZ _ arm2)
                                              reach acc2 best2 has2 bd3)))))))))))))
                  ((Succ k1)
                    (match erased pz _
                      ((PS e6)
                        (match erased rvp _
                          ((RevS a7 e7 e8 e9 rp1 x1 rvp1 nx1)
                            (let (erased d0) (drop-unstep _ _ _ _ _ dlp nx1))
                            (match erased drd _
                              ((DropS a8 e10 e11 e12 e13 drd1)
                                (match many rp _
                                  ((Cons a9 x1b rp1b)
                                    (match many k1 _
                                      ((Zero)
                                        (match erased d0 _
                                          ((DropZ a10 e14)
                                            (match erased rvp1 _
                                              ((RevZ a11 e15 e16)
                                                (match many rp1b _
                                                  ((Cons a12 wb restb)
                                                    (tail (scan _ m pr _ rest (Zero) _ dra2 z2 (Zero) (Cons _ w (Cons _ x1b lp)) restb rd
                                                          (DropZ _ (Cons _ w li)) (RevZ _ (Cons _ w li) rest) drd1
                                                          reach acc2 best2 has2 bd3)))))))))
                                      ((Succ k2)
                                        (match erased rvp1 _
                                          ((RevS a13 e17 e18 e19 rp2 x2 rvp2 nx2)
                                            (match many rp1b _
                                              ((Cons a14 x2b rp2b)
                                                (tail (scan _ m pr _ rest (Zero) _ dra2 z2 k1 (Cons _ x2b (Cons _ x1b lp)) rp2b rd
                                                      (DropS _ _ w _ _ (drop-unstep _ _ _ _ _ d0 nx2))
                                                      (revonto-shift _ _ _ _ _ _ rvp2) drd1
                                                      reach acc2 best2 has2 bd3)))))))))))))))))))))

  (many scan : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (subterm many (List (Nat)) ri) (subterm erased (Nat) ph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m ri arm) dra) (erased (Zip (Nat) xs li ri) z)
      (many (Nat) q) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) q li lp) dlp) (erased (RevOnto (Nat) q li ri rp) rvp) (erased (Drop (Nat) q arm rd) drd)
      (many (Reach m xs li ri q) reach) (many (Back m xs li ri) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best xs li ri acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m xs lend (Nil (Nat))) accend)
      (erased (Bound m best2 xs lend (Nil (Nat)) accend) bdend)
    (match many ri _
      ((Nil a) (values best has li z acc bd))
      ((Cons a w rest)
        (match many reach _
          ((Out e1 e1b e2 e3)
            (let (many p) (many lp2) (many rp2) (many rd2) (erased dl2) (erased rv2) (erased dr2) (erased ag2) (erased dis2)
              (expand q lp rp rd _ _ _ dlp rvp drd (AgreeZ li arm)))
            (tail (after-expand _ m pr _ w rest _ (Refl _ (Succ (Succ (Zero)))) _ dra z p lp2 rp2 rd2 dl2 rv2 dr2 ag2 dis2 acc best has bd)))
          ((In e1 e1b e2 e3 q1 lc wc armc pc d e x lm rm1 drc agc rvl drr aq aem dlm rvm mp)
            (match many mp _
              ((BackS e4 e4b e5 e6 e7 p2 c mp2)
                (let-match erased c (MkCert e8 e9 e10 e11 armm dram agm dism))
                (let (erased midc) (erased mdc) (erased cmc) (mid-of _ _ _ pr drc))
                (let (erased rvarm) (revonto-drop-mid _ _ _ _ _ _ _ _ mdc aem rvm dram))
                (let (erased x1) (mirror-agree _ _ _ _ _ _ _ _ _ _ _ agc mdc cmc rvarm aem rvl aq))
                (let (erased x2) (agree-drop _ _ _ _ _ _ _ dlm (drop-swap _ _ _ _ _ _ drr dra drc) aq agc))
                (match many (lt-dec p2 q) _
                  ((Yes a1 b1 lt)
                    (let (erased agi) (erased disi) (mirror-cert _ _ _ _ _ _ x1 x2 agm dism lt))
                    (let (erased nw) (erased drr2) (drop-nth _ _ _ _ _ drr))
                    (let (erased rvl2) (RevS _ _ _ _ _ _ rvl nw))
                    (match many q _
                      ((Succ q1b)
                        (match many q1b _
                          ((Zero)
                            (tail (finish _ m pr _ w rest _ (Refl _ (Succ (Zero))) _ dra z p2 agi disi q lp rp rd dlp rvp drd
                                    q1b (PS q1b) (Out m xs (Cons _ w li) rest) acc best has bd)))
                          ((Succ q2)
                            (let (erased x3) (erased lm2) (erased elm) (agree-drop-cons _ _ _ _ _ agc dlm (add-lt-succ _ _ _ aq)))
                            (let-match erased elm (Refl t3 e3b))
                            (let (erased nx3) (erased dlm2) (drop-nth _ _ _ _ _ dlm))
                                (let (erased c1) (erased epc) (erased aq1) (add-succ-right-inv _ _ _ aq))
                                (let-match erased epc (Refl t4 e4b))
                                (tail (finish _ m pr _ w rest _ (Refl _ (Succ (Zero))) _ dra z p2 agi disi q lp rp rd dlp rvp drd
                                            q1b (PS q1b)
                                            (In _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                drc agc rvl2 drr2 (AddSucc _ _ _ aq1) (add-succ-right _ _ _ aem) dlm2
                                                (RevS _ _ _ _ _ _ rvm nx3) mp2)
                                            acc best has bd)))))))
                  ((No a1 b1 ge)
                    (let (erased agq) (agree-trans _ _ _ _ x1 (agree-trans _ _ _ _ (agree-sym _ _ _ (agree-weaken-to _ _ _ _ agm ge)) x2)))
                    (let (many p) (many lp2) (many rp2) (many rd2) (erased dl2) (erased rv2) (erased dr2) (erased ag2) (erased dis2)
                      (expand q lp rp rd _ _ _ dlp rvp drd agq))
                    (tail (after-expand _ m pr _ w rest _ (Refl _ (Succ (Succ (Zero)))) _ dra z p lp2 rp2 rd2 dl2 rv2 dr2 ag2 dis2 acc best has bd))))))))))))


; --- from the certificates to NoLargerPalindromeF ---
; FwdB is the certificate chain read forwards from a zipper, every window it certifies no longer than b.

(def-adts
  (FwdB : ((Nat) m) ((Nat) b) ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many FwdNil : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) l) -> (FwdB m b l (Nil (Nat))))
    (many FwdCons : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) l) (erased (Nat) x) (erased (List (Nat)) r) (erased (Nat) p)
        (erased (Nat) pp) (erased (Nat) n)
        (erased (Cert m l (Cons _ x r) p) c) (erased (Double p pp) dd) (erased (Add pp m n) an) (erased (Lt n (Succ b)) le)
        (erased (FwdB m b (Cons _ x l) r) rest) -> (FwdB m b l (Cons _ x r)))))

(def-fns _ $ erased back-fwd : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Back m xs l r) bk) (subterm erased (Bound m b xs l r bk) bd) (erased (FwdB m b l r) fwd) -> (erased (FwdB m b (Nil (Nat)) xs) fwd2)
  (match erased bd _
    ((BoundZ a e e2) fwd)
    ((BoundS a e e2 l0 x r0 p c rest pp n dd an le bd1)
      (back-fwd _ _ _ _ _ _ bd1 (FwdCons _ _ _ _ _ _ _ _ c dd an le fwd)))))

(def-fns _ $ erased revonto-unshift : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A y) (erased (List A) acc) (erased (List A) res)
    (subterm erased (RevOnto A (Succ k) (Cons _ y xs) acc res) p) -> (erased (RevOnto A k xs (Cons _ y acc) res) q)
  (match erased p _
    ((RevS a k1 e1 e2 res0 x p1 n)
      (match erased n _
        ((NthHere a2 e3 e4) (match erased p1 _ ((RevZ a3 e5 e6) (RevZ _ xs (Cons _ y acc)))))
        ((NthThere a2 i2 y2 r2 e3 n1) (RevS _ _ _ _ _ _ (revonto-unshift _ _ _ _ _ _ p1) n1))))))

(def-fns _ $ erased fwd-at : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (Nat) k)
    (erased (List (Nat)) lk) (erased (Nat) x) (erased (List (Nat)) rk)
    (subterm erased (FwdB m b l r) fwd) (erased (RevOnto (Nat) k r l lk) rv) (erased (Drop (Nat) k r (Cons _ x rk)) dr) ->
    (erased (Nat) p) (erased (Nat) pp) (erased (Nat) n)
    (erased (Cert m lk (Cons _ x rk) p) c) (erased (Double p pp) dd) (erased (Add pp m n) an) (erased (Lt n (Succ b)) le)
  (match erased dr _
    ((DropZ a e)
      (match erased rv _
        ((RevZ a2 e2 e3)
          (match erased fwd _
            ((FwdCons e4 e5 e6 x2 r2 p pp n c dd an le rest) (values p pp n c dd an le))))))
    ((DropS a k1 x0 r1 e dr1)
      (match erased fwd _
        ((FwdCons e4 e5 e6 x2 r2 p2 pp2 n2 c2 dd2 an2 le2 rest)
          (fwd-at _ _ _ _ _ _ _ _ rest (revonto-unshift _ _ _ _ _ _ rv) dr1))))))

(def-fns _ $ erased take-drop-ex : (erased Type A) (erased (Nat) n) (erased (List A) s) (erased (List A) w) (erased (Nat) k)
    (subterm erased (Take A n s w) t) (erased (Lt k (Succ n)) le) -> (erased (List A) d) (erased (Drop A k s d) dr)
  (match erased t _
    ((TakeZero a e) (match erased le _ ((LtZ b) (values s (DropZ _ s))) ((LtS a2 b2 l2) (match erased l2 _))))
    ((TakeSucc a n1 x s1 w1 t1)
      (match erased k _
        ((Zero) (values s (DropZ _ s)))
        ((Succ k1)
          (match erased le _
            ((LtS a2 b2 l2)
              (let (erased d) (erased dr) (take-drop-ex _ _ _ _ _ t1 l2))
              (values d (DropS _ _ x _ _ dr)))))))))

(def-fns _ $ erased drop-revonto-ex : (erased Type A) (erased (Nat) k) (erased (List A) s) (erased (List A) d) (erased (List A) acc)
    (subterm erased (Drop A k s d) dr) -> (erased (List A) l) (erased (RevOnto A k s acc l) rv)
  (match erased dr _
    ((DropZ a e) (values acc (RevZ _ s acc)))
    ((DropS a k1 x s1 e dr1)
      (let (erased l) (erased rv) (drop-revonto-ex _ _ _ _ (Cons _ x acc) dr1))
      (values l (revonto-shift _ _ _ _ _ _ rv)))))

(def-fns _ $ erased drop-succ-split : (erased Type A) (erased (Nat) k) (erased (List A) s) (erased (List A) d)
    (subterm erased (Drop A (Succ k) s d) dr) -> (erased A y) (erased (Drop A k s (Cons _ y d)) dr2)
  (match erased dr _
    ((DropS a k1 x s1 e dr1)
      (match erased k _
        ((Zero) (match erased dr1 _ ((DropZ a2 e2) (values x (DropZ _ s)))))
        ((Succ k2)
          (let (erased y) (erased dr2) (drop-succ-split _ _ _ _ dr1))
          (values y (DropS _ _ x _ _ dr2)))))))

(def-fns _ $ erased walk-inverse : (erased Type A) (erased (Nat) k) (erased (List A) rj) (erased (List A) lj) (erased (List A) li) (erased (List A) ri)
    (subterm erased (RevOnto A k rj lj li) rv) (erased (Drop A k rj ri) dr) -> (erased (RevOnto A k li ri rj) rv2)
  (match erased rv _
    ((RevZ a e1 e2) (match erased dr _ ((DropZ a2 e3) (RevZ _ lj rj))))
    ((RevS a k1 e1 e2 li0 x rv1 n)
      (revonto-shift _ _ _ _ _ _ (walk-inverse _ _ _ _ _ _ rv1 (drop-unstep _ _ _ _ _ dr n))))))

(def-fns _ $ erased length-ex : (erased Type A) (subterm erased (List A) l) -> (erased (Nat) n) (erased (Length A l n) len)
  (match erased l _
    ((Nil a) (values (Zero) (LNil A)))
    ((Cons a x rest)
      (let (erased n) (erased len) (length-ex _ rest))
      (values (Succ n) (LCons A x rest n len)))))

(def-fns _ $ erased revonto-length : (erased Type A) (erased (Nat) t) (erased (List A) s) (erased (List A) acc) (erased (List A) res)
    (erased (Nat) la) (erased (Nat) lr)
    (subterm erased (RevOnto A t s acc res) rv) (erased (Length A acc la) len) (erased (Add t la lr) ad) -> (erased (Length A res lr) len2)
  (match erased rv _
    ((RevZ a e1 e2) (match erased ad _ ((AddZero b) len)))
    ((RevS a t1 e1 e2 res0 x rv1 n)
      (match erased ad _
        ((AddSucc a2 b2 lr0 ad1) (LCons A x res0 lr0 (revonto-length _ _ _ _ _ _ _ rv1 len ad1)))))))

(def-fns _ $ erased nth-ex : (erased Type A) (erased (List A) l) (erased (Nat) len) (erased (Nat) k)
    (subterm erased (Length A l len) ln) (erased (Lt k len) lt) -> (erased A x) (erased (Nth A k l x) n)
  (match erased ln _
    ((LNil a) (match erased lt _))
    ((LCons a x rest n1 ln1)
      (match erased k _
        ((Zero) (values x (NthHere _ x rest)))
        ((Succ k1)
          (match erased lt _
            ((LtS a2 b2 lt1)
              (let (erased y) (erased n) (nth-ex _ _ _ _ ln1 lt1))
              (values y (NthThere _ _ x _ _ n)))))))))

(def-fns _ $ erased win-total : (subterm erased (Nat) k) (erased (List (Nat)) li) (erased (List (Nat)) mid) (erased (List (Nat)) arm) (erased (List (Nat)) d)
    (erased (Nat) len) (erased (Length (Nat) li len) ln) (erased (Lt k (Succ len)) le) (erased (Drop (Nat) k arm d) dr) ->
    (erased (List (Nat)) w) (erased (Win k li mid arm w) win)
  (match erased k _
    ((Zero) (values mid (WinZ li mid arm)))
    ((Succ k1)
      (match erased le _
        ((LtS a b lt1)
          (let (erased x) (erased nx) (nth-ex _ _ _ _ ln lt1))
          (let (erased y) (erased dr1) (drop-succ-split _ _ _ _ dr))
          (let (erased ny) (erased dr2) (drop-nth _ _ _ _ _ dr1))
          (let (erased w0) (erased win0) (win-total _ _ mid _ _ _ ln (lt-weaken _ _ lt1) dr1))
          (let (erased wy) (erased q) (concat-total _ w0 (Cons _ y (Nil (Nat)))))
          (values (Cons _ x wy) (WinS _ _ _ _ _ _ _ _ win0 nx ny q)))))))

(def-fns _ $ erased double-add : (erased (Nat) a) (erased (Nat) b) (subterm erased (Double a b) d) -> (erased (Add a a b) p)
  (match erased d _
    ((D0) (AddZero (Zero)))
    ((DS a1 b1 d1) (AddSucc _ _ _ (add-succ-right _ _ _ (double-add _ _ d1))))))

(def-fns _ $ erased add-fn : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c1) (erased (Nat) c2)
    (subterm erased (Add a b c1) p) (erased (Add a b c2) q) -> (erased (Eq (Nat) c1 c2) e)
  (match erased p _
    ((AddZero b1) (match erased q _ ((AddZero b2) (Refl _ c1))))
    ((AddSucc a1 b1 c p1) (match erased q _ ((AddSucc a2 b2 c0 q1) (let-match erased (add-fn _ _ _ _ p1 q1) (Refl t e))
                                                                   (Refl _ c1))))))

(def-fns _ $ erased add-assoc : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) ab) (erased (Nat) abc) (erased (Nat) bc)
    (subterm erased (Add a b ab) p) (erased (Add ab c abc) q) (erased (Add b c bc) r) -> (erased (Add a bc abc) s)
  (match erased p _
    ((AddZero b1) (let-match erased (add-fn _ _ _ _ q r) (Refl t e))
                  (AddZero bc))
    ((AddSucc a1 b1 c1 p1)
      (match erased q _
        ((AddSucc a2 b2 c2 q1) (AddSucc _ _ _ (add-assoc _ _ _ _ _ _ p1 q1 r)))))))

(def-fns _ $ erased add-cancel-lt : (erased (Nat) m) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Nat) c2)
    (subterm erased (Add m a c) p) (erased (Add m b c2) q) (erased (Lt c c2) lt) -> (erased (Lt a b) lt2)
  (match erased p _
    ((AddZero b1) (match erased q _ ((AddZero b2) lt)))
    ((AddSucc a1 b1 c1 p1)
      (match erased q _
        ((AddSucc a2 b2 c3 q1) (match erased lt _ ((LtS x y lt1) (add-cancel-lt _ _ _ _ _ p1 q1 lt1))))))))

(def-fns _ $ erased double-lt-inv : (erased (Nat) p) (erased (Nat) pp) (erased (Nat) k) (erased (Nat) kk)
    (subterm erased (Double p pp) dp) (erased (Double k kk) dk) (erased (Lt pp kk) lt) -> (erased (Lt p k) lt2)
  (match erased dp _
    ((D0) (match erased dk _ ((D0) (match erased lt _)) ((DS a b d) (LtZ a))))
    ((DS a1 b1 d1)
      (match erased dk _
        ((D0) (match erased lt _))
        ((DS a2 b2 d2)
          (match erased lt _
            ((LtS x y lt1) (match erased lt1 _ ((LtS x2 y2 lt2) (LtS _ _ (double-lt-inv _ _ _ _ d1 d2 lt2)))))))))))

(def-fns _ $ erased double-le : (subterm erased (Nat) k) (erased (Nat) kk) (erased (Double k kk) d) -> (erased (Lt k (Succ kk)) lt)
  (match erased d _
    ((D0) (LtZ (Zero)))
    ((DS a b d1) (LtS _ _ (lt-weaken _ _ (double-le _ _ d1))))))

(def-fns _ $ erased radius-lt : (erased (Nat) k) (erased (Nat) kk) (erased (Nat) n1) (erased (Nat) m)
    (erased (Double k kk) dk) (erased (Add kk m (Succ n1)) an) -> (erased (Lt k (Succ n1)) lt)
  (match erased dk _
    ((D0) (LtZ n1))
    ((DS k1 kk1 dk1) (lt-le-trans _ _ _ (LtS _ _ (double-le _ _ dk1)) (add-le-left _ _ _ an)))))

(def-fns _ $ erased slide : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Nat) k) (erased (Nat) kk) (erased (Nat) n2)
    (erased (Par m) pr) (subterm erased (FwdB m b l r) fwd) (erased (Double k kk) dk) (erased (Add kk m n2) an) (erased (Lt b n2) ltb) ->
    (erased (NoPalindromeOfLengthF r n2) np)
  (match erased (take-dec _ n2 r) _
    ((TooShort a e1 e2 len ln short) (SlideShort r n2 len ln short))
    ((Took a e1 e2 w tk)
      (match erased n2 _
        ((Zero) (match erased ltb _))
        ((Succ n1)
          (match erased tk _
            ((TakeSucc a2 e3 x0 r1 w1 tk1)
              (match erased fwd _
                ((FwdCons e4 e5 e6 e7 e8 p0 pp0 nn0 c0 dd0 an0 le0 rest)
                  (let (erased ltk) (radius-lt _ _ _ _ dk an))
                  (let (erased d1) (erased drd1) (take-drop-ex _ _ _ _ _ tk (LtS _ _ ltk)))
                  (let (erased x) (erased drk) (drop-succ-split _ _ _ _ drd1))
                  (let (erased lk) (erased rvk) (drop-revonto-ex _ _ _ _ l drk))
                  (let (erased p) (erased pp) (erased n) (erased c) (erased dd) (erased ann) (erased le) (fwd-at _ _ _ _ _ _ _ _ fwd rvk drk))
                  (let-match erased c (MkCert e9 e10 e11 e12 arm dram ag dis))
                  (let (erased mid) (erased md) (erased cm) (mid-of _ _ _ pr dram))
                  (let (erased la) (erased lna) (length-ex _ l))
                  (let (erased lkl) (erased akl) (add k la))
                  (let (erased lnk) (revonto-length _ _ _ _ _ _ _ rvk lna akl))
                  (let (erased km) (erased akm) (add k m))
                  (let (erased dn) (erased drn) (take-drop-ex _ _ _ _ _ tk (lt-succ n2)))
                  (let (erased y1) (erased dry1) (erased dry2) (drop-split _ _ _ _ _ _ drn (add-assoc _ _ _ _ _ _ (double-add _ _ dk) an akm)))
                  (let-match erased (drop-fn _ _ _ _ _ dry1 drk) (Refl t1 er1))
                  (let (erased y2) (erased dry3) (erased dry4) (drop-split _ _ _ _ _ _ dry2 (add-comm _ _ _ akm)))
                      (let-match erased (drop-fn _ _ _ _ _ dry3 dram) (Refl t2 er2))
                      (let (erased w2) (erased win) (win-total _ _ mid _ _ _ lnk (add-le-left _ _ _ akl) dry4))
                          (let (erased pre) (win-prefix _ _ _ _ _ _ _ _ win cm (walk-inverse _ _ _ _ _ _ rvk drk) dry4))
                          (let (erased lw) (win-length _ _ _ _ _ _ _ _ win (mid-length _ _ md) dk an))
                          (let-match erased (take-fn _ _ _ _ _ tk (concat-take _ _ _ _ _ pre lw)) (Refl t3 er3))
                          (let (erased ltn) (lt-le-trans _ _ _ le (LtS _ _ ltb)))
                              (let (erased ltp) (double-lt-inv _ _ _ _ dd dk (add-cancel-lt _ _ _ _ _ (add-comm _ _ _ ann) (add-comm _ _ _ an) ltn)))
                              (SlideStep n2 x0 r1 w tk (win-notpal _ _ _ _ _ _ win ag dis ltp)
                                (slide _ _ _ _ _ _ _ pr rest dk an ltb)))))))))))

(def-fns _ $ erased split-parity : (subterm erased (Nat) n) ->
    (erased (Nat) k) (erased (Nat) kk) (erased (Nat) m) (erased (Double k kk) dd) (erased (Add kk m n) an) (erased (Par m) pr)
  (match erased n _
    ((Zero) (values (Zero) (Zero) (Zero) (D0) (AddZero (Zero)) (PEven)))
    ((Succ n1)
      (match erased n1 _
        ((Zero) (values (Zero) (Zero) (Succ (Zero)) (D0) (AddZero (Succ (Zero))) (POdd)))
        ((Succ n2)
          (let (erased k) (erased kk) (erased m) (erased dd) (erased an) (erased pr) (split-parity n2))
          (values (Succ k) (Succ (Succ kk)) m (DS _ _ dd) (AddSucc _ _ _ (AddSucc _ _ _ an)) pr))))))

(def-fns _ $ erased nolarger-from : (erased (List (Nat)) xs) (erased (Nat) b0) (erased (Nat) b1) (erased (Nat) best) (erased (Nat) len)
    (erased (FwdB (Zero) b0 (Nil (Nat)) xs) fwd0) (erased (FwdB (Succ (Zero)) b1 (Nil (Nat)) xs) fwd1)
    (erased (Lt b0 (Succ best)) le0) (erased (Lt b1 (Succ best)) le1) (erased (Length (Nat) xs len) ln)
    (erased (Nat) n) (subterm erased (Nat) d) (erased (Add n d len) ad) (erased (Lt best (Succ n)) lbn) -> (erased (NoLargerPalindromeF xs n) nl)
  (match erased d _
    ((Zero) (let-match erased (add-fn _ _ _ _ (add-zero-right n) ad) (Refl t e))
            (NoLargerDoneF xs n len ln (lt-succ len)))
    ((Succ d1)
      (let (erased c1) (erased e) (erased ad1) (add-succ-right-inv _ _ _ ad))
      (let-match erased e (Refl t e2))
      (let (erased k) (erased kk) (erased m) (erased dk) (erased an) (erased pr) (split-parity (Succ n)))
          (let (erased here)
            (match erased pr (((NoPalindromeOfLengthF xs (Succ n)) h))
              ((PEven) (slide _ _ _ _ _ _ _ pr fwd0 dk an (lt-le-trans _ _ _ le0 (LtS _ _ lbn))))
              ((POdd) (slide _ _ _ _ _ _ _ pr fwd1 dk an (lt-le-trans _ _ _ le1 (LtS _ _ lbn))))))
          (NoLargerStepF xs n here (nolarger-from _ _ _ _ _ fwd0 fwd1 le0 le1 ln _ _ (AddSucc _ _ _ ad1) (lt-weaken _ _ lbn))))))


(def-fns _ $ many manacher-par : (many (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) ->
    (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend)
    (many (Back m xs lend (Nil (Nat))) acc) (erased (Bound m best xs lend (Nil (Nat)) acc) bd)
  (let (erased has0) (HasHere xs (Zero) (Nil (Nat)) (TakeZero (Nat) xs) (PalNil (Nat))))
  (match many xs _
    ((Nil a) (values (Zero) has0 (Nil (Nat)) (ZipZ _ xs) (BackZ m xs) (BoundZ m (Zero) xs)))
    ((Cons a x xs1)
      (match many m _
        ((Zero)
          (tail (scan _ m pr _ xs (Zero) _ (DropZ _ xs) (ZipZ _ xs) (Zero) (Nil (Nat)) xs xs
                (DropZ _ (Nil (Nat))) (RevZ _ (Nil (Nat)) xs) (DropZ _ xs) (Out m xs (Nil (Nat)) xs) (BackZ m xs) (Zero) has0 (BoundZ m (Zero) xs))))
        ((Succ m1)
          (match erased pr _
            ((POdd)
              (tail (scan _ m pr _ xs (Zero) _ (DropS _ _ x _ _ (DropZ _ xs1)) (ZipZ _ xs) (Zero) (Nil (Nat)) xs xs1
                    (DropZ _ (Nil (Nat))) (RevZ _ (Nil (Nat)) xs) (DropZ _ xs1) (Out m xs (Nil (Nat)) xs) (BackZ m xs) (Zero) has0 (BoundZ m (Zero) xs))))))))))

(def-fns _ $ many manacher : (many (List (Nat)) xs) -> (many (Nat) best) (erased (LongestPalindromeF xs best) p)
  (let (many b0) (erased h0) (erased le0) (erased z0) (many acc0) (erased bd0) (manacher-par xs (Zero) (PEven)))
  (let (many b1) (erased h1) (erased le1) (erased z1) (many acc1) (erased bd1) (manacher-par xs (Succ (Zero)) (POdd)))
  (let (erased fwd0) (back-fwd _ _ _ _ _ _ bd0 (FwdNil (Zero) b0 le0)))
  (let (erased fwd1) (back-fwd _ _ _ _ _ _ bd1 (FwdNil (Succ (Zero)) b1 le1)))
  (let (many best) (erased has) (erased lt0) (erased lt1)
    (match many (lt-dec b0 b1) (((Nat) b) ((HasPalindromeOfLength xs b) h) ((Lt b0 (Succ b)) l0) ((Lt b1 (Succ b)) l1))
      ((Yes a c lt) (values b1 h1 (lt-weaken _ _ lt) (lt-succ b1)))
      ((No a c ge) (values b0 h0 (lt-succ b0) ge))))
  (let (many len) (erased ln) (list-length _ xs))
  (let (erased d) (erased ad)
    (match many (lt-dec len best) (((Nat) d) ((Add best d len) a))
      (absurd (Yes a c lt) (has-not-short _ _ _ has ln lt))
      ((No a c ge) (sub len best ge))))
  (values best (IsLongestF xs best has (nolarger-from _ _ _ _ _ fwd0 fwd1 lt0 lt1 ln _ _ ad (lt-succ best)))))

(def-fns _ $ many longest-palindrome-linear : (many (List (Nat)) xs) -> (many (Nat) n) (erased (LongestPalindrome xs n) q)
  (let (many n) (erased p) (manacher xs))
  (values n (longest-bridge _ _ p)))

(let (many n0) (erased q0) (longest-palindrome-linear (Nil (Nat))))
(let (many n1) (erased q1) (longest-palindrome-linear (Cons _ 7 $ Nil (Nat))))
(let (many n2) (erased q2) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Nil (Nat))))
(let (many n3) (erased q3) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 2 $ Cons _ 1 $ Cons _ 4 $ Nil (Nat))))
(let (many n4) (erased q4) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Cons _ 1 $ Nil (Nat))))
(let (many n5) (erased q5) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons _ 5 $ Nil (Nat))))
(let (many n6) (erased q6) (longest-palindrome-linear (Cons _ 3 $ Cons _ 1 $ Cons _ 1 $ Cons _ 3 $ Cons _ 1 $ Cons _ 1 $ Nil (Nat))))
(let (many n7) (erased q7) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Cons _ 3 $ Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Nil (Nat))))
(let (many n8) (erased q8) (longest-palindrome-linear (Cons _ 1 $ Cons _ 1 $ Cons _ 1 $ Cons _ 1 $ Nil (Nat))))
(let (many n9) (erased q9) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Cons _ 2 $ Nil (Nat))))
(let (many n10) (erased q10) (longest-palindrome-linear (Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Cons _ 1 $ Cons _ 2 $ Cons _ 1 $ Nil (Nat))))
(let (many n11) (erased q11) (longest-palindrome-linear (Cons _ 4 $ Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Cons _ 1 $ Cons _ 4 $ Cons _ 1 $ Cons _ 2 $ Cons _ 2 $ Cons _ 1 $ Cons _ 4 $ Cons _ 7 $ Cons _ 7 $ Nil (Nat))))

(Cons _ n0 $ Cons _ n1 $ Cons _ n2 $ Cons _ n3 $ Cons _ n4 $ Cons _ n5 $ Cons _ n6 $ Cons _ n7 $ Cons _ n8 $ Cons _ n9 $ Cons _ n10 $ Cons _ n11 $ Nil (Nat))
