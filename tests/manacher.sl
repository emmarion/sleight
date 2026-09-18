; needs: palindrome_relations
; expect: (Cons 0 (Cons 1 (Cons 1 (Cons 5 (Cons 4 (Cons 1 (Cons 5 (Nil))))))))
; Manacher's algorithm over a List (Nat), with lists alone (two zippers and a
; suffix of the radius list stand in for the arrays), returning the spec's
; LongestPalindrome proof of palindrome_relations.sl. Written by a Claude
; session; the checker, not this comment, is the evidence that it is right.

; --- list relations ---

(def-adts
  (Nth : (Type A) ((Nat) i) ((List A) xs) (A x) -> Type
    enum
    (many NthHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Nth A (Zero) (Cons A x rest) x))
    (many NthThere : (erased Type A) (erased (Nat) i) (erased A y) (erased (List A) rest) (erased A x)
        (erased (Nth A i rest x) p) -> (Nth A (Succ i) (Cons A y rest) x)))
  (Drop : (Type A) ((Nat) k) ((List A) xs) ((List A) ys) -> Type
    enum
    (many DropZ : (erased Type A) (erased (List A) xs) -> (Drop A (Zero) xs xs))
    (many DropS : (erased Type A) (erased (Nat) k) (erased A x) (erased (List A) xs) (erased (List A) ys)
        (erased (Drop A k xs ys) p) -> (Drop A (Succ k) (Cons A x xs) ys)))
  (RevOnto : (Type A) ((Nat) k) ((List A) xs) ((List A) acc) ((List A) res) -> Type
    enum
    (many RevZ : (erased Type A) (erased (List A) xs) (erased (List A) acc) -> (RevOnto A (Zero) xs acc acc))
    (many RevS : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) acc) (erased (List A) res)
        (erased A x) (erased (RevOnto A k xs acc res) p) (erased (Nth A k xs x) n) ->
       (RevOnto A (Succ k) xs acc (Cons A x res))))
  (Zip : (Type A) ((List A) xs) ((List A) l) ((List A) r) -> Type
    enum
    (many ZipZ : (erased Type A) (erased (List A) xs) -> (Zip A xs (Nil A) xs))
    (many ZipS : (erased Type A) (erased (List A) xs) (erased (List A) l) (erased A x) (erased (List A) r)
        (erased (Zip A xs l (Cons A x r)) p) -> (Zip A xs (Cons A x l) r))))

; --- the two arms of a centre agree on their first k elements, or not ---

(def-adts
  (Agree : ((Nat) k) ((List (Nat)) xs) ((List (Nat)) ys) -> Type
    enum
    (many AgreeZ : (erased (List (Nat)) xs) (erased (List (Nat)) ys) -> (Agree (Zero) xs ys))
    (many AgreeS : (erased (Nat) k) (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Agree k xs ys) p) -> (Agree (Succ k) (Cons (Nat) x xs) (Cons (Nat) x ys))))
  (Disagree : ((Nat) k) ((List (Nat)) xs) ((List (Nat)) ys) -> Type
    enum
    (many DisNilL : (erased (Nat) k) (erased (List (Nat)) ys) -> (Disagree (Succ k) (Nil (Nat)) ys))
    (many DisNilR : (erased (Nat) k) (erased (List (Nat)) xs) -> (Disagree (Succ k) xs (Nil (Nat))))
    (many DisHead : (erased (Nat) k) (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (NatApart x y) d) -> (Disagree (Succ k) (Cons (Nat) x xs) (Cons (Nat) y ys)))
    (many DisTail : (erased (Nat) k) (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
        (erased (Disagree k xs ys) p) -> (Disagree (Succ k) (Cons (Nat) x xs) (Cons (Nat) x ys)))))

; --- the middle of a centre: nothing, or one element ---

(def-adts
  (Mid : ((Nat) m) ((List (Nat)) mid) -> Type
    enum
    (many MidEven : -> (Mid (Zero) (Nil (Nat))))
    (many MidOdd : (erased (Nat) z) -> (Mid (Succ (Zero)) (Cons (Nat) z (Nil (Nat)))))))

; --- the window of radius k around a centre, onion style, deepest pair outermost ---

(def-adts
  (Win : ((Nat) k) ((List (Nat)) l) ((List (Nat)) mid) ((List (Nat)) r) ((List (Nat)) w) -> Type
    enum
    (many WinZ : (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) -> (Win (Zero) l mid r mid))
    (many WinS : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r)
        (erased (List (Nat)) w) (erased (Nat) x) (erased (Nat) y) (erased (List (Nat)) wy)
        (erased (Win k l mid r w) p) (erased (Nth (Nat) k l x) nx) (erased (Nth (Nat) k r y) ny)
        (erased (Concat (Nat) w (Cons (Nat) y (Nil (Nat))) wy) q) ->
       (Win (Succ k) l mid r (Cons (Nat) x wy)))))

; --- small lemmas ---

(def-fns _ $ erased agree-weaken : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree (Succ k) xs ys) p) -> (erased (Agree k xs ys) q)
  (match erased p _
    ((AgreeS k0 x xs0 ys0 p0)
      (match erased p0 _
        ((AgreeZ a b) (AgreeZ xs ys))
        ((AgreeS k1 x1 xs1 ys1 p1) (AgreeS k1 x xs0 ys0 (agree-weaken k1 xs0 ys0 p0)))))))

(def-fns _ $ erased agree-sym : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) -> (erased (Agree k ys xs) q)
  (match erased p _
    ((AgreeZ a b) (AgreeZ ys xs))
    ((AgreeS k0 x xs0 ys0 p0) (AgreeS k0 x ys0 xs0 (agree-sym k0 xs0 ys0 p0)))))

(def-fns _ $ erased agree-trans : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (List (Nat)) zs)
    (subterm erased (Agree k xs ys) p) (erased (Agree k ys zs) q) -> (erased (Agree k xs zs) r)
  (match erased p _
    ((AgreeZ a b) (AgreeZ xs zs))
    ((AgreeS k0 x xs0 ys0 p0)
      (match erased q _
        ((AgreeS k1 x1 ys1 zs0 q0) (AgreeS k0 x xs0 zs0 (agree-trans k0 xs0 ys0 zs0 p0 q0)))))))

(def-fns _ $ erased agree-nth : (erased (Nat) i) (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x)
    (subterm erased (Agree k xs ys) p) (erased (Lt i k) lt) (erased (Nth (Nat) i xs x) n) -> (erased (Nth (Nat) i ys x) n2)
  (match erased p _
    ((AgreeZ a b) (match erased lt _))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased n _
        ((NthHere a e r) (NthHere (Nat) x ys0))
        ((NthThere a i1 y r e n1)
          (match erased lt _
            ((LtS l1 l2 lt1) (NthThere (Nat) i1 x0 ys0 x (agree-nth i1 k0 xs0 ys0 x p0 lt1 n1)))))))))

(def-fns _ $ erased agree-snoc : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x)
    (subterm erased (Agree k xs ys) p) (erased (Nth (Nat) k xs x) nx) (erased (Nth (Nat) k ys x) ny) -> (erased (Agree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b)
      (match erased nx _
        ((NthHere a1 e1 r1) (match erased ny _ ((NthHere a2 e2 r2) (AgreeS (Zero) x r1 r2 (AgreeZ r1 r2)))))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased nx _
        ((NthThere a1 i1 y1 r1 e1 n1)
          (match erased ny _
            ((NthThere a2 i2 y2 r2 e2 n2) (AgreeS (Succ k0) x0 xs0 ys0 (agree-snoc k0 xs0 ys0 x p0 n1 n2)))))))))

(def-fns _ $ erased disagree-at : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys) (erased (Nat) x) (erased (Nat) y)
    (subterm erased (Agree k xs ys) p) (erased (Nth (Nat) k xs x) nx) (erased (Nth (Nat) k ys y) ny) (erased (NatApart x y) d) ->
    (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b)
      (match erased nx _
        ((NthHere a1 e1 r1) (match erased ny _ ((NthHere a2 e2 r2) (DisHead (Zero) x y r1 r2 d))))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased nx _
        ((NthThere a1 i1 y1 r1 e1 n1)
          (match erased ny _
            ((NthThere a2 i2 y2 r2 e2 n2) (DisTail (Succ k0) x0 xs0 ys0 (disagree-at k0 xs0 ys0 x y p0 n1 n2 d)))))))))

(def-fns _ $ erased disagree-short : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Drop (Nat) k xs (Nil (Nat))) dr) -> (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b) (match erased dr _ ((DropZ a1 e1) (DisNilL (Zero) ys))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased dr _
        ((DropS a1 k1 x1 xs1 ys1 dr1) (DisTail (Succ k0) x0 xs0 ys0 (disagree-short k0 xs0 ys0 p0 dr1)))))))

(def-fns _ $ erased disagree-short-r : (erased (Nat) k) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Drop (Nat) k ys (Nil (Nat))) dr) -> (erased (Disagree (Succ k) xs ys) q)
  (match erased p _
    ((AgreeZ a b) (match erased dr _ ((DropZ a1 e1) (DisNilR (Zero) xs))))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased dr _
        ((DropS a1 k1 x1 xs1 ys1 dr1) (DisTail (Succ k0) x0 xs0 ys0 (disagree-short-r k0 xs0 ys0 p0 dr1)))))))

(def-fns _ $ erased drop-nth : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A x) (erased (List A) rest)
    (subterm erased (Drop A k xs (Cons A x rest)) dr) -> (erased (Nth A k xs x) n) (erased (Drop A (Succ k) xs rest) dr1)
  (match erased dr _
    ((DropZ a e) (values (NthHere A x rest) (DropS A (Zero) x rest rest (DropZ A rest))))
    ((DropS a k1 y xs1 ys1 dr1)
      (let (erased n) (erased d2) (drop-nth A k1 xs1 x rest dr1))
      (values (NthThere A k1 y xs1 x n) (DropS A (Succ k1) y xs1 rest d2)))))

(def-fns _ $ erased revonto-shift : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A y) (erased (List A) acc) (erased (List A) res)
    (subterm erased (RevOnto A k xs (Cons A y acc) res) p) -> (erased (RevOnto A (Succ k) (Cons A y xs) acc res) q)
  (match erased p _
    ((RevZ a e1 e2) (RevS A (Zero) (Cons A y xs) acc acc y (RevZ A (Cons A y xs) acc) (NthHere A y xs)))
    ((RevS a k1 e1 e2 res1 x p1 n)
      (RevS A (Succ k1) (Cons A y xs) acc res1 x (revonto-shift A k1 xs y acc res1 p1) (NthThere A k1 y xs x n)))))


(def-fns _ $ erased nth-fn : (erased Type A) (erased (Nat) i) (erased (List A) xs) (erased A x) (erased A y)
    (subterm erased (Nth A i xs x) p) (erased (Nth A i xs y) q) -> (erased (Eq A x y) e)
  (match erased p _
    ((NthHere a e r) (match erased q _ ((NthHere a2 e2 r2) (Refl A x))))
    ((NthThere a i1 z r e p1) (match erased q _ ((NthThere a2 i2 z2 r2 e2 q1) (nth-fn A i1 r x y p1 q1))))))

(def-fns _ $ erased concat-total : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (Concat A xs ys zs) p)
  (match erased xs _
    ((Nil a) (values ys (CatNil A ys)))
    ((Cons a x rest)
      (let (erased zs) (erased p) (concat-total A rest ys))
      (values (Cons A x zs) (CatCons A x rest ys zs p)))))

(def-fns _ $ erased concat-length-snoc : (erased Type A) (erased (List A) xs) (erased A y) (erased (List A) xy) (erased (Nat) n)
    (subterm erased (Concat A xs (Cons A y (Nil A)) xy) p) (erased (Length A xs n) l) -> (erased (Length A xy (Succ n)) l2)
  (match erased p _
    ((CatNil a e) (match erased l _ ((LNil a2) (LCons A y (Nil A) (Zero) (LNil A)))))
    ((CatCons a x rest e zs p1)
      (match erased l _
        ((LCons a2 e2 e3 n1 l1) (LCons A x zs (Succ n1) (concat-length-snoc A rest y zs n1 p1 l1)))))))

(def-fns _ $ erased concat-snoc-shift : (erased Type A) (erased (List A) xs) (erased A y) (erased (List A) xy) (erased (List A) d) (erased (List A) s)
    (subterm erased (Concat A xs (Cons A y (Nil A)) xy) p) (erased (Concat A xs (Cons A y d) s) q) -> (erased (Concat A xy d s) r)
  (match erased p _
    ((CatNil a e) (match erased q _ ((CatNil a2 e2) (CatCons A y (Nil A) d d (CatNil A d)))))
    ((CatCons a x rest e zs p1)
      (match erased q _
        ((CatCons a2 x2 rest2 e2 zs2 q1) (CatCons A x zs d zs2 (concat-snoc-shift A rest y zs d zs2 p1 q1)))))))

(def-fns _ $ erased drop-unstep : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased A y) (erased (List A) d)
    (subterm erased (Drop A (Succ k) xs d) dr) (erased (Nth A k xs y) n) -> (erased (Drop A k xs (Cons A y d)) dr2)
  (match erased dr _
    ((DropS a k1 x0 xs0 e p)
      (match erased n _
        ((NthHere a2 e2 r2) (match erased p _ ((DropZ a3 e3) (DropZ A xs))))
        ((NthThere a2 i2 z2 r2 e2 n1) (DropS A i2 x0 xs0 (Cons A y d) (drop-unstep A i2 xs0 y d p n1)))))))

(def-fns _ $ erased apart-irrefl : (erased (Nat) x) (erased (NatApart x x) d) -> (erased (False) f)
  (match erased d _
    ((ApartLt a b lt) (lt-asym x x lt (lt-succ x)))
    ((ApartGt a b lt) (lt-asym x x lt (lt-succ x)))))

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
        (absurd (DisHead k2 x2 y2 xs2 ys2 d0) (apart-irrefl x0 d0))
        ((DisTail k2 x2 xs2 ys2 dis0)
          (match erased nx _
            ((NthThere a i z r e n1) (match erased ny _ ((NthThere a2 i2 z2 r2 e2 n2) (disagree-nth k xs0 ys0 x y ag0 dis0 n1 n2))))))))))

(def-fns _ $ erased win-pal : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (subterm erased (Win k l mid r w) win) (erased (Agree k l r) ag) (erased (Palindrome (Nat) mid) pm) -> (erased (Palindrome (Nat) w) p)
  (match erased win _
    ((WinZ a b c) pm)
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased (nth-fn (Nat) k0 r x y (agree-nth k0 k l r x ag (lt-succ k0) nx) ny) _
        ((Refl t e) (PalWrap (Nat) x w0 wy (win-pal k0 l mid r w0 win0 (agree-weaken k0 l r ag) pm) q))))))

(def-fns _ $ erased win-notpal : (erased (Nat) k) (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (subterm erased (Win k l mid r w) win) (erased (Agree p l r) ag) (erased (Disagree (Succ p) l r) dis) (erased (Lt p k) lt) -> (erased (NotPalindrome w) np)
  (match erased win _
    ((WinZ a b c) (match erased lt _))
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased (nat-cmp p k0) _
        ((CEq t rr a) (NotPalEnds x y w0 wy q (disagree-nth p l r x y ag dis nx ny)))
        (absurd (CGt t rr a b gt) (lt-asym k0 p gt lt))
        ((CLt t rr a b plt)
          (match erased (nat-cmp x y) _
            ((CLt t2 r2 a2 b2 xlt) (NotPalEnds x y w0 wy q (ApartLt x y xlt)))
            ((CGt t2 r2 a2 b2 xgt) (NotPalEnds x y w0 wy q (ApartGt x y xgt)))
            ((CEq t2 r2 a2) (NotPalInner x w0 wy q (win-notpal k0 p l mid r w0 win0 ag dis plt)))))))))

(def-fns _ $ erased win-inner : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (erased (Nat) x) (erased (List (Nat)) midx)
    (subterm erased (Win k l (Cons (Nat) x midx) r w) win) (erased (Concat (Nat) mid (Cons (Nat) x (Nil (Nat))) midx) cm) ->
    (erased (Win (Succ k) (Cons (Nat) x l) mid (Cons (Nat) x r) w) win2)
  (match erased win _
    ((WinZ a b c)
      (WinS (Zero) (Cons (Nat) x l) mid (Cons (Nat) x r) mid x x midx (WinZ (Cons (Nat) x l) mid (Cons (Nat) x r))
            (NthHere (Nat) x l) (NthHere (Nat) x r) cm))
    ((WinS k0 l0 m0 r0 w0 a b wb win0 na nb q)
      (WinS (Succ k0) (Cons (Nat) x l) mid (Cons (Nat) x r) w0 a b wb (win-inner k0 l mid r w0 x midx win0 cm)
            (NthThere (Nat) k0 x l a na) (NthThere (Nat) k0 x r b nb) q))))

(def-fns _ $ erased agree-win : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) mid)
    (subterm erased (Agree k l r) ag) -> (erased (List (Nat)) w) (erased (Win k l mid r w) win)
  (match erased ag _
    ((AgreeZ a b) (values mid (WinZ l mid r)))
    ((AgreeS k0 x xs ys ag0)
      (let (erased midx) (erased cm) (concat-total (Nat) mid (Cons (Nat) x (Nil (Nat)))))
      (let (erased w) (erased win) (agree-win k0 xs ys (Cons (Nat) x midx) ag0))
      (values w (win-inner k0 xs mid ys w x midx win cm)))))

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
                  (LCons (Nat) x wy (Succ n0) (concat-length-snoc (Nat) w0 y wy n0 q (win-length k0 l mid r w0 m kk0 n0 win0 lm dk0 ad0))))))))))))

(def-fns _ $ erased win-prefix : (erased (Nat) k) (erased (List (Nat)) l) (erased (List (Nat)) mid) (erased (List (Nat)) r) (erased (List (Nat)) w)
    (erased (List (Nat)) mr) (erased (List (Nat)) s) (erased (List (Nat)) d)
    (subterm erased (Win k l mid r w) win) (erased (Concat (Nat) mid r mr) cm) (erased (RevOnto (Nat) k l mr s) rv) (erased (Drop (Nat) k r d) dr) ->
    (erased (Concat (Nat) w d s) c)
  (match erased win _
    ((WinZ a b c) (match erased rv _ ((RevZ a2 b2 c2) (match erased dr _ ((DropZ a3 b3) cm)))))
    ((WinS k0 l0 m0 r0 w0 x y wy win0 nx ny q)
      (match erased rv _
        ((RevS a2 k2 e2 e3 s0 x2 rv0 nx2)
          (match erased (nth-fn (Nat) k0 l x x2 nx nx2) _
            ((Refl t e)
              (CatCons (Nat) x wy d s0
                (concat-snoc-shift (Nat) w0 y wy d s0 q
                  (win-prefix k0 l mid r w0 mr s0 (Cons (Nat) y d) win0 cm rv0 (drop-unstep (Nat) k0 r y d dr ny)))))))))))


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
        ((Succ j1) (match erased le _ ((LtS a1 b1 l1) (AgreeS j1 x xs0 ys0 (agree-weaken-to k0 j1 xs0 ys0 p0 l1)))))))))

(def-fns _ $ erased agree-nth-ex : (erased (Nat) k) (erased (Nat) i) (erased (List (Nat)) xs) (erased (List (Nat)) ys)
    (subterm erased (Agree k xs ys) p) (erased (Lt i k) lt) -> (erased (Nat) x) (erased (Nth (Nat) i xs x) nx) (erased (Nth (Nat) i ys x) ny)
  (match erased p _
    ((AgreeZ a b) (match erased lt _))
    ((AgreeS k0 x0 xs0 ys0 p0)
      (match erased i _
        ((Zero) (values x0 (NthHere (Nat) x0 xs0) (NthHere (Nat) x0 ys0)))
        ((Succ i1)
          (match erased lt _
            ((LtS a1 b1 l1)
              (let (erased x) (erased nx) (erased ny) (agree-nth-ex k0 i1 xs0 ys0 p0 l1))
              (values x (NthThere (Nat) i1 x0 xs0 x nx) (NthThere (Nat) i1 x0 ys0 x ny)))))))))

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
                ((AgreeS k0 x0 xs0 ys0 ag0) (agree-drop c3 d1 q l1 r1 ld rd dl1 dr1 ad1 ag0))))))))))

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
            ((AddSucc a3 b3 s1 ad1) (NthThere (Nat) s1 z w1 x (nth-concat-after mid1 r w1 m1 e s1 x cm1 lm1 ad1 n)))))))))

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
                                                  (AgreeS q1 z l r (agree-weaken q1 l r (agree-weaken (Succ q1) l r ag))))))))))))))))))))))))))
    ((RevS a1 k1 e1 e2 b1 lx rb1 nl)
      (let (erased em1) (erased eem) (erased aem1) (add-succ-right-inv m k1 em aem))
      (match erased eem _
        ((Refl t1 r1)
          (match erased ra _
            ((RevS a2 k2 e3 e4 a1 wx ra1 nw)
              (match erased aq _
                ((AddSucc a3 b3 c3 aq1)
                  (let (erased ltk) (lt-le-trans k1 (Succ em1) p (add-le-left k1 m em1 (add-comm m k1 em1 aem1)) (LtS em1 p (add-le-left em1 q c3 aq1))))
                  (let (erased nr) (agree-nth k1 p l r lx ag ltk nl))
                  (let (erased nw2) (nth-concat-after mid r w m k1 em1 lx cm (mid-length m mid md) aem1 nr))
                  (match erased (nth-fn (Nat) em1 w wx lx nw nw2) _
                    ((Refl t2 r2)
                      (let (erased ih) (mirror-agree p m k1 em1 (Succ q) l r mid w a1 b1 ag md cm rb1 aem1 ra1 (add-succ-right em1 q c3 aq1)))
                      (match erased q _
                        ((Zero) (AgreeZ a b))
                        ((Succ q2) (AgreeS q2 lx a1 b1 (agree-weaken q2 a1 b1 (agree-weaken (Succ q2) a1 b1 ih))))))))))))))))


; A centre's certificate: its radius is exact. Back is the runtime list of radii of the centres
; before a zipper, each with its certificate; Bound says every radius there gives a window no longer than b.

(def-adts
  (Cert : ((Nat) m) ((List (Nat)) l) ((List (Nat)) r) ((Nat) p) -> Type
    enum
    (many MkCert : (erased (Nat) m) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (Nat) p) (erased (List (Nat)) arm)
        (erased (Drop (Nat) m r arm) dr) (erased (Agree p l arm) ag) (erased (Disagree (Succ p) l arm) dis) -> (Cert m l r p))))

(def-adts
  (Back : ((Nat) m) ((List (Nat)) l) ((List (Nat)) r) -> Type
    enum
    (many BackZ : (erased (Nat) m) (erased (List (Nat)) r) -> (Back m (Nil (Nat)) r))
    (many BackS : (erased (Nat) m) (erased (List (Nat)) l) (erased (Nat) x) (erased (List (Nat)) r) (many (Nat) p)
        (erased (Cert m l (Cons (Nat) x r) p) c) (many (Back m l (Cons (Nat) x r)) rest) -> (Back m (Cons (Nat) x l) r))))

(def-adts
  (Bound : ((Nat) m) ((Nat) b) ((List (Nat)) l) ((List (Nat)) r) ((Back m l r) bk) -> Type
    enum
    (many BoundZ : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) r) -> (Bound m b (Nil (Nat)) r (BackZ m r)))
    (many BoundS : (erased (Nat) m) (erased (Nat) b) (erased (List (Nat)) l) (erased (Nat) x) (erased (List (Nat)) r) (erased (Nat) p)
        (erased (Cert m l (Cons (Nat) x r) p) c) (erased (Back m l (Cons (Nat) x r)) rest)
        (erased (Nat) pp) (erased (Nat) n) (erased (Double p pp) dd) (erased (Add pp m n) an) (erased (Lt n (Succ b)) le)
        (erased (Bound m b l (Cons (Nat) x r) rest) bd) ->
       (Bound m b (Cons (Nat) x l) r (BackS m l x r p c rest)))))

; The mirror gives a certificate for the current centre when the mirror centre's radius p2 falls
; short of the reach q: la/ra are the current arms, lm/rm the mirror's.

(def-fns _ $ erased mirror-cert : (erased (Nat) q) (erased (Nat) p2) (erased (List (Nat)) la) (erased (List (Nat)) ra)
    (erased (List (Nat)) lm) (erased (List (Nat)) rm)
    (erased (Agree q la rm) x1) (erased (Agree q lm ra) x2) (erased (Agree p2 lm rm) ag) (erased (Disagree (Succ p2) lm rm) dis)
    (erased (Lt p2 q) lt) ->
    (erased (Agree p2 la ra) ag2) (erased (Disagree (Succ p2) la ra) dis2)
  (let (erased le) (lt-weaken p2 q lt))
  (let (erased a1) (agree-weaken-to q p2 la rm x1 le))
  (let (erased a2) (agree-weaken-to q p2 lm ra x2 le))
  (let (erased ag2) (agree-trans p2 la rm ra a1 (agree-trans p2 rm lm ra (agree-sym p2 lm rm ag) a2)))
  (let (erased x) (erased nlm) (erased nra) (agree-nth-ex q p2 lm ra x2 lt))
  (let (erased y) (erased nla) (erased nrm) (agree-nth-ex q p2 la rm x1 lt))
  (let (erased d) (disagree-nth p2 lm rm x y ag dis nlm nrm))
  (values ag2 (disagree-at p2 la ra y x ag2 nla nra (apart-sym x y d))))

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
    ((Nil a) (values k lp rp rd dl rv dr ag (disagree-short k l r ag dl)))
    ((Cons a x lp1)
      (match many rd _
        ((Nil a2) (values k lp rp rd dl rv dr ag (disagree-short-r k l r ag dr)))
        ((Cons a2 y rd1)
          (let (erased nx) (erased dl1) (drop-nth (Nat) k l x lp1 dl))
          (let (erased ny) (erased dr1) (drop-nth (Nat) k r y rd1 dr))
          (match many (nat-cmp x y) _
            ((CLt t rr a3 b3 lt) (values k lp rp rd dl rv dr ag (disagree-at k l r x y ag nx ny (ApartLt x y lt))))
            ((CGt t rr a3 b3 gt) (values k lp rp rd dl rv dr ag (disagree-at k l r x y ag nx ny (ApartGt x y gt))))
            ((CEq t rr a3)
              (expand (Succ k) lp1 (Cons (Nat) x rp) rd1 l ri r dl1 (RevS (Nat) k l ri rp x rv nx) dr1 (agree-snoc k l r x ag nx ny)))))))))


(def-fns _ $ erased drop-fn : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
    (subterm erased (Drop A k xs ys) p) (erased (Drop A k xs zs) q) -> (erased (Eq (List A) ys zs) e)
  (match erased p _
    ((DropZ a e1) (match erased q _ ((DropZ a2 e2) (Refl (List A) ys))))
    ((DropS a k1 x xs1 e1 p1) (match erased q _ ((DropS a2 k2 x2 xs2 e2 q1) (drop-fn A k1 xs1 ys zs p1 q1))))))

(def-fns _ $ erased drop-compose : (erased Type A) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
    (subterm erased (Drop A a xs ys) p) (erased (Drop A b ys zs) q) (erased (Add a b c) ad) -> (erased (Drop A c xs zs) r)
  (match erased p _
    ((DropZ a1 e1) (match erased ad _ ((AddZero b1) q)))
    ((DropS a1 k1 x xs1 e1 p1)
      (match erased ad _
        ((AddSucc a2 b2 c2 ad1) (DropS A c2 x xs1 zs (drop-compose A k1 b c2 xs1 ys zs p1 q ad1)))))))

(def-fns _ $ erased drop-split : (erased Type A) (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (List A) xs) (erased (List A) zs)
    (subterm erased (Drop A c xs zs) p) (erased (Add a b c) ad) -> (erased (List A) ys) (erased (Drop A a xs ys) q) (erased (Drop A b ys zs) r)
  (match erased ad _
    ((AddZero b1) (values xs (DropZ A xs) p))
    ((AddSucc a1 b1 c1 ad1)
      (match erased p _
        ((DropS a2 k2 x xs1 e2 p1)
          (let (erased ys) (erased q) (erased r) (drop-split A a1 b c1 xs1 zs p1 ad1))
          (values ys (DropS A a1 x xs1 ys q) r))))))

; drop m after drop d is drop d after drop m
(def-fns _ $ erased drop-swap : (erased (Nat) d) (erased (Nat) m) (erased (List (Nat)) w) (erased (List (Nat)) ri) (erased (List (Nat)) arm) (erased (List (Nat)) armc)
    (erased (Drop (Nat) d w ri) p) (erased (Drop (Nat) m ri arm) q) (erased (Drop (Nat) m w armc) r) -> (erased (Drop (Nat) d armc arm) s)
  (let (erased dm) (erased adm) (add d m))
  (let (erased ys) (erased q2) (erased r2) (drop-split (Nat) m d dm w arm (drop-compose (Nat) d m dm w ri arm p q adm) (add-comm d m dm adm)))
  (match erased (drop-fn (Nat) m w ys armc q2 r) _ ((Refl t e) r2)))

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
            ((DropZ a2 e2) (values (Cons (Nat) x (Nil (Nat))) (MidOdd x) (CatCons (Nat) x (Nil (Nat)) xs xs (CatNil (Nat) xs))))))))))

(def-fns _ $ erased drop-nth-head : (erased Type A) (erased (Nat) k) (erased (List A) l) (erased A x) (erased (List A) l0)
    (subterm erased (Drop A k l l0) d) (erased (Nth A k l x) n) -> (erased (List A) l1) (erased (Eq (List A) l0 (Cons A x l1)) e) (erased (Drop A (Succ k) l l1) d2)
  (match erased d _
    ((DropZ a e1) (match erased n _ ((NthHere a2 e2 rest) (values rest (Refl (List A) l0) (DropS A (Zero) x rest rest (DropZ A rest))))))
    ((DropS a k1 y l2 e1 d1)
      (match erased n _
        ((NthThere a2 i2 y2 r2 e2 n1)
          (let (erased l1) (erased e) (erased d2) (drop-nth-head A k1 l2 x l0 d1 n1))
          (values l1 e (DropS A (Succ k1) y l2 l1 d2)))))))

(def-fns _ $ erased zip-back : (erased Type A) (erased (Nat) k) (erased (List A) xs) (erased (List A) l) (erased (List A) r) (erased (List A) s)
    (subterm erased (RevOnto A k l r s) rv) (erased (Zip A xs l r) z) -> (erased (List A) l0) (erased (Drop A k l l0) d) (erased (Zip A xs l0 s) z2)
  (match erased rv _
    ((RevZ a e1 e2) (values l (DropZ A l) z))
    ((RevS a k1 e1 e2 s0 x rv1 n)
      (let (erased l0) (erased d) (erased z2) (zip-back A k1 xs l r s0 rv1 z))
      (let (erased l1) (erased e) (erased d2) (drop-nth-head A k1 l x l0 d n))
      (match erased e _
        ((Refl t e3)
          (match erased z2 _
            ((ZipS a2 e4 l2 x2 e5 z3) (values l1 d2 z3))))))))

(def-fns _ $ erased zip-has : (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) s) (erased (Nat) n)
    (subterm erased (Zip (Nat) xs l s) z) (erased (HasPalindromeOfLength s n) h) -> (erased (HasPalindromeOfLength xs n) h2)
  (match erased z _
    ((ZipZ a e) h)
    ((ZipS a e l1 x r z1) (zip-has xs l1 (Cons (Nat) x s) n z1 (HasThere x s n h)))))

(def-fns _ $ erased concat-take : (erased Type A) (erased (List A) w) (erased (List A) d) (erased (List A) s) (erased (Nat) n)
    (subterm erased (Concat A w d s) c) (erased (Length A w n) l) -> (erased (Take A n s w) t)
  (match erased c _
    ((CatNil a e) (match erased l _ ((LNil a2) (TakeZero A s))))
    ((CatCons a x rest e zs c1)
      (match erased l _ ((LCons a2 e2 e3 n1 l1) (TakeSucc A n1 x zs rest (concat-take A rest d zs n1 c1 l1)))))))

(def-fns _ $ erased bound-weaken : (erased (Nat) m) (erased (Nat) b) (erased (Nat) b2) (erased (List (Nat)) l) (erased (List (Nat)) r)
    (erased (Back m l r) bk) (subterm erased (Bound m b l r bk) bd) (erased (Lt b (Succ b2)) le) -> (erased (Bound m b2 l r bk) bd2)
  (match erased bd _
    ((BoundZ a e r0) (BoundZ m b2 r))
    ((BoundS a e l0 x r0 p c rest pp n dd an lt bd1)
      (BoundS m b2 l0 x r0 p c rest pp n dd an (lt-le-trans n (Succ b) (Succ b2) lt (LtS b (Succ b2) le)) (bound-weaken m b b2 l0 (Cons (Nat) x r0) rest bd1 le)))))

(def-fns _ $ erased agree-drop-ex : (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) arm)
    (subterm erased (Agree p l arm) ag) -> (erased (List (Nat)) d) (erased (Drop (Nat) p arm d) dr)
  (match erased ag _
    ((AgreeZ a b) (values arm (DropZ (Nat) arm)))
    ((AgreeS k x xs ys ag0)
      (let (erased d) (erased dr) (agree-drop-ex k xs ys ag0))
      (values d (DropS (Nat) k x ys d dr)))))

; The evidence that the window of radius p around the centre at (l, ri) is a palindrome of length n.

(def-fns _ $ erased has-at-centre : (erased (List (Nat)) xs) (erased (List (Nat)) l) (erased (List (Nat)) ri) (erased (List (Nat)) arm)
    (erased (Nat) m) (erased (Nat) p) (erased (List (Nat)) s) (erased (Nat) pp) (erased (Nat) n)
    (erased (Zip (Nat) xs l ri) z) (erased (Par m) pr) (erased (Drop (Nat) m ri arm) dr) (erased (Agree p l arm) ag)
    (erased (RevOnto (Nat) p l ri s) rv) (erased (Double p pp) dd) (erased (Add pp m n) an) -> (erased (HasPalindromeOfLength xs n) h)
  (let (erased mid) (erased md) (erased cm) (mid-of m ri arm pr dr))
  (let (erased w) (erased win) (agree-win p l arm mid ag))
  (let (erased pal) (win-pal p l mid arm w win ag (mid-pal m mid md)))
  (let (erased lw) (win-length p l mid arm w m pp n win (mid-length m mid md) dd an))
  (let (erased d) (erased dr2) (agree-drop-ex p l arm ag))
  (let (erased pre) (win-prefix p l mid arm w ri s d win cm rv dr2))
  (let (erased l0) (erased dl0) (erased z2) (zip-back (Nat) p xs l ri s rv z))
  (zip-has xs l0 s n z2 (HasHere s n w (concat-take (Nat) w d s n pre lw) pal)))


; --- the main loop ---
; Reach is what the loop knows about the rightmost palindrome seen so far, at the centre (li, ri): nothing
; (Out), or (In) the palindrome of radius pc at (lc, w), the current centre d steps past it with q more
; steps inside it, and the radius list from the mirror centre (mp).

(def-adts
  (Reach : ((Nat) m) ((List (Nat)) li) ((List (Nat)) ri) ((Nat) q) -> Type
    enum
    (many Out : (erased (Nat) m) (erased (List (Nat)) li) (erased (List (Nat)) ri) -> (Reach m li ri (Zero)))
    (many In : (erased (Nat) m) (erased (List (Nat)) li) (erased (List (Nat)) ri) (erased (Nat) q1)
        (erased (List (Nat)) lc) (erased (List (Nat)) w) (erased (List (Nat)) armc) (erased (Nat) pc) (erased (Nat) d) (erased (Nat) e)
        (erased (Nat) x) (erased (List (Nat)) lm) (erased (List (Nat)) rm1)
        (erased (Drop (Nat) m w armc) drc) (erased (Agree pc lc armc) agc)
        (erased (RevOnto (Nat) d w lc li) rvl) (erased (Drop (Nat) d w ri) drr)
        (erased (Add d (Succ q1) pc) aq) (erased (Add m e d) aem)
        (erased (Drop (Nat) d lc lm) dlm) (erased (RevOnto (Nat) d lc w (Cons (Nat) x rm1)) rvm)
        (many (Back m (Cons (Nat) x lm) rm1) mp) ->
       (Reach m li ri (Succ q1)))))

(def-adts
  (PredZ : ((Nat) k) ((Nat) qn) -> Type
    enum
    (many PZ : -> (PredZ (Zero) (Zero)))
    (many PS : (erased (Nat) k) -> (PredZ (Succ k) k))))

(def-fns _ $ erased agree-drop-cons : (erased (Nat) p) (erased (Nat) d) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) ld)
    (erased (Agree p l r) ag) (subterm erased (Drop (Nat) d l ld) dr) (erased (Lt d p) lt) ->
    (erased (Nat) y) (erased (List (Nat)) ld2) (erased (Eq (List (Nat)) ld (Cons (Nat) y ld2)) e)
  (match erased dr _
    ((DropZ a e1) (match erased lt _ ((LtZ b) (match erased ag _ ((AgreeS k x xs ys ag0) (values x xs (Refl (List (Nat)) ld)))))))
    ((DropS a k1 x xs e1 dr1)
      (match erased lt _
        ((LtS a2 b2 lt1) (match erased ag _ ((AgreeS k x2 xs2 ys ag0) (agree-drop-cons b2 k1 xs2 ys ld ag0 dr1 lt1))))))))

(def-fns _ $ erased next-arm : (erased (Nat) m) (erased (Nat) w) (erased (Nat) y) (erased (List (Nat)) rest2) (erased (List (Nat)) arm)
    (erased (Par m) pr) (erased (Drop (Nat) m (Cons (Nat) w (Cons (Nat) y rest2)) arm) dr) ->
    (erased (Nat) h) (erased (List (Nat)) arm2) (erased (Eq (List (Nat)) arm (Cons (Nat) h arm2)) e) (erased (Drop (Nat) m (Cons (Nat) y rest2) arm2) dr2)
  (match erased pr _
    ((PEven) (match erased dr _ ((DropZ a e1) (values w (Cons (Nat) y rest2) (Refl (List (Nat)) arm) (DropZ (Nat) (Cons (Nat) y rest2))))))
    ((POdd)
      (match erased dr _
        ((DropS a k x xs e1 dr1)
          (match erased dr1 _
            ((DropZ a2 e2) (values y rest2 (Refl (List (Nat)) arm) (DropS (Nat) (Zero) y rest2 rest2 (DropZ (Nat) rest2))))))))))

(def-fns _ $ erased par-e : (erased (Nat) m) (erased (Par m) pr) -> (erased (Nat) e) (erased (Add m e (Succ (Zero))) a)
  (match erased pr _
    ((PEven) (values (Succ (Zero)) (AddZero (Succ (Zero)))))
    ((POdd) (values (Zero) (AddSucc (Zero) (Zero) (Zero) (AddZero (Zero)))))))

(def-fns _ $ erased agree-revonto-ex : (erased (Nat) p) (erased (List (Nat)) l) (erased (List (Nat)) r) (erased (List (Nat)) acc)
    (subterm erased (Agree p l r) ag) -> (erased (List (Nat)) s) (erased (RevOnto (Nat) p l acc s) rv)
  (match erased ag _
    ((AgreeZ a b) (values acc (RevZ (Nat) l acc)))
    ((AgreeS k x xs ys ag0)
      (let (erased s) (erased rv) (agree-revonto-ex k xs ys (Cons (Nat) x acc) ag0))
      (values s (revonto-shift (Nat) k xs x acc s rv)))))

(def-fns _ $ erased add-lt-succ : (erased (Nat) d) (erased (Nat) k) (erased (Nat) p) (erased (Add d (Succ k) p) a) -> (erased (Lt d p) lt)
  (let (erased c1) (erased e) (erased a1) (add-succ-right-inv d k p a))
  (match erased e _ ((Refl t r) (add-le-left d k c1 a1))))

(def-fns _
  (many after-expand : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (many (Nat) w) (subterm many (List (Nat)) rest) (subterm erased (Nat) ph) (erased (Eq (Nat) ph (Succ (Succ (Zero)))) eph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m (Cons (Nat) w rest) arm) dra) (erased (Zip (Nat) xs li (Cons (Nat) w rest)) z)
      (many (Nat) p) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) p li lp) dlp) (erased (RevOnto (Nat) p li (Cons (Nat) w rest) rp) rvp) (erased (Drop (Nat) p arm rd) drd)
      (erased (Agree p li arm) ag) (erased (Disagree (Succ p) li arm) dis)
      (many (Back m li (Cons (Nat) w rest)) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best li (Cons (Nat) w rest) acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m lend (Nil (Nat))) accend)
      (erased (Bound m best2 lend (Nil (Nat)) accend) bdend)
    (match erased eph _
      ((Refl t e0)
        (match many p _
          ((Zero)
            (finish xs m pr li w rest (Succ (Zero)) (Refl (Nat) (Succ (Zero))) arm dra z p ag dis p lp rp rd dlp rvp drd
                    (Zero) (PZ) (Out m (Cons (Nat) w li) rest) acc best has bd))
          ((Succ p1)
            (match many p1 _
              ((Zero)
                (finish xs m pr li w rest (Succ (Zero)) (Refl (Nat) (Succ (Zero))) arm dra z p ag dis p lp rp rd dlp rvp drd
                        p1 (PS p1) (Out m (Cons (Nat) w li) rest) acc best has bd))
              ((Succ p2)
                (match erased ag _
                  ((AgreeS k x lm ys ag0)
                    (let (erased e) (erased aem) (par-e m pr))
                    (finish xs m pr li w rest (Succ (Zero)) (Refl (Nat) (Succ (Zero))) arm dra z p ag dis p lp rp rd dlp rvp drd
                            p1 (PS p1)
                            (In m (Cons (Nat) w li) rest p2 li (Cons (Nat) w rest) arm p (Succ (Zero)) e x lm (Cons (Nat) w rest)
                                dra ag
                                (RevS (Nat) (Zero) (Cons (Nat) w rest) li li w (RevZ (Nat) (Cons (Nat) w rest) li) (NthHere (Nat) w rest))
                                (DropS (Nat) (Zero) w rest rest (DropZ (Nat) rest))
                                (AddSucc (Zero) p1 p1 (AddZero p1)) aem
                                (DropS (Nat) (Zero) x lm lm (DropZ (Nat) lm))
                                (RevS (Nat) (Zero) li (Cons (Nat) w rest) (Cons (Nat) w rest) x (RevZ (Nat) li (Cons (Nat) w rest)) (NthHere (Nat) x lm))
                                acc)
                            acc best has bd))))))))))

  (many finish : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (many (Nat) w) (subterm many (List (Nat)) rest) (subterm erased (Nat) ph) (erased (Eq (Nat) ph (Succ (Zero))) eph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m (Cons (Nat) w rest) arm) dra) (erased (Zip (Nat) xs li (Cons (Nat) w rest)) z)
      (many (Nat) p) (erased (Agree p li arm) ag) (erased (Disagree (Succ p) li arm) dis)
      (many (Nat) ki) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) ki li lp) dlp) (erased (RevOnto (Nat) ki li (Cons (Nat) w rest) rp) rvp) (erased (Drop (Nat) ki arm rd) drd)
      (many (Nat) qn) (erased (PredZ ki qn) pz) (many (Reach m (Cons (Nat) w li) rest qn) reach)
      (many (Back m li (Cons (Nat) w rest)) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best li (Cons (Nat) w rest) acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m lend (Nil (Nat))) accend)
      (erased (Bound m best2 lend (Nil (Nat)) accend) bdend)
    (let (many pp) (erased dd) (double p))
    (let (many n) (erased an) (add pp m))
    (let (many best2) (erased has2) (erased le) (erased bd2)
      (match many (lt-dec best n) (((Nat) b2) ((HasPalindromeOfLength xs b2) h2) ((Lt n (Succ b2)) l2) ((Bound m b2 li (Cons (Nat) w rest) acc) d2))
        ((Yes a b lt)
          (let (erased s) (erased rvs) (agree-revonto-ex p li arm (Cons (Nat) w rest) ag))
          (values n (has-at-centre xs li (Cons (Nat) w rest) arm m p s pp n z pr dra ag rvs dd an) (lt-succ n)
                  (bound-weaken m best n li (Cons (Nat) w rest) acc bd (lt-weaken best n lt))))
        ((No a b ge) (values best has ge bd))))
    (let (many acc2) (BackS m li w rest p (MkCert m li (Cons (Nat) w rest) p arm dra ag dis) acc))
    (let (erased bd3) (BoundS m best2 li w rest p (MkCert m li (Cons (Nat) w rest) p arm dra ag dis) acc pp n dd an le bd2))
    (let (erased z2) (ZipS (Nat) xs li w rest z))
    (match erased eph _
      ((Refl t e0)
        (match many rest _
          ((Nil a) (values best2 has2 (Cons (Nat) w li) z2 acc2 bd3))
          ((Cons a y rest2)
            (let (erased h) (erased arm2) (erased earm) (erased dra2) (next-arm m w y rest2 arm pr dra))
            (match erased earm _
              ((Refl t2 e2)
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
                                        (scan xs m pr (Cons (Nat) w li) rest (Zero) arm2 dra2 z2 (Zero) (Cons (Nat) w lp) rest rd2
                                              (DropZ (Nat) (Cons (Nat) w li)) (RevZ (Nat) (Cons (Nat) w li) rest) (DropZ (Nat) arm2)
                                              reach acc2 best2 has2 bd3))))))))))))
                  ((Succ k1)
                    (match erased pz _
                      ((PS e6)
                        (match erased rvp _
                          ((RevS a7 e7 e8 e9 rp1 x1 rvp1 nx1)
                            (let (erased d0) (drop-unstep (Nat) k1 li x1 lp dlp nx1))
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
                                                    (scan xs m pr (Cons (Nat) w li) rest (Zero) arm2 dra2 z2 (Zero) (Cons (Nat) w (Cons (Nat) x1b lp)) restb rd
                                                          (DropZ (Nat) (Cons (Nat) w li)) (RevZ (Nat) (Cons (Nat) w li) rest) drd1
                                                          reach acc2 best2 has2 bd3))))))))
                                      ((Succ k2)
                                        (match erased rvp1 _
                                          ((RevS a13 e17 e18 e19 rp2 x2 rvp2 nx2)
                                            (match many rp1b _
                                              ((Cons a14 x2b rp2b)
                                                (scan xs m pr (Cons (Nat) w li) rest (Zero) arm2 dra2 z2 k1 (Cons (Nat) x2b (Cons (Nat) x1b lp)) rp2b rd
                                                      (DropS (Nat) k2 w li (Cons (Nat) x2 (Cons (Nat) x1 lp)) (drop-unstep (Nat) k2 li x2 (Cons (Nat) x1 lp) d0 nx2))
                                                      (revonto-shift (Nat) k2 li w rest rp2 rvp2) drd1
                                                      reach acc2 best2 has2 bd3))))))))))))))))))))))))

  (many scan : (erased (List (Nat)) xs) (many (Nat) m) (erased (Par m) pr) (erased (List (Nat)) li)
      (subterm many (List (Nat)) ri) (subterm erased (Nat) ph)
      (erased (List (Nat)) arm) (erased (Drop (Nat) m ri arm) dra) (erased (Zip (Nat) xs li ri) z)
      (many (Nat) q) (many (List (Nat)) lp) (many (List (Nat)) rp) (many (List (Nat)) rd)
      (erased (Drop (Nat) q li lp) dlp) (erased (RevOnto (Nat) q li ri rp) rvp) (erased (Drop (Nat) q arm rd) drd)
      (many (Reach m li ri q) reach) (many (Back m li ri) acc)
      (many (Nat) best) (erased (HasPalindromeOfLength xs best) has) (erased (Bound m best li ri acc) bd) ->
      (many (Nat) best2) (erased (HasPalindromeOfLength xs best2) has2)
      (erased (List (Nat)) lend) (erased (Zip (Nat) xs lend (Nil (Nat))) zend) (many (Back m lend (Nil (Nat))) accend)
      (erased (Bound m best2 lend (Nil (Nat)) accend) bdend)
    (match many ri _
      ((Nil a) (values best has li z acc bd))
      ((Cons a w rest)
        (match many reach _
          ((Out e1 e2 e3)
            (let (many p) (many lp2) (many rp2) (many rd2) (erased dl2) (erased rv2) (erased dr2) (erased ag2) (erased dis2)
              (expand q lp rp rd li ri arm dlp rvp drd (AgreeZ li arm)))
            (after-expand xs m pr li w rest (Succ (Succ (Zero))) (Refl (Nat) (Succ (Succ (Zero)))) arm dra z p lp2 rp2 rd2 dl2 rv2 dr2 ag2 dis2 acc best has bd))
          ((In e1 e2 e3 q1 lc wc armc pc d e x lm rm1 drc agc rvl drr aq aem dlm rvm mp)
            (match many mp _
              ((BackS e4 e5 e6 e7 p2 c mp2)
                (let-match erased c (MkCert e8 e9 e10 e11 armm dram agm dism))
                (let (erased midc) (erased mdc) (erased cmc) (mid-of m wc armc pr drc))
                (let (erased rvarm) (revonto-drop-mid m midc d e lc wc (Cons (Nat) x rm1) armm mdc aem rvm dram))
                (let (erased x1) (mirror-agree pc m e d q lc armc midc wc li armm agc mdc cmc rvarm aem rvl aq))
                (let (erased x2) (agree-drop pc d q lc armc lm arm dlm (drop-swap d m wc ri arm armc drr dra drc) aq agc))
                (match many (lt-dec p2 q) _
                  ((Yes a1 b1 lt)
                    (let (erased agi) (erased disi) (mirror-cert q p2 li arm lm armm x1 x2 agm dism lt))
                    (let (erased nw) (erased drr2) (drop-nth (Nat) d wc w rest drr))
                    (let (erased rvl2) (RevS (Nat) d wc lc li w rvl nw))
                    (match many q _
                      ((Succ q1b)
                        (match many q1b _
                          ((Zero)
                            (finish xs m pr li w rest (Succ (Zero)) (Refl (Nat) (Succ (Zero))) arm dra z p2 agi disi q lp rp rd dlp rvp drd
                                    q1b (PS q1b) (Out m (Cons (Nat) w li) rest) acc best has bd))
                          ((Succ q2)
                            (let (erased x3) (erased lm2) (erased elm) (agree-drop-cons pc d lc armc lm agc dlm (add-lt-succ d (Succ q2) pc aq)))
                            (match erased elm _
                              ((Refl t3 e3b)
                                (let (erased nx3) (erased dlm2) (drop-nth (Nat) d lc x3 lm2 dlm))
                                (let (erased c1) (erased epc) (erased aq1) (add-succ-right-inv d (Succ q2) pc aq))
                                (match erased epc _
                                  ((Refl t4 e4b)
                                    (finish xs m pr li w rest (Succ (Zero)) (Refl (Nat) (Succ (Zero))) arm dra z p2 agi disi q lp rp rd dlp rvp drd
                                            q1b (PS q1b)
                                            (In m (Cons (Nat) w li) rest q2 lc wc armc pc (Succ d) (Succ e) x3 lm2 (Cons (Nat) x rm1)
                                                drc agc rvl2 drr2 (AddSucc d (Succ q2) c1 aq1) (add-succ-right m e d aem) dlm2
                                                (RevS (Nat) d lc wc (Cons (Nat) x rm1) x3 rvm nx3) mp2)
                                            acc best has bd))))))))))
                  ((No a1 b1 ge)
                    (let (erased agq) (agree-trans q li armm arm x1 (agree-trans q armm lm arm (agree-sym q lm armm (agree-weaken-to p2 q lm armm agm ge)) x2)))
                    (let (many p) (many lp2) (many rp2) (many rd2) (erased dl2) (erased rv2) (erased dr2) (erased ag2) (erased dis2)
                      (expand q lp rp rd li ri arm dlp rvp drd agq))
                    (after-expand xs m pr li w rest (Succ (Succ (Zero))) (Refl (Nat) (Succ (Succ (Zero)))) arm dra z p lp2 rp2 rd2 dl2 rv2 dr2 ag2 dis2 acc best has bd)))))))))))

(Zero)
