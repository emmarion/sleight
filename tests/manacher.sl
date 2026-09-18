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

(Zero)
