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

(Zero)
