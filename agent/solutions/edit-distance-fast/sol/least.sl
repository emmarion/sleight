; Minimum selection with an entirely erased witness list.
(def-fns _ $ (erased ed-atmost-lower : (erased (Nat) a b) (erased (Le a b) ab)
    (erased (List (Nat)) cs) (subterm erased (AtMost b cs) p) -> (erased (AtMost a cs) q))
  (let-match erased p (AtMostCons _ c rest bc more) ((AtMostNil _) (AtMostNil a)))
  (AtMostCons a c rest
    (MkLe a c (lt-le-trans a (Succ b) (Succ c) (le-lt a b ab) (LtS b (Succ c) (le-lt b c bc))))
    (ed-atmost-lower a b ab rest more)))

(def-fns _ $ (erased ed-least-one : (erased (Nat) a) ->
    (erased (Least (Cons (Nat) a (Nil (Nat))) a) p))
  (MkLeast _ a 0 (NthHere _ a (Nil _))
    (AtMostCons a a (Nil _) (MkLe a a (lt-succ a)) (AtMostNil a))))

(def-fns _ $ (many ed-min-cons : (many (Nat) c d) (erased (Lt c u62-modulus) pc) (erased (Lt d u62-modulus) pd)
    (erased (List (Nat)) cs) (erased (Least cs d) least) ->
    (many (Nat) m) (erased (Least (Cons (Nat) c cs) m) p) (erased (Lt m u62-modulus) pm)
    (erased (Le m c) mc) (erased (Le m d) md))
  (let-match erased least (MkLeast _ _ i member below))
  (let-match many (u62-lt-dec c d pc pd) (Yes _ _ _ _ cd)
    ((No _ _ _ _ le-dc) (let ((erased dc)) (lt-eq-succ _ _ le-dc))
      (let ((erased dc-le)) (MkLe d c dc))
      (values d (MkLeast _ d (Succ i) (NthThere _ c cs i d member) (AtMostCons d c cs dc-le below))
        pd dc-le (MkLe d d (lt-succ d)))))
  (let ((erased cd-le)) (MkLe c d (lt-weaken c d cd)))
  (values c (MkLeast _ c 0 (NthHere _ c cs) (AtMostCons c c cs (MkLe c c (lt-succ c)) (ed-atmost-lower c d cd-le cs below)))
    pc (MkLe c c (lt-succ c)) cd-le))

(def-fns _ $ (many ed-min3 : (many (Nat) a b c)
    (erased (Lt a u62-modulus) pa) (erased (Lt b u62-modulus) pb) (erased (Lt c u62-modulus) pc) ->
    (many (Nat) m) (erased (Least (Cons (Nat) a (Cons (Nat) b (Cons (Nat) c (Nil (Nat))))) m) p)
    (erased (Lt m u62-modulus) pm))
  (let ((many bc) (erased pbc) (erased pbc-fit) (erased _) (erased _))
    (ed-min-cons b c pb pc _ (ed-least-one c)))
  (let ((many m) (erased p) (erased pm) (erased _) (erased _)) (ed-min-cons a bc pa pbc-fit _ pbc))
  (values m p pm))

(def-fns _ $ (many ed-min4 : (many (Nat) a b c d)
    (erased (Lt a u62-modulus) pa) (erased (Lt b u62-modulus) pb) (erased (Lt c u62-modulus) pc) (erased (Lt d u62-modulus) pd) ->
    (many (Nat) m) (erased (Least (Cons (Nat) a (Cons (Nat) b (Cons (Nat) c (Cons (Nat) d (Nil (Nat)))))) m) p)
    (erased (Lt m u62-modulus) pm))
  (let ((many bcd) (erased pbcd) (erased pbcd-fit)) (ed-min3 b c d pb pc pd))
  (let ((many m) (erased p) (erased pm) (erased _) (erased _)) (ed-min-cons a bcd pa pbcd-fit _ pbcd))
  (values m p pm))
