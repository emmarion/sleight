(def-fns _ $ (erased respects-nth : (erased (List (Nat)) lab xs ls) (erased (Nat) i j l) (subterm erased (Respects lab xs ls) rp)
    (erased (Nth (Nat) xs i j) p) (erased (Nth (Nat) ls i l) q) -> (erased (Nth (Nat) lab j l) r))
  (let-match erased rp (RespCons _ xs1 ls1 j1 l1 p1 rp1) (absurd (RespNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p2)
    ((NthHere _ _ _) (let-match erased q (NthHere _ _ _)) p1))
  (let-match erased q (NthThere _ _ _ _ _ q2))
  (respects-nth lab xs1 ls1 i1 j l rp1 p2 q2))

(def-fns _ $ (erased respects-lab : (erased (List (Nat)) lab lab2 xs ls) (erased (Nat) a) (subterm erased (Respects lab xs ls) rp)
    (erased (Snoc (Nat) lab a lab2) sn) -> (erased (Respects lab2 xs ls) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l p rp1) ((RespNil _) (RespNil lab2)))
  (RespCons lab2 xs1 ls1 j l (snoc-old _ lab lab2 a l j sn p) (respects-lab lab lab2 xs1 ls1 a rp1 sn)))

(def-fns _ $ (erased respects-setnth : (erased (List (Nat)) lab xs xs2 ls) (erased (Nat) i y l) (subterm erased (Respects lab xs ls) rp)
    (erased (SetNth (Nat) xs i y xs2) s) (erased (Nth (Nat) ls i l) q) (erased (Nth (Nat) lab y l) py) -> (erased (Respects lab xs2 ls) r))
  (let-match erased rp (RespCons _ xs1 ls1 j l1 p rp1) (absurd (RespNil _) q))
  (match erased s _
    ((SetHere _ _ _ _) (let-match erased q (NthHere _ _ _)) (RespCons lab xs1 ls1 y l py rp1))
    ((SetThere _ _ _ i1 _ xs3 s1)
      (let-match erased q (NthThere _ _ _ _ _ q1))
      (RespCons lab xs3 ls1 j l1 p (respects-setnth lab xs1 xs3 ls1 i1 y l rp1 s1 q1 py)))))

(def-fns _ $ (erased respects-snoc : (erased (List (Nat)) lab xs xs2 ls ls2) (erased (Nat) c l) (subterm erased (Respects lab xs ls) rp)
    (erased (Nth (Nat) lab c l) pc) (erased (Snoc (Nat) xs c xs2) s1) (erased (Snoc (Nat) ls l ls2) s2) -> (erased (Respects lab xs2 ls2) r))
  (match erased rp _
    ((RespNil _)
      (let-match erased s1 (SnocNil _ _))
      (let-match erased s2 (SnocNil _ _))
      (RespCons lab _ _ c l pc (RespNil lab)))
    ((RespCons _ xs1 ls1 j l1 p rp1)
      (let-match erased s1 (SnocCons _ _ _ _ xs3 s3))
      (let-match erased s2 (SnocCons _ _ _ _ ls3 s4))
      (RespCons lab xs3 ls3 j l1 p (respects-snoc lab xs1 xs3 ls1 ls3 c l rp1 pc s3 s4)))))

; A dart inserted after d takes d's label.
(def-fns _ $ (erased respects-insert : (erased (List (Nat)) lab lab2 nd nd2) (erased (Nat) d x n l)
    (erased (Respects lab nd lab) rp) (erased (Insert nd d x nd2) i) (erased (Length (Nat) lab x) len)
    (erased (Nth (Nat) lab d l) pd) (erased (Snoc (Nat) lab l lab2) sn) -> (erased (Respects lab2 nd2 lab2) r))
  (let-match erased i (MkInsert _ nd1 _ _ _ c pc s q))
  (let ((erased rp2)) (respects-lab lab lab2 nd lab l rp sn))
  (let ((erased pc2)) (snoc-old _ lab lab2 l l c sn (respects-nth lab nd lab d c l rp pc pd)))
  (let ((erased rp3)) (respects-setnth lab2 nd nd1 lab d x l rp2 s pd (snoc-new _ lab lab2 l x sn len)))
  (respects-snoc lab2 nd1 nd2 lab lab2 c l rp3 pc2 q sn))

(def-fns _ $ (erased respects-new : (erased (List (Nat)) lab lab2 nd nd2) (erased (Nat) x l)
    (erased (Respects lab nd lab) rp) (erased (Snoc (Nat) nd x nd2) i) (erased (Length (Nat) lab x) len)
    (erased (Snoc (Nat) lab l lab2) sn) -> (erased (Respects lab2 nd2 lab2) r))
  (respects-snoc lab2 nd nd2 lab lab2 x l (respects-lab lab lab2 nd lab l rp sn) (snoc-new _ lab lab2 l x sn len) i sn))

(def-adts $ (NodeReach : ((List (Nat)) nd) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many NRHere : (erased (List (Nat)) nd) (erased (Nat) a) -> (NodeReach nd a a))
  (many NRStep : (erased (List (Nat)) nd) (erased (Nat) a b c)
      (erased (Nth (Nat) nd a b) pn) (erased (NodeReach nd b c) r) -> (NodeReach nd a c)))

(def-fns _ $ (erased nr-snoc : (erased (List (Nat)) nd) (erased (Nat) a b c) (subterm erased (NodeReach nd a b) r)
    (erased (Nth (Nat) nd b c) p) -> (erased (NodeReach nd a c) r2))
  (let-match erased r (NRStep _ _ b1 _ p1 r1) ((NRHere _ _) (NRStep nd a c c p (NRHere nd c))))
  (NRStep nd a b1 c p1 (nr-snoc nd b1 b c r1 p)))

; An insertion after d turns the step out of d into two steps.
(def-fns _ $ (erased nr-insert : (erased (List (Nat)) nd nd2) (erased (Nat) d x a b) (subterm erased (NodeReach nd a b) r)
    (erased (Insert nd d x nd2) i) (erased (Length (Nat) nd x) len) -> (erased (NodeReach nd2 a b) r2))
  (let-match erased r (NRStep _ _ b1 _ p1 r1) ((NRHere _ _) (NRHere nd2 a)))
  (let ((erased rest)) (nr-insert nd nd2 d x b1 b r1 i len))
  (match erased (nat-cmp a d) _
    ((CLt _ _ _ _ lt) (NRStep nd2 a b1 b (insert-other nd nd2 d x a b1 i p1 (ApLt _ _ a d lt)) rest))
    ((CEq _ _ _)
      (NRStep nd2 a x b (insert-at nd nd2 a x i) (NRStep nd2 x b1 b (insert-new nd nd2 a x x b1 i len p1) rest)))
    ((CGt _ _ _ _ gt) (NRStep nd2 a b1 b (insert-other nd nd2 d x a b1 i p1 (ApGt _ _ a d gt)) rest))))

(def-fns _ $ (erased nr-grow : (erased (List (Nat)) nd nd2) (erased (Nat) c a b) (subterm erased (NodeReach nd a b) r)
    (erased (Snoc (Nat) nd c nd2) s) -> (erased (NodeReach nd2 a b) r2))
  (let-match erased r (NRStep _ _ b1 _ p1 r1) ((NRHere _ _) (NRHere nd2 a)))
  (NRStep nd2 a b1 b (snoc-old _ nd nd2 c b1 a s p1) (nr-grow nd nd2 c b1 b r1 s)))

; Dart i and those after it, labelled ls, are each reached along nd from their label's representative in rep.
(def-adts $ (Reps : ((List (Nat)) nd) ((List (Nat)) rep) ((Nat) i) ((List (Nat)) ls) -> Type)
  enum
  (many RepsNil : (erased (List (Nat)) nd rep) (erased (Nat) i) -> (Reps nd rep i (Nil (Nat))))
  (many RepsCons : (erased (List (Nat)) nd rep ls) (erased (Nat) i l r) (erased (Nth (Nat) rep l r) pr)
      (erased (NodeReach nd r i) reach) (erased (Reps nd rep (Succ i) ls) rest) -> (Reps nd rep i (Cons (Nat) l ls))))

(def-fns _ $ (erased reps-insert : (erased (List (Nat)) nd nd2 rep ls) (erased (Nat) d x i) (subterm erased (Reps nd rep i ls) rs)
    (erased (Insert nd d x nd2) ins) (erased (Length (Nat) nd x) len) -> (erased (Reps nd2 rep i ls) r))
  (let-match erased rs (RepsCons _ _ ls1 _ l r pr reach rs1) ((RepsNil _ _ _) (RepsNil nd2 rep i)))
  (RepsCons nd2 rep ls1 i l r pr (nr-insert nd nd2 d x r i reach ins len) (reps-insert nd nd2 rep ls1 d x (Succ i) rs1 ins len)))

(def-fns _ $ (erased reps-grow : (erased (List (Nat)) nd nd2 rep ls) (erased (Nat) c i) (subterm erased (Reps nd rep i ls) rs)
    (erased (Snoc (Nat) nd c nd2) s) -> (erased (Reps nd2 rep i ls) r))
  (let-match erased rs (RepsCons _ _ ls1 _ l r pr reach rs1) ((RepsNil _ _ _) (RepsNil nd2 rep i)))
  (RepsCons nd2 rep ls1 i l r pr (nr-grow nd nd2 c r i reach s) (reps-grow nd nd2 rep ls1 c (Succ i) rs1 s)))

(def-fns _ $ (erased reps-rep : (erased (List (Nat)) nd rep rep2 ls) (erased (Nat) a i) (subterm erased (Reps nd rep i ls) rs)
    (erased (Snoc (Nat) rep a rep2) s) -> (erased (Reps nd rep2 i ls) r))
  (let-match erased rs (RepsCons _ _ ls1 _ l r pr reach rs1) ((RepsNil _ _ _) (RepsNil nd rep2 i)))
  (RepsCons nd rep2 ls1 i l r (snoc-old _ rep rep2 a r l s pr) reach (reps-rep nd rep rep2 ls1 a (Succ i) rs1 s)))

; Dart j = i + k, the next one after the k darts of ls, joins with label l.
(def-fns _ $ (erased reps-snoc : (erased (List (Nat)) nd rep ls ls2) (erased (Nat) i k j l r) (subterm erased (Reps nd rep i ls) rs)
    (erased (Length (Nat) ls k) len) (erased (Add k i j) a) (erased (Snoc (Nat) ls l ls2) s)
    (erased (Nth (Nat) rep l r) pr) (erased (NodeReach nd r j) reach) -> (erased (Reps nd rep i ls2) res))
  (match erased rs _
    ((RepsNil _ _ _)
      (let-match erased s (SnocNil _ _))
      (let-match erased len (LengthNil _))
      (let-match erased a (AddZero _))
      (RepsCons nd rep _ i l r pr reach (RepsNil nd rep (Succ i))))
    ((RepsCons _ _ ls1 _ l1 r1 pr1 reach1 rs1)
      (let-match erased s (SnocCons _ _ _ _ ls3 s1))
      (let-match erased len (LengthCons _ _ _ k1 len1))
      (let-match erased a (AddSucc _ _ j1 a1))
      (RepsCons nd rep ls3 i l1 r1 pr1 reach1
        (reps-snoc nd rep ls1 ls3 (Succ i) k1 j l r rs1 len1 (add-succ-right k1 i j1 a1) s1 pr reach)))))
