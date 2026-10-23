(def-adts
  ((At : ((List (U8)) xs) ((Nat) o) ((String) w) -> Type)
    enum
    (many AtEnd : (erased (List (U8)) xs) (erased (Nat) o) -> (At xs o (SNil)))
    (many AtChar : (erased (List (U8)) xs) (erased (Nat) o) (erased (U8) u) (erased (String) w)
       (erased (Nth (U8) xs o u) here) (erased (At xs (Succ o) w) rest) -> (At xs o (SCons (MkChar u) w)))))

(def-adts
  ((Drop : ((List (U8)) xs) ((Nat) o) ((String) t) -> Type)
    enum
    (many DropEnd : (erased (List (U8)) xs) (erased (Nat) o) (erased (Length (U8) xs o) len) -> (Drop xs o (SNil)))
    (many DropChar : (erased (List (U8)) xs) (erased (Nat) o) (erased (U8) u) (erased (String) t)
       (erased (Nth (U8) xs o u) here) (erased (Drop xs (Succ o) t) rest) -> (Drop xs o (SCons (MkChar u) t)))))

(def-adts
  ((Boundary : ((String) t) -> Type)
    enum
    (many AtTextEnd : -> (Boundary (SNil)))
    (many AtNewline : (erased (String) r) -> (Boundary (SCons #\newline r)))))

(def-adts
  ((StartOk : ((List (U8)) xs) ((Nat) s) -> Type)
    enum
    (many AtStart : (erased (List (U8)) xs) -> (StartOk xs (Zero)))
    (many PastNewline : (erased (List (U8)) xs) (erased (Nat) s) (erased (U8) u) (erased (Nth (U8) xs s u) here)
       (erased (Eq (Char) (MkChar u) #\newline) nl) -> (StartOk xs (Succ s)))))

(def-adts
  ((ByteKind : ((U8) b) -> Type)
    enum
    (many NewlineByte : (erased (U8) b) (erased (Eq (Char) (MkChar b) #\newline) e) -> (ByteKind b))
    (many OtherByte : (erased (U8) b) (erased (NotNewline (MkChar b)) nl) -> (ByteKind b))))

(def-fns _ $ (many classify : (many (U8) b) -> (many (ByteKind b) r))
  (let-match many b (MkU8 n p))
  (let-match many (nat-cmp n 10) (CEq _ _ _)
    ((CLt _ _ _ _ lt) (OtherByte b (BeforeNewline n p lt)))
    ((CGt _ _ _ _ gt) (OtherByte b (AfterNewline n p gt))))
  (let-match erased #\newline (MkChar u0))
  (let-match erased u0 (MkU8 n0 p0))
  (let-match erased (lt-unique n0 u8-modulus p p0) (Refl _ _))
  (NewlineByte b (Refl _ (MkChar b))))

(def-fns _ $ (erased drop-unshift : (erased (List (U8)) xs) (erased (U8) u) (erased (Nat) o) (erased (String) t)
    (subterm erased (Drop (Cons (U8) u xs) (Succ o) t) d) -> (erased (Drop xs o t) r))
  (match erased d _
    ((DropEnd _ _ len) (let-match erased len (LengthCons _ _ _ _ len1)) (DropEnd xs o len1))
    ((DropChar _ _ c t1 here rest)
      (let-match erased here (NthThere _ _ _ _ _ here1))
      (DropChar xs o c t1 here1 (drop-unshift xs u (Succ o) t1 rest)))))

(def-fns _ $ (erased drop-zero : (erased (String) text) (erased (List (U8)) xs) (subterm erased (StrBytes text xs) sb)
    (erased (String) t) (erased (Drop xs (Zero) t) d) -> (erased (Eq (String) t text) e))
  (match erased sb _
    ((SBNil) (let-match erased d (DropEnd _ _ _) (absurd (DropChar _ _ _ _ here _) here)) (Refl _ t))
    ((SBCons u text1 xs1 sb1)
      (let-match erased d (DropChar _ _ _ t1 here rest) (absurd (DropEnd _ _ len) len))
      (let-match erased here (NthHere _ _ _))
      (let-match erased (drop-zero text1 xs1 sb1 t1 (drop-unshift xs1 u (Zero) t1 rest)) (Refl _ _))
      (Refl _ t))))

(def-fns _ $ (erased drop-le : (erased (List (U8)) xs) (erased (Nat) o) (erased (Nat) n) (erased (String) t)
    (subterm erased (Drop xs o t) d) (erased (Length (U8) xs n) ln) -> (erased (Lt o (Succ n)) r))
  (match erased d _
    ((DropEnd _ _ len) (let-match erased (length-fn _ xs o n len ln) (Refl _ _)) (lt-succ o))
    ((DropChar _ _ _ t1 _ rest)
      (let-match erased (drop-le xs (Succ o) n t1 rest ln) (LtS _ _ lt))
      (lt-weaken _ _ lt))))

(def-fns _ $ (erased drop-word-at : (erased (List (U8)) xs) (erased (Nat) s) (erased (String) wt) (erased (Drop xs s wt) dw)
    (erased (String) w) (erased (String) t) (subterm erased (WordThen wt w t) wth) -> (erased (At xs s w) r))
  (match erased wth _
    ((LastChar _ _) (let-match erased dw (DropChar _ _ u _ here _)) (AtChar xs s u (SNil) here (AtEnd _ _)))
    ((EndOfLine _ _ _) (let-match erased dw (DropChar _ _ u _ here _)) (AtChar xs s u (SNil) here (AtEnd _ _)))
    ((MoreChars _ t1 w1 _ _ more)
      (let-match erased dw (DropChar _ _ u _ here rest))
      (AtChar xs s u w1 here (drop-word-at xs (Succ s) t1 rest w1 t more)))))

(def-fns _ $ (erased word-splice : (erased (List (U8)) xs) (erased (Nat) s) (erased (Nat) k) (erased (List (U8)) ys)
    (subterm erased (Splice (U8) xs s k ys xs) sp)
    (erased (String) wt) (erased (Drop xs s wt) dw) (erased (String) w) (erased (String) t) (erased (WordThen wt w t) wth) (erased (StrLength w k) lw)
    -> (erased (StrBytes w ys) r))
  (match erased sp _
    (absurd (SpliceNil _ _) (let-match erased lw (SLenNil)) wth)
    ((SpliceThere _ x xs1 i _ _ _ p)
      (word-splice xs1 i k ys p wt (drop-unshift xs1 x i wt dw) w t wth lw))
    ((SpliceHere _ x _ xs1 k1 ys1 _ p)
      (let-match erased dw (DropChar _ _ _ wt1 here rest) (absurd (DropEnd _ _ _) wth))
      (let-match erased here (NthHere _ _ _))
      (let ((erased dw1)) (drop-unshift xs1 x (Zero) wt1 rest))
      (match erased wth _
        ((LastChar _ _) (let-match erased lw (SLenCons _ _ _ lw1)) (let-match erased lw1 (SLenNil)) (let-match erased p (SpliceNil _ _))
          (SBCons x (SNil) (Nil (U8)) (SBNil)))
        ((EndOfLine _ _ _) (let-match erased lw (SLenCons _ _ _ lw1)) (let-match erased lw1 (SLenNil)) (let-match erased p (SpliceNil _ _))
          (SBCons x (SNil) (Nil (U8)) (SBNil)))
        ((MoreChars _ t2 w2 _ _ more)
          (let-match erased lw (SLenCons _ _ _ lw1))
          (SBCons x w2 ys1 (word-splice xs1 (Zero) k1 ys1 p t2 dw1 w2 t more lw1)))))))

(def-fns _ $ (erased strbytes-fn : (erased (String) a) (erased (String) b) (erased (List (U8)) ys)
    (subterm erased (StrBytes a ys) pa) (erased (StrBytes b ys) pb) -> (erased (Eq (String) a b) e))
  (match erased pa _
    ((SBNil) (let-match erased pb (SBNil)) (Refl _ a))
    ((SBCons u a1 ys1 pa1)
      (let-match erased pb (SBCons _ b1 _ pb1))
      (let-match erased (strbytes-fn a1 b1 ys1 pa1 pb1) (Refl _ _))
      (Refl _ a))))

(def-fns _ $ (erased first-char : (erased (String) t) (erased (Char) c) (erased (Boundary t) bd) (erased (NotNewline c) nl)
    -> (erased (WordThen (SCons c t) (SCons c (SNil)) t) r))
  (match erased bd _
    ((AtTextEnd) (LastChar c nl))
    ((AtNewline r) (EndOfLine c r nl))))

(def-fns _ $ (erased add-cancel-left : (erased (Nat) a) (erased (Nat) b1) (erased (Nat) b2) (erased (Nat) c)
    (subterm erased (Add a b1 c) p) (erased (Add a b2 c) q) -> (erased (Eq (Nat) b1 b2) e))
  (match erased p _
    ((AddZero _) (let-match erased q (AddZero _)) (Refl _ b1))
    ((AddSucc a1 _ c1 p1) (let-match erased q (AddSucc _ _ _ q1)) (add-cancel-left a1 b1 b2 c1 p1 q1))))

(def-fns _ $ (many word-back : (erased (List (U8)) xs) (many (Bytes xs) bs) (erased (Nat) n) (erased (Length (U8) xs n) ln)
    (subterm many (Nat) i) (erased (String) wt) (erased (Drop xs i wt) dw) (erased (String) w) (erased (String) t) (erased (WordThen wt w t) wth)
    (many (Nat) k) (erased (StrLength w k) lw) (erased (Nat) o) (erased (Add i k o) a)
    -> (many (Nat) k2) (erased (Nat) s) (erased (String) wt2) (erased (Drop xs s wt2) dw2) (erased (String) w2) (erased (WordThen wt2 w2 t) wth2)
    (erased (StrLength w2 k2) lw2) (erased (StartOk xs s) ok) (erased (Add s k2 o) a2))
  (let-match many i (Succ i1) ((Zero) (values k i wt dw w wth lw (AtStart xs) a)))
  (let-match erased (drop-le xs i n wt dw ln) (LtS _ _ lt))
  (let ((erased x) (erased nth)) (nth-exists _ xs n i1 ln lt))
  (let ((many b)) (bytes-get-many xs bs i1 x nth))
  (let-match erased a (AddSucc _ _ o1 a1))
  (match many (classify b) _
    ((NewlineByte _ e) (values k i wt dw w wth lw (PastNewline xs i1 b nth e) (AddSucc i1 k o1 a1)))
    ((OtherByte _ nl)
      (tail $ word-back xs bs n ln i1 (SCons (MkChar b) wt) (DropChar xs i1 b wt nth dw) (SCons (MkChar b) w) t (MoreChars (MkChar b) wt w t nl wth)
        (Succ k) (SLenCons (MkChar b) w k lw) o (add-succ-right i1 k o1 a1)))))

(def-fns _ $ (many word-string : (erased (List (U8)) xs) (many (Bytes xs) bs) (erased (Nat) n) (erased (Length (U8) xs n) ln)
    (many (Nat) s) (many (Nat) k) (erased (Nat) e) (erased (Add s k e) sum) (erased (Lt e (Succ n)) le)
    (erased (String) wt) (erased (Drop xs s wt) dw) (erased (String) w) (erased (String) t) (erased (WordThen wt w t) wth) (erased (StrLength w k) lw)
    -> (many w is v))
  (let ((erased ys) (erased sp)) (splice-range _ xs n ln s k e sum le))
  (let ((unique c)) (bytes-sub xs bs s k ys sp))
  (let ((many cs)) (share c))
  (let ((many str) (erased sb)) (bytes-str ys cs))
  (let-match erased (strbytes-fn _ _ _ sb (word-splice xs s k ys sp wt dw w t wth lw)) (Refl _ _))
  str)

(def-fns _ $ (many lines-of : (erased (String) text) (erased (List (U8)) xs) (many (Bytes xs) bs) (erased (Nat) n) (erased (Length (U8) xs n) ln)
    (erased (StrBytes text xs) sbt)
    (subterm many (Nat) o) (erased (String) t) (erased (Drop xs o t) dt) (erased (Boundary t) bd)
    (many (List (String)) acc) (erased (Words t acc) wa)
    -> (many (List (String)) ws) (erased (Words text ws) wd))
  (let-match many o (Succ o1)
    ((Zero) (let-match erased (drop-zero text xs sbt t dt) (Refl _ _)) (values acc wa)))
  (let ((erased le)) (drop-le xs o n t dt ln))
  (let-match erased le (LtS _ _ lt))
  (let ((erased x) (erased nth)) (nth-exists _ xs n o1 ln lt))
  (let ((many b)) (bytes-get-many xs bs o1 x nth))
  (let-match many (classify b) (OtherByte _ nl)
    ((NewlineByte _ e)
      (let-match erased e (Refl _ _))
      (tail $ lines-of text xs bs n ln sbt o1 (SCons #\newline t) (DropChar xs o1 b t nth dt) (AtNewline t) acc (SkipNewline t acc wa))))
  (let ((many k) (erased s) (erased wt) (erased dw) (erased w) (erased wth) (erased lw) (erased ok) (erased sum))
    (word-back xs bs n ln o1 (SCons (MkChar b) t) (DropChar xs o1 b t nth dt) (SCons (MkChar b) (SNil)) t (first-char t (MkChar b) bd nl)
      (Succ (Zero)) (SLenCons (MkChar b) (SNil) (Zero) (SLenNil)) o (add-succ-right o1 (Zero) o1 (add-zero-right o1))))
  (let ((many sr) (erased sum2)) (sub o k (add-le-right s k o sum)))
  (let-match erased (add-cancel-left k sr s o sum2 (add-comm s k o sum)) (Refl _ _))
  (let ((many ws)) (word-string xs bs n ln sr k o sum le wt dw w t wth lw))
  (let ((erased wa2)) (TakeWord wt w t acc wth wa))
  (let-match many sr (Succ s1)
    ((Zero) (let-match erased (drop-zero text xs sbt wt dw) (Refl _ _)) (values (Cons _ ws acc) wa2)))
  (let-match erased ok (PastNewline _ _ u here e))
  (let-match erased e (Refl _ _))
  (let-match erased sum (AddSucc _ _ c1 a1))
  (let ((erased dec)) (lt-subterm s1 o (add-le-left s1 k c1 a1)))
  (tail $ lines-of text xs bs n ln sbt (subterm dec) s1 (SCons #\newline wt) (DropChar xs s1 u wt here dw) (AtNewline wt) (Cons _ ws acc) (SkipNewline wt _ wa2)))

(def-fns _ $ (many split-words : (many (String) text) -> (many (List (String)) ws) (erased (Words text ws) wd))
  (let ((erased xs) (unique b) (erased sbt)) (str-bytes-copy text))
  (let ((many bs)) (share b))
  (let ((many n) (erased ln)) (bytes-length-many xs bs))
  (lines-of text xs bs n ln sbt n (SNil) (DropEnd xs n ln) (AtTextEnd) (Nil _) (NoText)))
