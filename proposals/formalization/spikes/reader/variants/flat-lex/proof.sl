(def-fns _ $ (erased char-lt-irrefl : (erased (Char) c) (erased (CharLt c c) p) -> (erased (False) f))
  (let-match erased p (MkCharLt m _ _ _ lt))
  (lt-asym m m lt (lt-succ m)))

(def-fns _ $ (erased char-apart-irrefl : (erased (Char) c) (erased (Apart (Char) CharLt c c) a) -> (erased (False) f))
  (match erased a _
    ((ApLt _ _ _ _ p) (char-lt-irrefl c p))
    ((ApGt _ _ _ _ p) (char-lt-irrefl c p))))

(def-fns _ $ (erased str-lt-irrefl : (erased (String) s) (subterm erased (StrLt s s) p) -> (erased (False) f))
  (match erased p _
    ((SLtHead c _ _ _ q) (char-lt-irrefl c q))
    ((SLtTail _ t _ q) (str-lt-irrefl t q))))

(def-fns _ $ (erased str-apart-irrefl : (erased (String) s) (erased (Apart (String) StrLt s s) a) -> (erased (False) f))
  (match erased a _
    ((ApLt _ _ _ _ p) (str-lt-irrefl s p))
    ((ApGt _ _ _ _ p) (str-lt-irrefl s p))))

(def-fns _ $ (erased class-fn : (erased (List (Entry)) table) (erased (Char) c) (erased (Kind) k1 k2)
    (subterm erased (Class table c k1) p) (erased (Class table c k2) q) -> (erased (Eq (Kind) k1 k2) e))
  (match erased p _
    ((ClassWord _) (match erased q _ ((ClassWord _) (Refl _ _))))
    ((ClassHere _ _ _)
      (match erased q _
        ((ClassHere _ _ _) (Refl _ _))
        (absurd (ClassThere _ _ _ _ _ a _) (char-apart-irrefl c a))))
    ((ClassThere _ _ _ _ rest a p2)
      (match erased q _
        (absurd (ClassHere _ _ _) (char-apart-irrefl c a))
        ((ClassThere _ _ _ _ _ _ q2) (class-fn rest c k1 k2 p2 q2))))))

(def-fns _ $ (erased comment-fn : (erased (String) text a1 a2) (subterm erased (Comment text a1) p) (erased (Comment text a2) q) ->
    (erased (Eq (String) a1 a2) e))
  (match erased p _
    ((CommentEnd) (match erased q _ ((CommentEnd) (Refl _ _))))
    ((CommentLine _)
      (match erased q _
        ((CommentLine _) (Refl _ _))
        (absurd (CommentSkip _ _ _ a _) (char-apart-irrefl #\newline a))))
    ((CommentSkip _ rest _ a p2)
      (match erased q _
        (absurd (CommentLine _) (char-apart-irrefl #\newline a))
        ((CommentSkip _ _ _ _ q2) (comment-fn rest a1 a2 p2 q2))))))

(def-fns _ $ (erased word-fn : (erased (String) text w1 a1 w2 a2) (subterm erased (Word text w1 a1) p) (erased (Word text w2 a2) q) ->
    (erased (Eq (String) w1 w2) e) (erased (Eq (String) a1 a2) f))
  (match erased p _
    ((WordEnd) (match erased q _ ((WordEnd) (values (Refl _ _) (Refl _ _)))))
    ((WordStop c _ _ k)
      (match erased q _
        ((WordStop _ _ _ _) (values (Refl _ _) (Refl _ _)))
        (absurd (WordMore _ _ _ _ k2 _) (class-fn delims c _ _ k k2))))
    ((WordMore c rest v1 _ k p2)
      (match erased q _
        (absurd (WordStop _ _ _ k2) (class-fn delims c _ _ k k2))
        ((WordMore _ _ v2 _ _ q2)
          (let ((erased e) (erased f)) (word-fn rest v1 a1 v2 a2 p2 q2))
          (let-match erased e (Refl _ _))
          (values (Refl _ _) f))))))

(def-fns _ $ (erased tok-fn : (erased (String) w) (erased (Tok) t1 t2) (erased (TokOf w t1) p) (erased (TokOf w t2) q) -> (erased (Eq (Tok) t1 t2) e))
  (match erased p _
    ((TokDollar)
      (match erased q _
        ((TokDollar) (Refl _ _))
        (absurd (TokAtom _ a) (str-apart-irrefl "$" a))))
    ((TokAtom _ a)
      (match erased q _
        (absurd (TokDollar) (str-apart-irrefl "$" a))
        ((TokAtom _ _) (Refl _ _))))))

(def-fns _ $ (erased lex-fn : (erased (String) text) (erased (List (Tok)) t1 t2) (subterm erased (Lex text t1) p) (erased (Lex text t2) q) ->
    (erased (Eq (List (Tok)) t1 t2) e))
  (match erased p _
    ((LexEnd) (match erased q _ ((LexEnd) (Refl _ _))))
    ((LexSpace c rest u1 k p2)
      (match erased q _
        ((LexSpace _ _ u2 _ q2) (lex-fn rest u1 u2 p2 q2))
        (absurd (LexOpen _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexClose _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexComment _ _ _ _ k2 _ _) (class-fn delims c _ _ k k2))
        (absurd (LexWord _ _ _ _ _ _ k2 _ _ _) (class-fn delims c _ _ k k2))))
    ((LexOpen c rest u1 k p2)
      (match erased q _
        (absurd (LexSpace _ _ _ k2 _) (class-fn delims c _ _ k k2))
        ((LexOpen _ _ u2 _ q2) (let-match erased (lex-fn rest u1 u2 p2 q2) (Refl _ _)) (Refl _ _))
        (absurd (LexClose _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexComment _ _ _ _ k2 _ _) (class-fn delims c _ _ k k2))
        (absurd (LexWord _ _ _ _ _ _ k2 _ _ _) (class-fn delims c _ _ k k2))))
    ((LexClose c rest u1 k p2)
      (match erased q _
        (absurd (LexSpace _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexOpen _ _ _ k2 _) (class-fn delims c _ _ k k2))
        ((LexClose _ _ u2 _ q2) (let-match erased (lex-fn rest u1 u2 p2 q2) (Refl _ _)) (Refl _ _))
        (absurd (LexComment _ _ _ _ k2 _ _) (class-fn delims c _ _ k k2))
        (absurd (LexWord _ _ _ _ _ _ k2 _ _ _) (class-fn delims c _ _ k k2))))
    ((LexComment c rest b1 _ k c1 p2)
      (match erased q _
        (absurd (LexSpace _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexOpen _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexClose _ _ _ k2 _) (class-fn delims c _ _ k k2))
        ((LexComment _ _ b2 _ _ c2 q2)
          (let-match erased (comment-fn rest b1 b2 c1 c2) (Refl _ _))
          (lex-fn b1 t1 t2 p2 q2))
        (absurd (LexWord _ _ _ _ _ _ k2 _ _ _) (class-fn delims c _ _ k k2))))
    ((LexWord c rest w1 b1 x1 u1 k r1 o1 p2)
      (match erased q _
        (absurd (LexSpace _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexOpen _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexClose _ _ _ k2 _) (class-fn delims c _ _ k k2))
        (absurd (LexComment _ _ _ _ k2 _ _) (class-fn delims c _ _ k k2))
        ((LexWord _ _ w2 b2 x2 u2 _ r2 o2 q2)
          (let ((erased e) (erased f)) (word-fn rest w1 b1 w2 b2 r1 r2))
          (let-match erased e (Refl _ _))
          (let-match erased f (Refl _ _))
          (let-match erased (tok-fn (SCons c w1) x1 x2 o1 o2) (Refl _ _))
          (let-match erased (lex-fn b1 u1 u2 p2 q2) (Refl _ _))
          (Refl _ _))))))

(def-fns _ $ (erased items-fn : (erased (List (Tok)) toks) (erased (List (Form)) f1 f2) (erased (Ending) e1 e2)
    (subterm erased (Items toks f1 e1) p) (erased (Items toks f2 e2) q) -> (erased (Eq (List (Form)) f1 f2) e) (erased (Eq (Ending) e1 e2) f))
  (match erased p _
    ((ItemsEnd) (match erased q _ ((ItemsEnd) (values (Refl _ _) (Refl _ _)))))
    ((ItemsClose _) (match erased q _ ((ItemsClose _) (values (Refl _ _) (Refl _ _)))))
    ((ItemsAtom _ ts g1 _ p2)
      (match erased q _
        ((ItemsAtom _ _ g2 _ q2)
          (let ((erased e) (erased f)) (items-fn ts g1 g2 e1 e2 p2 q2))
          (let-match erased e (Refl _ _))
          (values (Refl _ _) f))))
    ((ItemsOpen ts m1 i1 g1 _ p2 p3)
      (match erased q _
        ((ItemsOpen _ m2 i2 g2 _ q2 q3)
          (let ((erased e) (erased f)) (items-fn ts i1 i2 (AtClose m1) (AtClose m2) p2 q2))
          (let-match erased e (Refl _ _))
          (let-match erased f (Refl _ _))
          (let ((erased e3) (erased f3)) (items-fn m1 g1 g2 e1 e2 p3 q3))
          (let-match erased e3 (Refl _ _))
          (values (Refl _ _) f3))))
    ((ItemsDollar ts m1 i1 p2)
      (match erased q _
        ((ItemsDollar _ m2 i2 q2)
          (let ((erased e) (erased f)) (items-fn ts i1 i2 (AtClose m1) (AtClose m2) p2 q2))
          (let-match erased e (Refl _ _))
          (values (Refl _ _) f))))))

(def-fns _ $ (erased items-excl : (erased (List (Tok)) toks) (erased (List (Form)) forms) (erased (Ending) end) (erased (Mistake) m)
    (subterm erased (Items toks forms end) p) (erased (ItemsFail toks m) q) -> (erased (False) f))
  (match erased p _
    ((ItemsEnd) (match erased q _))
    ((ItemsClose _) (match erased q _))
    ((ItemsAtom _ ts fs _ p2) (match erased q _ ((FailAtom _ _ _ q2) (items-excl ts fs end m p2 q2))))
    ((ItemsOpen ts mid inner fs _ p2 p3)
      (match erased q _
        ((FailOpenInside _ _ q2) (items-excl ts inner (AtClose mid) m p2 q2))
        ((FailOpenEnd _ i2 q2)
          (let ((erased _) (erased f)) (items-fn ts inner i2 (AtClose mid) (AtEnd) p2 q2))
          (match erased f _))
        ((FailOpenAfter _ m2 i2 _ q2 q3)
          (let ((erased _) (erased f)) (items-fn ts inner i2 (AtClose mid) (AtClose m2) p2 q2))
          (let-match erased f (Refl _ _))
          (items-excl mid fs end m p3 q3))))
    ((ItemsDollar ts mid inner p2)
      (match erased q _
        ((FailDollarInside _ _ q2) (items-excl ts inner (AtClose mid) m p2 q2))
        ((FailDollarEnd _ i2 q2)
          (let ((erased _) (erased f)) (items-fn ts inner i2 (AtClose mid) (AtEnd) p2 q2))
          (match erased f _))))))

(def-fns _ $ (erased never-both : (erased (String) text) (erased (List (Form)) forms) (erased (Mistake) m)
    (erased (Reads text forms) p) (erased (Unreadable text m) q) -> (erased (False) f))
  (let-match erased p (ReadsBy _ t1 _ l1 i1))
  (match erased q _
    ((UnreadableItems _ t2 _ l2 i2)
      (let-match erased (lex-fn text t1 t2 l1 l2) (Refl _ _))
      (items-excl t1 forms (AtEnd) m i1 i2))
    ((UnreadableClose _ t2 after f2 l2 i2)
      (let-match erased (lex-fn text t1 t2 l1 l2) (Refl _ _))
      (let ((erased _) (erased f)) (items-fn t1 forms f2 (AtEnd) (AtClose after) i1 i2))
      (match erased f _))))

(def-fns _ $ (erased deterministic : (erased (String) text) (erased (List (Form)) f1 f2)
    (erased (Reads text f1) p) (erased (Reads text f2) q) -> (erased (Eq (List (Form)) f1 f2) e))
  (let-match erased p (ReadsBy _ t1 _ l1 i1))
  (let-match erased q (ReadsBy _ t2 _ l2 i2))
  (let-match erased (lex-fn text t1 t2 l1 l2) (Refl _ _))
  (let ((erased e) (erased _)) (items-fn t1 f1 f2 (AtEnd) (AtEnd) i1 i2))
  e)
