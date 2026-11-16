;! suppress warn SCons

(def-fns _ $ (many classify : (subterm many (List (Entry)) table) (many (Char) c) -> (many (Kind) k) (erased (Class table c k) p))
  (let-match many table (Cons _ e rest) ((Nil _) (values (KWord) (ClassWord c))))
  (let-match many e (MkEntry x d))
  (let-match many (char-eq c x) (Unequal _ _ _ _ a) ((Equal _ _ _) (values (KDelim d) (ClassHere c d rest))))
  (let ((many k) (erased p)) (tail $ classify rest c))
  (values k (ClassThere c x d k rest a p)))

(def-fns _ $ (many comment : (subterm many (String) text) -> (many (String) after) (erased (Comment text after) p))
  (let-match many text (SCons c rest) ((SNil) (values (SNil) (CommentEnd))))
  (let-match many (char-eq c #\newline) (Unequal _ _ _ _ a) ((Equal _ _ _) (values rest (CommentLine rest))))
  (let ((many after) (erased p)) (tail $ comment rest))
  (values after (CommentSkip c rest after a p)))

(def-fns _ $ (erased comment-sub : (erased (Char) x) (erased (String) text after) (subterm erased (Comment text after) p) ->
    (erased (Subterm (String) after (String) (SCons x text)) s))
  (match erased p _
    ((CommentEnd) (prove-subterm text (SCons x text)))
    ((CommentLine rest) (subterm-trans (prove-subterm rest text) (prove-subterm text (SCons x text))))
    ((CommentSkip c rest _ _ q) (subterm-trans (comment-sub c rest after q) (prove-subterm text (SCons x text))))))

(def-fns _ $ (many word : (subterm many (String) text) -> (many (String) w) (many (String) after) (erased (Word text w after) p))
  (let-match many text (SCons c rest) ((SNil) (values (SNil) (SNil) (WordEnd))))
  (let ((many k) (erased ck)) (classify delims c))
  (let-match many k (KWord) ((KDelim d) (values (SNil) text (WordStop c d rest ck))))
  (let ((many w) (many after) (erased p)) (notail $ word rest))
  (values (SCons c w) after (WordMore c rest w after ck p)))

(def-fns _ $ (erased word-sub : (erased (Char) x) (erased (String) text w after) (subterm erased (Word text w after) p) ->
    (erased (Subterm (String) after (String) (SCons x text)) s))
  (match erased p _
    ((WordEnd) (prove-subterm text (SCons x text)))
    ((WordStop _ _ _ _) (prove-subterm text (SCons x text)))
    ((WordMore c rest v _ _ q) (subterm-trans (word-sub c rest v after q) (prove-subterm text (SCons x text))))))

(def-fns _ $ (many tok-of : (many (String) w) -> (many (Tok) t) (erased (TokOf w t) p))
  (match many (str-eq w dollar) _
    ((Equal _ _ _) (values (TDollar) (TokDollar)))
    ((Unequal _ _ _ _ a) (values (TAtom w) (TokAtom w a)))))

(def-fns _ $ (many lex : (subterm many (String) text) -> (many (List (Tok)) toks) (erased (Lex text toks) p))
  (let-match many text (SCons c rest) ((SNil) (values (Nil _) (LexEnd))))
  (let ((many k) (erased ck)) (classify delims c))
  (let-match many k (KDelim d)
    ((KWord)
      (let ((many w) (many after) (erased q)) (word rest))
      (let ((many t) (erased o)) (tok-of (SCons c w)))
      (let ((many toks) (erased p)) (notail $ lex (subterm (word-sub c rest w after q)) after))
      (values (Cons _ t toks) (LexChar c k rest (Cons _ t toks) ck (AfterWord c rest w after t toks q o p)))))
  (match many d _
    ((DSpace)
      (let ((many toks) (erased p)) (tail $ lex rest))
      (values toks (LexChar c k rest toks ck (AfterSpace c rest toks p))))
    ((DOpen)
      (let ((many toks) (erased p)) (notail $ lex rest))
      (values (Cons _ (TOpen) toks) (LexChar c k rest (Cons _ (TOpen) toks) ck (AfterOpen c rest toks p))))
    ((DClose)
      (let ((many toks) (erased p)) (notail $ lex rest))
      (values (Cons _ (TClose) toks) (LexChar c k rest (Cons _ (TClose) toks) ck (AfterClose c rest toks p))))
    ((DSemi)
      (let ((many after) (erased q)) (comment rest))
      (let ((many toks) (erased p)) (tail $ lex (subterm (comment-sub c rest after q)) after))
      (values toks (LexChar c k rest toks ck (AfterSemi c rest after toks q p))))))

(def-adts $ (Parsed : ((List (Tok)) toks) -> Type)
  enum
  (many ParsedOk : (erased (List (Tok)) toks) (many (List (Form)) forms) (many (Ending) end) (erased (Items toks forms end) p) -> (Parsed toks))
  (many ParsedBad : (erased (List (Tok)) toks) (many (Mistake) m) (erased (ItemsFail toks m) p) -> (Parsed toks)))

(def-fns _ $ (erased items-sub : (erased (List (Tok)) toks after) (erased (List (Form)) forms) (subterm erased (Items toks forms (AtClose after)) p) ->
    (erased (Subterm (List (Tok)) after (List (Tok)) toks) s))
  (match erased p _
    ((ItemsClose _) (prove-subterm after toks))
    ((ItemsAtom _ ts fs _ q) (subterm-trans (items-sub ts after fs q) (prove-subterm ts toks)))
    ((ItemsOpen ts mid inner fs _ q r)
      (subterm-trans (items-sub mid after fs r) $ subterm-trans (items-sub ts mid inner q) (prove-subterm ts toks)))
    ((ItemsDollar ts _ inner q) (subterm-trans (items-sub ts after inner q) (prove-subterm ts toks)))))

(def-fns _ $ (many items : (subterm many (List (Tok)) toks) -> (many (Parsed toks) r))
  (let-match many toks (Cons _ t ts) ((Nil _) (ParsedOk _ (Nil _) (AtEnd) (ItemsEnd))))
  (match many t _
    ((TClose) (ParsedOk _ (Nil _) (AtClose ts) (ItemsClose ts)))
    ((TAtom a)
      (match many (notail $ items ts) _
        ((ParsedOk _ fs end p) (ParsedOk _ (Cons _ (FAtom a) fs) end (ItemsAtom a ts fs end p)))
        ((ParsedBad _ m p) (ParsedBad _ m (FailAtom a ts m p)))))
    ((TDollar)
      (let-match many (notail $ items ts) (ParsedOk _ inner end p) ((ParsedBad _ m p) (ParsedBad _ m (FailDollarInside ts m p))))
      (match many end _
        ((AtEnd) (ParsedBad _ (MissingCloseAfterDollar) (FailDollarEnd ts inner p)))
        ((AtClose after) (ParsedOk _ (Cons _ (FList inner) (Nil _)) end (ItemsDollar ts after inner p)))))
    ((TOpen)
      (let-match many (notail $ items ts) (ParsedOk _ inner end p) ((ParsedBad _ m p) (ParsedBad _ m (FailOpenInside ts m p))))
      (let-match many end (AtClose after) ((AtEnd) (ParsedBad _ (MissingClose) (FailOpenEnd ts inner p))))
      (let ((erased s)) (subterm-trans (items-sub ts after inner p) (prove-subterm ts toks)))
      (match many (notail $ items (subterm s) after) _
        ((ParsedOk _ fs end2 q) (ParsedOk _ (Cons _ (FList inner) fs) end2 (ItemsOpen ts after inner fs end2 p q)))
        ((ParsedBad _ m q) (ParsedBad _ m (FailOpenAfter ts after inner m p q)))))))

(def-fns _ $ (many read : (many (String) text) -> (many (Read text) r))
  (let ((many toks) (erased l)) (lex text))
  (let-match many (items toks) (ParsedOk _ forms end p) ((ParsedBad _ m p) (Rejected _ m (UnreadableItems text toks m l p))))
  (match many end _
    ((AtEnd) (Accepted _ forms (ReadsBy text toks forms l p)))
    ((AtClose after) (Rejected _ (UnexpectedClose) (UnreadableClose text toks after forms l p)))))
