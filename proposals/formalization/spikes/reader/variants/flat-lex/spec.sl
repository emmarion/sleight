(def-adts $ (Delim : -> Type)
  enum
  (many DSpace : -> (Delim))
  (many DOpen : -> (Delim))
  (many DClose : -> (Delim))
  (many DSemi : -> (Delim)))

(def-adts $ (Kind : -> Type)
  enum
  (many KWord : -> (Kind))
  (many KDelim : (many (Delim) d) -> (Kind)))

(def-adts $ (Entry : -> Type)
  enum
  (many MkEntry : (many (Char) c) (many (Delim) d) -> (Entry)))

(let ((many delims))
  (Cons _ (MkEntry #\space (DSpace)) $ Cons _ (MkEntry #\newline (DSpace)) $ Cons _ (MkEntry #\tab (DSpace)) $ Cons _ (MkEntry #\x0d (DSpace))
    $ Cons _ (MkEntry #\x28 (DOpen)) $ Cons _ (MkEntry #\x29 (DClose)) $ Cons _ (MkEntry #\x3b (DSemi)) $ Nil _))

(def-adts $ (Class : ((List (Entry)) table) ((Char) c) ((Kind) k) -> Type)
  enum
  (many ClassWord : (erased (Char) c) -> (Class (Nil (Entry)) c (KWord)))
  (many ClassHere : (erased (Char) c) (erased (Delim) d) (erased (List (Entry)) rest) -> (Class (Cons (Entry) (MkEntry c d) rest) c (KDelim d)))
  (many ClassThere : (erased (Char) c e) (erased (Delim) d) (erased (Kind) k) (erased (List (Entry)) rest)
     (erased (Apart (Char) CharLt c e) a) (erased (Class rest c k) p) -> (Class (Cons (Entry) (MkEntry e d) rest) c k)))

(def-adts $ (Tok : -> Type)
  enum
  (many TOpen : -> (Tok))
  (many TClose : -> (Tok))
  (many TDollar : -> (Tok))
  (many TAtom : (many (String) name) -> (Tok)))

(def-adts $ (Comment : ((String) text) ((String) after) -> Type)
  enum
  (many CommentEnd : -> (Comment (SNil) (SNil)))
  (many CommentLine : (erased (String) rest) -> (Comment (SCons #\newline rest) rest))
  (many CommentSkip : (erased (Char) c) (erased (String) rest after) (erased (Apart (Char) CharLt c #\newline) a) (erased (Comment rest after) p)
     -> (Comment (SCons c rest) after)))

(def-adts $ (Word : ((String) text) ((String) w) ((String) after) -> Type)
  enum
  (many WordEnd : -> (Word (SNil) (SNil) (SNil)))
  (many WordStop : (erased (Char) c) (erased (Delim) d) (erased (String) rest) (erased (Class delims c (KDelim d)) k)
     -> (Word (SCons c rest) (SNil) (SCons c rest)))
  (many WordMore : (erased (Char) c) (erased (String) rest w after) (erased (Class delims c (KWord)) k) (erased (Word rest w after) p)
     -> (Word (SCons c rest) (SCons c w) after)))

(def-adts $ (TokOf : ((String) w) ((Tok) t) -> Type)
  enum
  (many TokDollar : -> (TokOf "$" (TDollar)))
  (many TokAtom : (erased (String) w) (erased (Apart (String) StrLt w "$") a) -> (TokOf w (TAtom w))))

(def-adts $ (Lex : ((String) text) ((List (Tok)) toks) -> Type)
  enum
  (many LexEnd : -> (Lex (SNil) (Nil (Tok))))
  (many LexSpace : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks)
     (erased (Class delims c (KDelim (DSpace))) k) (erased (Lex rest toks) p) -> (Lex (SCons c rest) toks))
  (many LexOpen : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks)
     (erased (Class delims c (KDelim (DOpen))) k) (erased (Lex rest toks) p) -> (Lex (SCons c rest) (Cons (Tok) (TOpen) toks)))
  (many LexClose : (erased (Char) c) (erased (String) rest) (erased (List (Tok)) toks)
     (erased (Class delims c (KDelim (DClose))) k) (erased (Lex rest toks) p) -> (Lex (SCons c rest) (Cons (Tok) (TClose) toks)))
  (many LexComment : (erased (Char) c) (erased (String) rest after) (erased (List (Tok)) toks)
     (erased (Class delims c (KDelim (DSemi))) k) (erased (Comment rest after) q) (erased (Lex after toks) p) -> (Lex (SCons c rest) toks))
  (many LexWord : (erased (Char) c) (erased (String) rest w after) (erased (Tok) t) (erased (List (Tok)) toks)
     (erased (Class delims c (KWord)) k) (erased (Word rest w after) q) (erased (TokOf (SCons c w) t) o) (erased (Lex after toks) p)
     -> (Lex (SCons c rest) (Cons (Tok) t toks))))

(def-adts $ (Form : -> Type)
  enum
  (many FAtom : (many (String) name) -> (Form))
  (many FList : (many (List (Form)) items) -> (Form)))

(def-adts $ (Ending : -> Type)
  enum
  (many AtEnd : -> (Ending))
  (many AtClose : (many (List (Tok)) after) -> (Ending)))

(def-adts $ (Items : ((List (Tok)) toks) ((List (Form)) forms) ((Ending) end) -> Type)
  enum
  (many ItemsEnd : -> (Items (Nil (Tok)) (Nil (Form)) (AtEnd)))
  (many ItemsClose : (erased (List (Tok)) after) -> (Items (Cons (Tok) (TClose) after) (Nil (Form)) (AtClose after)))
  (many ItemsAtom : (erased (String) a) (erased (List (Tok)) ts) (erased (List (Form)) fs) (erased (Ending) end) (erased (Items ts fs end) p)
     -> (Items (Cons (Tok) (TAtom a) ts) (Cons (Form) (FAtom a) fs) end))
  (many ItemsOpen : (erased (List (Tok)) ts after) (erased (List (Form)) inner fs) (erased (Ending) end)
     (erased (Items ts inner (AtClose after)) p) (erased (Items after fs end) q)
     -> (Items (Cons (Tok) (TOpen) ts) (Cons (Form) (FList inner) fs) end))
  (many ItemsDollar : (erased (List (Tok)) ts after) (erased (List (Form)) inner) (erased (Items ts inner (AtClose after)) p)
     -> (Items (Cons (Tok) (TDollar) ts) (Cons (Form) (FList inner) (Nil (Form))) (AtClose after))))

(def-adts $ (Mistake : -> Type)
  enum
  (many MissingClose : -> (Mistake))
  (many MissingCloseAfterDollar : -> (Mistake))
  (many UnexpectedClose : -> (Mistake)))

(def-adts $ (ItemsFail : ((List (Tok)) toks) ((Mistake) m) -> Type)
  enum
  (many FailAtom : (erased (String) a) (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TAtom a) ts) m))
  (many FailOpenInside : (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TOpen) ts) m))
  (many FailOpenEnd : (erased (List (Tok)) ts) (erased (List (Form)) inner) (erased (Items ts inner (AtEnd)) p)
     -> (ItemsFail (Cons (Tok) (TOpen) ts) (MissingClose)))
  (many FailOpenAfter : (erased (List (Tok)) ts after) (erased (List (Form)) inner) (erased (Mistake) m)
     (erased (Items ts inner (AtClose after)) p) (erased (ItemsFail after m) q) -> (ItemsFail (Cons (Tok) (TOpen) ts) m))
  (many FailDollarInside : (erased (List (Tok)) ts) (erased (Mistake) m) (erased (ItemsFail ts m) p) -> (ItemsFail (Cons (Tok) (TDollar) ts) m))
  (many FailDollarEnd : (erased (List (Tok)) ts) (erased (List (Form)) inner) (erased (Items ts inner (AtEnd)) p)
     -> (ItemsFail (Cons (Tok) (TDollar) ts) (MissingCloseAfterDollar))))

(def-adts $ (Reads : ((String) text) ((List (Form)) forms) -> Type)
  enum
  (many ReadsBy : (erased (String) text) (erased (List (Tok)) toks) (erased (List (Form)) forms)
     (erased (Lex text toks) l) (erased (Items toks forms (AtEnd)) p) -> (Reads text forms)))

(def-adts $ (Unreadable : ((String) text) ((Mistake) m) -> Type)
  enum
  (many UnreadableItems : (erased (String) text) (erased (List (Tok)) toks) (erased (Mistake) m)
     (erased (Lex text toks) l) (erased (ItemsFail toks m) p) -> (Unreadable text m))
  (many UnreadableClose : (erased (String) text) (erased (List (Tok)) toks after) (erased (List (Form)) forms)
     (erased (Lex text toks) l) (erased (Items toks forms (AtClose after)) p) -> (Unreadable text (UnexpectedClose))))

(def-adts $ (Read : ((String) text) -> Type)
  enum
  (many Accepted : (erased (String) text) (many (List (Form)) forms) (erased (Reads text forms) p) -> (Read text))
  (many Rejected : (erased (String) text) (many (Mistake) m) (erased (Unreadable text m) p) -> (Read text)))

(def-adts $ (Reader : -> Type)
  enum
  (many MkReader : (erased (Level) L N D)
     (many (Fn L (many (String) text) -> (many (Read text) r)) read)
     (erased (Fn N (erased (String) text) (erased (List (Form)) forms) (erased (Mistake) m)
                   (erased (Reads text forms) p) (erased (Unreadable text m) q) -> (erased (False) f)) never-both)
     (erased (Fn D (erased (String) text) (erased (List (Form)) f1 f2)
                   (erased (Reads text f1) p) (erased (Reads text f2) q) -> (erased (Eq (List (Form)) f1 f2) e)) deterministic)
     -> (Reader)))

(goal many (Reader))
