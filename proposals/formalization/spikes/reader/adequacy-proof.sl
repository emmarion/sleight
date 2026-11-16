(def-adts $ (Follows : ((Ending) end) ((List (Tok)) more) -> Type)
  enum
  (many FollowsEnd : -> (Follows (AtEnd) (Nil (Tok))))
  (many FollowsClose : (erased (List (Tok)) after) -> (Follows (AtClose after) (Cons (Tok) (TClose) after))))

(def-fns _ $ (erased items-prints : (erased (List (Tok)) toks more) (erased (List (Form)) forms) (erased (Ending) end)
    (subterm erased (Items toks forms end) p) (erased (Follows end more) w) -> (erased (Prints forms toks more) q))
  (match erased p _
    ((ItemsEnd) (let-match erased w (FollowsEnd)) (PrintsNone more))
    ((ItemsClose _) (let-match erased w (FollowsClose _)) (PrintsNone more))
    ((ItemsAtom a ts fs _ p2) (PrintsAtom a fs ts more (items-prints ts more fs end p2 w)))
    ((ItemsOpen ts mid inner fs _ p2 p3)
      (PrintsList inner fs ts mid more
        (items-prints ts (Cons _ (TClose) mid) inner (AtClose mid) p2 (FollowsClose mid))
        (items-prints mid more fs end p3 w)))
    ((ItemsDollar ts after inner p2)
      (let-match erased w (FollowsClose _))
      (PrintsDollar inner ts after (items-prints ts more inner end p2 w)))))

(def-fns _ $ (erased prints-items : (erased (List (Tok)) toks more) (erased (List (Form)) forms) (erased (Ending) end)
    (subterm erased (Prints forms toks more) p) (erased (Follows end more) w) -> (erased (Items toks forms end) q))
  (match erased p _
    ((PrintsNone _) (match erased w _ ((FollowsEnd) (ItemsEnd)) ((FollowsClose after) (ItemsClose after))))
    ((PrintsAtom a fs ts _ p2) (ItemsAtom a ts fs end (prints-items ts more fs end p2 w)))
    ((PrintsList inner fs ts mid _ p2 p3)
      (ItemsOpen ts mid inner fs end
        (prints-items ts (Cons _ (TClose) mid) inner (AtClose mid) p2 (FollowsClose mid))
        (prints-items mid more fs end p3 w)))
    ((PrintsDollar inner ts after p2)
      (let-match erased w (FollowsClose _))
      (ItemsDollar ts after inner (prints-items ts more inner end p2 w)))))

(def-fns _ $ (erased reading-prints : (erased (List (Tok)) toks) (erased (List (Form)) forms)
    (erased (Items toks forms (AtEnd)) p) -> (erased (Prints forms toks (Nil (Tok))) q))
  (items-prints toks (Nil _) forms (AtEnd) p (FollowsEnd)))

(def-fns _ $ (erased printing-reads : (erased (List (Tok)) toks) (erased (List (Form)) forms)
    (erased (Prints forms toks (Nil (Tok))) p) -> (erased (Items toks forms (AtEnd)) q))
  (prints-items toks (Nil _) forms (AtEnd) p (FollowsEnd)))

(let ((many kind-open) (erased class-open)) (classify delims #\x28))
(comptime-match many kind-open (KDelim delim-open))
(comptime-match many delim-open (DOpen))
(let ((many kind-close) (erased class-close)) (classify delims #\x29))
(comptime-match many kind-close (KDelim delim-close))
(comptime-match many delim-close (DClose))
(let ((many kind-dollar) (erased class-dollar)) (classify delims #\$))
(comptime-match many kind-dollar (KWord))
(let ((many kind-space) (erased class-space)) (classify delims #\space))
(comptime-match many kind-space (KDelim delim-space))
(comptime-match many delim-space (DSpace))

(def-fns _ $ (erased space-lex : (erased (String) rest) (erased (List (Tok)) toks) (erased (Lex rest toks) p) -> (erased (Lex (SCons #\space rest) toks) q))
  (LexChar #\space (KDelim (DSpace)) rest toks class-space (AfterSpace #\space rest toks p)))

(def-fns _ $ (erased word-spelled : (erased (String) w rest text) (erased (WordChars w) k) (subterm erased (Append w (SCons #\space rest) text) s) ->
    (erased (Word text w (SCons #\space rest)) q))
  (let-match erased s (AppCons c v _ t s2) ((AppNil _) (WordStop #\space (DSpace) rest class-space)))
  (let-match erased k (WordCharsMore _ _ ck k2))
  (WordMore c t v (SCons #\space rest) ck (word-spelled v rest t k2 s2)))

(def-fns _ $ (erased spelled-lex : (erased (List (Tok)) toks) (erased (String) text) (subterm erased (Spelled toks text) s) -> (erased (Lex text toks) q))
  (let-match erased s (SpelledAtom c w rest _ ts k a ap s2)
    ((SpelledNone) (LexEnd))
    ((SpelledOpen ts rest s2)
      (LexChar #\x28 (KDelim (DOpen)) (SCons #\space rest) toks class-open
        (AfterOpen #\x28 (SCons #\space rest) ts (space-lex rest ts (spelled-lex ts rest s2)))))
    ((SpelledClose ts rest s2)
      (LexChar #\x29 (KDelim (DClose)) (SCons #\space rest) toks class-close
        (AfterClose #\x29 (SCons #\space rest) ts (space-lex rest ts (spelled-lex ts rest s2)))))
    ((SpelledDollar ts rest s2)
      (LexChar #\$ (KWord) (SCons #\space rest) toks class-dollar
        (AfterWord #\$ (SCons #\space rest) (SNil) (SCons #\space rest) (TDollar) ts
          (WordStop #\space (DSpace) rest class-space) (TokDollar) (space-lex rest ts (spelled-lex ts rest s2))))))
  (let-match erased ap (AppCons _ _ _ t ap2))
  (let-match erased k (WordCharsMore _ _ ck k2))
  (LexChar c (KWord) t toks ck
    (AfterWord c t w (SCons #\space rest) (TAtom (SCons c w)) ts
      (word-spelled w rest t k2 ap2) (TokAtom (SCons c w) a) (space-lex rest ts (spelled-lex ts rest s2)))))

(def-fns _ $ (erased written-reads : (erased (List (Form)) forms) (erased (List (Tok)) toks) (erased (String) text)
    (erased (Prints forms toks (Nil (Tok))) w) (erased (Spelled toks text) s) -> (erased (Reads text forms) r))
  (ReadsBy text toks forms (spelled-lex toks text s) (printing-reads toks forms w)))

(qed (MkAdequate (level-of reading-prints) (level-of printing-reads) (level-of written-reads) reading-prints printing-reads written-reads))
