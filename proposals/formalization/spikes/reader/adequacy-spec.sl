(def-adts $ (Prints : ((List (Form)) forms) ((List (Tok)) toks) ((List (Tok)) more) -> Type)
  enum
  (many PrintsNone : (erased (List (Tok)) more) -> (Prints (Nil (Form)) more more))
  (many PrintsAtom : (erased (String) a) (erased (List (Form)) fs) (erased (List (Tok)) toks more) (erased (Prints fs toks more) p)
     -> (Prints (Cons (Form) (FAtom a) fs) (Cons (Tok) (TAtom a) toks) more))
  (many PrintsList : (erased (List (Form)) inner fs) (erased (List (Tok)) toks mid more)
     (erased (Prints inner toks (Cons (Tok) (TClose) mid)) p) (erased (Prints fs mid more) q)
     -> (Prints (Cons (Form) (FList inner) fs) (Cons (Tok) (TOpen) toks) more))
  (many PrintsDollar : (erased (List (Form)) inner) (erased (List (Tok)) toks after) (erased (Prints inner toks (Cons (Tok) (TClose) after)) p)
     -> (Prints (Cons (Form) (FList inner) (Nil (Form))) (Cons (Tok) (TDollar) toks) (Cons (Tok) (TClose) after))))

(def-adts $ (WordChars : ((String) w) -> Type)
  enum
  (many WordCharsNone : -> (WordChars (SNil)))
  (many WordCharsMore : (erased (Char) c) (erased (String) w) (erased (Class delims c (KWord)) k) (erased (WordChars w) p) -> (WordChars (SCons c w))))

(def-adts $ (Spelled : ((List (Tok)) toks) ((String) text) -> Type)
  enum
  (many SpelledNone : -> (Spelled (Nil (Tok)) (SNil)))
  (many SpelledOpen : (erased (List (Tok)) toks) (erased (String) rest) (erased (Spelled toks rest) p)
     -> (Spelled (Cons (Tok) (TOpen) toks) (SCons #\x28 (SCons #\space rest))))
  (many SpelledClose : (erased (List (Tok)) toks) (erased (String) rest) (erased (Spelled toks rest) p)
     -> (Spelled (Cons (Tok) (TClose) toks) (SCons #\x29 (SCons #\space rest))))
  (many SpelledDollar : (erased (List (Tok)) toks) (erased (String) rest) (erased (Spelled toks rest) p)
     -> (Spelled (Cons (Tok) (TDollar) toks) (SCons #\$ (SCons #\space rest))))
  (many SpelledAtom : (erased (Char) c) (erased (String) w rest text) (erased (List (Tok)) toks)
     (erased (WordChars (SCons c w)) k) (erased (Apart (String) StrLt (SCons c w) dollar) a)
     (erased (Append (SCons c w) (SCons #\space rest) text) s) (erased (Spelled toks rest) p)
     -> (Spelled (Cons (Tok) (TAtom (SCons c w)) toks) text)))

(def-adts $ (Adequate : -> Type)
  enum
  (many MkAdequate : (erased (Level) L M N)
     (erased (Fn L (erased (List (Tok)) toks) (erased (List (Form)) forms)
                   (erased (Items toks forms (AtEnd)) p) -> (erased (Prints forms toks (Nil (Tok))) q)) reading-prints)
     (erased (Fn M (erased (List (Tok)) toks) (erased (List (Form)) forms)
                   (erased (Prints forms toks (Nil (Tok))) p) -> (erased (Items toks forms (AtEnd)) q)) printing-reads)
     (erased (Fn N (erased (List (Form)) forms) (erased (List (Tok)) toks) (erased (String) text)
                   (erased (Prints forms toks (Nil (Tok))) w) (erased (Spelled toks text) s) -> (erased (Reads text forms) r)) written-reads)
     -> (Adequate)))

(goal erased (Adequate))
