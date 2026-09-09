; self/reader.sl -- s-expressions with $ (DESIGN.md sections 1-2), read by a structural tokenizer over the
; source string and a fold over the tokens with a stack of open forms, so nothing recurses on a computed
; suffix of the input.

(def-adts
  (Raw : -> Type
    enum
    (many RAtom : (many (Nat) line) (many (String) s) -> (Raw))
    (many RString : (many (Nat) line) (many (String) s) -> (Raw))
    (many RList : (many (Nat) line) (many (List $ Raw) items) -> (Raw))))

(def-fns _ $ many raw-line : (many (Raw) r) -> (many (Nat) line)
  (match many r _ ((RAtom l s) l) ((RString l s) l) ((RList l items) l)))

(def-adts $ Tok : -> Type
  enum
  (many TOpen : (many (Nat) line) -> (Tok))
  (many TClose : (many (Nat) line) -> (Tok))
  (many TDollar : (many (Nat) line) -> (Tok))
  (many TWord : (many (Nat) line) (many (String) s) -> (Tok))
  (many TStrLit : (many (Nat) line) (many (String) s) -> (Tok))
  (many TError : (many (Nat) line) (many (String) msg) -> (Tok)))

; A syntax error and the line it is reported for.
(def-adts $ SynErr : -> Type
  enum
  (many MkSynErr : (many (Nat) line) (many (String) msg) -> (SynErr)))

(def-fns _ $ many is-delim : (many (Char) c) -> (many (Bool) r)
  (let (many n) $ char-code c)
  (or (nat-lt n 33)
    (or (nat-eq n 40)
      $ or (nat-eq n 41) $ nat-eq n 59)))

(def-fns _ $ many word-tok : (many (Nat) line) (many (String) rev) -> (many (Tok) t)
  (let (many w) $ str-rev-onto rev $ SNil)
  (match many (str-cmp w "$") _
    ((CEq eq-t eq-r eq-x) (TDollar line))
    (else (TWord line w))))

(def-fns _ $ many next-line : (many (Nat) line) (many (Char) c) -> (many (Nat) r)
  (match many (char-is c 10) _ ((BTrue) (Succ line)) ((BFalse) line)))

(def-fns _ $ many escape-ok : (many (Char) e) -> (many (Bool) r)
  (let (many n) $ char-code e)
  (or (nat-eq n 110) $ or (nat-eq n 116) $ or (nat-eq n 34) $ nat-eq n 92))

(def-fns _ $ many unescape : (many (Char) e) -> (many (Char) c)
  (let (many n) $ char-code e)
  (match many (nat-cmp n 110) _
    ((CEq eq-t eq-r eq-x) #\newline)
    (else
      (match many (nat-cmp n 116) _
        ((CEq eq-t eq-r eq-x) #\tab)
        (else e)))))

; Tokens accumulate reversed in [acc]; an atom's characters accumulate reversed in [word]; [line] counts
; the newlines passed, and a string literal's token carries the line of its closing quote as the
; reference reader's does.
(def-fns _
  (many tokenize : (subterm many (String) s) (many (Nat) line) (many (List $ Tok) acc) -> (many (List $ Tok) toks)
    (match many s _
      ((SNil) (list-rev _ acc))
      ((SCons c rest)
        (let (many n) $ char-code c)
        (match many (nat-lt n 33) _
          ((BTrue) (tokenize rest (next-line line c) acc))
          ((BFalse)
            (match many (nat-cmp n 59) _
              ((CEq eq-t eq-r eq-x) (skip-comment rest line acc))
              (else
                (match many (nat-cmp n 40) _
                  ((CEq eq-t eq-r eq-x) (tokenize rest line $ Cons _ (TOpen line) acc))
                  (else
                    (match many (nat-cmp n 41) _
                      ((CEq eq-t eq-r eq-x) (tokenize rest line $ Cons _ (TClose line) acc))
                      (else
                        (match many (nat-cmp n 34) _
                          ((CEq eq-t eq-r eq-x) (string-lit rest line (SNil) acc))
                          (else (word rest line (SCons c $ SNil) acc))))))))))))))
  (many skip-comment : (subterm many (String) s) (many (Nat) line) (many (List $ Tok) acc) -> (many (List $ Tok) toks)
    (match many s _
      ((SNil) (list-rev _ acc))
      ((SCons c rest)
        (match many (char-is c 10) _
          ((BTrue) (tokenize rest (Succ line) acc))
          ((BFalse) (skip-comment rest line acc))))))
  (many word : (subterm many (String) s) (many (Nat) line) (many (String) rev) (many (List $ Tok) acc) -> (many (List $ Tok) toks)
    (match many s _
      ((SNil) (list-rev _ $ Cons _ (word-tok line rev) acc))
      ((SCons c rest)
        (match many (is-delim c) _
          ((BTrue)
            (let (many acc1) $ Cons _ (word-tok line rev) acc)
            (let (many n) $ char-code c)
            (match many (nat-cmp n 59) _
              ((CEq eq-t eq-r eq-x) (skip-comment rest line acc1))
              (else
                (match many (nat-cmp n 40) _
                  ((CEq eq-t eq-r eq-x) (tokenize rest line $ Cons _ (TOpen line) acc1))
                  (else
                    (match many (nat-cmp n 41) _
                      ((CEq eq-t eq-r eq-x) (tokenize rest line $ Cons _ (TClose line) acc1))
                      (else (tokenize rest (next-line line c) acc1))))))))
          ((BFalse) (word rest line (SCons c rev) acc))))))
  (many string-lit : (subterm many (String) s) (many (Nat) line) (many (String) rev) (many (List $ Tok) acc) -> (many (List $ Tok) toks)
    (match many s _
      ((SNil) (list-rev _ $ Cons _ (TError line "unterminated string literal") acc))
      ((SCons c rest)
        (let (many n) $ char-code c)
        (match many (nat-cmp n 34) _
          ((CEq eq-t eq-r eq-x) (tokenize rest line $ Cons _ (TStrLit line $ str-rev-onto rev $ SNil) acc))
          (else
            (match many (nat-cmp n 92) _
              ((CEq eq-t eq-r eq-x)
                (match many rest _
                  ((SNil) (list-rev _ $ Cons _ (TError line "unterminated string literal") acc))
                  ((SCons e rest2)
                    (match many (escape-ok e) _
                      ((BTrue) (string-lit rest2 line (SCons (unescape e) rev) acc))
                      ((BFalse) (list-rev _ $ Cons _ (TError line $ str-cat "unknown escape \\" $ SCons e $ SNil) acc))))))
              (else (string-lit rest (next-line line c) (SCons c rev) acc)))))))))

; A frame is an open form: the line it opened on, whether $ opened it, and its items so far, reversed.
(def-adts $ Frame : -> Type
  enum
  (many MkFrame : (many (Nat) line) (many (Bool) dollar) (many (List $ Raw) items) -> (Frame)))

(def-fns _ $ many push-item : (many (Raw) item) (many (List $ Frame) stack) -> (many (List $ Frame) r)
  (match many stack _
    ((Nil a) (Cons _ (MkFrame 1 (BFalse) $ Cons _ item $ Nil _) $ Nil _))
    ((Cons a f rest)
      (match many f _
        ((MkFrame l d items) (Cons _ (MkFrame l d $ Cons _ item items) rest))))))

; Closes the top frame into its parent as a list.
(def-fns _ $ many close-top : (many (List $ Frame) stack) -> (many (List $ Frame) r)
  (match many stack _
    ((Nil a) stack)
    ((Cons a f rest)
      (match many f _
        ((MkFrame l d items) (push-item (RList l $ list-rev _ items) rest))))))

; Closes every $-opened frame on top of the stack, each into the frame below it.
(def-fns _
  (many close-dollars : (subterm many (List $ Frame) stack) -> (many (List $ Frame) r)
    (match many stack _
      ((Nil a) stack)
      ((Cons a f rest)
        (match many f _
          ((MkFrame l d items)
            (match many d _
              ((BFalse) stack)
              ((BTrue) (close-into rest $ RList l $ list-rev _ items))))))))
  (many close-into : (subterm many (List $ Frame) stack) (many (Raw) item) -> (many (List $ Frame) r)
    (match many stack _
      ((Nil a) (push-item item stack))
      ((Cons a f rest)
        (match many f _
          ((MkFrame l d items)
            (match many d _
              ((BFalse) (Cons _ (MkFrame l d $ Cons _ item items) rest))
              ((BTrue) (close-into rest $ RList l $ list-rev _ $ Cons _ item items)))))))))

; The stack starts with a root frame; a ) closes the $ frames above the nearest ( frame and then that
; frame; a ) with only the root open, a form still open at the end, or a bad token is a syntax error
; (DESIGN.md section 2).
(def-fns _ $ many parse-toks : (subterm many (List $ Tok) toks) (many (List $ Frame) stack) -> (many (List $ Frame) r) (many (Maybe $ SynErr) err)
  (match many toks _
    ((Nil a) (values stack $ None _))
    ((Cons a t rest)
      (match many t _
        ((TOpen l) (parse-toks rest $ Cons _ (MkFrame l (BFalse) $ Nil _) stack))
        ((TDollar l) (parse-toks rest $ Cons _ (MkFrame l (BTrue) $ Nil _) stack))
        ((TWord l w) (parse-toks rest $ push-item (RAtom l w) stack))
        ((TStrLit l s) (parse-toks rest $ push-item (RString l s) stack))
        ((TError l m) (values stack $ Some _ $ MkSynErr l m))
        ((TClose l)
          (let (many s1) $ close-dollars stack)
          (match many s1 _
            ((Nil b) (values s1 $ Some _ $ MkSynErr l "unexpected )"))
            ((Cons b f s2)
              (match many s2 _
                ((Nil c) (values s1 $ Some _ $ MkSynErr l "unexpected )"))
                ((Cons c g s3) (parse-toks rest $ close-top s1))))))))))

; Reads the root frame's items once nothing is open; an open form at the end is a missing ), reported
; for the innermost, which is the $ form's when that is what is open, at the line the form opened on.
(def-fns _ $ many finish-stack : (many (List $ Frame) stack) -> (many (List $ Raw) items) (many (Maybe $ SynErr) err)
  (match many stack _
    ((Nil a) (values (Nil _) $ None _))
    ((Cons a f rest)
      (match many rest _
        ((Nil b) (match many f _ ((MkFrame l d items) (values (list-rev _ items) $ None _))))
        ((Cons b g rest2)
          (match many f _
            ((MkFrame l d items) (values (Nil _) $ Some _ $ MkSynErr l $ match many d (((String) m)) ((BTrue) "missing ) after $") ((BFalse) "missing )")))))))))

(def-fns _ $ many parse : (many (String) src) -> (many (List $ Raw) items) (many (Maybe $ SynErr) err)
  (let (many stack) (many err) (parse-toks (tokenize src 1 $ Nil _)
                                            $ Cons _ (MkFrame 1 (BFalse) $ Nil _) $ Nil _))
  (match many err _
    ((Some a m) (values (Nil _) err))
    ((None a) (finish-stack stack))))

(def-fns _
  (many show-raw : (subterm many (Raw) r) -> (many (Rope) out)
    (match many r _
      ((RAtom l s) (RStr s))
      ((RString l s) (rcat3 (RStr "\"") (RStr $ ocaml-escape s) $ RStr "\""))
      ((RList l items) (rcat3 (RStr "(") (show-raws items) $ RStr ")"))))
  (many show-raws : (subterm many (List $ Raw) rs) -> (many (Rope) out)
    (match many rs _
      ((Nil a) (REmpty))
      ((Cons a r rest)
        (match many rest _
          ((Nil b) (show-raw r))
          ((Cons b r2 rest2) (rcat3 (show-raw r) (RStr " ") $ show-raws rest)))))))
