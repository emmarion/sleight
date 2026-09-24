; self/reader.sl -- s-expressions with $ (DESIGN.md sections 1-2), read by a structural tokenizer over the
; source string and a fold over the tokens with a stack of open forms, so nothing recurses on a computed
; suffix of the input.

; Where a token's first character sits, which every message a session writes points at (ASSUMPTIONS 194);
; both counted from one.
(def-adts $ (Pos : -> Type)
  enum
  (many MkPos : (many (Nat) line) (many (Nat) col) -> (Pos)))

(def-adts
  ((Raw : -> Type)
    enum
    (many RAtom : (many (Pos) pos) (many (String) s) -> (Raw))
    (many RString : (many (Pos) pos) (many (String) s) -> (Raw))
    (many RList : (many (Pos) pos) (many (List $ Raw) items) -> (Raw))))

(def-fns _ $ (many raw-pos : (many (Raw) r) -> (many (Pos) pos))
  (match many r _ ((RAtom l _) l) ((RString l _) l) ((RList l _) l)))

; Where a form's first item sits, which is what a declaration's messages name: the signature rather than
; the entry that carries it.
(def-fns _ $ (many raw-head-pos : (many (Raw) r) -> (many (Pos) pos))
  (match many r _
    ((RList l items)
      (match many items (((Pos) _))
        ((Cons _ h _) (raw-pos h))
        ((Nil _) l)))
    (else (raw-pos r))))

(def-adts $ (Tok : -> Type)
  enum
  (many TOpen : (many (Pos) pos) -> (Tok))
  (many TClose : (many (Pos) pos) -> (Tok))
  (many TDollar : (many (Pos) pos) -> (Tok))
  (many TWord : (many (Pos) pos) (many (String) s) -> (Tok))
  (many TStrLit : (many (Pos) pos) (many (String) s) -> (Tok))
  (many TError : (many (Pos) pos) (many (String) msg) -> (Tok))
  (many TPragma : (many (Pos) pos) (many (List $ Raw) words) -> (Tok)))

; A syntax error and where it is reported.
(def-adts $ (SynErr : -> Type)
  enum
  (many MkSynErr : (many (Pos) pos) (many (String) msg) (many (Bool) paren) -> (SynErr)))

; A parenthesis a file gets wrong is found faster with bin/shape than from the one position a message names
; (lib/reader.ml's shape_note).
(def-fns _ $ (many shape-note : (many (String) path) -> (many (String) r))
  (str-cat path ": note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes"))

(def-fns _ $ (many is-delim : (many (Char) c) -> (many (Bool) r))
  (let ((many n)) $ char-code c)
  (or (nat-lt n 33)
    (or (nat-eq n 40)
      $ or (nat-eq n 41) $ nat-eq n 59)))

(def-fns _ $ (many word-tok : (many (Pos) pos) (many (String) start) (many (Nat) k) (erased (Nat) len) (erased (StrLength start len) l) (erased (Nat) rl) (erased (Add k rl len) sum) -> (many (Tok) t))
  (let ((many w) (many after) (erased p) (erased la)) (str-split start k len l (add-le-left k rl len sum)))
  (match many (str-cmp w "$") _
    ((CEq _ _ _) (TDollar pos))
    (else (TWord pos w))))

(def-fns _ $ (many escape-ok : (many (Char) e) -> (many (Bool) r))
  (let ((many n)) $ char-code e)
  (or (nat-eq n 110) $ or (nat-eq n 116) $ or (nat-eq n 34) $ nat-eq n 92))

(def-fns _ $ (many unescape : (many (Char) e) -> (many (Char) c))
  (let ((many n)) $ char-code e)
  (match many (nat-cmp n 110) _
    ((CEq _ _ _) #\newline)
    (else
      (match many (nat-cmp n 116) _
        ((CEq _ _ _) #\tab)
        (else e)))))

(def-fns _ $ (many end-toks : (many (Tok) t) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (list-rev _ $ Cons _ t acc))

(def-fns _ $ (many unterminated : (many (Pos) pos) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (end-toks (TError pos "unterminated string literal") acc))

; [col] counts the characters read on the current line, so the character being read sits at column
; (Succ col); a newline starts the next line over at zero.
(def-fns _ $ (many delim-step : (many (Char) c) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) ->
    (many (Bool) comment) (many (Nat) line2) (many (Nat) col2) (many (List $ Tok) acc2))
  (let ((many n)) $ char-code c)
  (match many (nat-eq n 59) _
    ((BTrue) (values (BTrue) line (Succ col) acc))
    ((BFalse)
      (match many (nat-eq n 40) _
        ((BTrue) (values (BFalse) line (Succ col) $ Cons _ (TOpen $ MkPos line $ Succ col) acc))
        ((BFalse)
          (match many (nat-eq n 41) _
            ((BTrue) (values (BFalse) line (Succ col) $ Cons _ (TClose $ MkPos line $ Succ col) acc))
            ((BFalse)
              (match many (nat-eq n 10) _
                ((BTrue) (values (BFalse) (Succ line) 0 acc))
                ((BFalse) (values (BFalse) line (Succ col) acc))))))))))

(def-fns _ $ (many pragma-field : (many (Maybe $ Pos) start) (many (Rope) cur) (many (List $ Raw) words) -> (many (List $ Raw) r))
  (match many start _
    ((None _) words)
    ((Some _ p) (Cons _ (RAtom p $ rope-str cur) words))))

(def-fns _ $ (many pragma-tok : (many (Pos) pos) (many (Maybe $ Pos) start) (many (Rope) cur) (many (List $ Raw) words) -> (many (Tok) t))
  (TPragma pos $ list-rev _ $ pragma-field start cur words))

; Tokens accumulate reversed in [acc]; an atom's or a literal's characters accumulate as a rope; [line] and
; [col] count the newlines and the characters passed, and a token is placed where it starts, a string
; literal's at its opening quote, as the reference reader places one.
(def-fns _
  ((many tokenize : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (list-rev _ acc))
      ((SCons c rest)
        (match many (is-delim c) _
          ((BTrue)
            (let ((many comment) (many line2) (many col2) (many acc2)) $ delim-step c line col acc)
            (match many comment _ ((BTrue) (tail $ comment-start rest line2 col2 acc2)) ((BFalse) (tail $ tokenize rest line2 col2 acc2))))
          ((BFalse)
            (match many (char-is c 34) _
              ((BTrue) (tail $ string-lit rest line (Succ col) (MkPos line $ Succ col) (REmpty) acc))
              ((BFalse)
                (let ((many len) (erased l)) (str-length s))
                (let-match erased l (SLenCons c0 s0 rl lr))
                (tail $ word rest line (Succ col) s len l (Succ (Zero)) rl lr (AddSucc (Zero) rl rl (AddZero rl)) (MkPos line $ Succ col) acc))))))))
  ((many comment-start : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (list-rev _ acc))
      ((SCons c rest)
        (match many (char-is c 33) _
          ((BTrue) (tail $ pragma-line rest line (Succ col) (MkPos line col) (Nil _) (None _) (REmpty) (REmpty) acc))
          ((BFalse)
            (match many (char-is c 10) _
              ((BTrue) (tail $ tokenize rest (Succ line) 0 acc))
              ((BFalse) (tail $ skip-comment rest line acc))))))))
  ((many pragma-line : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Pos) pos) (many (List $ Raw) words)
      (many (Maybe $ Pos) start) (many (Rope) cur) (many (Rope) blanks) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (end-toks (pragma-tok pos start cur words) acc))
      ((SCons c rest)
        (match many (char-is c 10) _
          ((BTrue) (tail $ tokenize rest (Succ line) 0 $ Cons _ (pragma-tok pos start cur words) acc))
          ((BFalse)
            (match many (or (char-is c 32) $ or (char-is c 9) $ char-is c 13) _
              ((BTrue)
                (match many start _
                  ((None _) (tail $ pragma-line rest line (Succ col) pos words start cur blanks acc))
                  ((Some _ _)
                    (match many (nat-lt (list-length _ words) 2) _
                      ((BTrue) (tail $ pragma-line rest line (Succ col) pos (pragma-field start cur words) (None _) (REmpty) (REmpty) acc))
                      ((BFalse) (tail $ pragma-line rest line (Succ col) pos words start cur (RCat blanks $ RChar c) acc))))))
              ((BFalse)
                (match many start _
                  ((None _) (tail $ pragma-line rest line (Succ col) pos words (Some _ $ MkPos line $ Succ col) (RChar c) (REmpty) acc))
                  ((Some _ _) (tail $ pragma-line rest line (Succ col) pos words start (RCat (RCat cur blanks) $ RChar c) (REmpty) acc))))))))))
  ((many skip-comment : (subterm many (String) s) (many (Nat) line) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (list-rev _ acc))
      ((SCons c rest)
        (match many (char-is c 10) _
          ((BTrue) (tail $ tokenize rest (Succ line) 0 acc))
          ((BFalse) (tail $ skip-comment rest line acc))))))
  ((many word : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (String) start) (erased (Nat) len) (erased (StrLength start len) l) (many (Nat) k) (erased (Nat) rl) (erased (StrLength s rl) lr) (erased (Add k rl len) sum) (many (Pos) pos) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (end-toks (word-tok pos start k len l rl sum) acc))
      ((SCons c rest)
        (match many (is-delim c) _
          ((BTrue)
            (let ((many comment) (many line2) (many col2) (many acc2)) $ delim-step c line col $ Cons _ (word-tok pos start k len l rl sum) acc)
            (match many comment _ ((BTrue) (tail $ comment-start rest line2 col2 acc2)) ((BFalse) (tail $ tokenize rest line2 col2 acc2))))
          ((BFalse)
            (let-match erased lr (SLenCons c0 s0 rl1 lr1))
            (tail $ word rest line (Succ col) start len l (Succ k) rl1 lr1 (add-shift k rl1 len sum) pos acc))))))
  ((many string-lit : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Pos) pos) (many (Rope) rev) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (match many s _
      ((SNil) (unterminated (MkPos line $ Succ col) acc))
      ((SCons c rest)
        (let ((many n)) $ char-code c)
        (match many (nat-eq n 34) _
          ((BTrue) (tail $ tokenize rest line (Succ col) $ Cons _ (TStrLit pos $ rope-str rev) acc))
          ((BFalse)
            (match many (nat-eq n 92) _
              ((BTrue)
                (match many rest _
                  ((SNil) (unterminated (MkPos line $ Succ col) acc))
                  ((SCons e rest2)
                    (match many (escape-ok e) _
                      ((BTrue) (tail $ string-lit rest2 line (Succ (Succ col)) pos (RCat rev $ RChar $ unescape e) acc))
                      ((BFalse) (end-toks (TError (MkPos line $ Succ col) $ str-cat "unknown escape \\" $ SCons e $ SNil) acc))))))
              ((BFalse)
                (match many (nat-eq n 10) _
                  ((BTrue) (tail $ string-lit rest (Succ line) 0 pos (RCat rev $ RChar c) acc))
                  ((BFalse) (tail $ string-lit rest line (Succ col) pos (RCat rev $ RChar c) acc)))))))))))

; A frame is an open form: where it opened, whether $ opened it, and its items so far, reversed.
(def-adts $ (Frame : -> Type)
  enum
  (many MkFrame : (many (Pos) pos) (many (Bool) dollar) (many (List $ Raw) items) -> (Frame)))

(def-fns _ $ (many push-item : (many (Raw) item) (many (List $ Frame) stack) -> (many (List $ Frame) r))
  (match many stack _
    ((Nil _) (Cons _ (MkFrame (MkPos 1 1) (BFalse) $ Cons _ item $ Nil _) $ Nil _))
    ((Cons _ f rest)
      (match many f _
        ((MkFrame l d items) (Cons _ (MkFrame l d $ Cons _ item items) rest))))))

; Closes the top frame into its parent as a list.
(def-fns _ $ (many close-top : (many (List $ Frame) stack) -> (many (List $ Frame) r))
  (match many stack _
    ((Nil _) stack)
    ((Cons _ f rest)
      (match many f _
        ((MkFrame l _ items) (push-item (RList l $ list-rev _ items) rest))))))

; Closes every $-opened frame on top of the stack, each into the frame below it.
(def-fns _
  ((many close-dollars : (subterm many (List $ Frame) stack) -> (many (List $ Frame) r))
    (match many stack _
      ((Nil _) stack)
      ((Cons _ f rest)
        (match many f _
          ((MkFrame l d items)
            (match many d _
              ((BFalse) stack)
              ((BTrue) (tail $ close-into rest $ RList l $ list-rev _ items))))))))
  ((many close-into : (subterm many (List $ Frame) stack) (many (Raw) item) -> (many (List $ Frame) r))
    (match many stack _
      ((Nil _) (push-item item stack))
      ((Cons _ f rest)
        (match many f _
          ((MkFrame l d items)
            (match many d _
              ((BFalse) (Cons _ (MkFrame l d $ Cons _ item items) rest))
              ((BTrue) (tail $ close-into rest $ RList l $ list-rev _ $ Cons _ item items)))))))))

; The stack starts with a root frame; a ) closes the $ frames above the nearest ( frame and then that
; frame; a ) with only the root open, a form still open at the end, or a bad token is a syntax error
; (DESIGN.md section 2).
(def-fns _ $ (many parse-toks : (subterm many (List $ Tok) toks) (many (List $ Frame) stack) -> (many (List $ Frame) r) (many (Maybe $ SynErr) err))
  (match many toks _
    ((Nil _) (values stack $ None _))
    ((Cons _ t rest)
      (match many t _
        ((TOpen l) (tail $ parse-toks rest $ Cons _ (MkFrame l (BFalse) $ Nil _) stack))
        ((TDollar l) (tail $ parse-toks rest $ Cons _ (MkFrame l (BTrue) $ Nil _) stack))
        ((TWord l w) (tail $ parse-toks rest $ push-item (RAtom l w) stack))
        ((TStrLit l s) (tail $ parse-toks rest $ push-item (RString l s) stack))
        ((TError l m) (values stack $ Some _ $ MkSynErr l m $ BFalse))
        ((TPragma l ws)
          (match many (nat-lt (list-length _ stack) 2) _
            ((BTrue) (tail $ parse-toks rest $ push-item (RList l $ Cons _ (RAtom l ";!") ws) stack))
            ((BFalse) (values stack $ Some _ $ MkSynErr l "a pragma must be written between top-level forms" $ BFalse))))
        ((TClose l)
          (let ((many s1)) $ close-dollars stack)
          (match many s1 _
            ((Nil _) (values s1 $ Some _ $ MkSynErr l "unexpected `)`" $ BTrue))
            ((Cons _ _ s2)
              (match many s2 _
                ((Nil _) (values s1 $ Some _ $ MkSynErr l "unexpected `)`" $ BTrue))
                ((Cons _ _ _) (tail $ parse-toks rest $ close-top s1))))))))))

; Reads the root frame's items once nothing is open; an open form at the end is a missing ), reported
; for the innermost, which is the $ form's when that is what is open, at the line the form opened on.
(def-fns _ $ (many finish-stack : (many (List $ Frame) stack) -> (many (List $ Raw) items) (many (Maybe $ SynErr) err))
  (match many stack _
    ((Nil _) (values (Nil _) $ None _))
    ((Cons _ f rest)
      (match many rest _
        ((Nil _) (match many f _ ((MkFrame _ _ items) (values (list-rev _ items) $ None _))))
        ((Cons _ _ _)
          (match many f _
            ((MkFrame l d _) (values (Nil _) $ Some _ $ MkSynErr l (match many d (((String) _)) ((BTrue) "missing `)` after `$`") ((BFalse) "missing `)`")) $ BTrue))))))))

(def-fns _ $ (many parse : (many (String) src) -> (many (List $ Raw) items) (many (Maybe $ SynErr) err))
  (let ((many stack) (many err)) (parse-toks (tokenize src 1 0 $ Nil _)
                                            $ Cons _ (MkFrame (MkPos 1 1) (BFalse) $ Nil _) $ Nil _))
  (match many err _
    ((Some _ _) (values (Nil _) err))
    ((None _) (finish-stack stack))))

(def-fns _
  ((many show-raw : (subterm many (Raw) r) -> (many (Rope) out))
    (match many r _
      ((RAtom _ s) (RStr s))
      ((RString _ s) (rwrap "\"" (ocaml-escape s) "\""))
      ((RList _ items) (rwrap "(" (rjoin (notail $ show-raws items) " ") ")"))))
  ((many show-raws : (subterm many (List $ Raw) rs) -> (many (List $ Rope) out))
    (match many rs _
      ((Nil _) (Nil _))
      ((Cons _ r rest) (Cons _ (notail $ show-raw r) $ notail $ show-raws rest)))))

; The indentation check of lib/indent.ml, read from the source text rather than from the tokens above, which
; carry no column: indentation is a claim about paren nesting, and a line's claim is checked against the
; depth in force where its first token starts. It runs before the parse, so a file the reader goes on to
; refuse is reported on too. $ is not nesting and is not tracked; lib/indent.ml's header says why.

; One indentation level still open: the line that opened it, which a later line's note names, and the
; indentation and nesting it opened at.
(def-adts $ (IndLevel : -> Type)
  enum
  (many MkIndLevel : (many (Pos) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndLevel)))

(def-adts $ (IndentLine : -> Type)
  enum
  (many MkIndentLine : (many (Pos) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndentLine)))

; The scan's state: the line and the characters seen on it, the paren depth and where each form still open
; was opened, innermost first, whether a token has started on this line and whether a tab sits in what
; precedes it, the first ) that closed more than was open, and the lines checked and the lines carrying a
; tab, both reversed.
(def-adts $ (IndentSt : -> Type)
  enum
  (many MkIndentSt : (many (Nat) line) (many (Nat) col) (many (Nat) depth) (many (List $ Pos) opens)
      (many (Bool) started) (many (Bool) tabbed) (many (Maybe $ Pos) surplus)
      (many (List $ IndentLine) lines) (many (List $ Pos) tabs) -> (IndentSt)))

(def-fns _ $ (many ind-nl : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l _ d op _ _ u ls ts) (MkIndentSt (Succ l) 0 d op (BFalse) (BFalse) u ls ts))))

(def-fns _ $ (many ind-plain : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l c d op s t u ls ts) (MkIndentSt l (Succ c) d op s t u ls ts))))

; A tab is recorded for the line it sits on whatever is being read there, a literal included: what the check
; reads is the text between the start of a line and the first token attributed to it.
(def-fns _ $ (many ind-tab : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l c d op s _ u ls ts) (MkIndentSt l (Succ c) d op s (BTrue) u ls ts))))

(def-fns _ $ (many ind-mark : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _
    ((MkIndentSt l c d op s t u ls ts)
      (match many s _
        ((BTrue) st)
        ((BFalse)
          (let ((many (List $ Pos) ts2))
            (match many t (((List $ Pos) _))
              ((BTrue) (Cons _ (MkPos l $ Succ c) ts))
              ((BFalse) ts)))
          (MkIndentSt l c d op (BTrue) t u (Cons _ (MkIndentLine (MkPos l $ Succ c) c d) ls) ts2))))))

(def-fns _ $ (many ind-open : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many (ind-plain $ ind-mark st) _
    ((MkIndentSt l c d op s t u ls ts) (MkIndentSt l c (Succ d) (Cons _ (MkPos l c) op) s t u ls ts))))

; A ) with nothing open is recorded where it sits and leaves the depth at zero, so the lines after it are
; still checked against the count of forms actually open.
(def-fns _ $ (many ind-close : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many (ind-plain $ ind-mark st) _
    ((MkIndentSt l c d op s t u ls ts)
      (match many d _
        ((Succ p)
          (let ((many (List $ Pos) op2))
            (match many op (((List $ Pos) _))
              ((Cons _ _ more) more)
              ((Nil _) op)))
          (MkIndentSt l c p op2 s t u ls ts))
        ((Zero)
          (let ((many (Maybe $ Pos) u2))
            (match many u (((Maybe $ Pos) _))
              ((Some _ _) u)
              ((None _) (Some _ $ MkPos l c))))
          (MkIndentSt l c 0 op s t u2 ls ts))))))

; A string literal's token sits at its opening quote, so the line it opened on is recorded once the literal
; closes, and an unterminated one is no token at all, the reference reader emitting none for it.
(def-fns _ $ (many ind-close-str : (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc) (many (Bool) os)
    (many (Bool) ot) -> (many (IndentSt) r))
  (match many st _
    ((MkIndentSt l c d op _ t u ls ts)
      (let ((many (List $ IndentLine) ls2) (many (List $ Pos) ts2))
        (match many os (((List $ IndentLine) _) ((List $ Pos) y))
          ((BTrue) (values ls ts))
          ((BFalse)
            (let ((many (List $ Pos) ts1))
              (match many ot (((List $ Pos) _))
                ((BTrue) (Cons _ (MkPos ol $ Succ oc) ts))
                ((BFalse) ts)))
            (values (Cons _ (MkIndentLine (MkPos ol $ Succ oc) oc d) ls) ts1))))
      (MkIndentSt l c d op (nat-eq l ol) t u ls2 ts2))))

(def-fns _ $ (many ind-delim : (many (Char) c) (many (IndentSt) st) ->
    (many (Bool) comment) (many (IndentSt) st2))
  (let ((many n)) (char-code c))
  (match many (nat-eq n 59) _
    ((BTrue) (values (BTrue) (ind-plain st)))
    ((BFalse)
      (match many (nat-eq n 40) _
        ((BTrue) (values (BFalse) (ind-open st)))
        ((BFalse)
          (match many (nat-eq n 41) _
            ((BTrue) (values (BFalse) (ind-close st)))
            ((BFalse)
              (match many (nat-eq n 10) _
                ((BTrue) (values (BFalse) (ind-nl st)))
                ((BFalse)
                  (match many (nat-eq n 9) _
                    ((BTrue) (values (BFalse) (ind-tab st)))
                    ((BFalse) (values (BFalse) (ind-plain st)))))))))))))

; Five modes over the source: between tokens, inside a word, inside a comment, and inside a string literal
; or its escape. A word runs to a delimiter, which a quote is not, so only a quote met between tokens opens
; a literal, as in the tokenizer above. The scan stops where the tokenizer's lexing would, at an unterminated
; literal or an escape it does not know, so that what is reported is what was read, as in lib/indent.ml.
(def-fns _
  ((many ind-scan : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (match many s _
      ((SNil) st)
      ((SCons c rest)
        (match many (is-delim c) _
          ((BTrue)
            (let ((many comment) (many st2)) (ind-delim c st))
            (match many comment _
              ((BTrue) (tail $ ind-comment rest st2))
              ((BFalse) (tail $ ind-scan rest st2))))
          ((BFalse)
            (match many (char-is c 34) _
              ((BTrue)
                (match many st (((IndentSt) _))
                  ((MkIndentSt l cl _ _ sd t _ _ _) (tail $ ind-str rest (ind-plain st) l cl sd t))))
              ((BFalse) (tail $ ind-word rest (ind-plain $ ind-mark st)))))))))
  ((many ind-word : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (match many s _
      ((SNil) st)
      ((SCons c rest)
        (match many (is-delim c) _
          ((BTrue)
            (let ((many comment) (many st2)) (ind-delim c st))
            (match many comment _
              ((BTrue) (tail $ ind-comment rest st2))
              ((BFalse) (tail $ ind-scan rest st2))))
          ((BFalse) (tail $ ind-word rest (ind-plain st)))))))
  ((many ind-comment : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (match many s _
      ((SNil) st)
      ((SCons c rest)
        (match many (char-is c 10) _
          ((BTrue) (tail $ ind-scan rest (ind-nl st)))
          ((BFalse) (tail $ ind-comment rest (ind-plain st)))))))
  ((many ind-str : (subterm many (String) s) (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc)
       (many (Bool) os) (many (Bool) ot) -> (many (IndentSt) r))
    (match many s _
      ((SNil) st)
      ((SCons c rest)
        (match many (char-is c 34) _
          ((BTrue) (tail $ ind-scan rest (ind-close-str (ind-plain st) ol oc os ot)))
          ((BFalse)
            (match many (char-is c 92) _
              ((BTrue) (tail $ ind-str-esc rest (ind-plain st) ol oc os ot))
              ((BFalse)
                (match many (char-is c 10) _
                  ((BTrue) (tail $ ind-str rest (ind-nl st) ol oc os ot))
                  ((BFalse)
                    (match many (char-is c 9) (((IndentSt) _))
                      ((BTrue) (tail $ ind-str rest (ind-tab st) ol oc os ot))
                      ((BFalse) (tail $ ind-str rest (ind-plain st) ol oc os ot))))))))))))
  ((many ind-str-esc : (subterm many (String) s) (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc)
       (many (Bool) os) (many (Bool) ot) -> (many (IndentSt) r))
    (match many s _
      ((SNil) st)
      ((SCons c rest)
        (match many (escape-ok c) _
          ((BFalse) st)
          ((BTrue) (tail $ ind-str rest (ind-plain st) ol oc os ot)))))))

(def-fns _ $ (many ind-cat : (subterm many (List $ String) parts) -> (many (String) r))
  (match many parts _
    ((Nil _) (SNil))
    ((Cons _ p rest) (str-cat p $ notail $ ind-cat rest))))

(def-fns _ $ (many ind-msg : (many (String) path) (many (Pos) pos) (many (String) kind)
    (many (String) msg) -> (many (String) r))
  (match many pos _
    ((MkPos line col)
      (ind-cat
        $ Cons _ path
        $ Cons _ ":"
        $ Cons _ (nat-str line)
        $ Cons _ ":"
        $ Cons _ (nat-str col)
        $ Cons _ kind
        $ Cons _ msg
        $ Nil _))))

(def-fns _ $ (many ind-at : (many (String) path) (many (Pos) pos) (many (String) msg) -> (many (String) r))
  (ind-msg path pos ": warning: " msg))

; A note is the second location the warning before it talks about: each of these rules compares two lines,
; and the line compared against is worth naming rather than describing.
(def-fns _ $ (many ind-note : (many (String) path) (many (Pos) pos) (many (String) msg) -> (many (String) r))
  (ind-msg path pos ": note: " msg))

(def-fns _ $ (many ind-msg-same : (many (Nat) i) (many (Nat) n) (many (Nat) tn) -> (many (String) r))
  (ind-cat
    $ Cons _ "same indentation ("
    $ Cons _ (nat-str i)
    $ Cons _ ") as the previous checked line but nesting is "
    $ Cons _ (nat-str n)
    $ Cons _ ", expected "
    $ Cons _ (nat-str tn)
    $ Cons _ " (matching that line)"
    $ Nil _))

(def-fns _ $ (many ind-msg-deeper : (many (Nat) ti) (many (Nat) i) (many (Nat) tn) (many (Nat) n) ->
    (many (String) r))
  (ind-cat
    $ Cons _ "indentation increased ("
    $ Cons _ (nat-str ti)
    $ Cons _ " -> "
    $ Cons _ (nat-str i)
    $ Cons _ ") but nesting did not increase ("
    $ Cons _ (nat-str tn)
    $ Cons _ " -> "
    $ Cons _ (nat-str n)
    $ Cons _ ")"
    $ Nil _))

(def-fns _ $ (many ind-msg-pop : (many (Nat) ei) (many (Nat) en) (many (Nat) n) -> (many (String) r))
  (ind-cat
    $ Cons _ "dedented past indentation "
    $ Cons _ (nat-str ei)
    $ Cons _ " (nesting "
    $ Cons _ (nat-str en)
    $ Cons _ "), but this line's nesting is "
    $ Cons _ (nat-str n)
    $ Cons _ " (expected less than "
    $ Cons _ (nat-str en)
    $ Cons _ ")"
    $ Nil _))

(def-fns _ $ (many ind-msg-enclosing : (many (Nat) i) (many (Nat) ei) (many (Nat) en) (many (Nat) n) ->
    (many (String) r))
  (ind-cat
    $ Cons _ "dedented to indentation "
    $ Cons _ (nat-str i)
    $ Cons _ ", but an enclosing line at indentation "
    $ Cons _ (nat-str ei)
    $ Cons _ " has nesting "
    $ Cons _ (nat-str en)
    $ Cons _ ", not less than this line's "
    $ Cons _ (nat-str n)
    $ Nil _))

(def-fns _ $ (many ind-msg-back : (many (Nat) i) (many (Nat) en) (many (Nat) n) -> (many (String) r))
  (ind-cat
    $ Cons _ "dedented back to indentation "
    $ Cons _ (nat-str i)
    $ Cons _ ", matching an earlier line, but nesting is "
    $ Cons _ (nat-str en)
    $ Cons _ " there vs "
    $ Cons _ (nat-str n)
    $ Cons _ " here"
    $ Nil _))

; Naming where each form left open was opened says where each missing ) goes, which is what the reader's
; own "missing )" does not; the first is the warning and the rest its notes, innermost first.
(def-fns _ $ (many ind-unclosed : (many (String) path) (subterm many (List $ Pos) opens) (many (Bool) first)
    (many (List $ String) acc) -> (many (List $ String) r))
  (match many opens _
    ((Nil _) acc)
    ((Cons _ o more)
      (let ((many (String) line))
        (match many first (((String) _))
          ((BTrue) (ind-at path o "this form is never closed"))
          ((BFalse) (ind-note path o "and this one"))))
      (tail $ ind-unclosed path more (BFalse) $ Cons _ line acc))))

(def-fns _ $ (many ind-tabs : (many (String) path) (subterm many (List $ Pos) ts)
    (many (List $ String) acc) -> (many (List $ String) r))
  (match many ts _
    ((Nil _) acc)
    ((Cons _ l more)
      (tail $ ind-tabs path more
        $ Cons _ (ind-at path l "indentation uses a tab, not spaces only") acc))))

(def-fns _ $ (many ind-pop : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (subterm many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) rest) (many (List $ String) acc2))
  (match many stack _
    ((Nil _) (values stack acc))
    ((Cons _ e more)
      (match many e _
        ((MkIndLevel ep ei en)
          (match many (nat-lt i ei) _
            ((BFalse) (values stack acc))
            ((BTrue)
              (let ((many (List $ String) acc1))
                (match many (nat-lt n en) (((List $ String) _))
                  ((BTrue) acc)
                  ((BFalse)
                    (Cons _ (ind-note path ep "the line at that indentation")
                      $ Cons _ (ind-at path ln $ ind-msg-pop ei en n) acc))))
              (tail $ ind-pop path ln i n more acc1))))))))

(def-fns _ $ (many ind-enclosing : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (subterm many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ String) acc2))
  (match many stack _
    ((Nil _) acc)
    ((Cons _ e more)
      (match many e _
        ((MkIndLevel ep ei en)
          (let ((many (List $ String) acc1))
            (match many (and (nat-lt ei i) (not $ nat-lt en n)) (((List $ String) _))
              ((BFalse) acc)
              ((BTrue)
                (Cons _ (ind-note path ep "that enclosing line")
                  $ Cons _ (ind-at path ln $ ind-msg-enclosing i ei en n) acc))))
          (tail $ ind-enclosing path ln i n more acc1))))))

(def-fns _ $ (many ind-same : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (Pos) tp) (many (Nat) tn) (many (List $ IndLevel) more) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many (List $ String) acc1))
    (match many (nat-eq n tn) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (ind-note path tp "the previous line at this indentation")
          $ Cons _ (ind-at path ln $ ind-msg-same i n tn) acc))))
  (values (Cons _ (MkIndLevel ln i n) more) acc1))

(def-fns _ $ (many ind-deeper : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (Pos) tp) (many (Nat) ti) (many (Nat) tn) (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many (List $ String) acc1))
    (match many (nat-lt tn n) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (ind-note path tp "the line before it")
          $ Cons _ (ind-at path ln $ ind-msg-deeper ti i tn n) acc))))
  (values (Cons _ (MkIndLevel ln i n) stack) acc1))

(def-fns _ $ (many ind-back : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (IndLevel) e) (many (List $ IndLevel) rest)
    (many (List $ IndLevel) rem) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (match many e _
    ((MkIndLevel ep ei en)
      (match many (nat-eq ei i) (((List $ IndLevel) _) ((List $ String) r))
        ((BFalse) (values (Cons _ (MkIndLevel ln i n) rem) acc))
        ((BTrue)
          (let ((many (List $ String) acc1))
            (match many (nat-eq en n) (((List $ String) _))
              ((BTrue) acc)
              ((BFalse)
                (Cons _ (ind-note path ep "the earlier line it matches")
                  $ Cons _ (ind-at path ln $ ind-msg-back i en n) acc))))
          (values (Cons _ (MkIndLevel ln i n) rest) acc1))))))

(def-fns _ $ (many ind-dedent : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many rem) (many acc1)) (ind-pop path ln i n stack acc))
  (let ((many acc2)) (ind-enclosing path ln i n rem acc1))
  (match many rem (((List $ IndLevel) _) ((List $ String) r))
    ((Nil _) (values (Cons _ (MkIndLevel ln i n) rem) acc2))
    ((Cons _ e2 rest2) (ind-back path ln i n e2 rest2 rem acc2))))

(def-fns _ $ (many ind-head : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (IndLevel) e) (many (List $ IndLevel) more)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (match many e _
    ((MkIndLevel tp ti tn)
      (match many (nat-eq i ti) (((List $ IndLevel) _) ((List $ String) r))
        ((BTrue) (ind-same path ln i n tp tn more acc))
        ((BFalse)
          (match many (nat-lt ti i) (((List $ IndLevel) _) ((List $ String) r))
            ((BTrue) (ind-deeper path ln i n tp ti tn stack acc))
            ((BFalse) (ind-dedent path ln i n stack acc))))))))

(def-fns _ $ (many ind-step : (many (String) path) (many (Pos) ln) (many (Nat) i) (many (Nat) n)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (match many stack _
    ((Nil _) (values (Cons _ (MkIndLevel ln i n) $ Nil _) acc))
    ((Cons _ e more) (ind-head path ln i n e more stack acc))))

(def-fns _ $ (many ind-check : (many (String) path) (subterm many (List $ IndentLine) lines)
    (many (List $ IndLevel) stack) (many (List $ String) acc) -> (many (List $ String) r))
  (match many lines _
    ((Nil _) acc)
    ((Cons _ il more)
      (match many il _
        ((MkIndentLine ln i n)
          (let ((many stack2) (many acc2)) (ind-step path ln i n stack acc))
          (tail $ ind-check path more stack2 acc2))))))

; The warnings one file's text earns, in line order: the tabs, then the nesting claims, then a surplus ) and
; the count of forms left open, which are what the reader's own error does not name.
(def-fns _ $ (many indent-warnings : (many (String) path) (many (String) src) -> (many (List $ String) ws))
  (let ((many st))
    (ind-scan src (MkIndentSt 1 0 0 (Nil _) (BFalse) (BFalse) (None _) (Nil _) (Nil _))))
  (match many st (((List $ String) _))
    ((MkIndentSt _ _ _ op _ _ u ls ts)
      (let ((many acc0)) (ind-tabs path (list-rev _ ts) (Nil _)))
      (let ((many acc1)) (ind-check path (list-rev _ ls) (Nil _) acc0))
      (let ((many (List $ String) acc2))
        (match many u (((List $ String) _))
          ((None _) acc1)
          ((Some _ sl)
            (Cons _ (ind-at path sl "a `)` here closes more than is open (surplus `)`)") acc1))))
      (let ((many acc3)) $ ind-unclosed path op (BTrue) acc2)
      (match many acc3 _ ((Nil _) acc3) ((Cons _ _ _) (list-rev _ $ Cons _ (shape-note path) acc3))))))
