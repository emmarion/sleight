; self/reader.sl -- s-expressions with $ (DESIGN.md sections 1-2), read by a structural tokenizer over the
; source string and a fold over the tokens with a stack of open forms, so nothing recurses on a computed
; suffix of the input.

; Where a token's first character sits, which every message a session writes points at (ASSUMPTIONS 194);
; both counted from one.
(def-adts $ (Spot : -> Type)
  enum
  (many MkSpot : (many (Nat) line) (many (Nat) col) -> (Spot))
  (many PosSpot : (many (Pos) p) -> (Spot)))

(def-adts
  ((Syn : -> Type)
    enum
    (many RAtom : (many (Spot) pos) (many (Name) s) -> (Syn))
    (many RWild : (many (Spot) pos) -> (Syn))
    (many RNat : (many (Spot) pos) (many (Nat) n) -> (Syn))
    (many RChr : (many (Spot) pos) (many (Nat) code) -> (Syn))
    (many RString : (many (Spot) pos) (many (String) s) -> (Syn))
    (many RList : (many (Spot) pos) (many (List $ Syn) items) -> (Syn))))

(def-fns _ $ (many raw-pos : (many (Syn) r) -> (many (Spot) pos))
  (match many r _ ((RAtom l _) l) ((RWild l) l) ((RNat l _) l) ((RChr l _) l) ((RString l _) l) ((RList l _) l)))

; Where a form's first item sits, which is what a declaration's messages name: the signature rather than
; the entry that carries it.
(def-fns _ $ (many raw-head-pos : (many (Syn) r) -> (many (Spot) pos))
  (let-match many r (RList l items) (else (raw-pos r)))
  (match many items (((Spot) _))
    ((Cons _ h _) (raw-pos h))
    ((Nil _) l)))

(def-adts $ (Tok : -> Type)
  enum
  (many TOpen : (many (Spot) pos) -> (Tok))
  (many TClose : (many (Spot) pos) -> (Tok))
  (many TDollar : (many (Spot) pos) -> (Tok))
  (many TItem : (many (Syn) r) -> (Tok))
  (many TError : (many (Spot) pos) (many (String) msg) -> (Tok))
  (many TPragma : (many (Spot) pos) (many (List $ Syn) words) -> (Tok)))

; A syntax error and where it is reported.
(def-adts $ (SynErr : -> Type)
  enum
  (many MkSynErr : (many (Spot) pos) (many (String) msg) (many (Bool) paren) (many (Maybe $ Pair (Spot) (String)) note) -> (SynErr)))

(def-adts $ (Region : -> Type)
  enum
  (many MkRegion : (many (Nat) index) (many (String) name) (many (Spot) from) (many (Maybe $ Spot) until) -> (Region)))

(def-fns _ $ (many spot-coords : (many (Spot) p) -> (many (Nat) line) (many (Nat) col))
  (let-match many p (PosSpot q) ((MkSpot l c) (values l c)))
  (match many q (((Nat) l) ((Nat) c)) ((NoPos) (values 0 0)) ((MkPos _ l c) (values l c))))

(def-fns _ $ (many pos-lt : (many (Spot) a) (many (Spot) b) -> (many (Bool) r))
  (let ((many al) (many ac)) $ spot-coords a)
  (let ((many bl) (many bc)) $ spot-coords b)
  (or (nat-lt al bl) $ and (nat-eq al bl) $ nat-lt ac bc))

(def-fns _ $ (many region-covers : (many (Region) r) (many (Spot) p) -> (many (Bool) b))
  (match many r _ ((MkRegion _ _ from until)
    (and (not $ pos-lt p from) $ match many until (((Bool) _)) ((None _) (BTrue)) ((Some _ u) (pos-lt p u))))))

(def-fns _ $ (many region-named : (subterm many (List $ Region) rs) (many (String) name) -> (many (Maybe $ Region) r))
  (let-match many rs (Cons _ r rest)
    ((Nil _) (None _)))
  (let-match many r (MkRegion _ n _ _))
  (match many (str-eq n name) _ ((BTrue) (Some _ r)) ((BFalse) (tail $ region-named rest name))))

(def-fns _ $ (many region-drop : (subterm many (List $ Region) rs) (many (String) name) -> (many (List $ Region) r))
  (let-match many rs (Cons _ r rest)
    ((Nil _) rs))
  (let-match many r (MkRegion _ n _ _))
  (match many (str-eq n name) _ ((BTrue) rest) ((BFalse) (Cons _ r $ notail $ region-drop rest name))))

(def-fns _ $ (many region-insert : (many (Region) r) (subterm many (List $ Region) rs) -> (many (List $ Region) out))
  (let-match many rs (Cons _ q rest) ((Nil _) (Cons _ r rs)))
  (let-match many r (MkRegion i _ _ _))
  (let-match many q (MkRegion j _ _ _))
  (match many (nat-lt i j) _ ((BTrue) (Cons _ r rs)) ((BFalse) (Cons _ q $ notail $ region-insert r rest))))

(def-fns _ $ (many regions-sorted : (subterm many (List $ Region) rs) (many (List $ Region) acc) -> (many (List $ Region) out))
  (match many rs _
    ((Nil _) acc)
    ((Cons _ r rest) (tail $ regions-sorted rest $ region-insert r acc))))

; A parenthesis a file gets wrong is found faster with bin/shape than from the one position a message names
; (lib/reader.ml's shape_note).
(def-fns _ $ (many shape-note : (many (String) path) -> (many (String) r))
  (str-cat path ": note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes"))

(def-fns _ $ (many is-delim : (many (Char) c) -> (many (Bool) r))
  (let ((many n)) $ char-code c)
  (let-match many (nat-lt n 33) (BFalse) ((BTrue) (BTrue)))
  (let-match many (nat-lt 59 n) (BFalse) ((BTrue) (BFalse)))
  (or (nat-eq n 40) $ or (nat-eq n 41) $ nat-eq n 59))

(def-fns _ $ (many word-item : (many (Spot) pos) (many (String) w) -> (many (Tok) t))
  (let-match many (str-eq w "_") (BFalse) ((BTrue) (TItem $ RWild pos)))
  (let-match many (is-reserved-name w) (BFalse)
    ((BTrue) (TError pos $ str-cat3 (str-cat3 "`" w "` begins with `__`, which is reserved for the compilers' messages; write it `") (spell-text w) "`")))
  (let-match many (literal-error w) (None _) ((Some _ msg) (TError pos msg)))
  (match many (classify w) _
    ((LName) (TItem $ RAtom pos $ NSrc w))
    ((LNumeral) (TItem $ RNat pos $ parse-nat w 0))
    ((LChar) (TItem $ RChr pos $ match many (char-lit-code w) (((Nat) _)) ((Some _ n) n) ((None _) 0)))))

(def-fns _ $ (many word-tok : (many (Spot) pos) (many (String) start) (many (Nat) k) (erased (Nat) len) (erased (StrLength start len) l) (erased (Nat) rl) (erased (Add k rl len) sum) -> (many (Tok) t))
  (let ((many w) (many _) (erased _) (erased _)) (str-split start k len l (add-le-left k rl len sum)))
  (match many (str-cmp w "$") _
    ((CEq _ _ _) (TDollar pos))
    (else (word-item pos w))))

(def-adts $ (StrKind : -> Type)
  enum
  (many SKLit : -> (StrKind))
  (many SKName : -> (StrKind))
  (many SKPragma : (many (Spot) pos) (many (List $ Syn) words) -> (StrKind)))

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

(def-fns _ $ (many bad-escape : (many (Spot) pos) (many (Char) e) -> (many (Tok) t))
  (TError pos $ rope-str $ RCat (RStr "unknown escape \\") $ RChar e))

(def-fns _ $ (many end-toks : (many (Tok) t) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (list-rev _ $ Cons _ t acc))

(def-fns _ $ (many unterminated : (many (Spot) pos) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (end-toks (TError pos "unterminated string literal") acc))

; [col] counts the characters read on the current line, so the character being read sits at column
; (Succ col); a newline starts the next line over at zero.
(def-fns _ $ (many delim-step : (many (Char) c) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) ->
    (many (Bool) comment) (many (Nat) line2) (many (Nat) col2) (many (List $ Tok) acc2))
  (let ((many n)) $ char-code c)
  (let-match many (nat-eq n 59) (BFalse) ((BTrue) (values (BTrue) line (Succ col) acc)))
  (let-match many (nat-eq n 40) (BFalse) ((BTrue) (values (BFalse) line (Succ col) $ Cons _ (TOpen $ MkSpot line $ Succ col) acc)))
  (let-match many (nat-eq n 41) (BFalse)
    ((BTrue) (values (BFalse) line (Succ col) $ Cons _ (TClose $ MkSpot line $ Succ col) acc)))
  (match many (nat-eq n 10) _
    ((BTrue) (values (BFalse) (Succ line) 0 acc))
    ((BFalse) (values (BFalse) line (Succ col) acc))))

(def-fns _ $ (many pragma-limit : (many (List $ Syn) words) -> (many (Nat) n))
  (let-match many (list-rev _ words) (Cons _ w _)
    ((Nil _) 3))
  (let-match many w (RAtom _ n) (else 3))
  (let-match many n (NSrc s) (else 3))
  (match many (str-eq s "warn") _ ((BTrue) 2) ((BFalse) 3)))

(def-fns _ $ (many pragma-field : (many (Maybe $ Spot) start) (many (Rope) cur) (many (List $ Syn) words) -> (many (List $ Syn) r))
  (let ((many text)) $ rope-str cur)
  (match many start _
    ((None _) words)
    ((Some _ p) (Cons _ (RAtom p $ NSrc text) words))))

(def-fns _ $ (many pragma-tok : (many (Spot) pos) (many (Maybe $ Spot) start) (many (Rope) cur) (many (List $ Syn) words) -> (many (Tok) t))
  (TPragma pos $ list-rev _ $ pragma-field start cur words))

; Tokens accumulate reversed in [acc]; an atom's or a literal's characters accumulate as a rope; [line] and
; [col] count the newlines and the characters passed, and a token is placed where it starts, a string
; literal's at its opening quote, as the reference reader places one.
(def-fns _
  ((many tokenize : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (list-rev _ acc)))
    (match many (is-delim c) _
      ((BTrue)
        (let ((many comment) (many line2) (many col2) (many acc2)) $ delim-step c line col acc)
        (match many comment _ ((BTrue) (tail $ comment-start rest line2 col2 acc2)) ((BFalse) (tail $ tokenize rest line2 col2 acc2))))
      ((BFalse)
        (let-match many (char-is c 34) (BFalse)
          ((BTrue) (tail $ string-lit rest line (Succ col) (MkSpot line $ Succ col) (SKLit) (REmpty) acc)))
        (let-match many (and (char-is c 35) $ str-starts "\"" rest) (BFalse)
          ((BTrue)
            (let-match many rest (SCons _ rest2) ((SNil) (list-rev _ acc)))
            (tail $ string-lit rest2 line (Succ (Succ col)) (MkSpot line $ Succ col) (SKName) (REmpty) acc)))
        (let ((erased len) (erased l)) (str-length s))
        (let-match erased l (SLenCons _ _ rl lr))
        (tail $ word rest line (Succ col) s len l (Succ (Zero)) rl lr (AddSucc (Zero) rl rl (AddZero rl)) (MkSpot line $ Succ col) acc))))
  ((many comment-start : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (list-rev _ acc)))
    (let-match many (char-is c 33) (BFalse)
      ((BTrue) (tail $ pragma-line rest line (Succ col) (MkSpot line col) (Nil _) (None _) (REmpty) (REmpty) acc)))
    (match many (char-is c 10) _
      ((BTrue) (tail $ tokenize rest (Succ line) 0 acc))
      ((BFalse) (tail $ skip-comment rest line acc))))
  ((many pragma-line : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Spot) pos) (many (List $ Syn) words)
      (many (Maybe $ Spot) start) (many (Rope) cur) (many (Rope) blanks) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (end-toks (pragma-tok pos start cur words) acc)))
    (let-match many (char-is c 10) (BFalse)
      ((BTrue) (tail $ tokenize rest (Succ line) 0 $ Cons _ (pragma-tok pos start cur words) acc)))
    (match many (or (char-is c 32) $ or (char-is c 9) $ char-is c 13) _
      ((BTrue)
        (let-match many start (Some _ _) ((None _) (tail $ pragma-line rest line (Succ col) pos words start cur blanks acc)))
        (match many (nat-lt (list-length _ words) $ pragma-limit words) _
          ((BTrue) (tail $ pragma-line rest line (Succ col) pos (pragma-field start cur words) (None _) (REmpty) (REmpty) acc))
          ((BFalse) (tail $ pragma-line rest line (Succ col) pos words start cur (RCat blanks $ RChar c) acc))))
      ((BFalse)
        (let-match many start (None _)
          ((Some _ _) (tail $ pragma-line rest line (Succ col) pos words start (RCat (RCat cur blanks) $ RChar c) (REmpty) acc)))
        (let-match many (and (nat-lt (list-length _ words) $ pragma-limit words) $ and (char-is c 35) $ str-starts "\"" rest) (BFalse)
          ((BTrue)
            (let-match many rest (SCons _ rest2) ((SNil) (list-rev _ acc)))
            (tail $ string-lit rest2 line (Succ (Succ col)) (MkSpot line $ Succ col) (SKPragma pos words) (REmpty) acc)))
        (tail $ pragma-line rest line (Succ col) pos words (Some _ $ MkSpot line $ Succ col) (RChar c) (REmpty) acc))))
  ((many skip-comment : (subterm many (String) s) (many (Nat) line) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (list-rev _ acc)))
    (match many (char-is c 10) _
      ((BTrue) (tail $ tokenize rest (Succ line) 0 acc))
      ((BFalse) (tail $ skip-comment rest line acc))))
  ((many word : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (String) start) (erased (Nat) len) (erased (StrLength start len) l) (many (Nat) k) (erased (Nat) rl) (erased (StrLength s rl) lr) (erased (Add k rl len) sum) (many (Spot) pos) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (end-toks (word-tok pos start k len l rl sum) acc)))
    (match many (is-delim c) _
      ((BTrue)
        (let ((many comment) (many line2) (many col2) (many acc2)) $ delim-step c line col $ Cons _ (word-tok pos start k len l rl sum) acc)
        (match many comment _ ((BTrue) (tail $ comment-start rest line2 col2 acc2)) ((BFalse) (tail $ tokenize rest line2 col2 acc2))))
      ((BFalse)
        (let-match erased lr (SLenCons _ _ rl1 lr1))
        (tail $ word rest line (Succ col) start len l (Succ k) rl1 lr1 (add-shift k rl1 len sum) pos acc))))
  ((many string-lit : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Spot) pos) (many (StrKind) kind) (many (Rope) rev) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (unterminated (MkSpot line $ Succ col) acc)))
    (let ((many n)) $ char-code c)
    (let-match many (nat-eq n 34) (BFalse)
      ((BTrue)
        (let ((many body)) $ rope-str rev)
        (match many kind _
          ((SKLit) (tail $ tokenize rest line (Succ col) $ Cons _ (TItem $ RString pos body) acc))
          ((SKName) (tail $ tokenize rest line (Succ col) $ Cons _ (TItem $ RAtom pos $ NSrc body) acc))
          ((SKPragma pp ws) (tail $ pragma-line rest line (Succ col) pp (Cons _ (RAtom pos $ NSrc body) ws) (None _) (REmpty) (REmpty) acc)))))
    (match many (nat-eq n 92) _
      ((BTrue)
        (let-match many rest (SCons e rest2) ((SNil) (unterminated (MkSpot line $ Succ col) acc)))
        (let-match many (char-is e 120) (BTrue)
          ((BFalse)
            (match many (escape-ok e) _
              ((BTrue) (tail $ string-lit rest2 line (Succ (Succ col)) pos kind (RCat rev $ RChar $ unescape e) acc))
              ((BFalse) (end-toks (bad-escape (MkSpot line $ Succ col) e) acc)))))
        (let ((many hex)) $ match many rest2 (((Maybe $ Char) _))
          ((SCons h1 r3) (match many r3 (((Maybe $ Char) _)) ((SCons h2 _) (hex-pair h1 h2)) ((SNil) (None _))))
          ((SNil) (None _)))
        (let-match many hex (Some _ b) ((None _) (end-toks (bad-escape (MkSpot line $ Succ col) e) acc)))
        (let-match many rest2 (SCons _ r3) ((SNil) (unterminated (MkSpot line $ Succ col) acc)))
        (let-match many r3 (SCons _ r4) ((SNil) (unterminated (MkSpot line $ Succ col) acc)))
        (tail $ string-lit r4 line (nat-add col 4) pos kind (RCat rev $ RChar b) acc))
      ((BFalse)
        (let-match many (nat-eq n 10) (BTrue) ((BFalse) (tail $ string-lit rest line (Succ col) pos kind (RCat rev $ RChar c) acc)))
        (let-match many kind (SKPragma _ _) (else (tail $ string-lit rest (Succ line) 0 pos kind (RCat rev $ RChar c) acc)))
        (end-toks (TError pos "a pragma ends with its line") acc)))))

; A frame is an open form: where it opened, whether $ opened it, and its items so far, reversed.
(def-adts $ (Frame : -> Type)
  enum
  (many MkFrame : (many (Spot) pos) (many (Bool) dollar) (many (List $ Syn) items) -> (Frame)))

(def-fns _ $ (many push-item : (many (Syn) item) (many (List $ Frame) stack) -> (many (List $ Frame) r))
  (let-match many stack (Cons _ f rest) ((Nil _) (Cons _ (MkFrame (MkSpot 1 1) (BFalse) $ Cons _ item $ Nil _) $ Nil _)))
  (match many f _
    ((MkFrame l d items) (Cons _ (MkFrame l d $ Cons _ item items) rest))))

; Closes the top frame into its parent as a list.
(def-fns _ $ (many close-top : (many (List $ Frame) stack) -> (many (List $ Frame) r))
  (let-match many stack (Cons _ f rest) ((Nil _) stack))
  (match many f _
    ((MkFrame l _ items) (push-item (RList l $ list-rev _ items) rest))))

; Closes every $-opened frame on top of the stack, each into the frame below it.
(def-fns _
  ((many close-dollars : (subterm many (List $ Frame) stack) -> (many (List $ Frame) r))
    (let-match many stack (Cons _ f rest) ((Nil _) stack))
    (let-match many f (MkFrame l d items))
    (match many d _
      ((BFalse) stack)
      ((BTrue) (tail $ close-into rest $ RList l $ list-rev _ items))))
  ((many close-into : (subterm many (List $ Frame) stack) (many (Syn) item) -> (many (List $ Frame) r))
    (let-match many stack (Cons _ f rest) ((Nil _) (push-item item stack)))
    (let-match many f (MkFrame l d items))
    (match many d _
      ((BFalse) (Cons _ (MkFrame l d $ Cons _ item items) rest))
      ((BTrue) (tail $ close-into rest $ RList l $ list-rev _ $ Cons _ item items)))))

; The stack starts with a root frame; a ) closes the $ frames above the nearest ( frame and then that
; frame; a ) with only the root open, a form still open at the end, or a bad token is a syntax error
; (DESIGN.md section 2).
(def-fns _ $ (many is-atom-text : (many (Syn) r) (many (String) x) -> (many (Bool) b))
  (let-match many r (RAtom _ y) (else (BFalse)))
  (let-match many y (NSrc t) (else (BFalse)))
  (str-eq x t))

(def-fns _ $ (many syn-err : (many (Spot) l) (many (String) m) -> (many (Maybe $ SynErr) e))
  (Some _ $ MkSynErr l m (BFalse) $ None _))

(def-fns _ $ (many parse-toks : (subterm many (List $ Tok) toks) (many (List $ Frame) stack) (many (List $ Region) opened) (many (List $ Region) closed) ->
    (many (List $ Frame) r) (many (Maybe $ SynErr) err) (many (List $ Region) regions))
  (let-match many toks (Cons _ t rest) ((Nil _) (values stack (None _) $ regions-sorted opened $ regions-sorted closed $ Nil _)))
  (match many t _
    ((TOpen l) (tail $ parse-toks rest (Cons _ (MkFrame l (BFalse) $ Nil _) stack) opened closed))
    ((TDollar l) (tail $ parse-toks rest (Cons _ (MkFrame l (BTrue) $ Nil _) stack) opened closed))
    ((TItem r) (tail $ parse-toks rest (push-item r stack) opened closed))
    ((TError l m) (values stack (syn-err l m) closed))
    ((TPragma l ws)
      (let-match many ws (Cons _ w args) ((Nil _) (values stack (syn-err l "a pragma needs a word after `;!`") closed)))
      (let-match many w (RAtom wl kn) (else (values stack (syn-err l "a pragma needs a word after `;!`") closed)))
      (let-match many kn (NSrc kw) (else (values stack (syn-err l "a pragma needs a word after `;!`") closed)))
      (match many (str-eq kw "warn") _
        ((BTrue)
          (match many (nat-lt (list-length _ stack) 2) _
            ((BTrue) (tail $ parse-toks rest (push-item (RList l $ Cons _ (RAtom l $ NSrc ";!") ws) stack) opened closed))
            ((BFalse) (values stack (syn-err l "`;! warn` must be written between top-level forms") closed))))
        ((BFalse)
          (let-match many (or (str-eq kw "suppress") $ str-eq kw "restore") (BTrue)
            ((BFalse) (values stack (syn-err wl $ str-cat3 "unknown pragma `" kw "`") closed)))
          (let ((many (Maybe $ String) name)) $ match many args _
            ((Cons _ a more)
              (let-match many (and (is-atom-text a "warn") $ not $ list-is-empty _ more) (BTrue)
                ((BFalse) (None _)))
              (let-match many more (Cons _ n _) ((Nil _) (None _)))
              (let-match many n (RAtom _ x) (else (None _)))
              (let-match many x (NSrc text) (else (None _)))
              (Some _ text))
            ((Nil _) (None _)))
          (let-match many name (Some _ n) ((None _) (values stack (syn-err l $ str-cat3 "`;! " kw "` takes `warn NAME`") closed)))
          (match many (str-eq kw "suppress") _
            ((BTrue)
              (let-match many (region-named opened n) (Some _ first)
                ((None _) (tail $ parse-toks rest stack (Cons _ (MkRegion (nat-add (list-length _ opened) $ list-length _ closed) n l $ None _) opened) closed)))
              (match many first _ ((MkRegion _ _ fp _)
                (values stack (Some _ $ MkSynErr l (str-cat3 "`;! suppress warn` for `" n "` is already open") (BFalse) $ Some _ $ MkPair _ _ fp "opened here") closed))))
            ((BFalse)
              (let-match many (region-named opened n) (Some _ r)
                ((None _) (values stack (syn-err l $ str-cat3 "`;! restore warn` for `" n "` has no open `;! suppress warn`") closed)))
              (match many r _ ((MkRegion i _ from _)
                (tail $ parse-toks rest stack (region-drop opened n) $ Cons _ (MkRegion i n from $ Some _ l) closed))))))))
    ((TClose l)
      (let ((many s1)) $ close-dollars stack)
      (let-match many s1 (Cons _ _ s2) ((Nil _) (values s1 (Some _ $ MkSynErr l "unexpected `)`" (BTrue) $ None _) closed)))
      (match many s2 _
        ((Nil _) (values s1 (Some _ $ MkSynErr l "unexpected `)`" (BTrue) $ None _) closed))
        ((Cons _ _ _) (tail $ parse-toks rest (close-top s1) opened closed))))))

; Reads the root frame's items once nothing is open; an open form at the end is a missing ), reported
; for the innermost, which is the $ form's when that is what is open, at the line the form opened on.
(def-fns _ $ (many finish-stack : (many (List $ Frame) stack) -> (many (List $ Syn) items) (many (Maybe $ SynErr) err))
  (let-match many stack (Cons _ f rest) ((Nil _) (values (Nil _) $ None _)))
  (let-match many rest (Cons _ _ _) ((Nil _) (match many f _ ((MkFrame _ _ items) (values (list-rev _ items) $ None _)))))
  (match many f _
    ((MkFrame l d _) (values (Nil _) $ Some _ $ MkSynErr l (match many d (((String) _)) ((BTrue) "missing `)` after `$`") ((BFalse) "missing `)`")) (BTrue) $ None _))))

(def-fns _ $ (many parse : (many (String) src) -> (many (List $ Syn) items) (many (Maybe $ SynErr) err) (many (List $ Region) regions))
  (let ((many stack) (many err) (many regions)) (parse-toks (tokenize src 1 0 $ Nil _)
                                            (Cons _ (MkFrame (MkSpot 1 1) (BFalse) $ Nil _) $ Nil _) (Nil _) (Nil _)))
  (let-match many err (None _) ((Some _ _) (values (Nil _) err $ Nil _)))
  (let ((many items) (many err2)) $ finish-stack stack)
  (values items err2 regions))

(def-fns _
  ((many show-raw : (subterm many (Syn) r) -> (many (Rope) out))
    (match many r _
      ((RAtom _ s) (RStr $ spell-name s))
      ((RWild _) (RStr "_"))
      ((RNat _ n) (RStr $ nat-str n))
      ((RChr _ c) (lit-char-rope c))
      ((RString _ s) (lit-string-rope s))
      ((RList _ items) (rwrap "(" (rjoin (notail $ show-raws items) " ") ")"))))
  ((many show-raws : (subterm many (List $ Syn) rs) -> (many (List $ Rope) out))
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
  (many MkIndLevel : (many (Spot) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndLevel)))

(def-adts $ (IndentLine : -> Type)
  enum
  (many MkIndentLine : (many (Spot) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndentLine)))

; The scan's state: the line and the characters seen on it, the paren depth and where each form still open
; was opened, innermost first, whether a token has started on this line and whether a tab sits in what
; precedes it, the first ) that closed more than was open, and the lines checked and the lines carrying a
; tab, both reversed.
(def-adts $ (IndentSt : -> Type)
  enum
  (many MkIndentSt : (many (Nat) line) (many (Nat) col) (many (Nat) depth) (many (List $ Spot) opens)
      (many (Bool) started) (many (Bool) tabbed) (many (Maybe $ Spot) surplus)
      (many (List $ IndentLine) lines) (many (List $ Spot) tabs) -> (IndentSt)))

(def-fns _ $ (many ind-nl : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l _ d op _ _ u ls ts) (MkIndentSt (Succ l) 0 d op (BFalse) (BFalse) u ls ts))))

(def-fns _ $ (many ind-plain : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l c d op s t u ls ts) (MkIndentSt l (Succ c) d op s t u ls ts))))

; A tab is recorded for the line it sits on whatever is being read there, a literal included: what the check
; reads is the text between the start of a line and the first token attributed to it.
(def-fns _ $ (many ind-tab : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many st _ ((MkIndentSt l c d op s _ u ls ts) (MkIndentSt l (Succ c) d op s (BTrue) u ls ts))))

(def-fns _ $ (many ind-mark : (many (IndentSt) st) -> (many (IndentSt) r))
  (let-match many st (MkIndentSt l c d op s t u ls ts))
  (let-match many s (BFalse) ((BTrue) st))
  (let ((many (List $ Spot) ts2))
    (match many t (((List $ Spot) _))
      ((BTrue) (Cons _ (MkSpot l $ Succ c) ts))
      ((BFalse) ts)))
  (MkIndentSt l c d op (BTrue) t u (Cons _ (MkIndentLine (MkSpot l $ Succ c) c d) ls) ts2))

(def-fns _ $ (many ind-open : (many (IndentSt) st) -> (many (IndentSt) r))
  (match many (ind-plain $ ind-mark st) _
    ((MkIndentSt l c d op s t u ls ts) (MkIndentSt l c (Succ d) (Cons _ (MkSpot l c) op) s t u ls ts))))

; A ) with nothing open is recorded where it sits and leaves the depth at zero, so the lines after it are
; still checked against the count of forms actually open.
(def-fns _ $ (many ind-close : (many (IndentSt) st) -> (many (IndentSt) r))
  (let-match many (ind-plain $ ind-mark st) (MkIndentSt l c d op s t u ls ts))
  (match many d _
    ((Succ p)
      (let ((many (List $ Spot) op2))
        (match many op (((List $ Spot) _))
          ((Cons _ _ more) more)
          ((Nil _) op)))
      (MkIndentSt l c p op2 s t u ls ts))
    ((Zero)
      (let ((many (Maybe $ Spot) u2))
        (match many u (((Maybe $ Spot) _))
          ((Some _ _) u)
          ((None _) (Some _ $ MkSpot l c))))
      (MkIndentSt l c 0 op s t u2 ls ts))))

; A string literal's token sits at its opening quote, so the line it opened on is recorded once the literal
; closes, and an unterminated one is no token at all, the reference reader emitting none for it.
(def-fns _ $ (many ind-close-str : (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc) (many (Bool) os)
    (many (Bool) ot) -> (many (IndentSt) r))
  (let-match many st (MkIndentSt l c d op _ t u ls ts))
  (let ((many (List $ IndentLine) ls2) (many (List $ Spot) ts2))
    (match many os (((List $ IndentLine) _) ((List $ Spot) y))
      ((BTrue) (values ls ts))
      ((BFalse)
        (let ((many (List $ Spot) ts1))
          (match many ot (((List $ Spot) _))
            ((BTrue) (Cons _ (MkSpot ol $ Succ oc) ts))
            ((BFalse) ts)))
        (values (Cons _ (MkIndentLine (MkSpot ol $ Succ oc) oc d) ls) ts1))))
  (MkIndentSt l c d op (nat-eq l ol) t u ls2 ts2))

(def-fns _ $ (many ind-delim : (many (Char) c) (many (IndentSt) st) ->
    (many (Bool) comment) (many (IndentSt) st2))
  (let ((many n)) (char-code c))
  (let-match many (nat-eq n 59) (BFalse) ((BTrue) (values (BTrue) (ind-plain st))))
  (let-match many (nat-eq n 40) (BFalse) ((BTrue) (values (BFalse) (ind-open st))))
  (let-match many (nat-eq n 41) (BFalse) ((BTrue) (values (BFalse) (ind-close st))))
  (let-match many (nat-eq n 10) (BFalse) ((BTrue) (values (BFalse) (ind-nl st))))
  (match many (nat-eq n 9) _
    ((BTrue) (values (BFalse) (ind-tab st)))
    ((BFalse) (values (BFalse) (ind-plain st)))))

; Five modes over the source: between tokens, inside a word, inside a comment, and inside a string literal
; or its escape. A word runs to a delimiter, which a quote is not, so only a quote met between tokens opens
; a literal, as in the tokenizer above. The scan stops where the tokenizer's lexing would, at an unterminated
; literal or an escape it does not know, so that what is reported is what was read, as in lib/indent.ml.
(def-fns _
  ((many ind-scan : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (let-match many s (SCons c rest) ((SNil) st))
    (match many (is-delim c) _
      ((BTrue)
        (let ((many comment) (many st2)) (ind-delim c st))
        (match many comment _
          ((BTrue) (tail $ ind-comment rest st2))
          ((BFalse) (tail $ ind-scan rest st2))))
      ((BFalse)
        (let-match many (char-is c 34) (BTrue) ((BFalse) (tail $ ind-word rest (ind-plain $ ind-mark st))))
        (match many st (((IndentSt) _))
          ((MkIndentSt l cl _ _ sd t _ _ _) (tail $ ind-str rest (ind-plain st) l cl sd t))))))
  ((many ind-word : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (let-match many s (SCons c rest) ((SNil) st))
    (let-match many (is-delim c) (BTrue) ((BFalse) (tail $ ind-word rest (ind-plain st))))
    (let ((many comment) (many st2)) (ind-delim c st))
    (match many comment _
      ((BTrue) (tail $ ind-comment rest st2))
      ((BFalse) (tail $ ind-scan rest st2))))
  ((many ind-comment : (subterm many (String) s) (many (IndentSt) st) -> (many (IndentSt) r))
    (let-match many s (SCons c rest) ((SNil) st))
    (match many (char-is c 10) _
      ((BTrue) (tail $ ind-scan rest (ind-nl st)))
      ((BFalse) (tail $ ind-comment rest (ind-plain st)))))
  ((many ind-str : (subterm many (String) s) (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc)
       (many (Bool) os) (many (Bool) ot) -> (many (IndentSt) r))
    (let-match many s (SCons c rest) ((SNil) st))
    (let-match many (char-is c 34) (BFalse) ((BTrue) (tail $ ind-scan rest (ind-close-str (ind-plain st) ol oc os ot))))
    (let-match many (char-is c 92) (BFalse) ((BTrue) (tail $ ind-str-esc rest (ind-plain st) ol oc os ot)))
    (let-match many (char-is c 10) (BFalse) ((BTrue) (tail $ ind-str rest (ind-nl st) ol oc os ot)))
    (match many (char-is c 9) (((IndentSt) _))
      ((BTrue) (tail $ ind-str rest (ind-tab st) ol oc os ot))
      ((BFalse) (tail $ ind-str rest (ind-plain st) ol oc os ot))))
  ((many ind-str-esc : (subterm many (String) s) (many (IndentSt) st) (many (Nat) ol) (many (Nat) oc)
       (many (Bool) os) (many (Bool) ot) -> (many (IndentSt) r))
    (let-match many s (SCons c rest) ((SNil) st))
    (let-match many (char-is c 120) (BTrue)
      ((BFalse)
        (match many (escape-ok c) _
          ((BFalse) st)
          ((BTrue) (tail $ ind-str rest (ind-plain st) ol oc os ot)))))
    (let-match many rest (SCons h1 r3) ((SNil) st))
    (let-match many r3 (SCons h2 r4) ((SNil) st))
    (let-match many (hex-pair h1 h2) (Some _ _) ((None _) st))
    (tail $ ind-str r4 (ind-plain $ ind-plain $ ind-plain st) ol oc os ot)))

(def-fns _ $ (many ind-cat : (subterm many (List $ String) parts) -> (many (String) r))
  (match many parts _
    ((Nil _) (SNil))
    ((Cons _ p rest) (str-cat p $ notail $ ind-cat rest))))

(def-fns _ $ (many ind-msg : (many (String) path) (many (Spot) pos) (many (String) kind)
    (many (String) msg) -> (many (String) r))
  (let ((many line) (many col)) $ spot-coords pos)
  (ind-cat
    $ Cons _ path
    $ Cons _ ":"
    $ Cons _ (nat-str line)
    $ Cons _ ":"
    $ Cons _ (nat-str col)
    $ Cons _ kind
    $ Cons _ msg
    $ Nil _))

(def-fns _ $ (many ind-at : (many (String) path) (many (Spot) pos) (many (String) msg) -> (many (String) r))
  (ind-msg path pos ": warning: " msg))

; A note is the second location the warning before it talks about: each of these rules compares two lines,
; and the line compared against is worth naming rather than describing.
(def-fns _ $ (many ind-note : (many (String) path) (many (Spot) pos) (many (String) msg) -> (many (String) r))
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
(def-fns _ $ (many ind-unclosed : (many (String) path) (subterm many (List $ Spot) opens) (many (Bool) first)
    (many (List $ String) acc) -> (many (List $ String) r))
  (let-match many opens (Cons _ o more) ((Nil _) acc))
  (let ((many (String) line))
    (match many first (((String) _))
      ((BTrue) (ind-at path o "this form is never closed"))
      ((BFalse) (ind-note path o "and this one"))))
  (tail $ ind-unclosed path more (BFalse) $ Cons _ line acc))

(def-fns _ $ (many ind-tabs : (many (String) path) (subterm many (List $ Spot) ts)
    (many (List $ String) acc) -> (many (List $ String) r))
  (let-match many ts (Cons _ l more) ((Nil _) acc))
  (tail $ ind-tabs path more
    $ Cons _ (ind-at path l "indentation uses a tab, not spaces only") acc))

(def-fns _ $ (many ind-pop : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (subterm many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) rest) (many (List $ String) acc2))
  (let-match many stack (Cons _ e more) ((Nil _) (values stack acc)))
  (let-match many e (MkIndLevel ep ei en))
  (let-match many (nat-lt i ei) (BTrue) ((BFalse) (values stack acc)))
  (let ((many (List $ String) acc1))
    (match many (nat-lt n en) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (str-cat3 (ind-at path ln $ ind-msg-pop ei en n) "\n" (ind-note path ep "the line at that indentation")) acc))))
  (tail $ ind-pop path ln i n more acc1))

(def-fns _ $ (many ind-enclosing : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (subterm many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ String) acc2))
  (let-match many stack (Cons _ e more) ((Nil _) acc))
  (let-match many e (MkIndLevel ep ei en))
  (let ((many (List $ String) acc1))
    (match many (and (nat-lt ei i) (not $ nat-lt en n)) (((List $ String) _))
      ((BFalse) acc)
      ((BTrue)
        (Cons _ (str-cat3 (ind-at path ln $ ind-msg-enclosing i ei en n) "\n" (ind-note path ep "that enclosing line")) acc))))
  (tail $ ind-enclosing path ln i n more acc1))

(def-fns _ $ (many ind-same : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (Spot) tp) (many (Nat) tn) (many (List $ IndLevel) more) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many (List $ String) acc1))
    (match many (nat-eq n tn) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (str-cat3 (ind-at path ln $ ind-msg-same i n tn) "\n" (ind-note path tp "the previous line at this indentation")) acc))))
  (values (Cons _ (MkIndLevel ln i n) more) acc1))

(def-fns _ $ (many ind-deeper : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (Spot) tp) (many (Nat) ti) (many (Nat) tn) (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many (List $ String) acc1))
    (match many (nat-lt tn n) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (str-cat3 (ind-at path ln $ ind-msg-deeper ti i tn n) "\n" (ind-note path tp "the line before it")) acc))))
  (values (Cons _ (MkIndLevel ln i n) stack) acc1))

(def-fns _ $ (many ind-back : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (IndLevel) e) (many (List $ IndLevel) rest)
    (many (List $ IndLevel) rem) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let-match many e (MkIndLevel ep ei en))
  (let-match many (nat-eq ei i) (BTrue) ((BFalse) (values (Cons _ (MkIndLevel ln i n) rem) acc)))
  (let ((many (List $ String) acc1))
    (match many (nat-eq en n) (((List $ String) _))
      ((BTrue) acc)
      ((BFalse)
        (Cons _ (str-cat3 (ind-at path ln $ ind-msg-back i en n) "\n" (ind-note path ep "the earlier line it matches")) acc))))
  (values (Cons _ (MkIndLevel ln i n) rest) acc1))

(def-fns _ $ (many ind-dedent : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let ((many rem) (many acc1)) (ind-pop path ln i n stack acc))
  (let ((many acc2)) (ind-enclosing path ln i n rem acc1))
  (match many rem (((List $ IndLevel) _) ((List $ String) r))
    ((Nil _) (values (Cons _ (MkIndLevel ln i n) rem) acc2))
    ((Cons _ e2 rest2) (ind-back path ln i n e2 rest2 rem acc2))))

(def-fns _ $ (many ind-head : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (IndLevel) e) (many (List $ IndLevel) more)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (let-match many e (MkIndLevel tp ti tn))
  (let-match many (nat-eq i ti) (BFalse) ((BTrue) (ind-same path ln i n tp tn more acc)))
  (match many (nat-lt ti i) (((List $ IndLevel) _) ((List $ String) r))
    ((BTrue) (ind-deeper path ln i n tp ti tn stack acc))
    ((BFalse) (ind-dedent path ln i n stack acc))))

(def-fns _ $ (many ind-step : (many (String) path) (many (Spot) ln) (many (Nat) i) (many (Nat) n)
    (many (List $ IndLevel) stack) (many (List $ String) acc) ->
    (many (List $ IndLevel) s2) (many (List $ String) acc2))
  (match many stack _
    ((Nil _) (values (Cons _ (MkIndLevel ln i n) $ Nil _) acc))
    ((Cons _ e more) (ind-head path ln i n e more stack acc))))

(def-fns _ $ (many ind-check : (many (String) path) (subterm many (List $ IndentLine) lines)
    (many (List $ IndLevel) stack) (many (List $ String) acc) -> (many (List $ String) r))
  (let-match many lines (Cons _ il more) ((Nil _) acc))
  (let-match many il (MkIndentLine ln i n))
  (let ((many stack2) (many acc2)) (ind-step path ln i n stack acc))
  (tail $ ind-check path more stack2 acc2))

; The warnings one file's text earns, in line order: the tabs, then the nesting claims, then a surplus ) and
; the count of forms left open, which are what the reader's own error does not name.
(def-fns _ $ (many indent-warnings : (many (Bool) notes) (many (String) path) (many (String) src) -> (many (List $ String) ws))
  (let ((many st))
    (ind-scan src (MkIndentSt 1 0 0 (Nil _) (BFalse) (BFalse) (None _) (Nil _) (Nil _))))
  (let-match many st (MkIndentSt _ _ _ op _ _ u ls ts))
  (let ((many acc0)) (ind-tabs path (list-rev _ ts) (Nil _)))
  (let ((many acc1)) (ind-check path (list-rev _ ls) (Nil _) acc0))
  (let ((many (List $ String) acc2))
    (match many u (((List $ String) _))
      ((None _) acc1)
      ((Some _ sl)
        (Cons _ (ind-at path sl "a `)` here closes more than is open (surplus `)`)") acc1))))
  (let ((many unclosed)) $ ind-unclosed path op (BTrue) (Nil _))
  (let ((many acc3)) $ match many unclosed (((List $ String) _)) ((Nil _) acc2) ((Cons _ _ _) (Cons _ (join-strs (list-rev _ unclosed) "\n") acc2)))
  (match many acc3 _ ((Nil _) acc3) ((Cons _ w rest) (list-rev _ $ Cons _ (match many notes (((String) _)) ((BTrue) (str-cat3 w "\n" $ shape-note path)) ((BFalse) w)) rest))))
