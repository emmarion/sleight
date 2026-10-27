; self/reader.sl -- s-expressions with $ (DESIGN.md sections 1-2), read by a structural tokenizer over the
; source string and a fold over the tokens with a stack of open forms, so nothing recurses on a computed
; suffix of the input.

; Where a token's first character sits, which every message a session writes points at (ASSUMPTIONS 194);
; both counted from one.
(def-adts $ (Spot : -> Type)
  enum
  (many MkSpot : (many (Nat) line) (many (Nat) col) -> (Spot))
  (many PosSpot : (many (Pos) p) -> (Spot))
  (many ExpSpot : (many (Nat) expansion) (many (Spot) p) -> (Spot))
  (many SplicedSpot : (many (List $ Pair (Nat) (Nat)) splices) (many (Spot) p) -> (Spot)))

(def-fns _ $ (many spot-bare : (subterm many (Spot) p) -> (many (Spot) q))
  (match many p _ ((ExpSpot _ q) (tail $ spot-bare q)) ((SplicedSpot _ q) (tail $ spot-bare q)) (else p)))

(def-fns _ $ (many spot-framed : (subterm many (Spot) p) -> (many (Bool) r))
  (match many p _ ((ExpSpot _ _) (BTrue)) ((SplicedSpot _ q) (tail $ spot-framed q)) (else (BFalse))))

(def-fns _ $ (many spot-frame : (subterm many (Spot) p) -> (many (Nat) x))
  (match many p _ ((ExpSpot x _) x) ((SplicedSpot _ q) (tail $ spot-frame q)) (else 0)))

(def-fns _ $ (many spot-splices : (subterm many (Spot) p) -> (many (List $ Pair (Nat) (Nat)) s))
  (let-match many p (SplicedSpot s q) ((ExpSpot _ q) (tail $ spot-splices q)) (else (Nil _)))
  (let ((many r) (erased _)) (list-append _ (notail $ spot-splices q) s))
  r)

(def-fns _ $ (many spot-unframed : (subterm many (Spot) p) -> (many (Spot) q))
  (match many p _ ((ExpSpot _ q) (tail $ spot-unframed q)) ((SplicedSpot s q) (SplicedSpot s $ notail $ spot-unframed q)) (else p)))

(def-fns _ $ (many spot-reframed : (many (Nat) x) (many (Spot) p) -> (many (Spot) q))
  (match many x _ ((Zero) (spot-unframed p)) (else (ExpSpot x $ spot-unframed p))))

(def-fns _ $ (many spot-in : (many (Spot) outer) (many (Spot) p) -> (many (Spot) r))
  (let-match many (spot-framed p) (BFalse) ((BTrue) p))
  (spot-reframed (spot-frame outer) p))

(def-fns _ $ (many spot-pos : (many (String) file) (many (Spot) p) -> (many (Pos) q))
  (match many (spot-bare p) _ ((MkSpot l c) (MkPos file l c)) ((PosSpot q) q) (else (NoPos))))

(def-adts
  ((Syn : -> Type)
    enum
    (many RAtom : (many (Spot) pos) (many (Name) s) -> (Syn))
    (many RWild : (many (Spot) pos) -> (Syn))
    (many RNat : (many (Spot) pos) (many (Nat) n) -> (Syn))
    (many RChr : (many (Spot) pos) (many (Char) c) -> (Syn))
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
  (many TPragma : (many (Spot) pos) (many (List $ Syn) words) -> (Tok))
  (many TTab : (many (Spot) pos) -> (Tok))
  (many THalt : (many (Spot) pos) (many (String) msg) -> (Tok))
  (many TFile : (many (String) name) -> (Tok)))

; A syntax error and where it is reported.
(def-adts $ (SynErr : -> Type)
  enum
  (many MkSynErr : (many (Spot) pos) (many (String) msg) (many (Bool) paren) (many (Maybe $ Pair (Spot) (String)) note) -> (SynErr)))

(def-adts $ (Region : -> Type)
  enum
  (many MkRegion : (many (Nat) index) (many (String) name) (many (Spot) from) (many (Maybe $ Spot) until) -> (Region)))

(def-fns _ $ (many spot-coords : (many (Spot) p) -> (many (Nat) line) (many (Nat) col))
  (match many (spot-pos "" p) (((Nat) l) ((Nat) c)) ((NoPos) (values 0 0)) ((MkPos _ l c) (values l c))))

(def-fns _ $ (many pos-lt : (many (Spot) a) (many (Spot) b) -> (many (Bool) r))
  (let ((many al) (many ac)) $ spot-coords a)
  (let ((many bl) (many bc)) $ spot-coords b)
  (or (nat-lt al bl) $ and (nat-eqb al bl) $ nat-lt ac bc))

(def-fns _ $ (many region-covers : (many (Region) r) (many (Spot) p) -> (many (Bool) b))
  (match many r _ ((MkRegion _ _ from until)
    (and (not $ pos-lt p from) $ match many until (((Bool) _)) ((None _) (BTrue)) ((Some _ u) (pos-lt p u))))))

(def-fns _ $ (many region-named : (subterm many (List $ Region) rs) (many (String) name) -> (many (Maybe $ Region) r))
  (let-match many rs (Cons _ r rest)
    ((Nil _) (None _)))
  (let-match many r (MkRegion _ n _ _))
  (match many (str-eqb n name) _ ((BTrue) (Some _ r)) ((BFalse) (tail $ region-named rest name))))

(def-fns _ $ (many region-drop : (subterm many (List $ Region) rs) (many (String) name) -> (many (List $ Region) r))
  (let-match many rs (Cons _ r rest)
    ((Nil _) rs))
  (let-match many r (MkRegion _ n _ _))
  (match many (str-eqb n name) _ ((BTrue) rest) ((BFalse) (Cons _ r $ notail $ region-drop rest name))))

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
  (let-match many (char-lt-dec c #\!) (No _ _ _ _ _) ((Yes _ _ _ _ _) (BTrue)))
  (let-match many (char-lt-dec #\x3b c) (No _ _ _ _ _) ((Yes _ _ _ _ _) (BFalse)))
  (or (char-eqb c #\x28) $ or (char-eqb c #\x29) $ char-eqb c #\x3b))

(def-fns _ $ (many word-item : (many (Spot) pos) (many (String) w) -> (many (Tok) t))
  (let-match many (str-eqb w "_") (BFalse) ((BTrue) (TItem $ RWild pos)))
  (let-match many (is-reserved-name w) (BFalse)
    ((BTrue) (TError pos $ str-cat3 (str-cat3 "`" w "` begins with `__`, which is reserved for the compilers' messages; write it `") (spell-text w) "`")))
  (let-match many (literal-error w) (None _) ((Some _ msg) (TError pos msg)))
  (match many (classify w) _
    ((LName) (TItem $ RAtom pos $ NSrc w))
    ((LNumeral) (TItem $ RNat pos $ parse-nat w))
    ((LChar) (TItem $ RChr pos $ match many (char-lit-code w) (((Char) _)) ((Some _ c) c) ((None _) #\x00)))))

(def-fns _ $ (many word-tok : (many (Spot) pos) (many (String) start) (many (Nat) k) (erased (Nat) len) (erased (StrLength start len) l) (erased (Nat) rl) (erased (Add k rl len) sum) -> (many (Tok) t))
  (let ((many w) (many _) (erased _) (erased _)) (str-split start k len l (add-le-left k rl len sum)))
  (match many (str-cmp w "$") _
    ((CEq _ _ _) (TDollar pos))
    (else (word-item pos w))))

(def-fns _ $ (many lit-count : (many (Unescaped) u) (many (String) rest) -> (many (Nat) n))
  (match many u _
    ((ReadOk _ used _) (nat-pred $ nat-pred used))
    ((ReadBadEscape off _) (nat-pred off))
    (else (let ((many n) (erased _)) (str-length rest)) n)))

(def-adts $ (StrKind : -> Type)
  enum
  (many SKLit : -> (StrKind))
  (many SKName : -> (StrKind))
  (many SKPragma : (many (Spot) pos) (many (List $ Syn) words) (many (Bool) name) -> (StrKind)))

(def-fns _ $ (many bad-escape : (many (Spot) pos) (many (Char) e) -> (many (Tok) t))
  (THalt pos $ rope-str $ RCat (RStr "unknown escape \\") $ RChar e))

(def-fns _ $ (many end-toks : (many (Tok) t) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (list-rev _ $ Cons _ t acc))

(def-fns _ $ (many unterminated : (many (Spot) pos) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
  (end-toks (THalt pos "unterminated string literal") acc))

(def-fns _ $ (many push-tab : (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) r))
  (let ((many pushed)) (Cons _ (TTab $ MkSpot line $ Succ col) acc))
  (let-match many acc (Cons _ t _) ((Nil _) pushed))
  (let-match many t (TTab p) (else pushed))
  (let ((many l) (many _)) $ spot-coords p)
  (match many (nat-eqb l line) _ ((BTrue) acc) ((BFalse) pushed)))

; [col] counts the characters read on the current line, so the character being read sits at column
; (Succ col); a newline starts the next line over at zero.
(def-fns _ $ (many delim-step : (many (Char) c) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) ->
    (many (Bool) comment) (many (Nat) line2) (many (Nat) col2) (many (List $ Tok) acc2))
  (let-match many (char-eq c #\x3b) (Unequal _ _ _ _ _) ((Equal _ _ _) (values (BTrue) line (Succ col) acc)))
  (let-match many (char-eq c #\x28) (Unequal _ _ _ _ _) ((Equal _ _ _) (values (BFalse) line (Succ col) $ Cons _ (TOpen $ MkSpot line $ Succ col) acc)))
  (let-match many (char-eq c #\x29) (Unequal _ _ _ _ _)
    ((Equal _ _ _) (values (BFalse) line (Succ col) $ Cons _ (TClose $ MkSpot line $ Succ col) acc)))
  (let-match many (char-eq c #\tab) (Unequal _ _ _ _ _) ((Equal _ _ _) (values (BFalse) line (Succ col) $ push-tab line col acc)))
  (match many (char-eq c #\newline) _
    ((Equal _ _ _) (values (BFalse) (Succ line) 0 acc))
    ((Unequal _ _ _ _ _) (values (BFalse) line (Succ col) acc))))

(def-fns _ $ (many pragma-first : (many (List $ Syn) words) -> (many (String) s))
  (let-match many (list-rev _ words) (Cons _ w _)
    ((Nil _) ""))
  (let-match many w (RAtom _ n) (else ""))
  (let-match many n (NSrc s) (else ""))
  s)

(def-fns _ $ (many pragma-limit : (many (List $ Syn) words) -> (many (Nat) n))
  (match many (str-eqb (pragma-first words) "warn") _ ((BTrue) 2) ((BFalse) 3)))

(def-fns _ $ (many pragma-field : (many (Maybe $ Spot) start) (many (Rope) cur) (many (List $ Syn) words) -> (many (List $ Syn) r))
  (let ((many text)) $ rope-str cur)
  (match many start _
    ((None _) words)
    ((Some _ p) (Cons _ (RAtom p $ NSrc text) words))))

(def-fns _ $ (many pragma-tok : (many (Spot) pos) (many (Maybe $ Spot) start) (many (Rope) cur) (many (List $ Syn) words) -> (many (Tok) t))
  (TPragma pos $ list-rev _ $ pragma-field start cur words))

(def-fns _ $ (many is-atom-text : (many (Syn) r) (many (String) x) -> (many (Bool) b))
  (let-match many r (RAtom _ y) (else (BFalse)))
  (let-match many y (NSrc t) (else (BFalse)))
  (str-eqb x t))

(def-fns _ $ (many pragma-done : (many (Tok) t) -> (many (Tok) r))
  (let-match many t (TPragma l ws) (else t))
  (let-match many ws (Cons _ w rest) ((Nil _) t))
  (let-match many (is-atom-text w "file") (BTrue) ((BFalse) t))
  (let ((many bad)) $ THalt l "`;! file` takes one non-empty string literal, the file's name")
  (let-match many rest (Cons _ n more) ((Nil _) bad))
  (let-match many n (RString _ f) (else bad))
  (let-match many more (Nil _) ((Cons _ _ _) bad))
  (match many (str-is-empty f) _ ((BTrue) bad) ((BFalse) (TFile f))))

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
        (let-match many (char-eqb c #\") (BFalse)
          ((BTrue)
            (let ((many u)) (read-string s))
            (tail $ string-lit rest line (Succ col) (MkSpot line $ Succ col) (SKLit) u (lit-count u rest) acc)))
        (let-match many (and (char-eqb c #\#) $ str-starts "\"" rest) (BFalse)
          ((BTrue)
            (let-match many rest (SCons _ rest2) ((SNil) (list-rev _ acc)))
            (let ((many u)) (read-string rest))
            (tail $ string-lit rest2 line (Succ (Succ col)) (MkSpot line $ Succ col) (SKName) u (lit-count u rest2) acc)))
        (let ((erased len) (erased l)) (str-length s))
        (let-match erased l (SLenCons _ _ rl lr))
        (tail $ word rest line (Succ col) s len l (Succ (Zero)) rl lr (AddSucc (Zero) rl rl (AddZero rl)) (MkSpot line $ Succ col) acc))))
  ((many comment-start : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (list-rev _ acc)))
    (let-match many (char-eqb c #\!) (BFalse)
      ((BTrue) (tail $ pragma-line rest line (Succ col) (MkSpot line col) (Nil _) (None _) (REmpty) (REmpty) acc)))
    (match many (char-eqb c #\newline) _
      ((BTrue) (tail $ tokenize rest (Succ line) 0 acc))
      ((BFalse) (tail $ skip-comment rest line acc))))
  ((many pragma-line : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Spot) pos) (many (List $ Syn) words)
      (many (Maybe $ Spot) start) (many (Rope) cur) (many (Rope) blanks) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (end-toks (pragma-done $ pragma-tok pos start cur words) acc)))
    (let-match many (char-eqb c #\newline) (BFalse)
      ((BTrue)
        (let ((many t)) $ pragma-done $ pragma-tok pos start cur words)
        (match many t _
          ((TFile _) (tail $ tokenize rest 1 0 $ Cons _ t acc))
          ((THalt _ _) (end-toks t acc))
          (else (tail $ tokenize rest (Succ line) 0 $ Cons _ t acc)))))
    (match many (or (char-eqb c #\space) $ or (char-eqb c #\tab) $ char-eqb c #\x0d) _
      ((BTrue)
        (let-match many start (Some _ _) ((None _) (tail $ pragma-line rest line (Succ col) pos words start cur blanks acc)))
        (match many (nat-lt (list-length _ words) $ pragma-limit words) _
          ((BTrue) (tail $ pragma-line rest line (Succ col) pos (pragma-field start cur words) (None _) (REmpty) (REmpty) acc))
          ((BFalse) (tail $ pragma-line rest line (Succ col) pos words start cur (RCat blanks $ RChar c) acc))))
      ((BFalse)
        (let-match many start (None _)
          ((Some _ _) (tail $ pragma-line rest line (Succ col) pos words start (RCat (RCat cur blanks) $ RChar c) (REmpty) acc)))
        (let ((many open)) $ nat-lt (list-length _ words) $ pragma-limit words)
        (let-match many (and open $ and (char-eqb c #\") $ str-eqb (pragma-first words) "file") (BFalse)
          ((BTrue)
            (let ((many u)) (read-string s))
            (tail $ string-lit rest line (Succ col) (MkSpot line $ Succ col) (SKPragma pos words $ BFalse) u (lit-count u rest) acc)))
        (let-match many (and open $ and (char-eqb c #\#) $ str-starts "\"" rest) (BFalse)
          ((BTrue)
            (let-match many rest (SCons _ rest2) ((SNil) (list-rev _ acc)))
            (let ((many u)) (read-string rest))
            (tail $ string-lit rest2 line (Succ (Succ col)) (MkSpot line $ Succ col) (SKPragma pos words $ BTrue) u (lit-count u rest2) acc)))
        (tail $ pragma-line rest line (Succ col) pos words (Some _ $ MkSpot line $ Succ col) (RChar c) (REmpty) acc))))
  ((many skip-comment : (subterm many (String) s) (many (Nat) line) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many s (SCons c rest) ((SNil) (list-rev _ acc)))
    (match many (char-eqb c #\newline) _
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
  ((many string-lit : (subterm many (String) s) (many (Nat) line) (many (Nat) col) (many (Spot) pos) (many (StrKind) kind)
      (many (Unescaped) u) (many (Nat) count) (many (List $ Tok) acc) -> (many (List $ Tok) toks))
    (let-match many count (Succ k)
      ((Zero)
        (let-match many u (ReadOk body _ _)
          ((ReadBadEscape _ e) (end-toks (bad-escape (MkSpot line $ Succ col) e) acc))
          (else (unterminated pos acc)))
        (let-match many s (SCons _ rest) ((SNil) (unterminated pos acc)))
        (let-match many kind (SKPragma pp ws nm)
          ((SKLit) (tail $ tokenize rest line (Succ col) $ Cons _ (TItem $ RString pos body) acc))
          ((SKName) (tail $ tokenize rest line (Succ col) $ Cons _ (TItem $ RAtom pos $ NSrc body) acc)))
        (let ((many w)) $ match many nm (((Syn) _)) ((BTrue) (RAtom pos $ NSrc body)) ((BFalse) (RString pos body)))
        (tail $ pragma-line rest line (Succ col) pp (Cons _ w ws) (None _) (REmpty) (REmpty) acc)))
    (let-match many s (SCons c rest) ((SNil) (unterminated pos acc)))
    (let-match many (char-eq c #\newline) (Equal _ _ _)
      ((Unequal _ _ _ _ _)
        (let ((many acc2)) $ match many (char-eq c #\tab) (((List $ Tok) _)) ((Equal _ _ _) (push-tab line col acc)) ((Unequal _ _ _ _ _) acc))
        (tail $ string-lit rest line (Succ col) pos kind u k acc2)))
    (let-match many kind (SKPragma _ _ _) (else (tail $ string-lit rest (Succ line) 0 pos kind u k acc)))
    (end-toks (THalt pos "a pragma ends with its line") acc)))

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
      (match many (str-eqb kw "warn") _
        ((BTrue)
          (match many (nat-lt (list-length _ stack) 2) _
            ((BTrue) (tail $ parse-toks rest (push-item (RList l $ Cons _ (RAtom l $ NSrc ";!") ws) stack) opened closed))
            ((BFalse) (values stack (syn-err l "`;! warn` must be written between top-level forms") closed))))
        ((BFalse)
          (let-match many (or (str-eqb kw "suppress") $ str-eqb kw "restore") (BTrue)
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
          (match many (str-eqb kw "suppress") _
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
        ((Cons _ _ _) (tail $ parse-toks rest (close-top s1) opened closed))))
    (else (tail $ parse-toks rest stack opened closed))))

; Reads the root frame's items once nothing is open; an open form at the end is a missing ), reported
; for the innermost, which is the $ form's when that is what is open, at the line the form opened on.
(def-fns _ $ (many finish-stack : (many (List $ Frame) stack) -> (many (List $ Syn) items) (many (Maybe $ SynErr) err))
  (let-match many stack (Cons _ f rest) ((Nil _) (values (Nil _) $ None _)))
  (let-match many rest (Cons _ _ _) ((Nil _) (match many f _ ((MkFrame _ _ items) (values (list-rev _ items) $ None _)))))
  (match many f _
    ((MkFrame l d _) (values (Nil _) $ Some _ $ MkSynErr l (match many d (((String) _)) ((BTrue) "missing `)` after `$`") ((BFalse) "missing `)`")) (BTrue) $ None _))))

(def-adts $ (SrcFile : -> Type)
  enum
  (many MkSrcFile : (many (String) path) (many (String) name) (many (List $ Tok) toks) (many (Maybe $ SynErr) stop) -> (SrcFile)))

(def-fns _ $ (many cut-files : (many (String) path) (many (String) name) (subterm many (List $ Tok) toks) (many (List $ Tok) acc) (many (List $ SrcFile) cut) -> (many (List $ SrcFile) r))
  (let-match many toks (Cons _ t rest) ((Nil _) (list-rev _ $ Cons _ (MkSrcFile path name (list-rev _ acc) $ None _) cut)))
  (match many t _
    ((TFile f) (tail $ cut-files path f rest (Nil _) $ Cons _ (MkSrcFile path name (list-rev _ acc) $ None _) cut))
    ((THalt l m) (list-rev _ $ Cons _ (MkSrcFile path name (list-rev _ acc) $ syn-err l m) cut))
    (else (tail $ cut-files path name rest (Cons _ t acc) cut))))

(def-fns _ $ (many src-files : (many (String) path) (many (String) src) -> (many (List $ SrcFile) r))
  (cut-files path path (tokenize src 1 0 $ Nil _) (Nil _) (Nil _)))

(def-fns _ $ (many parse : (many (SrcFile) f) -> (many (List $ Syn) items) (many (Maybe $ SynErr) err) (many (List $ Region) regions))
  (let-match many f (MkSrcFile _ _ toks stop))
  (let-match many stop (None _) ((Some _ _) (values (Nil _) stop $ Nil _)))
  (let ((many stack) (many err) (many regions)) (parse-toks toks (Cons _ (MkFrame (MkSpot 1 1) (BFalse) $ Nil _) $ Nil _) (Nil _) (Nil _)))
  (let-match many err (None _) ((Some _ _) (values (Nil _) err $ Nil _)))
  (let ((many items) (many err2)) $ finish-stack stack)
  (values items err2 regions))

(def-fns _
  ((many show-raw : (subterm many (Syn) r) -> (many (Rope) out))
    (match many r _
      ((RAtom _ s) (RStr $ spell-name s))
      ((RWild _) (RStr "_"))
      ((RNat _ n) (RStr $ shown-text $ ShNat n))
      ((RChr _ c) (RStr $ shown-text $ ShChr c))
      ((RString _ s) (RStr $ shown-text $ ShStr s))
      ((RList _ items) (rwrap "(" (rjoin (notail $ show-raws items) " ") ")"))))
  ((many show-raws : (subterm many (List $ Syn) rs) -> (many (List $ Rope) out))
    (match many rs _
      ((Nil _) (Nil _))
      ((Cons _ r rest) (Cons _ (notail $ show-raw r) $ notail $ show-raws rest)))))

(def-fns _ $ (many syn-shown : (many (Syn) r) -> (many (Shown) s))
  (match many r _ ((RNat _ n) (ShNat n)) ((RChr _ c) (ShChr c)) ((RString _ s) (ShStr s)) (else (ShText $ rope-str $ show-raw r))))

; The indentation check of lib/indent.ml, read from one file's tokens: indentation is a claim about paren
; nesting, and a line's claim is checked against the depth in force where its first token starts. It runs
; before the parse, so a file the reader goes on to refuse is reported on too. $ is not nesting and is not
; tracked; lib/indent.ml's header says why.

; One indentation level still open: the line that opened it, which a later line's note names, and the
; indentation and nesting it opened at.
(def-adts $ (IndLevel : -> Type)
  enum
  (many MkIndLevel : (many (Spot) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndLevel)))

(def-adts $ (IndentLine : -> Type)
  enum
  (many MkIndentLine : (many (Spot) pos) (many (Nat) indent) (many (Nat) nesting) -> (IndentLine)))

; The fold's state: the line the last token started on, where each form still open was opened, innermost
; first, the first ) that closed more than was open, and the lines checked and the tabs read, both reversed.
(def-adts $ (IndentSt : -> Type)
  enum
  (many MkIndentSt : (many (Nat) line) (many (List $ Spot) opens) (many (Maybe $ Spot) surplus)
      (many (List $ IndentLine) lines) (many (List $ Spot) tabs) -> (IndentSt)))

(def-fns _ $ (many ind-mark : (many (Spot) p) (many (IndentSt) st) -> (many (IndentSt) r))
  (let-match many st (MkIndentSt cur op u ls ts))
  (let ((many l) (many c)) $ spot-coords p)
  (match many (nat-eqb l cur) _
    ((BTrue) st)
    ((BFalse) (MkIndentSt l op u (Cons _ (MkIndentLine p (nat-pred c) $ list-length _ op) ls) ts))))

; A ) with nothing open is recorded where it sits and leaves the depth at zero, so the lines after it are
; still checked against the count of forms actually open.
(def-fns _ $ (many ind-tok : (many (IndentSt) st) (many (Tok) t) -> (many (IndentSt) r))
  (match many t _
    ((TOpen p) (match many (ind-mark p st) _ ((MkIndentSt l op u ls ts) (MkIndentSt l (Cons _ p op) u ls ts))))
    ((TClose p)
      (let-match many (ind-mark p st) (MkIndentSt l op u ls ts))
      (match many op _
        ((Cons _ _ more) (MkIndentSt l more u ls ts))
        ((Nil _) (MkIndentSt l op (match many u (((Maybe $ Spot) _)) ((Some _ _) u) ((None _) (Some _ p))) ls ts))))
    ((TDollar p) (ind-mark p st))
    ((TItem r) (ind-mark (raw-pos r) st))
    ((TError p _) (ind-mark p st))
    ((TTab p) (match many st _ ((MkIndentSt l op u ls ts) (MkIndentSt l op u ls $ Cons _ p ts))))
    (else st)))

(def-fns _ $ (many ind-fold : (subterm many (List $ Tok) toks) (many (IndentSt) st) -> (many (IndentSt) r))
  (let-match many toks (Cons _ t rest) ((Nil _) st))
  (tail $ ind-fold rest $ ind-tok st t))

; A line is read as tabbed when a tab sits on it before its first token, a literal's included.
(def-fns _ $ (many tab-before : (subterm many (List $ Spot) ts) (many (Nat) l) (many (Nat) c) -> (many (List $ Spot) rest) (many (Bool) r))
  (let-match many ts (Cons _ t more) ((Nil _) (values ts (BFalse))))
  (let ((many tl) (many tc)) $ spot-coords t)
  (let-match many (and (nat-eqb tl l) $ nat-lt tc c) (BFalse) ((BTrue) (values more (BTrue))))
  (match many (nat-lt tl l) _ ((BTrue) (values ts (BFalse))) ((BFalse) (tail $ tab-before more l c))))

(def-fns _ $ (many ind-tabbed : (subterm many (List $ IndentLine) ls) (many (List $ Spot) ts) -> (many (List $ Spot) r))
  (let-match many ls (Cons _ il rest) ((Nil _) (Nil _)))
  (let-match many il (MkIndentLine p _ _))
  (let ((many l) (many c)) $ spot-coords p)
  (let ((many ts2) (many hit)) (tab-before ts l c))
  (let ((many more)) $ notail $ ind-tabbed rest ts2)
  (match many hit _ ((BTrue) (Cons _ p more)) ((BFalse) more)))

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
    (match many (nat-eqb n tn) (((List $ String) _))
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
  (let-match many (nat-eqb ei i) (BTrue) ((BFalse) (values (Cons _ (MkIndLevel ln i n) rem) acc)))
  (let ((many (List $ String) acc1))
    (match many (nat-eqb en n) (((List $ String) _))
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
  (let-match many (nat-eqb i ti) (BFalse) ((BTrue) (ind-same path ln i n tp tn more acc)))
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

; The warnings one file earns, in line order: the tabs, then the nesting claims, then a surplus ) and the
; count of forms left open, which are what the reader's own error does not name.
(def-fns _ $ (many indent-warnings : (many (Bool) notes) (many (SrcFile) f) -> (many (List $ String) ws))
  (let-match many f (MkSrcFile path name toks _))
  (let-match many (ind-fold toks $ MkIndentSt 0 (Nil _) (None _) (Nil _) (Nil _)) (MkIndentSt _ op u ls ts))
  (let ((many acc0)) (ind-tabs name (list-rev _ $ ind-tabbed ls ts) (Nil _)))
  (let ((many acc1)) (ind-check name (list-rev _ ls) (Nil _) acc0))
  (let ((many (List $ String) acc2))
    (match many u (((List $ String) _))
      ((None _) acc1)
      ((Some _ sl)
        (Cons _ (ind-at name sl "a `)` here closes more than is open (surplus `)`)") acc1))))
  (let ((many unclosed)) $ ind-unclosed name op (BTrue) (Nil _))
  (let ((many acc3)) $ match many unclosed (((List $ String) _)) ((Nil _) acc2) ((Cons _ _ _) (Cons _ (join-strs (list-rev _ unclosed) "\n") acc2)))
  (match many acc3 _ ((Nil _) acc3) ((Cons _ w rest) (list-rev _ $ Cons _ (match many notes (((String) _)) ((BTrue) (str-cat3 w "\n" $ shape-note path)) ((BFalse) w)) rest))))
