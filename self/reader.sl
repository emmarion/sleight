; self/reader.sl -- s-expressions with $ (DESIGN.md sections 1-2), read by a structural tokenizer over the
; source string and a fold over the tokens with a stack of open forms, so nothing recurses on a computed
; suffix of the input.

(def-adts
  (Raw : -> Type
    enum
    (many RAtom : (many (String) s) -> (Raw))
    (many RString : (many (String) s) -> (Raw))
    (many RList : (many (List (Raw)) items) -> (Raw))))

(def-adts $ Tok : -> Type
  enum
  (many TOpen : -> (Tok))
  (many TClose : -> (Tok))
  (many TDollar : -> (Tok))
  (many TWord : (many (String) s) -> (Tok))
  (many TStrLit : (many (String) s) -> (Tok))
  (many TError : (many (String) msg) -> (Tok)))

(def-fns _ $ many is-delim : (many (Char) c) -> (many (Bool) r)
  (let (many n) (char-code (predates _) c))
  (or (predates _) (nat-lt (predates _) n 33)
    (or (predates _) (nat-eq (predates _) n 40)
      (or (predates _) (nat-eq (predates _) n 41) (nat-eq (predates _) n 59)))))

(def-fns _ $ many word-tok : (many (String) rev) -> (many (Tok) t)
  (let (many w) (str-rev-onto (predates _) rev (SNil)))
  (match many (str-eq (predates _) w "$") _
    ((BTrue) (TDollar))
    ((BFalse) (TWord w))))

(def-fns _ $ many escape-ok : (many (Char) e) -> (many (Bool) r)
  (let (many n) (char-code (predates _) e))
  (or (predates _) (nat-eq (predates _) n 110) (or (predates _) (nat-eq (predates _) n 116) (or (predates _) (nat-eq (predates _) n 34) (nat-eq (predates _) n 92)))))

(def-fns _ $ many unescape : (many (Char) e) -> (many (Char) c)
  (let (many n) (char-code (predates _) e))
  (match many (nat-eq (predates _) n 110) _
    ((BTrue) #\newline)
    ((BFalse)
      (match many (nat-eq (predates _) n 116) _
        ((BTrue) #\tab)
        ((BFalse) e)))))

; Tokens accumulate reversed in [acc]; an atom's characters accumulate reversed in [word].
(def-fns _
  (many tokenize : (subterm many (String) s) (many (List (Tok)) acc) -> (many (List (Tok)) toks)
    (match many s _
      ((SNil) (list-rev (predates _) (Tok) acc))
      ((SCons c rest)
        (let (many n) (char-code (predates _) c))
        (match many (nat-lt (predates _) n 33) _
          ((BTrue) (tokenize (subterm _) rest acc))
          ((BFalse)
            (match many (nat-eq (predates _) n 59) _
              ((BTrue) (skip-comment (subterm _) rest acc))
              ((BFalse)
                (match many (nat-eq (predates _) n 40) _
                  ((BTrue) (tokenize (subterm _) rest (Cons (Tok) (TOpen) acc)))
                  ((BFalse)
                    (match many (nat-eq (predates _) n 41) _
                      ((BTrue) (tokenize (subterm _) rest (Cons (Tok) (TClose) acc)))
                      ((BFalse)
                        (match many (nat-eq (predates _) n 34) _
                          ((BTrue) (string-lit (subterm _) rest (SNil) acc))
                          ((BFalse) (word (subterm _) rest (SCons c (SNil)) acc))))))))))))))
  (many skip-comment : (subterm many (String) s) (many (List (Tok)) acc) -> (many (List (Tok)) toks)
    (match many s _
      ((SNil) (list-rev (predates _) (Tok) acc))
      ((SCons c rest)
        (match many (char-is (predates _) c 10) _
          ((BTrue) (tokenize (subterm _) rest acc))
          ((BFalse) (skip-comment (subterm _) rest acc))))))
  (many word : (subterm many (String) s) (many (String) rev) (many (List (Tok)) acc) -> (many (List (Tok)) toks)
    (match many s _
      ((SNil) (list-rev (predates _) (Tok) (Cons (Tok) (word-tok (predates _) rev) acc)))
      ((SCons c rest)
        (match many (is-delim (predates _) c) _
          ((BTrue)
            (let (many acc1) (Cons (Tok) (word-tok (predates _) rev) acc))
            (let (many n) (char-code (predates _) c))
            (match many (nat-eq (predates _) n 59) _
              ((BTrue) (skip-comment (subterm _) rest acc1))
              ((BFalse)
                (match many (nat-eq (predates _) n 40) _
                  ((BTrue) (tokenize (subterm _) rest (Cons (Tok) (TOpen) acc1)))
                  ((BFalse)
                    (match many (nat-eq (predates _) n 41) _
                      ((BTrue) (tokenize (subterm _) rest (Cons (Tok) (TClose) acc1)))
                      ((BFalse) (tokenize (subterm _) rest acc1))))))))
          ((BFalse) (word (subterm _) rest (SCons c rev) acc))))))
  (many string-lit : (subterm many (String) s) (many (String) rev) (many (List (Tok)) acc) -> (many (List (Tok)) toks)
    (match many s _
      ((SNil) (list-rev (predates _) (Tok) (Cons (Tok) (TError "unterminated string literal") acc)))
      ((SCons c rest)
        (let (many n) (char-code (predates _) c))
        (match many (nat-eq (predates _) n 34) _
          ((BTrue) (tokenize (subterm _) rest (Cons (Tok) (TStrLit (str-rev-onto (predates _) rev (SNil))) acc)))
          ((BFalse)
            (match many (nat-eq (predates _) n 92) _
              ((BTrue)
                (match many rest _
                  ((SNil) (list-rev (predates _) (Tok) (Cons (Tok) (TError "unterminated string literal") acc)))
                  ((SCons e rest2)
                    (match many (escape-ok (predates _) e) _
                      ((BTrue) (string-lit (subterm _) rest2 (SCons (unescape (predates _) e) rev) acc))
                      ((BFalse) (list-rev (predates _) (Tok) (Cons (Tok) (TError (str-cat (predates _) "unknown escape \\" (SCons e (SNil)))) acc)))))))
              ((BFalse) (string-lit (subterm _) rest (SCons c rev) acc)))))))))

; A frame is an open form: whether $ opened it, and its items so far, reversed.
(def-adts $ Frame : -> Type
  enum
  (many MkFrame : (many (Bool) dollar) (many (List (Raw)) items) -> (Frame)))

(def-fns _ $ many push-item : (many (Raw) item) (many (List (Frame)) stack) -> (many (List (Frame)) r)
  (match many stack _
    ((Nil a) (Cons (Frame) (MkFrame (BFalse) (Cons (Raw) item (Nil (Raw)))) (Nil (Frame))))
    ((Cons a f rest)
      (match many f _
        ((MkFrame d items) (Cons (Frame) (MkFrame d (Cons (Raw) item items)) rest))))))

; Closes the top frame into its parent as a list.
(def-fns _ $ many close-top : (many (List (Frame)) stack) -> (many (List (Frame)) r)
  (match many stack _
    ((Nil a) stack)
    ((Cons a f rest)
      (match many f _
        ((MkFrame d items) (push-item (predates _) (RList (list-rev (predates _) (Raw) items)) rest))))))

; Closes every $-opened frame on top of the stack; the fuel bounds the stack's depth.
(def-fns _ $ many close-dollars : (subterm many (Nat) fuel) (many (List (Frame)) stack) -> (many (List (Frame)) r)
  (match many fuel _
    ((Zero) stack)
    ((Succ k)
      (match many stack _
        ((Nil a) stack)
        ((Cons a f rest)
          (match many f _
            ((MkFrame d items)
              (match many d _
                ((BFalse) stack)
                ((BTrue) (close-dollars (subterm _) k (close-top (predates _) stack)))))))))))

; The stack starts with a root frame; a ) closes the $ frames above the nearest ( frame and then that
; frame; a ) with only the root open, a form still open at the end, or a bad token is a syntax error
; (DESIGN.md section 2).
(def-fns _ $ many parse-toks : (subterm many (List (Tok)) toks) (many (List (Frame)) stack) -> (many (List (Frame)) r) (many (Maybe (String)) err)
  (match many toks _
    ((Nil a) (values stack (None (String))))
    ((Cons a t rest)
      (match many t _
        ((TOpen) (parse-toks (subterm _) rest (Cons (Frame) (MkFrame (BFalse) (Nil (Raw))) stack)))
        ((TDollar) (parse-toks (subterm _) rest (Cons (Frame) (MkFrame (BTrue) (Nil (Raw))) stack)))
        ((TWord w) (parse-toks (subterm _) rest (push-item (predates _) (RAtom w) stack)))
        ((TStrLit s) (parse-toks (subterm _) rest (push-item (predates _) (RString s) stack)))
        ((TError m) (values stack (Some (String) m)))
        ((TClose)
          (let (many s1) (close-dollars (predates _) (list-length (predates _) (Frame) stack) stack))
          (match many s1 _
            ((Nil b) (values s1 (Some (String) "unexpected )")))
            ((Cons b f s2)
              (match many s2 _
                ((Nil c) (values s1 (Some (String) "unexpected )")))
                ((Cons c g s3) (parse-toks (subterm _) rest (close-top (predates _) s1)))))))))))

; Reads the root frame's items once nothing is open; an open form at the end is a missing ), reported
; for the innermost, which is the $ form's when that is what is open.
(def-fns _ $ many finish-stack : (many (List (Frame)) stack) -> (many (List (Raw)) items) (many (Maybe (String)) err)
  (match many stack _
    ((Nil a) (values (Nil (Raw)) (None (String))))
    ((Cons a f rest)
      (match many rest _
        ((Nil b) (match many f _ ((MkFrame d items) (values (list-rev (predates _) (Raw) items) (None (String))))))
        ((Cons b g rest2)
          (match many f _
            ((MkFrame d items) (values (Nil (Raw)) (Some (String) (match many d (((String) m)) ((BTrue) "missing ) after $") ((BFalse) "missing )")))))))))))

(def-fns _ $ many parse : (many (String) src) -> (many (List (Raw)) items) (many (Maybe (String)) err)
  (let (many stack) (many err) (parse-toks (predates _) (tokenize (predates _) src (Nil (Tok)))
                                            (Cons (Frame) (MkFrame (BFalse) (Nil (Raw))) (Nil (Frame)))))
  (match many err _
    ((Some a m) (values (Nil (Raw)) err))
    ((None a) (finish-stack (predates _) stack))))

(def-fns _
  (many show-raw : (subterm many (Raw) r) -> (many (Rope) out)
    (match many r _
      ((RAtom s) (RStr s))
      ((RString s) (rcat3 (predates _) (RStr "\"") (RStr (ocaml-escape (predates _) s)) (RStr "\"")))
      ((RList items) (rcat3 (predates _) (RStr "(") (show-raws (subterm _) items) (RStr ")")))))
  (many show-raws : (subterm many (List (Raw)) rs) -> (many (Rope) out)
    (match many rs _
      ((Nil a) (REmpty))
      ((Cons a r rest)
        (match many rest _
          ((Nil b) (show-raw (subterm _) r))
          ((Cons b r2 rest2) (rcat3 (predates _) (show-raw (subterm _) r) (RStr " ") (show-raws (subterm _) rest))))))))
