(def-fns _ $ (many rope-str : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased _)) (flatten r))
  s)

(def-fns _ $ (many lines-onto : (many (Rope) acc) (subterm many (String) s) -> (many (List $ String) r))
  (let-match many s (SCons c rest) ((SNil) (Cons _ (rope-str acc) $ Nil _)))
  (match many (char-cmp c #\newline) _
    ((CEq _ _ _) (Cons _ (rope-str acc) $ notail $ lines-onto (REmpty) rest))
    (else (tail $ lines-onto (RCat acc $ RChar c) rest))))

(def-fns _ $ (many non-empty : (subterm many (List $ String) xs) -> (many (List $ String) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let ((many r)) (notail $ non-empty rest))
  (match many x _ ((SNil) r) ((SCons _ _) (Cons _ x r))))

(def-fns _ $ (many words : (many (String) s) -> (many (List $ String) r))
  (non-empty $ lines-onto (REmpty) s))

(def-fns _ $ (many unwords : (subterm many (List $ String) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (REmpty)))
  (RCat (RCat (RChar #\space) (RStr x)) $ notail $ unwords rest))

(def-fns _ $ (many report : (many (String) query) (many (List $ String) ws) -> (many (String) out))
  (let-match many (words query) (Cons _ q _) ((Nil _) "no query word\n"))
  (let ((many best) (many ties)) (nearest-names q ws))
  (let-match many best (Some _ d) ((None _) "no words\n"))
  (rope-str $ RCat (RCat (RStr (nat-str d)) (unwords ties)) (RChar #\newline)))

(def-fns _ $ (many read : (unique (World) w) (many (String) path) -> (unique (World) w2 at w) (many (Maybe $ String) r))
  (let ((unique w1) (many r)) (world-do _ w (ReadFile path)))
  (values w1 (match many r _ ((Ok _ s) (Some _ s)) ((Fail _ _) (None _)))))

(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes _ _ one-u8))
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ zero-u8))

(def-fns _ $ (many fail : (erased (Level) L) (unique (World) w) (many (String) msg) -> (unique (World) w2 at w) (unique (Program L) next))
  (let ((unique w1) (many _)) (world-do _ w (WriteErr msg)))
  (values w1 (Exit L (MkU8 1 one-u8))))

(def-lvl Main)

(def-unique Main $ (unique start : (unique (World) w) -> (unique (World) w2 at w) (unique (Program Main) next))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let-match many args (Cons _ wf rest) ((Nil _) (fail Main w1 "usage: -- WORDS-FILE QUERY-FILE\n")))
  (let-match many rest (Cons _ qf _) ((Nil _) (fail Main w1 "usage: -- WORDS-FILE QUERY-FILE\n")))
  (let ((unique w2) (many ws)) (read w1 wf))
  (let ((unique w3) (many qs)) (read w2 qf))
  (let-match many ws (Some _ wtext) ((None _) (fail Main w3 "cannot read words file\n")))
  (let-match many qs (Some _ qtext) ((None _) (fail Main w3 "cannot read query file\n")))
  (let ((unique w4) (many _)) (world-do _ w3 (WriteOut (report qtext (words wtext)))))
  (values w4 (Exit Main (MkU8 0 zero-u8))))

(Continue Main start)
