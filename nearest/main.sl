(def-fns _ $ (many rope-str : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased _)) (flatten r))
  s)

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
  (let ((unique w4) (many _)) (world-do _ w3 (WriteOut (answer wtext qtext))))
  (values w4 (Exit Main (MkU8 0 zero-u8))))

(Continue Main start)
