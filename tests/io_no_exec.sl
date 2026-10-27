; no-exec: yes
; expect: Fail /bin/sh: exec is disabled (--no-exec)
; expect: Fail true: exec is disabled (--no-exec)
; expect: empty: []
; Under --no-exec every job of an Exec request answers Fail without running anything, and a request with
; no jobs answers no results.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many shown : (subterm many (List (Result (Exited))) rs) -> (many (String) s))
  (let-match many rs (Cons _ r rest) ((Nil _) ""))
  (str-append (match many r (((String) _)) ((Ok _ _) "ran\n") ((Fail _ m) (str-append "Fail " $ str-append m "\n"))) $ notail $ shown rest))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many done)) (world-do _ w (Exec (None _) $ Cons _ (MkExecJob "/bin/sh" (Cons _ "-c" $ Cons _ "true" $ Nil _) (Nil _) (None _) "") $ Cons _ (MkExecJob "true" (Nil _) (Nil _) (None _) "") $ Nil _)))
  (let-match many done (MkExecResults _ rs _ _ _))
  (let ((unique w2) (many none)) (world-do _ w1 (Exec (None _) (Nil _))))
  (let-match many none (MkExecResults _ zs _ _ _))
  (let ((unique w3) (many _)) (world-do _ w2 (WriteOut $ str-append (shown rs) $ str-append "empty: [" $ str-append (shown zs) "]\n")))
  (values w3 (Exit P code0)))

(Continue P start)
