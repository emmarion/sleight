; Round-6 review of 06: run.sl's driver on OPred of a register holding 0, which no Runs rule covers; prints stuck.
; Needs std/list.sl, spec.sl and machine.sl first.

(def-fns _ $ (many show-val : (many (Val) v) -> (many (String) s))
  (match many v _ ((VNum n) (nat-str n)) ((VPtr a) (str-append "#" $ nat-str a))))

(def-fns _ $ (many show-vals : (subterm many (List (Val)) vs) -> (many (String) s))
  (let-match many vs (Cons _ v rest) ((Nil _) ""))
  (str-append " " $ str-append (show-val v) $ notail $ show-vals rest))

(def-fns _ $ (many show-heap : (subterm many (List (List (Val))) h) -> (many (String) s))
  (let-match many h (Cons _ blk rest) ((Nil _) ""))
  (str-append " [" $ str-append (show-vals blk) $ str-append " ]" $ notail $ show-heap rest))

(def-fns _ $ (many block : (subterm many (List (Cmd)) cs) -> (many (Cmd) c))
  (let-match many cs (Cons _ c rest) ((Nil _) (CSkip)))
  (CSeq c $ notail $ block rest))

(def-lvl D)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns D $ (many drive : (erased (Cmd) c0) (erased (Mem) m0) (many (Nat) n) (many (List (Cmd)) k) (many (Mem) m)
    (erased (Trace (Cons (Cmd) c0 (Nil (Cmd))) m0 k m) t) -> (unique (Program P) p))
  (def-unique P $ (unique again : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
    (let-match many (advance c0 m0 k m t) (Ended _ _ _ _ o)
      ((Running _ _ _ _ k2 m2 t2 _) (values w (drive c0 m0 (Succ n) k2 m2 t2))))
    (let-match many o (Halted _ _ mf d)
      ((Stuck _ _)
        (let ((unique w1) (many _)) (world-do _ w (WriteOut "stuck\n")))
        (values w1 (Exit P code0))))
    (let-match many mf (MkMem e h))
    (let ((unique w1) (many _))
      (world-do _ w (WriteOut $ str-append "halted after " $ str-append (nat-str n) $ str-append " steps; registers"
        $ str-append (show-vals e) $ str-append "; heap" $ str-append (show-heap h) "\n")))
    (values w1 (Exit P code0)))
  (Continue P again))

(let ((many prog)) (COp $ OPred 0 0))
(let ((many mem0)) (MkMem (Cons _ (VNum 0) $ Nil _) (Nil _)))
(drive prog mem0 0 (Cons _ prog $ Nil _) mem0 (TNil (Cons _ prog $ Nil _) mem0))
