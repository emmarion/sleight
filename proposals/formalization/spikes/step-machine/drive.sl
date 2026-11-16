(def-fns _ $ (many step-many : (erased (Env) env0) (erased (Core) c0) (subterm many (Nat) quantum) (many (State env0 c0) s) (many (Nat) steps) ->
    (many (Stepped env0 c0) r) (many (Nat) steps-after))
  (let-match many quantum (Succ smaller) ((Zero) (values (Next _ _ s) steps)))
  (let-match many (step _ _ s) (Next _ _ s2) ((Halted _ _ result) (values (Halted _ _ result) (Succ steps))))
  (tail $ step-many _ _ smaller s2 (Succ steps)))

(def-fns _ $ (many unary-of : (subterm many (Val) v) (many (Nat) acc) -> (many (Maybe (Nat)) n))
  (let-match many v (VCon _ args) (else (None _)))
  (let-match many args (Cons _ pred rest) ((Nil _) (Some _ acc)))
  (let-match many rest (Nil _) (else (None _)))
  (tail $ unary-of pred (Succ acc)))

(def-fns _
  ((many show-val : (subterm many (Val) v) -> (many (String) s))
    (match many v _
      ((VCon ctor args) (str-append "(VCon " $ str-append (nat-str ctor) $ str-append (notail $ show-vals args) ")"))
      ((VAtom id) (str-append "(VAtom " $ str-append (nat-str id) ")"))
      ((VFormer _ _) "(VFormer)")
      ((VClo _ _ _) "(VClo)")
      ((VToken) "(VToken)")))
  ((many show-vals : (subterm many (List (Val)) vs) -> (many (String) s))
    (let-match many vs (Cons _ v rest) ((Nil _) ""))
    (str-append " " $ str-append (notail $ show-val v) (notail $ show-vals rest))))

(def-fns _ $ (many show-result : (many (List (Val)) vs) -> (many (String) s))
  (let-match many (single vs) (IsSingle v) ((NotSingle _) (show-vals vs)))
  (match many (unary-of v 0) _
    ((Some _ n) (str-append " unary " (nat-str n)))
    ((None _) (show-vals vs))))

(def-fns _ $ (many report : (erased (Env) env0) (erased (Core) c0) (many (Evaled env0 c0) result) (many (String) unit) (many (Nat) spent) -> (many (String) line))
  (let ((many (String) outcome))
    (match many result _
      ((MkEvaled _ _ vs _) (str-append "done" (show-result vs)))
      ((EvalStuck _ _) "stuck")))
  (str-append outcome $ str-append " " $ str-append unit $ str-append " " $ str-append (nat-str spent) "\n"))

(def-lvl FINISH)
(def-lvl WORK)
(def-lvl PROG)
(let ((many exit-ok)) (MkU8 (Zero) u8-modulus-pos))

(def-fns FINISH $ (many finish : (erased (Env) env0) (erased (Core) c0) (many (Evaled env0 c0) result) (many (String) unit) (many (Nat) spent) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program PROG) p))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut (report _ _ result unit spent))))
  (values w1 (Exit PROG exit-ok)))

(def-fns WORK
  ((many drive : (erased (Env) env0) (erased (Core) c0) (many (State env0 c0) s) (many (Nat) steps) (unique (World) w at vacant-slot) ->
      (unique (World) w2 at w) (unique (Program PROG) p))
    (let-match many (step _ _ s) (Next _ _ s2) ((Halted _ _ result) (finish _ _ result "steps" (Succ steps) w)))
    (def-unique PROG $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program PROG) p))
      (drive _ _ s2 (Succ steps) v))
    (values w (Continue PROG again)))
  ((many drive-batched : (erased (Env) env0) (erased (Core) c0) (many (Nat) quantum) (many (State env0 c0) s) (many (Nat) steps) (unique (World) w at vacant-slot) ->
      (unique (World) w2 at w) (unique (Program PROG) p))
    (let ((many stepped) (many steps-after)) (step-many _ _ quantum s steps))
    (let-match many stepped (Next _ _ s2) ((Halted _ _ result) (finish _ _ result "steps" steps-after w)))
    (def-unique PROG $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program PROG) p))
      (drive-batched _ _ quantum s2 steps-after v))
    (values w (Continue PROG again))))

