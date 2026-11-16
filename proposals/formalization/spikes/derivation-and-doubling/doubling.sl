(def-fns _
  ((many show-val : (subterm many (Val) v) -> (many (String) s))
    (match many v _
      ((VCon h args) (str-append "(VCon " $ str-append (nat-str h) $ str-append (notail $ show-vals args) ")"))
      ((VAtom id) (str-append "(VAtom " $ str-append (nat-str id) ")"))
      ((VFormer _ _) "(VFormer)")
      ((VClo _ _ _) "(VClo)")
      ((VToken) "(VToken)")))
  ((many show-vals : (subterm many (List (Val)) vs) -> (many (String) s))
    (let-match many vs (Cons _ v rest) ((Nil _) ""))
    (str-append " " $ str-append (notail $ show-val v) (notail $ show-vals rest))))

(def-fns _ $ (many arg-nat : (subterm many (List (String)) args) (many (Nat) i) (many (Nat) default) -> (many (Nat) n))
  (let-match many args (Cons _ a rest) ((Nil _) default))
  (let-match many i (Succ j) ((Zero) (match many (str-nat a) _ ((Some _ n) n) ((None _) default))))
  (tail $ arg-nat rest j default))

(def-fns _ $ (many stamp : (unique (World) w at vacant-slot) (many (String) label) -> (unique (World) w2 at w))
  (let ((unique w1) (many usage)) (world-do _ w (Measure (Stop))))
  (let-match many usage (MkUsage _ user-ns _ _ _ _ _ _))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteErr (str-append label $ str-append " at user-ns " $ str-append (nat-str user-ns) "\n"))))
  w2)

(def-adts $ (Outcome : -> Type)
  enum
  (many Values : (many (List (Val)) vs) -> (Outcome))
  (many Failure : (many (Why) w) -> (Outcome)))

(def-lvl evaluator)

(def-fns evaluator $ (many by-eval : (many (Nat) fuel) (many (Core) c) -> (many (Outcome) o))
  (match many (eval fuel (ENil) c) _
    ((MkEvaled _ _ vs _) (Values vs))
    ((EvalFail _ _ w) (Failure w))))

(def-fns evaluator $ (many by-run : (many (Nat) fuel) (many (Core) c) -> (many (Outcome) o))
  (match many (run fuel (ENil) c) _
    ((Done _ _ _ vs _) (Values vs))
    ((Failed _ _ _ w _) (Failure w))))

(def-lvl PA)
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ _ _ zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes _ _ _ _ zp1))
(let ((many code1)) (MkU8 1 zp1))

(def-fns PA $ (many attempt : (unique (World) w at vacant-slot) (many (Fn evaluator (many (Nat) fuel) (many (Core) c) -> (many (Outcome) o)) ev) (many (Core) c) (many (Nat) fuel) ->
    (unique (World) w2 at w) (unique (Program P) p))
  (let ((many outcome)) (ev fuel c))
  (let ((many label)) (str-append "fuel " (nat-str fuel)))
  (let ((unique w1)) (stamp w (str-append label " done")))
  (let-match many outcome (Failure why)
    ((Values vs)
      (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ str-append ": values" $ str-append (show-vals vs) "\n"))))
      (values w2 (Exit P code0))))
  (let-match many why (OutOfFuel)
    ((Stuck)
      (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label ": stuck\n"))))
      (values w2 (Exit P code1))))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label ": out of fuel\n"))))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p)) (attempt v ev c (nat-add fuel fuel)))
  (values w2 (Continue P again)))

(def-fns PA $ (many pick : (many (Nat) which) -> (many (Fn evaluator (many (Nat) fuel) (many (Core) c) -> (many (Outcome) o)) ev))
  (match many which _ ((Zero) by-eval) ((Succ _) by-run)))

(MkUnit)
