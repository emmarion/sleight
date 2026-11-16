(def-fns WORK $ (many drive-sampled : (erased (Env) env0) (erased (Core) c0) (many (Nat) quantum) (many (State env0 c0) s) (many (Nat) steps) (many (Nat) deepest) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program PROG) p))
  (let ((many stepped) (many steps-after)) (step-many _ _ quantum s steps))
  (let-match many stepped (Next _ _ s2)
    ((Halted _ _ result)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut (str-append "deepest sampled stack " $ str-append (nat-str deepest) "\n"))))
      (finish _ _ result "steps" steps-after w1)))
  (let ((many depth)) (state-depth _ _ s2))
  (let ((many (Nat) deeper))
    (match many (lt-dec deepest depth) _
      ((Yes _ _ _ _ _) depth)
      ((No _ _ _ _ _) deepest)))
  (def-unique PROG $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program PROG) p))
    (drive-sampled _ _ quantum s2 steps-after deeper v))
  (values w (Continue PROG again)))

(def-unique PROG $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program PROG) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many program)) (build (arg-or args 0 "pred") (parse-nat-or (arg-or args 1 "") 2)))
  (drive-sampled _ _ (parse-nat-or (arg-or args 2 "") 1) (load program) 0 0 w1))

(Continue PROG start)
