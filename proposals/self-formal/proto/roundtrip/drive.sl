(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))
(let ((many d1)) (lt-dec 1 u8-modulus))
(comptime-match many d1 (Yes _ _ za1 zb1 zp1))
(let ((many code1)) (MkU8 1 zp1))

(let ((many omega)) (App (Lam $ App (Var 0) (Var 0)) (Lam $ App (Var 0) (Var 0))))
(let ((many k-comb)) (Lam $ Lam $ Var 1))

(def-fns _ $ (many prog : (many (Nat) which) -> (many (List $ Stmt) p))
  (let ((many ok)) (Cons _ (Let $ App (App k-comb (Num 3)) (Num 0)) $ Cons _ (Assert 0 (CSucc)) $ Cons _ (Need 0 (CSucc))
    $ Cons _ (Let $ App (Lam $ Var 1) k-comb) $ Cons _ (Assert 0 (CSucc)) $ Cons _ (Need 1 (CSucc)) $ Nil _))
  (let-match many which (Succ w1) ((Zero) ok))
  (let-match many w1 (Succ w2) ((Zero) (Cons _ (Let $ Num 3) $ Cons _ (Need 0 (CSucc)) $ Nil _)))
  (let-match many w2 (Succ w3) ((Zero) (Cons _ (Let $ Num 0) $ Cons _ (Assert 0 (CSucc)) $ Nil _)))
  (let-match many w3 (Succ w4) ((Zero) (Cons _ (Let $ App (Num 1) (Num 2)) ok)))
  (let-match many w4 (Succ w5) ((Zero) (Cons _ (Let $ Var 5) $ Nil _)))
  (let-match many w5 (Succ w6) ((Zero) (Cons _ (Let $ Num 1) $ Cons _ (Assert 1 (CZero)) $ Nil _)))
  (Cons _ (Let omega) $ Cons _ (Need 0 (CZero)) $ Nil _))

(def-fns _ $ (many arg-nat : (many (List $ String) args) -> (many (Nat) n) (many (List $ String) rest))
  (let-match many args (Cons _ a rest) ((Nil _) (values 0 args)))
  (match many (str-nat a) _ ((Some _ n) (values n rest)) ((None _) (values 0 rest))))

(def-lvl M)
(def-fns M
  ((many zipper : (erased (List $ Stmt) p) (many (CState p) s) -> (many (Turn CState p) t)) (cstep p s))
  ((many replay : (erased (List $ Stmt) p) (many (RState p) s) -> (many (Turn RState p) t)) (rstep p s)))

(def-lvl PA)
(def-lvl P)

(def-fns PA $ (many drive : (erased (TyCtor ((List $ Stmt) p) -> Type) S)
    (many (Fn M (erased (List $ Stmt) p) (many (S p) s) -> (many (Turn S p) t)) step)
    (erased (List $ Stmt) p0) (many (S p0) s) (many (Nat) n) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program P) next))
  (let-match many (step p0 s) (Fin _ _ v)
    ((More _ _ s2)
      (def-unique P $ (unique again : (unique (World) u at vacant-slot) -> (unique (World) u2 at u) (unique (Program P) next))
        (drive S step p0 s2 (Succ n) u))
      (values w (Continue P again))))
  (let ((many after)) (str-append " after " $ str-append (nat-str $ Succ n) " Program steps\n"))
  (match many v _
    ((Accepted _ _)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append "accepted" after)))
      (values w1 (Exit P code0)))
    ((Rejected _ _ why)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append "rejected: " $ str-append why after)))
      (values w1 (Exit P code1)))))

(def-unique P $ (unique main : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((many which) (many args2)) (arg-nat args))
  (let ((many how) (many _)) (arg-nat args2))
  (let ((many p0)) (prog which))
  (match many how _
    ((Zero) (drive CState zipper p0 (start p0) 0 w1))
    ((Succ _) (drive RState replay p0 (rstart p0) 0 w1))))

(Continue P main)
