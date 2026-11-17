; A heap machine for a tiny ANF fragment of post-erasure code: a total single step over an explicit
; continuation, slot-eq answered from an oracle bit, and a fuel-free run by the Program driver.
; An overnight agent's proposal; nothing here is settled design.

(def-adts
  ((Word : -> Type)
    enum
    (many WImm : (many (Nat) n) -> (Word))
    (many WPtr : (many (Nat) a) -> (Word)))
  ((Code : -> Type)
    enum
    (many KVar : (many (Nat) i) -> (Code))
    (many KImm : (many (Nat) n) -> (Code))
    (many KCon : (many (Nat) tag) (many (List (Nat)) args) -> (Code))
    (many KCellAlloc : (many (Nat) tag) (many (Nat) arity) -> (Code))
    (many KInvoke : (many (Nat) cell) (many (List (Nat)) args) -> (Code))
    (many KSlotEq : (many (Nat) a) (many (Nat) b) -> (Code))
    (many KLam : (many (Code) body) -> (Code))
    (many KApp : (many (Nat) f) (many (Nat) arg) -> (Code))
    (many KLet : (many (Code) rhs) (many (Code) rest) -> (Code))
    (many KField : (many (Nat) v) (many (Nat) i) -> (Code)))
  ((Block : -> Type)
    enum
    (many BCon : (many (Nat) tag) (many (List (Word)) fields) -> (Block))
    (many BClo : (many (Code) body) (many (List (Word)) env) -> (Block)))
  ((Frame : -> Type)
    enum
    (many FLet : (many (List (Word)) env) (many (Code) rest) -> (Frame)))
  ((Cfg : -> Type)
    enum
    (many Eval : (many (Code) c) (many (List (Word)) env) (many (List (Frame)) k) (many (List (Block)) heap) -> (Cfg))
    (many Ret : (many (Word) w) (many (List (Frame)) k) (many (List (Block)) heap) -> (Cfg)))
  ((Step : -> Type)
    enum
    (many Next : (many (Cfg) c) -> (Step))
    (many Done : (many (Word) w) (many (List (Block)) heap) -> (Step))
    (many Stuck : -> (Step))))

(def-fns _ $ (many nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (Maybe A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (None _)))
  (match many i _ ((Zero) (Some _ x)) ((Succ j) (tail $ nth _ rest j))))

(def-fns _ $ (many set-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) (many A y) -> (many (List A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (match many i _ ((Zero) (Cons _ y rest)) ((Succ j) (Cons _ x $ notail $ set-nth _ rest j y))))

(def-fns _ $ (many snoc : (erased Type A) (subterm many (List A) xs) (many A y) -> (many (List A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Cons _ y $ Nil _)))
  (Cons _ x $ notail $ snoc _ rest y))

(def-fns _ $ (many len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (let-match many xs (Cons _ _ rest) ((Nil _) 0))
  (Succ $ notail $ len _ rest))

(def-fns _ $ (many lookup-all : (many (List (Word)) env) (subterm many (List (Nat)) ids) -> (many (Maybe (List (Word))) r))
  (let-match many ids (Cons _ i rest) ((Nil _) (Some _ $ Nil _)))
  (let-match many (nth _ env i) (Some _ w) ((None _) (None _)))
  (let-match many (notail $ lookup-all env rest) (Some _ ws) ((None _) (None _)))
  (Some _ $ Cons _ w ws))

(def-fns _ $ (many repeat-vacant : (subterm many (Nat) n) -> (many (List (Word)) ws))
  (let-match many n (Succ m) ((Zero) (Nil _)))
  (Cons _ (WImm 0) $ notail $ repeat-vacant m))

(def-fns _ $ (many nat-eqb : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (match many (nat-eq a b) _ ((Equal _ _ _) (BTrue)) ((Unequal _ _ _ _ _) (BFalse))))

(def-fns _ $ (many word-eq : (many (Word) a) (many (Word) b) -> (many (Bool) r))
  (match many a _
    ((WImm m) (match many b _ ((WImm n) (nat-eqb m n)) ((WPtr _) (BFalse))))
    ((WPtr m) (match many b _ ((WPtr n) (nat-eqb m n)) ((WImm _) (BFalse))))))

(def-fns _ $ (many alloc : (many (List (Block)) heap) (many (Block) b) -> (many (Word) w) (many (List (Block)) heap2))
  (values (WPtr $ len _ heap) (snoc _ heap b)))

(def-fns _ $ (many step : (many (Bool) bit) (many (Cfg) cfg) -> (many (Step) r))
  (let-match many cfg (Eval c env k heap)
    ((Ret w k heap)
      (let-match many k (Cons _ fr rest) ((Nil _) (Done w heap)))
      (let-match many fr (FLet env code))
      (Next $ Eval code (Cons _ w env) rest heap)))
  (match many c _
    ((KVar i) (match many (nth _ env i) _ ((Some _ w) (Next $ Ret w k heap)) ((None _) (Stuck))))
    ((KImm n) (Next $ Ret (WImm n) k heap))
    ((KCon tag args)
      (let-match many (lookup-all env args) (Some _ ws) ((None _) (Stuck)))
      (let ((many w) (many h2)) (alloc heap $ BCon tag ws))
      (Next $ Ret w k h2))
    ((KCellAlloc tag n)
      (let ((many w) (many h2)) (alloc heap $ BCon tag $ repeat-vacant n))
      (Next $ Ret w k h2))
    ((KInvoke u args)
      (let-match many (nth _ env u) (Some _ cw) ((None _) (Stuck)))
      (let-match many cw (WPtr a) ((WImm _) (Stuck)))
      (let-match many (nth _ heap a) (Some _ b) ((None _) (Stuck)))
      (let-match many b (BCon tag _) (else (Stuck)))
      (let-match many (lookup-all env args) (Some _ ws) ((None _) (Stuck)))
      (Next $ Ret cw k $ set-nth _ heap a $ BCon tag ws))
    ((KSlotEq a b)
      (let-match many (lookup-all env $ Cons _ a $ Cons _ b $ Nil _) (Some _ ws) ((None _) (Stuck)))
      (let-match many ws (Cons _ x r1) ((Nil _) (Stuck)))
      (let-match many r1 (Cons _ y _) ((Nil _) (Stuck)))
      (let-match many bit (BTrue) ((BFalse) (Next $ Ret (WImm 0) k heap)))
      (match many (word-eq x y) _ ((BTrue) (Next $ Ret (WImm 1) k heap)) ((BFalse) (Next $ Ret (WImm 0) k heap))))
    ((KLam body)
      (let ((many w) (many h2)) (alloc heap $ BClo body env))
      (Next $ Ret w k h2))
    ((KApp f x)
      (let-match many (lookup-all env $ Cons _ f $ Cons _ x $ Nil _) (Some _ ws) ((None _) (Stuck)))
      (let-match many ws (Cons _ fw r1) ((Nil _) (Stuck)))
      (let-match many r1 (Cons _ xw _) ((Nil _) (Stuck)))
      (let-match many fw (WPtr a) ((WImm _) (Stuck)))
      (let-match many (nth _ heap a) (Some _ b) ((None _) (Stuck)))
      (let-match many b (BClo body cenv) (else (Stuck)))
      (Next $ Eval body (Cons _ xw cenv) k heap))
    ((KLet rhs rest) (Next $ Eval rhs env (Cons _ (FLet env rest) k) heap))
    ((KField v i)
      (let-match many (nth _ env v) (Some _ vw) ((None _) (Stuck)))
      (let-match many vw (WPtr a) ((WImm _) (Stuck)))
      (let-match many (nth _ heap a) (Some _ b) ((None _) (Stuck)))
      (let-match many b (BCon _ fs) (else (Stuck)))
      (match many (nth _ fs i) _ ((Some _ w) (Next $ Ret w k heap)) ((None _) (Stuck))))))

(def-fns _ $ (many word-str : (many (Word) w) -> (many (String) s))
  (match many w _
    ((WImm n) (str-append "imm " $ nat-str n))
    ((WPtr a) (str-append "ptr " $ nat-str a))))

(def-fns _ $ (many bits : (subterm many (Nat) n) -> (many (List (Bool)) r))
  (let-match many n (Succ m) ((Zero) (Nil _)))
  (Cons _ (BTrue) $ notail $ bits m))

(let ((many tape)) (bits 100))

(def-lvl MA)
(def-lvl M)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many ok)) (MkU8 0 zp0))

(def-fns MA $ (many drive : (many (List (Bool)) oracle) (many (Cfg) cfg) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program M) p))
  (let-match many oracle (Cons _ bit more) ((Nil _) (values w (Exit M ok))))
  (match many (step bit cfg) _
    ((Stuck)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut "stuck\n")))
      (values w1 (Exit M ok)))
    ((Done r _)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append (word-str r) "\n")))
      (values w1 (Exit M ok)))
    ((Next c2)
      (def-unique M $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program M) p))
        (drive more c2 v))
      (values w (Continue M again)))))

(let ((many prog))
  (KLet (KCellAlloc 1 2) $ KLet (KVar 0) $ KLet (KImm 7) $ KLet (KInvoke 2 $ Cons _ 0 $ Cons _ 0 $ Nil _) $
    KLet (KSlotEq 2 0) $ KLet (KCon 1 $ Cons _ 0 $ Cons _ 1 $ Nil _) $ KField 0 0))

(def-unique M $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program M) p))
  (drive tape (Eval prog (Nil _) (Nil _) (Nil _)) w))

(Continue M start)
