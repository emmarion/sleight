(def-lvl W)
(def-lvl K)

(def-adts $ (LoopM : -> Type)
  enum
  (many LRet : (many (Nat) v) -> (LoopM))
  (many LBind : (many (LoopM) m) (many (Fn K (many (Nat) x) -> (many (LoopM) next)) f) -> (LoopM)))

(def-fns W $ (many spin : (subterm many (Tree) t) -> (many (LoopM) m))
  (def-fns K $ (many again : (many (Nat) x) -> (many (LoopM) next))
    (spin t))
  (LBind (LRet 0) again))

(def-fns _ $ (many turn : (many (LoopM) m) (many (List (Fn K (many (Nat) x) -> (many (LoopM) next))) stack) ->
    (many (Maybe (LoopM)) m2) (many (List (Fn K (many (Nat) x) -> (many (LoopM) next))) stack2))
  (let-match many m (LRet v) ((LBind m1 f) (values (Some _ m1) (Cons _ f stack))))
  (let-match many stack (Cons _ f rest) ((Nil _) (values (None _) stack)))
  (values (Some _ (f v)) rest))

(def-lvl drive-lvl)
(def-lvl P)

(def-fns drive-lvl $ (many drive : (unique (World) w at vacant-slot) (many (LoopM) m) (many (List (Fn K (many (Nat) x) -> (many (LoopM) next))) stack) (many (Nat) steps) ->
    (unique (World) w2 at w) (unique (Program P) p))
  (let ((many m2) (many stack2)) (turn m stack))
  (let-match many m2 (Some _ m3) ((None _) (values w (Exit P code0))))
  (let-match many (nat-eq steps 100000) (Unequal _ _ _ _ _)
    ((Equal _ _ _)
      (let ((unique w1) (many _)) (world-do _ w (WriteOut "still looping after 100000 driver steps; giving up\n")))
      (values w1 (Exit P code2))))
  (def-unique P $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program P) p))
    (drive v m3 stack2 (Succ steps)))
  (values w (Continue P again)))

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (drive w (spin demo-tree) (Nil _) 0))

(Continue P start)
