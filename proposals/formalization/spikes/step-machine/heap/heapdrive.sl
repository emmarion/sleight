(def-fns _ $ (many hstep-many : (erased Store now) (erased Store s0) (erased (HExpr) e0) (subterm many (Nat) quantum) (many (HControl now s0 e0) c)
    (unique (Array (Copy (Nat)) now) heap) (many (Nat) steps) ->
    (erased Store after) (unique (Array (Copy (Nat)) after) heap-after at heap) (many (HStepped after s0 e0) r) (many (Nat) steps-after))
  (let-match many quantum (Succ smaller) ((Zero) (values now heap (HNext _ _ _ c) steps)))
  (let ((erased middle) (unique heap1) (many stepped)) (hstep _ _ _ c heap))
  (let-match many stepped (HNext _ _ _ c2)
    ((HHalted _ _ _ v p) (values middle heap1 (HHalted _ _ _ v p) (Succ steps)))
    ((HStuck _ _ _) (values middle heap1 (HStuck _ _ _) (Succ steps))))
  (tail $ hstep-many _ _ _ smaller c2 heap1 (Succ steps)))

(def-fns _ $ (many countdown : -> (many (HExpr) program))
  (let ((many counter)) (HLit 0))
  (HSeq (HWhile (HGet counter) (HSet counter (HPred (HGet counter)))) (HGet counter)))

(def-fns _ $ (many arg-nat : (subterm many (List (String)) args) (many (Nat) index) (many (Nat) default) -> (many (Nat) n))
  (let-match many args (Cons _ first rest) ((Nil _) default))
  (let-match many index (Succ before) ((Zero) (match many (str-nat first) _ ((Some _ n) n) ((None _) default))))
  (tail $ arg-nat rest before default))

(def-lvl HFINISH)
(def-lvl HWORK)
(def-lvl HPROG)
(let ((many exit-ok)) (MkU8 (Zero) u8-modulus-pos))

(def-fns HFINISH $ (many hfinish : (many (String) outcome) (many (Nat) steps) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program HPROG) p))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut (str-append outcome $ str-append " steps " $ str-append (nat-str steps) "\n"))))
  (values w1 (Exit HPROG exit-ok)))

(def-fns HWORK $ (many hdrive : (erased Store now) (erased Store s0) (erased (HExpr) e0) (many (Nat) quantum) (many (HControl now s0 e0) c)
    (unique (Array (Copy (Nat)) now) heap) (many (Nat) steps) (unique (World) w at vacant-slot) ->
    (unique (World) w2 at w) (unique (Program HPROG) p))
  (let ((erased _) (unique heap-after) (many stepped) (many steps-after)) (hstep-many _ _ _ quantum c heap steps))
  (let-match many stepped (HNext _ _ _ c2)
    ((HHalted _ _ _ v _) (hfinish (str-append "done value " (nat-str v)) steps-after w))
    ((HStuck _ _ _) (hfinish "stuck" steps-after w)))
  (def-unique HPROG $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program HPROG) p))
    (hdrive _ _ _ quantum c2 heap-after steps-after v))
  (values w (Continue HPROG again)))

(def-unique HPROG $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program HPROG) p))
  (let ((unique w1) (many args)) (world-do _ w (GetArgs)))
  (let ((erased _) (unique heap) (erased _)) (array-make _ (arg-nat args 1 1) (arg-nat args 0 3)))
  (let ((many program)) (countdown))
  (hdrive _ _ _ (arg-nat args 2 1) (HRun _ _ _ program $ MkHResume _ _ _ _ _ _ (HTailHere _ _) $ HDone _ _) heap 0 w1))

(Continue HPROG start)
