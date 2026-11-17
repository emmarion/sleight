; Accepted and run (added by the reviewer): a closure invariant at one fixed level L, applied by the stepper at a
; halt, extended each step through a same-level call that decreases an erased step counter. The demo's
; fuel is only for the demo. Needs std/list.sl, spec.sl and machine.sl first.
(def-lvl L)
(def-adts $ (CState : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many CS : (erased (Cmd) c0) (erased (Mem) m0) (many (List (Cmd)) k) (many (Mem) m) (erased (Nat) n)
     (erased (Fn L (subterm erased (Nat) j) (erased (Eq (Nat) j n) e) (erased (Mem) mf) (erased (RunsAll m k mf) a)
        -> (erased (Runs m0 c0 mf) d)) inv) -> (CState c0 m0)))

(def-adts $ (CAdv : ((Cmd) c0) ((Mem) m0) -> Type)
  enum
  (many CNext : (erased (Cmd) c0) (erased (Mem) m0) (many (CState c0 m0) st) -> (CAdv c0 m0))
  (many CEnd : (erased (Cmd) c0) (erased (Mem) m0) (many (Outcome c0 m0) o) -> (CAdv c0 m0)))

(def-fns _ $ (many adv-c : (erased (Cmd) c0) (erased (Mem) m0) (many (CState c0 m0) st) -> (many (CAdv c0 m0) r))
  (let-match many st (CS _ _ k m n inv))
  (let-match many (step k m) (SNext _ _ k2 m2 s)
    ((SHalt _) (CEnd _ _ (Halted _ _ m (inv n (Refl _ n) m (RANil m)))))
    ((SStuck _ _) (CEnd _ _ (Stuck _ _))))
  (def-fns L $ (erased inv2 : (subterm erased (Nat) j) (erased (Eq (Nat) j (Succ n)) e) (erased (Mem) mf)
      (erased (RunsAll m2 k2 mf) a) -> (erased (Runs m0 c0 mf) d))
    (let-match erased e (Refl _ _))
    (inv n (Refl _ n) mf (step-back k k2 m m2 mf s a)))
  (CNext _ _ (CS c0 m0 k2 m2 (Succ n) inv2)))
(def-fns _ $ (many fin : (erased (Cmd) c0) (erased (Mem) m0) (many (CState c0 m0) st) (subterm many (Nat) fuel) -> (many (Nat) r))
  (let-match many fuel (Succ f) ((Zero) 99))
  (let-match many (adv-c c0 m0 st) (CNext _ _ st2) ((CEnd _ _ o) (match many o _ ((Halted _ _ mf d) 0) ((Stuck _ _) 1))))
  (tail (fin c0 m0 st2 f)))
(let ((many prog)) (CSeq (COp $ OSet 0 3) (CWhile 0 $ COp $ OPred 0 0)))
(let ((many mem0)) (MkMem (Cons _ (VNum 9) $ Nil _) (Nil _)))
(def-fns L $ (erased inv0 : (subterm erased (Nat) j) (erased (Eq (Nat) j (Zero)) e) (erased (Mem) mf)
   (erased (RunsAll mem0 (Cons _ prog $ Nil _) mf) a) -> (erased (Runs mem0 prog mf) d))
  (let-match erased a (RACons _ m1 _ _ _ d a1))
  (let-match erased a1 (RANil _))
  d)
(fin prog mem0 (CS prog mem0 (Cons _ prog $ Nil _) mem0 (Zero) inv0) 1000)
