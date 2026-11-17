; The converse direction for spec.sl and machine.sl: Runs implies a finite run of Step, Step is
; deterministic, and so advance, iterated by recursion on that erased run, halts with the spec's result
; or is stuck. Needs std/list.sl, spec.sl and machine.sl earlier on the command line. An overnight
; agent's spike; nothing here is settled.

(def-adts $ (Star : ((List (Cmd)) k) ((Mem) m) ((List (Cmd)) k2) ((Mem) m2) -> Type)
  enum
  (many StarRefl : (erased (List (Cmd)) k) (erased (Mem) m) -> (Star k m k m))
  (many StarCons : (erased (List (Cmd)) k k1 k2) (erased (Mem) m m1 m2) (erased (Step k m k1 m1) s) (erased (Star k1 m1 k2 m2) d)
     -> (Star k m k2 m2)))

(def-fns _ $ (erased star-trans : (erased (List (Cmd)) k k1 k2) (erased (Mem) m m1 m2)
    (subterm erased (Star k m k1 m1) d) (erased (Star k1 m1 k2 m2) e) -> (erased (Star k m k2 m2) r))
  (match erased d _
    ((StarRefl _ _) e)
    ((StarCons _ ka _ _ ma _ s d1) (StarCons k ka k2 m ma m2 s (star-trans ka k1 k2 ma m1 m2 d1 e)))))

(def-fns _ $ (erased runs-star : (erased (Mem) m m1) (erased (Cmd) c) (erased (List (Cmd)) k) (subterm erased (Runs m c m1) d)
    -> (erased (Star (Cons (Cmd) c k) m k m1) r))
  (match erased d _
    ((ExSkip _) (StarCons _ k k m m m (SSkip k m) (StarRefl k m)))
    ((ExOp _ _ o r) (StarCons _ k k m m1 m1 (SOp k m m1 o r) (StarRefl k m1)))
    ((ExSeq _ ma _ c1 c2 d1 d2)
      (StarCons _ _ k m m m1 (SSeq k m c1 c2)
        (star-trans _ (Cons _ c2 k) k m ma m1 (runs-star m ma c1 (Cons _ c2 k) d1) (runs-star ma m1 c2 k d2))))
    ((ExIf _ _ x c1 c2 ca p d1) (StarCons _ _ k m m m1 (SIf k m x c1 c2 ca p) (runs-star m m1 ca k d1)))
    ((ExWhile _ _ x b d1) (StarCons _ _ k m m m1 (SWhile k m x b) (runs-star m m1 _ k d1)))))

(def-fns _ $ (erased step-det : (erased (List (Cmd)) k k1 k2) (erased (Mem) m m1 m2) (erased (Step k m k1 m1) s) (erased (Step k m k2 m2) u)
    -> (erased (Eq (List (Cmd)) k1 k2) e) (erased (Eq (Mem) m1 m2) f))
  (match erased s _
    ((SSkip _ _) (let-match erased u (SSkip _ _)) (values (Refl _ k1) (Refl _ m1)))
    ((SOp _ _ _ o r)
      (let-match erased u (SOp _ _ _ _ r2))
      (let-match erased (runop-fn m m1 m2 o r r2) (Refl _ _))
      (values (Refl _ k1) (Refl _ m1)))
    ((SSeq _ _ _ _) (let-match erased u (SSeq _ _ _ _)) (values (Refl _ k1) (Refl _ m1)))
    ((SIf ks _ x c1 c2 ca p)
      (let-match erased u (SIf _ _ _ _ _ cb q))
      (let-match erased (pick-fn m x c1 c2 ca cb p q) (Refl _ _))
      (values (Refl _ k1) (Refl _ m1)))
    ((SWhile _ _ _ _) (let-match erased u (SWhile _ _ _ _)) (values (Refl _ k1) (Refl _ m1)))))

(def-fns _ $ (many finish : (erased (Cmd) c0) (erased (Mem) m0 mf) (many (List (Cmd)) k) (many (Mem) m)
    (erased (Trace (Cons (Cmd) c0 (Nil (Cmd))) m0 k m) t) (subterm erased (Star k m (Nil (Cmd)) mf) d) -> (many (Outcome c0 m0) o))
  (let-match many (advance c0 m0 k m t) (Running _ _ _ _ k2 m2 t2 s) ((Ended _ _ _ _ o) o))
  (let-match erased d (StarCons _ k1 _ _ m1 _ s1 d1) (absurd (StarRefl _ _) s))
  (let ((erased e1) (erased e2)) (step-det k k2 k1 m m2 m1 s s1))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (tail (finish c0 m0 mf k2 m2 t2 d1)))

(def-adts $ (Agrees : ((Cmd) c0) ((Mem) m0) ((Mem) mf) -> Type)
  enum
  (many AgreeHalted : (erased (Cmd) c0) (erased (Mem) m0 mf) (many mf is r) -> (Agrees c0 m0 mf))
  (many AgreeStuck : (erased (Cmd) c0) (erased (Mem) m0 mf) -> (Agrees c0 m0 mf)))

(def-fns _ $ (many run-total : (many (Cmd) c0) (many (Mem) m0) (erased (Mem) mf) (erased (Runs m0 c0 mf) spec)
    -> (many (Agrees c0 m0 mf) a))
  (let-match many (finish c0 m0 mf (Cons _ c0 (Nil _)) m0 (TNil _ m0) (runs-star m0 mf c0 (Nil _) spec)) (Halted _ _ r d)
    ((Stuck _ _) (AgreeStuck _ _ _)))
  (let-match erased (runs-fn m0 r mf c0 d spec) (Refl _ _))
  (AgreeHalted _ _ _ r))
