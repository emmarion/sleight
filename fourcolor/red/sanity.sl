(let ((many pentagon)) (Cons _ (SH) $ Cons _ (SR 4) $ Cons _ (SY) $ Cons _ (SY) $ Cons _ (SY) $ Nil _))
(let-match many (cf004) (MkConfig sym4 _ p4))

(def-fns _ $ (many pent : (many (List (Nat)) c) -> (many (Bool) r))
  (check-reducible (MkConfig (BFalse) c pentagon)))

(def-fns _ $ (many cf004-with : (many (List (Nat)) c) -> (many (Bool) r))
  (check-reducible (MkConfig sym4 c p4)))

(def-fns _ $ (many d-reducible : (many (Config) cf) -> (many (Bool) r))
  (let-match many cf (MkConfig _ _ cp))
  (ct-empty (kempe-tree cp)))

(def-fns _ $ (many s1 : -> (many (Bool) r))
  (orb (pent $ Cons _ 0 $ Nil _) $ orb (pent $ Cons _ 1 $ Nil _) $ orb (pent $ Cons _ 2 $ Nil _) $
    orb (pent $ Cons _ 3 $ Nil _) $ orb (pent $ Cons _ 4 $ Nil _) $ orb (pent $ Cons _ 0 $ Cons _ 2 $ Nil _) (pent $ Cons _ 1 $ Cons _ 3 $ Nil _)))
(def-fns _ $ (many s2 : -> (many (Bool) r)) (check-reducible (cf004)))
(def-fns _ $ (many s3 : -> (many (Bool) r))
  (orb (cf004-with $ Cons _ 1 $ Nil _) $ orb (cf004-with $ Cons _ 1 $ Cons _ 2 $ Cons _ 12 $ Nil _) (cf004-with $ Cons _ 1 $ Cons _ 2 $ Cons _ 12 $ Cons _ 14 $ Nil _)))
(def-fns _ $ (many s4 : -> (many (Bool) r)) (d-reducible (cf004)))
(def-fns _ $ (many s5 : -> (many (Bool) r)) (andb (d-reducible (cf001)) (check-reducible (cf001))))
(def-fns _ $ (many s6 : -> (many (Bool) r)) (check-reducible $ MkConfig sym4 (Nil _) p4))

(let ((many r1) (many r2) (many r3) (many r4) (many r5) (many r6)) (native-compute s1 s2 s3 s4 s5 s6))
(comptime-match many r1 (BFalse))
(comptime-match many r2 (BTrue))
(comptime-match many r3 (BFalse))
(comptime-match many r4 (BFalse))
(comptime-match many r5 (BTrue))
(comptime-match many r6 (BFalse))
