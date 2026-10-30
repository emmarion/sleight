; Load after check.sl, in the order of PLAN.md.
(let-match many (cf004) (MkConfig sym4 _ p4))
(def-fns _ $ (many c1 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf002) (Nil _))) (match many b _ ((RCYes _ _ _ _ _ _ _ _ _ _) (BTrue)) ((RCNo _) (BFalse))))
(def-fns _ $ (many c2 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf004) (Nil _))) (match many b _ ((RCYes _ _ _ _ _ _ _ _ _ _) (BTrue)) ((RCNo _) (BFalse))))
(def-fns _ $ (many c3 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf001) (Nil _))) (match many b _ ((RCYes _ _ _ _ _ _ _ _ _ _) (BTrue)) ((RCNo _) (BFalse))))
(def-fns _ $ (many c4 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (MkConfig sym4 (Nil _) p4) (Nil _))) (match many b _ ((RCYes _ _ _ _ _ _ _ _ _ _) (BTrue)) ((RCNo _) (BFalse))))

(let ((many r1) (many r2) (many r3) (many r4)) (native-compute c1 c2 c3 c4))
(comptime-match many r1 (BTrue))
(comptime-match many r2 (BTrue))
(comptime-match many r3 (BTrue))
(comptime-match many r4 (BFalse))
