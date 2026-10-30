; slc std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/red/red.sl fourcolor/red/configs.sl fourcolor/red/{color,ctree,gtree,grestrict,crestrict,kempe,bridge,init,check,sanity-c}.sl
(let-match many (cf004) (MkConfig sym4 _ p4))
(def-fns _ $ (many c1 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf002) (Nil _))) b)
(def-fns _ $ (many c2 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf004) (Nil _))) b)
(def-fns _ $ (many c3 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (cf001) (Nil _))) b)
(def-fns _ $ (many c4 : -> (many (Bool) r)) (let ((many b) (many _)) (check-reducible-c (MkConfig sym4 (Nil _) p4) (Nil _))) b)

(let ((many r1) (many r2) (many r3) (many r4)) (native-compute c1 c2 c3 c4))
(comptime-match many r1 (BTrue))
(comptime-match many r2 (BTrue))
(comptime-match many r3 (BTrue))
(comptime-match many r4 (BFalse))
