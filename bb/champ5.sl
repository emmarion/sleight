(let ((many champ)) (Cons _ (Mov (BTrue) (DR) 1) $ Cons _ (Mov (BTrue) (DL) 2) $ Cons _ (Mov (BTrue) (DR) 2) $ Cons _ (Mov (BTrue) (DR) 1) $
  Cons _ (Mov (BTrue) (DR) 3) $ Cons _ (Mov (BFalse) (DL) 4) $ Cons _ (Mov (BTrue) (DL) 0) $ Cons _ (Mov (BTrue) (DL) 3) $
  Cons _ (Hlt) $ Cons _ (Mov (BFalse) (DL) 0) $ Nil (Tr)))
(let ((many cw0)) (rows-check 5 5 champ))
(comptime-match many cw0 (ROk _ cw))

(def-fns _ $ (many champ-run : -> (many (Res (HaltsAt champ (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) 47176870)) r))
  (let ((many cp) (erased cdl)) (defs champ))
  (let-match many (psim cp 47176871 (Zero) (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)) (PRNil cp _)) (PSHalt _ ct cq cl cr chh cpr cpl) (else (RFail _)))
  (let-match many (nat-eq (Succ ct) 47176870) (Equal _ _ _) (else (RFail _)))
  (let ((erased cex)) (defl-ext champ cp cdl))
  (ROk _ (run-add champ _ (MkConf cq cl chh cr) ct (Succ (Zero)) (Succ ct) (prun-run cp champ cex _ _ ct cpr)
    (HStop champ cq cl cr chh (ext-look cp champ cq chh _ cex cpl)) (add-succ-right ct (Zero) ct (add-zero-right ct)))))
(let ((many champ-res)) (native-compute champ-run))
(comptime-match many champ-res (ROk _ ch))
