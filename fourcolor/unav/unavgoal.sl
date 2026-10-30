; The unavoidability goal for the rules of data.sl. One compiled run (native-compute) does the certified walks and cap
; checks and then asks redpart of every obligation they return, answering Unav only when all of it passes. Load after
; unav.sl and data.sl.

(let ((many drs)) (symmetrize (base-drules)))

(goal erased (Unav drs))

(def-fns _ $ (many redp-list : (many (Qzt) qt) (subterm many (List (List (Sub))) obl) -> (many (Bool) b))
  (let-match many obl (Cons _ q rest) ((Nil _) (BTrue)))
  (and (redpart qt q) (tail $ redp-list qt rest)))

(def-fns _ $ (many redp-lists : (many (Qzt) qt) (subterm many (List (List (List (Sub)))) obls) -> (many (Bool) b))
  (let-match many obls (Cons _ obl rest) ((Nil _) (BTrue)))
  (and (redp-list qt obl) (tail $ redp-lists qt rest)))

(def-fns _ $ (many unav-run : -> (many (Checked (Unav drs)) r))
  (let ((many sok) (erased sw)) (small-c drs))
  (let-match many sok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many wok) (many wobl) (erased ww))
    (walk-c drs 5 12 (Cons _ (script5) $ Cons _ (script6) $ Cons _ (script7) $ Cons _ (script8) $ Cons _ (script9) $ Cons _ (script10) $
      Cons _ (script11) $ Nil _)))
  (let-match many wok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many cok) (many cobl) (erased cw)) (cap-c drs (Nil _) 5 9 4))
  (let-match many cok (BTrue) ((BFalse) (ChkNo _)))
  (let ((many qt)) (the-quiz-tree))
  (let-match many (and (redp-lists qt wobl) (redp-list qt cobl)) (BTrue) ((BFalse) (ChkNo _)))
  (let-match erased sw (IfY _ sm))
  (let-match erased ww (IfY _ wl))
  (let-match erased cw (IfY _ cl))
  (ChkYes _ (MkUnav drs cobl wobl sm wl cl (level-of posz-dscore) (level-of unav-dart) posz-dscore unav-dart)))

(let ((many res)) (native-compute unav-run))
(comptime-match many res (ChkYes _ u))
(qed u)
