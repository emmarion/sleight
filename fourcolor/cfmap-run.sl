; Builds the map of each of the 633 configurations with cpmap-c under native-compute, and checks its ring has red.sl's
; cprsize darts. Load after cfmap.sl, red/red.sl, cpmap.sl and red/configs.sl.

(def-fns _ $ (many cf-ok : (many (Config) cf) -> (many (Bool) b))
  (let-match many cf (MkConfig _ _ cp))
  (let-match many (noa-dec cp) (NoAYes _ na) ((NoANo _) (BFalse)))
  (let ((many d) (many e) (many f) (many r) (erased c)) (cpmap-c cp na))
  (nat-eqb (size _ r) (cprsize cp)))

(def-fns _ $ (many all-ok : (subterm many (List (Config)) cfs) -> (many (Bool) b))
  (let-match many cfs (Cons _ cf rest) ((Nil _) (BTrue)))
  (match many (cf-ok cf) _ ((BTrue) (tail $ all-ok rest)) ((BFalse) (BFalse))))

(def-fns _ $ (many chunks-ok : (subterm many (List (List (Config))) css) -> (many (Bool) b))
  (let-match many css (Cons _ cs rest) ((Nil _) (BTrue)))
  (match many (all-ok cs) _ ((BTrue) (tail $ chunks-ok rest)) ((BFalse) (BFalse))))

(def-fns _ $ (many j : -> (many (Bool) r)) (chunks-ok (config-chunks)))
(let ((many r)) (native-compute j))
(comptime-match many r (BTrue))
