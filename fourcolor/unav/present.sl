(def-adts $ (Script : -> Type)
  enum
  (many SSplit : (many (Loc) i) (many (Nat) j k) (many (Bool) lo lab) (many (Script) l r) -> (Script))
  (many SRed : -> (Script))
  (many SHub : (many (List (Hc)) hc) -> (Script))
  (many SSim : (many (Nat) idx) (many (Bool) mir) (many (Nat) n) -> (Script)))

(def-fns _ $ (many nth-part : (subterm many (Nat) i) (many (List (List (Sub))) xs) -> (many (List (Sub)) x))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let-match many i (Succ i1) ((Zero) x))
  (tail $ nth-part i1 rest))

(def-fns _ $ (many check : (many (Ctx) c) (many (List (List (Sub))) env) (many (List (Sub)) p0 p) (subterm many (Script) s) -> (many (Bool) b))
  (match many s _
    ((SSplit i j k lo lab l r)
      (let ((many pl) (many pr)) (values (split-part i j k lo p) (split-part i j k (negb lo) p)))
      (let ((many p0l)) (bif _ (good-split i j k p0) (split-part i j k lo p0) pl))
      (and (good-split i j k p) (notail $ check c env p0l pl l) (tail $ check c (bif _ lab (Cons _ p0l env) env) p0 pr r)))
    ((SRed) (redp c p))
    ((SHub hc) (and (hubcap-cover c hc) (hubcap-fit c p hc)))
    ((SSim idx mir n)
      (let ((many ps)) (nth-part idx env))
      (let ((many p2)) (rot _ n (bif _ mir (mirror-part p) p)))
      (andb (nat-eqb (size _ ps) (size _ p2)) (rel-sub (cmp-part p2 ps))))))

(def-fns _ $ (many check-arity : (many (Qzt) qt) (many (List (List (Sub))) base) (many (Nat) n) (many (Script) s) -> (many (Bool) b))
  (let ((many p)) (pcons- n))
  (check (make-ctx n qt base) (Nil _) p p s))

(def-fns _ $ (many concat-cfs : (subterm many (List (List (Config))) css) -> (many (List (Config)) cs))
  (let-match many css (Cons _ c rest) ((Nil _) (Nil _)))
  (cat _ c $ notail $ concat-cfs rest))

(def-fns _ $ (many the-quiz-tree : -> (many (Qzt) qt))
  (cfquiz-tree-rec (qzt-empty) (concat-cfs (config-chunks))))

(def-fns _ $ (many check-cap1 : (many (Qzt) qt) (many (List (List (Sub))) base) (subterm many (Nat) k) -> (many (Bool) b))
  (let-match many k (Succ k1) ((Zero) (BTrue)))
  (let ((many n)) (nat-add 5 k1))
  (and (check-dbound1 (make-ctx n qt base) (pcons- n) 5) (tail $ check-cap1 qt base k1)))
