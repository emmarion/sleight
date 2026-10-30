; Every hypermap has a genus, and the derived hypermaps of hypermap.v (permN, permF, dual) keep it.

(def-fns _ $ (erased add-assoc : (erased (Nat) a b c ab abc) (subterm erased (Add a b ab) p) (erased (Add ab c abc) q) ->
    (erased (Nat) bc) (erased (Add b c bc) r) (erased (Add a bc abc) s))
  (let-match erased p (AddSucc a1 _ ab1 p1) ((AddZero _) (values abc q (AddZero abc))))
  (let-match erased q (AddSucc _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (add-assoc a1 b c ab1 abc1 p1 q1))
  (values bc r (AddSucc a1 bc abc1 s)))

(def-fns _ $ (erased add-assoc-inv : (erased (Nat) a b c bc abc) (erased (Add b c bc) p) (subterm erased (Add a bc abc) q) ->
    (erased (Nat) ab) (erased (Add a b ab) r) (erased (Add ab c abc) s))
  (let-match erased q (AddSucc a1 _ abc1 q1) ((AddZero _) (values b (AddZero b) p)))
  (let ((erased ab) (erased r) (erased s)) (add-assoc-inv a1 b c bc abc1 p q1))
  (values (Succ ab) (AddSucc a1 b ab r) (AddSucc ab c abc1 s)))

(def-fns _ $ (erased es-rot : (erased (Nat) kc d a b c g) (erased (EulerSum kc d a b c g) es) -> (erased (EulerSum kc d b c a g) r))
  (let-match erased es (MkEulerSum _ _ _ _ _ _ c2 lhs s1 rhs g2 dc al a1 ar dg ag))
  (let ((erased bc) (erased p) (erased q)) (add-assoc a b c s1 rhs a1 ar))
  (MkEulerSum kc d b c a g c2 lhs bc rhs g2 dc al p (add-comm a bc rhs q) dg ag))

(def-fns _ $ (erased es-swap : (erased (Nat) kc d a b c g) (erased (EulerSum kc d a b c g) es) -> (erased (EulerSum kc d a c b g) r))
  (let-match erased es (MkEulerSum _ _ _ _ _ _ c2 lhs s1 rhs g2 dc al a1 ar dg ag))
  (let ((erased bc) (erased p) (erased q)) (add-assoc a b c s1 rhs a1 ar))
  (let ((erased ac) (erased p2) (erased q2)) (add-assoc-inv a c b bc rhs (add-comm b c bc p) q))
  (MkEulerSum kc d a c b g c2 lhs ac rhs g2 dc al p2 q2 dg ag))

(def-fns _ $ (erased genus-parts : (erased (Nat) d gen) (erased (List (Nat)) e n f) (erased (Genus d e n f gen) p)
    -> (erased (Nat) kc ke kn kf) (erased (List (Bond)) g) (erased (Orbits d e ke) oe) (erased (Orbits d n kn) on) (erased (Orbits d f kf) of)
    (erased (Glink d e n f g) gl) (erased (Classes g d kc) cc) (erased (EulerSum kc d ke kn kf gen) es))
  (let-match erased p (MkGenus _ _ ke kn kf kc c2 lhs s1 rhs g2 _ _ _ g oe on of gl cc dc al a1 ar dg ag))
  (values kc ke kn kf g oe on of gl cc (MkEulerSum kc d ke kn kf gen c2 lhs s1 rhs g2 dc al a1 ar dg ag)))

(def-fns _ $ (erased genus-make : (erased (Nat) d gen kc ke kn kf) (erased (List (Nat)) e n f) (erased (List (Bond)) g)
    (erased (Orbits d e ke) oe) (erased (Orbits d n kn) on) (erased (Orbits d f kf) of) (erased (Glink d e n f g) gl) (erased (Classes g d kc) cc)
    (erased (EulerSum kc d ke kn kf gen) es) -> (erased (Genus d e n f gen) r))
  (let-match erased es (MkEulerSum _ _ _ _ _ _ c2 lhs s1 rhs g2 dc al a1 ar dg ag))
  (MkGenus d gen ke kn kf kc c2 lhs s1 rhs g2 e n f g oe on of gl cc dc al a1 ar dg ag))

(def-fns _ $ (erased glink-spans : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) ge gn gf g) (erased (Glink d e n f g) gl)
    (erased (Graph d e ge) gre) (erased (Graph d n gn) grn) (erased (Graph d f gf) grf)
    -> (erased (Spans g ge) se) (erased (Spans g gn) sn) (erased (Spans g gf) sf))
  (let-match erased gl (MkGlink _ _ _ _ ge2 gn2 gf2 gnf _ pe pn pf c1 c2))
  (let-match erased (graph-fn d e ge ge2 gre pe) (Refl _ _))
  (let-match erased (graph-fn d n gn gn2 grn pn) (Refl _ _))
  (let-match erased (graph-fn d f gf gf2 grf pf) (Refl _ _))
  (values (spans-lift-l ge gnf g ge (spans-self ge) c2) (spans-lift-r ge gnf g gn (spans-lift-l gn gf gnf gn (spans-self gn) c1) c2)
    (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2)))

(def-fns _ $ (erased glink-to : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) g h ge gn gf) (erased (Glink d e n f g) gl)
    (erased (Graph d e ge) gre) (erased (Graph d n gn) grn) (erased (Graph d f gf) grf) (erased (Spans h ge) se) (erased (Spans h gn) sn)
    (erased (Spans h gf) sf) -> (erased (Spans h g) r))
  (let-match erased gl (MkGlink _ _ _ _ ge2 gn2 gf2 gnf _ pe pn pf c1 c2))
  (let-match erased (graph-fn d e ge ge2 gre pe) (Refl _ _))
  (let-match erased (graph-fn d n gn gn2 grn pn) (Refl _ _))
  (let-match erased (graph-fn d f gf gf2 grf pf) (Refl _ _))
  (spans-cat h ge gnf g c2 se (spans-cat h gn gf gnf c1 sn sf)))

(def-fns _ $ (erased glink-below : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) g) (erased (Hypermap d e n f) h)
    (erased (Glink d e n f g) gl) -> (erased (Below g d) r))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf gnf _ pe pn pf c1 c2))
  (let ((erased nfe) (erased pme)) (hyper-perm d e n f h))
  (let ((erased nfn) (erased pmn)) (hyper-perm d n f e (hyper-rot d e n f h)))
  (let ((erased nfp) (erased pmf)) (hyper-perm d f e n (hyper-rot d n f e (hyper-rot d e n f h))))
  (below-cat ge gnf g d c2 (graph-below d e nfe ge (graph-fun d e ge pe) pme)
    (below-cat gn gf gnf d c1 (graph-below d n nfn gn (graph-fun d n gn pn) pmn) (graph-below d f nfp gf (graph-fun d f gf pf) pmf))))

(def-fns _ $ (erased glink-classes : (erased (Nat) d k) (erased (List (Nat)) e n f e2 n2 f2) (erased (List (Bond)) g g2) (erased (Hypermap d e2 n2 f2) h2)
    (erased (Glink d e2 n2 f2 g2) gl2) (erased (Classes g d k) cs) (erased (Spans g2 g) s1) (erased (Spans g g2) s2) -> (erased (Classes g2 d k) r))
  (classes-equiv g g2 d k cs s1 s2 (glink-below d e2 n2 f2 g2 h2 gl2)))

(def-fns _ $ (erased glink-exists : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) ge gn gf) (erased (Graph d e ge) gre)
    (erased (Graph d n gn) grn) (erased (Graph d f gf) grf) -> (erased (List (Bond)) g) (erased (Glink d e n f g) gl))
  (let ((erased gnf) (erased c1)) (cat-exists gn gf))
  (let ((erased g) (erased c2)) (cat-exists ge gnf))
  (values g (MkGlink d e n f ge gn gf gnf g gre grn grf c1 c2)))

(def-fns _ $ (erased hyper-core : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    -> (erased (List (Nat)) nf ni fi) (erased (Respects n f nf) rnf) (erased (Perm d e nf) pe) (erased (Perm d n ni) pn) (erased (Perm d f fi) pf))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen _ cnf inf))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased ni) (erased pn)) (hyper-perm d n f e (hyper-rot d e n f h)))
  (let ((erased fi) (erased pf)) (hyper-perm d f e n (hyper-rot d n f e (hyper-rot d e n f h))))
  (values nf ni fi cnf (MkPerm d e nf ids io le
    (respects-assoc e f n fe nf ids d cfe ke cnf (respects-length-inv e nf ids d inf (iota-length d ids io)) lf) inf) pn pf))

(def-fns _ $ (erased core-genus : (erased (Nat) d kx kn kf kc gen) (erased (List (Nat)) e n f nf ni fi) (erased (List (Bond)) gn gf g)
    (erased (Perm d e nf) pe) (erased (Respects n f nf) rnf) (erased (Perm d n ni) pn) (erased (Perm d f fi) pf)
    (erased (Orbits d nf kx) ox) (erased (Orbits d n kn) on) (erased (Orbits d f kf) of) (erased (Graph d n gn) grn) (erased (Graph d f gf) grf)
    (erased (Cat gn gf g) cg) (erased (Classes g d kc) cs) (erased (EulerSum kc d kx kn kf gen) es) -> (erased (Genus d e n f gen) r))
  (let ((erased ge) (erased gre)) (perm-graph d e nf pe))
  (let ((erased gl0) (erased c2)) (cat-exists ge g))
  (let ((erased gl)) (MkGlink d e n f ge gn gf g gl0 gre grn grf cg c2))
  (let ((erased se) (erased sn) (erased sf)) (glink-spans d e n f ge gn gf gl0 gl gre grn grf))
  (genus-make d gen kc kx kn kf e n f gl0 (orbits-inv d kx nf e (perm-sym d e nf pe) ox) on of gl
    (classes-equiv g gl0 d kc cs (spans-cat gl0 gn gf g cg sn sf)
      (glink-to d e n f gl0 g ge gn gf gl gre grn grf
        (spans-edge d e n f nf ge gn gf g (graph-fun d e ge gre) pe rnf (perm-length d f fi pf) grn grf cg)
        (spans-lift-l gn gf g gn (spans-self gn) cg) (spans-lift-r gn gf g gf (spans-self gf) cg))
      (below-cat ge g gl0 d c2 (graph-below d e nf ge (graph-fun d e ge gre) pe)
        (below-cat gn gf g d cg (graph-below d n ni gn (graph-fun d n gn grn) pn) (graph-below d f fi gf (graph-fun d f gf grf) pf))))
    es))

(def-fns _ $ (erased genus-core : (erased (Nat) d gen) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f gen) p)
    -> (erased (List (Nat)) nf ni fi) (erased (Respects n f nf) rnf) (erased (Perm d e nf) pe) (erased (Perm d n ni) pn) (erased (Perm d f fi) pf)
    (erased (Nat) kx kn kf kc) (erased (Orbits d nf kx) ox) (erased (Orbits d n kn) on) (erased (Orbits d f kf) of)
    (erased (List (Bond)) gn gf g) (erased (Graph d n gn) grn) (erased (Graph d f gf) grf) (erased (Cat gn gf g) cg) (erased (Classes g d kc) cs)
    (erased (EulerSum kc d kx kn kf gen) es))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased kc) (erased ke) (erased kn) (erased kf) (erased gl0) (erased oe) (erased on) (erased of) (erased gl) (erased cc) (erased es))
    (genus-parts d gen e n f p))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf _ _ gre grn grf _ _))
  (let ((erased se) (erased sn) (erased sf)) (glink-spans d e n f ge gn gf gl0 gl gre grn grf))
  (let ((erased g) (erased cg)) (cat-exists gn gf))
  (values nf ni fi rnf pe pn pf ke kn kf kc (orbits-inv d ke e nf pe oe) on of gn gf g grn grf cg
    (classes-equiv gl0 g d kc cc
      (glink-to d e n f gl0 g ge gn gf gl gre grn grf
        (spans-edge d e n f nf ge gn gf g (graph-fun d e ge gre) pe rnf (perm-length d f fi pf) grn grf cg)
        (spans-lift-l gn gf g gn (spans-self gn) cg) (spans-lift-r gn gf g gf (spans-self gf) cg))
      (spans-cat gl0 gn gf g cg sn sf)
      (below-cat gn gf g d cg (graph-below d n ni gn (graph-fun d n gn grn) pn) (graph-below d f fi gf (graph-fun d f gf grf) pf)))
    es))

; Every hypermap has a genus: Euler_lhs = 2 genus + Euler_rhs (Gonthier's even_genusP).
(def-fns _ $ (erased even-genus : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (Nat) gen) (erased (Genus d e n f gen) r))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased kn) (erased on)) (orbits-exists d n ni pn))
  (let ((erased kf) (erased of)) (orbits-exists d f fi pf))
  (let ((erased kx) (erased ox)) (orbits-exists d nf e (perm-sym d e nf pe)))
  (let-match erased on (MkOrbits _ _ _ gn grn _))
  (let-match erased of (MkOrbits _ _ _ gf grf _))
  (let ((erased g) (erased cg)) (cat-exists gn gf))
  (let ((erased m) (erased am)) (sub d kf (orbits-bound d kf f of)))
  (let ((erased kc) (erased gen) (erased cs) (erased es)) (euler-core d kn kf kx n ni f fi nf gn gf g pn pf rnf on of ox grn grf cg m am))
  (values gen (core-genus d kx kn kf kc gen e n f nf ni fi gn gf g pe rnf pn pf ox on of grn grf cg cs es)))

; permN keeps the genus.
(def-fns _ $ (erased genus-rot : (erased (Nat) d gen) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f gen) p)
    -> (erased (Genus d n f e gen) r))
  (let ((erased kc) (erased ke) (erased kn) (erased kf) (erased g) (erased oe) (erased on) (erased of) (erased gl) (erased cc) (erased es))
    (genus-parts d gen e n f p))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf _ _ pe pn pf _ _))
  (let ((erased g2) (erased gl2)) (glink-exists d n f e gn gf ge pn pf pe))
  (let ((erased se) (erased sn) (erased sf)) (glink-spans d e n f ge gn gf g gl pe pn pf))
  (let ((erased tn) (erased tf) (erased te)) (glink-spans d n f e gn gf ge g2 gl2 pn pf pe))
  (genus-make d gen kc kn kf ke n f e g2 on of oe gl2
    (glink-classes d kc e n f n f e g g2 (hyper-rot d e n f h) gl2 cc (glink-to d e n f g g2 ge gn gf gl pe pn pf te tn tf)
      (glink-to d n f e g2 g gn gf ge gl2 pn pf pe sn sf se))
    (es-rot kc d ke kn kf gen es)))

; permF is permN applied twice.
(def-fns _ $ (erased genus-rot2 : (erased (Nat) d gen) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f gen) p)
    -> (erased (Hypermap d f e n) h2) (erased (Genus d f e n gen) r))
  (let ((erased h1)) (hyper-rot d e n f h))
  (values (hyper-rot d n f e h1) (genus-rot d gen n f e h1 (genus-rot d gen e n f h p))))

; The dual: e, n and f inverted, with node and face exchanged. Its permutations are the composites n . f, e . n and f . e.
(def-fns _ $ (erased hyper-dual : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    -> (erased (List (Nat)) ei fi ni) (erased (Hypermap d ei fi ni) h2) (erased (Perm d e ei) pe) (erased (Perm d f fi) pf) (erased (Perm d n ni) pn))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased lfe)) (respects-length f e fe d cfe le))
  (let ((erased len)) (respects-length e n en d cen ln))
  (let ((erased lnf)) (respects-length n f nf d cnf lf))
  (let ((erased ke2)) (respects-assoc f n e nf en ids d cnf kf cen len ln))
  (let ((erased kn2)) (respects-assoc n e f en fe ids d cen kn cfe lfe le))
  (let ((erased kf2)) (respects-assoc e f n fe nf ids d cfe ke cnf lnf lf))
  (values nf en fe
    (MkHypermap d nf en fe ids f n e io (respects-assoc nf e f ids fe f d kf (respects-id-right d ids f io lf) cfe lfe le) ke2
      (respects-assoc en f n ids nf n d kn (respects-id-right d ids n io ln) cnf lnf lf) kn2
      (respects-assoc fe n e ids en e d ke (respects-id-right d ids e io le) cen len ln) kf2)
    (MkPerm d e nf ids io le kf2 kf) (MkPerm d f en ids io lf ke2 kn) (MkPerm d n fe ids io ln kn2 ke)))

(def-fns _ $ (erased spans-to-inv : (erased (Nat) d) (erased (List (Nat)) p q) (erased (List (Bond)) h gp gq) (erased (Spans h gp) sh)
    (erased (Perm d p q) pm) (erased (Graph d p gp) grp) (erased (Graph d q gq) grq) -> (erased (Spans h gq) r))
  (spans-trans h gp gq (spans-inv d p q gp gq (graph-fun d q gq grq) (perm-sym d p q pm) grp) sh))

; The dual keeps the genus.
(def-fns _ $ (erased genus-dual : (erased (Nat) d gen) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f gen) p)
    -> (erased (List (Nat)) ei fi ni) (erased (Hypermap d ei fi ni) h2) (erased (Perm d e ei) pe) (erased (Perm d f fi) pf) (erased (Perm d n ni) pn)
    (erased (Genus d ei fi ni gen) r))
  (let ((erased kc) (erased ke) (erased kn) (erased kf) (erased g) (erased oe) (erased on) (erased of) (erased gl) (erased cc) (erased es))
    (genus-parts d gen e n f p))
  (let ((erased ei) (erased fi) (erased ni) (erased h2) (erased pe) (erased pf) (erased pn)) (hyper-dual d e n f h))
  (let-match erased gl (MkGlink _ _ _ _ ge gn gf _ _ gre grn grf _ _))
  (let ((erased gei) (erased grei)) (perm-graph d ei e (perm-sym d e ei pe)))
  (let ((erased gfi) (erased grfi)) (perm-graph d fi f (perm-sym d f fi pf)))
  (let ((erased gni) (erased grni)) (perm-graph d ni n (perm-sym d n ni pn)))
  (let ((erased g2) (erased gl2)) (glink-exists d ei fi ni gei gfi gni grei grfi grni))
  (let ((erased se) (erased sn) (erased sf)) (glink-spans d e n f ge gn gf g gl gre grn grf))
  (let ((erased te) (erased tf) (erased tn)) (glink-spans d ei fi ni gei gfi gni g2 gl2 grei grfi grni))
  (let ((erased qe)) (perm-sym d e ei pe))
  (let ((erased qf)) (perm-sym d f fi pf))
  (let ((erased qn)) (perm-sym d n ni pn))
  (values ei fi ni h2 pe pf pn
    (genus-make d gen kc ke kf kn ei fi ni g2 (orbits-inv d ke e ei pe oe) (orbits-inv d kf f fi pf of) (orbits-inv d kn n ni pn on) gl2
      (glink-classes d kc e n f ei fi ni g g2 h2 gl2 cc
        (glink-to d e n f g g2 ge gn gf gl gre grn grf (spans-to-inv d ei e g2 gei ge te qe grei gre) (spans-to-inv d ni n g2 gni gn tn qn grni grn)
          (spans-to-inv d fi f g2 gfi gf tf qf grfi grf))
        (glink-to d ei fi ni g2 g gei gfi gni gl2 grei grfi grni (spans-to-inv d e ei g ge gei se pe gre grei) (spans-to-inv d f fi g gf gfi sf pf grf grfi)
          (spans-to-inv d n ni g gn gni sn pn grn grni)))
      (es-swap kc d ke kn kf gen es))))
