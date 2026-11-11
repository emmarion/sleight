(def-fns _ $ (erased point-kit : (erased (Level) M N) -> (erased (Level) P) (erased (PointKit M N P) k))
  (let ((erased K1) (erased _) (erased creal-appart-eq-compat) (erased creal-appart-irrefl) (erased _) (erased K2) (erased _)) (creal-eq-kit M N))
  (def-fns _
    ((erased compat : (erased (RPoint M) x y z) (erased (RPointEq M N x y) a) (erased (RPointApart M y z) b) -> (erased (RPointApart M x z) r))
      (let-match erased a (MkRPointEq _ _ px py qx qy xp yp xq yq ex ey))
      (match erased b _
        ((RApartX _ _ _ rx ry _ _ xr yr d) (RApartX M px py rx ry xp yp xr yr (creal-appart-eq-compat px qx rx xp xq xr ex d)))
        ((RApartY _ _ _ rx ry _ _ xr yr d) (RApartY M px py rx ry xp yp xr yr (creal-appart-eq-compat py qy ry yp yq yr ey d)))))
    ((erased irrefl : (erased (RPoint M) x) (erased (RPointApart M x x) a) -> (erased (False) f))
      (match erased a _
        ((RApartX _ px _ _ _ xp _ _ _ d) (creal-appart-irrefl px xp d))
        ((RApartY _ _ py _ _ _ yp _ _ d) (creal-appart-irrefl py yp d)))))
  (values (level-of compat) (MkPointKit M N (level-of compat) compat irrefl)))
