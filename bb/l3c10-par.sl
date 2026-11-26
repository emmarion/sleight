(def-adts
  ((Rr : ((List (Tr)) m) ((Rq) e e2) -> Type)
    enum
    (many MkRr : (erased (List (Tr)) m) (erased (Rq) e e2) (erased (Conf) c) (erased (Dc e c) dc) (erased (Rch m c e2) ch) -> (Rr m e e2))))

(def-fns _ $ (erased rq-conf : (erased (Rq) e) -> (erased (Conf) c) (erased (Dc e c) dc))
  (let-match erased e (MkRq q L h R))
  (let ((erased l) (erased dl)) (den-ex L))
  (let ((erased r) (erased dr)) (den-ex R))
  (values (MkConf q l h r) (MkDc q L R h l r dl dr)))

(def-fns _ $ (erased rr-cat : (erased (List (Tr)) m) (erased (Conf) c0) (erased (Rq) e e2) (erased (Rch m c0 e) ch) (erased (Rr m e e2) rr)
    -> (erased (Rch m c0 e2) ch2))
  (let-match erased rr (MkRr _ _ _ c dc ch1))
  (let-match erased ch1 (MkRch _ _ a2 c2 _ t r dc2 z2))
  (rch-z m c0 c c a2 c2 e e2 t ch dc (cez-refl c) r dc2 (cez-sym c2 a2 z2)))

(def-fns _ $ (many rr-run : (many (Nat) n) (many (Rq) e e2) -> (many (Res (Rr l3 e e2)) r))
  (let ((erased c) (erased dc)) (rq-conf e))
  (let ((many _) (many f) (erased ch)) (c10-run2 c n e (MkRch l3 c c c e (Zero) (RNil l3 c) dc (cez-refl c))))
  (let-match many (rq-eq f e2) (ESome _ eq) ((ENone _) (RFail _)))
  (let-match erased eq (Refl _ _))
  (ROk _ (MkRr l3 e e2 c dc ch)))
