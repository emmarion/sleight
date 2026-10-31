; The certified presentation walks of arities m to hi - 1 and the unavoidability statement they give with cap.sl's
; checks: on a plain cubic pentagonal map every dart of positive dscore has an obligation of the walk of its arity, or a
; cap obligation when the arity is 12 or more, fitting exactly at some dart. Load after cap.sl.

; wobl lists the walks' obligations, one list per arity from m.
(def-adts $ (WalkL : ((List (List (Sub))) drs) ((List (List (List (Sub)))) wobl) ((Nat) m hi) -> Type)
  enum
  (many WLNil : (erased (List (List (Sub))) drs) (erased (Nat) m) -> (WalkL drs (Nil (List (List (Sub)))) m m))
  (many WLCons : (erased (List (List (Sub))) drs rs rt out) (erased (List (List (List (Sub)))) wobl) (erased (Nat) m hi) (erased (List (Sub)) p)
      (erased (OfSize m drs rs) sz) (erased (Tgt m drs rt) tg) (erased (Repeat (Sub) m sub59 p) rp) (erased (Pres m rt rs (Nil (List (Sub))) p out) pr)
      (erased (WalkL drs wobl (Succ m) hi) rest) -> (WalkL drs (Cons (List (List (Sub))) out wobl) m hi)))

(def-fns _ $ (many walk-c : (many (List (List (Sub))) drs) (many (Nat) m hi) (subterm many (List (Script)) ss)
    -> (many (Bool) ok) (many (List (List (List (Sub)))) wobl) (erased (IfT ok (WalkL drs wobl m hi)) w))
  (let-match many (nat-eq m hi) (Unequal _ _ _ _ _) ((Equal _ _ _) (values (BTrue) (Nil _) (IfY _ (WLNil drs m)))))
  (let-match many ss (Cons _ s ss1) ((Nil _) (values (BFalse) (Nil _) (IfF _))))
  (let ((many rs) (erased sz)) (of-size-c m drs))
  (let ((many rt) (erased tg)) (pick-target-c m drs))
  (let ((many p) (erased rp)) (nseq-c _ m sub59))
  (let ((many ok1) (many out) (erased w1))
    (check2-c m rt rs (Nil (List (Sub))) (Nil _) (Nil _) (EENil m rt rs (Nil (List (Sub))) (Nil _)) p p p p (FRoot m rt rs (Nil (List (Sub))) (Nil _) p) (FRoot m rt rs (Nil (List (Sub))) (Nil _) p) s))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) (Nil _) (IfF _))))
  (let-match erased w1 (IfY _ w3))
  (let-match erased w3 (MkW3 _ _ _ _ _ _ _ _ pr _ _))
  (let ((many ok) (many wobl) (erased w)) (notail $ walk-c drs (Succ m) hi ss1))
  (values ok (Cons _ out wobl) (match erased w _ ((IfY _ wl) (IfY _ (WLCons drs rs rt out wobl m hi p sz tg rp pr wl))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased walk-look : (erased (List (List (Sub))) drs) (erased (List (List (List (Sub)))) wobl) (erased (Nat) a m hi)
    (subterm erased (WalkL drs wobl m hi) wl) (erased (Lt m (Succ a)) lo) (erased (Lt a hi) up)
    -> (erased (Nat) i) (erased (List (List (Sub))) rs rt out) (erased (List (Sub)) p) (erased (Nth (List (List (Sub))) wobl i out) pn) (erased (Add i m a) ad)
    (erased (OfSize a drs rs) sz) (erased (Tgt a drs rt) tg) (erased (Repeat (Sub) a sub59 p) rp) (erased (Pres a rt rs (Nil (List (Sub))) p out) pr))
  (let-match erased wl (WLCons _ rs rt out wobl1 _ _ p sz tg rp pr rest) (absurd (WLNil _ _) (lt-le-absurd a m up lo)))
  (let-match erased (nat-eq a m) (Unequal _ _ _ _ ap)
    ((Equal _ _ _) (values (Zero) rs rt out p (NthHere _ out wobl1) (AddZero a) sz tg rp pr)))
  (let-match erased ap (ApGt _ _ _ _ l)
    (absurd (ApLt _ _ _ _ l) (lt-le-absurd a m l lo)))
  (let ((erased i) (erased rs1) (erased rt1) (erased out1) (erased p1) (erased pn) (erased ad) (erased sz1) (erased tg1) (erased rp1) (erased pr1))
    (walk-look drs wobl1 a (Succ m) hi rest (LtS m a l) up))
  (values (Succ i) rs1 rt1 out1 p1 (NthThere _ out wobl1 i out1 pn) (add-shift i m a ad) sz1 tg1 rp1 pr1))

; Which obligations fit exactly for a dart x of positive dscore: those of the walk of its arity a = 5 + i, or the cap ones.
(def-adts $ (UnavAt : ((Nat) d) ((List (Nat)) e f ks) ((List (List (List (Sub)))) wobl) ((List (List (Sub))) cobl) ((Nat) x) -> Type)
  enum
  (many UWalk : (erased (Nat) d x a i) (erased (List (Nat)) e f ks) (erased (List (List (List (Sub)))) wobl) (erased (List (List (Sub))) cobl obl)
      (erased (Nth (Nat) ks x a) pa) (erased (Add i 5 a) ad) (erased (Nth (List (List (Sub))) wobl i obl) pn) (erased (MapHit d e f ks obl) h)
      -> (UnavAt d e f ks wobl cobl x))
  (many UCap : (erased (Nat) d x a) (erased (List (Nat)) e f ks) (erased (List (List (List (Sub)))) wobl) (erased (List (List (Sub))) cobl)
      (erased (Nth (Nat) ks x a) pa) (erased (Lt 11 a) l11) (erased (MapHit d e f ks cobl) h) -> (UnavAt d e f ks wobl cobl x)))

(def-fns _ $ (erased unav-dart : (erased (Nat) d x pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) drs acc cobl)
    (erased (List (List (List (Sub)))) wobl) (erased (Small drs) sm) (erased (WalkL drs wobl 5 12) wl) (erased (CapL drs acc cobl 5 9) cl)
    (erased (Geo d e n f ks) g) (erased (Lt x d) lx) (erased (DScore d e n f ks drs x pos neg) dsc) (erased (Lt neg pos) lt)
    -> (erased (UnavAt d e f ks wobl cobl x) r))
  (let-match erased g (MkGeo _ _ _ _ _ _ _ _ ol ab))
  (let ((erased a) (erased pa) (erased _)) (arity-at d x f ks ol lx))
  (match erased (le-dec 12 a) _
    ((LeY _ _ l12)
      (let-match erased l12 (LtS _ _ l11))
      (UCap d x a e f ks wobl cobl pa l11 (cap-sound d x a pos neg e n f ks drs acc cobl g lx dsc lt pa l11 sm cl)))
    ((LeN _ _ la)
      (let ((erased i) (erased rs) (erased rt) (erased out) (erased p) (erased pn) (erased ad) (erased sz) (erased tg) (erased rp) (erased pr))
        (walk-look drs wobl a 5 12 wl (LtS 4 a (above-nth ks 4 x a ab pa)) la))
      (let ((erased ws) (erased iw)) (iota-exists d))
      (let ((erased os) (erased ob)) (obs-exists d x e n f ks g a lx))
      (let ((erased xa)) (MkExactAt e f ks x a os p pa ob (root-exact d x a e n f ks os p g ob rp)))
      (UWalk d x a i e f ks wobl cobl out pa ad pn
        (preshit-map d e n f ks drs out (pres-sound d a e n f ks ws drs rt rs (Nil (List (Sub))) g sz iw (tgt-all d d a e n f ks ws drs rt g tg iw (lt-succ d)) x pos neg out p lx dsc lt xa pr))))))

; The statement for the rules drs: the certified walks and cap checks succeed with obligation lists wobl and cobl, some
; dart of a plain cubic connected pentagonal map of genus 0 has positive dscore, and on a plain cubic pentagonal map,
; for any rules and successful checks, each dart of positive dscore has its UnavAt.
(def-adts $ (Unav : ((List (List (Sub))) drs) -> Type)
  enum
  (many MkUnav : (erased (List (List (Sub))) drs cobl) (erased (List (List (List (Sub)))) wobl) (erased (Small drs) sm)
      (erased (WalkL drs wobl 5 12) wl) (erased (CapL drs (Nil (List (Sub))) cobl 5 9) cl) (erased (Level) lv1 lv2)
      (erased (Fn lv1 (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) rs) (erased (Geo d e n f ks) g)
          (erased (Connected d e n f) cc) (erased (Genus d e n f (Zero)) gen)
          -> (erased (Nat) x pos neg) (erased (Lt x d) lx) (erased (DScore d e n f ks rs x pos neg) dsc) (erased (Lt neg pos) lt)) somepos)
      (erased (Fn lv2 (erased (Nat) d x pos neg) (erased (List (Nat)) e n f ks) (erased (List (List (Sub))) rs acc cob)
          (erased (List (List (List (Sub)))) wob) (erased (Small rs) sm2) (erased (WalkL rs wob 5 12) wl2) (erased (CapL rs acc cob 5 9) cl2)
          (erased (Geo d e n f ks) g) (erased (Lt x d) lx) (erased (DScore d e n f ks rs x pos neg) dsc) (erased (Lt neg pos) lt)
          -> (erased (UnavAt d e f ks wob cob x) r)) every)
      -> (Unav drs)))

(def-adts $ (Checked : (Type P) -> Type)
  enum
  (many ChkYes : (erased Type P) (erased P p) -> (Checked P))
  (many ChkNo : (erased Type P) -> (Checked P)))
