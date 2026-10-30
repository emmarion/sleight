; Rotating a chromogram with the trace it matches, after gram_neg, gram_flip and gram_rot of kempe.v. Load after bridge.sl.

; bs2 is bs with the bit x added at the bottom.
(def-adts $ (Bot : ((Bool) x) ((Bstack) bs bs2) -> Type)
  enum
  (many BotF : -> (Bot (BFalse) (BS0) (BP0 (BS0))))
  (many BotT : -> (Bot (BTrue) (BS0) (BP1 (BS0))))
  (many Bot0 : (erased (Bool) x) (erased (Bstack) bs bs2) (erased (Bot x bs bs2) p) -> (Bot x (BP0 bs) (BP0 bs2)))
  (many Bot1 : (erased (Bool) x) (erased (Bstack) bs bs2) (erased (Bot x bs bs2) p) -> (Bot x (BP1 bs) (BP1 bs2))))

; bs holds n bits.
(def-adts $ (Sz : ((Bstack) bs) ((Nat) n) -> Type)
  enum
  (many SzNil : -> (Sz (BS0) (Zero)))
  (many Sz0 : (erased (Bstack) bs) (erased (Nat) n) (erased (Sz bs n) p) -> (Sz (BP0 bs) (Succ n)))
  (many Sz1 : (erased (Bstack) bs) (erased (Nat) n) (erased (Sz bs n) p) -> (Sz (BP1 bs) (Succ n))))

; The symbol s takes n open chords to n2.
(def-adts $ (Step : ((Gsym) s) ((Nat) n n2) -> Type)
  enum
  (many StSkip : (erased (Nat) n) -> (Step (GSkip) n n))
  (many StPush : (erased (Nat) n) -> (Step (GPush) n (Succ n)))
  (many StPop0 : (erased (Nat) n) -> (Step (GPop0) (Succ n) n))
  (many StPop1 : (erased (Nat) n) -> (Step (GPop1) (Succ n) n)))

; From n open chords, w never closes more than it opens and ends with none open.
(def-adts $ (Dep : ((Nat) n) ((List (Gsym)) w) -> Type)
  enum
  (many DNil : -> (Dep (Zero) (Nil (Gsym))))
  (many DCons : (erased (Gsym) s) (erased (Nat) n n2) (erased (List (Gsym)) w) (erased (Step s n n2) st) (erased (Dep n2 w) d)
      -> (Dep n (Cons (Gsym) s w))))

; gram_neg_rec n w = w2.
(def-adts $ (Neg : ((Nat) n) ((List (Gsym)) w w2) -> Type)
  enum
  (many NgNil : (erased (Nat) n) -> (Neg n (Nil (Gsym)) (Nil (Gsym))))
  (many NgStep : (erased (Gsym) s) (erased (Nat) n n2) (erased (List (Gsym)) w w2) (erased (Step s n n2) st) (erased (Neg n2 w w2) p)
      -> (Neg n (Cons (Gsym) s w) (Cons (Gsym) s w2)))
  (many NgP0 : (erased (List (Gsym)) w) -> (Neg (Zero) (Cons (Gsym) (GPop0) w) (Cons (Gsym) (GPop1) w)))
  (many NgP1 : (erased (List (Gsym)) w) -> (Neg (Zero) (Cons (Gsym) (GPop1) w) (Cons (Gsym) (GPop0) w))))

; gram_flip_rec n w = w2.
(def-adts $ (Flip : ((Nat) n) ((List (Gsym)) w w2) -> Type)
  enum
  (many FlNil : (erased (Nat) n) -> (Flip n (Nil (Gsym)) (Cons (Gsym) (GPush) (Nil (Gsym)))))
  (many FlStep : (erased (Gsym) s) (erased (Nat) n n2) (erased (List (Gsym)) w w2) (erased (Step s n n2) st) (erased (Flip n2 w w2) p)
      -> (Flip n (Cons (Gsym) s w) (Cons (Gsym) s w2)))
  (many FlP0 : (erased (List (Gsym)) w w2) (erased (Neg (Zero) w w2) p) -> (Flip (Zero) (Cons (Gsym) (GPop0) w) (Cons (Gsym) (GPush) w2)))
  (many FlP1 : (erased (List (Gsym)) w) -> (Flip (Zero) (Cons (Gsym) (GPop1) w) (Cons (Gsym) (GPush) w))))

; gram_rot w = w1, for a w that starts a match from the empty stack.
(def-adts $ (GramRot : ((List (Gsym)) w w1) -> Type)
  enum
  (many GRSkip : (erased (List (Gsym)) w w1) (erased (Snoc (Gsym) w (GSkip) w1) s) -> (GramRot (Cons (Gsym) (GSkip) w) w1))
  (many GRPush : (erased (List (Gsym)) w w2 w1) (erased (Snoc (Gsym) w (GPop1) w2) s) (erased (Flip (Zero) w2 w1) f)
      -> (GramRot (Cons (Gsym) (GPush) w) w1)))

; S is sb with b and then c added at the bottom, b and c different.
(def-adts $ (Bot2 : ((Bstack) sb s) -> Type)
  enum
  (many MkBot2 : (erased (Bstack) sb a s) (erased (Bool) b c) (erased (Not b c) n) (erased (Bot b sb a) p) (erased (Bot c a s) q) -> (Bot2 sb s)))

(def-fns _ $ (erased absurd bot-ne : (erased (Bool) x) (erased (Bstack) bs) (erased (Bot x bs (BS0)) p) -> (erased (False) f))
  (match erased p _))

(def-fns _ $ (erased bot-exists : (erased (Bool) x) (subterm erased (Bstack) bs) -> (erased (Bstack) bs2) (erased (Bot x bs bs2) p))
  (match erased bs _
    ((BS0) (match erased x _ ((BFalse) (values (BP0 (BS0)) (BotF))) ((BTrue) (values (BP1 (BS0)) (BotT)))))
    ((BP0 b1) (let ((erased b2) (erased p)) (bot-exists x b1)) (values (BP0 b2) (Bot0 x b1 b2 p)))
    ((BP1 b1) (let ((erased b2) (erased p)) (bot-exists x b1)) (values (BP1 b2) (Bot1 x b1 b2 p)))))

(def-fns _ $ (erased bot-fn : (erased (Bool) x) (erased (Bstack) bs b2 b3) (subterm erased (Bot x bs b2) p) (erased (Bot x bs b3) q) -> (erased (Eq (Bstack) b2 b3) e))
  (match erased p _
    ((BotF) (let-match erased q (BotF)) (Refl _ b2))
    ((BotT) (let-match erased q (BotT)) (Refl _ b2))
    ((Bot0 _ b1 c1 p1) (let-match erased q (Bot0 _ _ c2 q1)) (let-match erased (bot-fn x b1 c1 c2 p1 q1) (Refl _ _)) (Refl _ b2))
    ((Bot1 _ b1 c1 p1) (let-match erased q (Bot1 _ _ c2 q1)) (let-match erased (bot-fn x b1 c1 c2 p1 q1) (Refl _ _)) (Refl _ b2))))

(def-fns _ $ (erased step-succ : (erased (Gsym) s) (erased (Nat) n n2) (erased (Step s n n2) st) -> (erased (Step s (Succ n) (Succ n2)) r))
  (match erased st _ ((StSkip _) (StSkip (Succ n))) ((StPush _) (StPush (Succ n))) ((StPop0 m) (StPop0 (Succ m))) ((StPop1 m) (StPop1 (Succ m)))))

(def-fns _ $ (erased sym-sz : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (Nat) n) (erased (Sym s bs e bs2) sy) (erased (Sz bs n) z)
    -> (erased (Nat) n2) (erased (Sz bs2 n2) z2) (erased (Step s n n2) st))
  (match erased sy _
    ((SSkip _) (values n z (StSkip n)))
    ((SPush2 _) (values (Succ n) (Sz0 bs n z) (StPush n)))
    ((SPush3 _) (values (Succ n) (Sz1 bs n z) (StPush n)))
    ((SPop02 _) (let-match erased z (Sz0 _ m z1)) (values m z1 (StPop0 m)))
    ((SPop12 _) (let-match erased z (Sz1 _ m z1)) (values m z1 (StPop1 m)))
    ((SPop03 _) (let-match erased z (Sz1 _ m z1)) (values m z1 (StPop0 m)))
    ((SPop13 _) (let-match erased z (Sz0 _ m z1)) (values m z1 (StPop1 m)))))

(def-fns _ $ (erased match-dep : (erased (Bstack) bs) (erased (List (Col)) et) (erased (List (Gsym)) w) (erased (Nat) n) (subterm erased (MatchG bs et w) m)
    (erased (Sz bs n) z) -> (erased (Dep n w) d))
  (match erased m _
    ((MGNil) (let-match erased z (SzNil)) (DNil))
    ((MGCons _ bs2 e s ct cw sy q)
      (let ((erased n2) (erased z2) (erased st)) (sym-sz s bs bs2 e n sy z))
      (DCons s n n2 cw st (match-dep bs2 ct cw n2 q z2)))))

; A symbol read above the bottom bit.
(def-fns _ $ (erased sym-bot : (erased (Gsym) s) (erased (Bstack) bs bs2 b) (erased (Col) e) (erased (Bool) x) (erased (Sym s bs e bs2) sy) (erased (Bot x bs b) p)
    -> (erased (Bstack) b2) (erased (Bot x bs2 b2) q) (erased (Sym s b e b2) sy2))
  (match erased sy _
    ((SSkip _) (values b p (SSkip b)))
    ((SPush2 _) (values (BP0 b) (Bot0 x bs b p) (SPush2 b)))
    ((SPush3 _) (values (BP1 b) (Bot1 x bs b p) (SPush3 b)))
    ((SPop02 _) (let-match erased p (Bot0 _ _ b2 p1)) (values b2 p1 (SPop02 b2)))
    ((SPop12 _) (let-match erased p (Bot1 _ _ b2 p1)) (values b2 p1 (SPop12 b2)))
    ((SPop03 _) (let-match erased p (Bot1 _ _ b2 p1)) (values b2 p1 (SPop03 b2)))
    ((SPop13 _) (let-match erased p (Bot0 _ _ b2 p1)) (values b2 p1 (SPop13 b2)))))

; A symbol that leaves the bottom bit alone, read without it.
(def-fns _ $ (erased sym-unbot : (erased (Gsym) s) (erased (Bstack) s2 b2 sb) (erased (Col) e) (erased (Bool) x) (erased (Nat) n n2) (erased (Sym s s2 e b2) sy)
    (erased (Bot x sb s2) p) (erased (Sz sb n) z) (erased (Step s n n2) st) -> (erased (Bstack) b) (erased (Sym s sb e b) sy2) (erased (Bot x b b2) q) (erased (Sz b n2) z2))
  (match erased sy _
    ((SSkip _) (let-match erased st (StSkip _)) (values sb (SSkip sb) p z))
    ((SPush2 _) (let-match erased st (StPush _)) (values (BP0 sb) (SPush2 sb) (Bot0 x sb s2 p) (Sz0 sb n z)))
    ((SPush3 _) (let-match erased st (StPush _)) (values (BP1 sb) (SPush3 sb) (Bot1 x sb s2 p) (Sz1 sb n z)))
    ((SPop02 _) (let-match erased st (StPop0 _)) (let-match erased p (Bot0 _ b _ p1) (absurd (BotF) z))
      (let-match erased z (Sz0 _ _ z1)) (values b (SPop02 b) p1 z1))
    ((SPop12 _) (let-match erased st (StPop1 _)) (let-match erased p (Bot1 _ b _ p1) (absurd (BotT) z))
      (let-match erased z (Sz1 _ _ z1)) (values b (SPop12 b) p1 z1))
    ((SPop03 _) (let-match erased st (StPop0 _)) (let-match erased p (Bot1 _ b _ p1) (absurd (BotT) z))
      (let-match erased z (Sz1 _ _ z1)) (values b (SPop03 b) p1 z1))
    ((SPop13 _) (let-match erased st (StPop1 _)) (let-match erased p (Bot0 _ b _ p1) (absurd (BotF) z))
      (let-match erased z (Sz0 _ _ z1)) (values b (SPop13 b) p1 z1))))

(def-fns _ $ (erased skip-snoc : (erased (Bstack) bs) (erased (List (Col)) et et2) (erased (List (Gsym)) w w2) (subterm erased (MatchG bs et w) m)
    (erased (Snoc (Col) et (C1) et2) se) (erased (Snoc (Gsym) w (GSkip) w2) sw) -> (erased (MatchG bs et2 w2) r))
  (match erased m _
    ((MGNil) (let-match erased se (SnocNil _ _)) (let-match erased sw (SnocNil _ _)) (MGCons (BS0) (BS0) (C1) (GSkip) (Nil _) (Nil _) (SSkip (BS0)) (MGNil)))
    ((MGCons _ bs2 e s ct cw sy q)
      (let-match erased se (SnocCons _ _ _ _ ct2 se1))
      (let-match erased sw (SnocCons _ _ _ _ cw2 sw1))
      (MGCons bs bs2 e s ct2 cw2 sy (skip-snoc bs2 ct ct2 cw cw2 q se1 sw1)))))

(def-fns _ $ (erased skip-unsnoc : (erased (Bstack) bs) (erased (List (Col)) ct) (erased (List (Gsym)) w w2) (erased (MatchG bs ct w2) m)
    (subterm erased (Snoc (Gsym) w (GSkip) w2) sw) -> (erased (List (Col)) et) (erased (Snoc (Col) et (C1) ct) se) (erased (MatchG bs et w) r))
  (match erased sw _
    ((SnocNil _ _) (let-match erased m (MGCons _ bs2 e _ ct1 _ sy q)) (let-match erased sy (SSkip _)) (let-match erased q (MGNil)) (values (Nil _) (SnocNil _ (C1)) (MGNil)))
    ((SnocCons _ s _ w1 w21 sw1)
      (let-match erased m (MGCons _ bs2 e _ ct1 _ sy q))
      (let ((erased et1) (erased se1) (erased m1)) (skip-unsnoc bs2 ct1 w1 w21 q sw1))
      (values (Cons _ e et1) (SnocCons _ e (C1) et1 ct1 se1) (MGCons bs bs2 e s et1 w1 sy m1)))))

; Appending a pop of the bottom bit x to a chromogram matched from bs (the case b :: lb of match_gram_rot).
(def-fns _ $ (erased bot-snoc : (erased (Bstack) bs s2 x0) (erased (Bool) x) (erased (List (Col)) et et2) (erased (Col) e) (erased (List (Gsym)) w w2)
    (subterm erased (MatchG bs et w) m) (erased (Bot x bs s2) p) (erased (Snoc (Col) et e et2) se) (erased (Snoc (Gsym) w (GPop1) w2) sw)
    (erased (Bot x (BS0) x0) p0) (erased (Sym (GPop1) x0 e (BS0)) sy0) -> (erased (MatchG s2 et2 w2) r))
  (match erased m _
    ((MGNil) (let-match erased se (SnocNil _ _)) (let-match erased sw (SnocNil _ _)) (let-match erased (bot-fn x (BS0) s2 x0 p p0) (Refl _ _))
      (MGCons s2 (BS0) e (GPop1) (Nil _) (Nil _) sy0 (MGNil)))
    ((MGCons _ bs2 e1 s ct cw sy q)
      (let-match erased se (SnocCons _ _ _ _ ct2 se1))
      (let-match erased sw (SnocCons _ _ _ _ cw2 sw1))
      (let ((erased b2) (erased p2) (erased sy2)) (sym-bot s bs bs2 s2 e1 x sy p))
      (MGCons s2 b2 e1 s ct2 cw2 sy2 (bot-snoc bs2 b2 x0 x ct ct2 e cw cw2 q p2 se1 sw1 p0 sy0)))))

(def-fns _ $ (erased bot-unsnoc : (erased (Bstack) bs s2) (erased (Bool) x) (erased (List (Col)) et2) (erased (List (Gsym)) w w2) (erased (Nat) n)
    (erased (MatchG s2 et2 w2) m) (erased (Bot x bs s2) p) (subterm erased (Snoc (Gsym) w (GPop1) w2) sw) (erased (Dep n w) d) (erased (Sz bs n) z)
    -> (erased (List (Col)) et) (erased (Col) e) (erased (Bstack) x0) (erased (Snoc (Col) et e et2) se) (erased (MatchG bs et w) r)
    (erased (Bot x (BS0) x0) p0) (erased (Sym (GPop1) x0 e (BS0)) sy0))
  (match erased sw _
    ((SnocNil _ _)
      (let-match erased m (MGCons _ b2 e1 _ ct1 _ sy q))
      (let-match erased d (DNil))
      (let-match erased z (SzNil))
      (let-match erased q (MGNil))
      (values (Nil _) e1 s2 (SnocNil _ e1) (MGNil) p sy))
    ((SnocCons _ s _ w1 w21 sw1)
      (let-match erased m (MGCons _ b2 e1 _ ct1 _ sy q))
      (let-match erased d (DCons _ _ n2 _ st d1))
      (let ((erased b) (erased sy2) (erased p2) (erased z2)) (sym-unbot s s2 b2 bs e1 x n n2 sy p z st))
      (let ((erased et1) (erased e) (erased x0) (erased se1) (erased m1) (erased p0) (erased sy0)) (bot-unsnoc b b2 x ct1 w1 w21 n2 q p2 sw1 d1 z2))
      (values (Cons _ e1 et1) e x0 (SnocCons _ e1 e et1 ct1 se1) (MGCons bs b e1 s et1 w1 sy2 m1) p0 sy0))))

(def-adts $ (PopSw : ((Gsym) s s2) -> Type)
  enum
  (many PS01 : -> (PopSw (GPop0) (GPop1)))
  (many PS10 : -> (PopSw (GPop1) (GPop0))))

(def-fns _ $ (erased pop-sw : (erased (Gsym) s s2) (erased (Col) e) (erased (Bstack) x1 x2 b2) (erased (Bool) b c) (erased (Sym s x1 e b2) sy)
    (erased (Bot c (BS0) x1) p) (erased (Bot b (BS0) x2) q) (erased (Not b c) n) (erased (PopSw s s2) ps) -> (erased (Sym s2 x2 e b2) r))
  (match erased n _
    ((NotT)
      (let-match erased p (BotF))
      (let-match erased q (BotT))
      (match erased ps _
        ((PS01) (let-match erased sy (SPop02 _)) (SPop12 b2))
        ((PS10) (let-match erased sy (SPop13 _)) (SPop03 b2))))
    ((NotF)
      (let-match erased p (BotT))
      (let-match erased q (BotF))
      (match erased ps _
        ((PS01) (let-match erased sy (SPop03 _)) (SPop13 b2))
        ((PS10) (let-match erased sy (SPop12 _)) (SPop02 b2))))))

(def-fns _ $ (erased neg-sym : (erased (Nat) n) (erased (List (Gsym)) w w2) (subterm erased (Neg n w w2) p) -> (erased (Neg n w2 w) r))
  (match erased p _
    ((NgNil _) (NgNil n))
    ((NgStep s _ n2 w1 w21 st p1) (NgStep s n n2 w21 w1 st (neg-sym n2 w1 w21 p1)))
    ((NgP0 w1) (NgP1 w1))
    ((NgP1 w1) (NgP0 w1))))

; match_gram_neg: the bottom bit c read by w is the bit b read by w2.
(def-fns _ $ (erased neg-match : (erased (Nat) n) (erased (List (Gsym)) w w2) (erased (Bstack) sb s s2) (erased (Bool) b c) (erased (List (Col)) et)
    (subterm erased (Neg n w w2) p) (erased (Sz sb n) z) (erased (Not b c) nb) (erased (Bot b sb s) pb) (erased (Bot c sb s2) pc) (erased (MatchG s2 et w) m)
    -> (erased (MatchG s et w2) r))
  (match erased p _
    ((NgNil _) (let-match erased m (MGNil)) (match erased (bot-ne c sb pc) _))
    ((NgStep s0 _ n2 w1 w21 st p1)
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (let ((erased sb2) (erased sy1) (erased pc2) (erased z2)) (sym-unbot s0 s2 b2 sb e c n n2 sy pc z st))
      (let ((erased bb) (erased pb2) (erased sy2)) (sym-bot s0 sb sb2 s e b sy1 pb))
      (MGCons s bb e s0 et1 w21 sy2 (neg-match n2 w1 w21 sb2 bb b2 b c et1 p1 z2 nb pb2 pc2 q)))
    ((NgP0 w1)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (MGCons s b2 e (GPop1) et1 w1 (pop-sw (GPop0) (GPop1) e s2 s b2 b c sy pc pb nb (PS01)) q))
    ((NgP1 w1)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (MGCons s b2 e (GPop0) et1 w1 (pop-sw (GPop1) (GPop0) e s2 s b2 b c sy pc pb nb (PS10)) q))))

(def-fns _ $ (erased bot-sz : (erased (Bool) x) (erased (Bstack) bs b2) (erased (Nat) n) (subterm erased (Bot x bs b2) p) (erased (Sz bs n) z) -> (erased (Sz b2 (Succ n)) r))
  (match erased p _
    ((BotF) (let-match erased z (SzNil)) (Sz0 (BS0) (Zero) (SzNil)))
    ((BotT) (let-match erased z (SzNil)) (Sz1 (BS0) (Zero) (SzNil)))
    ((Bot0 _ b1 c1 p1) (let-match erased z (Sz0 _ m z1)) (Sz0 c1 (Succ m) (bot-sz x b1 c1 m p1 z1)))
    ((Bot1 _ b1 c1 p1) (let-match erased z (Sz1 _ m z1)) (Sz1 c1 (Succ m) (bot-sz x b1 c1 m p1 z1)))))

(def-fns _ $ (erased step-fn : (erased (Gsym) s) (erased (Nat) n a b) (erased (Step s n a) p) (erased (Step s n b) q) -> (erased (Eq (Nat) a b) e))
  (match erased p _
    ((StSkip _) (let-match erased q (StSkip _)) (Refl _ a))
    ((StPush _) (let-match erased q (StPush _)) (Refl _ a))
    ((StPop0 _) (let-match erased q (StPop0 _)) (Refl _ a))
    ((StPop1 _) (let-match erased q (StPop1 _)) (Refl _ a))))

(def-fns _ $ (erased push-bot : (erased (Col) e) (erased (Bstack) x0) (erased (Sym (GPush) (BS0) e x0) sy) -> (erased (Bool) b) (erased (Bot b (BS0) x0) p))
  (match erased sy _ ((SPush2 _) (values (BFalse) (BotF))) ((SPush3 _) (values (BTrue) (BotT)))))

(def-fns _ $ (erased pop0-push : (erased (Col) e) (erased (Bstack) x0) (erased (Bool) b) (erased (Sym (GPop0) x0 e (BS0)) sy) (erased (Bot b (BS0) x0) p)
    -> (erased (Sym (GPush) (BS0) e x0) r))
  (match erased p _ ((BotF) (let-match erased sy (SPop02 _)) (SPush2 (BS0))) ((BotT) (let-match erased sy (SPop03 _)) (SPush3 (BS0)))))

(def-fns _ $ (erased pop1-push : (erased (Col) e) (erased (Bstack) x0 y0) (erased (Bool) b c) (erased (Sym (GPop1) x0 e (BS0)) sy) (erased (Bot b (BS0) x0) p)
    (erased (Not b c) n) (erased (Bot c (BS0) y0) q) -> (erased (Sym (GPush) (BS0) e y0) r))
  (match erased n _
    ((NotT) (let-match erased p (BotT)) (let-match erased q (BotF)) (let-match erased sy (SPop12 _)) (SPush2 (BS0)))
    ((NotF) (let-match erased p (BotF)) (let-match erased q (BotT)) (let-match erased sy (SPop13 _)) (SPush3 (BS0)))))

(def-fns _ $ (erased push-pop0 : (erased (Col) e) (erased (Bstack) x0 s y0) (erased (Bool) c) (erased (Sym (GPush) (BS0) e x0) sy) (erased (Bot c x0 s) p)
    (erased (Bot c (BS0) y0) q) -> (erased (Sym (GPop0) s e y0) r))
  (match erased sy _
    ((SPush2 _) (let-match erased p (Bot0 _ _ y1 p1)) (let-match erased (bot-fn c (BS0) y1 y0 p1 q) (Refl _ _)) (SPop02 y0))
    ((SPush3 _) (let-match erased p (Bot1 _ _ y1 p1)) (let-match erased (bot-fn c (BS0) y1 y0 p1 q) (Refl _ _)) (SPop03 y0))))

(def-fns _ $ (erased push-pop1 : (erased (Col) e) (erased (Bstack) x0 a s) (erased (Bool) b c) (erased (Sym (GPush) (BS0) e x0) sy) (erased (Bot c (BS0) x0) px)
    (erased (Not b c) n) (erased (Bot b (BS0) a) pa) (erased (Bot c a s) ps) -> (erased (Sym (GPop1) s e x0) r))
  (match erased sy _
    ((SPush2 _) (let-match erased px (BotF)) (let-match erased n (NotT)) (let-match erased pa (BotT)) (let-match erased ps (Bot1 _ _ _ p1))
      (let-match erased p1 (BotF)) (SPop12 x0))
    ((SPush3 _) (let-match erased px (BotT)) (let-match erased n (NotF)) (let-match erased pa (BotF)) (let-match erased ps (Bot0 _ _ _ p1))
      (let-match erased p1 (BotT)) (SPop13 x0))))

; match_gram_flip, one way: a chromogram matched from sb ++ [b; c] flips into one matched from sb.
(def-fns _ $ (erased flip-match : (erased (Nat) n) (erased (List (Gsym)) w w2) (erased (Bstack) sb s) (erased (List (Col)) et) (subterm erased (Flip n w w2) f)
    (erased (Sz sb n) z) (erased (Bot2 sb s) bt) (erased (MatchG s et w) m) -> (erased (MatchG sb et w2) r))
  (let-match erased bt (MkBot2 _ a _ b c nt pb pc))
  (match erased f _
    ((FlNil _) (let-match erased m (MGNil)) (match erased (bot-ne c a pc) _))
    ((FlStep s0 _ n2 w1 w21 st f1)
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (let ((erased a2) (erased sy1) (erased pc2) (erased za)) (sym-unbot s0 s b2 a e c (Succ n) (Succ n2) sy pc (bot-sz b sb a n pb z) (step-succ s0 n n2 st)))
      (let ((erased sb2) (erased sy2) (erased pb2) (erased z2)) (sym-unbot s0 a a2 sb e b n n2 sy1 pb z st))
      (MGCons sb sb2 e s0 et1 w21 sy2 (flip-match n2 w1 w21 sb2 b2 et1 f1 z2 (MkBot2 sb2 a2 b2 b c nt pb2 pc2) q)))
    ((FlP0 w1 w21 ng)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (let ((erased a2) (erased sy1) (erased pc2) (erased za)) (sym-unbot (GPop0) s b2 a e c (Succ (Zero)) (Zero) sy pc (bot-sz b sb a n pb z) (StPop0 (Zero))))
      (let-match erased za (SzNil))
      (MGCons sb a e (GPush) et1 w21 (pop0-push e a b sy1 pb) (neg-match (Zero) w1 w21 (BS0) a b2 b c et1 ng (SzNil) nt pb pc2 q)))
    ((FlP1 w1)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ b2 e _ et1 _ sy q))
      (let ((erased a2) (erased sy1) (erased pc2) (erased za)) (sym-unbot (GPop1) s b2 a e c (Succ (Zero)) (Zero) sy pc (bot-sz b sb a n pb z) (StPop1 (Zero))))
      (let-match erased za (SzNil))
      (MGCons sb b2 e (GPush) et1 w1 (pop1-push e a b2 b c sy1 pb nt pc2) q))))

; match_gram_flip, the other way.
(def-fns _ $ (erased flip-unmatch : (erased (Nat) n) (erased (List (Gsym)) w w2) (erased (Bstack) sb) (erased (List (Col)) et) (subterm erased (Flip n w w2) f)
    (erased (Sz sb n) z) (erased (MatchG sb et w2) m) -> (erased (Bstack) s) (erased (Bot2 sb s) bt) (erased (MatchG s et w) r))
  (match erased f _
    ((FlNil _) (let-match erased m (MGCons _ b2 e _ et1 _ sy q)) (let-match erased q (MGNil)) (match erased sy _))
    ((FlStep s0 _ n2 w1 w21 st f1)
      (let-match erased m (MGCons _ sb2 e _ et1 _ sy q))
      (let ((erased n3) (erased z2) (erased st2)) (sym-sz s0 sb sb2 e n sy z))
      (let-match erased (step-fn s0 n n3 n2 st2 st) (Refl _ _))
      (let ((erased s2) (erased bt) (erased m1)) (flip-unmatch n2 w1 w21 sb2 et1 f1 z2 q))
      (let-match erased bt (MkBot2 _ a2 _ b c nt pb pc))
      (let ((erased a) (erased pa)) (bot-exists b sb))
      (let ((erased a3) (erased pa3) (erased sya)) (sym-bot s0 sb sb2 a e b sy pa))
      (let-match erased (bot-fn b sb2 a3 a2 pa3 pb) (Refl _ _))
      (let ((erased s) (erased ps)) (bot-exists c a))
      (let ((erased s3) (erased ps3) (erased sys)) (sym-bot s0 a a2 s e c sya ps))
      (let-match erased (bot-fn c a2 s3 s2 ps3 pc) (Refl _ _))
      (values s (MkBot2 sb a s b c nt pa ps) (MGCons s s2 e s0 et1 w1 sys m1)))
    ((FlP0 w1 w21 ng)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ x0 e _ et1 _ sy q))
      (let ((erased b) (erased px)) (push-bot e x0 sy))
      (let ((erased c) (erased nt)) (not-exists b))
      (let ((erased y0) (erased py)) (bot-exists c (BS0)))
      (let ((erased s) (erased ps)) (bot-exists c x0))
      (values s (MkBot2 (BS0) x0 s b c nt px ps)
        (MGCons s y0 e (GPop0) et1 w1 (push-pop0 e x0 s y0 c sy ps py)
          (neg-match (Zero) w21 w1 (BS0) y0 x0 c b et1 (neg-sym (Zero) w1 w21 ng) (SzNil) (not-sym b c nt) py px q))))
    ((FlP1 w1)
      (let-match erased z (SzNil))
      (let-match erased m (MGCons _ x0 e _ et1 _ sy q))
      (let ((erased c) (erased px)) (push-bot e x0 sy))
      (let ((erased b) (erased ncb)) (not-exists c))
      (let ((erased nt)) (not-sym c b ncb))
      (let ((erased a) (erased pa)) (bot-exists b (BS0)))
      (let ((erased s) (erased ps)) (bot-exists c a))
      (values s (MkBot2 (BS0) a s b c nt pa ps) (MGCons s x0 e (GPop1) et1 w1 (push-pop1 e x0 a s b c sy px nt pa ps) q)))))

(def-fns _ $ (erased neg-ex : (erased (Nat) n) (subterm erased (List (Gsym)) w) -> (erased (List (Gsym)) w2) (erased (Neg n w w2) p))
  (let-match erased w (Cons _ s w1) ((Nil _) (values (Nil _) (NgNil n))))
  (match erased s _
    ((GSkip) (let ((erased w2) (erased p)) (neg-ex n w1)) (values (Cons _ s w2) (NgStep s n n w1 w2 (StSkip n) p)))
    ((GPush) (let ((erased w2) (erased p)) (neg-ex (Succ n) w1)) (values (Cons _ s w2) (NgStep s n (Succ n) w1 w2 (StPush n) p)))
    ((GPop0) (match erased n _
      ((Zero) (values (Cons _ (GPop1) w1) (NgP0 w1)))
      ((Succ m) (let ((erased w2) (erased p)) (neg-ex m w1)) (values (Cons _ s w2) (NgStep s n m w1 w2 (StPop0 m) p)))))
    ((GPop1) (match erased n _
      ((Zero) (values (Cons _ (GPop0) w1) (NgP1 w1)))
      ((Succ m) (let ((erased w2) (erased p)) (neg-ex m w1)) (values (Cons _ s w2) (NgStep s n m w1 w2 (StPop1 m) p)))))))

(def-fns _ $ (erased flip-ex : (erased (Nat) n) (subterm erased (List (Gsym)) w) -> (erased (List (Gsym)) w2) (erased (Flip n w w2) p))
  (let-match erased w (Cons _ s w1) ((Nil _) (values (Cons _ (GPush) (Nil _)) (FlNil n))))
  (match erased s _
    ((GSkip) (let ((erased w2) (erased p)) (flip-ex n w1)) (values (Cons _ s w2) (FlStep s n n w1 w2 (StSkip n) p)))
    ((GPush) (let ((erased w2) (erased p)) (flip-ex (Succ n) w1)) (values (Cons _ s w2) (FlStep s n (Succ n) w1 w2 (StPush n) p)))
    ((GPop0) (match erased n _
      ((Zero) (let ((erased w2) (erased p)) (neg-ex (Zero) w1)) (values (Cons _ (GPush) w2) (FlP0 w1 w2 p)))
      ((Succ m) (let ((erased w2) (erased p)) (flip-ex m w1)) (values (Cons _ s w2) (FlStep s n m w1 w2 (StPop0 m) p)))))
    ((GPop1) (match erased n _
      ((Zero) (values (Cons _ (GPush) w1) (FlP1 w1)))
      ((Succ m) (let ((erased w2) (erased p)) (flip-ex m w1)) (values (Cons _ s w2) (FlStep s n m w1 w2 (StPop1 m) p)))))))

(def-fns _ $ (erased rot-push : (erased (Col) e) (erased (List (Col)) et ct) (erased (List (Gsym)) w) (erased (Bool) b c) (erased (Bstack) b0 x0 s)
    (erased (MatchG b0 et w) m) (erased (Snoc (Col) et e ct) se) (erased (Not b c) nt) (erased (Bot b (BS0) b0) pb) (erased (Bot c b0 s) ps)
    (erased (Bot c (BS0) x0) px) (erased (Sym (GPop1) x0 e (BS0)) sy) -> (erased (List (Gsym)) w1) (erased (GramRot (Cons (Gsym) (GPush) w) w1) g)
    (erased (MatchG (BS0) ct w1) r))
  (let ((erased w2) (erased sw)) (snoc-exists (Gsym) w (GPop1)))
  (let ((erased w1) (erased fl)) (flip-ex (Zero) w2))
  (values w1 (GRPush w w2 w1 sw fl)
    (flip-match (Zero) w2 w1 (BS0) s ct fl (SzNil) (MkBot2 (BS0) b0 s b c nt pb ps) (bot-snoc b0 s x0 c et ct e w w2 m ps se sw px sy))))

; match_gram_rot, one way: rotating a matched trace by one rotates its chromogram.
(def-fns _ $ (erased rot-match : (erased (Col) e) (erased (List (Col)) et ct) (erased (List (Gsym)) w) (erased (MatchG (BS0) (Cons (Col) e et) w) m)
    (erased (Snoc (Col) et e ct) se) -> (erased (List (Gsym)) w1) (erased (GramRot w w1) g) (erased (MatchG (BS0) ct w1) r))
  (let-match erased m (MGCons _ b0 _ s _ w0 sy q))
  (match erased sy _
    ((SSkip _)
      (let ((erased w1) (erased sw)) (snoc-exists (Gsym) w0 (GSkip)))
      (values w1 (GRSkip w0 w1 sw) (skip-snoc (BS0) et ct w0 w1 q se sw)))
    ((SPush2 _)
      (rot-push e et ct w0 (BFalse) (BTrue) b0 (BP1 (BS0)) (BP0 (BP1 (BS0))) q se (NotF) (BotF) (Bot0 (BTrue) (BS0) (BP1 (BS0)) (BotT)) (BotT) (SPop12 (BS0))))
    ((SPush3 _)
      (rot-push e et ct w0 (BTrue) (BFalse) b0 (BP0 (BS0)) (BP1 (BP0 (BS0))) q se (NotT) (BotT) (Bot1 (BFalse) (BS0) (BP0 (BS0)) (BotF)) (BotF) (SPop13 (BS0))))))

; match_gram_rot, the other way, for a w matching some trace.
(def-fns _ $ (erased rot-unmatch : (erased (List (Gsym)) w w1) (erased (List (Col)) ct et0) (erased (GramRot w w1) g) (erased (MatchG (BS0) ct w1) m)
    (erased (MatchG (BS0) et0 w) m0) -> (erased (Col) e) (erased (List (Col)) et) (erased (Snoc (Col) et e ct) se) (erased (MatchG (BS0) (Cons (Col) e et) w) r))
  (match erased g _
    ((GRSkip w0 _ sw)
      (let ((erased et) (erased se) (erased m1)) (skip-unsnoc (BS0) ct w0 w1 m sw))
      (values (C1) et se (MGCons (BS0) (BS0) (C1) (GSkip) et w0 (SSkip (BS0)) m1)))
    ((GRPush w0 w2 _ sw fl)
      (let ((erased s) (erased bt) (erased m2)) (flip-unmatch (Zero) w2 w1 (BS0) ct fl (SzNil) m))
      (let-match erased bt (MkBot2 _ a _ b c nt pa ps))
      (let-match erased m0 (MGCons _ b0 e0 _ et01 _ sy0 q0))
      (let ((erased n2) (erased z2) (erased st)) (sym-sz (GPush) (BS0) b0 e0 (Zero) sy0 (SzNil)))
      (let-match erased st (StPush _))
      (let ((erased et) (erased e) (erased x0) (erased se) (erased m3) (erased px) (erased sy))
        (bot-unsnoc a s c ct w0 w2 (Succ (Zero)) m2 ps sw (match-dep b0 et01 w0 n2 q0 z2) (bot-sz b (BS0) a (Zero) pa (SzNil))))
      (values e et se (MGCons (BS0) a e (GPush) et w0 (pop1-push e x0 a c b sy px (not-sym b c nt) pa) m3)))))
