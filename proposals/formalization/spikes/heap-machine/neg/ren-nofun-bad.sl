(def-adts
  ((Ren : -> Type)
    enum
    (many RNil : -> (Ren))
    (many RCons : (many (Nat) a) (many (Nat) a') (many (Ren) rest) -> (Ren)))
  ((RenA : ((Ren) r) ((Nat) a) ((Nat) a') -> Type)
    enum
    (many RenHere : (erased (Nat) a a') (erased (Ren) rest) -> (RenA (RCons a a' rest) a a'))
    (many RenThere : (erased (Nat) a a' c c') (erased (Ren) rest) (erased (Neq a c) n) (erased (Neq a' c') n') (erased (RenA rest a a') p)
       -> (RenA (RCons c c' rest) a a')))
  ((RenW : ((Ren) r) ((Word) w) ((Word) w') -> Type)
    enum
    (many RenImm : (erased (Ren) r) (erased (Nat) n) -> (RenW r (WImm n) (WImm n)))
    (many RenAddr : (erased (Ren) r) (erased (Nat) a a') (erased (RenA r a a') p) -> (RenW r (WAddr a) (WAddr a'))))
  ((RenWs : ((Ren) r) ((List (Word)) ws) ((List (Word)) ws') -> Type)
    enum
    (many RenWsNil : (erased (Ren) r) -> (RenWs r (Nil (Word)) (Nil (Word))))
    (many RenWsCons : (erased (Ren) r) (erased (Word) w w') (erased (List (Word)) ws ws') (erased (RenW r w w') p) (erased (RenWs r ws ws') q)
       -> (RenWs r (Cons (Word) w ws) (Cons (Word) w' ws'))))
  ((RenB : ((Ren) r) ((Block) b) ((Block) b') -> Type)
    enum
    (many MkRenB : (erased (Ren) r) (erased (Nat) tag) (erased (List (Word)) fs fs') (erased (RenWs r fs fs') p)
       -> (RenB r (MkBlock tag fs) (MkBlock tag fs'))))
  ((RenH : ((Ren) r) ((Heap) h) ((Heap) h') -> Type)
    enum
    (many RenHNil : (erased (Ren) r) -> (RenH r (HNil) (HNil)))
    (many RenHCons : (erased (Ren) r) (erased (Nat) a a') (erased (Block) b b') (erased (Heap) h h')
       (erased (RenA r a a') pa) (erased (RenB r b b') pb) (erased (RenH r h h') ph) -> (RenH r (HCons a b h) (HCons a' b' h'))))
  ((RenL : ((Ren) r) ((Label) l) ((Label) l') -> Type)
    enum
    (many RenLTau : (erased (Ren) r) -> (RenL r (LTau) (LTau)))
    (many RenLAddr : (erased (Ren) r) (erased (Nat) a a') (erased (RenA r a a') p) -> (RenL r (LAddr a) (LAddr a')))
    (many RenLYes : (erased (Ren) r) -> (RenL r (LYes) (LYes)))
    (many RenLNo : (erased (Ren) r) -> (RenL r (LNo) (LNo))))
  ((RenCh : ((Ren) r) ((Choices) ch) ((Choices) ch') -> Type)
    enum
    (many RenChOne : (erased (Ren) r) (erased (Label) l l') (erased (RenL r l l') p) -> (RenCh r (ChOne l) (ChOne l')))
    (many RenChSeq : (erased (Ren) r) (erased (Choices) c1 c1' c2 c2') (erased (RenCh r c1 c1') p) (erased (RenCh r c2 c2') q)
       -> (RenCh r (ChSeq c1 c2) (ChSeq c1' c2')))))

(def-fns _ $ (erased ren-fun : (erased (Ren) r) (erased (Nat) a x y) (subterm erased (RenA r a x) p) (erased (RenA r a y) q) -> (erased (Eq (Nat) x y) e))
  (match erased p _
    ((RenHere _ _ _)
      (match erased q _
        ((RenHere _ _ _) (Refl _ x))
        (absurd (RenThere _ _ _ _ _ n _ _) (neq-irrefl a n))))
    ((RenThere _ _ c c' rest n _ p1)
      (let-match erased q (RenThere _ _ _ _ _ _ _ q1) (absurd (RenHere _ _ _) (neq-irrefl a n)))
      (ren-fun rest a x y p1 q1))))

(def-fns _ $ (erased ren-inj : (erased (Ren) r) (erased (Nat) a b x) (subterm erased (RenA r a x) p) (erased (RenA r b x) q) -> (erased (Eq (Nat) a b) e))
  (match erased p _
    ((RenHere _ _ _)
      (match erased q _
        ((RenHere _ _ _) (Refl _ a))
        (absurd (RenThere _ _ _ _ _ _ n' _) (neq-irrefl x n'))))
    ((RenThere _ _ c c' rest _ n' p1)
      (let-match erased q (RenThere _ _ _ _ _ _ _ q1) (absurd (RenHere _ _ _) (neq-irrefl x n')))
      (ren-inj rest a b x p1 q1))))

(def-fns _ $ (erased ren-neq : (erased (Ren) r) (erased (Nat) a a' b b') (erased (RenA r a a') p) (erased (RenA r b b') q) (erased (Neq a b) n) ->
    (erased (Neq a' b') m))
  (match erased (nat-dec a' b') _
    ((NDDiff _ _ m) m)
    (absurd (NDSame _) (let-match erased (ren-inj r a b a' p q) (Refl _ _)) (neq-irrefl a n))))

(def-fns _ $ (erased renw-fun : (erased (Ren) r) (erased (Word) w x y) (erased (RenW r w x) p) (erased (RenW r w y) q) -> (erased (Eq (Word) x y) e))
  (match erased p _
    ((RenImm _ _) (let-match erased q (RenImm _ _)) (Refl _ x))
    ((RenAddr _ a a1 p1)
      (let-match erased q (RenAddr _ _ a2 q1))
      (let-match erased (ren-fun r a a1 a2 p1 q1) (Refl _ _))
      (Refl _ x))))

(def-fns _ $ (erased ren-nth : (erased (Ren) r) (erased (List (Word)) ws ws') (erased (Nat) i) (erased (Word) w)
    (erased (RenWs r ws ws') rw) (subterm erased (Nth (Word) ws i w) p) ->
    (erased (Word) w') (erased (Nth (Word) ws' i w') q) (erased (RenW r w w') e))
  (match erased p _
    ((NthHere _ _ rest) (let-match erased rw (RenWsCons _ _ v _ rest' pv _)) (values v (NthHere _ v rest') pv))
    ((NthThere _ y rest j _ p1)
      (let-match erased rw (RenWsCons _ _ y' _ rest' _ rw1))
      (let ((erased w') (erased q) (erased e)) (ren-nth r rest rest' j w rw1 p1))
      (values w' (NthThere _ y' rest' j w' q) e))))

(def-fns _ $ (erased ren-atomval : (erased (Ren) r) (erased (List (Word)) env env') (erased (Atom) a) (erased (Word) w)
    (erased (RenWs r env env') re) (erased (AtomVal env a w) p) ->
    (erased (Word) w') (erased (AtomVal env' a w') q) (erased (RenW r w w') e))
  (let-match erased p (AVVar _ i _ p1) ((AVImm _ n) (values (WImm n) (AVImm env' n) (RenImm r n))))
  (let ((erased w') (erased q) (erased e)) (ren-nth r env env' i w re p1))
  (values w' (AVVar env' i w' q) e))

(def-fns _ $ (erased ren-atomvals : (erased (Ren) r) (erased (List (Word)) env env') (erased (List (Atom)) as) (erased (List (Word)) ws)
    (erased (RenWs r env env') re) (subterm erased (AtomVals env as ws) p) ->
    (erased (List (Word)) ws') (erased (AtomVals env' as ws') q) (erased (RenWs r ws ws') e))
  (let-match erased p (AVsCons _ a w rest ws1 pa p1) ((AVsNil _) (values (Nil _) (AVsNil env') (RenWsNil r))))
  (let ((erased w') (erased pa') (erased rw)) (ren-atomval r env env' a w re pa))
  (let ((erased ws1') (erased q) (erased e)) (ren-atomvals r env env' rest ws1 re p1))
  (values (Cons _ w' ws1') (AVsCons env' a w' rest ws1' pa' q) (RenWsCons r w w' ws1 ws1' rw e)))

(def-fns _ $ (erased ren-cat : (erased (Ren) r) (erased (List (Word)) xs ys zs xs' ys')
    (subterm erased (Cat xs ys zs) p) (erased (RenWs r xs xs') rx) (erased (RenWs r ys ys') ry) ->
    (erased (List (Word)) zs') (erased (Cat xs' ys' zs') q) (erased (RenWs r zs zs') rz))
  (match erased p _
    ((CatNil _) (let-match erased rx (RenWsNil _)) (values ys' (CatNil ys') ry))
    ((CatCons x rest _ zs1 p1)
      (let-match erased rx (RenWsCons _ _ x' _ rest' px rx1))
      (let ((erased zs1') (erased q) (erased rz)) (ren-cat r rest ys zs1 rest' ys' p1 rx1 ry))
      (values (Cons _ x' zs1') (CatCons x' rest' ys' zs1' q) (RenWsCons r x x' zs1 zs1' px rz)))))

(def-fns _ $ (erased ren-setnth : (erased (Ren) r) (erased (List (Word)) xs xs') (erased (Nat) i) (erased (Word) y y') (erased (List (Word)) ys)
    (subterm erased (SetNth (Word) xs i y ys) p) (erased (RenWs r xs xs') rx) (erased (RenW r y y') ry) ->
    (erased (List (Word)) ys') (erased (SetNth (Word) xs' i y' ys') q) (erased (RenWs r ys ys') rz))
  (match erased p _
    ((SetHere _ x _ rest)
      (let-match erased rx (RenWsCons _ _ x' _ rest' _ rx1))
      (values (Cons _ y' rest') (SetHere _ x' y' rest') (RenWsCons r y y' rest rest' ry rx1)))
    ((SetThere _ x rest j _ rest2 p1)
      (let-match erased rx (RenWsCons _ _ x' _ rest' px rx1))
      (let ((erased rest2') (erased q) (erased rz)) (ren-setnth r rest rest' j y y' rest2 p1 rx1 ry))
      (values (Cons _ x' rest2') (SetThere _ x' rest' j y' rest2' q) (RenWsCons r x x' rest2 rest2' px rz)))))

(def-fns _ $ (erased ren-lookup : (erased (Ren) r) (erased (Heap) h h') (erased (Nat) a a') (erased (Block) b)
    (erased (RenH r h h') rh) (subterm erased (Lookup h a b) lk) (erased (RenA r a a') ra) ->
    (erased (Block) b') (erased (Lookup h' a' b') lk') (erased (RenB r b b') rb))
  (match erased lk _
    ((LkHere _ _ rest)
      (let-match erased rh (RenHCons _ _ a2 _ b2 _ rest' pa pb _))
      (let-match erased (ren-fun r a a' a2 ra pa) (Refl _ _))
      (values b2 (LkHere a' b2 rest') pb))
    ((LkThere _ c _ other rest n lk1)
      (let-match erased rh (RenHCons _ _ c' _ other' _ rest' pc _ rh1))
      (let ((erased b') (erased lk') (erased rb)) (ren-lookup r rest rest' a a' b rh1 lk1 ra))
      (values b' (LkThere a' c' b' other' rest' (ren-neq r a a' c c' ra pc n) lk') rb))))

(def-fns _ $ (erased ren-fresh : (erased (Ren) r) (erased (Heap) h h') (erased (Nat) a a')
    (erased (RenH r h h') rh) (subterm erased (Fresh h a) f) (erased (RenA r a a') ra) -> (erased (Fresh h' a') f'))
  (match erased f _
    ((FreshNil _) (let-match erased rh (RenHNil _)) (FreshNil a'))
    ((FreshCons _ c other rest n f1)
      (let-match erased rh (RenHCons _ _ c' _ other' _ rest' pc _ rh1))
      (FreshCons a' c' other' rest' (ren-neq r a a' c c' ra pc n) (ren-fresh r rest rest' a a' rh1 f1 ra)))))

(def-fns _ $ (erased ren-update : (erased (Ren) r) (erased (Heap) h h') (erased (Nat) a a') (erased (Block) b b') (erased (Heap) h2)
    (erased (RenH r h h') rh) (subterm erased (Update h a b h2) u) (erased (RenA r a a') ra) (erased (RenB r b b') rb) ->
    (erased (Heap) h2') (erased (Update h' a' b' h2') u') (erased (RenH r h2 h2') rh2))
  (match erased u _
    ((UpHere _ old _ rest)
      (let-match erased rh (RenHCons _ _ a2 _ old' _ rest' pa _ rh1))
      (let-match erased (ren-fun r a a' a2 ra pa) (Refl _ _))
      (values (HCons a' b' rest') (UpHere a' old' b' rest') (RenHCons r a a' b b' rest rest' ra rb rh1)))
    ((UpThere _ c _ other rest rest2 n u1)
      (let-match erased rh (RenHCons _ _ c' _ other' _ rest' pc po rh1))
      (let ((erased rest2') (erased u') (erased rh2)) (ren-update r rest rest' a a' b b' rest2 rh1 u1 ra rb))
      (values (HCons c' other' rest2') (UpThere a' c' b' other' rest' rest2' (ren-neq r a a' c c' ra pc n) u')
        (RenHCons r c c' other other' rest2 rest2' pc po rh2)))))

(def-fns _ $ (erased ren-alloc : (erased (Ren) r) (erased (Heap) h h') (erased (Nat) a a') (erased (Block) b b') (erased (Heap) h2)
    (erased (RenH r h h') rh) (erased (Alloc h a b h2) al) (erased (RenA r a a') ra) (erased (RenB r b b') rb) ->
    (erased (Heap) h2') (erased (Alloc h' a' b' h2') al') (erased (RenH r h2 h2') rh2))
  (let-match erased al (MkAlloc _ _ _ f))
  (values (HCons a' b' h') (MkAlloc h' a' b' (ren-fresh r h h' a a' rh f ra)) (RenHCons r a a' b b' h h' ra rb rh)))

(def-fns _ $ (erased ren-patched : (erased (Ren) r) (erased (Heap) h h') (erased (List (Word)) env env') (erased (Atom) a) (erased (Nat) i) (erased (Atom) b)
    (erased (Nat) p) (erased (Block) blk)
    (erased (RenH r h h') rh) (erased (RenWs r env env') re) (erased (Patched h env a i b p blk) pt) ->
    (erased (Nat) p') (erased (Block) blk') (erased (Patched h' env' a i b p' blk') pt') (erased (RenA r p p') rp) (erased (RenB r blk blk') rb))
  (let-match erased pt (MkPatched _ _ _ _ _ _ w tag fs fs2 pa pb lk st))
  (let ((erased wa') (erased pa') (erased rwa)) (ren-atomval r env env' a (WAddr p) re pa))
  (let-match erased rwa (RenAddr _ _ p' rp))
  (let ((erased w') (erased pb') (erased rw)) (ren-atomval r env env' b w re pb))
  (let ((erased old') (erased lk') (erased rold)) (ren-lookup r h h' p p' (MkBlock tag fs) rh lk rp))
  (let-match erased rold (MkRenB _ _ _ fs' rfs))
  (let ((erased fs2') (erased st') (erased rfs2)) (ren-setnth r fs fs' i w w' fs2 st rfs rw))
  (values p' (MkBlock tag fs2') (MkPatched h' env' a i b p' w' tag fs' fs2' pa' pb' lk' st') rp (MkRenB r tag fs2 fs2' rfs2)))

(def-fns _ $ (erased ren-prim : (erased (Ren) r) (erased (Heap) h h') (erased (List (Word)) env env') (erased (Instr) i) (erased (Label) l l')
    (erased (Heap) h2) (erased (Word) w)
    (erased (RenH r h h') rh) (erased (RenWs r env env') re) (erased (RenL r l l') rl) (erased (Prim h env i l h2 w) d) ->
    (erased (Heap) h2') (erased (Word) w') (erased (Prim h' env' i l' h2' w') d') (erased (RenH r h2 h2') rh2) (erased (RenW r w w') rw))
  (match erased d _
    ((PAtom _ _ a _ p)
      (let-match erased rl (RenLTau _))
      (let ((erased w') (erased p') (erased rw)) (ren-atomval r env env' a w re p))
      (values h' w' (PAtom h' env' a w' p') rh rw))
    ((PCon _ _ tag args ws p _ pa al)
      (let-match erased rl (RenLAddr _ _ p' rp))
      (let ((erased ws') (erased pa') (erased rws)) (ren-atomvals r env env' args ws re pa))
      (let ((erased h2') (erased al') (erased rh2))
        (ren-alloc r h h' p p' (MkBlock tag ws) (MkBlock tag ws') h2 rh al rp (MkRenB r tag ws ws' rws)))
      (values h2' (WAddr p') (PCon h' env' tag args ws' p' h2' pa' al') rh2 (RenAddr r p p' rp)))
    ((PWrite _ _ a j b p blk _ pt up)
      (let-match erased rl (RenLTau _))
      (let ((erased p') (erased blk') (erased pt') (erased rp) (erased rb)) (ren-patched r h h' env env' a j b p blk rh re pt))
      (let ((erased h2') (erased up') (erased rh2)) (ren-update r h h' p p' blk blk' h2 rh up rp rb))
      (values h2' (WAddr p') (PWrite h' env' a j b p' blk' h2' pt' up') rh2 (RenAddr r p p' rp)))
    ((PCopy _ _ a j b p blk q _ pt al)
      (let-match erased rl (RenLAddr _ _ q' rq))
      (let ((erased p') (erased blk') (erased pt') (erased rp) (erased rb)) (ren-patched r h h' env env' a j b p blk rh re pt))
      (let ((erased h2') (erased al') (erased rh2)) (ren-alloc r h h' q q' blk blk' h2 rh al rq rb))
      (values h2' (WAddr q') (PCopy h' env' a j b p' blk' q' h2' pt' al') rh2 (RenAddr r q q' rq)))
    ((PSameYes _ _ a b v pa pb)
      (let-match erased rl (RenLYes _))
      (let ((erased va) (erased pa') (erased ra)) (ren-atomval r env env' a v re pa))
      (let ((erased vb) (erased pb') (erased rb)) (ren-atomval r env env' b v re pb))
      (values h' (WImm (Succ (Zero))) (PSameYes h' env' a b va pa' pb') rh (RenImm r (Succ (Zero)))))
    ((PSameNo _ _ a b v1 v2 pa pb)
      (let-match erased rl (RenLNo _))
      (let ((erased va) (erased pa') (erased ra)) (ren-atomval r env env' a v1 re pa))
      (let ((erased vb) (erased pb') (erased rb)) (ren-atomval r env env' b v2 re pb))
      (values h' (WImm (Zero)) (PSameNo h' env' a b va vb pa' pb') rh (RenImm r (Zero))))))

(def-fns _ $ (erased ren-select : (erased (Ren) r) (erased (Heap) h h') (erased (Word) w w') (erased (List (Code)) blocks imms) (erased (Code) body)
    (erased (List (Word)) fs)
    (erased (RenH r h h') rh) (erased (RenW r w w') rw) (erased (Select h w blocks imms body fs) sel) ->
    (erased (List (Word)) fs') (erased (Select h' w' blocks imms body fs') sel') (erased (RenWs r fs fs') rfs))
  (match erased sel _
    ((SelImm _ n _ _ _ br)
      (let-match erased rw (RenImm _ _))
      (values (Nil _) (SelImm h' n blocks imms body br) (RenWsNil r)))
    ((SelBlock _ p _ _ _ tag _ lk br)
      (let-match erased rw (RenAddr _ _ p' rp))
      (let ((erased b') (erased lk') (erased rb)) (ren-lookup r h h' p p' (MkBlock tag fs) rh lk rp))
      (let-match erased rb (MkRenB _ _ _ fs' rfs))
      (values fs' (SelBlock h' p' blocks imms body tag fs' lk' br) rfs))))

(def-fns _ $ (erased ren-run : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (List (Word)) env env') (erased (Code) c)
    (erased (Choices) ch ch') (erased (Heap) h2) (erased (Word) w)
    (erased (RenH r h h') rh) (erased (RenWs r env env') re) (erased (RenCh r ch ch') rc) (subterm erased (Run fns h env c ch h2 w) d) ->
    (erased (Heap) h2') (erased (Word) w') (erased (Run fns h' env' c ch' h2' w') d') (erased (RenH r h2 h2') rh2) (erased (RenW r w w') rw))
  (match erased d _
    ((RunDo _ _ _ i l _ _ p)
      (let-match erased rc (RenChOne _ _ l' rl))
      (let ((erased h2') (erased w') (erased p') (erased rh2) (erased rw)) (ren-prim r h h' env env' i l l' h2 w rh re rl p))
      (values h2' w' (RunDo fns h' env' i l' h2' w' p') rh2 rw))
    ((RunLet _ _ _ rhs body ch1 h1 w1 ch2 _ _ p q)
      (let-match erased rc (RenChSeq _ _ ch1' _ ch2' rc1 rc2))
      (let ((erased h1') (erased w1') (erased p') (erased rh1) (erased rw1)) (ren-run r fns h h' env env' rhs ch1 ch1' h1 w1 rh re rc1 p))
      (let ((erased h2') (erased w') (erased q') (erased rh2) (erased rw))
        (ren-run r fns h1 h1' (Cons _ w1 env) (Cons _ w1' env') body ch2 ch2' h2 w rh1 (RenWsCons r w1 w1' env env' rw1 re) rc2 q))
      (values h2' w' (RunLet fns h' env' rhs body ch1' h1' w1' ch2' h2' w' p' q') rh2 rw))
    ((RunMatch _ _ _ a blocks imms v body fs env2 _ _ _ pa sel ct q)
      (let ((erased v') (erased pa') (erased rv)) (ren-atomval r env env' a v re pa))
      (let ((erased fs') (erased sel') (erased rfs)) (ren-select r h h' v v' blocks imms body fs rh rv sel))
      (let ((erased env2') (erased ct') (erased re2)) (ren-cat r fs env env2 fs' env' ct rfs re))
      (let ((erased h2') (erased w') (erased q') (erased rh2) (erased rw)) (ren-run r fns h h' env2 env2' body ch ch' h2 w rh re2 rc q))
      (values h2' w' (RunMatch fns h' env' a blocks imms v' body fs' env2' ch' h2' w' pa' sel' ct' q') rh2 rw))
    ((RunCall _ _ _ f args body ws _ _ _ pf pa q)
      (let ((erased ws') (erased pa') (erased rws)) (ren-atomvals r env env' args ws re pa))
      (let ((erased h2') (erased w') (erased q') (erased rh2) (erased rw)) (ren-run r fns h h' ws ws' body ch ch' h2 w rh rws rc q))
      (values h2' w' (RunCall fns h' env' f args body ws' ch' h2' w' pf pa' q') rh2 rw))))
