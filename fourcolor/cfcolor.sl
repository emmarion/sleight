; The ring traces of the colourings of a configuration's map, after Gonthier and Werner's cfcolor.v. Load after
; cpmap.sl and red/color.sl.

(unary 4)

; c is a + b, the colours forming the Klein four-group of color.v with C0 its unit.
(def-adts $ (AddC : ((Col) a b c) -> Type)
  enum
  (many AddL : (erased (Col) a) -> (AddC (C0) a a))
  (many AddR : (erased (Col) a) -> (AddC a (C0) a))
  (many AddSame : (erased (Col) a) -> (AddC a a (C0)))
  (many Add12 : -> (AddC (C1) (C2) (C3)))
  (many Add21 : -> (AddC (C2) (C1) (C3)))
  (many Add13 : -> (AddC (C1) (C3) (C2)))
  (many Add31 : -> (AddC (C3) (C1) (C2)))
  (many Add23 : -> (AddC (C2) (C3) (C1)))
  (many Add32 : -> (AddC (C3) (C2) (C1))))

; c is the colour numbered k.
(def-adts $ (NCol : ((Nat) k) ((Col) c) -> Type)
  enum
  (many NC0 : -> (NCol (Zero) (C0)))
  (many NC1 : -> (NCol (Succ (Zero)) (C1)))
  (many NC2 : -> (NCol (Succ (Succ (Zero))) (C2)))
  (many NC3 : -> (NCol (Succ (Succ (Succ (Zero)))) (C3))))

(def-adts $ (NZ : ((Col) c) -> Type)
  enum
  (many NZ1 : -> (NZ (C1)))
  (many NZ2 : -> (NZ (C2)))
  (many NZ3 : -> (NZ (C3))))

(def-fns _ $ (many addc-c : (many (Col) a b) -> (many (Col) c) (erased (AddC a b c) p))
  (match many a _
    ((C0) (values b (AddL b)))
    ((C1) (match many b _ ((C0) (values a (AddR a))) ((C1) (values (C0) (AddSame a))) ((C2) (values (C3) (Add12))) ((C3) (values (C2) (Add13)))))
    ((C2) (match many b _ ((C0) (values a (AddR a))) ((C1) (values (C3) (Add21))) ((C2) (values (C0) (AddSame a))) ((C3) (values (C1) (Add23)))))
    ((C3) (match many b _ ((C0) (values a (AddR a))) ((C1) (values (C2) (Add31))) ((C2) (values (C1) (Add32))) ((C3) (values (C0) (AddSame a)))))))

(def-fns _ $ (erased addc-comm : (erased (Col) a b c) (erased (AddC a b c) p) -> (erased (AddC b a c) q))
  (match erased p _
    ((AddL _) (AddR b)) ((AddR _) (AddL a)) ((AddSame _) (AddSame a)) ((Add12) (Add21)) ((Add21) (Add12)) ((Add13) (Add31))
    ((Add31) (Add13)) ((Add23) (Add32)) ((Add32) (Add23))))

(def-fns _ $ (erased ncol-ex : (erased (Nat) k) (erased (Lt k 4) lk) -> (erased (Col) c) (erased (NCol k c) p))
  (let-match erased k (Succ k1) ((Zero) (values (C0) (NC0))))
  (let-match erased k1 (Succ k2) ((Zero) (values (C1) (NC1))))
  (let-match erased k2 (Succ k3) ((Zero) (values (C2) (NC2))))
  (let-match erased k3 (Zero)
    (absurd (Succ k4) (let-match erased lk (LtS _ _ l1)) (let-match erased l1 (LtS _ _ l2)) (let-match erased l2 (LtS _ _ l3))
      (let-match erased l3 (LtS _ _ l4)) l4))
  (values (C3) (NC3)))

(def-fns _ $ (erased ncol-num : (erased (Col) c) -> (erased (Nat) k) (erased (Lt k 4) lk) (erased (NCol k c) p))
  (match erased c _
    ((C0) (values (Zero) (LtZ _) (NC0)))
    ((C1) (values (Succ (Zero)) (LtS _ _ (LtZ _)) (NC1)))
    ((C2) (values (Succ (Succ (Zero))) (LtS _ _ (LtS _ _ (LtZ _))) (NC2)))
    ((C3) (values (Succ (Succ (Succ (Zero)))) (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))) (NC3)))))

(def-fns _ $ (erased ncol-fn : (erased (Nat) k) (erased (Col) c c2) (erased (NCol k c) p) (erased (NCol k c2) q) -> (erased (Eq (Col) c c2) e))
  (match erased p _
    ((NC0) (let-match erased q (NC0)) (Refl _ c))
    ((NC1) (let-match erased q (NC1)) (Refl _ c))
    ((NC2) (let-match erased q (NC2)) (Refl _ c))
    ((NC3) (let-match erased q (NC3)) (Refl _ c))))

(def-fns _ $ (erased ncol-inj : (erased (Nat) k j) (erased (Col) c) (erased (NCol k c) p) (erased (NCol j c) q) -> (erased (Eq (Nat) k j) e))
  (match erased p _
    ((NC0) (let-match erased q (NC0)) (Refl _ k))
    ((NC1) (let-match erased q (NC1)) (Refl _ k))
    ((NC2) (let-match erased q (NC2)) (Refl _ k))
    ((NC3) (let-match erased q (NC3)) (Refl _ k))))

; Colours of different numbers sum to a nonzero colour.
(def-fns _ $ (erased addc-apart : (erased (Nat) j k) (erased (Col) a b c) (erased (NCol j a) pa) (erased (NCol k b) pb) (erased (AddC a b c) p)
    (erased (Apart (Nat) Lt j k) ne) -> (erased (NZ c) r))
  (match erased p _
    (absurd (AddSame _) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne))
    ((AddL _) (match erased b _ (absurd (C0) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne)) ((C1) (NZ1)) ((C2) (NZ2)) ((C3) (NZ3))))
    ((AddR _) (match erased a _ (absurd (C0) (let-match erased (ncol-inj j k b pa pb) (Refl _ _)) (apart-irrefl j ne)) ((C1) (NZ1)) ((C2) (NZ2)) ((C3) (NZ3))))
    ((Add12) (NZ3)) ((Add21) (NZ3)) ((Add13) (NZ2)) ((Add31) (NZ2)) ((Add23) (NZ1)) ((Add32) (NZ1))))

(def-fns _ $ (erased addc-cancel : (erased (Col) a b c) (erased (AddC a c b) p) -> (erased (AddC a b c) q))
  (match erased p _
    ((AddL _) (AddL c)) ((AddR _) (AddSame a)) ((AddSame _) (AddR a)) ((Add12) (Add13)) ((Add21) (Add23)) ((Add13) (Add12))
    ((Add31) (Add32)) ((Add23) (Add21)) ((Add32) (Add31))))

(def-fns _ $ (erased nz-apart : (erased (Nat) j k) (erased (Col) a b c) (erased (NCol j a) pa) (erased (NCol k b) pb) (erased (AddC a b c) p)
    (erased (NZ c) nz) -> (erased (Apart (Nat) Lt j k) r))
  (match erased (nat-eq j k) _
    (absurd (Equal _ _ _) (let-match erased (ncol-fn j a b pa pb) (Refl _ _))
      (match erased p _ (absurd (AddL _) nz) (absurd (AddR _) nz) (absurd (AddSame _) nz)))
    ((Unequal _ _ _ _ ne) ne)))

; cs are the colours numbered ns.
(def-adts $ (NCols : ((List (Nat)) ns) ((List (Col)) cs) -> Type)
  enum
  (many NCsNil : -> (NCols (Nil (Nat)) (Nil (Col))))
  (many NCsCons : (erased (Nat) k) (erased (Col) c) (erased (List (Nat)) ns) (erased (List (Col)) cs) (erased (NCol k c) p) (erased (NCols ns cs) rest)
      -> (NCols (Cons (Nat) k ns) (Cons (Col) c cs))))

; et sums each colour of x :: cs with the next one, and the last with c0.
(def-adts $ (CTr : ((Col) c0 x) ((List (Col)) cs et) -> Type)
  enum
  (many CTLast : (erased (Col) c0 x t) (erased (AddC x c0 t) p) -> (CTr c0 x (Nil (Col)) (Cons (Col) t (Nil (Col)))))
  (many CTStep : (erased (Col) c0 x y t) (erased (List (Col)) cs et) (erased (AddC x y t) p) (erased (CTr c0 y cs et) rest)
      -> (CTr c0 x (Cons (Col) y cs) (Cons (Col) t et))))

; Gonthier's trace of the colours of a ring.
(def-adts $ (Trace : ((List (Col)) cs et) -> Type)
  enum
  (many MkTrace : (erased (Col) c) (erased (List (Col)) cs et) (erased (CTr c c cs et) p) -> (Trace (Cons (Col) c cs) et)))

; et is the ring trace of a colouring of the map of cp (ring_trace of cfcolor.v).
(def-adts $ (CpCol : ((List (Step)) cp) ((List (Col)) et) -> Type)
  enum
  (many MkCpCol : (erased (List (Step)) cp) (erased (Nat) d) (erased (List (Nat)) e f r ks rc) (erased (List (Col)) cs et) (erased (Cpmap cp d e f r) c)
      (erased (FourColoring e f ks) col) (erased (Respects ks r rc) rr) (erased (NCols rc cs) nc) (erased (Trace cs et) tr) -> (CpCol cp et)))

; A U step adds two entries c, for any nonzero c, in front of a ring trace.
(def-fns _ $ (erased cpcol-u : (erased (List (Step)) cp) (erased (List (Col)) et) (erased (Col) c) (erased (CpCol cp et) cc) (erased (NZ c) nz)
    -> (erased (CpCol (Cons (Step) (SU) cp) (Cons (Col) c (Cons (Col) c et))) r))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r cm))
  (let ((erased e2) (erased f2) (erased r2) (erased st) (erased n2) (erased pm2)) (ecpU-c d e f r n pm))
  (let-match erased tr (MkTrace a cs1 _ ctr))
  (let-match erased nc (NCsCons ka _ rc1 _ pa nc1))
  (let ((erased b) (erased pb)) (addc-c a c))
  (let ((erased kb) (erased lb) (erased pkb)) (ncol-num b))
  (let ((erased ab)) (addc-cancel a b c pb))
  (let ((erased ks2) (erased col2) (erased rr2)) (ecpU-color d kb ka e n f r e2 f2 r2 ks rc1 pm st col rr lb
    (apart-sym ka kb (nz-apart ka kb a b c pa pkb ab nz))))
  (MkCpCol (Cons (Step) (SU) cp) (Succ (Succ d)) e2 f2 r2 ks2 _ (Cons (Col) a (Cons (Col) b (Cons (Col) a cs1))) _ (CmU d cp e f r e2 f2 r2 cm st) col2 rr2
    (NCsCons ka a _ _ pa (NCsCons kb b _ _ pkb nc))
    (MkTrace a _ _ (CTStep a a b c _ _ ab (CTStep a b a c _ _ (addc-comm a b c ab) ctr)))))

(def-adts $ (AllNZ : ((List (Col)) et) -> Type)
  enum
  (many AllNZNil : -> (AllNZ (Nil (Col))))
  (many AllNZCons : (erased (Col) c) (erased (List (Col)) et) (erased (NZ c) p) (erased (AllNZ et) rest) -> (AllNZ (Cons (Col) c et))))

; Darts a node apart have different colours.
(def-fns _ $ (erased node-color : (erased (Nat) d u v ku kv) (erased (List (Nat)) e n f ks) (erased (Hypermap d e n f) h) (erased (FourColoring e f ks) col)
    (erased (Nth (Nat) n v u) pn) (erased (Nth (Nat) ks u ku) pu) (erased (Nth (Nat) ks v kv) pv) -> (erased (Apart (Nat) Lt ku kv) r))
  (let ((erased w) (erased pw) (erased pf)) (hyper-back d u v e n f h pn))
  (let-match erased col (MkFourColoring _ _ _ ke face ce edge _))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased lu)) (nth-lt-length _ e u d w pw le))
  (let ((erased l) (erased pl)) (nth-exists _ ke d u (respects-length ks e ke d ce le) lu))
  (let ((erased pwl)) (respects-nth ks e ke u w l ce pw pl))
  (let-match erased (nth-fn _ ks v kv l pv (respects-nth ks f ks w v l face pf pwl)) (Refl _ _))
  (apart-sym kv ku (differ-nth ke ks u kv ku edge pl pu)))

(def-fns _ $ (erased trace-nz : (erased (Nat) d u y ku ky k0) (erased (List (Nat)) e n f ks p rcp) (erased (Col) x c0) (erased (List (Col)) csp et)
    (erased (Hypermap d e n f) h) (erased (FourColoring e f ks) col) (subterm erased (RPath n u p y) rp) (erased (Nth (Nat) ks u ku) pu)
    (erased (NCol ku x) px) (erased (Respects ks p rcp) rr) (erased (NCols rcp csp) nc) (erased (CTr c0 x csp et) ct) (erased (NCol k0 c0) p0)
    (erased (Nth (Nat) ks y ky) py) (erased (Apart (Nat) Lt ky k0) last) -> (erased (AllNZ et) r))
  (match erased rp _
    ((RPNil _ _)
      (let-match erased rr (RespNil _))
      (let-match erased nc (NCsNil))
      (let-match erased ct (CTLast _ _ t pt))
      (let-match erased (nth-fn _ ks u ku ky pu py) (Refl _ _))
      (AllNZCons t (Nil (Col)) (addc-apart ku k0 x c0 t px p0 pt last) (AllNZNil)))
    ((RPCons _ p1 _ z _ pz rp1)
      (let-match erased rr (RespCons _ _ rc1 _ kz pkz rr1))
      (let-match erased nc (NCsCons _ cz _ cs1 pcz nc1))
      (let-match erased ct (CTStep _ _ _ t _ et1 pt ct1))
      (AllNZCons t et1 (addc-apart ku kz x cz t px pcz pt (node-color d u z ku kz e n f ks h col pz pu pkz))
        (trace-nz d z y kz ky k0 e n f ks p1 rc1 cz c0 cs1 et1 h col rp1 pkz pcz rr1 nc1 ct1 p0 py last)))))

; A ring trace has no zero (memc0_trace_cpring).
(def-fns _ $ (erased cpcol-nz : (erased (List (Step)) cp) (erased (List (Col)) et) (erased (CpCol cp et) cc) -> (erased (AllNZ et) r))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r cm))
  (let-match erased pm (MkPointedMap _ _ _ _ _ h cr))
  (let-match erased cr (MkCpring _ p a y rp back dp))
  (let-match erased tr (MkTrace c cs1 _ ctr))
  (let-match erased rr (RespCons _ _ rc1 _ ka pka rr1))
  (let-match erased nc (NCsCons _ _ _ _ pc nc1))
  (let-match erased col (MkFourColoring _ _ _ ke face ce edge four))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased lk)) (respects-length ks f ks d face lf))
  (let ((erased nf) (erased ni) (erased fi) (erased _) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased ky) (erased py)) (nth-exists _ ks d y lk (perm-val d a y n ni pn back)))
  (trace-nz d a y ka ky ka e n f ks p rc1 c c cs1 et h col rp pka pc rr1 nc1 ctr pc py (node-color d y a ky ka e n f ks h col back py pka)))
