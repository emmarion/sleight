; The ring traces of the colourings of a configuration's map, after Gonthier and Werner's cfcolor.v. Load after
; cpmap.sl and red/color.sl.

(unary 4)

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

; c is a + b, the colours forming the Klein four-group of color.v with C0 its unit.
(def-adts $ (AddC : ((Col) a b c) -> Type)
  enum
  (many Add00 : -> (AddC (C0) (C0) (C0)))
  (many Add01 : -> (AddC (C0) (C1) (C1)))
  (many Add02 : -> (AddC (C0) (C2) (C2)))
  (many Add03 : -> (AddC (C0) (C3) (C3)))
  (many Add10 : -> (AddC (C1) (C0) (C1)))
  (many Add11 : -> (AddC (C1) (C1) (C0)))
  (many Add12 : -> (AddC (C1) (C2) (C3)))
  (many Add13 : -> (AddC (C1) (C3) (C2)))
  (many Add20 : -> (AddC (C2) (C0) (C2)))
  (many Add21 : -> (AddC (C2) (C1) (C3)))
  (many Add22 : -> (AddC (C2) (C2) (C0)))
  (many Add23 : -> (AddC (C2) (C3) (C1)))
  (many Add30 : -> (AddC (C3) (C0) (C3)))
  (many Add31 : -> (AddC (C3) (C1) (C2)))
  (many Add32 : -> (AddC (C3) (C2) (C1)))
  (many Add33 : -> (AddC (C3) (C3) (C0))))

(def-fns _ $ (many addc-c : (many (Col) a b) -> (many (Col) c) (erased (AddC a b c) p))
  (match many a _
    ((C0) (match many b _ ((C0) (values (C0) (Add00))) ((C1) (values (C1) (Add01))) ((C2) (values (C2) (Add02))) ((C3) (values (C3) (Add03)))))
    ((C1) (match many b _ ((C0) (values (C1) (Add10))) ((C1) (values (C0) (Add11))) ((C2) (values (C3) (Add12))) ((C3) (values (C2) (Add13)))))
    ((C2) (match many b _ ((C0) (values (C2) (Add20))) ((C1) (values (C3) (Add21))) ((C2) (values (C0) (Add22))) ((C3) (values (C1) (Add23)))))
    ((C3) (match many b _ ((C0) (values (C3) (Add30))) ((C1) (values (C2) (Add31))) ((C2) (values (C1) (Add32))) ((C3) (values (C0) (Add33)))))))

(def-fns _ $ (erased addc-comm : (erased (Col) a b c) (erased (AddC a b c) p) -> (erased (AddC b a c) q))
  (match erased p _
    ((Add00) (Add00))
    ((Add01) (Add10))
    ((Add02) (Add20))
    ((Add03) (Add30))
    ((Add10) (Add01))
    ((Add11) (Add11))
    ((Add12) (Add21))
    ((Add13) (Add31))
    ((Add20) (Add02))
    ((Add21) (Add12))
    ((Add22) (Add22))
    ((Add23) (Add32))
    ((Add30) (Add03))
    ((Add31) (Add13))
    ((Add32) (Add23))
    ((Add33) (Add33))))

(def-fns _ $ (erased addc-cancel : (erased (Col) a b c) (erased (AddC a c b) p) -> (erased (AddC a b c) q))
  (match erased p _
    ((Add00) (Add00))
    ((Add01) (Add01))
    ((Add02) (Add02))
    ((Add03) (Add03))
    ((Add10) (Add11))
    ((Add11) (Add10))
    ((Add12) (Add13))
    ((Add13) (Add12))
    ((Add20) (Add22))
    ((Add21) (Add23))
    ((Add22) (Add20))
    ((Add23) (Add21))
    ((Add30) (Add33))
    ((Add31) (Add32))
    ((Add32) (Add31))
    ((Add33) (Add30))))

(def-fns _ $ (erased addc-fn : (erased (Col) a b c c2) (erased (AddC a b c) p) (erased (AddC a b c2) q) -> (erased (Eq (Col) c c2) e))
  (match erased p _
    ((Add00) (let-match erased q (Add00)) (Refl _ c))
    ((Add01) (let-match erased q (Add01)) (Refl _ c))
    ((Add02) (let-match erased q (Add02)) (Refl _ c))
    ((Add03) (let-match erased q (Add03)) (Refl _ c))
    ((Add10) (let-match erased q (Add10)) (Refl _ c))
    ((Add11) (let-match erased q (Add11)) (Refl _ c))
    ((Add12) (let-match erased q (Add12)) (Refl _ c))
    ((Add13) (let-match erased q (Add13)) (Refl _ c))
    ((Add20) (let-match erased q (Add20)) (Refl _ c))
    ((Add21) (let-match erased q (Add21)) (Refl _ c))
    ((Add22) (let-match erased q (Add22)) (Refl _ c))
    ((Add23) (let-match erased q (Add23)) (Refl _ c))
    ((Add30) (let-match erased q (Add30)) (Refl _ c))
    ((Add31) (let-match erased q (Add31)) (Refl _ c))
    ((Add32) (let-match erased q (Add32)) (Refl _ c))
    ((Add33) (let-match erased q (Add33)) (Refl _ c))))

; (a + b) + c = a + (b + c).
(def-fns _ $ (erased addc-assoc : (erased (Col) a b c ab bc abc) (erased (AddC a b ab) p) (erased (AddC ab c abc) q) (erased (AddC b c bc) s)
    -> (erased (AddC a bc abc) r))
  (match erased p _
    ((Add00) (match erased c _ ((C0) (let-match erased q (Add00)) (let-match erased s (Add00)) (Add00)) ((C1) (let-match erased q (Add01)) (let-match erased s (Add01)) (Add01)) ((C2) (let-match erased q (Add02)) (let-match erased s (Add02)) (Add02)) ((C3) (let-match erased q (Add03)) (let-match erased s (Add03)) (Add03))))
    ((Add01) (match erased c _ ((C0) (let-match erased q (Add10)) (let-match erased s (Add10)) (Add01)) ((C1) (let-match erased q (Add11)) (let-match erased s (Add11)) (Add00)) ((C2) (let-match erased q (Add12)) (let-match erased s (Add12)) (Add03)) ((C3) (let-match erased q (Add13)) (let-match erased s (Add13)) (Add02))))
    ((Add02) (match erased c _ ((C0) (let-match erased q (Add20)) (let-match erased s (Add20)) (Add02)) ((C1) (let-match erased q (Add21)) (let-match erased s (Add21)) (Add03)) ((C2) (let-match erased q (Add22)) (let-match erased s (Add22)) (Add00)) ((C3) (let-match erased q (Add23)) (let-match erased s (Add23)) (Add01))))
    ((Add03) (match erased c _ ((C0) (let-match erased q (Add30)) (let-match erased s (Add30)) (Add03)) ((C1) (let-match erased q (Add31)) (let-match erased s (Add31)) (Add02)) ((C2) (let-match erased q (Add32)) (let-match erased s (Add32)) (Add01)) ((C3) (let-match erased q (Add33)) (let-match erased s (Add33)) (Add00))))
    ((Add10) (match erased c _ ((C0) (let-match erased q (Add10)) (let-match erased s (Add00)) (Add10)) ((C1) (let-match erased q (Add11)) (let-match erased s (Add01)) (Add11)) ((C2) (let-match erased q (Add12)) (let-match erased s (Add02)) (Add12)) ((C3) (let-match erased q (Add13)) (let-match erased s (Add03)) (Add13))))
    ((Add11) (match erased c _ ((C0) (let-match erased q (Add00)) (let-match erased s (Add10)) (Add11)) ((C1) (let-match erased q (Add01)) (let-match erased s (Add11)) (Add10)) ((C2) (let-match erased q (Add02)) (let-match erased s (Add12)) (Add13)) ((C3) (let-match erased q (Add03)) (let-match erased s (Add13)) (Add12))))
    ((Add12) (match erased c _ ((C0) (let-match erased q (Add30)) (let-match erased s (Add20)) (Add12)) ((C1) (let-match erased q (Add31)) (let-match erased s (Add21)) (Add13)) ((C2) (let-match erased q (Add32)) (let-match erased s (Add22)) (Add10)) ((C3) (let-match erased q (Add33)) (let-match erased s (Add23)) (Add11))))
    ((Add13) (match erased c _ ((C0) (let-match erased q (Add20)) (let-match erased s (Add30)) (Add13)) ((C1) (let-match erased q (Add21)) (let-match erased s (Add31)) (Add12)) ((C2) (let-match erased q (Add22)) (let-match erased s (Add32)) (Add11)) ((C3) (let-match erased q (Add23)) (let-match erased s (Add33)) (Add10))))
    ((Add20) (match erased c _ ((C0) (let-match erased q (Add20)) (let-match erased s (Add00)) (Add20)) ((C1) (let-match erased q (Add21)) (let-match erased s (Add01)) (Add21)) ((C2) (let-match erased q (Add22)) (let-match erased s (Add02)) (Add22)) ((C3) (let-match erased q (Add23)) (let-match erased s (Add03)) (Add23))))
    ((Add21) (match erased c _ ((C0) (let-match erased q (Add30)) (let-match erased s (Add10)) (Add21)) ((C1) (let-match erased q (Add31)) (let-match erased s (Add11)) (Add20)) ((C2) (let-match erased q (Add32)) (let-match erased s (Add12)) (Add23)) ((C3) (let-match erased q (Add33)) (let-match erased s (Add13)) (Add22))))
    ((Add22) (match erased c _ ((C0) (let-match erased q (Add00)) (let-match erased s (Add20)) (Add22)) ((C1) (let-match erased q (Add01)) (let-match erased s (Add21)) (Add23)) ((C2) (let-match erased q (Add02)) (let-match erased s (Add22)) (Add20)) ((C3) (let-match erased q (Add03)) (let-match erased s (Add23)) (Add21))))
    ((Add23) (match erased c _ ((C0) (let-match erased q (Add10)) (let-match erased s (Add30)) (Add23)) ((C1) (let-match erased q (Add11)) (let-match erased s (Add31)) (Add22)) ((C2) (let-match erased q (Add12)) (let-match erased s (Add32)) (Add21)) ((C3) (let-match erased q (Add13)) (let-match erased s (Add33)) (Add20))))
    ((Add30) (match erased c _ ((C0) (let-match erased q (Add30)) (let-match erased s (Add00)) (Add30)) ((C1) (let-match erased q (Add31)) (let-match erased s (Add01)) (Add31)) ((C2) (let-match erased q (Add32)) (let-match erased s (Add02)) (Add32)) ((C3) (let-match erased q (Add33)) (let-match erased s (Add03)) (Add33))))
    ((Add31) (match erased c _ ((C0) (let-match erased q (Add20)) (let-match erased s (Add10)) (Add31)) ((C1) (let-match erased q (Add21)) (let-match erased s (Add11)) (Add30)) ((C2) (let-match erased q (Add22)) (let-match erased s (Add12)) (Add33)) ((C3) (let-match erased q (Add23)) (let-match erased s (Add13)) (Add32))))
    ((Add32) (match erased c _ ((C0) (let-match erased q (Add10)) (let-match erased s (Add20)) (Add32)) ((C1) (let-match erased q (Add11)) (let-match erased s (Add21)) (Add33)) ((C2) (let-match erased q (Add12)) (let-match erased s (Add22)) (Add30)) ((C3) (let-match erased q (Add13)) (let-match erased s (Add23)) (Add31))))
    ((Add33) (match erased c _ ((C0) (let-match erased q (Add00)) (let-match erased s (Add30)) (Add33)) ((C1) (let-match erased q (Add01)) (let-match erased s (Add31)) (Add32)) ((C2) (let-match erased q (Add02)) (let-match erased s (Add32)) (Add31)) ((C3) (let-match erased q (Add03)) (let-match erased s (Add33)) (Add30))))))

; Colours of different numbers sum to a nonzero colour.
(def-fns _ $ (erased addc-apart : (erased (Nat) j k) (erased (Col) a b c) (erased (NCol j a) pa) (erased (NCol k b) pb) (erased (AddC a b c) p)
    (erased (Apart (Nat) Lt j k) ne) -> (erased (NZ c) r))
  (match erased p _
    (absurd (Add00) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne))
    ((Add01) (NZ1))
    ((Add02) (NZ2))
    ((Add03) (NZ3))
    ((Add10) (NZ1))
    (absurd (Add11) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne))
    ((Add12) (NZ3))
    ((Add13) (NZ2))
    ((Add20) (NZ2))
    ((Add21) (NZ3))
    (absurd (Add22) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne))
    ((Add23) (NZ1))
    ((Add30) (NZ3))
    ((Add31) (NZ2))
    ((Add32) (NZ1))
    (absurd (Add33) (let-match erased (ncol-inj j k a pa pb) (Refl _ _)) (apart-irrefl j ne))))

(def-fns _ $ (erased nz-apart : (erased (Nat) j k) (erased (Col) a b c) (erased (NCol j a) pa) (erased (NCol k b) pb) (erased (AddC a b c) p)
    (erased (NZ c) nz) -> (erased (Apart (Nat) Lt j k) r))
  (match erased (nat-eq j k) _
    (absurd (Equal _ _ _) (let-match erased (ncol-fn j a b pa pb) (Refl _ _))
      (match erased p _ (absurd (Add00) nz) (absurd (Add11) nz) (absurd (Add22) nz) (absurd (Add33) nz)))
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

(def-fns _ $ (erased absurd addc-self : (erased (Col) a t) (erased (AddC a a t) p) (erased (NZ t) nz) -> (erased (False) r))
  (match erased p _ (absurd (Add00) nz) (absurd (Add11) nz) (absurd (Add22) nz) (absurd (Add33) nz)))

; (a + g) + x = (a + x) + g.
(def-fns _ $ (erased addc-mid : (erased (Col) a g c x e1 h) (erased (AddC a g c) pc) (erased (AddC a x e1) px) (erased (AddC e1 g h) ph)
    -> (erased (AddC c x h) r))
  (let ((erased t) (erased pt)) (addc-c c x))
  (let ((erased gx) (erased pgx)) (addc-c g x))
  (let-match erased (addc-fn a gx t h (addc-assoc a g x c gx t pc pt pgx) (addc-assoc a x g e1 gx h px ph (addc-comm g x gx pgx))) (Refl _ _))
  pt)

; A Y step replaces the first entry e1 of a ring trace by g and h, for nonzero g and h with e1 + g = h.
(def-fns _ $ (erased cpcol-y : (erased (List (Step)) cp) (erased (List (Col)) r1) (erased (Col) e1 g h) (erased (CpCol cp (Cons (Col) e1 r1)) cc)
    (erased (AddC e1 g h) p) (erased (NZ g) ng) (erased (NZ h) nh) -> (erased (CpCol (Cons (Step) (SY) cp) (Cons (Col) g (Cons (Col) h r1))) res))
  (let ((erased nzs)) (cpcol-nz cp _ cc))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r cm))
  (let-match erased tr (MkTrace a cs1 _ ctr))
  (let-match erased nc (NCsCons ka _ rc1 _ pa nc1))
  (let-match erased ctr (CTStep _ _ x _ cs2 _ pax ctr1)
    (absurd (CTLast _ _ _ paa) (let-match erased nzs (AllNZCons _ _ nz0 _)) (addc-self a e1 paa nz0)))
  (let-match erased nc1 (NCsCons kx _ rc2 _ px1 nc2))
  (let ((erased c) (erased pc)) (addc-c a g))
  (let ((erased kc) (erased lc) (erased pkc)) (ncol-num c))
  (let ((erased acg)) (addc-cancel a c g pc))
  (let ((erased e1m) (erased f1m) (erased r1m) (erased stu) (erased n1) (erased pm1)) (ecpU-c d e f r n pm))
  (let ((erased ks1) (erased col1) (erased rr1)) (ecpU-color d kc ka e n f r e1m f1m r1m ks rc1 pm stu col rr lc
    (apart-sym ka kc (nz-apart ka kc a c g pa pkc acg ng))))
  (let ((erased e2) (erased f2) (erased r2) (erased stn) (erased n2) (erased pm2)) (ecpN-c (Succ (Succ d)) e1m f1m r1m n1 pm1))
  (let ((erased cxh)) (addc-mid a g c x e1 h pc pax p))
  (let ((erased ks2) (erased col2) (erased rr2)) (ecpN-color (Succ (Succ d)) kc kx e1m n1 f1m r1m e2 f2 r2 ks1 _ _ pm1 stn col1 rr1
    (R3Four ka kc ka kx rc2) (nz-apart kc kx c x h pkc px1 cxh nh)))
  (MkCpCol (Cons (Step) (SY) cp) (Succ (Succ (Succ (Succ d)))) e2 f2 r2 ks2 _ (Cons (Col) a (Cons (Col) c (Cons (Col) x cs2))) _
    (CmY d cp e f r e1m f1m r1m e2 f2 r2 cm stu stn) col2 rr2
    (NCsCons ka a _ _ pa (NCsCons kc c _ _ pkc (NCsCons kx x _ _ px1 nc2)))
    (MkTrace a _ _ (CTStep a a c g _ _ acg (CTStep a c x h _ _ cxh ctr1)))))

(def-fns _ $ (erased addc-0l : (erased (Col) c) -> (erased (AddC (C0) c c) r))
  (match erased c _ ((C0) (Add00)) ((C1) (Add01)) ((C2) (Add02)) ((C3) (Add03))))

(def-fns _ $ (erased addc-ii : (erased (Col) c) -> (erased (AddC c c (C0)) r))
  (match erased c _ ((C0) (Add00)) ((C1) (Add11)) ((C2) (Add22)) ((C3) (Add33))))

; (a + b) + c = (a + c) + b.
(def-fns _ $ (erased addc-swap : (erased (Col) a b c ab abc ac) (erased (AddC a b ab) p) (erased (AddC ab c abc) q) (erased (AddC a c ac) s)
    -> (erased (AddC ac b abc) r))
  (let ((erased bc) (erased pbc)) (addc-c b c))
  (let ((erased t) (erased pt)) (addc-c ac b))
  (let-match erased (addc-fn a bc abc t (addc-assoc a b c ab bc abc p q pbc) (addc-assoc a c b ac bc t s pt (addc-comm b c bc pbc))) (Refl _ _))
  pt)

; (a + x) + (x + z) = a + z.
(def-fns _ $ (erased addc-link : (erased (Col) a x z e1 e2 ee az) (erased (AddC a x e1) p) (erased (AddC x z e2) q) (erased (AddC e1 e2 ee) s)
    (erased (AddC a z az) t) -> (erased (Eq (Col) ee az) r))
  (addc-fn a z ee az (addc-assoc a x e2 e1 z ee p s (addc-cancel x e2 z q)) t))

; An H step replaces the first two entries e1, e2 of a ring trace by g and h = (e1 + e2) + g, for g, e1 + g and h nonzero.
(def-fns _ $ (erased cpcol-h : (erased (List (Step)) cp) (erased (List (Col)) r2) (erased (Col) e1 e2 ee g s1 h)
    (erased (CpCol cp (Cons (Col) e1 (Cons (Col) e2 r2))) cc) (erased (AddC e1 e2 ee) pee) (erased (AddC e1 g s1) ps1) (erased (AddC ee g h) ph)
    (erased (NZ g) ng) (erased (NZ s1) ns1) (erased (NZ h) nh) -> (erased (CpCol (Cons (Step) (SH) cp) (Cons (Col) g (Cons (Col) h r2))) res))
  (let ((erased nzs)) (cpcol-nz cp _ cc))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r cm))
  (let-match erased tr (MkTrace a cs1 _ ctr))
  (let-match erased nc (NCsCons ka _ rc1 _ pa nc1))
  (let-match erased ctr (CTStep _ _ x _ cs2 _ pax ctr1))
  (let-match erased nc1 (NCsCons kx _ rc2 _ px1 nc2))
  (let ((erased c) (erased pc)) (addc-c a g))
  (let ((erased kc) (erased lc) (erased pkc)) (ncol-num c))
  (let ((erased acg)) (addc-cancel a c g pc))
  (let ((erased e1m) (erased f1m) (erased r1m) (erased stu) (erased n1) (erased pm1)) (ecpU-c d e f r n pm))
  (let ((erased ks1) (erased col1) (erased rr1)) (ecpU-color d kc ka e n f r e1m f1m r1m ks rc1 pm stu col rr lc
    (apart-sym ka kc (nz-apart ka kc a c g pa pkc acg ng))))
  (let ((erased e2m) (erased f2m) (erased r2m) (erased stn) (erased n2) (erased pm2)) (ecpN-c (Succ (Succ d)) e1m f1m r1m n1 pm1))
  (let ((erased ks2) (erased col2) (erased rr2)) (ecpN-color (Succ (Succ d)) kc kx e1m n1 f1m r1m e2m f2m r2m ks1 _ _ pm1 stn col1 rr1
    (R3Four ka kc ka kx rc2) (nz-apart kc kx c x s1 pkc px1 (addc-mid a g c x e1 s1 pc pax ps1) ns1)))
  (let ((erased e3) (erased f3) (erased r3) (erased stn2) (erased n3) (erased pm3)) (ecpN-c (Succ (Succ (Succ (Succ d)))) e2m f2m r2m n2 pm2))
  (let ((erased d6)) (Succ (Succ (Succ (Succ (Succ (Succ d)))))))
  (match erased ctr1 _
    ((CTLast _ _ _ pxa)
      (let-match erased nc2 (NCsNil))
      (let-match erased (addc-fn a x e1 e2 pax (addc-comm x a e2 pxa)) (Refl _ _))
      (let-match erased (addc-fn e1 e1 ee (C0) pee (addc-ii e1)) (Refl _ _))
      (let-match erased (addc-fn (C0) g h g ph (addc-0l g)) (Refl _ _))
      (let ((erased ks3) (erased col3) (erased rr3)) (ecpN-color (Succ (Succ (Succ (Succ d)))) kc ka e2m n2 f2m r2m e3 f3 r3 ks2 _ _ pm2 stn2 col2 rr2
        (R3Three ka kc kx) (nz-apart kc ka c a g pkc pa (addc-comm a c g acg) ng)))
      (MkCpCol (Cons (Step) (SH) cp) d6 e3 f3 r3 ks3 _ (Cons (Col) a (Cons (Col) c (Nil (Col)))) _ (CmH d cp e f r e1m f1m r1m e2m f2m r2m e3 f3 r3 cm stu stn stn2)
        col3 rr3 (NCsCons ka a _ _ pa (NCsCons kc c _ _ pkc (NCsNil)))
        (MkTrace a _ _ (CTStep a a c g _ _ acg (CTLast a c g (addc-comm a c g acg))))))
    ((CTStep _ _ z _ cs3 _ pxz ctr2)
      (let-match erased nc2 (NCsCons kz _ rc3 _ pz1 nc3))
      (let ((erased az) (erased paz)) (addc-c a z))
      (let-match erased (addc-link a x z e1 e2 ee az pax pxz pee paz) (Refl _ _))
      (let ((erased czh)) (addc-swap a z g ee h c paz ph pc))
      (let ((erased ks3) (erased col3) (erased rr3)) (ecpN-color (Succ (Succ (Succ (Succ d)))) kc kz e2m n2 f2m r2m e3 f3 r3 ks2 _ _ pm2 stn2 col2 rr2
        (R3Four ka kc kx kz rc3) (nz-apart kc kz c z h pkc pz1 czh nh)))
      (MkCpCol (Cons (Step) (SH) cp) d6 e3 f3 r3 ks3 _ (Cons (Col) a (Cons (Col) c (Cons (Col) z cs3))) _ (CmH d cp e f r e1m f1m r1m e2m f2m r2m e3 f3 r3 cm stu stn stn2)
        col3 rr3 (NCsCons ka a _ _ pa (NCsCons kc c _ _ pkc (NCsCons kz z _ _ pz1 nc3)))
        (MkTrace a _ _ (CTStep a a c g _ _ acg (CTStep a c z h _ _ czh ctr2)))))))
