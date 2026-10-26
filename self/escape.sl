(def-fns _ $ (many escape-letter : (many (Nat) k) -> (many (Nat) e))
  (let-match many (nat-eqb k 34) (BFalse) ((BTrue) 34))
  (let-match many (nat-eqb k 92) (BFalse) ((BTrue) 92))
  (let-match many (nat-eqb k 10) (BFalse) ((BTrue) 110))
  (match many (nat-eqb k 9) _ ((BTrue) 116) ((BFalse) 0)))

(def-fns _ $ (many escape-width : (many (Nat) k) -> (many (Nat) w))
  (let-match many (nat-eqb (escape-letter k) 0) (BTrue) ((BFalse) 2))
  (match many (and (nat-lt 31 k) (nat-lt k 127)) _ ((BTrue) 1) ((BFalse) 4)))

(def-fns _ $ (many escape-byte : (many (Nat) k) (many (Nat) w) (many (Nat) d) -> (many (Nat) c))
  (let-match many (nat-eqb w 1) (BFalse) ((BTrue) k))
  (let-match many (nat-eqb d 0) (BFalse) ((BTrue) 92))
  (let-match many (nat-eqb w 2) (BFalse) ((BTrue) (escape-letter k)))
  (let-match many (nat-eqb d 1) (BFalse) ((BTrue) 120))
  (let ((many hi) (many lo) (erased _) (erased _) (erased _) (erased _)) (divmod k 16 sixteen-positive))
  (hex-code $ match many (nat-eqb d 2) _ ((BTrue) hi) ((BFalse) lo)))

(def-fns _ $ (erased append-nil-right : (subterm erased (String) s) -> (erased (Append s (SNil) s) p))
  (match erased s _
    ((SNil) (AppNil (SNil)))
    ((SCons c t) (AppCons c t (SNil) t (append-nil-right t)))))

(def-fns _ $ (erased append-unique : (erased (String) a b t u s) (erased (Nat) i)
    (subterm erased (Append a t s) p) (erased (StrLength a i) la) (erased (Append b u s) q) (erased (StrLength b i) lb) ->
    (erased (Eq (String) t u) e))
  (match erased p _
    ((AppNil _)
      (let-match erased la (SLenNil))
      (let-match erased lb (SLenNil))
      (let-match erased q (AppNil _))
      (Refl _ t))
    ((AppCons _ a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let-match erased lb (SLenCons _ b1 _ lb1))
      (let-match erased q (AppCons _ _ _ _ q1))
      (append-unique a1 b1 t u s1 i1 p1 la1 q1 lb1))))

(def-fns _ $ (erased append-snoc : (erased (String) a t s) (erased (Char) c) (erased (Nat) i)
    (subterm erased (Append a (SCons c t) s) p) (erased (StrLength a i) la) ->
    (erased (String) a2) (erased (Append a2 t s) q) (erased (StrLength a2 (Succ i)) la2))
  (match erased p _
    ((AppNil _)
      (let-match erased la (SLenNil))
      (values (SCons c (SNil)) (AppCons c (SNil) t t (AppNil t)) (SLenCons c (SNil) (Zero) (SLenNil))))
    ((AppCons d a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let ((erased a3) (erased q1) (erased l1)) (append-snoc a1 t s1 c i1 p1 la1))
      (values (SCons d a3) (AppCons d a3 t s1 q1) (SLenCons d a3 (Succ i1) l1)))))

(def-fns _ $ (erased prefix-lt : (erased (String) a t s) (erased (Nat) i len)
    (subterm erased (Append a t s) p) (erased (StrLength a i) la) (erased (StrLength s len) ls) ->
    (erased (Lt i (Succ len)) lt))
  (match erased p _
    ((AppNil _) (let-match erased la (SLenNil)) (LtZ len))
    ((AppCons _ a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let-match erased ls (SLenCons _ _ len1 ls1))
      (LtS i1 (Succ len1) (prefix-lt a1 t s1 i1 len1 p1 la1 ls1)))))

(def-fns _ $ (erased add-shift : (erased (Nat) a b c) (subterm erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (match erased p _
    ((AddZero _) (AddSucc (Zero) b b (AddZero b)))
    ((AddSucc a1 _ c1 p1) (AddSucc (Succ a1) b c1 (add-shift a1 b c1 p1)))))

(def-fns _ $ (many width-rope : (subterm many (Nat) k) (many (Rope) acc) -> (many (Rope) r))
  (let-match many k (Succ k1) ((Zero) acc))
  (tail $ width-rope k1 $ RCat (RChar $ char-of-code $ escape-width k1) acc))

(let ((many escape-widths)) (rope-str $ width-rope u8-modulus $ REmpty))
(let ((many widths-len) (erased widths-sl)) (str-length escape-widths))
(comptime-match many (nat-eq widths-len u8-modulus) (Equal _ _ _))

(def-adts $ (EscW : ((Nat) k) ((Nat) w) -> Type)
  enum
  (many MkEscW : (erased (Nat) k) (erased (Nat) w) (erased (Lt w u8-modulus) q) (erased (String) a) (erased (String) b)
     (erased (Append a (SCons (MkChar (MkU8 w q)) b) escape-widths) p) (erased (StrLength a k) la) -> (EscW k w)))

(def-fns _ $ (many esc-width-of : (many (Nat) k) (erased (Lt k u8-modulus) q) -> (many (Nat) w) (erased (EscW k w) e))
  (let ((many c) (erased a) (erased b) (erased p) (erased la)) (str-get escape-widths k u8-modulus widths-sl q))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 w lt))
  (values w (MkEscW k w lt a b p la)))

(def-fns _ $ (erased esc-w-fn : (erased (Nat) k v w) (erased (EscW k v) e) (erased (EscW k w) f) -> (erased (Eq (Nat) v w) r))
  (let-match erased e (MkEscW _ _ _ a _ p la))
  (let-match erased f (MkEscW _ _ _ a2 _ p2 la2))
  (let-match erased (append-unique a a2 _ _ escape-widths k p la p2 la2) (Refl _ _))
  (Refl _ v))

(def-adts $ (EscWidth : ((String) t) ((Nat) n) -> Type)
  enum
  (many EWNil : -> (EscWidth (SNil) (Zero)))
  (many EWCons : (erased (Nat) k) (erased (Lt k u8-modulus) q) (erased (String) t) (erased (Nat) w) (erased (Nat) r) (erased (Nat) n)
     (erased (EscW k w) e) (erased (EscWidth t r) rest) (erased (Add w r n) ad)
     -> (EscWidth (SCons (MkChar (MkU8 k q)) t) n)))

(def-fns _ $ (many escaped-width : (many (String) s) (erased (Nat) len) (erased (StrLength s len) ls)
    (subterm many (Nat) i) (erased (String) a t) (erased (Append a t s) p) (erased (StrLength a i) la)
    (many (Nat) acc) (erased (EscWidth t acc) e) ->
    (many (Nat) n) (erased (EscWidth s n) f))
  (let-match many i (Succ i1)
    ((Zero) (let-match erased la (SLenNil)) (let-match erased p (AppNil _)) (values acc e)))
  (let-match erased (prefix-lt a t s i len p la ls) (LtS _ _ lt))
  (let ((many c) (erased a2) (erased b) (erased p2) (erased la2)) (str-get s i1 len ls lt))
  (let ((erased a3) (erased p3) (erased la3)) (append-snoc a2 b s c i1 p2 la2))
  (let-match erased (append-unique a3 a b t s i p3 la3 p la) (Refl _ _))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k q))
  (let ((many w) (erased ew)) (esc-width-of k q))
  (let ((many acc2) (erased ad)) (add w acc))
  (tail $ escaped-width s len ls i1 a2 (SCons c b) p2 la2 acc2 (EWCons k q b w acc acc2 ew e ad)))

(def-fns _ $ (many put-bytes : (many (Nat) k) (many (Nat) w) (subterm many (Nat) left) (many (Nat) d)
    (erased (Nat) rest rr m) (erased (Add left rest rr) al)
    (erased (List (U8)) xs) (erased (Length (U8) xs (Succ m)) l) (unique (Bytes xs) b) (many (Nat) j) (erased (Add j rr m) aj) ->
    (erased (List (U8)) ys) (erased (Length (U8) ys (Succ m)) l2) (unique (Bytes ys) r at b) (many (Nat) j2) (erased (Add j2 rest m) aj2))
  (let-match many left (Succ left1) ((Zero) (let-match erased al (AddZero _)) (values xs l b j aj)))
  (let-match erased al (AddSucc _ _ rr1 al1))
  (let ((erased x) (erased nth)) (nth-exists _ xs (Succ m) j l (add-le-left j rr m aj)))
  (let-match many (char-of-code $ escape-byte k w d) (MkChar u))
  (let ((erased ys) (unique b2) (erased sp)) (bytes-set _ b j u x nth))
  (tail $ put-bytes k w left1 (Succ d) rest rr1 m al1 ys (setnth-length _ xs j (Succ m) u ys sp l) b2 (Succ j) (add-shift j rr1 m aj)))

(def-fns _ $ (many escape-into : (many (String) s) (erased (Nat) len) (erased (StrLength s len) ls)
    (subterm many (Nat) left) (many (Nat) i) (erased (String) a t) (erased (Append a t s) p) (erased (StrLength a i) la)
    (erased (StrLength t left) lst) (erased (Nat) rr m) (erased (EscWidth t rr) e)
    (erased (List (U8)) xs) (erased (Length (U8) xs (Succ m)) l) (unique (Bytes xs) b) (many (Nat) j) (erased (Add j rr m) aj) ->
    (erased (List (U8)) ys) (unique (Bytes ys) r at b))
  (let-match many left (Succ left1) ((Zero) (values xs b)))
  (let-match erased lst (SLenCons c0 t1 _ lst1))
  (let ((erased a2) (erased p2) (erased la2)) (append-snoc a t1 s c0 i p la))
  (let-match erased (prefix-lt a2 t1 s (Succ i) len p2 la2 ls) (LtS _ _ lt))
  (let ((many c) (erased a3) (erased b3) (erased p3) (erased la3)) (str-get s i len ls lt))
  (let-match erased (append-unique a3 a (SCons c b3) t s i p3 la3 p la) (Refl _ _))
  (let-match erased e (EWCons k _ _ w rest _ ew e1 ad))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k2 q2))
  (let ((many w2) (erased ew2)) (esc-width-of k2 q2))
  (let-match erased (esc-w-fn k w w2 ew ew2) (Refl _ _))
  (let ((erased ys) (erased l2) (unique b2) (many j2) (erased aj2)) (put-bytes k2 w2 w2 0 rest rr m ad xs l b j aj))
  (tail $ escape-into s len ls left1 (Succ i) a2 t1 p2 la2 lst1 rest m e1 ys l2 b2 j2 aj2))

(def-fns _ $ (many lit-string : (many (String) s) -> (many (String) r))
  (let ((many len) (erased ls)) (str-length s))
  (let ((many total) (erased e)) (escaped-width s len ls len s (SNil) (append-nil-right s) ls (Zero) (EWNil)))
  (let ((many n)) (Succ (Succ total)))
  (let-match many (char-of-code 34) (MkChar quote))
  (let ((erased xs) (unique b) (erased rp)) (bytes-make n quote))
  (let ((erased _) (unique b2))
    (escape-into s len ls len (Zero) (SNil) s (AppNil s) (SLenNil) ls total (Succ total) e
      xs (repeat-length _ n quote xs rp) b (Succ (Zero)) (AddSucc (Zero) total total (AddZero total))))
  (let ((many c)) (share b2))
  (let ((many r) (erased _)) (bytes-str _ c))
  r)

(def-fns _ $ (many spell-text : (many (String) s) -> (many (String) r))
  (match many (is-plain-name s) _ ((BTrue) s) ((BFalse) (rope-str $ rcat (RStr "#") $ RStr $ lit-string s))))

(def-fns _ $ (many spell-name : (many (Name) n) -> (many (String) r))
  (match many n _
    ((NSrc s) (spell-text s))
    ((NGen k s) (str-cat3 "__g" (nat-str k) $ str-cat "_" $ spell-text s))
    ((NHandle _ _ _ s) s)))

(def-fns _ $ (many name-text : (many (Name) n) -> (many (String) r))
  (match many n _ ((NSrc s) s) (else (spell-name n))))
