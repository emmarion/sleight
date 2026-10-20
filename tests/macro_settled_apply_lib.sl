; needs: ../std/macro
(def-adts $ (NatH : -> Type)
  enum
  (many MkNatH : (erased (Nat) n) (many (Settled (MMany) (Nat) n) h) -> (NatH)))

(def-fns _ $ (many arg-nat-h : (unique (MacroWorld) mw) (many (Raw) r) ->
    (unique (MacroWorld) mw2 at mw) (many (Maybe (NatH)) v))
  (let-match many r (RawSettled _ _ _ _ c) (else (values mw (None _))))
  (let-match many (settled-mult _ _ _ c) (MMany) (else (values mw (None _))))
  (let ((unique mw1) (many e)) (settled-eq _ _ _ _ _ _ mw (settled-type _ _ _ c) (settled-of erased nat-type)))
  (let-match many e (Some _ j) ((None _) (values mw1 (None _))))
  (let-match erased j (JMRefl _ _))
  (values mw1 (Some _ $ MkNatH _ c)))

(def-fns _ $ (many two-nats : (unique (MacroWorld) mw) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (Maybe $ Pair (NatH) (NatH)) r))
  (let-match many args (Cons _ ra r1) ((Nil _) (values mw (None _))))
  (let-match many r1 (Cons _ rb r2) ((Nil _) (values mw (None _))))
  (let-match many r2 (Nil _) ((Cons _ _ _) (values mw (None _))))
  (let ((unique mw1) (many ma)) (arg-nat-h mw ra))
  (let-match many ma (Some _ ha) ((None _) (values mw1 (None _))))
  (let ((unique mw2) (many mb)) (arg-nat-h mw1 rb))
  (let-match many mb (Some _ hb) ((None _) (values mw2 (None _))))
  (values mw2 (Some _ $ MkPair _ _ ha hb)))

(def-fns _ $ (many lit-lt-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many m)) (two-nats mw args))
  (let-match many m (Some _ ab) ((None _) (macro-fail mw1 here "`lit-lt` takes two numerals")))
  (let-match many ab (MkPair _ _ ha hb))
  (let-match many ha (MkNatH _ ca))
  (let-match many hb (MkNatH _ cb))
  (let-match many (lt-dec (settled-value _ _ ca) (settled-value _ _ cb)) (Yes _ _ p)
    ((No _ _ _) (macro-fail mw1 here "`lit-lt`: not below")))
  (let ((unique mw2) (many rt)) (settled-ty-apply mw1 (settled-of erased Lt) (settled-erase _ _ _ ca) (settled-erase _ _ _ cb)))
  (let-match many rt (Some _ th) ((None _) (macro-fail mw2 here "`lit-lt`: `Lt` does not apply")))
  (let ((unique mw3) (many hp)) (mint-settled-erased mw2 _ th p))
  (values mw3 $ one $ RawSettled here _ _ _ hp))
(let ((many lit-lt)) (MkMacro _ lit-lt-fn))

(def-fns _ $ (many pair-of-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many m)) (two-nats mw args))
  (let-match many m (Some _ ab) ((None _) (macro-fail mw1 here "`pair-of` takes two numerals")))
  (let-match many ab (MkPair _ _ ha hb))
  (let-match many ha (MkNatH _ ca))
  (let-match many hb (MkNatH _ cb))
  (let ((many nat-h)) (settled-of erased nat-type))
  (let ((unique mw2) (many r)) (settled-val-apply mw1 (settled-of many MkPair) nat-h nat-h ca cb))
  (let-match many r (Some _ p-h) ((None _) (macro-fail mw2 here "`MkPair` does not apply")))
  (let ((unique mw3) (many r2)) (settled-ty-apply mw2 (settled-of erased List) (settled-type _ _ _ p-h)))
  (let-match many r2 (Some _ lt-h) ((None _) (macro-fail mw3 here "`List` does not apply")))
  (let ((unique mw4) (many l-h)) (mint-settled mw3 _ lt-h (Cons _ (settled-value _ _ p-h) $ Nil _)))
  (values mw4 $ two (RawSettled here _ _ _ p-h) (RawSettled here _ _ _ l-h)))
(let ((many pair-of)) (MkMacro _ pair-of-fn))

(def-fns _ $ (many succ-of-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many args (Cons _ ra _) ((Nil _) (macro-fail mw here "`succ-of` takes a numeral")))
  (let ((unique mw1) (many ma)) (arg-nat-h mw ra))
  (let-match many ma (Some _ ha) ((None _) (macro-fail mw1 here "`succ-of` takes a numeral")))
  (let-match many ha (MkNatH _ ca))
  (let ((unique mw2) (many r)) (settled-val-apply mw1 (settled-of many Succ) ca))
  (let-match many r (Some _ h) ((None _) (macro-fail mw2 here "`Succ` does not apply")))
  (values mw2 $ one $ RawSettled here _ _ _ h))
(let ((many succ-of)) (MkMacro _ succ-of-fn))

(def-adts $ (Same : ((Nat) a) -> Type)
  enum
  (many MkSame : (erased (Nat) a) (erased a is b) -> (Same a)))

(def-fns _ $ (many same-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many nat-h)) (settled-of erased nat-type))
  (let ((unique mw1) (many x)) (mint-settled mw _ nat-h 5))
  (let ((unique mw2) (many y)) (mint-settled mw1 _ nat-h 5))
  (let-match many (nat-cmp (settled-value _ _ x) (settled-value _ _ y)) (CEq _ _ _) (else (macro-fail mw2 here "not equal")))
  (let ((unique mw3) (many r)) (settled-val-apply mw2 (settled-of erased MkSame) (settled-erase _ _ _ x) (settled-erase _ _ _ y)))
  (let-match many r (Some _ _) ((None _) (macro-fail mw3 here "`MkSame` checks where it is written and not where it runs")))
  (macro-fail mw3 here "minted"))
(let ((many same)) (MkMacro _ same-fn))
