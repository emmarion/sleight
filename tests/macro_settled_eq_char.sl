; needs: ../std/macro macro_lib
; expect: "no yes"
(def-fns _ $ (many said : (erased Type A) (erased A a) (erased Type B) (erased B b) (many (Maybe $ JMEq A a B b) r) ->
    (many (String) t))
  (match many r _ ((None _) "no") ((Some _ _) "yes")))
(comptime-match many (lt-dec 97 u8-modulus) (Yes a b q))
(let ((many fresh)) (MkChar $ MkU8 97 q))
(comptime-match many #\a (MkChar u))
(comptime-match many u (MkU8 n p))
(let ((many own)) (MkChar $ MkU8 n p))
(def-fns _ $ (many cmp-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many c)) (intern-char mw #\a))
  (let ((unique mw2) (many r1)) (settled-eq _ _ _ _ _ _ mw1 c (settled-of many fresh)))
  (let ((unique mw3) (many r2)) (settled-eq _ _ _ _ _ _ mw2 c (settled-of many own)))
  (let ((unique mw4) (many o)) (str-raw mw3 here $ str-append (said _ _ _ _ r1) $ str-append " " (said _ _ _ _ r2)))
  (values mw4 $ Cons _ o $ Nil _))
(let ((many cmp)) (MkMacro _ cmp-fn))
(cmp)
