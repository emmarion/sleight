; needs: macro_lib
; expect: "yes no"
(let ((many k)) 5)
(let ((many s)) "s")
(def-fns _ $ (many said : (erased Type A) (erased A a) (erased Type B) (erased B b) (many (Maybe $ JMEq A a B b) r) ->
    (many (String) t))
  (match many r _ ((None _) "no") ((Some _ e) "yes")))
(def-fns _ $ (many cmp-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many lit)) (intern-nat mw (nat-add 9000 1)))
  (let ((unique mw2) (many r1)) (settled-eq _ _ _ _ _ _ mw1 (settled-type _ _ _ lit) (settled-type _ _ _ (settled-of many k))))
  (let ((unique mw3) (many r2)) (settled-eq _ _ _ _ _ _ mw2 (settled-type _ _ _ lit) (settled-type _ _ _ (settled-of many s))))
  (let ((unique mw4) (many o)) (str-raw mw3 here $ str-append (said _ _ _ _ r1) $ str-append " " (said _ _ _ _ r2)))
  (values mw4 $ one o))
(let ((many cmp)) (MkMacro _ cmp-fn))
(def-fns _ $ (many f : (many (Nat) n) -> (many (String) t))
  (match many n _ ((Zero) (cmp)) ((Succ m) (cmp))))
(def-fns _ $ (many go : -> (many (String) t)) (f 2))
go
