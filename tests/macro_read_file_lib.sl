; needs: ../std/macro macro_lib
(let ((erased string-type)) (String))
(def-fns _ $ (many arg-str : (unique (MacroWorld) mw) (many (List $ Raw) args) -> (unique (MacroWorld) mw2 at mw) (many (String) s))
  (let-match many args (Cons _ r _) ((Nil _) (values mw "")))
  (let-match many r (RawSettled _ _ _ _ c) (else (values mw "")))
  (let-match many (settled-mult _ _ _ c) (MMany) (else (values mw "")))
  (let ((unique mw1) (many e)) (settled-eq _ _ _ _ _ _ mw (settled-type _ _ _ c) (settled-of erased string-type)))
  (let-match many e (Some _ j) ((None _) (values mw1 "")))
  (let-match erased j (JMRefl _ _))
  (values mw1 $ settled-value _ _ c))
(def-fns _ $ (many read-at : (unique (MacroWorld) mw) (many (Pos) here) (many (Pos) from) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many path)) (arg-str mw args))
  (let ((unique mw2) (many r)) (read-file mw1 from path))
  (let ((many text)) $ match many r (((String) _)) ((Ok _ s) s) ((Fail _ m) (str-append "Fail: " m)))
  (let ((unique mw3) (many o)) (str-raw mw2 here text))
  (values mw3 $ one o))
(def-fns _ $ (many include-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (read-at mw here here args))
(let ((many include)) (MkMacro _ include-fn))
(def-fns _ $ (many include-nowhere-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (read-at mw here (NoPos) args))
(let ((many include-nowhere)) (MkMacro _ include-nowhere-fn))
(def-fns _ $ (many include-elsewhere-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (read-at mw here (MkPos "elsewhere.sl" 1 1) args))
(let ((many include-elsewhere)) (MkMacro _ include-elsewhere-fn))
