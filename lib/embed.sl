; The files of lib/ that slc embeds, each read when slc is compiled. self/header.sl adds self/runtime.ml.
(let ((erased string-type)) (String))

(def-fns _ $ (many embed-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many usage)) (RawList here $ Cons _ (RawSymbol here $ SName "compile-error") $ Nil _))
  (let-match many args (Cons _ a _) ((Nil _) (values mw $ Cons _ usage $ Nil _)))
  (let-match many a (RawSettled _ _ _ _ c) (else (values mw $ Cons _ usage $ Nil _)))
  (let-match many (settled-mult _ _ _ c) (MMany) (else (values mw $ Cons _ usage $ Nil _)))
  (let ((unique mw1) (many e)) (settled-eq _ _ _ _ _ _ mw (settled-type _ _ _ c) (settled-of erased string-type)))
  (let-match many e (Some _ j) ((None _) (values mw1 $ Cons _ usage $ Nil _)))
  (let-match erased j (JMRefl _ _))
  (let ((unique mw2) (many r)) (read-file mw1 here $ settled-value _ _ c))
  (let ((many text)) $ match many r (((String) _)) ((Ok _ s) s) ((Fail _ msg) msg))
  (let ((unique mw3) (many h)) (intern-string mw2 text))
  (let ((many lit)) (RawSettled here _ _ _ h))
  (match many r _
    ((Ok _ _) (values mw3 $ Cons _ lit $ Nil _))
    ((Fail _ _) (values mw3 $ Cons _ (RawList here $ Cons _ (RawSymbol here $ SName "compile-error") $ Cons _ lit $ Nil _) $ Nil _))))

(let ((many embed)) (MkMacro _ embed-fn))

(let ((many ffi-core)) (embed "ffi_core.ml"))
(let ((many driver-core)) (embed "driver_core.ml"))
(let ((many extern-templates)) (embed "ffi_templates.txt"))
(let ((many specials-help)) (embed "specials.txt"))
(let ((many prelude-source)) (embed "prelude.sl"))
