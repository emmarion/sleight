; expect: "erased erased erased 5"
(let ((many k)) 5)
(def-fns _ $ (many mult-name : (many (Mult) m) -> (many (String) s))
  (match many m _ ((MErased) "erased") ((MMany) "many") ((MUnique) "unique")))
(def-fns _ $ (many go : -> (many (String) s))
  (let ((many h)) (settled-of many k))
  (str-append (mult-name $ settled-mult _ _ _ $ settled-type _ _ _ h) $ str-append " " $
    str-append (mult-name $ settled-mult _ _ _ $ settled-erase _ _ _ h) $ str-append " " $
    str-append (mult-name $ settled-mult _ _ _ $ settled-type _ _ _ $ settled-type _ _ _ h) $ str-append " " $
    nat-str $ settled-value _ _ h))
go
