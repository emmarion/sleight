; needs: ../std/macro macro_lib
; error: type mismatch: expected `(List (Nat))`, got `(Nat)`
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many typed-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw9) (many lit)) (nat-raw mw here 3))
  (values mw9 $ one $ form here $ three (name here "let") (form here $ one $ form here $ three (name here "many") (RawSettled here _ _ _ (settled-type _ _ _ (settled-of many xs))) (name here "n")) lit))
(let ((many typed)) (MkMacro _ typed-fn))
(typed)
