; expect: 2
; DESIGN.md sections 31 and 32: List and length; Nat comes from the prelude.
; The declarations here deliberately shadow: List, Nil and Cons are the prelude's
; own names, redeclared so that section 31's worked example stands on its own, and
; Cons's tail field is section 27's tail marker, which is the case the warning is
; most worth finding. The ; warns: lines at the end of the file are what that
; earns; the rest of the tests are clean of it. They sit at the end because each
; names a line of this file, and a directive written above the code it names moves
; that code as it is added.

(def-adts
  ((List : (Type A) -> Type)
    enum
    (many Nil : (erased Type A) -> (List A))
    (many Cons : (erased Type A) (many A head) (many (List A) tail)
       -> (List A))))

(def-lvl list-lvl)

(def-fns list-lvl $ (many length : (erased Type A) (subterm many (List A) xs) ->
    (many (Nat) n))
  (match many xs (((Nat) r))
    ((Nil a) (Zero))
    ((Cons a hd tl)
      (let ((erased p)) (prove-subterm tl xs))
      (Succ $ notail $ length A (subterm p) tl))))

(let ((many list-xs)) (Cons (Nat) (Zero) $ Cons (Nat) (Succ (Zero)) $ Nil (Nat)))

(length (Nat) list-xs)
; warns: tests/list.sl:12:4: warning: declaration of `List` shadows a previous binder
; warns: lib/prelude.sl:834:4: note: shadowed binder is here
; warns: tests/list.sl:14:5: warning: declaration of `Nil` shadows a previous binder
; warns: lib/prelude.sl:836:5: note: shadowed binder is here
; warns: tests/list.sl:15:48: warning: declaration of `tail` shadows a built-in
; warns: tests/list.sl:15:5: warning: declaration of `Cons` shadows a previous binder
; warns: lib/prelude.sl:837:5: note: shadowed binder is here
