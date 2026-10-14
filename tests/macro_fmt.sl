; needs: ../std/macro macro_fmt_lib
; expect: (MkPair _ _ "ann has 3 apples (~50%)" $ MkPair _ _ "<7><8>" "")
(def-fns _ $ (many show : (many (Nat) x) (many (String) who) -> (many (String) s))
  ((fmt "~s has ~n apples (~~~n%)") who x 50))
(def-fns _ $ (many twice : (many (Nat) x) -> (many (String) s))
  (let ((many line)) (fmt "<~n>"))
  (str-append (line x) (line $ nat-add x 1)))
(MkPair _ _ (show 3 "ann") $ MkPair _ _ (twice 7) ((fmt "") ))
