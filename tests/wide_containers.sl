; needs: ../std/macro wide_lib
; expect: (Cons _ 5 $ Cons _ 5 $ Cons _ 6 $ Cons _ 7 $ Nil _)
; Values of a type past OCaml's block tags under a newtype and its coercions, and inside a list and an
; array, which hold them as any other word.
(def-adts $ (Wd : -> Type)
  enum
  (wide ctors Wd Wv 247 1 (Nat)))

(def-adts $ (Wrap : -> Type)
  enum newtype
  (many MkWrap : (many (Wd) w) -> (Wrap)))

(def-fns _ $ (many field : (many (Wd) x) -> (many (Nat) r))
  (match many x _ ((Wv246 n) n) ((Wv0 n) n) (else 0)))

(def-fns _ $ (many sum : (subterm many (List (Wd)) xs) -> (many (Nat) r))
  (match many xs _ ((Nil _) 0) ((Cons _ x rest) (nat-add (field x) $ notail $ sum rest))))

(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (let ((many x)) (Wv246 5))
  (let ((many w)) (coerce x (coercible-wrap (Shared) MkWrap x)))
  (let-match many w (MkWrap y))
  (let ((many back)) (coerce w (coercible-sym (coercible-wrap (Shared) MkWrap x))))
  (let ((many a)) (ACons _ _ (Wv0 3) (ACons _ _ (Wv246 4) (ANil (Wd)))))
  (let ((many p)) (array-get-many _ _ a (Zero) _ (NthHere _ _ _)))
  (let ((many q)) (array-get-many _ _ a (Succ (Zero)) _ (NthThere _ _ _ _ _ (NthHere _ _ _))))
  (Cons _ (field y) $ Cons _ (field back) $ Cons _ (sum $ Cons _ x $ Cons _ (Wv0 1) $ Nil _)
    $ Cons _ (nat-add (field p) $ field q) $ Nil _))

main
; warns: tests/wide_containers.sl:24:20: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1185:1: note: `;! warn` for `ACons` is here
; warns: tests/wide_containers.sl:24:39: warning: application of `ACons`: copies the whole array, O(n); allocate with `array-new` and fill with `array-place`
; warns: lib/prelude.sl:1185:1: note: `;! warn` for `ACons` is here
