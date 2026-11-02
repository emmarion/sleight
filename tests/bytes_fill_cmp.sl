; expect: (Cons _ "hexxxxxorld" $ Cons _ "111e" $ Cons _ "000u" $ Cons _ "000u" $ Cons _ "222u" $ Cons _ "222u" $ Cons _ "111e" $ Cons _ "222u" $ Cons _ "000u" $ Nil _)
; bytes-fill over a range, and the three forms of bytes-cmp on ranges of two buffers: both unique, unique and
; shared, both shared, with cmp-flip and cmp-eq. Each line is the three answers (0 less, 1 equal, 2 greater)
; and the equality: whole buffers, a proper prefix, a difference inside an 8-byte word and one past it, the
; empty ranges, and bytes above 127.

(def-fns _ $ (many digit : (erased (List (U8)) as bs) (many (Cmp (List (U8)) BytesLt as bs) c) -> (many (String) d))
  (match many c _ ((CLt _ _ _ _ _) "0") ((CEq _ _ _) "1") ((CGt _ _ _ _ _) "2")))

(def-fns _ $ (many cmp3 : (many (String) s) (many (Nat) i m) (many (String) t) (many (Nat) j n) -> (many (String) r))
  (let ((erased _) (unique a0) (erased _)) (str-bytes-copy s))
  (let ((many la) (erased pa) (unique a)) (bytes-length _ a0))
  (let ((erased _) (unique b0) (erased _)) (str-bytes-copy t))
  (let ((many lb) (erased pb) (unique b)) (bytes-length _ b0))
  (let ((many ea) (erased aa)) (add i m))
  (let ((many eb) (erased ab)) (add j n))
  (let-match many (lt-dec ea (Succ la)) (Yes _ _ _ _ lta) ((No _ _ _ _ _) "range"))
  (let-match many (lt-dec eb (Succ lb)) (Yes _ _ _ _ ltb) ((No _ _ _ _ _) "range"))
  (let ((erased _) (erased ra)) (splice-range _ _ _ pa i m ea aa lta))
  (let ((erased _) (erased rb)) (splice-range _ _ _ pb j n eb ab ltb))
  (let ((many c1) (unique a2) (unique b2)) (bytes-cmp _ _ _ _ a i m b j n ra rb))
  (let ((many fb)) (share b2))
  (let ((many c2) (unique b3)) (bytes-cmp-unique-many _ _ _ _ a2 i m fb j n ra rb))
  (let ((many c3)) (cmp-flip _ _ _ _ (bytes-cmp-many _ _ _ _ fb j n (share b3) i m rb ra)))
  (let ((many e)) (match many (cmp-eq _ _ _ _ c3) (((String) _)) ((Equal _ _ _) "e") ((Unequal _ _ _ _ _) "u")))
  (str-append (digit _ _ c1) $ str-append (digit _ _ c2) $ str-append (digit _ _ c3) e))

(def-fns _ $ (many fill-test : -> (many (String) r))
  (let-match many #\x (MkChar x))
  (let ((erased _) (unique b0) (erased _)) (str-bytes-copy "hello world"))
  (let ((many l) (erased pl) (unique b)) (bytes-length _ b0))
  (let ((many e) (erased a)) (add 2 5))
  (let-match many (lt-dec e (Succ l)) (Yes _ _ _ _ lt) ((No _ _ _ _ _) "range"))
  (let ((erased _) (erased range)) (splice-range _ _ _ pl 2 5 e a lt))
  (let ((erased _) (erased _) (unique r) (erased _) (erased _)) (bytes-fill _ _ b 2 5 x range))
  (let ((many s) (erased _)) (bytes-str _ (share r)))
  s)

(def-fns _ $ (many all : -> (many (List (String)) r))
  (Cons _ (fill-test) $
    Cons _ (cmp3 "hello" 1 3 "yellow" 1 3) $
    Cons _ (cmp3 "abc" 0 3 "abd" 0 3) $
    Cons _ (cmp3 "abcdefghijklmnop" 2 12 "xxcdefghijklmnoz" 2 13) $
    Cons _ (cmp3 "abcdefghijklmnopq" 1 15 "abcdefghijklmnoPq" 1 15) $
    Cons _ (cmp3 "zzzzzzzzzz" 1 9 "zzzAzzzzzz" 1 9) $
    Cons _ (cmp3 "a" 1 0 "b" 0 0) $
    Cons _ (cmp3 "\xff\x00" 0 2 "\x01\xff" 0 2) $
    Cons _ (cmp3 "\x01\xff" 0 1 "\x01\x00" 0 2) $ Nil _))

(all)
