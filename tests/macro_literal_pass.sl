; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 7 $ MkPair _ _ #\a "ab")
(MkPair _ _ (splice 7) $ MkPair _ _ (splice #\x61) (splice "a\x62"))
