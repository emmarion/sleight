; needs: ../std/list bytes_le
; expect: (MkLe "\x00\x00\x00\x00" "\x00\x00\x00\x00" 0 0 0 0 0 0)
(let-match many #\x00 (MkChar zero))
(le-test zero zero)
