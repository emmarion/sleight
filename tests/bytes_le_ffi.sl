; needs: bytes_le
; externs: only
; expect: (MkLe "\xfe\xff\xff\xff" "\xfe\xff\xfe\xff" 65535 65534 4294901758 4294901758 65534 4294901758)
(let-match many #\xff (MkChar ff))
(let-match many #\xfe (MkChar fe))
(le-test ff fe)
