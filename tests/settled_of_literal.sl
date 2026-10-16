; expect: (MkPair _ _ 5 $ MkPair _ _ #\a "ab")
(MkPair _ _ (settled-value _ _ (settled-of many 5)) $ MkPair _ _ (settled-value _ _ (settled-of many #\a)) (settled-value _ _ (settled-of many "ab")))
