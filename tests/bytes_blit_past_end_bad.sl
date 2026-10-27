; error: argument 11, `to`, of `bytes-blit`: type mismatch
(def-fns _ $ (many past-end : -> (many (String) r))
  (let ((erased xs) (unique src) (erased sp)) (str-bytes-copy "ab"))
  (let ((many len) (erased lp) (unique src2)) (bytes-length _ src))
  (let ((many e) (erased a)) (add 0 2))
  (let-match many (lt-dec e (Succ len)) (Yes _ _ _ _ lt) ((No _ _ _ _ _) ""))
  (let ((erased ys) (erased from)) (splice-range _ _ _ lp 0 2 e a lt))
  (let ((erased ds) (unique dst) (erased dp)) (str-bytes-copy "x"))
  (let ((erased zs) (unique r) (erased q)) (bytes-blit _ (share src2) 0 _ dst 0 2 _ from _ from))
  (let ((many s) (erased p)) (bytes-str _ (share r)))
  s)
past-end
