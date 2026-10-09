(def-fns _ $ (many twice : (many (Nat) n) -> (many (Nat) m))
  (nat-add n n))
(def-unique _ $ (unique once : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
;! warn twice doubles slowly
;! warn once runs once
;! warn nat-add adds
(let ((many a)) (twice 1))
(let ((many tw)) twice)
(let ((many b)) (tw 2))
(let ((erased e)) (twice 3))
(def-fns _ $ (many quad : (many (Nat) n) -> (many (Nat) m))
  (tail $ twice $ twice n))
(def-fns _ $ (erased quad-erased : (many (Nat) n) -> (many (Nat) m))
  (twice n))
(def-fns _ $ (many apply : (many (Fn (level-of twice) (many (Nat) x) -> (many (Nat) y)) f) (many (Nat) n) -> (many (Nat) m))
  (f n))
(let ((many c)) (apply twice 4))
(let ((many d)) (once 5))
(quad d)
; expect: 24
; warns: tests/warn_pragma_function.sl:8:18: warning: call of `twice`: doubles slowly
; warns: tests/warn_pragma_function.sl:5:1: note: `;! warn` for `twice` is here
; warns: tests/warn_pragma_function.sl:10:18: warning: call of `tw`: doubles slowly
; warns: tests/warn_pragma_function.sl:5:1: note: `;! warn` for `tw` is here
; warns: tests/warn_pragma_function.sl:13:11: warning: call of `tw`: doubles slowly
; warns: tests/warn_pragma_function.sl:5:1: note: `;! warn` for `tw` is here
; warns: tests/warn_pragma_function.sl:13:19: warning: call of `tw`: doubles slowly
; warns: tests/warn_pragma_function.sl:5:1: note: `;! warn` for `tw` is here
; warns: tests/warn_pragma_function.sl:19:18: warning: call of `once`: runs once
; warns: tests/warn_pragma_function.sl:6:1: note: `;! warn` for `once` is here
