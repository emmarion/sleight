; Text is a zero-cost newtype; bytes-length-many is an O(1) machine read.
(def-fns _ $ (many ed-text-length : (erased (List (U8)) xs) (many (Text xs) text) ->
    (many (Nat) n) (erased (Length (U8) xs n) len) (erased (Lt n max-array-length) fits)
    (erased (Lt n u62-modulus) pn))
  (let-match many text (MkText _ bytes k lk fits))
  (let ((many n) (erased len)) (bytes-length-many xs bytes))
  (let-match erased (length-fn _ xs k n lk len) (Refl _ _))
  (values n len fits (lt-trans n max-array-length u62-modulus fits max-array-length-below-u62)))
