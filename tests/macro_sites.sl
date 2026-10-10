; needs: macro_lib
; expect: 46
(def-adts $ (Shape : -> Type)
  enum
  (splice (many Dot : -> (Shape)) (many Box : (many (Nat) w) -> (Shape))))

(splice (let ((many a)) 1) (let ((many b)) 2))
(splice)

(def-fns _ $ (many area : (splice (many (Shape) s)) -> (many (splice (Nat)) n))
  (match many s _
    (splice ((Dot) 0) ((Box w) (swap nat-add 0 w)))))

(let ((splice (many c) (many d))) (values 3 4))
(let ((many s1)) (area (Box (splice 10))))
(let ((many s2)) (nat-add (splice c d)))

(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) y))
  (splice (let ((many z)) (nat-add x a)))
  (swap nat-add z b))
(let ((many s3)) (f 20))

(let ((many xs)) (Cons (splice _) 6 (Nil (splice _))))
(let-match many xs (Cons _ h t))
(splice (let ((many s4)) (area (Dot))) (nat-add h $ nat-add s1 $ nat-add s2 $ nat-add s3 s4))
