; error: `(coerce a p)`, at `(Unique)` by the target side of `p`'s type, used at many without `share`

(let ((unique a)) (Zero))
(let ((erased p)) (coercible-refl (Unique) a))
(let ((many b)) (coerce a p))
(Zero)
