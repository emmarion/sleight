; error: takes a (subterm p) annotation, not (predates p)
; A branch that equates the enclosing function's own level with an older one must not turn its
; same-level self-call into a lower-level one: both levels are read canonically (ASSUMPTIONS 75).
; Read literally, the call needs no Subterm decrease and bad is lt_subterm.sl's loop -- a total
; erased function returning a value of an empty type. What still stands between that and a token
; of (Absurd) in scope is that no caller can build the (Pair Q P) bad asks for.

; An empty type: no constructors, so no value, so a token of it would collapse section 10.
(def-adts $ Absurd : -> Type
  enum)

; Q is minted after P, so pq is the honest proof that P predates Q.
(def-lvl P)
(def-lvl Q)
(let (erased pq) (prove-predates P Q))

; Diag is diagonal: its return puts one variable in both index positions. So (Pair Q P) has a
; value only if Q and P are the same level -- which is exactly what entering the branch forces,
; the fact table aliasing the younger Q to the older P.
(def-adts
  (Pair : ((Level) A) ((Level) B) -> Type
    enum
    (many Diag : (erased (Level) L) -> (Pair L L))))

; bad sits at level Q and calls itself with pq written out. Inside the branch Q canonicalizes to P, so
; comparing the callee's level (canonically P) against the bare current level (Q) would make the two
; differ and the self-call read as a lower-level call -- which pq discharges, with no decreasing argument
; at all. tests/level_alias_bad.sl is the same program with the call bare.
(def-fns Q $ erased bad : (many (Pair Q P) t) -> (erased (Absurd) f)
  (match many t (((Absurd) r))
    ((Diag l) (bad (predates pq) t))))
