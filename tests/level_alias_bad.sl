; error: needs a (subterm p) annotation
; A branch that equates the enclosing function's own level with an older one must not turn its
; same-level self-call into a lower-level one: both levels are read canonically (ASSUMPTIONS 75).
; Read literally, the call needs no Subterm decrease, and bad is then lt_subterm.sl's loop --
; an erased function returning (False), guarded only by (Pair Q P) having no values.

(def-lvl P)
(def-adts
  (Pair : ((Level) A) ((Level) B) -> Type
    enum
    (many Diag : (erased (Level) L) -> (Pair L L))))

(def-lvl Q)
(let (erased pq) (prove-predates P Q))

(def-fns Q $ erased bad : (many (Pair Q P) t) -> (erased (False) f)
  (match many t (((False) r))
    ((Diag l) (bad (predates pq) t))))

(Zero)
