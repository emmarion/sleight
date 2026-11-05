; warns: tests/erased_kind_warn.sl:7:33: warning: `_A` is declared `many`, but a value of type `Type` is always erased, so it can be supplied only in an erased position; declare it `erased`
; warns: tests/erased_kind_warn.sl:9:34: warning: `_l` is declared `unique`, but a value of type `(Level)` is always erased, so it can be supplied only in an erased position; declare it `erased`
; warns: tests/erased_kind_warn.sl:13:20: warning: `f` is declared `many`, but a value of type `(TyCtor (Type A) -> Type)` is always erased, so it can be supplied only in an erased position; declare it `erased`
; warns: tests/erased_kind_warn.sl:15:53: warning: `_p` is declared `many`, but a value of type `(Predates (Level) l l)` is always erased, so it can be supplied only in an erased position; declare it `erased`
; expect: 3

(def-fns _ $ (many type-param : (many Type _A) ->) (values))

(def-fns _ $ (many level-param : (unique (Level) _l) ->) (values))

(def-adts $ (Holder : -> Type)
  enum
  (many MkHolder : (many (TyCtor (Type A) -> Type) f) -> (Holder)))

(def-fns _ $ (many proof-param : (erased (Level) l) (many (Predates (Level) l l) _p) ->) (values))

(def-fns _ $ (many pass : (erased Type T) (many T x) -> (many T y)) x)

(def-fns _ $ (many absurd explode : (erased Type A) (many (False) f) -> (many A a)) f)

(let ((erased U)) Type)

(def-fns _ $ (many alias-param : (many U _B) ->) (values))

(pass (Nat) 3)
; warns: tests/erased_kind_warn.sl:23:34: warning: `_B` is declared `many`, but a value of type `U` is always erased, so it can be supplied only in an erased position; declare it `erased`
