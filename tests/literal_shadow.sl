; expect: (MkPair _ _ 9 $ MkPair _ _ #\a "hi")
; Literals are the prelude's Nat, Char and String however the program shadows those names and the names
; literal interning uses.

(def-adts $ (Nat : -> Type) enum (many A : -> (Nat)))
(def-adts $ (Char : -> Type) enum (many B : -> (Char)))
(def-adts $ (String : -> Type) enum (many C : -> (String)))
(def-adts $ (U8 : -> Type) enum (many MkU8 : -> (U8)))
(def-adts $ (Numeral : -> Type) enum (many MkChar : -> (Numeral)))
(def-adts $ (Lt : -> Type) enum (many BZ : -> (Lt)) (many B1 : -> (Lt)) (many B2 : -> (Lt)))
(MkPair _ _ 9 $ MkPair _ _ #\a "hi")
; warns: tests/literal_shadow.sl:5:13: warning: declaration of `Nat` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:6:13: warning: declaration of `Char` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:7:13: warning: declaration of `String` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:8:13: warning: declaration of `U8` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:8:33: warning: declaration of `MkU8` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:9:13: warning: declaration of `Numeral` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:9:38: warning: declaration of `MkChar` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:10:13: warning: declaration of `Lt` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:10:33: warning: declaration of `BZ` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:10:53: warning: declaration of `B1` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/literal_shadow.sl:10:73: warning: declaration of `B2` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
