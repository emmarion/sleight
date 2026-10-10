(def-fns _ $ (many #"f g" : -> (many (Nat) r))
  0)
;! warn #"f g" do not call `#"f g"`
;! suppress warn #"f g"
(let ((many a)) (#"f g"))
;! restore warn #"f g"
(#"f g")
; warns: tests/raw_name_warn.sl:7:2: warning: call of `#"f g"`: do not call `#"f g"`
; warns: tests/raw_name_warn.sl:3:1: note: `;! warn` for `#"f g"` is here
; expect: 0
