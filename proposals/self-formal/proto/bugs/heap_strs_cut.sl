(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many pad : (subterm many (Nat) n) (many (List (String)) acc) -> (many (List (String)) r))
  (match many n _ ((Zero) acc) ((Succ k) (tail $ pad k (Cons _ "absent-dir" acc)))))

(def-fns _ $ (many report : (erased Type A) (many (String) label) (unique (World) w at vacant-slot) (unique (Request (Result A)) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut (str-append label $ match many r (((String) _)) ((Ok _ _) " ok\n") ((Fail _ _) " refused\n")))))
  w2)

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (report _ "confine" w (ConfinePaths (pad 1000000 (Cons _ "." $ Nil _)) (Nil _))))
  (let ((unique w2)) (report _ "stat cwd" w1 (Stat ".")))
  (values w2 (Exit P code0)))

(Continue P start)
