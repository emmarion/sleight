; error: `_p` begins with `_`, which is reserved for the compilers' messages
(match many 3 (((Nat) r))
  ((Zero) 0)
  ((Succ _p) 1))
