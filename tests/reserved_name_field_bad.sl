; error: `__p` begins with `__`, which is reserved for the compilers' messages
(match many 3 (((Nat) r))
  ((Zero) 0)
  ((Succ __p) 1))
