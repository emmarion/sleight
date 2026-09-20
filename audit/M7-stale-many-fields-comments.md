# M7. Stale comments say "many fields" where the code counts non-erased

Status: observation, comments only.

UNIQUE.md U12's reading: "section 41's shape check then compares the
non-erased arities of the model's constructors, not the many ones." The
code does that: `shapes` in `lib/elab.ml` and `Ffi.claim_fn`'s parameter
count both test `e.mult <> Erased`, so `ACons`'s two `unique` fields count
and the four array externs claim 1, 3, 2 and 3 parameters, matching the
FFI table. Two comments still describe the count as many fields: the one
above `shapes` ("its number of many fields") and `lib/ffi.ml`'s
`check_shape` comment ("the many-field arities of the non-phantom
constructors"). The code is right; the comments are Codex's and were left
for the owner, CLAUDE.md rule 4 covering comments.
