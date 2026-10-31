# Busy Beaver proofs

`bb/` proves busy beaver values in Sleight. [NOTICE.md](NOTICE.md)
credits the earlier proofs these follow.

## Checking BB(5)

The BB(5) proof can be checked against either of two statements:

- `agent/tasks/bb5/spec.sl`, the goal `BusyBeaver 5 47176870` over the
  definitions in `agent/tasks/bb5/defs.sl`. This is the recommended one.
- `bb/bbis5.sl`, the goal `BBIs 5 47176870` over `bb/tm.sl`'s
  definitions.

First build a release slc (see the top-level [README.md](../README.md)
for the dependencies):

```sh
sh self/release.sh
```

Then, from the repository root, the recommended check:

```sh
_build/release/slc std/nat.sl std/list.sl std/macro.sl std/tactics.sl std/immediate.sl agent/tasks/bb5/defs.sl agent/tasks/bb5/spec.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl bb/skelet.sl bb/sk17.sl bb/sk1.sl bb/holes.sl bb/par.sl bb/bb5.sl bb/spec.sl bb/spec5.sl --goal proved --inline 25
```

or the `BBIs` one:

```sh
_build/release/slc std/list.sl std/immediate.sl bb/tm.sl bb/sim.sl bb/cert.sl bb/perm.sl bb/cyc.sl bb/tree.sl bb/tnf.sl bb/sym.sl bb/vec.sl bb/search.sl bb/far.sl bb/wfar.sl bb/pat.sl std/macro.sl bb/skelet.sl bb/sk17.sl bb/sk1.sl bb/holes.sl bb/par.sl bb/bb5.sl bb/champ5.sl bb/bbis5.sl --goal proved --inline 25
```

Each prints `--goal proved: PASS`. Most of the work runs as native code
in parallel jobs, one per core. `--inline 25` is passed on to ocamlopt.
In one set of measurements on a 12-core Mac with OCaml 4.14, higher
levels made the jobs no faster but the compile slower, and lower ones
made the jobs slower. The check took about 36 s there.
