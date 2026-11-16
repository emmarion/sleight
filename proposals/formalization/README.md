# Formalizing Sleight in Sleight: proposals

A Claude session wrote everything under this directory overnight, at the
owner's request, as material for decisions. Nothing here is approved.
DESIGN.md, DECISIONS.md, OPEN.md, and ASSUMPTIONS.md are unchanged. A
claim in these files that a quoted line of DESIGN.md, a listed command,
or a checked spike does not bear out is a mistake in these files.

This file is filled in as the night's work lands.

## Spikes

Each runs with the reference implementation and with slc. From the
repository root, after `dune build` and `self/release.sh`:

```sh
cd proposals/formalization/spikes/verdict
../../../../_build/default/bin/main.exe spec.sl proof.sl qed.sl --goal proved
../../../../_build/release/slc spec.sl proof.sl qed.sl --goal proved
```

- `spikes/verdict/`: a toy language (lists of `Open` and `Close`,
  accepted when balanced) with separately written `Accepts` and `Fails`
  relations. Its goal packages a total decider whose result is one of
  the two with its erased derivation, and a proof that no source has
  both.
- `spikes/verdict-machine/`: the same language decided by a state
  machine whose step is a total function. Its goal says the machine's
  only exit is a verdict with its derivation. `drive.sl` loops the step
  under the driver as a `Program`; the exit code is 0 for accepted and
  1 for rejected:

  ```sh
  cd proposals/formalization/spikes/verdict-machine
  ../../../../_build/default/bin/main.exe spec.sl machine.sl qed.sl --goal proved
  ../../../../_build/default/bin/main.exe spec.sl machine.sl drive.sl run-unbalanced.sl; echo $?
  ```
