# Third-party notices and credits for real/

Written by a Claude session at the owner's request; it is not legal
advice, and what the license requires should be checked by the owner.

The definitions in `defs.sl` follow the constructive Cauchy reals of the
Rocq Prover's standard library, and the rational and integer definitions
they rest on.

## Upstream project

- **The Rocq Prover standard library**, <https://github.com/rocq-prover/stdlib>.
  The copy this work followed is commit
  `22fcaa27d17bc28ab4be728ed10a1fb73afb23ee`. The files followed carry the
  notice:

  > The Rocq Prover / The Rocq Development Team
  > Copyright INRIA, CNRS and contributors
  > (see version control and CREDITS file for authors & dates)
  > This file is distributed under the terms of the
  > GNU Lesser General Public License Version 2.1

  The license text is reproduced in [LICENSE](LICENSE).

## What is based on it

- `theories/Reals/Cauchy/ConstructiveCauchyReals.v`: `QCauchySeq`,
  `QBound`, `CReal`, `CRealLt`, `CRealLe`, `CRealEq`, `CReal_appart`,
  `CReal_plus`, `CReal_opp` and `CReal_minus`.
- `theories/Reals/Cauchy/ConstructiveCauchyRealsMult.v`: `CReal_mult`.
- `theories/QArith/QArith_base.v`, `Qabs.v` and `Qreduction.v`: `Q`,
  `Qlt`, `Qle`, `Qplus`, `Qmult`, `Qopp`, `Qminus`, `Qinv`, `Qpower`,
  `Qabs` and `Qred`.
- `theories/ZArith`: the shape of `Z`, and `Z.max`.
