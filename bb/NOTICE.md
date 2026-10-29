# Third-party notices and credits for bb/

The proofs in `bb/` are written in Sleight for this repository. Several
of them follow the structure of earlier Coq proofs, and some certificate
data is taken from them. The upstream projects are under the MIT
license; their notices are reproduced below. The mapping that follows
is reconstructed from this repository's commit messages and may be
incomplete.

## Upstream projects

- **Coq-BB5** (author: mxdys, <https://github.com/ccz181078/Coq-BB5>),
  MIT license, copyright (c) 2024 ccz181078.
- **busycoq** (author: Maja Kądziołka / meithecatte,
  <https://github.com/meithecatte/busycoq>), MIT license, copyright (c)
  2023 Maja Kądziołka. Coq-BB5 ships a partial snapshot of it, at commit
  333695b79707189d49f5e560a55c3ab8dda1cdc6, with changes made for
  Coq-BB5, especially in `Skelet1.v`.

## What follows what

- `bb/sk1.sl` (Skelet #1) follows `Skelet1.v` as shipped with Coq-BB5:
  its symbolic tape symbols, base rules, stride rule, the uni-cycle
  acceleration with P = 53946 and T = 215779, and the final cycle check.
  The lazy-stride runner described in `bb/SK1-LAZY.md` is this
  repository's own.
- `bb/skelet.sl`: the Skelet #10 proof follows busycoq's `Skelet10.v`.
  The Skelet #33 and #34/#35 proofs redo busycoq's `Skelet33.v` and the
  shift-overflow argument of `Skelet34.v` over this repository's own
  counter lemmas. The Skelet #26 proof, and Skelet #15 through its
  mirror image, are not recorded as following a specific upstream file.
- `bb/sk17.sl` (Skelet #17) follows the abstract machine of Coq-BB5's
  Skelet #17 proof.
- `bb/far.sl` is a finite-automata-reduction certificate in the style of
  Coq-BB5's DFA+NFA verifier. The DFAs used for the BB(5) holes in
  `bb/bb5.sl` come from Coq-BB5's hardcoded FAR certificates.
- `bb/wfar.sl` is a weighted-automata certificate in the style of
  Coq-BB5's MITM-WDFA verifier. The weighted DFAs and bounds used in
  `bb/bb5.sl` are Coq-BB5's, used directly or through the machine
  reached after a 0RB first step.
- `bb/pat.sl` certificates for the Finned machines in `bb/bb5.sl` were
  derived from Coq-BB5's invariants for those machines.
- `bb/search.sl`, `bb/tnf.sl`, `bb/tree.sl`: the n-gram (CPS-style)
  deciders, the LRU history variant (after Coq-BB5's NG_LRU), the TNF
  enumeration and the default settings order loosely follow Coq-BB5 and
  bbchallenge. The commit history records that no code was copied for
  these.

The analyses behind several of these machines are due to the bbchallenge
community; for example the Skelet #1 and #10 arguments follow Shawn
Ligocki's write-ups (<https://www.sligocki.com/2023/03/13/skelet-1-infinite.html>).

## Citing the BB(5) result

Coq-BB5 asks to be cited with these two entries:

```bibtex
@misc{BB5,
      title={{Determination of the fifth Busy Beaver value}},
      author={{The bbchallenge Collaboration} and Justin Blanchard and Daniel Briggs and Konrad Deka and Nathan Fenner and Yannick Forster and Georgi Georgiev and Matthew L. House and Rachel Hunter and Iijil and Maja Kądziołka and Pavel Kropitz and Shawn Ligocki and mxdys and Mateusz Naściszewski and savask and Tristan Stérin and Chris Xu and Jason Yuen and Théo Zimmermann},
      year={2025},
      eprint={2509.12337},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2509.12337},
      note={\url{https://arxiv.org/abs/2509.12337}}
}
```

```bibtex
@software{mxdys_2025_17061968,
  author    = {mxdys},
  title     = {{Coq-BB5 release v1.0.0}},
  month     = sep,
  year      = 2025,
  publisher = {Zenodo},
  version   = {1.0.0},
  doi       = {10.5281/zenodo.17061968},
  url       = {https://doi.org/10.5281/zenodo.17061968},
  note      = {\url{https://doi.org/10.5281/zenodo.17061968}}
}
```

## License texts

### Coq-BB5

```
MIT License

Copyright (c) 2024 ccz181078

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

### busycoq

```
Copyright (c) 2023 Maja Kądziołka

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
```
