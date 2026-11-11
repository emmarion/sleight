# Credits

This directory was written by a Claude session at the owner's request. The
proof is a translation into Sleight of existing proofs. None of the
arguments below originate here; what is new is only their encoding.

- **The main lemma** (part 1 in [README.md](README.md)) follows Felix
  Joachimski and Ralph Matthes, "Short proofs of normalization for the
  simply-typed λ-calculus, permutative conversions and Gödel's T",
  *Archive for Mathematical Logic* 42 (2003), 59–87,
  doi:10.1007/s00153-002-0156-9. That is the idea of characterizing
  strongly normalizing terms inductively and proving closure under
  substitution and application by induction on the type of the
  substituted variable, nested with induction on the derivation. Matthes
  published an erratum (2004) about lemmas on permutative conversions,
  which this pure λ-calculus development does not involve.
- **The shape of the inductive characterization** used here (neutral
  terms, abstractions, and closure under strong head expansion, with no
  spines) is the one used in Andreas Abel, Guillaume Allais, Aliya Hameer,
  Brigitte Pientka, Alberto Momigliano, Steven Schäfer and Kathrin Stark,
  "POPLMark reloaded: Mechanizing proofs by logical relations", *Journal
  of Functional Programming* 29 (2019), e19,
  doi:10.1017/S0956796819000170. That paper's main proof uses Kripke
  logical relations, which this directory does not use. Its soundness
  direction, that the inductive characterization implies strong
  normalization through closure under weak head expansion, is what part 2
  follows.
- **Inductive characterizations of strong normalization** go back at
  least to Femke van Raamsdonk and Paula Severi, "On normalisation", CWI
  technical report, January 1995. The session that wrote this directory
  did not read that report, and credits it on the strength of how the
  later papers above describe the history.
- **De Bruijn indices** are N. G. de Bruijn's ("Lambda calculus notation
  with nameless dummies", *Indagationes Mathematicae* 34, 1972). The
  single-variable substitution and shifting lemmas are the textbook ones;
  their arrangement here as relations with an index-insertion relation
  `Skip` was chosen in this session.
