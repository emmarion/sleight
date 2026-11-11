# Credits for higman/

The proof in `higman/` was written in Sleight for this repository by a
Claude session. It is not a translation of an earlier formal proof. Its
ingredients are standard; the sources below are the ones this session
knows of, and the attributions are this session's understanding, not
checked against the papers beyond their bibliographic records.

## The theorem

- Graham Higman, "Ordering by divisibility in abstract algebras",
  *Proceedings of the London Mathematical Society* (3) 2 (1952),
  326–336, doi:10.1112/plms/s3-2.1.326. The lemma `spec.sl` states, for
  a two-letter alphabet, is named after this paper.

## What the proof uses

- L. E. Dickson, "Finiteness of the odd perfect and primitive abundant
  numbers with n distinct prime factors", *American Journal of
  Mathematics* 35 (1913), 413–422, doi:10.2307/2370405. The lemma named
  after him, that ℕ^d has no infinite antichain or descending chain under
  the pointwise order, is what `box.sl`, `forest.sl` and `dickson.sl`
  prove in the form the search needs.
- The view of a downward-closed set of words as a finite union of simple
  products, here of the shape d₁^* c₁ d₂^* c₂ … c_k d_{k+1}^*, appears to
  go back to the simple regular expressions of P. A. Abdulla, A.
  Bouajjani and B. Jonsson, "On-the-fly analysis of systems with
  unbounded, lossy FIFO channels", CAV 1998, LNCS 1427,
  doi:10.1007/BFb0028754, and the journal version by Abdulla,
  Collomb-Annichini, Bouajjani and Jonsson, "Using forward reachability
  analysis for verification of lossy channel systems", *Formal Methods in
  System Design* 25 (2004), doi:10.1023/B:FORM.0000033962.51898.1a.
  `words.sl` uses the case of the complement of the upward closure of
  one word; the boxes of `sre.sl` are such products over any alphabet.
- The k-letter search's measure is a multiset of ranks under the
  multiset ordering of N. Dershowitz and Z. Manna, "Proving termination
  with multiset orderings", *Communications of the ACM* 22 (1979).
- S. Schmitz and Ph. Schnoebelen, "Multiply-recursive upper bounds with
  Higman's lemma", ICALP 2011, LNCS 6756, arXiv:1103.4399. Their bound on
  the length of controlled bad sequences over k letters, at level
  ω^(k−1) of the fast growing hierarchy, and their attribution of its
  tightness to Cichoń (2009), are why README.md gives one proof per k.
- The measure's order, ω^ω, appears to match the maximal order type of
  binary words under embedding, as this session understands the results
  of D. H. J. de Jongh and R. Parikh, "Well-partial orderings and
  hierarchies", *Indagationes Mathematicae* 39 (1977), 195–207.

## Constructive proofs this one does not follow

These were considered and set aside, because they recurse over an
infinitely branching inductive definition, which Sleight's termination
check does not accept (SOUNDNESS.md §2):

- T. Coquand and D. Fridlender, "A proof of Higman's lemma by structural
  induction", unpublished manuscript, about 1993.
- S. Berghofer, "A constructive proof of Higman's lemma in Isabelle",
  TYPES 2003, LNCS 3085, and the Isabelle theory
  `HOL/Proofs/Extraction/Higman.thy`, which formalize the proof above.
- D. Fridlender, "Higman's lemma in type theory", TYPES 1996, LNCS 1512.
