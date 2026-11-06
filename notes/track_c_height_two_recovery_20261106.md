# Track C recovery checkpoint — 6 November 2026

The original local patch mentioned in the chat as `track_c_height_two.patch` was located in a temporary workspace that is no longer accessible here. Its claimed local commit `ede18f8d99b26ceb14aee44976730f6ab23557cd` was not on GitHub at recovery time. Therefore the earlier asserted six-module result and 91-endpoint audit cannot be treated as available source or a reproducible CI result.

This **new**, separately reviewed change recovers only one independent milestone, in `DualTree/HigherRamseyFlat.lean`: a two-stage genuine flat Hales–Jewett selection, with the root length N chosen before the cone length M, and M depending on all `b^N` depth-N addresses.

## Exact positive result

For any natural b and d and finite alphabets β and γ, there exist root and cone lengths N and M such that every colouring

`(Fin N → Fin d → β) → (Fin M → Fin d → Fin (b ^ N) → β) → γ`

admits two proper variable words with one genuine variable apiece. Their **entire rectangular evaluated product span** is monochromatic. The root variable assigns independent letters in all d coordinates; the cone variable assigns independent letters for every coordinate and depth-N address.

The proof uses finite Hales–Jewett over the root alphabet first to select N. After N is fixed, parameter-uniform Hales–Jewett over the full cone alphabet selects M, with every root-band word as an independent colour parameter. For a given colouring, choose the uniform cone word, then a root word for its induced root-band colouring. This order avoids circular choices of heights.

## What is not established

This is a flat Ramsey prerequisite, **not** a higher-skew theorem. It does not construct a legal k=2 tree variable word, establish `SkewTree.completeB ... 2`, prove `VectorSkew.vectorCompleteB ... 2`, or obtain the all-D0 `MixedProduct.Good` theorem. Those are the substantive remaining obligations in issue #516. Neither the missing six-module patch nor its claimed local theorem checks are recreated by this change.

A subsequent PR must construct the support root at the first root-variable occurrence and b children at the cone first-variable level, retain constants in every unused cone, prove the tree-word below-root law and exact evaluated span, then prove both vector ordering clauses and the actual c-good conclusion. A further lemma extends the result to all sufficiently large ambient heights.

No manuscript text was changed, no new axioms or assumed higher-k Ramsey theorem are introduced, and passing CI on this stage must not be reported as completion of Track C.
