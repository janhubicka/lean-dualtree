# Actual local symbol decoding for final f' (18 October 2026)

The genuine mixed Ramsey word f_i returns a dependent symbol:
an alphabet beta-constant or a local variable v rooted in f_i.support.
The final support is rank-filtered: a local variable v occurs as a
global variable name ONLY if its target-budget projection P_i(v)
was selected. This is essential for frontiers of ambient T-rank m+1,
where their final support is one local level shorter.

Define localSymbol(i,z) : Sum alpha selectedFinalRoot:
- local constant a -> decode(a), for a supplied beta->alpha map;
- selected local variable v -> inr(P_i(v)) in the GLOBAL bounded
  root support, with the full sorted index i in its tag;
- excluded variable v -> inl(fallback), a supplied alpha letter.

Proved exact equalities for constants, excluded variables and the
selected variable's own root. Most importantly, if this
localSymbol emits a global variable at arbitrary local tail z,
the selected global root P_i(v) is an ambient prefix of P_i(z).
This follows from the local VariableWord.below axiom and the
previously certified prefix-preserving corrected projection.

This is the key local branch of the total f' substitution.
Outstanding: given an original ambient f root in a frontier cone,
recover its UNIQUE sorted frontier index and safe local tail; use
localSymbol there, and map early/unsafe roots consistently.
Prove the assembled global map fixes all selected roots, and
apply the root-compatible VariableWord refinement certificate.
The source word and original W_* order are still separate.
