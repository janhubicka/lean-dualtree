# Ambient refinement by a genuine root-compatible substitution

Given the original ambient variable word f and a chosen list R of
new roots, the entire VARIABLE-WORD LEGALITY problem is reduced to
a single root-compatible syntactic substitution rho:

  1. R is duplicate-free and is a subset of support(f).
  2. rho fixes every root in R at its original f-root.
  3. Whenever rho maps an old variable u to a selected new root v,
     the root v is an ambient prefix of u.

These imply atRoot and below for the genuinely substituted word
without assuming any semantic theorem about spans. Existing
SpanAudit.span_substitute_subset then gives evaluated span
inclusion of the new word into the original word.

A root-collapse witness demonstrates that the abstract
certificate is satisfiable whenever the selected subset R
contains an ambient common root. This is NOT a proof of the
actual desired f' in the corrected Lemma 27: that specific rho
must additionally realize every selected local f_i symbol and
agree with the fibrewise Q image on the prescribed subspaces.
The root-collapse witness generally fails those Q constraints.

For the NEXT bridge, use the existing FibreFrame.T_bounded to
turn the exact finalSupport finset (subset of ambient T) into a
list of bounded roots R; then the actual original ambient
word has the same T support. The checked final-support common
root supplies the root-collapse premise. The Q-compatible rho
is the genuinely remaining mathematical task.
