# Fibrewise evaluation of the genuine corrected ambient refinement

PR #374 defines one total root substitution on the original ambient
f-variable names, using actual selected shortened cone variables
and fallback constants, and proves root compatibility and span
inclusion. This module proves the evaluation semantics in the
precise original f-fibre sense.

For each global final-variable assignment sigma, define the induced
local assignment sigma_i(v):
   if P_i(v) is among the final rank-budget-selected roots,
   return sigma(P_i(v)); otherwise use fallback.
Selected variables from distinct coordinates retain distinct
global roots, so these assignments remain independent where
the final support retains them.

On an original ambient f-fibre rooted at P_i(z), the actual
final variable-word symbol equals the converted local component
symbol f_i.word(z). Therefore its evaluation under sigma is
the actual evaluation of f_i.word(z) under sigma_i.

The theorem is at every ambient position in the original f-fibre,
not just the projected root. This is the main local semantic
identity required to compare f' evaluations with the corrected
Q map of the induced mixed-product point.

Remaining proof steps: assemble a legal mixed-product point x_sigma
whose coordinate words are the induced f_i evaluations; certify
the corrected W_* subset condition; check entire Q(x_sigma) symbols
against the corresponding evaluation of the source target g';
prove Definition 24 simplicity pulls back; iterate the Ramsey
argument. Printed reverse-starred order remains a separate
translation problem.
