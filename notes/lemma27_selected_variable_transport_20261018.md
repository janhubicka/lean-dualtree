# Exact selected-variable transport towards f' (18 October 2026)

The corrected final support is already proved (m+q)-complete skew.
The ambient-root lift established that selected raw nodes are bounded
and belong to the original ambient word f's genuine root support.

This pass proves a bijective-on-image typing of the selected local
root tags (frontier_i, local_variable_v) into the global ambient
variable-root type:

  selectedTag (i,v) ↦ projected root P_i(v) ∈ finalBoundedRoots
  selectedTag (i,v) ↦ same node in original ambient f.Vars

Both maps are injective, including between differently tagged variables
that have the same local name. No Hall allocation to the much smaller
source starred-variable roots is attempted.

For each local component word f_i and occurrence
 f_i.word(z) = inr(v) with the projected root P_i(v) SELECTED
by the exact target-height filter, its root satisfies
 P_i(v) ⊑ P_i(z) in the original ambient homogeneous tree.
Thus any substitution realizing this local variable symbol at the
original f-root P_i(z) satisfies the crucial root-compatibility
requirement of the generic RootCompatibleRefinement.Certificate.

Not yet proved: defining the total global substitution on all
original ambient f roots; constants and excluded upper-band local
variables need a genuine prescribed fallback/constant choice;
the local letter decoding must agree with the actual mixed-product
evaluation in all safe cones. These are not solved by injectivity.
