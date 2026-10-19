# Source-facing cardinal obstruction when l <= m (19 October 2026)

Let T be the actual forward k-complete support of the original ambient
variable word f, and let t0 be the corrected inclusive forward cut.
Its intrinsic T-rank is m.

The verified retained prefix closure ensures every one of the m
distinct strict T-predecessors of t0 lies in retained(T,t0), and
t0 itself is retained. Therefore
  |retained(T,t0)| >= m+1.

The source starred word g' has precisely l independent variable roots:
its root-support set coincides with the interior of the l-interior-node
semi-complete source tree S. Thus when l <= m, retained(T,t0) contains
at least one original f-variable root u NOT in the old source support.

The previously proven exhaustive obstruction now applies:
rho(u) is either a constant or an old variable v. In the constant
case all Q(w) evaluations have a fixed value at u but f' does not.
In the variable case rho fixes v at its own different old root, so
rho identifies two retained roots and the two-root obstruction applies.

Over a two-letter alphabet, there exists a genuine element of the
complete-skew final f'-span outside ALL evaluated fibrewise
Q(w) images, even if the enlarged mixed-product input w is not
restricted to the corrected starred W_* domain.

**Scope**: This refutes the unrestricted reverse COVERING assertion
  span(f') subset union_(all w) span(Q(w))
for the CURRENT corrected f' construction whenever l <= m. It does
NOT refute the existence assertion of Lemma 27 or the Dual Ramsey
Theorem, and it does not diagnose every regime (e.g. m=l-1).

A repair must adjust the final word's retained-root independence
or change the exact Ramsey-domain requirement, and must check that
the resulting support remains complete skew and accommodates the
fixed early source refinement. The already verified forward
anchored-evaluation equality is consistent with this obstruction.
The printed reverse-auxiliary W_* mismatch is independent.
