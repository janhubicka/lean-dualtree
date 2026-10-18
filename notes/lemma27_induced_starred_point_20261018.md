# Canonical corrected W_* point for every selected f'-assignment

Fix positive local Ramsey dimension q. For each genuine global final
variable assignment sigma, its independently induced coordinate
words x_sigma.words_i are evaluations of f_i under the local
selected-root/fallback assignment and hence belong to the actual
vector-product span.

Choose every corrected D₂ bullet point to be the unique intrinsic
rank-zero local support root of that component. This belongs to
f_i.support; the corrected D₀/D₂ kind has no D₁/up indices
(by the existing ForwardSortedMixedProduct.kind_ne_up).

The original vector-q-completeness condition, applied to local
roots at the same intrinsic level 0, orders their ambient word
lengths along the honest sorted D₂ frontier subtype.
Consequently BulletLengthsOrdered holds, and the existing
ForwardQActualStarredSpace.starredInputOfOrdered constructor
provides a GENUINE corrected W_* input for every sigma.
The resulting point is in the FULL mixed-product f.span.

The existing concrete Q(x) versus evaluated f' comparison
then applies without any extra point-existence assumption
at every projected P_i(z). No Hall identification of
independent selected local variables is made.

This is for the corrected forward-auxiliary W_* only;
no equivalence with the paper's printed reverse-starred
version is asserted. Remaining: compare all original
ambient f-fibres, verify the initial and outside cone
parts and the smoothness/simplicity pullback, and complete
the Ramsey iteration.
