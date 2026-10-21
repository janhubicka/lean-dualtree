# Canonical target terminal for each source R marker

The previous patches proved:
* same corrected Definition-26 signature ⇒ identical literal R lists;
* every supported target leaf prefixes some source R marker;
* under true T'_M support and equal signatures, a target terminal
  has a safe selected local D2 address.

Here we also prove the converse existence AND uniqueness:
for every original literal R marker r, there is a unique
terminal t of O extending r. Instantiate the already verified
source leaf/R-marker bijection on the actual target O, using
the target as a corrected source frame inside the unchanged
complete support T, and transport the marker type by node
identity to the original source.

The constructed targetLeafForSourceMarker is a genuine member of
O.tree outside its interior and carries the exact prefix incidence
r ≼ t. This is a canonical marker-label choice, not a fresh
enumeration or Hall assignment.

Next work: apply the previously verified unique safe-address
and selected-component-support results to each chosen terminal
to obtain a concrete local D2 point indexed by the ORIGINAL
bulletForMarker(r). Then prove the entire tuple of chosen
local D2 points is vector-one-complete in the corrected sorted
frontier order. This is a nontrivial global order condition,
not a consequence of individual support membership alone.
