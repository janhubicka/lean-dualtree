# Target terminal -> original literal R marker

The structural repair of Lemma 27 has advanced beyond safety of
terminal coordinates. For any actual target starred O which has
the same first-boundary signature as the original source and
is contained in the same forward-complete enclosing support T,
we construct a new legitimate source-facing Frame with O as source.

The existing verified leaf-to-marker lemma, instantiated on this
target frame, associates each terminal of O with a literal R
marker prefix. The node-preserving marker subtype equivalence
from PR #411 identifies that marker with one of the ORIGINAL
source's literal R markers, without changing its ambient node.

Consequently, with same complete corrected signature and target
tree support inside T'_M (hence inside T), every O terminal has
a prefix in the original source R. This is stronger than the
previous raw safe-address existence and prepares a canonical
source D2 index for each target terminal.

Still open:
* Prove that this marker's selected T frontier is precisely the
  frontier of the terminal's unique safe address;
* Decode that safe terminal into the appropriate local D2 point;
* Show those exact points belong to f_i.support and obey corrected
  starred vector-one-completeness (not just ambient T ordering);
* Assemble markers to reconstruct O.tree and obtain full Q object
  equality. No statement of complete Lemma 27 follows yet.
