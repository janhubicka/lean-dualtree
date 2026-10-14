import DualTree.ForwardQFixedPrefixIso
import DualTree.ForwardQMarkerDirectionalIncidence

/-!
# Input-independent first-direction labelling of corrected Q outputs

The already verified fixed-shape equivalence identifies every
corrected Q support with the same source-labelled prefix tree
F(c) = Int(S) ⊕ R. The genuine Q terminal corresponding to a
literal R marker may vary in ambient length with the marked
mixed-product point, but its direction below EVERY original
interior vertex is independent of that point.

For an old interior node s and child direction i, define the
fixed incidence with a vertex labelled by either another old
node t or by a literal marker r:
  s++[i] prefix t, respectively s++[i] prefix r.

The realization in any genuine corrected Q(x) preserves and
reflects this incidence. Consequently any two corrected Q
outputs match not only as prefix trees, but also in every
first ambient direction at each original interior vertex.

This is a fixed direction-labelled SOURCE SHAPE theorem. It
does not yet construct the canonical homogeneous first-l model
address assignment required by Definition 24, or establish the
abstract model boundary A-to-literal-R equivalence.
-/

namespace DualTree.ForwardQFixedDirectionShape

open ForwardSourceQTree
open ForwardQFixedVertexShape
open ForwardQFixedPrefixIso
open ForwardQMarkerCoverage

/-- The first-direction cone membership of a fixed source-labelled
vertex, measured from a particular fixed old interior vertex. -/
def FixedChildCone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : OldVertex c) (i : Fin b) :
    FixedShape c → Prop
  | Sum.inl t => IsPrefix (s.1 ++ [i]) t.1
  | Sum.inr r => IsPrefix (s.1 ++ [i]) r.1

/-- The genuine Q-cone below every fixed original interior node
has precisely the expected label-independent first direction.
The nontrivial R case uses the previously verified actual
projected-marker child-cone theorem, not just abstract prefix
isomorphism. -/
theorem realize_old_childCone_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : OldVertex c)
    (i : Fin b)
    (v : FixedShape c) :
    IsPrefix (s.1 ++ [i]) (realize c x v).1 ↔
      FixedChildCone c s i v := by
  cases v with
  | inl t =>
      change IsPrefix (s.1 ++ [i]) t.1 ↔
        IsPrefix (s.1 ++ [i]) t.1
      exact Iff.rfl
  | inr r =>
      change IsPrefix (s.1 ++ [i])
        (markedProjection c x (bulletForMarker c r)).1 ↔
        IsPrefix (s.1 ++ [i]) r.1
      have hsBase : s.1 ∈ oldBase c :=
        (ForwardQFixedBase.oldBase_mem_iff_original_interior
          c s.1).2 s.2
      exact ForwardQMarkerDirectionalIncidence.oldBase_childCone_projection_iff_marker
        c x r s.1 hsBase i

/-- Every corrected Q input has the SAME first ambient direction
incidence at every original interior node, for every other
old vertex or literal-R-labelled terminal vertex. -/
theorem realize_old_childCone_invariant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (s : OldVertex c)
    (i : Fin b)
    (v : FixedShape c) :
    IsPrefix (s.1 ++ [i]) (realize c x v).1 ↔
      IsPrefix (s.1 ++ [i]) (realize c y v).1 := by
  exact (realize_old_childCone_iff c x s i v).trans
    (realize_old_childCone_iff c y s i v).symm

end DualTree.ForwardQFixedDirectionShape
