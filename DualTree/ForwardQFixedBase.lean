import DualTree.ForwardSignatureInteriorExact
import DualTree.ForwardSourceQTree

/-!
# The actual fixed base of the globally forward-repaired Q tree

The source-facing Q skeleton is built from the corrected signature
S' by retaining its interior together with the final branching cut.
ForwardSignatureInteriorExact proved that this retained base is
exactly the original source's interior, as a set.

Here we instantiate that equality for the fully typed Q.Frame.
This discharges the two conditions needed by the subsequent
terminal/level arguments:

* every base node is at or before the retained maximal cut
  in the forward auxiliary order;
* every base node belongs to the enclosing forward-complete
  support T.

The original interior is therefore retained inside the new
Q node set. No claim is made yet that these retained vertices
remain interior in Q or that its projected points satisfy
the remaining skew level conditions.
-/

namespace DualTree.ForwardQFixedBase

open ForwardSourceQTree

/-- The literal fixed base Int(S') ∪ {cut} of the corrected
Q tree coincides with the original starred source interior. -/
theorem oldBase_mem_iff_original_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b) :
    s ∈ oldBase c ↔ s ∈ SkewTree.interior c.source.tree := by
  exact ForwardSignatureInteriorExact.oldBase_mem_iff_original_interior
    c.source c.cut c.hcut c.hmax c.hout s

/-- Every retained Q base vertex is in the inclusive
forward auxiliary initial segment of the maximal cut. -/
theorem oldBase_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ oldBase c) :
    ForwardAux s c.cut := by
  have hsOld : s ∈ SkewTree.interior c.source.tree :=
    (oldBase_mem_iff_original_interior c s).1 hs
  simpa [SkewTree.forwardAuxB] using c.hmax s hsOld

/-- Every retained old vertex belongs to the enclosing
genuinely forward-complete support. -/
theorem oldBase_subset_complete
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ oldBase c) :
    s ∈ c.T := by
  have hsOld : s ∈ SkewTree.interior c.source.tree :=
    (oldBase_mem_iff_original_interior c s).1 hs
  have hsSource : s ∈ c.source.tree :=
    (List.mem_filter.mp hsOld).1
  exact c.hST s hsSource

/-- The original entire interior is retained in the
source-facing corrected Q node set, for arbitrary typed
D₀/D₂ mixed-product input. -/
theorem originalInterior_mem_Q
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    s ∈ nodes c x := by
  exact oldBase_mem c x s
    ((oldBase_mem_iff_original_interior c s).2 hs)

/-- In particular, the retained cut belongs to the
corrected reconstructed Q support. -/
theorem cut_mem_Q
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    c.cut ∈ nodes c x := by
  exact originalInterior_mem_Q c x c.cut c.hcut

end DualTree.ForwardQFixedBase
