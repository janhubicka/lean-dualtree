import DualTree.ForwardQMarkedTerminals
import DualTree.ForwardQFixedBase

/-!
# Source-facing terminality and ambient containment of corrected Q

The generic corrected Q terminal-projection theorem requires all
retained old-base nodes to lie at/before the forward auxiliary cut.
The exact forward signature interior equality identifies this base
with the original source interior and establishes the required cut
inequality automatically.

We discharge the base assumption for the *actual* corrected Q.Frame
and show, without extra axioms:

* every projected D₂ node is terminal in the reconstructed Q support;
* every Q interior vertex belongs to the original source interior;
* every node of Q lies in its genuinely forward-complete ambient
  support T.

These are one-way interior facts. Persistence of all original
interior vertices, exact intrinsic ranks, semi-complete skewness,
the reconstructed word and the colouring argument are separate.
-/

namespace DualTree.ForwardQSourceTerminals

open ForwardSourceQTree

/-- The fixed-old-base cut hypothesis is a proved source fact,
not an additional assumption on a corrected Q input. -/
theorem literal_oldBase_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    ∀ s, s ∈ oldBase c → ForwardAux s c.cut := by
  intro s hs
  exact ForwardQFixedBase.oldBase_before_cut c s hs

/-- All newly projected points are leaves of the *actual*
corrected source-facing Q tree under forward auxiliary order. -/
theorem markedProjection_terminal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    (markedProjection c x i).1 ∉
      SkewTree.interior (nodes c x).toList := by
  exact ForwardQMarkedTerminals.markedProjection_not_interior
    c x (literal_oldBase_before_cut c) i

/-- No newly projected D₂ point can introduce an extra
branching vertex: every interior of corrected Q was already
an interior of the source starred tree. -/
theorem Q_interior_subset_original
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior (nodes c x).toList) :
    s ∈ SkewTree.interior c.source.tree := by
  have hsBase : s ∈ oldBase c :=
    ForwardQMarkedTerminals.interior_subset_oldBase
      c x (literal_oldBase_before_cut c) s hs
  exact (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).1
    hsBase

/-- Every retained or newly projected vertex of Q is in the
genuinely forward-complete ambient support T. -/
theorem Q_nodes_subset_complete
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ nodes c x) :
    s ∈ c.T := by
  classical
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hs
  rcases Finset.mem_union.mp hs with hbase | hmark
  · exact ForwardQFixedBase.oldBase_subset_complete
      c s (List.mem_toFinset.mp hbase)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmark
    rw [← hi]
    exact (markedProjection c x i).2

end DualTree.ForwardQSourceTerminals
