import DualTree.ForwardSourceInteriorFirstL
import DualTree.ForwardSourceLeafMarkerEquiv
import DualTree.ForwardQAllDirections

/-!
# Genuine source leaves reached by the canonical model boundary

The source interior has been identified with exactly the first
l homogeneous forward-heap addresses. A model boundary address
has the form p ++ [i] where p is interior and its child is
not interior.

Because p realizes a genuine source interior vertex, source
semi-completeness supplies the unique next support successor
in direction i. Thus the boundary address is admissible and
its canonical realization is an ACTUAL source leaf.

We prove the resulting map from Definition 24's model
boundary A_l into original source leaves is injective.
Surjectivity and the final composition A_l ≃ SourceLeaf ≃ R
are still separate obligations; no cardinality shortcut is
used to assume them.
-/

namespace DualTree.ForwardSourceBoundaryLeaves

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceAddressOrder
open ForwardSourceHeapInitial
open ForwardSourceInteriorFirstL
open ForwardSourceLeafMarkerEquiv
open ForwardModelBoundaryHeap

/-- A generic support walk admits a final direction if and only
if its prefix is admissible and that directional branch really
exists at the realized prefix vertex. -/
theorem admissible_append_singleton_iff
    {b : Nat} (T : List (Node b))
    (root p : Node b) (i : Fin b) :
    CanonicalSupportWalk.Admissible T root (p ++ [i]) ↔
      CanonicalSupportWalk.Admissible T root p ∧
      SkewTree.uniqueBranchB T
        (CanonicalSupportWalk.walk T root p) i = true := by
  induction p generalizing root with
  | nil =>
      simp [CanonicalSupportWalk.Admissible,
        CanonicalSupportWalk.walk]
  | cons j p ih =>
      change
        (SkewTree.uniqueBranchB T root j = true ∧
          CanonicalSupportWalk.Admissible T
            (CanonicalSupportWalk.next T root j) (p ++ [i])) ↔
        (SkewTree.uniqueBranchB T root j = true ∧
          CanonicalSupportWalk.Admissible T
            (CanonicalSupportWalk.next T root j) p) ∧
        SkewTree.uniqueBranchB T
          (CanonicalSupportWalk.walk T
            (CanonicalSupportWalk.next T root j) p) i = true
      rw [ih (CanonicalSupportWalk.next T root j)]
      exact and_assoc.symm

/-- EVERY boundary address of the first l homogeneous model
is admissible for the true source support walk, because its
parent is interior and has a unique successor in each
direction. -/
theorem modelBoundary_admissible
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : {a : Node b // ModelBoundary l a}) :
    CanonicalSupportWalk.Admissible c.source.tree
      (ForwardQRooted.sourceRoot c) a.1 := by
  obtain ⟨p, i, hp, ha⟩ := a.2.2
  have hcut := cut_heapIndex_succ_eq_l hb c
  have hpLe : heapIndex p ≤ heapIndex (cutAddress c).1 := by
    change heapIndex p < l at hp
    omega
  have hpValid :=
    heap_le_cut_admissible hb c p hpLe
  let up : SourceAddress c := ⟨p, hpValid⟩
  have hparentInterior :
      (realize c up).1 ∈ SkewTree.interior c.source.tree :=
    (address_interior_iff_forward_le_cut hb c up).2
      ((ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
        hb p (cutAddress c).1).2 hpLe)
  have hbranch : SkewTree.uniqueBranchB c.source.tree
      (CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) p) i = true :=
    ForwardQAllDirections.source_full_directions
      c (realize c up).1 hparentInterior i
  have hvalid :
      CanonicalSupportWalk.Admissible c.source.tree
        (ForwardQRooted.sourceRoot c) (p ++ [i]) :=
    (admissible_append_singleton_iff c.source.tree
      (ForwardQRooted.sourceRoot c) p i).2 ⟨hpValid, hbranch⟩
  rw [ha]
  exact hvalid

/-- Realize a genuine model boundary address in the original
source. Because it lies outside the first l interior addresses,
its image is a terminal source node. -/
noncomputable def boundaryRealize
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    {a : Node b // ModelBoundary l a} → SourceLeaf c := by
  intro a
  let u : SourceAddress c :=
    ⟨a.1, modelBoundary_admissible hb c a⟩
  refine ⟨(realize c u).1, (realize c u).2, ?_⟩
  intro hinterior
  have hmodel : ModelInterior l a.1 :=
    (modelInterior_iff_sourceInterior_address hb c a.1).2
      ⟨u, rfl, hinterior⟩
  exact a.2.1 hmodel

/-- Distinct canonical model boundary addresses name distinct
source leaves, since admissible source walks are injective.
No arbitrary ordering of R markers enters the map. -/
theorem boundaryRealize_injective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    Function.Injective (boundaryRealize hb c) := by
  intro a d had
  let u : SourceAddress c :=
    ⟨a.1, modelBoundary_admissible hb c a⟩
  let v : SourceAddress c :=
    ⟨d.1, modelBoundary_admissible hb c d⟩
  have hraw :
      (boundaryRealize hb c a).1 =
        (boundaryRealize hb c d).1 :=
    congrArg Subtype.val had
  change (realize c u).1 = (realize c v).1 at hraw
  have huv : u = v :=
    realize_injective c (Subtype.ext hraw)
  have haddr : a.1 = d.1 := by
    exact congrArg Subtype.val huv
  exact Subtype.ext haddr

end DualTree.ForwardSourceBoundaryLeaves
