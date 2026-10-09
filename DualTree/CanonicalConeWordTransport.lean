import DualTree.CanonicalConeCoordinates
import DualTree.ConeProjectionAlignment

/-!
# Connecting concrete canonical cone projections to the cone-word decoder

The canonical skew-support map I_T is constructed and verified on all
source addresses below k. Its underlying successor walk is also defined
on arbitrary finite addresses, although only the intrinsically bounded
ones are guaranteed to lie in the complete support.

This file uses that total walk to replace the formerly abstract I and
P hypotheses in the root-alignment argument for the repaired three-way
cone-word decoder. The totalized projection agrees with the genuine
support-valued cone projection on every certified safe tail.

The resulting alignment lemmas do not silently assert support membership
at an overlong address or complete the global coding Q. The domain
correction and source-variable-address matching remain separate tasks.
-/

namespace DualTree.CanonicalConeWordTransport

/-- The total prefix-preserving extension of the actual canonical
cone projection rooted at a support vertex. -/
noncomputable def totalProjection {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T}) :
    Node b → Node b :=
  ConeProjectionAlgebra.projection
    (CompleteSupportRoot.canonicalWalk T hcomplete)
    (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1

/-- The totalized projection sends the empty local address to its
actual support frontier, not an abstractly supplied root. -/
theorem totalProjection_empty {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T}) :
    totalProjection T hcomplete frontier [] = frontier.1 := by
  have hroot :
      CompleteSupportRoot.canonicalWalk T hcomplete
          (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 =
        frontier.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete frontier)
  simpa [totalProjection, ConeProjectionAlgebra.projection] using hroot

/-- Prefix preservation of total canonical cone coordinates needs no
additional geometric hypotheses. -/
theorem totalProjection_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T})
    {u v : Node b} (huv : IsPrefix u v) :
    IsPrefix
      (totalProjection T hcomplete frontier u)
      (totalProjection T hcomplete frontier v) := by
  have hmono :
      ∀ {x y : Node b},
        IsPrefix x y →
          IsPrefix
            (CompleteSupportRoot.canonicalWalk T hcomplete x)
            (CompleteSupportRoot.canonicalWalk T hcomplete y) := by
    intro x y hxy
    exact CompleteSupportRoot.canonicalWalk_prefix T hcomplete hxy
  exact ConeProjectionAlgebra.projection_prefix
    (CompleteSupportRoot.canonicalWalk T hcomplete) hmono
    (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 huv

/-- Every totalized projection lies above its frontier in the
ambient prefix order, even when it has reached a missing branch. -/
theorem totalProjection_cone {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T})
    (z : Node b) :
    IsPrefix frontier.1 (totalProjection T hcomplete frontier z) := by
  have hmono :
      ∀ {x y : Node b},
        IsPrefix x y →
          IsPrefix
            (CompleteSupportRoot.canonicalWalk T hcomplete x)
            (CompleteSupportRoot.canonicalWalk T hcomplete y) := by
    intro x y hxy
    exact CompleteSupportRoot.canonicalWalk_prefix T hcomplete hxy
  have hroot :
      CompleteSupportRoot.canonicalWalk T hcomplete
          (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 =
        frontier.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete frontier)
  exact ConeProjectionAlgebra.projection_rooted_at_frontier
    (CompleteSupportRoot.canonicalWalk T hcomplete) hmono frontier.1
    (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 z
    hroot

/-- On every intrinsically safe tail, the totalized projection is
definitionally the same node as the genuine support-valued projection. -/
theorem totalProjection_eq_project {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T})
    (z : CanonicalConeCoordinates.SourceTail T hcomplete frontier) :
    totalProjection T hcomplete frontier z.1 =
      (CanonicalConeCoordinates.project T hcomplete frontier z).1 := by
  rfl

/-- The actual canonical map discharges the geometric hypotheses
needed for every variable emitted by the repaired cone-word decoder. -/
theorem lifted_root_prefix
    {b n m k : Nat} {α : Type*}
    (T A : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T})
    (a : α)
    (hfront : SkewTree.heightAt T frontier.1 ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (z : BoundedNode b n) (r : Node b)
    (hr : ConeWordLift.liftAtCone T A frontier.1 a hfront
      w.word
      (fun v : w.Vars =>
        totalProjection T hcomplete frontier v.1.1) z = Sum.inr r) :
    IsPrefix r (totalProjection T hcomplete frontier z.1) := by
  have hmono :
      ∀ {x y : Node b},
        IsPrefix x y →
          IsPrefix
            (CompleteSupportRoot.canonicalWalk T hcomplete x)
            (CompleteSupportRoot.canonicalWalk T hcomplete y) := by
    intro x y hxy
    exact CompleteSupportRoot.canonicalWalk_prefix T hcomplete hxy
  have hroot :
      CompleteSupportRoot.canonicalWalk T hcomplete
          (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 =
        frontier.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete frontier)
  exact ConeProjectionAlignment.lifted_root_prefix
    T A frontier.1
    (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1
    a hfront w (CompleteSupportRoot.canonicalWalk T hcomplete)
    hmono hroot z r hr

/-- The complete-skew source map also supplies root alignment of
the resulting source-variable substitution once local root addresses
are identified with their actual images. -/
theorem source_root_alignment
    {b n m k N : Nat} {α β : Type*}
    (f : VariableWord b N β)
    (T A : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (frontier : {t : Node b // t ∈ T})
    (a : α)
    (hfront : SkewTree.heightAt T frontier.1 ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (address : f.Vars → BoundedNode b n)
    (haddress : ∀ v : f.Vars,
      totalProjection T hcomplete frontier (address v).1 = v.1.1)
    (ρ : f.Vars → Sum α (Node b))
    (hcode : ∀ v : f.Vars,
      ρ v = ConeWordLift.liftAtCone T A frontier.1 a hfront
        w.word
        (fun u : w.Vars =>
          totalProjection T hcomplete frontier u.1.1)
        (address v))
    (v : f.Vars) (r : Node b)
    (hρ : ρ v = Sum.inr r) :
    IsPrefix r v.1.1 := by
  have hmono :
      ∀ {x y : Node b},
        IsPrefix x y →
          IsPrefix
            (CompleteSupportRoot.canonicalWalk T hcomplete x)
            (CompleteSupportRoot.canonicalWalk T hcomplete y) := by
    intro x y hxy
    exact CompleteSupportRoot.canonicalWalk_prefix T hcomplete hxy
  have hroot :
      CompleteSupportRoot.canonicalWalk T hcomplete
          (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1 =
        frontier.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete frontier)
  exact ConeProjectionAlignment.source_root_alignment
    f T A frontier.1
    (CompleteSupportSurjective.inverseAddress T hcomplete frontier).1
    a hfront w (CompleteSupportRoot.canonicalWalk T hcomplete)
    hmono hroot address haddress ρ hcode v r hρ

end DualTree.CanonicalConeWordTransport
