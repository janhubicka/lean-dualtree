import DualTree.CanonicalSupportWalk
import DualTree.CompleteSkewMeet

/-!
# Canonical starting root for the support-direction walk

A complete skew support is rooted. This fact is immediate for a
singleton and follows from the printed rootedness clause otherwise.
Extracting that root eliminates one of the parameters of the
constructive support walk and proves that its empty source address
maps into the support.

This does not by itself establish that every address of length
less than k follows an available support branch, that intrinsic
heights equal address lengths, or that the canonical walk gives
the full source isomorphism I_T of Lemma 27.
-/

namespace DualTree.CompleteSupportRoot

/-- Every complete skew support has a root which is a prefix of all
its vertices, including in the singleton case of the source definition. -/
theorem exists_root {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    ∃ r : Node b, r ∈ T ∧ ∀ t : Node b, t ∈ T → IsPrefix r t := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew : SkewTree.skewB SkewTree.paperAuxB T = true := hc.1
  by_cases hone : T.length = 1
  · cases T with
    | nil =>
        simp at hone
    | cons r ts =>
        cases ts with
        | nil =>
            refine ⟨r, by simp, ?_⟩
            intro t ht
            have htr : t = r := by simpa using ht
            subst t
            exact isPrefix_refl r
        | cons u us =>
            simp at hone
  · have hroot : SkewTree.rootedB T = true :=
      CompleteSkewMeet.rootedB_of_skew_nonSingleton
        SkewTree.paperAuxB T hskew hone
    unfold SkewTree.rootedB at hroot
    rcases List.any_eq_true.mp hroot with ⟨r, hr, htest⟩
    refine ⟨r, hr, ?_⟩
    intro t ht
    exact DirectionalSupport.prefix_of_isPrefixOf_true
      ((List.all_eq_true.mp htest) t ht)

/-- The canonical root chosen from the complete support itself. -/
noncomputable def rootOf {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    Node b :=
  Classical.choose (exists_root T hcomplete)

/-- The chosen canonical root belongs to the complete support. -/
theorem rootOf_mem {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    rootOf T hcomplete ∈ T :=
  (Classical.choose_spec (exists_root T hcomplete)).1

/-- Every support node extends the selected canonical root. -/
theorem rootOf_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : Node b) (ht : t ∈ T) :
    IsPrefix (rootOf T hcomplete) t :=
  (Classical.choose_spec (exists_root T hcomplete)).2 t ht

/-- The concrete root-anchored candidate for the map I_T. -/
noncomputable def canonicalWalk {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (address : Node b) : Node b :=
  CanonicalSupportWalk.walk T (rootOf T hcomplete) address

/-- The empty address is sent to the support root. -/
theorem canonicalWalk_nil {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    canonicalWalk T hcomplete [] = rootOf T hcomplete := by
  rfl

/-- The root-anchored walk is prefix-preserving for all finite addresses. -/
theorem canonicalWalk_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    {u v : Node b} (h : IsPrefix u v) :
    IsPrefix (canonicalWalk T hcomplete u)
      (canonicalWalk T hcomplete v) :=
  CanonicalSupportWalk.walk_prefix T (rootOf T hcomplete) h

/-- Every admissible address is sent to an actual support node. -/
theorem canonicalWalk_mem_of_admissible {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (address : Node b)
    (hvalid : CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete) address) :
    canonicalWalk T hcomplete address ∈ T :=
  CanonicalSupportWalk.walk_mem_of_admissible T
    (rootOf T hcomplete) address
    (rootOf_mem T hcomplete) hvalid

/-- The root-anchored map also supplies prefix-preserving cone projections. -/
theorem canonicalProjection_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (base : Node b) {u v : Node b}
    (h : IsPrefix u v) :
    IsPrefix
      (ConeProjectionAlgebra.projection
        (canonicalWalk T hcomplete) base u)
      (ConeProjectionAlgebra.projection
        (canonicalWalk T hcomplete) base v) := by
  have hp : ∀ {x y : Node b},
      IsPrefix x y →
        IsPrefix (canonicalWalk T hcomplete x)
          (canonicalWalk T hcomplete y) := by
    intro x y hxy
    exact canonicalWalk_prefix T hcomplete hxy
  exact ConeProjectionAlgebra.projection_prefix
    (canonicalWalk T hcomplete) hp base h

end DualTree.CompleteSupportRoot
