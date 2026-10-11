import DualTree.ForwardQLiteralSkeletonMeets
import DualTree.ForwardQMarkerCoverage
import DualTree.ForwardQFixedBase
import DualTree.MeetClosedDirectionConverse

/-!
# Meet closure of the genuine forward-corrected Q support

The source signature skeleton `Int(S) ∪ R` is ambient meet-closed.
The actual Q tree replaces each terminal first-exit marker r∈R by
a projected node q(r) extending r within its own sorted complete
support frontier cone.

Merely preserving the abstract prefix poset is not sufficient for
preserving ambient meets. Instead we use the *first-exit antichain*
property to prove a generic terminal-extension lemma: when the
original support is meet-closed, markers form an antichain, no marker
prefixes an original interior node, and all markers have original
support descendants, then replacing distinct markers by *arbitrary
extensions in their cones* retains ambient meet closure.

We instantiate this lemma on the actual D₂ projections, using the
bijective forward-sorted marker/bullet-coordinate correspondence.
Consequently Q is ambient meet-closed, and every interior support
vertex has at most one immediate successor in any ambient direction.
This is a geometric milestone, not a proof of semi-complete skewness,
its numerical branching counts, or the mixed-product word and colour.
-/

namespace DualTree.ForwardQMeetClosed

/-- A marker antichain may be extended arbitrarily along its cones
without losing ambient meet closure of its union with the old interior. -/
theorem meetClosed_of_terminal_extensions
    {b : Nat} {M : Type*}
    (S R : List (Node b))
    (hmeet : MeetGeometry.MeetClosed S)
    (hdesc : ∀ r, r ∈ R → ∃ t, t ∈ S ∧ IsPrefix r t)
    (hanti : ∀ r s, r ∈ R → s ∈ R → IsPrefix r s → r = s)
    (hnot : ∀ r, r ∈ R →
      ∀ u, u ∈ SkewTree.interior S → ¬ IsPrefix r u)
    (marker : M → Node b) (hmarker : Function.Injective marker)
    (hmarkR : ∀ i, marker i ∈ R)
    (project : M → Node b)
    (hproject : ∀ i, IsPrefix (marker i) (project i))
    (W : List (Node b))
    (hW : ∀ v, v ∈ W ↔
      v ∈ SkewTree.interior S ∨ ∃ i : M, project i = v) :
    MeetGeometry.MeetClosed W := by
  intro x y hx hy
  by_cases heq : x = y
  · subst y
    rw [InteriorMarkerMeet.commonPrefix_self]
    exact hx
  have hxto := (hW x).1 hx
  have hyto := (hW y).1 hy
  apply (hW _).2
  left
  rcases hxto with hxold | ⟨i, hi⟩
  · rcases hyto with hyold | ⟨j, hj⟩
    · have hxS : x ∈ S := (List.mem_filter.mp hxold).1
      have hyS : y ∈ S := (List.mem_filter.mp hyold).1
      exact InteriorMarkerMeet.commonPrefix_interior_of_distinct_support
        S hmeet hxS hyS heq
    · subst y
      have hsource :
          MeetGeometry.commonPrefix x (marker j) ∈
            SkewTree.interior S := by
        obtain ⟨t, ht, hmt⟩ := hdesc (marker j) (hmarkR j)
        exact InteriorMarkerMeet.meet_base_marker_interior
          S hmeet hxold ht hmt (hnot (marker j) (hmarkR j) x hxold)
      have hext :=
        InteriorMarkerMeet.commonPrefix_right_extension_of_not_prefix
          (hproject j) (hnot (marker j) (hmarkR j) x hxold)
      rw [hext] at hsource
      exact hsource
  · subst x
    rcases hyto with hyold | ⟨j, hj⟩
    · have hsource :
          MeetGeometry.commonPrefix y (marker i) ∈
            SkewTree.interior S := by
        obtain ⟨t, ht, hmt⟩ := hdesc (marker i) (hmarkR i)
        exact InteriorMarkerMeet.meet_base_marker_interior
          S hmeet hyold ht hmt (hnot (marker i) (hmarkR i) y hyold)
      have hext :=
        InteriorMarkerMeet.commonPrefix_right_extension_of_not_prefix
          (hproject i) (hnot (marker i) (hmarkR i) y hyold)
      rw [MeetGeometry.commonPrefix_comm]
      rw [← hext]
      exact hsource
    · subst y
      have hij : i ≠ j := by
        intro h
        subst j
        exact heq rfl
      have hmarkNe : marker i ≠ marker j := by
        intro h
        exact hij (hmarker h)
      have hnij : ¬ IsPrefix (marker i) (marker j) := by
        intro h
        exact hmarkNe (hanti (marker i) (marker j)
          (hmarkR i) (hmarkR j) h)
      have hnji : ¬ IsPrefix (marker j) (marker i) := by
        intro h
        exact hmarkNe ((hanti (marker j) (marker i)
          (hmarkR j) (hmarkR i) h).symm)
      obtain ⟨u, hu, hiu⟩ := hdesc (marker i) (hmarkR i)
      obtain ⟨v, hv, hjv⟩ := hdesc (marker j) (hmarkR j)
      have hsource :
          MeetGeometry.commonPrefix (marker i) (marker j) ∈
            SkewTree.interior S :=
        InteriorMarkerMeet.meet_markers_interior
          S hmeet hu hv hiu hjv hnij hnji
      have hext :=
        InteriorMarkerMeet.commonPrefix_extensions_of_incomparable
          (hproject i) (hproject j) hnij hnji
      rw [hext] at hsource
      exact hsource

/-- Every selected bullet coordinate of the *actual* Q
construction has a unique corresponding literal R marker. -/
noncomputable def markerOfBullet
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (i : MixedProduct.BulletIndex (ForwardSourceQTree.kind c)) :
    ForwardSortedMixedProduct.Marker c.source c.cut c.hout :=
  Classical.choose
    ((ForwardSortedMixedProduct.bulletIndex_bijective
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly).2 i)

/-- The chosen marker's genuine sorted frontier coordinate
is exactly the given D₂ bullet coordinate. -/
theorem bulletForMarker_markerOfBullet
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (i : MixedProduct.BulletIndex (ForwardSourceQTree.kind c)) :
    ForwardQMarkerCoverage.bulletForMarker c (markerOfBullet c i) = i :=
  Classical.choose_spec
    ((ForwardSortedMixedProduct.bulletIndex_bijective
      c.source c.cut c.hcut c.hmax c.hout
      c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly).2 i)

/-- The source marker recovered from a bullet coordinate
is injective: a marker cannot represent two distinct bullets. -/
theorem markerOfBullet_injective
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α) :
    Function.Injective (markerOfBullet c) := by
  intro i j h
  calc
    i = ForwardQMarkerCoverage.bulletForMarker c (markerOfBullet c i) :=
      (bulletForMarker_markerOfBullet c i).symm
    _ = ForwardQMarkerCoverage.bulletForMarker c (markerOfBullet c j) :=
      congrArg _ h
    _ = j := bulletForMarker_markerOfBullet c j

/-- Actual Q bullet projections extend the literal marker
recovered from their coordinate, with no choice of a substitute cone. -/
theorem recoveredMarker_prefix_projection
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c)
    (i : MixedProduct.BulletIndex (ForwardSourceQTree.kind c)) :
    IsPrefix (markerOfBullet c i).1
      (ForwardSourceQTree.markedProjection c x i).1 := by
  have h :=
    ForwardQMarkerCoverage.marker_prefix_projected_point
      c x (markerOfBullet c i)
  rw [bulletForMarker_markerOfBullet c i] at h
  exact h

/-- The actual forward-corrected Q support is ambient meet-closed:
every meet of two Q vertices is still a retained original interior
vertex (unless the vertices coincide). -/
theorem Q_meetClosed
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c) :
    MeetGeometry.MeetClosed (ForwardSourceQTree.nodes c x).toList := by
  let M := MixedProduct.BulletIndex (ForwardSourceQTree.kind c)
  let R := ForwardStarredSignature.literalR c.source c.cut c.hout
  let marker : M → Node b := fun i => (markerOfBullet c i).1
  let project : M → Node b :=
    fun i => (ForwardSourceQTree.markedProjection c x i).1
  have hmarkInjective : Function.Injective marker := by
    intro i j h
    exact markerOfBullet_injective c (Subtype.ext h)
  have hW : ∀ v : Node b,
      v ∈ (ForwardSourceQTree.nodes c x).toList ↔
        v ∈ SkewTree.interior c.source.tree ∨
          ∃ i : M, project i = v := by
    intro v
    constructor
    · intro hv
      have hfin : v ∈ ForwardSourceQTree.nodes c x :=
        Finset.mem_toList.mp hv
      change v ∈ (ForwardSourceQTree.oldBase c).toFinset ∪
        (Finset.univ : Finset M).image project at hfin
      rcases Finset.mem_union.mp hfin with hold | hnew
      · exact Or.inl ((ForwardQFixedBase.oldBase_mem_iff_original_interior
          c v).1 (List.mem_toFinset.mp hold))
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hnew
        exact Or.inr ⟨i, hi⟩
    · intro hv
      rcases hv with hold | ⟨i, hi⟩
      · exact Finset.mem_toList.mpr
          (ForwardQFixedBase.originalInterior_mem_Q c x v hold)
      · rw [← hi]
        exact Finset.mem_toList.mpr
          (ForwardSourceQTree.markedProjection_mem c x i)
  exact meetClosed_of_terminal_extensions
    c.source.tree R
    (ForwardQLiteralSkeletonMeets.source_meetClosed c)
    (ForwardQLiteralSkeletonMeets.literalMarker_has_source_descendant c)
    (ForwardQLiteralSkeletonMeets.literalR_antichain c)
    (ForwardQLiteralSkeletonMeets.literalR_not_prefix_interior c)
    marker hmarkInjective
    (fun i => (markerOfBullet c i).2)
    project
    (fun i => recoveredMarker_prefix_projection c x i)
    (ForwardSourceQTree.nodes c x).toList hW

/-- In the true repaired Q support, no two immediate support
successors can occupy the same ambient direction. -/
theorem Q_atMostOneDirection
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (x : ForwardSourceQTree.Input c) :
    MeetClosedFromBranching.AtMostOneDirection
      (ForwardSourceQTree.nodes c x).toList := by
  exact MeetClosedDirectionConverse.atMostOneDirection_of_meetClosed
    (ForwardSourceQTree.nodes c x).toList (Q_meetClosed c x)

end DualTree.ForwardQMeetClosed
