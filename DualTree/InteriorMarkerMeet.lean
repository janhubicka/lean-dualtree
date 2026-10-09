import DualTree.SemiCompleteSkewMeet
import DualTree.SignatureInteriorPersistence

/-!
# Meet closure of an interior tree with terminal boundary markers

A generic finite-tree lemma for the literal skeleton in Lemma 27.
Let S be a meet-closed finite support, and R an antichain of ambient
boundary markers such that

* every r ∈ R extends to a point of S;
* no marker r is a prefix of an interior point of S.

Then the finite node set Int(S) ∪ R is meet-closed. More precisely,
the ambient meet of any TWO DISTINCT nodes of this set belongs to
Int(S). All proof obligations are completely independent of the
particular auxiliary order and the definition of a starred word.

The key elementary observation is that extending one input of an
ambient longest-common-prefix meet cannot change the meet if that
input is not a prefix of the other.
-/

namespace DualTree.InteriorMarkerMeet

/-- The meet of a node with itself is that node. -/
theorem commonPrefix_self {b : Nat} (x : Node b) :
    MeetGeometry.commonPrefix x x = x := by
  have h := MeetGeometry.commonPrefix_append_left
    x ([] : Node b) ([] : Node b)
  simpa [MeetGeometry.commonPrefix] using h

/-- A shorter prefix is its own meet with any extension. -/
theorem commonPrefix_eq_left_of_prefix {b : Nat}
    {x y : Node b} (hxy : IsPrefix x y) :
    MeetGeometry.commonPrefix x y = x := by
  have hmx := MeetGeometry.commonPrefix_prefix_left x y
  have hxm : IsPrefix x (MeetGeometry.commonPrefix x y) :=
    MeetGeometry.prefix_commonPrefix (isPrefix_refl x) hxy
  exact isPrefix_antisymm hmx hxm

/-- Two ambient prefixes of the same word are comparable. -/
theorem prefix_comparable_of_common_extension {b : Nat}
    {x y z : Node b} (hx : IsPrefix x z) (hy : IsPrefix y z) :
    IsPrefix x y ∨ IsPrefix y x := by
  rcases le_total x.length y.length with hle | hle
  · exact Or.inl (CutFrontier.prefix_of_prefix_length_le hx hy hle)
  · exact Or.inr (CutFrontier.prefix_of_prefix_length_le hy hx hle)

/-- Extending the second argument does not change an ambient meet
if the second argument was not a prefix of the first. -/
theorem commonPrefix_right_extension_of_not_prefix {b : Nat}
    {x y z : Node b}
    (hyz : IsPrefix y z) (hnot : ¬ IsPrefix y x) :
    MeetGeometry.commonPrefix x y =
      MeetGeometry.commonPrefix x z := by
  let m := MeetGeometry.commonPrefix x y
  let n := MeetGeometry.commonPrefix x z
  have hmn : IsPrefix m n :=
    MeetGeometry.prefix_commonPrefix
      (MeetGeometry.commonPrefix_prefix_left x y)
      (isPrefix_trans
        (MeetGeometry.commonPrefix_prefix_right x y) hyz)
  by_cases hlen : n.length ≤ y.length
  · have hny : IsPrefix n y :=
      CutFrontier.prefix_of_prefix_length_le
        (MeetGeometry.commonPrefix_prefix_right x z) hyz hlen
    have hnm : IsPrefix n m :=
      MeetGeometry.prefix_commonPrefix
        (MeetGeometry.commonPrefix_prefix_left x z) hny
    exact isPrefix_antisymm hmn hnm
  · have hyn : IsPrefix y n :=
      CutFrontier.prefix_of_prefix_length_le hyz
        (MeetGeometry.commonPrefix_prefix_right x z) (by omega)
    have hyx : IsPrefix y x :=
      isPrefix_trans hyn
        (MeetGeometry.commonPrefix_prefix_left x z)
    exact False.elim (hnot hyx)

/-- Extending both members of a pair of incomparable ambient
prefixes leaves their longest common prefix unchanged. -/
theorem commonPrefix_extensions_of_incomparable {b : Nat}
    {r s x y : Node b}
    (hrx : IsPrefix r x) (hsy : IsPrefix s y)
    (hnrs : ¬ IsPrefix r s) (hnsr : ¬ IsPrefix s r) :
    MeetGeometry.commonPrefix r s =
      MeetGeometry.commonPrefix x y := by
  have hnry : ¬ IsPrefix r y := by
    intro hry
    rcases prefix_comparable_of_common_extension hry hsy with h | h
    · exact hnrs h
    · exact hnsr h
  calc
    MeetGeometry.commonPrefix r s =
        MeetGeometry.commonPrefix r y :=
      commonPrefix_right_extension_of_not_prefix hsy hnsr
    _ = MeetGeometry.commonPrefix y r :=
      MeetGeometry.commonPrefix_comm r y
    _ = MeetGeometry.commonPrefix y x :=
      commonPrefix_right_extension_of_not_prefix hrx hnry
    _ = MeetGeometry.commonPrefix x y :=
      MeetGeometry.commonPrefix_comm y x

/-- In a meet-closed support the ambient meet of two distinct
support nodes is itself an interior support node. -/
theorem commonPrefix_interior_of_distinct_support {b : Nat}
    (S : List (Node b)) (hmeet : MeetGeometry.MeetClosed S)
    {x y : Node b} (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) :
    MeetGeometry.commonPrefix x y ∈ SkewTree.interior S := by
  let m := MeetGeometry.commonPrefix x y
  have hm : m ∈ S := hmeet x y hx hy
  by_cases hmx : m = x
  · have hmy : IsStrictPrefix m y := by
      refine ⟨MeetGeometry.commonPrefix_prefix_right x y, ?_⟩
      intro hmy
      apply hne
      exact hmx.symm.trans hmy
    exact SignatureInteriorPersistence.interior_of_strict_descendant
      S m y hm hy hmy
  · have hmxStrict : IsStrictPrefix m x :=
      ⟨MeetGeometry.commonPrefix_prefix_left x y, hmx⟩
    exact SignatureInteriorPersistence.interior_of_strict_descendant
      S m x hm hx hmxStrict

/-- If a marker has a support descendant and does not precede
an interior vertex, their meet belongs to the original interior. -/
theorem meet_base_marker_interior {b : Nat}
    (S : List (Node b)) (hmeet : MeetGeometry.MeetClosed S)
    {u r t : Node b}
    (hu : u ∈ SkewTree.interior S)
    (ht : t ∈ S) (hrt : IsPrefix r t)
    (hnot : ¬ IsPrefix r u) :
    MeetGeometry.commonPrefix u r ∈ SkewTree.interior S := by
  have huS : u ∈ S := by
    unfold SkewTree.interior at hu
    exact (List.mem_filter.mp hu).1
  have hut : u ≠ t := by
    intro h
    exact hnot (by simpa [h] using hrt)
  have hmeet :
      MeetGeometry.commonPrefix u t ∈ SkewTree.interior S :=
    commonPrefix_interior_of_distinct_support S hmeet huS ht hut
  have heq :=
    commonPrefix_right_extension_of_not_prefix hrt hnot
  simpa only [heq] using hmeet

/-- Two incomparable markers with support descendants have an
ambient meet belonging to the original support's interior. -/
theorem meet_markers_interior {b : Nat}
    (S : List (Node b)) (hmeet : MeetGeometry.MeetClosed S)
    {r s x y : Node b}
    (hx : x ∈ S) (hy : y ∈ S)
    (hrx : IsPrefix r x) (hsy : IsPrefix s y)
    (hnrs : ¬ IsPrefix r s) (hnsr : ¬ IsPrefix s r) :
    MeetGeometry.commonPrefix r s ∈ SkewTree.interior S := by
  have hnry : ¬ IsPrefix r y := by
    intro hry
    rcases prefix_comparable_of_common_extension hry hsy with h | h
    · exact hnrs h
    · exact hnsr h
  have hxy : x ≠ y := by
    intro heq
    apply hnry
    simpa [heq] using hrx
  have hmeet :
      MeetGeometry.commonPrefix x y ∈ SkewTree.interior S :=
    commonPrefix_interior_of_distinct_support S hmeet hx hy hxy
  rw [commonPrefix_extensions_of_incomparable hrx hsy hnrs hnsr]
  exact hmeet

/-- Under the abstract marker assumptions, the meet of any
two distinct vertices of Int(S) ∪ R lies in Int(S). -/
theorem meet_distinct_interior_union_markers {b : Nat}
    (S R : List (Node b))
    (hmeet : MeetGeometry.MeetClosed S)
    (hdesc : ∀ r, r ∈ R → ∃ t, t ∈ S ∧ IsPrefix r t)
    (hanti : ∀ r s, r ∈ R → s ∈ R → IsPrefix r s → r = s)
    (hnot : ∀ r, r ∈ R →
      ∀ u, u ∈ SkewTree.interior S → ¬ IsPrefix r u)
    {x y : Node b}
    (hx : x ∈ SkewTree.interior S ∨ x ∈ R)
    (hy : y ∈ SkewTree.interior S ∨ y ∈ R)
    (hne : x ≠ y) :
    MeetGeometry.commonPrefix x y ∈ SkewTree.interior S := by
  rcases hx with hxOld | hxMarker
  · rcases hy with hyOld | hyMarker
    · have hxS : x ∈ S := by
        unfold SkewTree.interior at hxOld
        exact (List.mem_filter.mp hxOld).1
      have hyS : y ∈ S := by
        unfold SkewTree.interior at hyOld
        exact (List.mem_filter.mp hyOld).1
      exact commonPrefix_interior_of_distinct_support
        S hmeet hxS hyS hne
    · obtain ⟨t, ht, hyt⟩ := hdesc y hyMarker
      exact meet_base_marker_interior
        S hmeet hxOld ht hyt (hnot y hyMarker x hxOld)
  · rcases hy with hyOld | hyMarker
    · obtain ⟨t, ht, hxt⟩ := hdesc x hxMarker
      rw [MeetGeometry.commonPrefix_comm]
      exact meet_base_marker_interior
        S hmeet hyOld ht hxt (hnot x hxMarker y hyOld)
    · have hnxy : ¬ IsPrefix x y := by
        intro h
        exact hne (hanti x y hxMarker hyMarker h)
      have hnyx : ¬ IsPrefix y x := by
        intro h
        exact hne ((hanti y x hyMarker hxMarker h).symm)
      obtain ⟨t, ht, hxt⟩ := hdesc x hxMarker
      obtain ⟨u, hu, hyu⟩ := hdesc y hyMarker
      exact meet_markers_interior S hmeet ht hu hxt hyu hnxy hnyx

/-- Adding terminal boundary markers to the original interior
preserves ambient meet-closure under the stated abstract hypotheses. -/
theorem meetClosed_interior_union_markers {b : Nat}
    (S R : List (Node b))
    (hmeet : MeetGeometry.MeetClosed S)
    (hdesc : ∀ r, r ∈ R → ∃ t, t ∈ S ∧ IsPrefix r t)
    (hanti : ∀ r s, r ∈ R → s ∈ R → IsPrefix r s → r = s)
    (hnot : ∀ r, r ∈ R →
      ∀ u, u ∈ SkewTree.interior S → ¬ IsPrefix r u) :
    MeetGeometry.MeetClosed (SkewTree.interior S ++ R) := by
  intro x y hx hy
  rw [List.mem_append] at hx hy ⊢
  by_cases hxy : x = y
  · subst y
    rw [commonPrefix_self]
    exact hx
  · exact Or.inl
      (meet_distinct_interior_union_markers
        S R hmeet hdesc hanti hnot hx hy hxy)

end DualTree.InteriorMarkerMeet
