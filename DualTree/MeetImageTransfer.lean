import DualTree.Lemma27LiteralMeet

/-!
# Transporting ambient meets through a direction-preserving prefix map

An isomorphism of abstract rooted prefix-posets need not preserve
the actual ambient longest common prefixes (one can insert
unrecorded common prefix nodes between consecutive support levels).

Here is an exact additional condition: the map must preserve,
for every OLD meet node w, which first ambient directions are
occupied by each of its descendants. If the ambient meet of any
two distinct source nodes is represented by such a fixed base node,
then all ambient meets are preserved by the new labels.

The proof is local. If the new ambient meet strictly extended its
old fixed meet node w, both images would share an extra first
direction after w. Direction preservation would give the same
extra common direction to their source nodes, contradicting that
their source meet was exactly w.

This abstract lemma is deliberately independent of the two
specific finite skeletons in Lemma 27; a separate file applies it
to the literal leaf-replacement map.
-/

namespace DualTree.MeetImageTransfer

/-- The image of any two source points has its ambient meet
represented by an image point, provided all distinct source
meets lie in a fixed base and first directions are preserved there. -/
theorem meet_represented_of_prefix_and_directions
    {b : Nat} {P : Type*}
    (source target : P → Node b)
    (Base : P → Prop)
    (hfix : ∀ w, Base w → target w = source w)
    (hprefix : ∀ a c,
      IsPrefix (target a) (target c) ↔
        IsPrefix (source a) (source c))
    (hdir : ∀ w, Base w → ∀ a (i : Fin b),
      IsPrefix (source w ++ [i]) (target a) ↔
        IsPrefix (source w ++ [i]) (source a))
    (hmeets : ∀ a c, a ≠ c →
      ∃ w, Base w ∧
        source w = MeetGeometry.commonPrefix (source a) (source c))
    (a c : P) :
    ∃ w : P, target w = MeetGeometry.commonPrefix (target a) (target c) := by
  by_cases heq : a = c
  · subst c
    exact ⟨a, (InteriorMarkerMeet.commonPrefix_self (target a)).symm⟩
  · obtain ⟨w, hw, hsourceMeet⟩ := hmeets a c heq
    have hsrcA : IsPrefix (source w) (source a) := by
      rw [hsourceMeet]
      exact MeetGeometry.commonPrefix_prefix_left (source a) (source c)
    have hsrcC : IsPrefix (source w) (source c) := by
      rw [hsourceMeet]
      exact MeetGeometry.commonPrefix_prefix_right (source a) (source c)
    have hdstA : IsPrefix (target w) (target a) :=
      (hprefix w a).2 hsrcA
    have hdstC : IsPrefix (target w) (target c) :=
      (hprefix w c).2 hsrcC
    have hdstMeet : IsPrefix (target w)
        (MeetGeometry.commonPrefix (target a) (target c)) :=
      MeetGeometry.prefix_commonPrefix hdstA hdstC
    have hEq :
        MeetGeometry.commonPrefix (target a) (target c) = target w := by
      by_contra hne
      have hstrict :
          IsStrictPrefix (target w)
            (MeetGeometry.commonPrefix (target a) (target c)) :=
        ⟨hdstMeet, Ne.symm hne⟩
      obtain ⟨i, hi⟩ :=
        SupportReachability.first_direction_of_strictPrefix hstrict
      have hdirA : IsPrefix (target w ++ [i]) (target a) :=
        isPrefix_trans hi
          (MeetGeometry.commonPrefix_prefix_left (target a) (target c))
      have hdirC : IsPrefix (target w ++ [i]) (target c) :=
        isPrefix_trans hi
          (MeetGeometry.commonPrefix_prefix_right (target a) (target c))
      have hdirSourceA : IsPrefix (source w ++ [i]) (source a) :=
        (hdir w hw a i).1 (by simpa [hfix w hw] using hdirA)
      have hdirSourceC : IsPrefix (source w ++ [i]) (source c) :=
        (hdir w hw c i).1 (by simpa [hfix w hw] using hdirC)
      have hlong : IsPrefix (source w ++ [i])
          (MeetGeometry.commonPrefix (source a) (source c)) :=
        MeetGeometry.prefix_commonPrefix hdirSourceA hdirSourceC
      rw [← hsourceMeet] at hlong
      have hle := prefix_length_le hlong
      simp only [List.length_append, List.length_singleton] at hle
      omega
    exact ⟨w, hEq.symm⟩

/-- A finite target node set covered by such a direction-preserving
prefix map is closed under the actual ambient longest-prefix meet. -/
theorem meetClosed_of_prefix_and_directions
    {b : Nat} {P : Type*}
    (source target : P → Node b)
    (Base : P → Prop)
    (hfix : ∀ w, Base w → target w = source w)
    (hprefix : ∀ a c,
      IsPrefix (target a) (target c) ↔
        IsPrefix (source a) (source c))
    (hdir : ∀ w, Base w → ∀ a (i : Fin b),
      IsPrefix (source w ++ [i]) (target a) ↔
        IsPrefix (source w ++ [i]) (source a))
    (hmeets : ∀ a c, a ≠ c →
      ∃ w, Base w ∧
        source w = MeetGeometry.commonPrefix (source a) (source c))
    (S : List (Node b))
    (hmem : ∀ p, target p ∈ S)
    (hsurj : ∀ v, v ∈ S → ∃ p, target p = v) :
    MeetGeometry.MeetClosed S := by
  intro x y hx hy
  obtain ⟨a, rfl⟩ := hsurj x hx
  obtain ⟨c, rfl⟩ := hsurj y hy
  obtain ⟨w, hw⟩ :=
    meet_represented_of_prefix_and_directions
      source target Base hfix hprefix hdir hmeets a c
  rw [← hw]
  exact hmem w

end DualTree.MeetImageTransfer
