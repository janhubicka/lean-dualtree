import DualTree.ForwardQExceptionalRanks
import DualTree.ForwardQMarkerRanks

/-!
# Exact intrinsic Q height of the final cut's child markers

The corrected literal marker set R contains every ambient child
cut++[i] of the maximal original source interior node cut.
Each child has an assigned sorted D₂ bullet coordinate and
a genuine projected Q node in its corresponding cone.

The projected node has as Q predecessors precisely the old
interior support prefixes of cut together with cut itself.
Thus its intrinsic Q height is

  h_Q(P(cut++[i])) = h_S(cut) + 1,

independently of the ambient-T frontier root, the length of
the local D₂ bullet tail, and whether the child cut++[i]
itself was present as a source support vertex.

Together with ForwardQExceptionalRanks, this supplies an exact
intrinsic Q rank formula for both literal marker types. The
comparison with ambient T heights and word lengths remains open.
-/

namespace DualTree.ForwardQCutChildRank

open ForwardSourceQTree

/-- An original source interior node is a strict ambient prefix
of the immediate child cut++[i] iff it is a prefix of cut itself. -/
theorem interior_prefix_cut_child_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Fin b)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    IsStrictPrefix s (c.cut ++ [i]) ↔ IsPrefix s c.cut := by
  have hsEarly : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hlen : s.length ≤ c.cut.length := by
    rcases hsEarly with hlt | ⟨heq, _⟩ <;> omega
  constructor
  · intro hsc
    exact CutFrontier.prefix_of_prefix_length_le
      hsc.1 ⟨[i], rfl⟩ hlen
  · intro hsc
    refine ⟨isPrefix_trans hsc ⟨[i], rfl⟩, ?_⟩
    intro heq
    have hEqLen := congrArg List.length heq
    simp only [List.length_append, List.length_singleton] at hEqLen
    omega

/-- The intrinsic height of the *actual* corrected Q point in
the cone over cut++[i] is exactly the source cut's height plus one. -/
theorem projected_cut_child_Q_height
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : Fin b) :
    let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
        ⟨c.cut ++ [i],
          ForwardStarredSignature.cut_child_mem_literalR
            c.source c.cut c.hout i⟩
    SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
      SkewTree.heightAt c.source.tree c.cut + 1 := by
  classical
  let marker : ForwardSortedMixedProduct.Marker
      c.source c.cut c.hout :=
    ⟨c.cut ++ [i],
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i⟩
  change SkewTree.heightAt (nodes c x).toList
      (markedProjection c x
        (ForwardQMarkerCoverage.bulletForMarker c marker)).1 =
    SkewTree.heightAt c.source.tree c.cut + 1
  rw [ForwardQMarkerRanks.markedProjection_height_eq_marker_prefix_card
    c x marker]
  have hsourceNodup : c.source.tree.Nodup := by
    have hsemi := c.source.semi_complete
    simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
    have hskew := hsemi.1
    simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
    simpa using hskew.1
  have hpredNodup : (SkewTree.preds c.source.tree c.cut).Nodup := by
    unfold SkewTree.preds
    exact hsourceNodup.filter _
  have hset :
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun u =>
          SkewTree.strictPrefixB u (c.cut ++ [i]) = true) =
      insert c.cut (SkewTree.preds c.source.tree c.cut).toFinset := by
    ext u
    simp only [Finset.mem_filter, List.mem_toFinset,
      Finset.mem_insert, ImmediateSupportHeight.mem_preds_iff]
    constructor
    · rintro ⟨huInterior, huBool⟩
      have huStrict : IsStrictPrefix u (c.cut ++ [i]) :=
        (SkewBranchGeometry.strictPrefixB_iff u (c.cut ++ [i])).1 huBool
      have huCut : IsPrefix u c.cut :=
        (interior_prefix_cut_child_iff c i u huInterior).1 huStrict
      by_cases heq : u = c.cut
      · exact Or.inl heq
      · exact Or.inr ⟨(List.mem_filter.mp huInterior).1,
          ⟨huCut, heq⟩⟩
    · intro h
      rcases h with heq | ⟨huSource, huCut⟩
      · subst u
        have hstrict : IsStrictPrefix c.cut (c.cut ++ [i]) := by
          refine ⟨⟨[i], rfl⟩, ?_⟩
          intro heq
          have hh := congrArg List.length heq
          simp at hh
        exact ⟨c.hcut,
          (SkewBranchGeometry.strictPrefixB_iff
            c.cut (c.cut ++ [i])).2 hstrict⟩
      · have huInterior : u ∈ SkewTree.interior c.source.tree :=
          SignatureInteriorPersistence.interior_of_strict_descendant
            c.source.tree u c.cut huSource
            (List.mem_filter.mp c.hcut).1 huCut
        have huStrict : IsStrictPrefix u (c.cut ++ [i]) :=
          (interior_prefix_cut_child_iff c i u huInterior).2 huCut.1
        exact ⟨huInterior,
          (SkewBranchGeometry.strictPrefixB_iff
            u (c.cut ++ [i])).2 huStrict⟩
  have hnot :
      c.cut ∉ (SkewTree.preds c.source.tree c.cut).toFinset := by
    intro h
    have hh := (ImmediateSupportHeight.mem_preds_iff
      c.source.tree c.cut c.cut).1 (List.mem_toFinset.mp h)
    exact hh.2.2 rfl
  calc
    ((SkewTree.interior c.source.tree).toFinset.filter
      (fun u => SkewTree.strictPrefixB u (c.cut ++ [i]) = true)).card =
        (insert c.cut
          (SkewTree.preds c.source.tree c.cut).toFinset).card :=
      congrArg Finset.card hset
    _ = (SkewTree.preds c.source.tree c.cut).toFinset.card + 1 := by
      simp [hnot]
    _ = (SkewTree.preds c.source.tree c.cut).length + 1 := by
      rw [List.toFinset_card_of_nodup hpredNodup]
    _ = SkewTree.heightAt c.source.tree c.cut + 1 := rfl

end DualTree.ForwardQCutChildRank
