import DualTree.ForwardQIntrinsicRanks

/-!
# The retained original interior keeps its intrinsic support heights in Q

In the corrected Lemma 27 reconstruction every old source interior node
belongs to the Q support. Its strict predecessors in the source cannot
be source leaves: they have an actual strict descendant and are therefore
themselves interior.

The preceding Q height theorem counts exactly the old-interior prefixes.
For such a retained old node, those are precisely its original source
support predecessors. Thus the intrinsic height of each old interior
node is unchanged by reconstruction, despite the arbitrary safe D₂
cone-tail lengths chosen for the new terminal nodes.

This is an exact source-facing rank preservation statement, needed for
mixed old/marked comparisons in skew clauses (ii) and (iii).
-/

namespace DualTree.ForwardQRetainedRanks

open ForwardSourceQTree

/-- Every strict support predecessor of a genuine original
interior node belongs to the original interior. -/
theorem source_predecessor_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s u : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (hu : u ∈ c.source.tree)
    (hus : IsStrictPrefix u s) :
    u ∈ SkewTree.interior c.source.tree := by
  have hsTree : s ∈ c.source.tree :=
    (List.mem_filter.mp hs).1
  exact SignatureInteriorPersistence.interior_of_strict_descendant
    c.source.tree u s hu hsTree hus

/-- Old retained Q interior vertices have exactly their
original source intrinsic heights, independently of every
selected D₂ marked point and local cone-tail length. -/
theorem original_interior_Q_height_eq_source
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree) :
    SkewTree.heightAt (nodes c x).toList s =
      SkewTree.heightAt c.source.tree s := by
  classical
  have hsW : s ∈ nodes c x :=
    ForwardQFixedBase.originalInterior_mem_Q c x s hs
  rw [ForwardQIntrinsicRanks.Q_height_eq_original_interior_prefix_card
    c x s hsW]
  have hsourceNodup : c.source.tree.Nodup := by
    have hsemi := c.source.semi_complete
    simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
    have hskew := hsemi.1
    simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
    simpa using hskew.1
  have hpredNodup : (SkewTree.preds c.source.tree s).Nodup := by
    unfold SkewTree.preds
    exact hsourceNodup.filter _
  have hset : (SkewTree.preds c.source.tree s).toFinset =
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_filter,
      ImmediateSupportHeight.mem_preds_iff]
    constructor
    · rintro ⟨hu, hstrict⟩
      exact ⟨source_predecessor_interior c s u hs hu hstrict,
        (SkewBranchGeometry.strictPrefixB_iff u s).2 hstrict⟩
    · rintro ⟨huInterior, hstrict⟩
      exact ⟨(List.mem_filter.mp huInterior).1,
        (SkewBranchGeometry.strictPrefixB_iff u s).1 hstrict⟩
  calc
    ((SkewTree.interior c.source.tree).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true)).card =
      (SkewTree.preds c.source.tree s).toFinset.card :=
      congrArg Finset.card hset.symm
    _ = (SkewTree.preds c.source.tree s).length :=
      List.toFinset_card_of_nodup hpredNodup
    _ = SkewTree.heightAt c.source.tree s := rfl

end DualTree.ForwardQRetainedRanks
