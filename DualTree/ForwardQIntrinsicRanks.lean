import DualTree.ForwardQInteriorExact
import DualTree.ImmediateSupportHeight

/-!
# Exact intrinsic height as old-base predecessor cardinality in forward Q

The corrected Q support is the fixed original interior together
with terminal projected D₂ nodes. Every projected node is a leaf,
so the only strict predecessors of *any* Q node belong to the
fixed old base. Therefore Q intrinsic height is the number of
strict old-base prefixes, independent of ambient word length
and of the noncomputable order in which frontiers were enumerated.

This exact counting theorem is the numerical interface required
to prove skew clauses (ii) and (iii) for Q. It is stronger than
interior equality alone: intrinsic ranks of new terminal nodes
can now be calculated from their original interior prefix masks.

We use Finset cardinality explicitly; the old base is a List
whose duplicate-freeness is not required in this calculation.
-/

namespace DualTree.ForwardQIntrinsicRanks

open ForwardSourceQTree

/-- No marked D₂ projection can be a strict predecessor
of *any* vertex of the actual corrected Q support. -/
theorem Q_strict_predecessor_is_oldBase
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (u s : Node b)
    (hu : u ∈ nodes c x)
    (hs : s ∈ nodes c x)
    (hus : IsStrictPrefix u s) :
    u ∈ oldBase c := by
  classical
  change u ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hu
  rcases Finset.mem_union.mp hu with hbase | hnew
  · exact List.mem_toFinset.mp hbase
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hnew
    have heq : (markedProjection c x i).1 = u := hi
    have hcontr :=
      ForwardQMarkedTerminals.markedProjection_no_strict_descendant
        c x (ForwardQSourceTerminals.literal_oldBase_before_cut c)
        i s hs
    exact False.elim (hcontr (by simpa [heq] using hus))

/-- In the corrected Q support, strict predecessor membership
is exactly the old-base membership plus strict ambient prefix. -/
theorem Q_preds_iff_oldBase
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ nodes c x)
    (u : Node b) :
    u ∈ SkewTree.preds (nodes c x).toList s ↔
      u ∈ oldBase c ∧ IsStrictPrefix u s := by
  rw [ImmediateSupportHeight.mem_preds_iff]
  constructor
  · rintro ⟨huW, hus⟩
    exact ⟨Q_strict_predecessor_is_oldBase c x u s
      (Finset.mem_toList.mp huW) hs hus, hus⟩
  · rintro ⟨huBase, hus⟩
    exact ⟨Finset.mem_toList.mpr
      (oldBase_mem c x u huBase), hus⟩

/-- Every actual corrected Q node has intrinsic rank equal
to the number of original interior nodes properly below it
in the ambient prefix order. -/
theorem Q_height_eq_oldBase_prefix_card
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ nodes c x) :
    SkewTree.heightAt (nodes c x).toList s =
      ((oldBase c).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true)).card := by
  classical
  have hpredNodup :
      (SkewTree.preds (nodes c x).toList s).Nodup := by
    unfold SkewTree.preds
    exact (Finset.nodup_toList (nodes c x)).filter _
  have hset :
      (SkewTree.preds (nodes c x).toList s).toFinset =
      (oldBase c).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_filter,
      Q_preds_iff_oldBase c x s hs u,
      SkewBranchGeometry.strictPrefixB_iff]
    tauto
  calc
    SkewTree.heightAt (nodes c x).toList s =
      (SkewTree.preds (nodes c x).toList s).length := rfl
    _ = (SkewTree.preds (nodes c x).toList s).toFinset.card :=
      (List.toFinset_card_of_nodup hpredNodup).symm
    _ = ((oldBase c).toFinset.filter
      (fun u => SkewTree.strictPrefixB u s = true)).card :=
      congrArg Finset.card hset

/-- The more source-facing version uses the precise original
source interior rather than the signature's retained base list. -/
theorem Q_height_eq_original_interior_prefix_card
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ nodes c x) :
    SkewTree.heightAt (nodes c x).toList s =
      ((SkewTree.interior c.source.tree).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true)).card := by
  rw [Q_height_eq_oldBase_prefix_card c x s hs]
  have hset :
      (oldBase c).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true) =
      (SkewTree.interior c.source.tree).toFinset.filter
        (fun u => SkewTree.strictPrefixB u s = true) := by
    ext u
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hu, hprefix⟩
      exact ⟨(ForwardQFixedBase.oldBase_mem_iff_original_interior c u).1
        hu, hprefix⟩
    · rintro ⟨hu, hprefix⟩
      exact ⟨(ForwardQFixedBase.oldBase_mem_iff_original_interior c u).2
        hu, hprefix⟩
  exact congrArg Finset.card hset

end DualTree.ForwardQIntrinsicRanks
