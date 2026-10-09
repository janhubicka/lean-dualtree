import DualTree.Lemma27QLastWitness
import DualTree.Lemma27QBranchClause

/-!
# Isolating the two remaining skew order clauses of the Q support

A nonsingleton reconstructed Q support is already duplicate-free,
rooted, and satisfies the last-branching-witness clause (iv).
The entire skew predicate is therefore equivalent to clauses
(ii) and (iii), and the semi-complete predicate is equivalent to
exactly these same two order tests once b > 0.

This states the remaining mathematical obligation precisely.
It does not assume length/rank preservation under the Q leaf
replacement. That preservation needs a separate proof or a
correction of the printed construction.
-/

namespace DualTree.Lemma27QOrderReduction

/-- For any nonsingleton duplicate-free rooted support
satisfying skew clause (iv), skewness is equivalent to the
two independent height/ambient-length order clauses. -/
theorem skewB_iff_order_conditions
    {b : Nat} (aux : Node b → Node b → Bool)
    (S : List (Node b))
    (hnodup : S.Nodup)
    (hnonsingleton : S.length ≠ 1)
    (hroot : SkewTree.rootedB S = true)
    (hIV : SkewTree.condIVB aux S = true) :
    SkewTree.skewB aux S = true ↔
      SkewTree.condIIB S = true ∧ SkewTree.condIIIB S = true := by
  have hn : decide S.Nodup = true := by simp [hnodup]
  have hl : (S.length == 1) = false := by simp [hnonsingleton]
  simp [SkewTree.skewB, hn, hl, hroot, hIV, Bool.and_eq_true]

/-- The actual reconstructed Q support is nonsingleton:
the original maximal interior cut is retained and has an
immediate successor in each of the positive b directions. -/
theorem sourceQ_nonsingleton
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    (Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList.length
        ≠ 1 := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hcutW : cut ∈ W.toList :=
    Lemma27QInterior.originalInterior_mem_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x cut hcut
  have hcutInt : cut ∈ SkewTree.interior W.toList :=
    (Lemma27QInterior.source_interior_iff_original
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x cut).2
      hcut
  let i : Fin b := ⟨0, hb⟩
  have hfull : SkewTree.uniqueBranchB W.toList cut i = true :=
    Lemma27QRooted.sourceQ_full_immediate_at_nonleaf
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
      cut hcutInt i
  obtain ⟨t, ht, hdir⟩ :=
    DirectionalSupport.descendant_of_uniqueBranch W.toList cut i hfull
  have hne : cut ≠ t := by
    intro heq
    subst t
    have hlen := prefix_length_le hdir
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  exact SupportReachability.nonsingleton_of_distinct_members
    W.toList hcutW ht hne

/-- In the literal Lemma 27 Q reconstruction, the only
remaining unverified skew axioms are the executable clauses
(ii) and (iii) comparing ambient lengths at intrinsic levels. -/
theorem sourceQ_skew_iff_order_conditions
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    SkewTree.skewB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true ↔
    SkewTree.condIIB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true ∧
    SkewTree.condIIIB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  exact skewB_iff_order_conditions SkewTree.paperAuxB W.toList
    (Finset.nodup_toList W)
    (sourceQ_nonsingleton hb O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x)
    (Lemma27QRooted.sourceQ_rooted O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x)
    (Lemma27QLastWitness.sourceQ_condIVB hb O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x)

/-- Under positive branching, even the entire semi-complete
predicate for S_w is equivalent to the two still-open
height/length order conditions, with no branch-count gap. -/
theorem sourceQ_semiComplete_iff_order_conditions
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    SkewTree.semiCompleteB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true ↔
    SkewTree.condIIB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true ∧
    SkewTree.condIIIB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true := by
  exact (Lemma27QBranchClause.sourceQ_semiComplete_iff_skew
    hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).trans
    (sourceQ_skew_iff_order_conditions hb O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x)

end DualTree.Lemma27QOrderReduction
