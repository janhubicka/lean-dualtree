import DualTree.LiteralFrontierIndex
import Mathlib

/-!
# Counting the D₂ frontier coordinates of Lemma 27

Let F be the list of minimal support points beyond the inclusive cut.
The printed proof chooses a subset D₂ of those coordinates, one for
each member of the literal signature marker set R.

The previously validated injection R → F now gives the required finite
cardinality inequality |R| ≤ |F|.  This result does not require a
particular enumeration of F and does not address the separate
upper bound |F| ≤ b^(m'+1).
-/

namespace DualTree.LiteralFrontierCount

/-- A duplicate-free list of the support frontiers beyond an inclusive cut. -/
noncomputable def frontiers {b : Nat}
    (T : List (Node b)) (cut : Node b) : List (Node b) := by
  classical
  exact (T.filter (fun t =>
    decide (CutFrontier.Frontier T (fun u => PaperAux u cut) t))).dedup

/-- The chosen list contains exactly the inclusive-cut support frontiers. -/
theorem mem_frontiers_iff {b : Nat}
    (T : List (Node b)) (cut f : Node b) :
    f ∈ frontiers T cut ↔
      CutFrontier.Frontier T (fun u => PaperAux u cut) f := by
  classical
  simp only [frontiers, List.mem_dedup, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

/-- The frontier list has no duplicate entries. -/
theorem frontiers_nodup {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    (frontiers T cut).Nodup := by
  classical
  unfold frontiers
  exact List.nodup_dedup _

/-- The printed signature set R is also represented without duplicates. -/
theorem literalR_nodup
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    (LiteralSignatureR.literalR O cut hout).Nodup := by
  classical
  unfold LiteralSignatureR.literalR
  exact List.nodup_dedup _

/--
The number of literal signature markers is bounded by the number of
available frontier coordinates, exactly as required for d₂ ≤ d.
-/
theorem literalR_length_le_frontiers
    {b n l k : Nat} {α : Type*}
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
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    (LiteralSignatureR.literalR O cut hout).length ≤
      (frontiers T cut).length := by
  classical
  let R := LiteralSignatureR.literalR O cut hout
  let F := frontiers T cut
  let φ : Node b → Node b := fun s =>
    if h : s ∈ R then
      LiteralFrontierIndex.frontierFor O cut hcut hmax
        hout T hcomplete hST hcutT hlevel ⟨s, h⟩
    else s
  let A : Finset (Node b) := R.toFinset
  let B : Finset (Node b) := F.toFinset
  have hmaps : Set.MapsTo φ (↑A) (↑B) := by
    intro s hs
    have hsR : s ∈ R := by simpa [A] using hs
    have hfront :
        CutFrontier.Frontier T (fun u => PaperAux u cut)
          (LiteralFrontierIndex.frontierFor O cut hcut hmax
            hout T hcomplete hST hcutT hlevel ⟨s, hsR⟩) :=
      (LiteralFrontierIndex.frontierFor_spec O cut hcut hmax
        hout T hcomplete hST hcutT hlevel ⟨s, hsR⟩).1
    have hmem : φ s ∈ F := by
      simpa [φ, hsR, F] using
        (mem_frontiers_iff T cut _).2 hfront
    simpa [B] using hmem
  have hinj : Set.InjOn φ (↑A) := by
    intro s hs t ht hst
    have hsR : s ∈ R := by simpa [A] using hs
    have htR : t ∈ R := by simpa [A] using ht
    have heq :
        LiteralFrontierIndex.frontierFor O cut hcut hmax
          hout T hcomplete hST hcutT hlevel ⟨s, hsR⟩ =
        LiteralFrontierIndex.frontierFor O cut hcut hmax
          hout T hcomplete hST hcutT hlevel ⟨t, htR⟩ := by
      simpa [φ, hsR, htR] using hst
    have hinj' :=
      LiteralFrontierIndex.frontierFor_injective O cut
        hcut hmax hout T hcomplete hST hcutT hlevel heq
    exact congrArg Subtype.val hinj'
  have hcard : A.card ≤ B.card :=
    Finset.card_le_card_of_injOn φ hmaps hinj
  simpa [A, B, R, F,
    List.toFinset_card_of_nodup
      (literalR_nodup O cut hout),
    List.toFinset_card_of_nodup
      (frontiers_nodup T cut)] using hcard

/-- The numerical partition d = d₀ + d₂ is therefore well formed. -/
theorem frontier_partition_count
    {b n l k : Nat} {α : Type*}
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
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    ((frontiers T cut).length -
       (LiteralSignatureR.literalR O cut hout).length) +
       (LiteralSignatureR.literalR O cut hout).length =
       (frontiers T cut).length := by
  exact Nat.sub_add_cancel
    (literalR_length_le_frontiers O cut hcut hmax hout
      T hcomplete hST hcutT hlevel)

end DualTree.LiteralFrontierCount
