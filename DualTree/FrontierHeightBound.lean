import DualTree.SupportHeightRanks
import DualTree.RankCardinality
import DualTree.ConeLocalDecoder

/-!
# Intrinsic height of frontiers beyond an auxiliary cut

Let cut belong to a nonsingleton skew support T and let t be a
prefix-minimal support node outside the inclusive initial segment
at cut. Every proper support predecessor of t lies in that initial
segment. Skew level separation implies its intrinsic height is at
most that of cut. Since intrinsic heights along the branch are
distinct, there are at most height(cut)+1 predecessors.

This proves the missing uniform height bound used by the repaired
cone-local decoder in Lemma 27. It is independent of any particular
enumeration of the frontier nodes.
-/

namespace DualTree.FrontierHeightBound

/--
Minimal support points beyond a cut have intrinsic height at most one
greater than that of the cut.
-/
theorem frontier_height_le_cut_succ {b : Nat}
    (T : List (Node b)) (cut frontier : Node b)
    (hskew : SkewTree.skewB SkewTree.paperAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (hcut : cut ∈ T)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier) :
    SkewTree.heightAt T frontier ≤ SkewTree.heightAt T cut + 1 := by
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have hnodup : T.Nodup := by simpa using hparts.1
  have hpredNodup : (SkewTree.preds T frontier).Nodup := by
    unfold SkewTree.preds
    exact hnodup.filter _
  have hpred :
      ∀ r, r ∈ SkewTree.preds T frontier →
        r ∈ T ∧ IsStrictPrefix r frontier := by
    intro r hr
    change r ∈ T.filter
      (fun u => SkewTree.strictPrefixB u frontier) at hr
    rcases List.mem_filter.mp hr with ⟨hrT, hrB⟩
    exact ⟨hrT,
      (SkewBranchGeometry.strictPrefixB_iff r frontier).1 hrB⟩
  have hbound :
      ∀ r, r ∈ SkewTree.preds T frontier →
        SkewTree.heightAt T r ≤ SkewTree.heightAt T cut := by
    intro r hr
    rcases hpred r hr with ⟨hrT, hrPre⟩
    have hrEarly : PaperAux r cut :=
      hf.2.2 r hrT hrPre
    by_contra hn
    have hheight :
        SkewTree.heightAt T cut < SkewTree.heightAt T r := by
      omega
    have hlen : cut.length < r.length :=
      SkewLevelOrder.length_lt_of_height_lt T
        SkewTree.paperAuxB hskew hnonsingleton
        hcut hrT hheight
    rcases hrEarly with hlt | ⟨heq, _⟩ <;> omega
  have hinjective :
      ∀ r, r ∈ SkewTree.preds T frontier →
      ∀ s, s ∈ SkewTree.preds T frontier →
        SkewTree.heightAt T r = SkewTree.heightAt T s → r = s := by
    intro r hr s hs hheight
    rcases hpred r hr with ⟨hrT, hrPrefix⟩
    rcases hpred s hs with ⟨hsT, hsPrefix⟩
    exact SupportHeightRanks.heightAt_injective_on_common_path
      T hrT hsT hrPrefix.1 hsPrefix.1 hheight
  have hcount :=
    RankCardinality.nodup_length_le_of_rank_bound
      (SkewTree.preds T frontier)
      (SkewTree.heightAt T cut)
      (SkewTree.heightAt T)
      hpredNodup hbound hinjective
  exact hcount

/-- Source-facing specialization to an early cut in a complete skew support. -/
theorem frontier_height_le_complete {b k : Nat}
    (T : List (Node b)) (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier) :
    SkewTree.heightAt T frontier ≤ SkewTree.heightAt T cut + 1 := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  exact frontier_height_le_cut_succ T cut frontier hparts.1
    (LiteralFrontierCleanup.nonsingleton_of_early_level
      T hcomplete cut hcut hlevel) hcut hf

/-- The exact frontier-height hypothesis required by the local decoder. -/
theorem frontier_height_le_m_succ {b k m : Nat}
    (T : List (Node b)) (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier)
    (hcutHeight : SkewTree.heightAt T cut = m) :
    SkewTree.heightAt T frontier ≤ m + 1 := by
  have hh := frontier_height_le_complete T cut frontier
    hcomplete hcut hlevel hf
  omega

/--
The corrected m+1-letter decoder is available at any actual frontier
of an early cut, without a separate frontier-height assumption.
-/
noncomputable def decodeAtFrontier
    {b k m : Nat} {α : Type*}
    (T I : List (Node b)) (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier)
    (hcutHeight : SkewTree.heightAt T cut = m)
    (a : α) :
    Fin (m + 1) →
      Sum α (Fin (Lemma27Repair.visibleAncestors T I frontier).length) :=
  ConeLocalDecoder.decode T I frontier a
    (frontier_height_le_m_succ T cut frontier
      hcomplete hcut hlevel hf hcutHeight)

/-- Every visible ancestor index is realized by a decoded auxiliary letter. -/
theorem decodeAtFrontier_onto_visible
    {b k m : Nat} {α : Type*}
    (T I : List (Node b)) (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier)
    (hcutHeight : SkewTree.heightAt T cut = m)
    (a : α)
    (hpos : 0 < (Lemma27Repair.visibleAncestors T I frontier).length)
    (j : Fin (Lemma27Repair.visibleAncestors T I frontier).length) :
    ∃ i : Fin (m + 1),
      decodeAtFrontier T I cut frontier hcomplete hcut
        hlevel hf hcutHeight a i = Sum.inr j := by
  exact ConeLocalDecoder.decode_onto_visible T I frontier a
    (frontier_height_le_m_succ T cut frontier
      hcomplete hcut hlevel hf hcutHeight) hpos j

end DualTree.FrontierHeightBound
