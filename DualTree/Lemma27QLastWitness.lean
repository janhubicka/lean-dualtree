import DualTree.LastBranchWitness
import DualTree.Lemma27QInterior
import DualTree.Lemma27QRooted
import DualTree.Lemma27QBranchCount
import DualTree.Lemma27MarkedLeafGeometry

/-!
# The actual final branching witness in the reconstructed Q support

The retained original maximal interior cut is a valid witness for the
Boolean skew clause (iv). New projected Q markers lie outside the
inclusive auxiliary cut, and every retained old-base node is an
original interior. Thus every Q node before the cut is an interior
node and has all b immediate successor directions.

Conversely every Q node strictly after the cut is a leaf:
otherwise exact interior persistence would make it an original
interior, whose comparison with the maximal cut is impossible by
antisymmetry of the printed auxiliary order.

We then apply the generic full-last-witness criterion. This proves
clause (iv) only. The independent skew clauses (ii) and (iii),
involving intrinsic heights and ambient lengths, remain open.
-/

namespace DualTree.Lemma27QLastWitness

/-- Any reconstructed Q node at or before the auxiliary cut belongs
to the original interior (and therefore to the Q interior). -/
theorem sourceQ_before_cut_interior
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
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b)
    (hs : s ∈ (Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList)
    (hbefore : SkewTree.paperAuxB s cut = true) :
    s ∈ SkewTree.interior
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  classical
  have hsW : s ∈ Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x :=
    Finset.mem_toList.mp hs
  change s ∈ Lemma27SignatureTree.signatureNodes
    T hcomplete cut hcutT hlevel hm
    (Lemma27SignatureTree.oldSignatureBase O cut hout) x at hsW
  unfold Lemma27SignatureTree.signatureNodes at hsW
  rcases Finset.mem_union.mp hsW with hbase | hmarker
  · have hsOld : s ∈ SkewTree.interior O.tree :=
      (Lemma27QTreeCount.oldBase_mem_iff_original_interior
        O cut hcut hmax hout s).1 (List.mem_toFinset.mp hbase)
    exact (Lemma27QInterior.source_interior_iff_original
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s).2
      hsOld
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmarker
    have hnot :=
      Lemma27MarkedLeafGeometry.markedProjection_after_cut
        T hcomplete cut hcutT hlevel hm x i
    exact False.elim (hnot (by
      simpa [SkewTree.paperAuxB] using hbefore))

/-- All Q vertices strictly earlier than the maximal original
interior cut have full immediate successor directions. -/
theorem sourceQ_fullBeforeB
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
    SkewTree.fullBeforeB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      cut = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  unfold SkewTree.fullBeforeB
  apply List.all_eq_true.mpr
  intro s hs
  change (if SkewTree.paperAuxB s cut && !(s == cut)
    then (SkewTree.allFin b).all
      (fun i => SkewTree.uniqueBranchB W.toList s i)
    else true) = true
  split_ifs with hcase
  · have hbefore : SkewTree.paperAuxB s cut = true := by
      have hh := hcase
      simp only [Bool.and_eq_true] at hh
      exact hh.1
    have hsInterior :=
      sourceQ_before_cut_interior
        hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
        s hs hbefore
    apply List.all_eq_true.mpr
    intro i _
    exact Lemma27QRooted.sourceQ_full_immediate_at_nonleaf
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
      x s hsInterior i
  · rfl

/-- Every reconstructed Q node strictly later than the maximal
original interior cut is terminal in Q. The proof uses printed
auxiliary-order antisymmetry, not invariance under embeddings. -/
theorem sourceQ_emptyAfterB
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
    SkewTree.emptyAfterB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      cut = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  unfold SkewTree.emptyAfterB
  apply List.all_eq_true.mpr
  intro s hs
  change (if SkewTree.paperAuxB cut s && !(s == cut)
    then (SkewTree.immediateSuccs W.toList s).isEmpty
    else true) = true
  split_ifs with hcase
  · have hafter : SkewTree.paperAuxB cut s = true := by
      have hh := hcase
      simp only [Bool.and_eq_true] at hh
      exact hh.1
    have hsne : s ≠ cut := by
      intro heq
      subst s
      simp at hcase
    by_cases hempty : (SkewTree.immediateSuccs W.toList s).isEmpty = true
    · exact hempty
    · have hsInterior : s ∈ SkewTree.interior W.toList := by
        unfold SkewTree.interior
        apply List.mem_filter.mpr
        refine ⟨hs, ?_⟩
        cases hsucc : SkewTree.immediateSuccs W.toList s with
        | nil =>
            simp [hsucc] at hempty
        | cons t ts =>
            simp [hsucc]
      have hsOld : s ∈ SkewTree.interior O.tree :=
        (Lemma27QInterior.source_interior_iff_original
          hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s).1
          hsInterior
      have hbefore := hmax s hsOld
      have heq : cut = s :=
        PaperAuxAntisymm.paperAuxB_antisymm hafter hbefore
      exact False.elim (hsne heq.symm)
  · rfl

/-- The distinguished original maximal interior vertex is a
valid final branching witness for clause (iv) of the paper's
skew-tree definition, under positive branching. -/
theorem sourceQ_condIVB
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
    SkewTree.condIVB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hcutW : cut ∈ W.toList :=
    Lemma27QInterior.originalInterior_mem_Q
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
      cut hcut
  have hcutInterior : cut ∈ SkewTree.interior W.toList :=
    (Lemma27QInterior.source_interior_iff_original
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x cut).2
      hcut
  have hfullCut : ∀ i : Fin b, SkewTree.uniqueBranchB
      W.toList cut i = true := by
    intro i
    exact Lemma27QRooted.sourceQ_full_immediate_at_nonleaf
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm
      x cut hcutInterior i
  have hcount : (SkewTree.immediateSuccs W.toList cut).length = b :=
    Lemma27QBranchCount.immediateSuccs_length_eq_of_full_directions
      W.toList (Finset.nodup_toList W) cut hfullCut
  exact LastBranchWitness.condIVB_of_full_last_witness
    hb SkewTree.paperAuxB W.toList cut hcutW
    (sourceQ_fullBeforeB hb O cut hcut hmax hout T hcomplete hST
      hcutT hlevel hm x)
    (sourceQ_emptyAfterB hb O cut hcut hmax hout T hcomplete hST
      hcutT hlevel hm x)
    hcount hfullCut

end DualTree.Lemma27QLastWitness
