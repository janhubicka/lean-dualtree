import DualTree.Lemma27QBranchCount

/-!
# Exact residual for the semi-completeness of the Lemma 27 Q support

Once every non-leaf has exactly b immediate successors, the
additional branching conjunct of semiCompleteB is automatic.
Thus the reconstructed Q support is semi-complete if and only
if it satisfies the remaining skewB predicate. We record this
as a precise equivalence: it does not silently assume the
printed auxiliary-order or rank clauses.

The branch count is available under b > 0. The zero-branching
degenerate case is not asserted here.
-/

namespace DualTree.Lemma27QBranchClause

/-- The exact numerical semi-completeness branch clause, using
the source's executable Boolean test on the actual reconstructed
finite Q support, holds independently of skewness. -/
theorem sourceQ_boolean_branch_clause
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
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList.all
      (fun s =>
        decide ((SkewTree.immediateSuccs
          (Lemma27SignatureTree.sourceSignatureNodes
            O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
          s).length = 0 ∨
        (SkewTree.immediateSuccs
          (Lemma27SignatureTree.sourceSignatureNodes
            O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
          s).length = b)) = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  change W.toList.all
    (fun s => decide ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
      (SkewTree.immediateSuccs W.toList s).length = b)) = true
  apply List.all_eq_true.mpr
  intro s hs
  have hCount :=
    Lemma27QBranchCount.sourceQ_zero_or_b_immediate_successors
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s hs
  simpa using hCount

/-- For the actual reconstructed Q support, semi-completeness
is equivalent to the still open skewness assertion. In
particular, all remaining work for semiCompleteB lies in
skewB, not in the numerical successor counts. -/
theorem sourceQ_semiComplete_iff_skew
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
    SkewTree.skewB SkewTree.paperAuxB
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList
      = true := by
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hbranch : W.toList.all
      (fun s => decide ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
        (SkewTree.immediateSuccs W.toList s).length = b)) = true :=
    sourceQ_boolean_branch_clause
      hb O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  constructor
  · intro h
    have hh : SkewTree.skewB SkewTree.paperAuxB W.toList = true ∧
        W.toList.all
          (fun s => decide ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
            (SkewTree.immediateSuccs W.toList s).length = b)) = true := by
      simpa only [SkewTree.semiCompleteB, Bool.and_eq_true] using h
    exact hh.1
  · intro hskew
    change (SkewTree.skewB SkewTree.paperAuxB W.toList &&
      W.toList.all
        (fun s => decide ((SkewTree.immediateSuccs W.toList s).length = 0 ∨
          (SkewTree.immediateSuccs W.toList s).length = b))) = true
    exact Bool.and_eq_true.mpr ⟨hskew, hbranch⟩

end DualTree.Lemma27QBranchClause
