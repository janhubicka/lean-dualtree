import DualTree.InclusiveFrontier

/-!
# The signature markers really are boundaries of the inclusive cut

The candidate marker list for the R of Lemma 27 has two parts:
boundary points of exceptional leaves and immediate ambient successors
of the distinguished cut. Both types are *first* points beyond the
inclusive auxiliary-order initial segment. This observation allows
the exact frontier construction of the paper to be used without
silently replacing an inclusive cut by the strict signature cut.
-/

namespace DualTree.InclusiveSignatureMarkers

/-- Every immediate ambient child of the cut is an inclusive-cut boundary. -/
theorem child_paperCutBoundary {b : Nat}
    (cut : Node b) (i : Fin b) :
    InclusiveFrontier.PaperCutBoundary cut (cut ++ [i]) := by
  constructor
  · intro h
    have hlong : cut.length < (cut ++ [i]).length := by simp
    rcases h with hlt | ⟨heq, _⟩
    · omega
    · omega
  · intro r hr
    have hlen : r.length ≤ cut.length := by
      have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hr
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    have hrcut : IsPrefix r cut :=
      CutFrontier.prefix_of_prefix_length_le hr.1
        (show IsPrefix cut (cut ++ [i]) from ⟨[i], rfl⟩) hlen
    have hcut : PaperAux cut cut := by
      rcases finLexLE_total cut cut with hlex | hlex
      · exact Or.inr ⟨rfl, hlex⟩
      · exact Or.inr ⟨rfl, hlex⟩
    exact CutPreservation.paperAux_of_prefix hrcut hcut

/--
An exceptional leaf does not lie below the cut, so the first point
outside the strict signature cut is also the first point outside
the inclusive support cut.
-/
theorem boundaryMarker_paperCutBoundary
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SignatureMarker.boundaryMarkers O cut hout) :
    InclusiveFrontier.PaperCutBoundary cut s := by
  classical
  unfold SignatureMarker.boundaryMarkers at hs
  rcases List.mem_map.mp hs with ⟨t, _ht, hts⟩
  have hb := SignatureBoundary.firstBoundary_spec
    cut t.1 (hout t.1 t.2)
  have hnotBelow : ¬ IsPrefix cut t.1 :=
    (StarredSignature.exceptionalLeaves_spec O cut t.1 t.2).2.2
  have hne :
      SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2) ≠ cut := by
    intro heq
    exact hnotBelow (by simpa [heq] using hb.1)
  have houtInclusive :
      ¬ PaperAux
        (SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2)) cut := by
    intro hearly
    exact hb.2.1 ⟨hearly, hne⟩
  have hboundary : InclusiveFrontier.PaperCutBoundary cut
      (SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2)) :=
    ⟨houtInclusive, fun r hr => (hb.2.2 r hr).1⟩
  simpa only [hts] using hboundary

/-- Every candidate cone marker is a boundary of the inclusive cut. -/
theorem coneMarker_paperCutBoundary
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    InclusiveFrontier.PaperCutBoundary cut s := by
  unfold SignatureMarker.coneMarkers at hs
  rcases List.mem_append.mp hs with hboundary | hchild
  · exact boundaryMarker_paperCutBoundary O cut hout hboundary
  · rcases List.mem_map.mp hchild with ⟨i, _hi, heq⟩
    rw [← heq]
    exact child_paperCutBoundary cut i

/--
For exceptional signature-leaf boundaries, the unique support frontier
exists without a level-separation hypothesis: the original exceptional
leaf already witnesses support extension under S ⊆ T.
-/
theorem boundaryMarker_unique_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    {s : Node b}
    (hs : s ∈ SignatureMarker.boundaryMarkers O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f := by
  exact InclusiveFrontier.unique_frontier_complete_paper
    T hcomplete cut s
    (boundaryMarker_paperCutBoundary O cut hout hs)
    (SignatureMarker.boundaryMarker_has_support_descendant
      O cut hout T hST hs)

/--
For all candidate R markers, including the b immediate children, the
source's exact inclusive-cut frontier exists uniquely once the cut
precedes a later full-branching witness in intrinsic height.
-/
theorem coneMarker_unique_frontier_of_height_lt
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (witness : Node b)
    (hwitness : witness ∈ T)
    (hheight : SkewTree.heightAt T cut <
      SkewTree.heightAt T witness)
    (hfull : SkewTree.fullBeforeB SkewTree.paperAuxB T witness = true)
    {s : Node b}
    (hs : s ∈ SignatureMarker.coneMarkers O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f := by
  have hskew : SkewTree.skewB SkewTree.paperAuxB T = true := by
    have hparts := hcomplete
    simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
    exact hparts.1
  have hdesc : ∃ t, t ∈ T ∧ IsPrefix s t :=
    SkewLevelOrder.coneMarker_has_descendant_of_height_lt
      O cut hout T hST hskew hnonsingleton hcut
      witness hwitness hheight hfull hs
  exact InclusiveFrontier.unique_frontier_complete_paper
    T hcomplete cut s
    (coneMarker_paperCutBoundary O cut hout hs) hdesc

end DualTree.InclusiveSignatureMarkers
