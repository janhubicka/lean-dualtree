import DualTree.ForwardQFinalProjectedFullDirections
import DualTree.ForwardQFinalSupportCut
import DualTree.ForwardFrontierRanks

/-!
# The retained/new boundary: immediate ambient T-edges and the cut

For the exact M-filtered final Lemma 27 support, any immediate
support edge s->t of the large complete ambient T, with s
RETAINED at/before the distinguished inclusive cut, has
two mutually exclusive cases.

* If t remains at/before the cut, the edge is STILL immediate
  in the full joined target-filtered support T'_M. No retained
  vertex can intervene because the edge is T-immediate, and
  no selected projected vertex can precede a retained vertex.

* If t is outside the cut, then t ITSELF is a minimal
  outside-cut T frontier: all its proper T-predecessors
  lie at/before the inclusive cut, since s->t is immediate.
  Its ambient T-rank belongs to the known two-element band
  {m,m+1}.

This is the exact geometric case distinction needed to prove
full directional branching at RETAINED vertices. In the
second case the successor must be replaced by the selected
root P_i(z_i) of the corresponding post-Ramsey component.
Selecting and proving that replacement immediate is the
next separate obligation.

Neither the full M-complete skew conclusion nor final
ambient variable word f' is claimed here.
-/

namespace DualTree.ForwardQFinalRetainedEdges

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut
open ForwardQFinalHeightBudget

/-- A retained ambient T-support edge stays immediate
in the FULL target-filtered T'_M whenever its endpoint
also lies in the retained initial portion. -/
theorem retained_T_immediate_is_final_immediate
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (M : Nat)
    (s t : Node b)
    (hs : s ∈ retained c)
    (ht : t ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true) :
    SkewTree.immediateSuccB
      (finalBudgetSupport c f M).toList s t = true := by
  classical
  let S := (finalBudgetSupport c f M).toList
  have htFinal : t ∈ S := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_union.mpr (Or.inl ht)
  obtain ⟨_,hst,hno⟩ :=
    (SkewBranchGeometry.immediateSuccB_iff c.T s t).1 hstep
  apply (SkewBranchGeometry.immediateSuccB_iff S s t).2
  refine ⟨htFinal,hst,?_⟩
  intro u hu hbetween
  have huFinal : u ∈ finalBudgetSupport c f M :=
    Finset.mem_toList.mp hu
  rcases Finset.mem_union.mp huFinal with hret | hnew
  · exact hno u (retained_subset_T c u hret) hbetween
  · obtain ⟨v,_,heq⟩ := Finset.mem_image.mp hnew
    have hproj : IsPrefix (projected c v).1 t := by
      rw [heq]
      exact hbetween.2.1
    exact (projected_not_prefix_retained c v t ht) hproj

/-- An immediate edge in T from a retained vertex
to a node outside the inclusive cut terminates at
a genuine MINIMAL outside-cut T frontier. -/
theorem outside_immediate_T_edge_is_frontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true)
    (hout : ¬ ForwardAux t c.cut) :
    CutFrontier.Frontier c.T
      (fun u => ForwardAux u c.cut) t := by
  obtain ⟨htT,hst,hno⟩ :=
    (SkewBranchGeometry.immediateSuccB_iff c.T s t).1 hstep
  have hsCut : ForwardAux s c.cut :=
    (Finset.mem_filter.mp hs).2
  refine ⟨htT,hout,?_⟩
  intro r hr hrt
  by_cases hlen : r.length ≤ s.length
  · have hrs : IsPrefix r s :=
      CutFrontier.prefix_of_prefix_length_le
        hrt.1 hst.1 hlen
    exact ForwardInclusiveFrontier.forwardAux_of_prefix hrs hsCut
  · have hsr : IsPrefix s r :=
      CutFrontier.prefix_of_prefix_length_le
        hst.1 hrt.1 (by omega)
    by_cases heq : s = r
    · subst r
      exact hsCut
    · exact False.elim
        (hno r hr ⟨⟨hsr,heq⟩,hrt⟩)

/-- A crossing immediate edge necessarily lands at
one of the two possible corrected frontier T-ranks:
the original cut rank m or one level higher. -/
theorem outside_immediate_T_edge_rank_band
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ retained c)
    (hstep : SkewTree.immediateSuccB c.T s t = true)
    (hout : ¬ ForwardAux t c.cut) :
    SkewTree.heightAt c.T t = m ∨
      SkewTree.heightAt c.T t = m + 1 := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hf :=
    outside_immediate_T_edge_is_frontier
      c s t hs hstep hout
  have hband :=
    ForwardFrontierRanks.frontier_rank_band
      c.T hc.1 c.hnon c.cut t c.hcutT hf
  simpa only [c.hm] using hband

end DualTree.ForwardQFinalRetainedEdges
