import DualTree.ForwardQMeetClosed
import DualTree.ForwardQInteriorExact
import DualTree.Lemma27QImmediate

/-!
# Full directional occupancy of each old interior vertex in the corrected Q

The original source S is semi-complete skew, hence has one immediate
support successor in each ambient direction from every interior vertex.
The corrected Q is not obtained by including all S leaves; it replaces
literal first-exit boundaries of its signature by actual projected
terminal leaves in the appropriate frontier cones.

For each original interior node u and direction i, choose its unique
source immediate successor t in that direction.
* If u is the final cut, the literal marker u++[i] already lies in R
  and has a projected Q descendant.
* If u lies strictly before the final cut and t is still interior,
  it is retained in Q.
* If t is terminal, t cannot lie in the cone of the final cut
  (or the cut would intervene between u and an immediate successor).
  Hence t is an exceptional leaf. The first strict-cut boundary r
  on its ambient path belongs to R. Because u is before the cut,
  this boundary cannot appear at or before u; in particular r
  remains inside the chosen i-direction cone of u.
  The actual projected marker then supplies the Q descendant.

Thus every ambient direction is occupied at every genuine Q interior
vertex. The separate meet-closure proof of ForwardQMeetClosed shows
such a direction has at most one immediate support successor. Together
these give the exact full branching predicate. No numerical skew
order axiom is inferred by this lemma.
-/

namespace DualTree.ForwardQAllDirections

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- The first boundary of a terminal source path cannot appear
before an earlier original interior vertex in its chosen ambient
successor cone. The strict forward cut is prefix-downward closed. -/
theorem first_boundary_preserves_earlier_direction
    {b : Nat} (cut s t : Node b) (i : Fin b)
    (hsEarly : BeforeCut cut s)
    (hdir : IsPrefix (s ++ [i]) t)
    (hout : ¬ BeforeCut cut t) :
    IsPrefix (s ++ [i]) (firstBoundary cut t hout) := by
  let r := firstBoundary cut t hout
  have hr : Boundary cut t r := firstBoundary_spec cut t hout
  by_cases hlen : (s ++ [i]).length ≤ r.length
  · exact CutFrontier.prefix_of_prefix_length_le hdir hr.1 hlen
  · have hshort : r.length ≤ s.length := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hst : IsPrefix s t :=
      isPrefix_trans ⟨[i], rfl⟩ hdir
    have hrs : IsPrefix r s :=
      CutFrontier.prefix_of_prefix_length_le hr.1 hst hshort
    exact False.elim
      (hr.2.1 (ForwardSignatureInteriorPersistence.beforeCut_of_prefix
        hrs hsEarly))

/-- Every non-leaf of the original source has its full set
of b uniquely determined ambient source successors under the
globally corrected forward order. -/
theorem source_full_directions
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    SkewTree.uniqueBranchB c.source.tree s i = true := by
  have hsS : s ∈ c.source.tree := (List.mem_filter.mp hs).1
  have hnonleaf : (SkewTree.immediateSuccs c.source.tree s).length ≠ 0 := by
    have htest := (List.mem_filter.mp hs).2
    cases hlist : SkewTree.immediateSuccs c.source.tree s with
    | nil => simp [hlist] at htest
    | cons u us => simp [hlist]
  have htotal :
      ∀ s t : Node b, s ≠ t →
        SkewTree.forwardAuxB s t = true ∨
        SkewTree.forwardAuxB t s = true := by
    intro u v _
    rcases CanonicalForwardAuxIso.forwardAux_total u v with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  exact SemiCompleteSkewMeet.fullDirections_of_semiComplete_nonleaf_total
    SkewTree.forwardAuxB c.source.tree c.source.semi_complete
    (ForwardQRooted.source_nonsingleton c) htotal
    s hsS hnonleaf i

/-- Every direction from an original interior vertex is occupied
by an actual Q support node, for the completely source-facing,
sorted-frontier, forward-canonical reconstruction. -/
theorem Q_all_directions
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    ∃ t : Node b, t ∈ nodes c x ∧ IsPrefix (s ++ [i]) t := by
  by_cases hscut : s = c.cut
  · subst s
    have hr : c.cut ++ [i] ∈
        ForwardLiteralFrontierCoordinates.R c.source c.cut c.hout :=
      ForwardStarredSignature.cut_child_mem_literalR
        c.source c.cut c.hout i
    exact ForwardQMarkerCoverage.literalMarker_has_Q_descendant
      c x (c.cut ++ [i]) hr
  · have hsEarly : BeforeCut c.cut s := by
      have haux : ForwardAux s c.cut := by
        simpa [SkewTree.forwardAuxB] using c.hmax s hs
      exact ⟨haux, hscut⟩
    have hbranch := source_full_directions c s hs i
    let t := CanonicalSupportWalk.next c.source.tree s i
    have ht : t ∈ c.source.tree :=
      CanonicalSupportWalk.next_mem c.source.tree s i hbranch
    have hstep : SkewTree.immediateSuccB c.source.tree s t = true :=
      (CanonicalSupportWalk.next_unique
        c.source.tree s i hbranch).1
    have hdir : IsPrefix (s ++ [i]) t :=
      (CanonicalSupportWalk.next_unique
        c.source.tree s i hbranch).2
    by_cases htInterior : t ∈ SkewTree.interior c.source.tree
    · exact ⟨t, ForwardQFixedBase.originalInterior_mem_Q
        c x t htInterior, hdir⟩
    · have hnotBelow : ¬ IsPrefix c.cut t := by
        intro hcutT
        have hst : IsStrictPrefix s t :=
          ((SkewBranchGeometry.immediateSuccB_iff
            c.source.tree s t).1 hstep).2.1
        have hlen : s.length ≤ c.cut.length := by
          rcases hsEarly.1 with hlt | ⟨heq, _⟩ <;> omega
        have hsCut : IsPrefix s c.cut :=
          CutFrontier.prefix_of_prefix_length_le
            hst.1 hcutT hlen
        have hcutMem : c.cut ∈ c.source.tree :=
          (List.mem_filter.mp c.hcut).1
        have hcutNeT : c.cut ≠ t := by
          intro heq
          exact htInterior (by simpa [← heq] using c.hcut)
        exact
          ((SkewBranchGeometry.immediateSuccB_iff
            c.source.tree s t).1 hstep).2.2
            c.cut hcutMem
            ⟨⟨hsCut, hscut⟩, ⟨hcutT, hcutNeT⟩⟩
      have htEx : t ∈ StarredSignature.exceptionalLeaves c.source c.cut := by
        classical
        simp [StarredSignature.exceptionalLeaves,
          ht, htInterior, hnotBelow]
      let r := firstBoundary c.cut t (c.hout t htEx)
      have hr : r ∈
          ForwardLiteralFrontierCoordinates.R c.source c.cut c.hout := by
        exact ForwardQInteriorExact.exceptional_boundary_mem_literalR
          c.source c.cut c.hmax c.hout ⟨t, htEx⟩
      have hdirR : IsPrefix (s ++ [i]) r :=
        first_boundary_preserves_earlier_direction
          c.cut s t i hsEarly hdir (c.hout t htEx)
      obtain ⟨q, hq, hrq⟩ :=
        ForwardQMarkerCoverage.literalMarker_has_Q_descendant
          c x r hr
      exact ⟨q, hq, isPrefix_trans hdirR hrq⟩

/-- In the actual forward Q support, each direction from every
original interior vertex has exactly one immediate successor.
Existence comes from the source signature, and uniqueness from
the verified ambient meet closure of the reconstructed Q. -/
theorem Q_full_immediate_directions
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : Fin b) :
    SkewTree.uniqueBranchB (nodes c x).toList s i = true := by
  obtain ⟨t, ht, hdir⟩ :=
    Q_all_directions c x s hs i
  have hsW : s ∈ (nodes c x).toList :=
    Finset.mem_toList.mpr
      (ForwardQFixedBase.originalInterior_mem_Q c x s hs)
  exact Lemma27QImmediate.uniqueBranch_of_directional_descendant
    (nodes c x).toList
    (Finset.nodup_toList (nodes c x))
    (ForwardQMeetClosed.Q_atMostOneDirection c x)
    s hsW i t (Finset.mem_toList.mpr ht) hdir

end DualTree.ForwardQAllDirections
