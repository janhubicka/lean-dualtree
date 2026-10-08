import DualTree.MarkerAntichain

/-!
# The literal R of Lemma 27

The paper forms R from the non-interior points of the signature tree
other than t0, together with the immediate ambient children of t0.
This differs definitionally from the auxiliary coneMarkers list.

This file formalizes the literal expression and proves that R is
contained in coneMarkers under the one remaining signature-geometry
property: every original interior node except the distinguished cut
remains interior to the signature tree. Equality of the two marker
sets is neither asserted nor needed for frontier coverage.
-/

namespace DualTree.LiteralSignatureR

/-- Points of the signature tree outside its interior, excluding the cut. -/
noncomputable def signatureTerminalMarkers
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) := by
  classical
  let S' := StarredSignature.signatureTree O cut hout
  exact S'.filter (fun s =>
    decide (s ∉ SkewTree.interior S' ∧ s ≠ cut))

/-- The paper's set R as a duplicate-free list of ambient nodes. -/
noncomputable def literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) := by
  classical
  exact (signatureTerminalMarkers O cut hout ++
    (SkewTree.allFin b).map (fun i => cut ++ [i])).eraseDups

/-- Every signature-tree node is an original interior point or a leaf boundary. -/
theorem mem_signatureTree_iff
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : Node b) :
    s ∈ StarredSignature.signatureTree O cut hout ↔
      s ∈ SkewTree.interior O.tree ∨
      s ∈ SignatureMarker.boundaryMarkers O cut hout := by
  classical
  simp [StarredSignature.signatureTree,
    SignatureMarker.boundaryMarkers, List.mem_append]

/--
Source-facing signature persistence hypothesis. This is the remaining
geometry needed to identify all members of the literal R with one of
the two candidate marker types.
-/
def InteriorPersists
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) : Prop :=
  ∀ s, s ∈ SkewTree.interior O.tree → s ≠ cut →
    s ∈ SkewTree.interior (StarredSignature.signatureTree O cut hout)

/-- Every literal R node is among the candidate cone markers if interiors persist. -/
theorem literalR_subset_coneMarkers
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (hpersist : InteriorPersists O cut hout)
    {s : Node b}
    (hs : s ∈ literalR O cut hout) :
    s ∈ SignatureMarker.coneMarkers O cut hout := by
  classical
  have hr :
      s ∈ signatureTerminalMarkers O cut hout ++
        (SkewTree.allFin b).map (fun i => cut ++ [i]) := by
    simpa [literalR] using hs
  change s ∈ SignatureMarker.boundaryMarkers O cut hout ++
    (SkewTree.allFin b).map (fun i => cut ++ [i])
  rcases List.mem_append.mp hr with hterminal | hchild
  · unfold signatureTerminalMarkers at hterminal
    rcases List.mem_filter.mp hterminal with ⟨hsSig, htest⟩
    have hproperty :
        s ∉ SkewTree.interior (StarredSignature.signatureTree O cut hout) ∧
          s ≠ cut := by
      simpa using htest
    rcases (mem_signatureTree_iff O cut hout s).1 hsSig with hi | hb
    · exact (hproperty.1 (hpersist s hi hproperty.2)).elim
    · exact List.mem_append.mpr (Or.inl hb)
  · exact List.mem_append.mpr (Or.inr hchild)

/-- At most one literal R marker lies below each ambient frontier cone. -/
theorem literalR_unique_marker_in_cone
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (hpersist : InteriorPersists O cut hout)
    {s t f : Node b}
    (hs : s ∈ literalR O cut hout)
    (ht : t ∈ literalR O cut hout)
    (hsf : IsPrefix s f)
    (htf : IsPrefix t f) :
    s = t :=
  MarkerAntichain.unique_candidate_marker_in_cone
    O cut hout
    (literalR_subset_coneMarkers O cut hout hpersist hs)
    (literalR_subset_coneMarkers O cut hout hpersist ht)
    hsf htf

/--
Every literal marker R has a unique frontier beyond the inclusive
support cut, under interior persistence and the early-level condition.
-/
theorem literalR_unique_inclusive_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (hpersist : InteriorPersists O cut hout)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ literalR O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f :=
  CompleteInteriorBranching.coneMarker_unique_frontier_of_complete_height
    O cut hout T hcomplete hnonsingleton hST hcut hlevel
    (literalR_subset_coneMarkers O cut hout hpersist hs)

end DualTree.LiteralSignatureR
