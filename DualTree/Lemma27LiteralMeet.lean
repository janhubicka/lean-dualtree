import DualTree.InteriorMarkerMeet
import DualTree.SupportReachability
import DualTree.Lemma27QBranchOccupancy
import DualTree.Lemma27QLeafReplacement

/-!
# Meet closure of the literal Lemma 27 signature skeleton

The generic interior-plus-marker meet theorem is now instantiated
with the source's *literal* R, consisting of exceptional signature
leaf boundaries and all ambient immediate successors of t₀.

The starred source S is semi-complete, hence meet-closed.
The literal markers are an antichain outside the inclusive cut,
and no marker is a prefix of an old interior node.

The only remaining assumption in the generic theorem is that
every marker has a descendant in S. Exceptional boundaries
come with an original leaf. Every child of t₀ has an original
descendant because semi-completeness and skewness imply a
unique successor in every ambient direction at the non-leaf t₀.

Consequently the literal pre-replacement skeleton
   Int(S′) ∪ {t₀} ∪ R = Int(S) ∪ R
is closed under ambient meets, and the meet of any two
distinct vertices lies in the original interior Int(S).

The transfer of this property through the actual projected
D₂ leaf replacement to S_w remains separate.
-/

namespace DualTree.Lemma27LiteralMeet

/-- A maximal-interior cut in a starred semi-complete tree
has one immediate source-support successor in every direction. -/
theorem fullDirections_at_maxInterior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree) :
    ∀ i : Fin b, SkewTree.uniqueBranchB O.tree cut i = true := by
  have hs : cut ∈ O.tree := by
    have h := hcut
    change cut ∈ O.tree.filter
      (fun s => !(SkewTree.immediateSuccs O.tree s).isEmpty) at h
    exact (List.mem_filter.mp h).1
  have hflag :
      (SkewTree.immediateSuccs O.tree cut).isEmpty = false := by
    have h := hcut
    change cut ∈ O.tree.filter
      (fun s => !(SkewTree.immediateSuccs O.tree s).isEmpty) at h
    have htest := (List.mem_filter.mp h).2
    cases hchildren : SkewTree.immediateSuccs O.tree cut with
    | nil => simp [hchildren] at htest
    | cons u us => rfl
  cases hchildren : SkewTree.immediateSuccs O.tree cut with
  | nil =>
      simp [hchildren] at hflag
  | cons u us =>
      have hu : u ∈ SkewTree.immediateSuccs O.tree cut := by
        simp [hchildren]
      have hu' : u ∈ O.tree.filter
          (fun t => SkewTree.immediateSuccB O.tree cut t) := hu
      have huS : u ∈ O.tree := (List.mem_filter.mp hu').1
      have hstep : SkewTree.immediateSuccB O.tree cut u = true :=
        (List.mem_filter.mp hu').2
      have hne : cut ≠ u :=
        ((SkewBranchGeometry.immediateSuccB_iff O.tree cut u).1
          hstep).2.1.2
      have hnon : O.tree.length ≠ 1 :=
        SupportReachability.nonsingleton_of_distinct_members
          O.tree hs huS hne
      have hnonleaf : (SkewTree.immediateSuccs O.tree cut).length ≠ 0 := by
        simp [hchildren]
      exact SemiCompleteSkewMeet.fullDirections_of_semiComplete_nonleaf_total
        SkewTree.paperAuxB O.tree O.semi_complete hnon
        (fun x y _ => SkewMeetInstantiation.paperAuxB_total x y)
        cut hs hnonleaf

/-- Every literal R marker extends to a vertex of the
original semi-complete starred support S. -/
theorem literalMarker_has_original_support_descendant
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (r : Node b) (hr : r ∈ LiteralSignatureR.literalR O cut hout) :
    ∃ t : Node b, t ∈ O.tree ∧ IsPrefix r t := by
  have hpersist :=
    SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout
  have hrCandidate :
      r ∈ SignatureMarker.coneMarkers O cut hout :=
    LiteralSignatureR.literalR_subset_coneMarkers
      O cut hout hpersist hr
  have hbranches : ∀ i : Fin b,
      ∃ t, t ∈ O.tree ∧ IsPrefix (cut ++ [i]) t := by
    intro i
    exact DirectionalSupport.descendant_of_uniqueBranch
      O.tree cut i (fullDirections_at_maxInterior O cut hcut i)
  exact SignatureMarker.coneMarker_has_support_descendant
    O cut hout O.tree (fun t ht => ht) hbranches hrCandidate

/-- Distinct literal markers form a prefix antichain. -/
theorem literalR_antichain
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (r s : Node b)
    (hr : r ∈ LiteralSignatureR.literalR O cut hout)
    (hs : s ∈ LiteralSignatureR.literalR O cut hout)
    (hrs : IsPrefix r s) :
    r = s := by
  have hpersist :=
    SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout
  exact LiteralSignatureR.literalR_unique_marker_in_cone
    O cut hout hpersist hr hs hrs (isPrefix_refl s)

/-- No literal marker can be a prefix of an original interior node. -/
theorem literalR_not_prefix_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (r : Node b) (hr : r ∈ LiteralSignatureR.literalR O cut hout)
    (u : Node b) (hu : u ∈ SkewTree.interior O.tree) :
    ¬ IsPrefix r u := by
  let rs : {r : Node b // r ∈
    LiteralSignatureR.literalR O cut hout} := ⟨r, hr⟩
  have hOutside : ¬ PaperAux r cut :=
    Lemma27QLeafReplacement.literalMarker_after_cut
      O cut hcut hmax hout rs
  have huEarly : PaperAux u cut := by
    simpa [SkewTree.paperAuxB] using hmax u hu
  intro hru
  exact hOutside
    (CutPreservation.paperAux_of_prefix hru huEarly)

/-- Two distinct nodes of the literal Int(S) ∪ R skeleton
have their longest common prefix in the original interior Int(S). -/
theorem distinct_literal_skeleton_meet_in_original_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (x y : Node b)
    (hx : x ∈ SkewTree.interior O.tree ∨
      x ∈ LiteralSignatureR.literalR O cut hout)
    (hy : y ∈ SkewTree.interior O.tree ∨
      y ∈ LiteralSignatureR.literalR O cut hout)
    (hne : x ≠ y) :
    MeetGeometry.commonPrefix x y ∈ SkewTree.interior O.tree := by
  exact InteriorMarkerMeet.meet_distinct_interior_union_markers
    O.tree (LiteralSignatureR.literalR O cut hout)
    (SemiCompleteSkewMeet.meetClosed_starred O)
    (fun r hr =>
      literalMarker_has_original_support_descendant
        O cut hcut hmax hout r hr)
    (fun r s hr hs hpre =>
      literalR_antichain O cut hcut hmax hout r s hr hs hpre)
    (fun r hr u hu =>
      literalR_not_prefix_interior O cut hcut hmax hout r hr u hu)
    hx hy hne

/-- The source's literal finite tree
Int(S′) ∪ {t₀} ∪ R is ambient meet-closed. -/
theorem oldSkeleton_meetClosed
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    MeetGeometry.MeetClosed
      (Lemma27QBranchOccupancy.oldSkeleton O cut hout).toList := by
  have hmember : ∀ z : Node b,
      z ∈ (Lemma27QBranchOccupancy.oldSkeleton O cut hout).toList ↔
      z ∈ SkewTree.interior O.tree ++
        LiteralSignatureR.literalR O cut hout := by
    intro z
    classical
    change z ∈
      ((Lemma27SignatureTree.oldSignatureBase O cut hout).toFinset ∪
        (LiteralSignatureR.literalR O cut hout).toFinset).toList ↔
      z ∈ SkewTree.interior O.tree ++
        LiteralSignatureR.literalR O cut hout
    simp only [Finset.mem_toList, Finset.mem_union,
      List.mem_toFinset, List.mem_append]
    exact or_congr
      (Lemma27QTreeCount.oldBase_mem_iff_original_interior
        O cut hcut hmax hout z) Iff.rfl
  have hmeet : MeetGeometry.MeetClosed
      (SkewTree.interior O.tree ++
        LiteralSignatureR.literalR O cut hout) :=
    InteriorMarkerMeet.meetClosed_interior_union_markers
      O.tree (LiteralSignatureR.literalR O cut hout)
      (SemiCompleteSkewMeet.meetClosed_starred O)
      (fun r hr =>
        literalMarker_has_original_support_descendant
          O cut hcut hmax hout r hr)
      (fun r s hr hs hpre =>
        literalR_antichain O cut hcut hmax hout r s hr hs hpre)
      (fun r hr u hu =>
        literalR_not_prefix_interior O cut hcut hmax hout r hr u hu)
  intro x y hx hy
  have hx' := (hmember x).1 hx
  have hy' := (hmember y).1 hy
  exact (hmember _).2 (hmeet x y hx' hy')

end DualTree.Lemma27LiteralMeet
