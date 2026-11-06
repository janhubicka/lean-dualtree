import DualTree.ForwardQFinalFullSignature

/-!
# Complete corrected signatures independent of tree-list enumeration

The tree component of the corrected Definition-26 signature is a finite
set of actual nodes. Its list enumeration does not change the cut, the
old variable roots, the exceptional first-boundary nodes, or the rooted
partial word. This module records that set-valued signature while keeping
the full optional partial word, including its strict initial domain.

Equality of these complete set signatures forces a common cut. At that
cut it gives equal interior membership and equal boundary-marker
membership. These are the ingredients for reenumerating a target into
the existing literal-list interface without changing its word or nodes.
The existing literal signature API is left unchanged.
-/

namespace DualTree.ForwardQFinalSetSignature

open ForwardQFinalFullSignature
open ForwardSignatureBoundary

/-- The actual corrected signature with only its tree enumeration
erased. The optional rooted partial word still records its full domain. -/
noncomputable def completeSetSignature
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true) :
    Finset (Node b) ×
      (BoundedNode b n → Option (Sum α (BoundedNode b n))) :=
  ((completeSignature hb O cut hcut hmax).1.toFinset,
    (completeSignature hb O cut hcut hmax).2)

/-- Complete corrected signature agreement up to the enumeration of
the finite signature tree, with each maximal interior cut explicit. -/
structure SameCompleteSetForwardSignature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b) : Prop where
  cutInterior : cutO ∈ SkewTree.interior O.tree
  cutMaximal : ∀ t, t ∈ SkewTree.interior O.tree →
    SkewTree.forwardAuxB t cutO = true
  signatureEq :
    completeSetSignature hb O cutO cutInterior cutMaximal =
      completeSetSignature hb g.core.source g.core.cut
        g.core.hcut g.core.hmax

/-- Original interior nodes are exactly the signature nodes at or
before the maximal cut. Exceptional boundaries lie strictly outside it. -/
private theorem interior_iff_signature_early
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b) :
    s ∈ SkewTree.interior O.tree ↔
      s ∈ ForwardStarredSignature.signatureTree O cut hout ∧
        ForwardAux s cut := by
  constructor
  · intro hs
    refine ⟨ForwardStarredSignature.interior_mem_signatureTree O cut hout hs, ?_⟩
    simpa [SkewTree.forwardAuxB] using hmax s hs
  · rintro ⟨hs, hearly⟩
    rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout s).1 hs with hi | ⟨t, ht⟩
    · exact hi
    · have hlate :=
        (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
          O cut hout t.1 t.2).1
      rw [ht] at hlate
      exact False.elim (hlate hearly)

/-- The exceptional first-boundary nodes are exactly the signature
nodes outside the inclusive maximal cut. -/
private theorem boundary_iff_signature_late
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b) :
    (∃ t : {t : Node b // t ∈ StarredSignature.exceptionalLeaves O cut},
      firstBoundary cut t.1 (hout t.1 t.2) = s) ↔
      s ∈ ForwardStarredSignature.signatureTree O cut hout ∧
        ¬ ForwardAux s cut := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout s).2 (Or.inr ⟨t, ht⟩), ?_⟩
    have hlate :=
      (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
        O cut hout t.1 t.2).1
    simpa only [ht] using hlate
  · rintro ⟨hs, hlate⟩
    rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout s).1 hs with hi | hboundary
    · have hearly : ForwardAux s cut := by
        simpa [SkewTree.forwardAuxB] using hmax s hi
      exact False.elim (hlate hearly)
    · exact hboundary

namespace SameCompleteSetForwardSignature

variable {b n l k m : Nat} {α : Type*}
    {hb : 0 < b}
    {g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α}
    {O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))}
    {cutO : Node b}

/-- The retained partial-word domains determine the same actual cut,
regardless of how either signature tree is enumerated. -/
theorem same_cut (H : SameCompleteSetForwardSignature hb g O cutO) :
    cutO = g.core.cut := by
  have hPartial : strictPartialWord cutO O.word =
      strictPartialWord g.core.cut g.core.source.word :=
    congrArg Prod.snd H.signatureEq
  have hDomain : ∀ s : BoundedNode b n,
      BeforeCut cutO s.1 ↔ BeforeCut g.core.cut s.1 := by
    intro s
    calc
      BeforeCut cutO s.1 ↔ strictPartialWord cutO O.word s ≠ none :=
        (strictPartialWord_ne_none_iff cutO O.word s).symm
      _ ↔ strictPartialWord g.core.cut g.core.source.word s ≠ none := by
        rw [congrFun hPartial s]
      _ ↔ BeforeCut g.core.cut s.1 :=
        strictPartialWord_ne_none_iff g.core.cut g.core.source.word s
  let outCut : BoundedNode b n :=
    ⟨cutO, O.tree_bounded cutO (List.mem_filter.mp H.cutInterior).1⟩
  let oldCut : BoundedNode b n :=
    ⟨g.core.cut, g.T_bounded g.core.cut g.core.hcutT⟩
  exact congrArg Subtype.val
    (ForwardSignatureCutDomainRigidity.bounded_cut_eq_of_beforeCut_iff
      outCut oldCut hDomain)

/-- The original distinguished cut is also an interior node of the target. -/
theorem cutInterior_common (H : SameCompleteSetForwardSignature hb g O cutO) :
    g.core.cut ∈ SkewTree.interior O.tree := by
  rw [← H.same_cut]
  exact H.cutInterior

/-- Target maximality transported to the common distinguished cut. -/
theorem cutMaximal_common (H : SameCompleteSetForwardSignature hb g O cutO) :
    ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t g.core.cut = true := by
  intro t ht
  rw [← H.same_cut]
  exact H.cutMaximal t ht

/-- Every target exceptional leaf has its genuine boundary at the common cut. -/
theorem hout_common (H : SameCompleteSetForwardSignature hb g O cutO) :
    ∀ t, t ∈ StarredSignature.exceptionalLeaves O g.core.cut →
      ¬ BeforeCut g.core.cut t :=
  ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
    hb O g.core.cut H.cutInterior_common H.cutMaximal_common

/-- Equality of the actual signature-tree node sets at the common cut. -/
theorem signatureTree_finset_eq (H : SameCompleteSetForwardSignature hb g O cutO) :
    (ForwardStarredSignature.signatureTree O g.core.cut H.hout_common).toFinset =
      (ForwardStarredSignature.signatureTree
        g.core.source g.core.cut g.core.hout).toFinset := by
  have hcut := H.same_cut
  subst cutO
  exact congrArg Prod.fst H.signatureEq

/-- Node membership in the two actual signature trees agrees. -/
theorem signatureTree_mem_iff (H : SameCompleteSetForwardSignature hb g O cutO)
    (s : Node b) :
    s ∈ ForwardStarredSignature.signatureTree O g.core.cut H.hout_common ↔
      s ∈ ForwardStarredSignature.signatureTree
        g.core.source g.core.cut g.core.hout := by
  rw [← List.mem_toFinset, ← List.mem_toFinset, H.signatureTree_finset_eq]

/-- Equality of the full optional partial word at the recovered common cut. -/
theorem strictPartialWord_common_eq
    (H : SameCompleteSetForwardSignature hb g O cutO) :
    strictPartialWord g.core.cut O.word =
      strictPartialWord g.core.cut g.core.source.word := by
  have hPartial : strictPartialWord cutO O.word =
      strictPartialWord g.core.cut g.core.source.word :=
    congrArg Prod.snd H.signatureEq
  simpa only [H.same_cut] using hPartial

/-- Actual rooted symbols agree on every strictly pre-cut position. -/
theorem strict_prefix_eq (H : SameCompleteSetForwardSignature hb g O cutO)
    (s : BoundedNode b n) (hs : BeforeCut g.core.cut s.1) :
    CutPreservation.underlyingSymbol O.word s =
      CutPreservation.underlyingSymbol g.core.source.word s := by
  have hPartial := congrFun H.strictPartialWord_common_eq s
  have hsome : some (CutPreservation.underlyingSymbol O.word s) =
      some (CutPreservation.underlyingSymbol g.core.source.word s) := by
    simpa [strictPartialWord, hs] using hPartial
  exact Option.some.inj hsome

/-- Set-valued complete signatures determine exactly the old interior
roots, without comparing either tree's list enumeration. -/
theorem interior_mem_iff (H : SameCompleteSetForwardSignature hb g O cutO)
    (s : Node b) :
    s ∈ SkewTree.interior O.tree ↔
      s ∈ SkewTree.interior g.core.source.tree := by
  calc
    s ∈ SkewTree.interior O.tree ↔
        s ∈ ForwardStarredSignature.signatureTree O g.core.cut H.hout_common ∧
          ForwardAux s g.core.cut :=
      interior_iff_signature_early O g.core.cut H.cutMaximal_common H.hout_common s
    _ ↔ s ∈ ForwardStarredSignature.signatureTree
          g.core.source g.core.cut g.core.hout ∧ ForwardAux s g.core.cut :=
      and_congr (H.signatureTree_mem_iff s) Iff.rfl
    _ ↔ s ∈ SkewTree.interior g.core.source.tree :=
      (interior_iff_signature_early g.core.source g.core.cut
        g.core.hmax g.core.hout s).symm

/-- The signature interiors agree as node sets as well. -/
theorem signatureInterior_mem_iff
    (H : SameCompleteSetForwardSignature hb g O cutO) (s : Node b) :
    s ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree O g.core.cut H.hout_common) ↔
      s ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree
          g.core.source g.core.cut g.core.hout) := by
  calc
    s ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree O g.core.cut H.hout_common) ↔
        s ∈ SkewTree.interior O.tree ∧ s ≠ g.core.cut :=
      ForwardSignatureInteriorExact.signature_interior_iff_original_ne_cut
        O g.core.cut H.cutInterior_common H.cutMaximal_common H.hout_common s
    _ ↔ s ∈ SkewTree.interior g.core.source.tree ∧ s ≠ g.core.cut :=
      and_congr (H.interior_mem_iff s) Iff.rfl
    _ ↔ s ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree
          g.core.source g.core.cut g.core.hout) :=
      (ForwardSignatureInteriorExact.signature_interior_iff_original_ne_cut
        g.core.source g.core.cut g.core.hcut g.core.hmax g.core.hout s).symm

/-- A node is an actual exceptional first boundary for the target
exactly when it is one for the original source. -/
theorem exceptionalBoundary_mem_iff
    (H : SameCompleteSetForwardSignature hb g O cutO) (s : Node b) :
    (∃ t : {t : Node b // t ∈ StarredSignature.exceptionalLeaves O g.core.cut},
      firstBoundary g.core.cut t.1 (H.hout_common t.1 t.2) = s) ↔
      ∃ t : {t : Node b //
          t ∈ StarredSignature.exceptionalLeaves g.core.source g.core.cut},
        firstBoundary g.core.cut t.1 (g.core.hout t.1 t.2) = s := by
  calc
    (∃ t : {t : Node b // t ∈ StarredSignature.exceptionalLeaves O g.core.cut},
        firstBoundary g.core.cut t.1 (H.hout_common t.1 t.2) = s) ↔
        s ∈ ForwardStarredSignature.signatureTree O g.core.cut H.hout_common ∧
          ¬ ForwardAux s g.core.cut :=
      boundary_iff_signature_late O g.core.cut H.cutMaximal_common H.hout_common s
    _ ↔ s ∈ ForwardStarredSignature.signatureTree
          g.core.source g.core.cut g.core.hout ∧ ¬ ForwardAux s g.core.cut :=
      and_congr (H.signatureTree_mem_iff s) Iff.rfl
    _ ↔ ∃ t : {t : Node b //
          t ∈ StarredSignature.exceptionalLeaves g.core.source g.core.cut},
        firstBoundary g.core.cut t.1 (g.core.hout t.1 t.2) = s :=
      (boundary_iff_signature_late g.core.source g.core.cut
        g.core.hmax g.core.hout s).symm

/-- The genuine terminal signature-marker sets agree. -/
theorem signatureTerminalMarkers_mem_iff
    (H : SameCompleteSetForwardSignature hb g O cutO) (s : Node b) :
    s ∈ ForwardStarredSignature.signatureTerminalMarkers
        O g.core.cut H.hout_common ↔
      s ∈ ForwardStarredSignature.signatureTerminalMarkers
        g.core.source g.core.cut g.core.hout := by
  classical
  simp only [ForwardStarredSignature.signatureTerminalMarkers,
    List.mem_filter, decide_eq_true_eq]
  exact and_congr (H.signatureTree_mem_iff s)
    (and_congr (not_congr (H.signatureInterior_mem_iff s)) Iff.rfl)

/-- The complete literal-R marker node sets agree, including the
ambient children of the common cut. -/
theorem literalR_mem_iff (H : SameCompleteSetForwardSignature hb g O cutO)
    (s : Node b) :
    s ∈ ForwardStarredSignature.literalR O g.core.cut H.hout_common ↔
      s ∈ ForwardStarredSignature.literalR
        g.core.source g.core.cut g.core.hout := by
  classical
  simpa only [ForwardStarredSignature.literalR, List.mem_dedup, List.mem_append] using
    (or_congr (H.signatureTerminalMarkers_mem_iff s)
      (Iff.rfl :
        s ∈ (SkewTree.allFin b).map (fun i => g.core.cut ++ [i]) ↔
          s ∈ (SkewTree.allFin b).map (fun i => g.core.cut ++ [i])))

end SameCompleteSetForwardSignature

/-- Existing literal-list complete-signature equality always implies
the enumeration-independent complete set-signature certificate. -/
theorem of_sameCompleteForwardSignature
    {b n l k m : Nat} {α : Type*}
    {hb : 0 < b}
    {g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α}
    {O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))}
    {cutO : Node b}
    (H : SameCompleteForwardSignature hb g O cutO) :
    SameCompleteSetForwardSignature hb g O cutO := by
  refine {
    cutInterior := H.cutInterior
    cutMaximal := H.cutMaximal
    signatureEq := ?_
  }
  exact congrArg
    (fun signature : List (Node b) ×
        (BoundedNode b n → Option (Sum α (BoundedNode b n))) =>
      (signature.1.toFinset, signature.2)) H.signatureEq

end DualTree.ForwardQFinalSetSignature
