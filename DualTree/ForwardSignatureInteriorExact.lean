import DualTree.ForwardSignatureInteriorPersistence
import DualTree.ForwardMarkerAntichain
import DualTree.Lemma27QTerminal

/-!
# Exact interior of the globally forward-repaired signature

The source signature S' in Definition 26 consists of all original
interior nodes together with first strict-forward-cut boundaries of
exceptional leaves. The existing forward interior-persistence theorem
establishes only Int(S)\{cut} ⊆ Int(S').

We prove the converse: every exceptional boundary is a leaf of S'.
It has no strict descendant among the old interior (all those nodes
are forward-auxiliary ≤ cut, while the boundary is strictly outside
the inclusive cut), nor among the exceptional boundaries (which form
an antichain). The retained cut is also a leaf of S': no original
interior strictly extends the maximal cut, and exceptional boundary
paths come from leaves outside the cut's ambient cone.

Thus Int(S') = Int(S) \ {cut}. In particular,
Int(S') ∪ {cut} = Int(S) as finite sets, the exact source-side
base identity needed by the corrected Q construction.

Unlike the printed-order version, the entire argument refers only
to the forward-corrected signature and never assumes the false
reverse-auxiliary-order preservation.
-/

namespace DualTree.ForwardSignatureInteriorExact

open ForwardSignatureBoundary

/-- Every newly inserted exceptional-leaf boundary is terminal
in the corrected signature tree. -/
theorem exceptional_boundary_no_strict_signature_descendant
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves O cut})
    (u : Node b)
    (hu : u ∈ ForwardStarredSignature.signatureTree O cut hout) :
    ¬ IsStrictPrefix
      (firstBoundary cut t.1 (hout t.1 t.2)) u := by
  intro hstrict
  let r := firstBoundary cut t.1 (hout t.1 t.2)
  have hrBoundary :
      ForwardInclusiveFrontier.ForwardCutBoundary cut r :=
    ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      O cut hout t.1 t.2
  rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout u).1 hu with hi | ⟨v, hv⟩
  · have huEarly : ForwardAux u cut := by
      simpa [SkewTree.forwardAuxB] using hmax u hi
    have hrEarly : ForwardAux r cut :=
      ForwardInclusiveFrontier.forwardAux_of_prefix
        hstrict.1 huEarly
    exact hrBoundary.1 hrEarly
  · have hvBoundary :
        ForwardInclusiveFrontier.ForwardCutBoundary cut
          (firstBoundary cut v.1 (hout v.1 v.2)) :=
      ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
        O cut hout v.1 v.2
    have hrEq :
        r = firstBoundary cut v.1 (hout v.1 v.2) :=
      ForwardMarkerAntichain.eq_of_prefix_boundaries
        cut r
        (firstBoundary cut v.1 (hout v.1 v.2))
        hrBoundary hvBoundary
        (by simpa [r, hv] using hstrict.1)
    have hru : r = u := hrEq.trans hv
    exact hstrict.2 hru

/-- No exceptional boundary contributes a new interior node
to the corrected signature. -/
theorem exceptional_boundary_not_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves O cut}) :
    firstBoundary cut t.1 (hout t.1 t.2) ∉
      SkewTree.interior
        (ForwardStarredSignature.signatureTree O cut hout) := by
  exact Lemma27QTerminal.not_interior_of_no_strict_descendant
    (ForwardStarredSignature.signatureTree O cut hout)
    (firstBoundary cut t.1 (hout t.1 t.2))
    (fun u hu =>
      exceptional_boundary_no_strict_signature_descendant
        O cut hmax hout t u hu)

/-- Signature interior vertices must already belong to the
original source interior: no boundary can be interior. -/
theorem signature_interior_subset_original
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b)
    (hs : s ∈ SkewTree.interior
      (ForwardStarredSignature.signatureTree O cut hout)) :
    s ∈ SkewTree.interior O.tree := by
  have hsSig : s ∈
      ForwardStarredSignature.signatureTree O cut hout :=
    (List.mem_filter.mp hs).1
  rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout s).1 hsSig with hOld | ⟨t, ht⟩
  · exact hOld
  · have hNot :=
      exceptional_boundary_not_interior O cut hmax hout t
    rw [ht] at hNot
    exact False.elim (hNot hs)

/-- The retained final cut has no strict descendant in the
corrected signature, and so is itself terminal there. -/
theorem cut_not_signature_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) :
    cut ∉ SkewTree.interior
      (ForwardStarredSignature.signatureTree O cut hout) := by
  apply Lemma27QTerminal.not_interior_of_no_strict_descendant
  intro u hu
  intro hstrict
  rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout u).1 hu with hOld | ⟨t, ht⟩
  · have haux : ForwardAux u cut := by
      simpa [SkewTree.forwardAuxB] using hmax u hOld
    have hlt : cut.length < u.length :=
      MeetClosedFromBranching.length_lt_of_strictPrefix hstrict
    rcases haux with ha | ⟨ha, _⟩ <;> omega
  · have hp : IsPrefix
        (firstBoundary cut t.1 (hout t.1 t.2)) t.1 :=
      (firstBoundary_spec cut t.1 (hout t.1 t.2)).1
    have hcu : IsPrefix cut t.1 := by
      rw [← ht] at hstrict
      exact isPrefix_trans hstrict.1 hp
    exact (StarredSignature.exceptionalLeaves_spec
      O cut t.1 t.2).2.2 hcu

/-- The exact corrected signature interior is the original
source interior with its final cut removed. -/
theorem signature_interior_iff_original_ne_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b) :
    s ∈ SkewTree.interior
      (ForwardStarredSignature.signatureTree O cut hout) ↔
      s ∈ SkewTree.interior O.tree ∧ s ≠ cut := by
  constructor
  · intro hs
    refine ⟨signature_interior_subset_original
      O cut hmax hout s hs, ?_⟩
    intro hsc
    subst s
    exact (cut_not_signature_interior O cut hmax hout) hs
  · rintro ⟨hs, hne⟩
    exact ForwardSignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout s hs hne

/-- The fixed old base of the corrected Lemma 27 Q tree,
namely Int(S') together with cut, has the original
source's interior membership exactly. -/
theorem oldBase_mem_iff_original_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b) :
    s ∈
      (SkewTree.interior
          (ForwardStarredSignature.signatureTree O cut hout) ++
        [cut]) ↔
    s ∈ SkewTree.interior O.tree := by
  rw [List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (signature_interior_iff_original_ne_cut
        O cut hcut hmax hout s).1 h |>.1
    · subst s
      exact hcut
  · intro hs
    by_cases hsc : s = cut
    · exact Or.inr hsc
    · exact Or.inl
        ((signature_interior_iff_original_ne_cut
          O cut hcut hmax hout s).2 ⟨hs, hsc⟩)

end DualTree.ForwardSignatureInteriorExact
