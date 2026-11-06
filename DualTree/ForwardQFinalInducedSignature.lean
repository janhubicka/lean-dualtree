import DualTree.ForwardQFinalSetSignature
import DualTree.ForwardQLiteralMarkerLeafEquiv

/-!
# Every corrected Q output has the complete source set signature

The corrected Q tree keeps exactly the original source interior and
places one terminal in each literal source boundary cone. A terminal
in a cut-child cone remains a descendant of the cut. A terminal above an
exceptional first-boundary marker stays outside the cut cone and has the
same first boundary. Thus the actual finite-set signature tree is fixed.

The fibrewise Q word also agrees with the source word on the whole strict
initial domain: an ambient variable root below an initial position is
itself initial, and original ambient constants are preserved by the source
substitution. This proves equality of the full rooted partial word,
including its domain, without an alphabet-cardinality hypothesis.

The theorem applies to every genuine enlarged starred Q input. It does
not claim that every such output refines an arbitrarily supplied final
word; that separate conclusion uses the induced local evaluation.
-/

namespace DualTree.ForwardQFinalInducedSignature

open ForwardSourceQTree
open ForwardSignatureBoundary
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQFinalFullSignature
open ForwardQFinalSetSignature

private theorem output_interior_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback)
    (t : Node b) :
    t ∈ SkewTree.interior (fibreQStarredWord hb g fallback w).tree ↔
      t ∈ SkewTree.interior g.core.source.tree :=
  ForwardQInteriorExact.Q_interior_iff_original hb g.core
    (ForwardQEnlargedConstantWords.eraseAux g.core fallback w.1) t

private theorem firstBoundary_eq_of_extends
    {b : Nat} (cut old target : Node b)
    (hold : ¬ BeforeCut cut old)
    (htarget : ¬ BeforeCut cut target)
    (hprefix : IsPrefix (firstBoundary cut old hold) target) :
    firstBoundary cut target htarget = firstBoundary cut old hold := by
  have hboundary : Boundary cut target (firstBoundary cut old hold) :=
    ⟨hprefix, (firstBoundary_spec cut old hold).2⟩
  exact ((Classical.choose_spec
    (existsUnique_boundary_on_path cut target htarget)).2
      (firstBoundary cut old hold) hboundary).symm

private theorem exceptional_boundary_extension_not_under_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (e : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves c.source c.cut})
    (t : Node b)
    (hprefix : IsPrefix
      (firstBoundary c.cut e.1 (c.hout e.1 e.2)) t) :
    ¬ IsPrefix c.cut t := by
  intro hcut
  let r := firstBoundary c.cut e.1 (c.hout e.1 e.2)
  have hrOriginal : IsPrefix r e.1 :=
    (firstBoundary_spec c.cut e.1 (c.hout e.1 e.2)).1
  have hrOutside : ¬ ForwardAux r c.cut :=
    (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      c.source c.cut c.hout e.1 e.2).1
  rcases le_total c.cut.length r.length with hle | hle
  · have hcutR : IsPrefix c.cut r :=
      CutFrontier.prefix_of_prefix_length_le hcut hprefix hle
    exact (StarredSignature.exceptionalLeaves_spec
      c.source c.cut e.1 e.2).2.2
        (isPrefix_trans hcutR hrOriginal)
  · have hrCut : IsPrefix r c.cut :=
      CutFrontier.prefix_of_prefix_length_le hprefix hcut hle
    exact hrOutside (ForwardInclusiveFrontier.forwardAux_of_prefix
      hrCut (CanonicalForwardAuxIso.forwardAux_refl c.cut))

private theorem source_boundary_has_output_exceptional
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback)
    (houtQ : ∀ t,
      t ∈ StarredSignature.exceptionalLeaves
        (fibreQStarredWord hb g fallback w) g.core.cut →
      ¬ BeforeCut g.core.cut t)
    (e : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves g.core.source g.core.cut}) :
    ∃ eQ : {t : Node b //
        t ∈ StarredSignature.exceptionalLeaves
          (fibreQStarredWord hb g fallback w) g.core.cut},
      firstBoundary g.core.cut eQ.1 (houtQ eQ.1 eQ.2) =
        firstBoundary g.core.cut e.1 (g.core.hout e.1 e.2) := by
  classical
  let x := ForwardQEnlargedConstantWords.eraseAux g.core fallback w.1
  let r : ForwardSortedMixedProduct.Marker
      g.core.source g.core.cut g.core.hout :=
    ⟨firstBoundary g.core.cut e.1 (g.core.hout e.1 e.2),
      ForwardQInteriorExact.exceptional_boundary_mem_literalR
        g.core.source g.core.cut g.core.hmax g.core.hout e⟩
  let j := ForwardQMarkerCoverage.bulletForMarker g.core r
  let t := (markedProjection g.core x j).1
  have ht : t ∈ (fibreQStarredWord hb g fallback w).tree :=
    Finset.mem_toList.mpr (markedProjection_mem g.core x j)
  have hterminal :
      t ∉ SkewTree.interior (fibreQStarredWord hb g fallback w).tree :=
    ForwardQSourceTerminals.markedProjection_terminal g.core x j
  have hprefix : IsPrefix
      (firstBoundary g.core.cut e.1 (g.core.hout e.1 e.2)) t :=
    ForwardQMarkerCoverage.marker_prefix_projected_point g.core x r
  have hnotCut : ¬ IsPrefix g.core.cut t :=
    exceptional_boundary_extension_not_under_cut g.core e t hprefix
  have heQ : t ∈ StarredSignature.exceptionalLeaves
      (fibreQStarredWord hb g fallback w) g.core.cut := by
    simp only [StarredSignature.exceptionalLeaves, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨ht, hterminal, hnotCut⟩
  exact ⟨⟨t, heQ⟩, firstBoundary_eq_of_extends
    g.core.cut e.1 t (g.core.hout e.1 e.2) (houtQ t heQ) hprefix⟩

private theorem output_exceptional_has_source_boundary
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback)
    (houtQ : ∀ t,
      t ∈ StarredSignature.exceptionalLeaves
        (fibreQStarredWord hb g fallback w) g.core.cut →
      ¬ BeforeCut g.core.cut t)
    (eQ : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves
        (fibreQStarredWord hb g fallback w) g.core.cut}) :
    ∃ e : {t : Node b //
        t ∈ StarredSignature.exceptionalLeaves g.core.source g.core.cut},
      firstBoundary g.core.cut eQ.1 (houtQ eQ.1 eQ.2) =
        firstBoundary g.core.cut e.1 (g.core.hout e.1 e.2) := by
  classical
  let x := ForwardQEnlargedConstantWords.eraseAux g.core fallback w.1
  have heQ := StarredSignature.exceptionalLeaves_spec
    (fibreQStarredWord hb g fallback w) g.core.cut eQ.1 eQ.2
  let leaf : ForwardQLiteralMarkerLeafEquiv.QLeaf g.core x :=
    ⟨eQ.1, heQ.1, heQ.2.1⟩
  obtain ⟨j, hj⟩ :=
    ForwardQLiteralMarkerLeafEquiv.Q_leaf_has_bullet hb g.core x leaf
  obtain ⟨r, hr⟩ :=
    (ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core).surjective j
  have hprojection :
      (markedProjection g.core x
        (ForwardQMarkerCoverage.bulletForMarker g.core r)).1 = eQ.1 := by
    change (markedProjection g.core x
      ((ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core) r)).1 = eQ.1
    rw [hr]
    exact hj
  have hprefix : IsPrefix r.1 eQ.1 := by
    rw [← hprojection]
    exact ForwardQMarkerCoverage.marker_prefix_projected_point g.core x r
  have hrParts :
      r.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          g.core.source g.core.cut g.core.hout ++
        (SkewTree.allFin b).map (fun i => g.core.cut ++ [i]) := by
    have hrLiteral : r.1 ∈ ForwardStarredSignature.literalR
        g.core.source g.core.cut g.core.hout := r.2
    simpa only [ForwardStarredSignature.literalR, List.mem_dedup] using hrLiteral
  rcases List.mem_append.mp hrParts with hterminal | hchild
  · obtain ⟨e, he⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        g.core.source g.core.cut g.core.hcut g.core.hmax g.core.hout
        r.1 hterminal
    have hboundaryPrefix : IsPrefix
        (firstBoundary g.core.cut e.1 (g.core.hout e.1 e.2)) eQ.1 := by
      rw [he]
      exact hprefix
    exact ⟨e, firstBoundary_eq_of_extends
      g.core.cut e.1 eQ.1 (g.core.hout e.1 e.2)
      (houtQ eQ.1 eQ.2) hboundaryPrefix⟩
  · obtain ⟨i, _hi, hir⟩ := List.mem_map.mp hchild
    have hcutR : IsPrefix g.core.cut r.1 := by
      rw [← hir]
      exact ⟨[i], rfl⟩
    exact False.elim (heQ.2.2 (isPrefix_trans hcutR hprefix))

private theorem output_signatureTree_mem_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback)
    (houtQ : ∀ t,
      t ∈ StarredSignature.exceptionalLeaves
        (fibreQStarredWord hb g fallback w) g.core.cut →
      ¬ BeforeCut g.core.cut t)
    (s : Node b) :
    s ∈ ForwardStarredSignature.signatureTree
        (fibreQStarredWord hb g fallback w) g.core.cut houtQ ↔
      s ∈ ForwardStarredSignature.signatureTree
        g.core.source g.core.cut g.core.hout := by
  rw [ForwardSignatureInteriorPersistence.mem_signatureTree_iff,
    ForwardSignatureInteriorPersistence.mem_signatureTree_iff]
  constructor
  · rintro (hi | ⟨eQ, heQ⟩)
    · exact Or.inl ((output_interior_iff hb g fallback w s).1 hi)
    · obtain ⟨e, he⟩ :=
        output_exceptional_has_source_boundary hb g fallback w houtQ eQ
      exact Or.inr ⟨e, he.symm.trans heQ⟩
  · rintro (hi | ⟨e, he⟩)
    · exact Or.inl ((output_interior_iff hb g fallback w s).2 hi)
    · obtain ⟨eQ, heQ⟩ :=
        source_boundary_has_output_exceptional hb g fallback w houtQ e
      exact Or.inr ⟨eQ, heQ.trans he⟩

private theorem output_symbol_eq_source_before_cut
    {b n l k m : Nat} {α : Type*}
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
    (s : BoundedNode b n)
    (hs : BeforeCut g.core.cut s.1) :
    ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w s =
      g.core.source.word.word s := by
  cases hf : g.ambient.word s with
  | inl a =>
      have hsource : g.core.source.word.word s = Sum.inl a := by
        rw [g.source_substitution]
        simp only [SpanAudit.substitute, hf]
      exact (ForwardQAmbientFibreSymbol.fibreQ_original_constant
        g fallback w s a hf).trans hsource.symm
  | inr u =>
      have hbefore : ForwardAux u.1.1 g.core.cut :=
        (ForwardSignatureInteriorPersistence.beforeCut_of_prefix
          (g.ambient.below u s hf) hs).1
      exact ForwardQAmbientFibreSymbol.fibreQ_before_cut
        g fallback w s u hf hbefore

private theorem output_strictPartialWord_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback) :
    strictPartialWord g.core.cut (fibreQStarredWord hb g fallback w).word =
      strictPartialWord g.core.cut g.core.source.word := by
  classical
  funext s
  by_cases hs : BeforeCut g.core.cut s.1
  · have hlabel :
        CutPreservation.underlyingSymbol (fibreQStarredWord hb g fallback w).word s =
          CutPreservation.underlyingSymbol g.core.source.word s := by
      change
        (match ForwardQAmbientFibreSymbol.fibreQSymbol g fallback w.1 s with
          | Sum.inl a => Sum.inl a
          | Sum.inr v => Sum.inr v.1) =
        (match g.core.source.word.word s with
          | Sum.inl a => Sum.inl a
          | Sum.inr v => Sum.inr v.1)
      rw [output_symbol_eq_source_before_cut g fallback w.1 s hs]
    simp only [strictPartialWord, if_pos hs, hlabel]
  · simp only [strictPartialWord, if_neg hs]

/-- Every genuine enlarged starred Q output has exactly the complete
finite-set forward signature of its source, including the rooted strict
partial word. No local Ramsey word or alphabet-size assumption is needed. -/
theorem fibreQStarredWord_sameCompleteSetForwardSignature
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput g.core fallback) :
    SameCompleteSetForwardSignature hb g
      (fibreQStarredWord hb g fallback w) g.core.cut := by
  have hcut : g.core.cut ∈
      SkewTree.interior (fibreQStarredWord hb g fallback w).tree :=
    (output_interior_iff hb g fallback w g.core.cut).2 g.core.hcut
  have hmax : ∀ t,
      t ∈ SkewTree.interior (fibreQStarredWord hb g fallback w).tree →
      SkewTree.forwardAuxB t g.core.cut = true := by
    intro t ht
    exact g.core.hmax t ((output_interior_iff hb g fallback w t).1 ht)
  let houtQ := ForwardStarredSignature.exceptionalLeaves_not_before_of_maxInterior
    hb (fibreQStarredWord hb g fallback w) g.core.cut hcut hmax
  refine ⟨hcut, hmax, ?_⟩
  change
    ((ForwardStarredSignature.signatureTree
        (fibreQStarredWord hb g fallback w) g.core.cut houtQ).toFinset,
      strictPartialWord g.core.cut (fibreQStarredWord hb g fallback w).word) =
    ((ForwardStarredSignature.signatureTree
        g.core.source g.core.cut g.core.hout).toFinset,
      strictPartialWord g.core.cut g.core.source.word)
  apply Prod.ext
  · apply Finset.ext
    intro s
    simp only [List.mem_toFinset]
    exact output_signatureTree_mem_iff hb g fallback w houtQ s
  · exact output_strictPartialWord_eq hb g fallback w

end DualTree.ForwardQFinalInducedSignature
