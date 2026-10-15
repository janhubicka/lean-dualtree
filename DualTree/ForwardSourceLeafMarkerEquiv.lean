import DualTree.ForwardSourceCutLeaves
import DualTree.ForwardSourceExceptionalMarkers
import DualTree.ForwardQLiteralSkeletonMeets

/-!
# The literal corrected source markers R are exactly the source leaves

The repaired Lemma 27 construction uses two families of literal
source markers: immediate ambient children of the final interior
cut, and first-exit boundaries of exceptional source leaves.

The preceding source-facing theorems establish both families'
validity. Here we combine them without an arbitrary leaf order:

* Every literal R marker is a prefix of an actual source terminal.
  For an exceptional marker this follows from its defining leaf;
  for a cut-child marker it follows from the unique cut successor.
* No R marker can prefix two distinct source terminals: their
  source-supported ambient meet would be an interior node below
  an R boundary, contradicting the last interior cut.
* Every source terminal has an R marker on its path: below the
  cut take its first ambient cut-child direction; otherwise use
  its actual exceptional first-exit boundary.
* R is an antichain, so no terminal can have two different
  R markers on its path.

These existence and uniqueness statements produce a canonical
choice-independent equivalence SourceLeaf(S) ≃ R, preserving the
actual ambient prefix incidence.

This does NOT yet identify the first-l homogeneous model boundary
A_l with the leaves of S. That requires the missing canonical
direction-address map. No mixed-product span or Ramsey result
is inferred here.
-/

namespace DualTree.ForwardSourceLeafMarkerEquiv

open ForwardSourceQTree

/-- Actual source leaves, rather than arbitrary terminal positions
in the complete enclosing support T. -/
abbrev SourceLeaf
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {t : Node b //
    t ∈ c.source.tree ∧
    t ∉ SkewTree.interior c.source.tree}

/-- The ACTUAL corrected literal signature marker set R. -/
abbrev Marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardSortedMixedProduct.Marker c.source c.cut c.hout

/-- A literal R marker can lie below AT MOST ONE original
source terminal. Otherwise two source terminals sharing that
boundary would have a supported interior meet outside the cut. -/
theorem marker_prefix_source_leaf_unique
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Marker c)
    (t u : SourceLeaf c)
    (hrt : IsPrefix r.1 t.1)
    (hru : IsPrefix r.1 u.1) :
    t = u := by
  by_cases hval : t.1 = u.1
  · exact Subtype.ext hval
  let w : Node b := MeetGeometry.commonPrefix t.1 u.1
  have hwS : w ∈ c.source.tree :=
    (ForwardQLiteralSkeletonMeets.source_meetClosed c)
      t.1 u.1 t.2.1 u.2.1
  have hwt : IsPrefix w t.1 :=
    MeetGeometry.commonPrefix_prefix_left t.1 u.1
  have hwu : IsPrefix w u.1 :=
    MeetGeometry.commonPrefix_prefix_right t.1 u.1
  have hwnot : w ≠ t.1 := by
    intro heq
    have htu : IsPrefix t.1 u.1 := by
      rw [← heq]
      exact hwu
    exact t.2.2
      (SignatureInteriorPersistence.interior_of_strict_descendant
        c.source.tree t.1 u.1 t.2.1 u.2.1 ⟨htu, hval⟩)
  have hwInterior : w ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree w t.1 hwS t.2.1 ⟨hwt, hwnot⟩
  have hrw : IsPrefix r.1 w :=
    MeetGeometry.prefix_commonPrefix hrt hru
  exact (ForwardQLiteralSkeletonMeets.literalR_not_prefix_interior
    c r.1 r.2 w hwInterior hrw).elim

/-- Every actual R marker has a source-terminal descendant:
exceptional first-exit markers use their originating source
leaf; cut-child markers use the verified unique cut successor. -/
theorem marker_has_source_leaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (r : Marker c) :
    ∃ t : SourceLeaf c, IsPrefix r.1 t.1 := by
  have hrParts :
      r.1 ∈ ForwardStarredSignature.signatureTerminalMarkers
          c.source c.cut c.hout ++
        (SkewTree.allFin b).map (fun i => c.cut ++ [i]) := by
    have hr : r.1 ∈ ForwardStarredSignature.literalR
        c.source c.cut c.hout := r.2
    simpa [ForwardStarredSignature.literalR] using hr
  rcases List.mem_append.mp hrParts with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
        c.source c.cut c.hcut c.hmax c.hout r.1 hterminal
    have hspec :=
      StarredSignature.exceptionalLeaves_spec
        c.source c.cut t.1 t.2
    refine ⟨⟨t.1, ⟨hspec.1, hspec.2.1⟩⟩, ?_⟩
    rw [← ht]
    exact (ForwardSignatureBoundary.firstBoundary_spec
      c.cut t.1 (c.hout t.1 t.2)).1
  · rcases List.mem_map.mp hchild with ⟨i, _hi, hir⟩
    refine ⟨⟨ForwardSourceCutLeaves.cutLeaf c i,
      ⟨ForwardSourceCutLeaves.cutLeaf_mem c i,
       ForwardSourceCutLeaves.cutLeaf_terminal hb c i⟩⟩, ?_⟩
    rw [← hir]
    exact ForwardSourceCutLeaves.cutLeaf_cone c i

/-- Every original terminal lies above an actual literal R
marker. A leaf below cut has a unique first cut-child
direction; all other leaves belong to the exceptional family. -/
theorem source_leaf_has_marker
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : SourceLeaf c) :
    ∃ r : Marker c, IsPrefix r.1 t.1 := by
  by_cases hcut : IsPrefix c.cut t.1
  · rcases hcut with ⟨tail, htail⟩
    cases tail with
    | nil =>
        have htEq : t.1 = c.cut := by
          simpa using htail
        have htInterior : t.1 ∈
            SkewTree.interior c.source.tree := by
          rw [htEq]
          exact c.hcut
        exact (t.2.2 htInterior).elim
    | cons i rest =>
        have hr : c.cut ++ [i] ∈
            ForwardStarredSignature.literalR
              c.source c.cut c.hout :=
          ForwardStarredSignature.cut_child_mem_literalR
            c.source c.cut c.hout i
        refine ⟨⟨c.cut ++ [i], hr⟩, ?_⟩
        exact ⟨rest, by simpa [List.append_assoc] using htail⟩
  · have hexc : t.1 ∈
        StarredSignature.exceptionalLeaves c.source c.cut := by
      classical
      unfold StarredSignature.exceptionalLeaves
      apply List.mem_filter.mpr
      refine ⟨t.2.1, ?_⟩
      simp [t.2.2, hcut]
    let e : ForwardSourceExceptionalMarkers.Exceptional c :=
      ⟨t.1, hexc⟩
    refine ⟨⟨ForwardSourceExceptionalMarkers.exceptionalBoundary c e,
      ForwardSourceExceptionalMarkers.exceptionalBoundary_mem_literalR
        c e⟩, ?_⟩
    exact ForwardSourceExceptionalMarkers.exceptionalBoundary_prefix c e

/-- No source terminal is above two different literal R
markers, since the corrected first-exit boundaries form a
genuine ambient prefix antichain. -/
theorem source_leaf_prefix_marker_unique
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : SourceLeaf c)
    (r s : Marker c)
    (hrt : IsPrefix r.1 t.1)
    (hst : IsPrefix s.1 t.1) :
    r = s := by
  apply Subtype.ext
  rcases le_total r.1.length s.1.length with hle | hle
  · exact ForwardQLiteralSkeletonMeets.literalR_antichain
      c r.1 s.1 r.2 s.2
      (CutFrontier.prefix_of_prefix_length_le hrt hst hle)
  · exact (ForwardQLiteralSkeletonMeets.literalR_antichain
      c s.1 r.1 s.2 r.2
      (CutFrontier.prefix_of_prefix_length_le hst hrt hle)).symm

/-- The genuine source leaves and corrected literal R markers
have a CANONICAL correspondence characterized by prefix
incidence in the source. Both inverse maps are forced by
existence and uniqueness, independent of any list order. -/
noncomputable def sourceLeafMarkerEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    SourceLeaf c ≃ Marker c := by
  classical
  let F : SourceLeaf c → Marker c :=
    fun t => Classical.choose (source_leaf_has_marker c t)
  let G : Marker c → SourceLeaf c :=
    fun r => Classical.choose (marker_has_source_leaf hb c r)
  have hF : ∀ t : SourceLeaf c, IsPrefix (F t).1 t.1 :=
    fun t => Classical.choose_spec (source_leaf_has_marker c t)
  have hG : ∀ r : Marker c, IsPrefix r.1 (G r).1 :=
    fun r => Classical.choose_spec (marker_has_source_leaf hb c r)
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
  }
  · intro t
    exact marker_prefix_source_leaf_unique
      c (F t) (G (F t)) t (hG (F t)) (hF t)
  · intro r
    exact source_leaf_prefix_marker_unique
      c (G r) (F (G r)) r (hF (G r)) (hG r)

end DualTree.ForwardSourceLeafMarkerEquiv
