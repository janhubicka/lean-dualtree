import DualTree.ForwardSemiCompleteBoundary

/-!
# Source-independent corrected Definition 24 and its smooth Q pullback

The canonical map in this module is the intrinsic directional support
walk on the starred object itself. Its boundary is the first-l model
boundary, with the exceptional singleton root boundary when l = 0.
Neither the selector nor the simplicity predicate depends on a chosen
Q frame, source signature, cut, or literal marker set.

A starred object refines an ambient variable word when its tree lies
in that word's support and its evaluated word span is contained in the
ambient span. Simplicity uses precisely the three Definition 24
observations: the interior, the B2 boundary points, and the rooted word
outside the inclusive cones above those points.

For an actual forward-corrected Q frame this predicate is equivalent
to the already checked intrinsic-selector simplicity interface. The
canonical boundary is then identified with the actual D2 coordinates,
and the specific Q pullback has a total smooth extension. No separate
selector-agreement, root-law or successor-law hypothesis is supplied.

This is an explicit forward-order interpretation of Definition 24.
It does not identify it with the defective printed reverse-order Q
construction. The selector and simplicity predicate include l = 0;
the Q transfer uses frames, which necessarily have positive l.
-/

namespace DualTree.ForwardSemiCompleteSimplicity

open ForwardCanonicalPartialWalkUniqueness
open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteCanonicalRoot
open ForwardQModelBoundaryTransport
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardSourceQTree

/-- The full Definition 24 boundary depends only on b and l.
For l = 0 it consists of the empty model address. -/
abbrev Boundary (b l : Nat) :=
  ForwardSemiCompleteBoundary.Boundary b l

/-- The canonical boundary point is selected from U itself,
without any fixed source frame or source-relative marker. -/
noncomputable def canonicalPoint
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Boundary b l) : Node b :=
  canonicalWalkAll U a.1

/-- The selector used by simplicity is the actual canonical
leaf bijection. In particular its evaluations on the boundary
always follow genuine successors, even when l = 0. -/
theorem canonicalPoint_eq_leafEquiv
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Boundary b l) :
    canonicalPoint U a =
      ((ForwardSemiCompleteBoundary.boundaryLeafEquiv hb U) a).1 := rfl

/-- Each canonical point used in Definition 24 is a genuine
leaf of the arbitrary starred object U. -/
theorem canonicalPoint_is_leaf
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Boundary b l) :
    canonicalPoint U a ∈ U.tree ∧
      canonicalPoint U a ∉ SkewTree.interior U.tree :=
  ForwardSemiCompleteBoundary.boundary_is_leaf hb U a

/-- At the exceptional zero-interior boundary the canonical
point is exactly the intrinsic root of the starred support. -/
theorem canonicalPoint_zero
    {b n : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n 0 α
      (SkewTree.forwardAuxB (b := b)))
    (a : Boundary b 0) :
    canonicalPoint U a = starredRootAll U :=
  canonicalWalkAll_zero_boundary U a.1 a.2

/-- The source-facing refinement relation for a starred object
and an arbitrary ambient variable word, without Q-frame data. -/
def Refines
    {b n l : Nat} {α : Type*}
    (ambient : DualTree.VariableWord b n α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Prop :=
  (∀ t : Node b, t ∈ U.tree → t ∈ ambient.supportNodes) ∧
    U.word.span ⊆ ambient.span

/-- Corrected Definition 24 for a specified B2 subset of the
intrinsic model boundary. The complementary set is B1.
The comparison ranges over all starred refinements of ambient. -/
def SimpleWithin
    {b n l : Nat} {α γ : Type*}
    (ambient : DualTree.VariableWord b n α)
    (B2 : Set (Boundary b l))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ) : Prop :=
  ∀ (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))),
    Refines ambient U → Refines ambient V →
    (∀ t : Node b,
      t ∈ SkewTree.interior U.tree ↔
        t ∈ SkewTree.interior V.tree) →
    (∀ a : Boundary b l, a ∈ B2 →
      canonicalPoint U a = canonicalPoint V a) →
    (∀ s : BoundedNode b n,
      (∀ a : Boundary b l, a ∈ B2 →
        ¬ IsPrefix (canonicalPoint U a) s.1) →
      ForwardQSimpleLetterSmooth.rootLabel U s =
        ForwardQSimpleLetterSmooth.rootLabel V s) →
    color U = color V

/-- A simple colouring admits a partition of the canonical
boundary. This formulation remains meaningful at l = 0. -/
def Simple
    {b n l : Nat} {α γ : Type*}
    (ambient : DualTree.VariableWord b n α)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ) : Prop :=
  ∃ B2 : Set (Boundary b l), SimpleWithin ambient B2 color

/-- On any genuine source frame l is positive, and the full
Definition 24 boundary is exactly its existing model A_l. -/
def boundaryEquivModelA
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α) :
    Boundary b l ≃ ModelA c where
  toFun a := ⟨a.1,
    (definition24Boundary_pos_iff (frame_l_pos hb c) a.1).1 a.2⟩
  invFun a := ⟨a.1,
    (definition24Boundary_pos_iff (frame_l_pos hb c) a.1).2 a.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Transport only the boundary predicate to the existing
positive-l interface, preserving the underlying model address. -/
def modelB2
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (B2 : Set (Boundary b l)) : Set (ModelA c) :=
  {a | (boundaryEquivModelA hb c).symm a ∈ B2}

theorem boundary_mem_modelB2_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (B2 : Set (Boundary b l)) (a : Boundary b l) :
    (boundaryEquivModelA hb c) a ∈ modelB2 hb c B2 ↔ a ∈ B2 := by
  change (boundaryEquivModelA hb c).symm
    ((boundaryEquivModelA hb c) a) ∈ B2 ↔ a ∈ B2
  rw [Equiv.symm_apply_apply]

/-- The uniform selector agrees with the positive-interior
intrinsic selector on every U, not just on Q images. -/
theorem canonicalPoint_eq_intrinsic
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Boundary b l) :
    canonicalPoint U a =
      intrinsicModelPoint hb c U ((boundaryEquivModelA hb c) a) :=
  canonicalWalkAll_eq_positive (frame_l_pos hb c) U a.1

theorem canonicalPoint_symm_eq_intrinsic
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : ModelA c) :
    canonicalPoint U ((boundaryEquivModelA hb c).symm a) =
      intrinsicModelPoint hb c U a :=
  canonicalWalkAll_eq_positive (frame_l_pos hb c) U a.1

/-- A frame's actual ambient support has precisely the nodes T,
so the source-independent refinement relation is the old one. -/
theorem ambient_supportNodes_iff_T
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α) (t : Node b) :
    t ∈ c.ambient.supportNodes ↔ t ∈ c.core.T := by
  change t ∈ c.ambient.support.map (fun v => v.1) ↔ t ∈ c.core.T
  constructor
  · intro ht
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp ht
    exact heq ▸ (c.ambient_support_T v).1 hv
  · intro ht
    let v : BoundedNode b n := ⟨t, c.T_bounded t ht⟩
    exact List.mem_map.mpr ⟨v, (c.ambient_support_T v).2 ht, rfl⟩

theorem refines_iff_frame
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Refines c.ambient U ↔
      (∀ t : Node b, t ∈ U.tree → t ∈ c.core.T) ∧
        U.word.span ⊆ c.ambient.span := by
  constructor
  · intro h
    exact ⟨fun t ht => (ambient_supportNodes_iff_T c t).1 (h.1 t ht), h.2⟩
  · intro h
    exact ⟨fun t ht => (ambient_supportNodes_iff_T c t).2 (h.1 t ht), h.2⟩

/-- The source-independent simplicity predicate is equivalent
to the existing intrinsic-selector interface. This checks the
entire arbitrary-U domain, not only the Q-image restriction. -/
theorem simpleWithin_iff_frame
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (B2 : Set (Boundary b l))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ) :
    SimpleWithin c.ambient B2 color ↔
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (intrinsicModelPoint hb c.core)
        (fun a => a ∈ modelB2 hb c.core B2) color := by
  constructor
  · intro hs U V hU hV hinter hpoints houtside
    apply hs U V ((refines_iff_frame c U).2 hU)
      ((refines_iff_frame c V).2 hV) hinter
    · intro a ha
      rw [canonicalPoint_eq_intrinsic hb c.core U a,
        canonicalPoint_eq_intrinsic hb c.core V a]
      exact hpoints ((boundaryEquivModelA hb c.core) a)
        ((boundary_mem_modelB2_iff hb c.core B2 a).2 ha)
    · intro s hsoutside
      apply houtside s
      intro a ha
      have h := hsoutside ((boundaryEquivModelA hb c.core).symm a) ha
      rw [canonicalPoint_symm_eq_intrinsic hb c.core U a] at h
      exact h
  · intro hs U V hU hV hinter hpoints houtside
    apply hs U V ((refines_iff_frame c U).1 hU)
      ((refines_iff_frame c V).1 hV) hinter
    · intro a ha
      have h := hpoints ((boundaryEquivModelA hb c.core).symm a) ha
      rw [canonicalPoint_symm_eq_intrinsic hb c.core U a,
        canonicalPoint_symm_eq_intrinsic hb c.core V a] at h
      exact h
    · intro s hsoutside
      apply houtside s
      intro a ha
      have h := hsoutside ((boundaryEquivModelA hb c.core) a)
        ((boundary_mem_modelB2_iff hb c.core B2 a).2 ha)
      rw [canonicalPoint_eq_intrinsic hb c.core U a]
      exact h

/-- Canonical Definition 24 boundary indexing of actual D2
coordinates, including the verified A_l-to-literal-R transport. -/
noncomputable def boundaryToD2
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α) :
    Boundary b l ≃ MixedProduct.BulletIndex (kind c) :=
  (boundaryEquivModelA hb c).trans (modelAToD2 hb c)

/-- The actual smoothness partition induced by the fixed B2
subset of the source-independent canonical model boundary. -/
noncomputable def gamma1OfBoundaryB2
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (B2 : Set (Boundary b l)) :
    MixedProduct.BulletIndex (kind c) → Bool :=
  ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c
    (markerB2OfModelA hb c (modelB2 hb c B2))

theorem gamma2_iff_boundaryB2
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : Frame b n l k m α)
    (B2 : Set (Boundary b l)) (a : Boundary b l) :
    gamma1OfBoundaryB2 hb c B2 ((boundaryToD2 hb c) a) = false ↔
      a ∈ B2 := by
  change ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c
    (markerB2OfModelA hb c (modelB2 hb c B2))
    ((modelAToD2 hb c) ((boundaryEquivModelA hb c) a)) = false ↔
      a ∈ B2
  exact (ForwardQPaperSelectorReduction.modelA_B2_gamma2_iff
    hb c (modelB2 hb c B2) ((boundaryEquivModelA hb c) a)).symm.trans
    (boundary_mem_modelB2_iff hb c B2 a)

/-- On every actual corrected Q output the source-independent
selector is its true projected D2 terminal. The identification
is a theorem, not an extra premise on the source colouring. -/
theorem canonicalPoint_actual_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : Boundary b l) :
    canonicalPoint (fibreQStarredWord hb c fallback w) a =
      (markedProjection c.core
        (ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1)
        ((boundaryToD2 hb c.core) a)).1 := by
  rw [canonicalPoint_eq_intrinsic hb c.core]
  exact (intrinsicModelPoint_Qlocal hb c fallback w _).trans
    (canonicalModelATerminal_actual_Q hb c fallback w _)

/-- A colouring simple in the explicit corrected Definition 24
sense induces a smooth Q pullback on the true starred subtype. -/
theorem simpleWithin_Q_pullback_smooth
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (B2 : Set (Boundary b l))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : SimpleWithin c.ambient B2 color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (gamma1OfBoundaryB2 hb c.core B2) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) :=
  intrinsic_simple_Q_pullback_smooth hb c fallback
    (modelB2 hb c.core B2) color
    ((simpleWithin_iff_frame hb c B2 color).1 hsimple) x y hxy

/-- The specific Q pullback of a simple colouring extends to a
total smooth colouring of the whole enlarged mixed product.
No selector-agreement or Q-local recursion premise remains. -/
theorem exists_total_simpleWithin_Q_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (B2 : Set (Boundary b l))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : SimpleWithin c.ambient B2 color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (gamma1OfBoundaryB2 hb c.core B2) x y → total x = total y) :=
  exists_total_intrinsic_simple_Q_pullback hb c fallback fallbackColor
    (modelB2 hb c.core B2) color
    ((simpleWithin_iff_frame hb c B2 color).1 hsimple)

/-- Corrected Definition 24 simplicity, with its partition
existentially quantified, yields the required partition and
total smooth colouring. This conclusion supplies no Ramsey
word and makes no constancy claim for retained Gamma1 letters. -/
theorem simple_exists_total_smooth_Q_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b) (c : FibreFrame b n l k m α)
    (fallback : α) (fallbackColor : γ)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : Simple c.ambient color) :
    ∃ gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool,
      ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
        (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback,
          total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
        (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
          MixedProduct.SmoothRelated gamma1 x y → total x = total y) := by
  obtain ⟨B2, hB2⟩ := hsimple
  exact ⟨gamma1OfBoundaryB2 hb c.core B2,
    exists_total_simpleWithin_Q_pullback hb c fallback fallbackColor B2 color hB2⟩

end DualTree.ForwardSemiCompleteSimplicity
