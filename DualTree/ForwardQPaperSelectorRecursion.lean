import DualTree.ForwardSemiCompleteCanonicalRoot

/-!
# Exact root-and-successor criterion for the published I_U on Q images

The published Definition 24 uses a semi-complete canonical map
I_U(a), without defining its partial support-tree recursion in
the same explicit way as the earlier complete-tree I_T.

We have now kernel-checked the intrinsic rooted directional walk
on every positive-interior semi-complete starred support U, its
uniqueness on the first-l model, and its exact Q/D2 values.
This module packages the weakest remaining *operational* bridge
to the paper's original arbitrary-U selector.

Let paperMap U : Node b → Node b be ANY proposed partial-model
canonical map. The paper's simplicity condition still ranges
over ALL starred U,V. The proof only needs the two local
canonical laws AT ACTUAL FINISHED Q OUTPUTS:
  * paperMap Q [] = the unique intrinsic root of Q;
  * paperMap Q (p++[i]) = next_Q (paperMap Q p) i
    for every first-l model interior p.

By finite model boundary rigidity these laws force
paperMap Q(a) to agree with the checked intrinsic selector
for every genuine model boundary a; by the verified corrected-Q
geometry this is the corresponding actual projected D2 point.
The full colouring pullback and TOTAL smooth extension follow
without assuming the equality of two unrelated selectors.

The root/step laws of the paper's not-explicitly-defined I_U
are NOT claimed to be proved from the printed text. This file
gives the exact finite verification criterion that a corrected
Definition 24 should state. It does not repair the reverse
auxiliary-order W_* domain, mixed spans/Hall or Ramsey induction.
-/

namespace DualTree.ForwardQPaperSelectorRecursion

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQModelBoundaryTransport
open ForwardSemiCompleteCanonicalRoot
open ForwardModelBoundaryHeap

/-- Any proposed map with the intrinsic root and outgoing
support-successor recursion on a finished Q word must choose
the actual Q projected terminal at each Definition 24 A_l
boundary address. No assumption about its values on arbitrary
non-Q starred words is made. -/
theorem paperMap_Qlocal_of_root_successors
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (paperMap :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) →
      Node b → Node b)
    (hrootQ :
      ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        paperMap (fibreQStarredWord hb c fallback w) [] =
          starredRoot (frame_l_pos hb c.core)
            (fibreQStarredWord hb c fallback w))
    (hstepQ :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (p : Node b) (i : Fin b),
        ModelInterior l p →
        paperMap (fibreQStarredWord hb c fallback w) (p ++ [i]) =
          CanonicalSupportWalk.next
            (fibreQStarredWord hb c fallback w).tree
            (paperMap (fibreQStarredWord hb c fallback w) p) i)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : ModelA c.core) :
    paperMap (fibreQStarredWord hb c fallback w) a.1 =
      canonicalModelATerminal hb c.core
        (fibreQStarredWord hb c fallback w) a := by
  let U := fibreQStarredWord hb c fallback w
  have hboundary :
      ForwardCanonicalPartialWalkUniqueness.Definition24Boundary
        l a.1 :=
    (ForwardCanonicalPartialWalkUniqueness.definition24Boundary_pos_iff
      (frame_l_pos hb c.core) a.1).2 a.2
  have hwalk :=
    intrinsic_boundary_rigidity hb
      (frame_l_pos hb c.core) U
      (paperMap U) (hrootQ w)
      (hstepQ w) a.1 hboundary
  calc
    paperMap U a.1 =
        CanonicalSupportWalk.walk U.tree
          (starredRoot (frame_l_pos hb c.core) U) a.1 := hwalk
    _ = intrinsicModelPoint hb c.core U a := rfl
    _ = canonicalModelATerminal hb c.core U a :=
      intrinsicModelPoint_Qlocal hb c fallback w a

/-- The original ALL-U simplicity hypothesis, together with
only Q-local root/step laws for its selector, implies smoothness
of the complete actual Q colouring pullback. -/
theorem paper_simple_smooth_of_Q_root_successors
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (paperMap :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) →
      Node b → Node b)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (fun U a => paperMap U a.1)
        (fun a => a ∈ B2) color)
    (hrootQ :
      ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        paperMap (fibreQStarredWord hb c fallback w) [] =
          starredRoot (frame_l_pos hb c.core)
            (fibreQStarredWord hb c fallback w))
    (hstepQ :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (p : Node b) (i : Fin b),
        ModelInterior l p →
        paperMap (fibreQStarredWord hb c fallback w) (p ++ [i]) =
          CanonicalSupportWalk.next
            (fibreQStarredWord hb c fallback w).tree
            (paperMap (fibreQStarredWord hb c fallback w) p) i)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2)) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  exact
    ForwardQPaperSelectorReduction.paper_simple_Q_pullback_smooth_of_local_agreement
      hb c fallback
      (fun U a => paperMap U a.1) B2 color hsimple
      (fun w a =>
        paperMap_Qlocal_of_root_successors hb c fallback
          paperMap hrootQ hstepQ w a)
      x y hxy

/-- The same Q-local root/step verification criterion gives the
TOTAL smooth extension on the enlarged mixed-word product. -/
theorem exists_total_paper_simple_of_Q_root_successors
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (paperMap :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) →
      Node b → Node b)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (fun U a => paperMap U a.1)
        (fun a => a ∈ B2) color)
    (hrootQ :
      ∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        paperMap (fibreQStarredWord hb c fallback w) [] =
          starredRoot (frame_l_pos hb c.core)
            (fibreQStarredWord hb c fallback w))
    (hstepQ :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (p : Node b) (i : Fin b),
        ModelInterior l p →
        paperMap (fibreQStarredWord hb c fallback w) (p ++ [i]) =
          CanonicalSupportWalk.next
            (fibreQStarredWord hb c fallback w).tree
            (paperMap (fibreQStarredWord hb c fallback w) p) i) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
            (markerB2OfModelA hb c.core B2))
          x y → total x = total y) := by
  exact
    ForwardQPaperSelectorReduction.exists_total_paper_simple_Q_pullback_of_local_agreement
      hb c fallback fallbackColor
      (fun U a => paperMap U a.1)
      B2 color hsimple
      (fun w a =>
        paperMap_Qlocal_of_root_successors hb c fallback
          paperMap hrootQ hstepQ w a)

end DualTree.ForwardQPaperSelectorRecursion
