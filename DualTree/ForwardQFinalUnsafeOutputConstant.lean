import DualTree.ForwardQFinalSafeRootAgreement
import DualTree.ForwardQFinalGlobalFibreSubstitution

/-!
# Output constants at unsafe late original ambient-f roots

The exact final rank-filtered support consists of the retained
inclusive-cut vertices and selected genuine shortened projections.
Therefore a post-cut original f-variable root with no safe local
projection address cannot be a selected final variable root.

The interpolated ambient word f' uses its explicit fallback letter
at such a root. By the verified two-letter span/constant-preservation
lemma, every output O whose evaluated span refines f' must have the
SAME literal constant at that root.

This isolates the remaining, genuinely geometric, Q-side obligation:
the actual Q sampler must likewise fall back if a selected frontier
exists but the inverse local tail is outside the safe shortened domain.
It does not claim whole-word or starred-object Q equality.
-/

namespace DualTree.ForwardQFinalUnsafeOutputConstant

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution

/-- A late ambient-f root outside the ACTUAL safe projected-coordinate
image does not belong to the final rank-budgeted variable-root set. -/
theorem unsafe_late_root_not_final_support
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hunsafe : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = none) :
    u.1.1 ∉ finalBudgetSupport g.core f (m+q) := by
  classical
  intro hmem
  change u.1.1 ∈ ForwardQFinalSupportCut.retained g.core ∪
    selectedProjectedRoots g.core f (m+q) at hmem
  rcases Finset.mem_union.mp hmem with hret | hproj
  · exact hafter (Finset.mem_filter.mp hret).2
  · obtain ⟨a, ha, hroot⟩ := Finset.mem_image.mp hproj
    have hsome :
        ForwardQFinalSafeAddressLookup.safeAddress
          g.core u.1.1 = some a := by
      rw [← hroot]
      exact ForwardQFinalSafeAddressLookup.safeAddress_projected g.core a
    rw [hunsafe] at hsome
    cases hsome

/-- The actual interpolated final ambient word f' has a literal
fallback constant at EVERY late f-root absent from the safe local
projection domain, independent of the local mixed variable word. -/
theorem unsafe_late_interpolated_word_constant
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α)
    (fallback : α)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hunsafe : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = none) :
    (interpolatedFinalWord g f decode fallback).word u.1 =
      Sum.inl fallback := by
  have hnotRoot : u.1 ∉ boundedFinalRoots g f := by
    intro hmem
    exact (unsafe_late_root_not_final_support
      g f u hafter hunsafe)
      ((mem_boundedFinalRoots_iff g f u.1).1 hmem)
  change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f decode fallback) u.1 =
        Sum.inl fallback
  simp [SpanAudit.substitute, g.ambient.atRoot u,
    globalRootSymbol, hunsafe, hnotRoot]

/-- Over an alphabet containing two distinct letters, evaluated
span inclusion forces the starred output to retain that literal
fallback constant at every unsafe late original ambient-f root. -/
theorem unsafe_late_output_word_constant
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (interpolatedFinalWord g f (fun x : α => x) fallback).span)
    (u : g.ambient.Vars)
    (hafter : ¬ ForwardAux u.1.1 g.core.cut)
    (hunsafe : ForwardQFinalSafeAddressLookup.safeAddress
      g.core u.1.1 = none) :
    O.word.word u.1 = Sum.inl fallback := by
  exact SpanAudit.constant_preserved_of_span_subset
    hα
    (interpolatedFinalWord g f (fun x : α => x) fallback).word
    O.word.word
    hspan
    (unsafe_late_interpolated_word_constant
      g f (fun x : α => x) fallback u hafter hunsafe)

end DualTree.ForwardQFinalUnsafeOutputConstant
