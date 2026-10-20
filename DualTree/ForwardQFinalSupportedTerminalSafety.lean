import DualTree.ForwardQFinalPositiveQWordPreimage
import DualTree.ForwardQFinalHeightBudget
import DualTree.FullBeforeSignature

/-!
# The actual final support bounds the target's terminal addresses

The safety obstruction for corrected Q terminals is resolved whenever
the requested target starred tree is supported on the CONSTRUCTED
rank-filtered final support T'_M, as it should be when representing
a starred structure in the final ambient refinement.

First, every leaf of a genuine forward semi-complete starred tree
lies strictly after its maximal interior cut in the corrected
forward auxiliary order. Second, every T'_M vertex after that cut
is one of the selected genuine projected local roots, hence has
an actual safe shortened address.

Together, equality of actual complete signatures (which supplies
the matching maximal cut) and inclusion O.tree ⊆ T'_M imply that
EVERY terminal of O.tree has a safe local address.

This is not an unqualified statement about the word-only condition
O.word.span ⊆ f'.span. The support inclusion O.tree ⊆ T'_M is an
explicit independent geometric premise, and the precise D2 marker
labels, local marker-span membership, and corrected D2 order still
have to be reconstructed.
-/

namespace DualTree.ForwardQFinalSupportedTerminalSafety

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalFullSignature

/-- In positive arity, a terminal of an ACTUAL forward-starred
semi-complete tree cannot precede its maximal interior cut. This
also covers early side leaves which do not descend from the cut. -/
theorem terminal_after_maximal_interior_cut
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ¬ ForwardAux t cut := by
  have hfull :
      SkewTree.fullBeforeB SkewTree.forwardAuxB O.tree cut = true :=
    StarredSignature.fullBefore_at_maxInterior O cut hcut hmax
  have hleaf : SkewTree.immediateSuccs O.tree t = [] :=
    StarredSignature.immediateSuccs_nil_of_not_interior
      O.tree t ht hterminal
  have hneq : t ≠ cut := by
    intro h
    subst t
    exact hterminal hcut
  have hnot :=
    StarredSignature.leaf_not_before_of_fullBefore
      hb O.tree SkewTree.forwardAuxB cut t hfull ht hleaf hneq
  intro hbefore
  exact hnot (by simpa [SkewTree.forwardAuxB] using hbefore)

/-- Every vertex of the exact height-budgeted support T'_M
strictly after the inclusive cut belongs to the SELECTED safe
projection image and has a genuine local shortened address. -/
theorem final_support_after_cut_has_safe_address
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (t : Node b)
    (ht : t ∈ finalBudgetSupport c f (m + q))
    (hafter : ¬ ForwardAux t c.cut) :
    ∃ a : LocalAddress c,
      ForwardQFinalSafeAddressLookup.safeAddress c t = some a := by
  classical
  change t ∈ retained c ∪ selectedProjectedRoots c f (m + q) at ht
  rcases Finset.mem_union.mp ht with hret | hselected
  · exact False.elim (hafter (Finset.mem_filter.mp hret).2)
  · obtain ⟨a, ha, hprojected⟩ := Finset.mem_image.mp hselected
    refine ⟨a, ?_⟩
    rw [← hprojected]
    exact ForwardQFinalSafeAddressLookup.safeAddress_projected c a

/-- Under the true same-complete-signature hypothesis and inclusion
of the requested target's ENTIRE tree in the selected final ambient
support, every output terminal has a safe shortened projected address.

The target's terminal must subsequently be matched to the correct
literal R/D2 marker and its inverse local point must belong to the
local Ramsey variable support, with legal corrected starred order. -/
theorem supported_output_terminals_have_safe_addresses
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : SameCompleteForwardSignature hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ finalBudgetSupport g.core f (m + q))
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ a : LocalAddress g.core,
      ForwardQFinalSafeAddressLookup.safeAddress
        g.core t = some a := by
  have hafterO : ¬ ForwardAux t cutO :=
    terminal_after_maximal_interior_cut
      hb O cutO H.cutInterior H.cutMaximal t ht hterminal
  have hcut : cutO = g.core.cut :=
    complete_signature_forces_same_cut hb g O cutO H
  have hafter : ¬ ForwardAux t g.core.cut := by
    simpa only [hcut] using hafterO
  exact final_support_after_cut_has_safe_address
    g.core f t (hSupport t ht) hafter

end DualTree.ForwardQFinalSupportedTerminalSafety
