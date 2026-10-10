import DualTree.ForwardQSourceTerminals
import DualTree.CanonicalForwardAuxIso

/-!
# No branching after the retained maximal cut in corrected Q

The genuine forward-corrected Q construction retains the original
interior as fixed base and adds only terminal D₂ cone projections.
Consequently every Q interior node was an interior of the original
source. By maximality of the distinguished source cut, all such
interior vertices lie at or before cut in the forward auxiliary order.

Because this order is antisymmetric, any Q support vertex strictly
after cut must be terminal. This is exactly the executable
`emptyAfterB` conjunct from skew clause (iv).

The argument needs no assumption that Q is already rooted,
meet-closed or semi-complete skew, and works independently of
the positive-branching condition required to show *cut itself*
remains interior.
-/

namespace DualTree.ForwardQFinalCutOrder

open ForwardSourceQTree

/-- Every actual interior vertex of corrected Q belongs to
the inclusive forward auxiliary initial segment at cut. -/
theorem Q_interior_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior (nodes c x).toList) :
    ForwardAux s c.cut := by
  have hsOld :=
    ForwardQSourceTerminals.Q_interior_subset_original c x s hs
  simpa [SkewTree.forwardAuxB] using c.hmax s hsOld

/-- The *actual reconstructed* Q node set satisfies the
empty-after half of the final skew branching-witness condition. -/
theorem Q_emptyAfterB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.emptyAfterB SkewTree.forwardAuxB
      (nodes c x).toList c.cut = true := by
  let W := nodes c x
  unfold SkewTree.emptyAfterB
  apply List.all_eq_true.mpr
  intro s hs
  change (if SkewTree.forwardAuxB c.cut s && !(s == c.cut)
    then (SkewTree.immediateSuccs W.toList s).isEmpty
    else true) = true
  split_ifs with hcase
  · have hh := hcase
    simp only [Bool.and_eq_true] at hh
    have hafter : ForwardAux c.cut s := by
      simpa [SkewTree.forwardAuxB] using hh.1
    have hne : s ≠ c.cut := by
      intro heq
      subst s
      simp at hcase
    by_cases hterminal :
        (SkewTree.immediateSuccs W.toList s).isEmpty = true
    · exact hterminal
    · have hsInterior : s ∈ SkewTree.interior W.toList := by
        unfold SkewTree.interior
        apply List.mem_filter.mpr
        refine ⟨hs, ?_⟩
        cases hsucc : SkewTree.immediateSuccs W.toList s with
        | nil =>
            simp [hsucc] at hterminal
        | cons u us =>
            simp [hsucc]
      have hbefore : ForwardAux s c.cut :=
        Q_interior_before_cut c x s hsInterior
      have heq : c.cut = s :=
        CanonicalForwardAuxIso.forwardAux_antisymm hafter hbefore
      exact False.elim (hne heq.symm)
  · rfl

end DualTree.ForwardQFinalCutOrder
