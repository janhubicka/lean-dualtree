import DualTree.ZeroInteriorRelative

/-!
# Exact identification of the zero-interior one-root Ramsey target

The corrected canonical Ramsey proposition at interior count zero and
target height one is logically equivalent, at EACH fixed ambient height,
to the ordinary tree-word one-root Ramsey proposition. This is sharper
than the already proved implication from ground Ramsey to the canonical
starred case: the converse uses real pointed starred objects in the
chosen complete word, not an empty-domain shortcut.

The alphabet and colour types are assumed inhabited only for the reverse
bridge's supplied witnesses, and no two-letter hypothesis is imposed.
The eventual bound predicates are therefore equivalent with exactly the
same threshold, for positive Fin alphabet and colour sizes.

The equivalence neither proves arbitrary target height nor the relative
ground-word Ramsey hypothesis isolated by ZeroInteriorRelative.
-/

namespace DualTree.ZeroInteriorGroundEquivalence

open CorrectedTheoremSpec

/-- Ordinary ground-word one-root Ramsey at a fixed ambient height. -/
def GroundOneAt (b n : Nat) (α γ : Type*) : Prop :=
  ∀ c : TreeWord b n α → γ,
    ∃ f : Word b n 1 α, ∃ col : γ,
      ∀ w : TreeWord b n α, w ∈ f.span → c w = col

/-- Forgetting the marked vertex defines a globally simple semantic
zero-interior colour, with empty selected canonical boundary. -/
theorem groundColour_simpleWith_empty
    {b n : Nat} {α γ : Type*}
    (fallback : α) (c : TreeWord b n α → γ) :
    CanonicalTheoremSpec.SimpleWith
      (l := 0) (∅ : Set (CanonicalTheoremSpec.Boundary b 0))
      (fun O => c (ZeroInteriorRelative.groundOfObservation fallback O)) := by
  intro U V _ _ hword
  apply congrArg c
  funext s
  change (match CutPreservation.underlyingSymbol U.word s with
    | Sum.inl a => a
    | Sum.inr _ => fallback) =
    (match CutPreservation.underlyingSymbol V.word s with
    | Sum.inl a => a
    | Sum.inr _ => fallback)
  rw [hword s (by intro a ha; exact False.elim ha)]

/-- The reverse direction of the zero-interior bridge: every ordinary
ground colouring is already a globally simple starred colouring after
forgetting its marked point, and its monochromatic complete-word witness
yields a nonempty homogeneous ground span. -/
theorem groundOneAt_of_canonicalRamseyAt
    {b n : Nat} {α γ : Type*}
    (fallback : α)
    (h : CanonicalTheoremSpec.RamseyAt b n 0 1 α γ) :
    GroundOneAt b n α γ := by
  intro c
  let color : StarredObservation b n α → γ :=
    fun O => c (ZeroInteriorRelative.groundOfObservation fallback O)
  obtain ⟨f, hmono⟩ := h color
    ⟨∅, groundColour_simpleWith_empty fallback c⟩
  obtain ⟨p, hp⟩ := ZeroInteriorRamsey.exists_support_root f
  let w₀ : TreeWord b n α := f.toVariableWord.eval (fun _ => fallback)
  have hw₀ : w₀ ∈ f.span := ⟨fun _ => fallback, rfl⟩
  refine ⟨f, c w₀, ?_⟩
  intro w hw
  have hW : StarredBelow (ZeroInteriorRamsey.pointedStarred w p) f :=
    (ZeroInteriorRamsey.pointedStarred_below_iff w p f).2 ⟨hw, hp⟩
  have hW₀ : StarredBelow (ZeroInteriorRamsey.pointedStarred w₀ p) f :=
    (ZeroInteriorRamsey.pointedStarred_below_iff w₀ p f).2 ⟨hw₀, hp⟩
  have hc := hmono
    (ZeroInteriorRamsey.pointedStarred w p)
    (ZeroInteriorRamsey.pointedStarred w₀ p) hW hW₀
  change c (ZeroInteriorRelative.groundOfObservation fallback
      (starredObserve (ZeroInteriorRamsey.pointedStarred w p))) =
    c (ZeroInteriorRelative.groundOfObservation fallback
      (starredObserve (ZeroInteriorRamsey.pointedStarred w₀ p))) at hc
  simpa only [ZeroInteriorRamsey.pointedStarred_observe,
    ZeroInteriorRelative.groundOfObservation_pointObservation] using hc

/-- The corrected zero-interior target is PRECISELY ordinary one-root
ground-word Ramsey at the same ambient height. No change of parameters
or threshold is needed, including for a unary alphabet. -/
theorem canonicalRamseyAt_zero_one_iff_ground
    {b n : Nat} {α γ : Type*}
    (fallback : α) (fallbackColor : γ) :
    CanonicalTheoremSpec.RamseyAt b n 0 1 α γ ↔
      GroundOneAt b n α γ := by
  constructor
  · exact groundOneAt_of_canonicalRamseyAt fallback
  · intro hg
    exact (ZeroInteriorRamsey.positive_ramseyAt_zero_one_of_ground_word_ramsey
      fallback fallbackColor hg).2

/-- Equivalence of the ACTUAL positive eventual bound predicates, not just
existence at one ambient height. The numerical Ramsey thresholds agree
exactly for zero interior and target one. -/
theorem canonicalBound_zero_one_iff_ground
    {b ell r N : Nat} (hell : 0 < ell) (hr : 0 < r) :
    CanonicalTheoremSpec.Bound b ell 0 1 r N ↔
      EventualBound (fun n =>
        GroundOneAt b n (Fin ell) (Fin r)) N := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro n hn
    exact (canonicalRamseyAt_zero_one_iff_ground
      (⟨0, hell⟩ : Fin ell) (⟨0, hr⟩ : Fin r)).1 (h.2 n hn)
  · intro h
    refine ⟨h.1, ?_⟩
    intro n hn
    exact (canonicalRamseyAt_zero_one_iff_ground
      (⟨0, hell⟩ : Fin ell) (⟨0, hr⟩ : Fin r)).2 (h.2 n hn)

end DualTree.ZeroInteriorGroundEquivalence
