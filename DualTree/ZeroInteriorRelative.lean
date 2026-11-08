import DualTree.ZeroInteriorRamsey

/-!
# The exact relative zero-interior, one-root induction obligation

For the corrected syntactic notion of refinement, relative starred Ramsey
at interior count zero and target height one is EQUIVALENT to ordinary
relative ground-word Ramsey inside the prescribed complete source word.

The reverse direction is substantive: any ground-word colour is lifted to
a simple semantic starred colour by ignoring the marked point and replacing
any variable symbols by a fixed alphabet letter.  The resulting starred
witness gives a genuinely nonempty ground-word span via an actual support
root and the proved pointed-starred eligibility equivalence.

For the forward direction, an empty selected boundary is reduced to a
single fixed pointed constant observation, using *relative* simplicity.
A nonempty selected boundary already has an actual one-root syntactic
refinement by root masking, independently of the ground-word Ramsey input.

This is a reduction, not a proof that relative ground-word Ramsey always
holds: the latter remains the height-dependent input for Theorem 25.
-/

namespace DualTree.ZeroInteriorRelative

open CorrectedTheoremSpec

/-- The ordinary relative scalar tree-word Ramsey input at one root.
Both the source and chosen target have the same ambient height. -/
def RelativeGroundOne
    {b n k : Nat} {α γ : Type*} (f : Word b n k α) : Prop :=
  ∀ c : TreeWord b n α → γ,
    ∃ g : Word b n 1 α,
      KVariableWord.SyntacticRefines g f ∧
      ∀ u v : TreeWord b n α, u ∈ g.span → v ∈ g.span → c u = c v

/-- Turn a semantic rooted-word observation into an ordinary ground word.
This total projection is needed only when its input has variable symbols. -/
def groundOfObservation
    {b n : Nat} {α : Type*} (fallback : α)
    (O : StarredObservation b n α) : TreeWord b n α :=
  fun s => match O.2 s with
    | Sum.inl a => a
    | Sum.inr _ => fallback

/-- Zero interior has no variables, so the projection is exact. -/
theorem groundOfObservation_starredObserve
    {b n : Nat} {α : Type*} (fallback : α)
    (U : Starred b n 0 α) :
    groundOfObservation fallback (starredObserve U) =
      ZeroInteriorRamsey.constantWord U := by
  funext s
  change (match CutPreservation.underlyingSymbol U.word s with
    | Sum.inl a => a
    | Sum.inr _ => fallback) = ZeroInteriorRamsey.constantWord U s
  rw [ZeroInteriorRamsey.underlyingSymbol_eq_constant U s]

theorem groundOfObservation_pointObservation
    {b n : Nat} {α : Type*} (fallback : α)
    (w : TreeWord b n α) (p : Node b) :
    groundOfObservation fallback
      (ZeroInteriorRamsey.pointObservation w p) = w := by
  funext s
  rfl

/-- Every ground colour lifts to a relatively simple semantic colour with
empty selected boundary. This does not require a two-letter alphabet. -/
theorem groundColour_simpleWithin
    {b n k : Nat} {α γ : Type*}
    (f : Word b n k α) (fallback : α)
    (c : TreeWord b n α → γ) :
    Theorem25.SimpleWithin
      (l := 0) ForwardSemiCompleteSimplicity.canonicalPoint
      (fun O => c (groundOfObservation fallback O)) f := by
  refine ⟨∅, ?_⟩
  intro U V _ _ _ _ hword
  apply congrArg c
  funext s
  change (match CutPreservation.underlyingSymbol U.word s with
    | Sum.inl a => a
    | Sum.inr _ => fallback) =
    (match CutPreservation.underlyingSymbol V.word s with
    | Sum.inl a => a
    | Sum.inr _ => fallback)
  rw [hword s (by intro a ha; exact False.elim ha)]

/-- Relative simplicity with empty selected boundary lets us move the
marked support point, provided that both actual starred objects lie below
the same source.  In particular, it identifies any eligible zero-interior
observation with the pointed constant word at a fixed source root. -/
theorem color_eq_pointObservation_of_relative_empty_boundary
    {b n k : Nat} {α γ : Type*}
    (f : Word b n k α)
    (color : StarredObservation b n α → γ)
    (hsimple : Theorem25.SimpleWithinWith
      ForwardSemiCompleteSimplicity.canonicalPoint
      (∅ : Set (CanonicalTheoremSpec.Boundary b 0)) color f)
    (U : Starred b n 0 α) (hU : StarredBelow U f)
    (p : BoundedNode b n) (hp : p ∈ f.support) :
    color (starredObserve U) =
      color (ZeroInteriorRamsey.pointObservation
        (ZeroInteriorRamsey.constantWord U) p.1) := by
  rw [← ZeroInteriorRamsey.pointedStarred_observe]
  have hpoint : StarredBelow
      (ZeroInteriorRamsey.pointedStarred
        (ZeroInteriorRamsey.constantWord U) p) f :=
    (ZeroInteriorRamsey.pointedStarred_below_iff
      (ZeroInteriorRamsey.constantWord U) p f).2
      ⟨(starredBelow_span hU).2
        (ZeroInteriorRamsey.constantWord_mem_span U), hp⟩
  apply hsimple U
    (ZeroInteriorRamsey.pointedStarred (ZeroInteriorRamsey.constantWord U) p)
    hU hpoint
  · intro t
    simp only [ZeroInteriorRamsey.interior_nil, List.not_mem_nil]
  · intro a ha
    exact False.elim ha
  · intro s _
    rw [ZeroInteriorRamsey.underlyingSymbol_eq_constant U s]
    rfl

/-- The ordinary relative ground-word theorem implies the corrected
relative starred theorem at zero interior, by a genuine case split on the
selected boundary. In the nonempty case no ground Ramsey input is used. -/
theorem relative_zero_starred_of_ground
    {b n k : Nat} {α γ : Type*}
    (f : Word b n k α) (fallback : α)
    (hground : RelativeGroundOne (γ := γ) f) :
    Theorem25.RelativeRamseyInput
      (l := 0) ForwardSemiCompleteSimplicity.canonicalPoint 1 f := by
  intro color hsimple
  obtain ⟨B₂, hB₂⟩ := hsimple
  by_cases hempty : B₂ = ∅
  · subst B₂
    obtain ⟨p, hp⟩ := ZeroInteriorRamsey.exists_support_root f
    obtain ⟨g, hgf, hmono⟩ :=
      hground (fun w => color (ZeroInteriorRamsey.pointObservation w p.1))
    refine ⟨g, hgf, ?_⟩
    intro U V hU hV
    have hUf : StarredBelow U f :=
      starredBelow_of_syntacticRefines hgf hU
    have hVf : StarredBelow V f :=
      starredBelow_of_syntacticRefines hgf hV
    have hUw : ZeroInteriorRamsey.constantWord U ∈ g.span :=
      (starredBelow_span hU).2 (ZeroInteriorRamsey.constantWord_mem_span U)
    have hVw : ZeroInteriorRamsey.constantWord V ∈ g.span :=
      (starredBelow_span hV).2 (ZeroInteriorRamsey.constantWord_mem_span V)
    calc
      color (starredObserve U) =
          color (ZeroInteriorRamsey.pointObservation
            (ZeroInteriorRamsey.constantWord U) p.1) :=
        color_eq_pointObservation_of_relative_empty_boundary
          f color hB₂ U hUf p hp
      _ = color (ZeroInteriorRamsey.pointObservation
            (ZeroInteriorRamsey.constantWord V) p.1) :=
        hmono _ _ hUw hVw
      _ = color (starredObserve V) :=
        (color_eq_pointObservation_of_relative_empty_boundary
          f color hB₂ V hVf p hp).symm
  · have hnonempty : B₂.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    exact ZeroInteriorRamsey.exists_monochromatic_singleton_refinement_of_nonempty_boundary
      color f fallback B₂ hnonempty hB₂

/-- Conversely, the relative starred theorem is at least as strong as
ordinary relative ground-word Ramsey. Each word in the chosen span gives
a genuine eligible pointed object at one common support root. -/
theorem relative_ground_of_zero_starred
    {b n k : Nat} {α γ : Type*}
    (f : Word b n k α) (fallback : α)
    (hstar : Theorem25.RelativeRamseyInput
      (l := 0) (γ := γ)
      ForwardSemiCompleteSimplicity.canonicalPoint 1 f) :
    RelativeGroundOne (γ := γ) f := by
  intro c
  let color : StarredObservation b n α → γ :=
    fun O => c (groundOfObservation fallback O)
  obtain ⟨g, hgf, hmono⟩ :=
    hstar color (groundColour_simpleWithin f fallback c)
  obtain ⟨p, hp⟩ := ZeroInteriorRamsey.exists_support_root g
  refine ⟨g, hgf, ?_⟩
  intro u v hu hv
  have hU : StarredBelow (ZeroInteriorRamsey.pointedStarred u p) g :=
    (ZeroInteriorRamsey.pointedStarred_below_iff u p g).2 ⟨hu, hp⟩
  have hV : StarredBelow (ZeroInteriorRamsey.pointedStarred v p) g :=
    (ZeroInteriorRamsey.pointedStarred_below_iff v p g).2 ⟨hv, hp⟩
  have h := hmono (ZeroInteriorRamsey.pointedStarred u p)
    (ZeroInteriorRamsey.pointedStarred v p) hU hV
  change c (groundOfObservation fallback
      (starredObserve (ZeroInteriorRamsey.pointedStarred u p))) =
    c (groundOfObservation fallback
      (starredObserve (ZeroInteriorRamsey.pointedStarred v p))) at h
  simpa only [ZeroInteriorRamsey.pointedStarred_observe,
    groundOfObservation_pointObservation] using h

/-- The exact logical reduction of the corrected relative base case.
It leaves no special simplicity or marked-point hypothesis unresolved;
the remaining relative existence input is precisely ground-word Ramsey. -/
theorem relative_zero_starred_iff_ground
    {b n k : Nat} {α γ : Type*}
    (f : Word b n k α) (fallback : α) :
    Theorem25.RelativeRamseyInput
      (l := 0) (γ := γ)
      ForwardSemiCompleteSimplicity.canonicalPoint 1 f ↔
    RelativeGroundOne (γ := γ) f := by
  exact ⟨relative_ground_of_zero_starred f fallback,
    relative_zero_starred_of_ground f fallback⟩

end DualTree.ZeroInteriorRelative
