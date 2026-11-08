import DualTree.CanonicalTheoremSpec
import DualTree.ForwardSemiCompleteModelIso
import DualTree.RayHalesJewett
import DualTree.RootFreezing
import DualTree.AmbientHeightPadding

/-!
# An actual zero-interior Ramsey theorem at target height one

A zero-interior starred word has no variable symbols. Its semantic data
are an ordinary constant tree word and its one marked support vertex.
The constructions below retain uniform syntactic refinement, so no
two-letter hypothesis is needed for this description or its eligibility
criterion.

For a nonempty selected boundary, relative simplicity makes every
singleton-support refinement homogeneous: all its marked vertices are
the same root, and every variable occurrence lies in that root's cone.
For an empty selected boundary, simplicity removes the marked vertex
from the colour. The genuine scalar tree Hales--Jewett theorem then
supplies a monochromatic complete word of height one.

The final theorems construct a positive ambient height and then an actual
eventual threshold for the canonical corrected target at l = 0 and m = 1.
Only ordinary ground words are padded to obtain the eventual conclusion.
The arbitrary-m zero-interior base and the final induction's relative
empty-boundary input remain open. No fixed/current signature identification
is used.
-/

namespace DualTree.ZeroInteriorRamsey

open CorrectedTheoremSpec
open ForwardSemiCompleteZeroRoot

/-- A constant tree word, regarded as a variable word with empty support. -/
def constantVariableWord {b n : Nat} {α : Type*}
    (w : TreeWord b n α) : VariableWord b n α where
  support := []
  support_nodup := by simp
  word := fun s => Sum.inl (w s)
  atRoot := by
    intro v
    exact False.elim (by simpa using v.2)
  below := by
    intro v s hs
    exact False.elim (by simpa using v.2)

/-- The genuine zero-interior starred object associated to a word and point. -/
def pointedStarred {b n : Nat} {α : Type*}
    (w : TreeWord b n α) (p : BoundedNode b n) : Starred b n 0 α where
  tree := [p.1]
  tree_bounded := by
    intro t ht
    have h : t = p.1 := by simpa using ht
    simpa only [h] using p.2
  semi_complete := by
    simp [SkewTree.semiCompleteB, SkewTree.singleton_skewB,
      SkewTree.immediateSuccs, SkewTree.immediateSuccB,
      SkewTree.strictPrefixB]
  word := constantVariableWord w
  interior_card := by
    simp [StarredSignature.singleton_interior_nil]
  support_eq_interior := by
    intro t
    simp [constantVariableWord, VariableWord.supportNodes,
      StarredSignature.singleton_interior_nil]
  support_skew := by omega

/-- A semantic pointed constant observation. The point need not be bounded
until this observation is used to represent a genuine starred object. -/
def pointObservation {b n : Nat} {α : Type*}
    (w : TreeWord b n α) (p : Node b) : StarredObservation b n α :=
  ({p}, fun s => Sum.inl (w s))

theorem pointedStarred_observe {b n : Nat} {α : Type*}
    (w : TreeWord b n α) (p : BoundedNode b n) :
    starredObserve (pointedStarred w p) = pointObservation w p.1 := by
  apply Prod.ext
  · change [p.1].toFinset = ({p.1} : Finset (Node b))
    simp
  · funext s
    rfl

/-- Zero interior size really makes the interior list empty. -/
theorem interior_nil {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) : SkewTree.interior U.tree = [] :=
  List.length_eq_zero_iff.mp U.interior_card

/-- There is no variable name in a zero-interior starred word. -/
theorem no_variable {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) (v : U.word.Vars) : False := by
  have h := StarredSignature.variable_root_in_interior U v
  simp only [interior_nil U, List.not_mem_nil] at h

/-- The actual constant word contained in a zero-interior starred object. -/
def constantWord {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) : TreeWord b n α :=
  fun s => match U.word.word s with
    | Sum.inl a => a
    | Sum.inr v => False.elim (no_variable U v)

theorem word_eq_constant {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) (s : BoundedNode b n) :
    U.word.word s = Sum.inl (constantWord U s) := by
  cases h : U.word.word s with
  | inl a => simp [constantWord, h]
  | inr v => exact False.elim (no_variable U v)

theorem underlyingSymbol_eq_constant {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) (s : BoundedNode b n) :
    CutPreservation.underlyingSymbol U.word s =
      Sum.inl (constantWord U s) := by
  simp [CutPreservation.underlyingSymbol, word_eq_constant U s]

theorem constantWord_mem_span {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) : constantWord U ∈ U.word.span := by
  refine ⟨fun v => False.elim (no_variable U v), ?_⟩
  funext s
  simp [SpanAudit.eval, SpanAudit.evalSymbol, word_eq_constant U s]

/-- The marked root is an actual node of the original finite ambient tree. -/
noncomputable def point {b n : Nat} {α : Type*}
    (U : Starred b n 0 α) : BoundedNode b n :=
  ⟨starredRootAll U, U.tree_bounded _ (starredRootAll_mem U)⟩

/-- Every zero-interior semantic observation is exactly a pointed constant
word. No ordering or multiplicity information from a support presentation
is supplied to the colour. -/
theorem starredObserve_eq_pointObservation
    {b n : Nat} {α : Type*} (hb : 0 < b)
    (U : Starred b n 0 α) :
    starredObserve U = pointObservation (constantWord U) (point U).1 := by
  apply Prod.ext
  · apply Finset.ext
    intro t
    change t ∈ U.tree.toFinset ↔ t ∈ ({starredRootAll U} : Finset (Node b))
    simp only [List.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact ForwardSemiCompleteModelIso.zero_vertex_eq_root hb U t
    · intro h
      simpa only [h] using starredRootAll_mem U
  · funext s
    exact underlyingSymbol_eq_constant U s

/-- Exact eligibility of a pointed constant object. The converse constructs
its uniform substitution from an evaluation, even for a unary alphabet. -/
theorem pointedStarred_below_iff
    {b n k : Nat} {α : Type*}
    (w : TreeWord b n α) (p : BoundedNode b n) (f : Word b n k α) :
    StarredBelow (pointedStarred w p) f ↔
      w ∈ f.span ∧ p ∈ f.support := by
  constructor
  · intro h
    have hw : w ∈ (pointedStarred w p).word.span := by
      refine ⟨fun v => False.elim (no_variable (pointedStarred w p) v), ?_⟩
      rfl
    refine ⟨(starredBelow_span h).2 hw, ?_⟩
    have hp := h.1 p.1 (by simp [pointedStarred])
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hp
    have heq : q = p := Subtype.ext hqp
    simpa only [heq] using hq
  · rintro ⟨⟨σ, hσ⟩, hp⟩
    constructor
    · intro t ht
      have heq : t = p.1 := by simpa [pointedStarred] using ht
      exact List.mem_map.mpr ⟨p, hp, heq.symm⟩
    · refine ⟨fun v => Sum.inl (σ v), ?_⟩
      funext s
      change Sum.inl (w s) = _
      rw [← hσ]
      cases hs : f.word s <;>
        simp only [SpanAudit.eval, SpanAudit.evalSymbol, SpanAudit.substitute, hs] <;> rfl

/-- Empty-boundary simplicity makes the marked vertex irrelevant while
preserving the entire constant word. -/
theorem color_eq_pointObservation_of_empty_boundary
    {b n : Nat} {α γ : Type*}
    (color : StarredObservation b n α → γ)
    (hsimple : CanonicalTheoremSpec.SimpleWith
      (l := 0) (∅ : Set (CanonicalTheoremSpec.Boundary b 0)) color)
    (U : Starred b n 0 α) (p : BoundedNode b n) :
    color (starredObserve U) =
      color (pointObservation (constantWord U) p.1) := by
  rw [← pointedStarred_observe]
  apply hsimple U (pointedStarred (constantWord U) p)
  · intro t
    simp only [interior_nil, List.not_mem_nil]
  · intro a ha
    exact False.elim ha
  · intro s _
    rw [underlyingSymbol_eq_constant]
    rfl

/-- Every genuine complete word has a support root. This follows from
skewness itself, without assuming a numerical lower bound on its height. -/
theorem exists_support_root {b n k : Nat} {α : Type*}
    (f : Word b n k α) : ∃ p : BoundedNode b n, p ∈ f.support := by
  cases hs : f.support with
  | nil =>
      have h := f.complete_support
      simp [VariableWord.supportNodes, hs, SkewTree.completeB,
        SkewTree.skewB, SkewTree.rootedB] at h
  | cons p rest => exact ⟨p, by simp⟩

/-- The zero-interior refinement domain is inhabited whenever the alphabet
has a supplied letter. In particular the homogeneity conclusions below
are not obtained by choosing an empty starred-refinement domain. -/
theorem exists_starredBelow_zero {b n k : Nat} {α : Type*}
    (f : Word b n k α) (fallback : α) :
    ∃ U : Starred b n 0 α, StarredBelow U f := by
  obtain ⟨p, hp⟩ := exists_support_root f
  let w := f.toVariableWord.eval (fun _ => fallback)
  refine ⟨pointedStarred w p, (pointedStarred_below_iff w p f).2 ?_⟩
  exact ⟨⟨fun _ => fallback, rfl⟩, hp⟩

/-- Retain one old root, freezing all other variable names uniformly. -/
noncomputable def singletonRefinement
    {b n k : Nat} {α : Type*}
    (f : Word b n k α) (r : f.Vars) (fallback : α) : Word b n 1 α where
  toVariableWord := Lemma27Repair.restrictSupport f.toVariableWord [r.1]
    (by simp) (by
      intro t ht
      have h : t = r.1 := by simpa using ht
      simpa only [h] using r.2) fallback
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1 [r.1.1] = true
    exact SkewTree.singleton_complete_oneB _ _

theorem singletonRefinement_support
    {b n k : Nat} {α : Type*}
    (f : Word b n k α) (r : f.Vars) (fallback : α) :
    (singletonRefinement f r fallback).support = [r.1] := rfl

theorem singletonRefinement_syntacticRefines
    {b n k : Nat} {α : Type*}
    (f : Word b n k α) (r : f.Vars) (fallback : α) :
    KVariableWord.SyntacticRefines (singletonRefinement f r fallback) f :=
  ⟨Lemma27Repair.rootMask f.toVariableWord [r.1] fallback, rfl⟩

/-- In the nonempty-boundary case, actual relative simplicity already
makes any singleton-support syntactic refinement monochromatic.
The source colour is fixed before either complete word is selected. -/
theorem monochromatic_singleton_of_nonempty_boundary
    {b n k : Nat} {α γ : Type*}
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (g : Word b n 1 α)
    (hgf : KVariableWord.SyntacticRefines g f)
    (p : BoundedNode b n) (hsupport : g.support = [p])
    (B₂ : Set (CanonicalTheoremSpec.Boundary b 0)) (hB₂ : B₂.Nonempty)
    (hsimple : Theorem25.SimpleWithinWith
      ForwardSemiCompleteSimplicity.canonicalPoint B₂ color f) :
    StarredMonochromatic (l := 0) color g := by
  intro U V hU hV
  have hrootU : starredRootAll U = p.1 := by
    have h := hU.1 _ (starredRootAll_mem U)
    change starredRootAll U ∈ g.support.map Subtype.val at h
    simpa only [hsupport, List.map_cons, List.map_nil, List.mem_singleton] using h
  have hrootV : starredRootAll V = p.1 := by
    have h := hV.1 _ (starredRootAll_mem V)
    change starredRootAll V ∈ g.support.map Subtype.val at h
    simpa only [hsupport, List.map_cons, List.map_nil, List.mem_singleton] using h
  apply hsimple U V (starredBelow_of_syntacticRefines hgf hU)
    (starredBelow_of_syntacticRefines hgf hV)
  · intro t
    simp only [interior_nil, List.not_mem_nil]
  · intro a _
    rw [ForwardSemiCompleteSimplicity.canonicalPoint_zero,
      ForwardSemiCompleteSimplicity.canonicalPoint_zero, hrootU, hrootV]
  · intro s hs
    obtain ⟨a, ha⟩ := hB₂
    have hout : ¬ IsPrefix p.1 s.1 := by
      simpa only [ForwardSemiCompleteSimplicity.canonicalPoint_zero, hrootU]
        using hs a ha
    obtain ⟨ρ, hρ⟩ := hU.2
    obtain ⟨τ, hτ⟩ := hV.2
    cases hgs : g.word s with
    | inl c =>
        have hUs : U.word.word s = Sum.inl c := by
          rw [hρ]
          simp [SpanAudit.substitute, hgs]
        have hVs : V.word.word s = Sum.inl c := by
          rw [hτ]
          simp [SpanAudit.substitute, hgs]
        simp [CutPreservation.underlyingSymbol, hUs, hVs]
    | inr v =>
        have hv : v.1 = p := by
          simpa only [hsupport, List.mem_singleton] using v.2
        exact False.elim (hout (by
          simpa only [hv] using g.toVariableWord.below v s hgs))

/-- A genuine relative one-root witness in the nonempty-boundary case.
It is constructed inside the prescribed ambient word, including over
unary alphabets; there is no assumed refinement-existence input. -/
theorem exists_monochromatic_singleton_refinement_of_nonempty_boundary
    {b n k : Nat} {α γ : Type*}
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (fallback : α)
    (B₂ : Set (CanonicalTheoremSpec.Boundary b 0)) (hB₂ : B₂.Nonempty)
    (hsimple : Theorem25.SimpleWithinWith
      ForwardSemiCompleteSimplicity.canonicalPoint B₂ color f) :
    ∃ g : Word b n 1 α,
      KVariableWord.SyntacticRefines g f ∧
      StarredMonochromatic (l := 0) color g := by
  obtain ⟨p, hp⟩ := exists_support_root f
  let r : f.Vars := ⟨p, hp⟩
  let g := singletonRefinement f r fallback
  have hgf := singletonRefinement_syntacticRefines f r fallback
  refine ⟨g, hgf, ?_⟩
  exact monochromatic_singleton_of_nonempty_boundary color f g hgf p
    (singletonRefinement_support f r fallback) B₂ hB₂ hsimple

/-- The substantive zero-interior bridge: an ordinary complete one-root
ground-word Ramsey theorem gives the canonical simple starred theorem.
Its two simplicity cases are proved using actual starred observations
and uniform substitutions. No starred Ramsey input is assumed. -/
theorem positive_ramseyAt_zero_one_of_ground_word_ramsey
    {b n : Nat} {α γ : Type*}
    (fallback : α) (fallbackColor : γ)
    (hRamsey : ∀ c : TreeWord b n α → γ,
      ∃ f : Word b n 1 α,
        ∃ col : γ, ∀ w : TreeWord b n α, w ∈ f.span → c w = col) :
    0 < n ∧ CanonicalTheoremSpec.RamseyAt b n 0 1 α γ := by
  obtain ⟨seed, _, _⟩ := hRamsey (fun _ => fallbackColor)
  obtain ⟨p, _⟩ := exists_support_root seed
  have hnpos : 0 < n := by
    have hp := p.2
    change p.1.length < n at hp
    omega
  let basepoint : BoundedNode b n := ⟨[], by simpa [InHomTree] using hnpos⟩
  refine ⟨hnpos, ?_⟩
  intro color hsimple
  obtain ⟨B₂, hsimple⟩ := hsimple
  by_cases hempty : B₂ = ∅
  · subst B₂
    obtain ⟨f, col, hmono⟩ :=
      hRamsey (fun w => color (pointObservation w []))
    refine ⟨f, ?_⟩
    intro U V hU hV
    have hUword : constantWord U ∈ f.span :=
      (starredBelow_span hU).2 (constantWord_mem_span U)
    have hVword : constantWord V ∈ f.span :=
      (starredBelow_span hV).2 (constantWord_mem_span V)
    calc
      color (starredObserve U) =
          color (pointObservation (constantWord U) []) :=
        color_eq_pointObservation_of_empty_boundary color hsimple U basepoint
      _ = col := hmono _ hUword
      _ = color (pointObservation (constantWord V) []) := (hmono _ hVword).symm
      _ = color (starredObserve V) :=
        (color_eq_pointObservation_of_empty_boundary color hsimple V basepoint).symm
  · have hB₂ : B₂.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    have hrelative : Theorem25.SimpleWithinWith
        ForwardSemiCompleteSimplicity.canonicalPoint B₂ color seed := by
      intro U V _ _
      exact hsimple U V
    obtain ⟨g, _, hg⟩ :=
      exists_monochromatic_singleton_refinement_of_nonempty_boundary
        color seed fallback B₂ hB₂ hrelative
    exact ⟨g, hg⟩

/-- Actual finite Ramsey existence for the corrected canonical target at
l = 0 and m = 1. The two supplied values witness nonempty alphabet and
colour types. The positive ambient height is chosen before the colour. -/
theorem exists_positive_ramseyAt_zero_one
    {b : Nat} (hb : 0 < b)
    (α γ : Type*) [Finite α] [Finite γ]
    (fallback : α) (fallbackColor : γ) :
    ∃ n : Nat, 0 < n ∧ CanonicalTheoremSpec.RamseyAt b n 0 1 α γ := by
  obtain ⟨n, hRamsey⟩ :=
    RayHalesJewett.exists_monochromatic_one_root_tree_word hb α γ fallback
  exact ⟨n, positive_ramseyAt_zero_one_of_ground_word_ramsey
    fallback fallbackColor hRamsey⟩

/-- A proved positive eventual threshold for the same one-root target.
Padding the ground-word theorem supplies every later ambient height;
the canonical zero-interior bridge is then applied at that actual height. -/
theorem exists_eventual_ramseyAt_zero_one
    {b : Nat} (hb : 0 < b)
    (α γ : Type*) [Finite α] [Finite γ]
    (fallback : α) (fallbackColor : γ) :
    ∃ N : Nat, EventualBound
      (fun n => CanonicalTheoremSpec.RamseyAt b n 0 1 α γ) N := by
  obtain ⟨N, hRamsey⟩ :=
    RayHalesJewett.exists_monochromatic_one_root_tree_word hb α γ fallback
  have hpositive :=
    (positive_ramseyAt_zero_one_of_ground_word_ramsey
      fallback fallbackColor hRamsey).1
  refine ⟨N, hpositive, ?_⟩
  intro n hNn
  exact (positive_ramseyAt_zero_one_of_ground_word_ramsey fallback fallbackColor
    (AmbientHeightPadding.ground_word_ramsey_mono hNn fallback hRamsey)).2

/-- The actual canonical-alphabet bound specification is inhabited at
zero interior and target height one, including ell = 1 and b = 1. -/
theorem exists_bound_zero_one
    {b ell r : Nat} (hb : 0 < b) (hell : 0 < ell) (hr : 0 < r) :
    ∃ N : Nat, CanonicalTheoremSpec.Bound b ell 0 1 r N :=
  exists_eventual_ramseyAt_zero_one hb (Fin ell) (Fin r)
    ⟨0, hell⟩ ⟨0, hr⟩

end DualTree.ZeroInteriorRamsey
