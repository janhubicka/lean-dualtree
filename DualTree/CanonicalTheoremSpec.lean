import DualTree.Theorem25
import DualTree.ForwardSemiCompleteSimplicity

/-!
# Corrected Theorem 25 with its intrinsic canonical selector

The abstract selector in `CorrectedTheoremSpec` is now instantiated with
Track E's canonical boundary map on every semi-complete starred object,
including the singleton boundary when the interior is empty.

Colours here still act on semantic starred observations.  The bridges
below relate that convention to Track E's source-independent simplicity
predicate.  Global simplicity restricts to every ambient word without an
alphabet-size assumption.  For relative simplicity, the source predicate
compares evaluated-span refinements, whereas the corrected induction uses
syntactic refinements.  The latter predicates are proved equivalent only
when the alphabet contains two distinct letters.

The final Ramsey and eventual-bound definitions remain target propositions;
this module does not supply a Ramsey witness or prove the induction base.
-/

namespace DualTree.CanonicalTheoremSpec

open CorrectedTheoremSpec

/-- The intrinsic boundary index set is independent of ambient height and
of the particular starred object.  It includes the root index at `l = 0`. -/
abbrev Boundary (b l : Nat) := ForwardSemiCompleteSimplicity.Boundary b l

/-- Corrected Definition 24 on semantic observations, with the actual
canonical boundary selector and a specified partition. -/
def SimpleWith {b n l : Nat} {α γ : Type*}
    (B₂ : Set (Boundary b l))
    (color : StarredObservation b n α → γ) : Prop :=
  CorrectedTheoremSpec.SimpleWith
    ForwardSemiCompleteSimplicity.canonicalPoint B₂ color

/-- The partition is existentially quantified; the selector is fixed. -/
def Simple {b n l : Nat} {α γ : Type*}
    (color : StarredObservation b n α → γ) : Prop :=
  ∃ B₂ : Set (Boundary b l), SimpleWith B₂ color

/-- Global canonical simplicity supplies the exact source-relative
simplicity used by Track E, even for a one-letter alphabet. -/
theorem sourceSimpleWithin_of_simpleWith
    {b n l : Nat} {α γ : Type*}
    (ambient : VariableWord b n α)
    (B₂ : Set (Boundary b l))
    (color : StarredObservation b n α → γ)
    (hsimple : SimpleWith B₂ color) :
    ForwardSemiCompleteSimplicity.SimpleWithin ambient B₂
      (fun U => color (starredObserve U)) := by
  intro U V _ _ hInterior hPoints hWord
  exact hsimple U V hInterior hPoints hWord

theorem sourceSimple_of_simple
    {b n l : Nat} {α γ : Type*}
    (ambient : VariableWord b n α)
    (color : StarredObservation b n α → γ)
    (hsimple : Simple (l := l) color) :
    ForwardSemiCompleteSimplicity.Simple (l := l) ambient
      (fun U => color (starredObserve U)) := by
  obtain ⟨B₂, hB₂⟩ := hsimple
  exact ⟨B₂, sourceSimpleWithin_of_simpleWith ambient B₂ color hB₂⟩

/-- Every corrected syntactic starred refinement is an eligible
source-facing evaluated-span refinement.  No converse is used here. -/
theorem sourceRefines_of_starredBelow
    {b n l k : Nat} {α : Type*}
    {U : Starred b n l α} {f : Word b n k α}
    (hU : StarredBelow U f) :
    ForwardSemiCompleteSimplicity.Refines f.toVariableWord U :=
  starredBelow_span hU

/-- The source and corrected refinement domains coincide under precisely
the non-unary hypothesis required by symbolic substitution recovery. -/
theorem starredBelow_iff_sourceRefines
    {b n l k : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (U : Starred b n l α) (f : Word b n k α) :
    StarredBelow U f ↔
      ForwardSemiCompleteSimplicity.Refines f.toVariableWord U :=
  starredBelow_iff_span hα U f

/-- Source-relative simplicity restricts to the corrected syntactic
domain for every alphabet. -/
theorem relativeSimpleWith_of_source
    {b n l k : Nat} {α γ : Type*}
    (f : Word b n k α) (B₂ : Set (Boundary b l))
    (color : StarredObservation b n α → γ)
    (hsimple : ForwardSemiCompleteSimplicity.SimpleWithin
      f.toVariableWord B₂ (fun U => color (starredObserve U))) :
    Theorem25.SimpleWithinWith
      ForwardSemiCompleteSimplicity.canonicalPoint B₂ color f := by
  intro U V hU hV hInterior hPoints hWord
  exact hsimple U V (sourceRefines_of_starredBelow hU)
    (sourceRefines_of_starredBelow hV) hInterior hPoints hWord

/-- With two letters, the relative semantic induction predicate is
exactly Track E's source-facing canonical simplicity predicate. -/
theorem relativeSimpleWith_iff_source
    {b n l k : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : Word b n k α) (B₂ : Set (Boundary b l))
    (color : StarredObservation b n α → γ) :
    Theorem25.SimpleWithinWith
      ForwardSemiCompleteSimplicity.canonicalPoint B₂ color f ↔
    ForwardSemiCompleteSimplicity.SimpleWithin
      f.toVariableWord B₂ (fun U => color (starredObserve U)) := by
  constructor
  · intro hsimple U V hU hV hInterior hPoints hWord
    exact hsimple U V
      ((starredBelow_iff_sourceRefines hα U f).2 hU)
      ((starredBelow_iff_sourceRefines hα V f).2 hV)
      hInterior hPoints hWord
  · exact relativeSimpleWith_of_source f B₂ color

theorem relativeSimple_iff_source
    {b n l k : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (f : Word b n k α)
    (color : StarredObservation b n α → γ) :
    Theorem25.SimpleWithin (l := l)
      ForwardSemiCompleteSimplicity.canonicalPoint color f ↔
    ForwardSemiCompleteSimplicity.Simple (l := l) f.toVariableWord
      (fun U => color (starredObserve U)) := by
  constructor
  · rintro ⟨B₂, hB₂⟩
    exact ⟨B₂, (relativeSimpleWith_iff_source hα f B₂ color).1 hB₂⟩
  · rintro ⟨B₂, hB₂⟩
    exact ⟨B₂, (relativeSimpleWith_iff_source hα f B₂ color).2 hB₂⟩

/-- Corrected Theorem 25 at one ambient height, with no free selector
parameter remaining.  This is a specification, not an existence theorem. -/
def RamseyAt (b n l m : Nat) (α γ : Type*) : Prop :=
  StarredRamseyAt b n l m α γ (Boundary b l)
    ForwardSemiCompleteSimplicity.canonicalPoint

/-- A positive eventual threshold for the canonical-selector target.
The alphabet-size parameter is retained explicitly. -/
def Bound (b ell l m r N : Nat) : Prop :=
  EventualBound (fun n => RamseyAt b n l m (Fin ell) (Fin r)) N

/-- The full corrected qualitative target with the now-audited intrinsic
selector.  All nonnegative interior counts, including zero, are covered
by the statement; existence and the induction base remain unproved. -/
def CorrectedTheorem25 : Prop :=
  ∀ b ell l m r : Nat,
    0 < b → 0 < ell → 0 < m → 0 < r →
      ∃ N : Nat, Bound b ell l m r N

end DualTree.CanonicalTheoremSpec
