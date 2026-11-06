import DualTree.Lemma28

/-!
# Conditional signature-colour transfer for the corrected Theorem 25

The preceding finite fusion theorem gives constancy on signature fibres.
This module constructs a genuine total colour on those signatures and proves
the final transfer from lower-interior starred objects to upper-interior
objects.  Coverage is required INSIDE the selected final refinement; global
surjectivity of an unrelated map is not sufficient.

The induction input is explicitly RELATIVE to the prescribed intermediate
word.  The printed global induction hypothesis cannot be applied to such a
word without its own embedding and simplicity transport argument.  Both the
relative Ramsey input and simplicity of the induced colour remain visible
hypotheses below.  Neither is added as an axiom or claimed to have been
constructed by this module.

The map from lower objects to upper signatures acts on their semantic
observations.  Thus the interface cannot use arbitrary list presentations as
extra colour information.  Constructing this map with the required coverage
and simplicity laws is a separate source-facing obligation.
-/

namespace DualTree.Theorem25

open CorrectedTheoremSpec

/-- A total colour on signatures.  The fallback is used only for signatures
not realized by any starred refinement of `f`. -/
noncomputable def signatureColor
    {b n l k : Nat} {α γ Σ : Type*}
    (signature : Starred b n l α → Σ)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (fallback : γ) (s : Σ) : γ := by
  classical
  exact if h : ∃ O : Starred b n l α,
      StarredBelow O f ∧ signature O = s then
    color (starredObserve (Classical.choose h))
  else fallback

/-- Signature canonization makes the chosen colour exact on every realized
signature, independently of the representative selected by choice. -/
theorem signatureColor_exact
    {b n l k : Nat} {α γ Σ : Type*}
    (signature : Starred b n l α → Σ)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (fallback : γ)
    (hcanonical : Lemma28.SignatureCanonical signature
      (fun O => color (starredObserve O)) f)
    (O : Starred b n l α) (hO : StarredBelow O f) :
    signatureColor signature color f fallback (signature O) =
      color (starredObserve O) := by
  classical
  have h : ∃ U : Starred b n l α,
      StarredBelow U f ∧ signature U = signature O := ⟨O, hO, rfl⟩
  simp only [signatureColor, dif_pos h]
  exact hcanonical (Classical.choose h) O
    (Classical.choose_spec h).1 hO (Classical.choose_spec h).2

/-- Changing the fallback never changes the colour of a realized signature. -/
theorem signatureColor_fallback_independent
    {b n l k : Nat} {α γ Σ : Type*}
    (signature : Starred b n l α → Σ)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (a a' : γ)
    (hcanonical : Lemma28.SignatureCanonical signature
      (fun O => color (starredObserve O)) f)
    (O : Starred b n l α) (hO : StarredBelow O f) :
    signatureColor signature color f a (signature O) =
      signatureColor signature color f a' (signature O) := by
  rw [signatureColor_exact signature color f a hcanonical O hO,
    signatureColor_exact signature color f a' hcanonical O hO]

/-- The actual total colour supplied to the lower-interior Ramsey input. -/
noncomputable def signaturePullback
    {b n l k : Nat} {α γ Σ : Type*}
    (signature : Starred b n l α → Σ)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (fallback : γ)
    (Q : StarredObservation b n α → Σ) :
    StarredObservation b n α → γ :=
  fun U => signatureColor signature color f fallback (Q U)

/-- Constancy of the signature pullback on lower objects implies constancy
of the original colour on upper objects, provided EVERY eligible upper
signature has a lower preimage in the SAME final refinement. -/
theorem monochromatic_of_covered_signature_pullback
    {b n l k m : Nat} {α γ Σ : Type*}
    (signature : Starred b n (l + 1) α → Σ)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) (g : Word b n m α)
    (fallback : γ) (Q : StarredObservation b n α → Σ)
    (hgf : KVariableWord.SyntacticRefines g f)
    (hcanonical : Lemma28.SignatureCanonical signature
      (fun O => color (starredObserve O)) f)
    (hcover : ∀ O : Starred b n (l + 1) α,
      StarredBelow O g →
        ∃ U : Starred b n l α,
          StarredBelow U g ∧ Q (starredObserve U) = signature O)
    (hmono : StarredMonochromatic (l := l)
      (signaturePullback signature color f fallback Q) g) :
    StarredMonochromatic (l := l + 1) color g := by
  intro O O' hO hO'
  obtain ⟨U, hU, hQU⟩ := hcover O hO
  obtain ⟨V, hV, hQV⟩ := hcover O' hO'
  have hUcolor :
      signaturePullback signature color f fallback Q (starredObserve U) =
        color (starredObserve O) := by
    unfold signaturePullback
    rw [hQU]
    exact signatureColor_exact signature color f fallback hcanonical O
      (starredBelow_of_syntacticRefines hgf hO)
  have hVcolor :
      signaturePullback signature color f fallback Q (starredObserve V) =
        color (starredObserve O') := by
    unfold signaturePullback
    rw [hQV]
    exact signatureColor_exact signature color f fallback hcanonical O'
      (starredBelow_of_syntacticRefines hgf hO')
  exact hUcolor.symm.trans ((hmono U V hU hV).trans hVcolor)

/-- Definition-24 simplicity restricted to the actual prescribed word.
The boundary selector is explicit, as in the corrected global specification. -/
def SimpleWithinWith
    {b n l k : Nat} {α γ A : Type*}
    (point : Starred b n l α → A → Node b) (B₂ : Set A)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) : Prop :=
  ∀ U V : Starred b n l α,
    StarredBelow U f → StarredBelow V f →
    (∀ t, t ∈ SkewTree.interior U.tree ↔ t ∈ SkewTree.interior V.tree) →
    (∀ a, a ∈ B₂ → point U a = point V a) →
    (∀ s : BoundedNode b n,
      (∀ a, a ∈ B₂ → ¬ IsPrefix (point U a) s.1) →
      CutPreservation.underlyingSymbol U.word s =
        CutPreservation.underlyingSymbol V.word s) →
    color (starredObserve U) = color (starredObserve V)

def SimpleWithin
    {b n l k : Nat} {α γ A : Type*}
    (point : Starred b n l α → A → Node b)
    (color : StarredObservation b n α → γ)
    (f : Word b n k α) : Prop :=
  ∃ B₂ : Set A, SimpleWithinWith point B₂ color f

/-- A genuinely globally simple colour remains simple on a prescribed word.
The converse is not silently used. -/
theorem simpleWithin_of_simple
    {b n l k : Nat} {α γ A : Type*}
    {point : Starred b n l α → A → Node b}
    {color : StarredObservation b n α → γ}
    (f : Word b n k α) (hsimple : Simple point color) :
    SimpleWithin point color f := by
  obtain ⟨B₂, hB₂⟩ := hsimple
  refine ⟨B₂, ?_⟩
  intro U V _ _ hInt hpoint hword
  exact hB₂ U V hInt hpoint hword

/-- The same simplicity witness survives every further syntactic refinement. -/
theorem simpleWithin_of_syntacticRefines
    {b n l k m : Nat} {α γ A : Type*}
    {point : Starred b n l α → A → Node b}
    {color : StarredObservation b n α → γ}
    {f : Word b n k α} {g : Word b n m α}
    (hgf : KVariableWord.SyntacticRefines g f)
    (hsimple : SimpleWithin point color f) :
    SimpleWithin point color g := by
  obtain ⟨B₂, hB₂⟩ := hsimple
  refine ⟨B₂, ?_⟩
  intro U V hU hV hInt hpoint hword
  exact hB₂ U V
    (starredBelow_of_syntacticRefines hgf hU)
    (starredBelow_of_syntacticRefines hgf hV) hInt hpoint hword

/-- The lower-interior Ramsey input needed by the induction is relative to
the PRESCRIBED source word.  This proposition has no asserted inhabitant. -/
def RelativeRamseyInput
    {b n l k : Nat} {α γ A : Type*}
    (point : Starred b n l α → A → Node b)
    (m : Nat) (f : Word b n k α) : Prop :=
  ∀ color : StarredObservation b n α → γ,
    SimpleWithin point color f →
      ∃ g : Word b n m α,
        KVariableWord.SyntacticRefines g f ∧
        StarredMonochromatic (l := l) color g

/-- One conditional Theorem-25 induction step.  The hypotheses identify the
three independent inputs still needed after signature canonization:

* a relative lower-interior Ramsey theorem;
* simplicity of the actual induced colour;
* coverage of upper signatures inside EVERY candidate final refinement.

The conclusion is proved from these inputs by the real signature-colour
factorization and substitution composition, rather than assuming the desired
upper-interior monochromaticity. -/
theorem step_of_relative_ramsey
    {b n l k k' m : Nat} {α γ Σ A : Type*}
    (signature : Starred b n (l + 1) α → Σ)
    (color : StarredObservation b n α → γ)
    (f₁ : Word b n k α) (f₂ : Word b n k' α)
    (fallback : γ) (Q : StarredObservation b n α → Σ)
    (point : Starred b n l α → A → Node b)
    (hf₂f₁ : KVariableWord.SyntacticRefines f₂ f₁)
    (hcanonical : Lemma28.SignatureCanonical signature
      (fun O => color (starredObserve O)) f₁)
    (hrelative : RelativeRamseyInput (γ := γ) point m f₂)
    (hsimple : SimpleWithin point
      (signaturePullback signature color f₁ fallback Q) f₂)
    (hcover : ∀ g : Word b n m α,
      KVariableWord.SyntacticRefines g f₂ →
        ∀ O : Starred b n (l + 1) α, StarredBelow O g →
          ∃ U : Starred b n l α,
            StarredBelow U g ∧ Q (starredObserve U) = signature O) :
    ∃ g : Word b n m α,
      KVariableWord.SyntacticRefines g f₂ ∧
      StarredMonochromatic (l := l + 1) color g := by
  obtain ⟨g, hgf₂, hmono⟩ :=
    hrelative (signaturePullback signature color f₁ fallback Q) hsimple
  refine ⟨g, hgf₂, ?_⟩
  exact monochromatic_of_covered_signature_pullback
    signature color f₁ g fallback Q
    (KVariableWord.syntacticRefines_trans g f₂ f₁ hgf₂ hf₂f₁)
    hcanonical (hcover g hgf₂) hmono

end DualTree.Theorem25
