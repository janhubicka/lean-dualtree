import DualTree.CorrectedTheoremSpec

/-!
# Conditional finite signature fusion for the corrected Lemma 28

The induction in this module works with actual complete-support variable
words and their syntactic refinements.  Its one-step input has two separate
parts: canonize the next signature fibre, and preserve the interpretations of
all previously processed model signatures.  The latter is not a consequence
of arbitrary syntactic refinement; the intended application must derive it
from the increasing-cut schedule and preservation of the appropriate initial
roots.

The number of tasks must come from a finite MODEL tree, independently of the
ambient tree height.  Enumerating every ambient signature instead would not
give Lemma 28's uniform intrinsic-height bound.  A separate coverage input
states that every eligible final signature is represented by a model task.

This proves the finite induction and its exact hypotheses.  It does not
construct the model transport, prove the one-signature Ramsey step, or assert
the full corrected Lemma 28 without those inputs.  The signature map is an
explicit parameter so that the eventual application can use the corrected
signature, including its partial-word domain and representation invariance.
-/

namespace DualTree.Lemma28

open CorrectedTheoremSpec

/-- Pairwise monochromaticity of one actual signature fibre below a word.
An empty fibre requires no arbitrary choice of a colour. -/
def FibreMonochromatic
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) : Prop :=
  ∀ u v : Starred b n l α,
    StarredBelow u f → StarredBelow v f →
    signature u = s → signature v = s → color u = color v

/-- The desired conclusion of the signature-canonization step, expressed
without choosing representatives of signature classes. -/
def SignatureCanonical
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (f : Word b n k α) : Prop :=
  ∀ u v : Starred b n l α,
    StarredBelow u f → StarredBelow v f →
    signature u = signature v → color u = color v

/-- A fixed ambient signature fibre remains monochromatic after any
syntactic refinement.  This does not assert stability of a transported
MODEL signature, whose interpretation can depend on the current word. -/
theorem fibreMonochromatic_of_syntacticRefines
    {b n l k k' : Nat} {α γ Sig : Type*}
    {signature : Starred b n l α → Sig}
    {color : Starred b n l α → γ}
    {f : Word b n k α} {g : Word b n k' α} {s : Sig}
    (hgf : KVariableWord.SyntacticRefines g f)
    (hmono : FibreMonochromatic signature color f s) :
    FibreMonochromatic signature color g s := by
  intro u v hu hv hsu hsv
  exact hmono u v
    (starredBelow_of_syntacticRefines hgf hu)
    (starredBelow_of_syntacticRefines hgf hv) hsu hsv

/-- The first `p` model tasks have monochromatic fibres at their CURRENT
interpretations in `f`. -/
def Processed
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (p : Nat) (f : Word b n k α) : Prop :=
  ∀ i : Nat, i < p →
    FibreMonochromatic signature color f (transport f i)

/-- The exact one-stage input for fusion.  It canonizes only the new
signature, while keeping the interpretations of EARLIER model tasks fixed.
No monochromaticity of the earlier fibres is assumed by this input. -/
def LocalFusionStep
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (p : Nat) : Prop :=
  ∀ f : Word b n (height p) α,
    ∃ g : Word b n (height (p + 1)) α,
      KVariableWord.SyntacticRefines g f ∧
      FibreMonochromatic signature color g (transport g p) ∧
      ∀ i : Nat, i < p → transport g i = transport f i

/-- Finite fusion on genuine complete-support words.  The proof composes
the actual substitutions and propagates previously processed fibres using
the explicit transport-stability input at every stage. -/
theorem finite_signature_fusion
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (P : Nat)
    (f₀ : Word b n (height 0) α)
    (hstep : ∀ p : Nat, p < P →
      LocalFusionStep signature color transport height p) :
    ∃ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ ∧
      Processed signature color transport P g := by
  have hstage : ∀ p : Nat, p ≤ P →
      ∃ f : Word b n (height p) α,
        KVariableWord.SyntacticRefines f f₀ ∧
        Processed signature color transport p f := by
    intro p
    induction p with
    | zero =>
        intro _
        refine ⟨f₀, KVariableWord.syntacticRefines_refl f₀, ?_⟩
        intro i hi
        omega
    | succ p ih =>
        intro hp
        obtain ⟨f, hff₀, hprocessed⟩ := ih (by omega)
        obtain ⟨g, hgf, hnew, hstable⟩ := hstep p (by omega) f
        refine ⟨g,
          KVariableWord.syntacticRefines_trans g f f₀ hgf hff₀, ?_⟩
        intro i hi
        by_cases hip : i < p
        · rw [hstable i hip]
          exact fibreMonochromatic_of_syntacticRefines hgf
            (hprocessed i hip)
        · have hieq : i = p := by omega
          subst i
          exact hnew
  exact hstage P (Nat.le_refl P)

/-- Every eligible final signature is represented among the finitely many
model tasks.  Surjectivity onto unrelated ambient signatures is not required. -/
def CoversSignatures
    {b n l k : Nat} {α Sig : Type*}
    (signature : Starred b n l α → Sig)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (P : Nat) (f : Word b n k α) : Prop :=
  ∀ O : Starred b n l α, StarredBelow O f →
    ∃ i : Nat, i < P ∧ signature O = transport f i

/-- Coverage converts the finite list of stabilized fibres into the
signature-canonical conclusion for ALL starred refinements of the final word. -/
theorem signatureCanonical_of_processed
    {b n l k P : Nat} {α γ Sig : Type*}
    {signature : Starred b n l α → Sig}
    {color : Starred b n l α → γ}
    {transport : ∀ {q : Nat}, Word b n q α → Nat → Sig}
    {f : Word b n k α}
    (hprocessed : Processed signature color transport P f)
    (hcover : CoversSignatures signature transport P f) :
    SignatureCanonical signature color f := by
  intro u v hu hv huv
  obtain ⟨i, hi, hui⟩ := hcover u hu
  exact hprocessed i hi u v hu hv hui (huv.symm.trans hui)

/-- Conditional Lemma-28 assembly.  Model-signature coverage is retained as
an independent hypothesis, restricted to final refinements of the actual
starting word.  It is not manufactured by the finite induction. -/
theorem finite_signature_canonization
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (P : Nat)
    (f₀ : Word b n (height 0) α)
    (hstep : ∀ p : Nat, p < P →
      LocalFusionStep signature color transport height p)
    (hcover : ∀ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ →
      CoversSignatures signature transport P g) :
    ∃ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ ∧
      SignatureCanonical signature color g := by
  obtain ⟨g, hgf, hprocessed⟩ :=
    finite_signature_fusion signature color transport height P f₀ hstep
  exact ⟨g, hgf,
    signatureCanonical_of_processed hprocessed (hcover g hgf)⟩

/-- A uniform one-step height budget iterated once per model task.  No
positivity, monotonicity, or correctness as a Ramsey bound is assumed. -/
def uniformBudget (H : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => m
  | p + 1 => H (uniformBudget H m p)

/-- Heights for a forward iteration whose budget was calculated backwards. -/
def remainingHeight (H : Nat → Nat) (m P p : Nat) : Nat :=
  uniformBudget H m (P - p)

/-- The final word has exactly the requested intrinsic height. -/
theorem remainingHeight_final (H : Nat → Nat) (m P : Nat) :
    remainingHeight H m P P = m := by
  simp [remainingHeight, uniformBudget]

/-- Each stage consumes exactly one application of the supplied one-step
budget.  This arithmetic identity does not prove the local Ramsey input. -/
theorem remainingHeight_step
    (H : Nat → Nat) (m P p : Nat) (hp : p < P) :
    remainingHeight H m P p =
      H (remainingHeight H m P (p + 1)) := by
  have heq : P - p = (P - (p + 1)) + 1 := by omega
  simp only [remainingHeight, heq, uniformBudget]

end DualTree.Lemma28
