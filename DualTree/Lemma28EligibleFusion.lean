import DualTree.Lemma28

/-!
# Lemma 28: finite fusion with stability only on eligible signature fibres

The original conditional fusion in `Lemma28` preserves *literal equality*
of all previously processed model signatures after each refinement.
The induction uses less: for every object eligible below the NEW word,
membership in an old model fibre must agree with membership in the new
interpretation of the same task.

This file proves finite fusion and final signature canonization with that
weaker, semantic, fibrewise hypothesis. It also proves the original exact
transport step implies the new local step.

No geometric model-signature transport, one-fibre canonization, relative
Ramsey input or model-signature coverage is asserted to exist here.
-/

namespace DualTree.Lemma28EligibleFusion

open CorrectedTheoremSpec

/-- In a new refinement, the old and new interpretations of earlier model
tasks may be unequal as signature values, but their eligible fibres agree.
The equivalence is required only on objects refining the NEW word. -/
def EligibleFibreStable
    {b n l k m : Nat} {α Sig : Type*}
    (signature : Starred b n l α → Sig)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (f : Word b n k α) (g : Word b n m α) (p : Nat) : Prop :=
  ∀ i : Nat, i < p →
    ∀ U : Starred b n l α, StarredBelow U g →
      (signature U = transport g i ↔ signature U = transport f i)

/-- One local signature-canonization step with the exact preservation
hypothesis needed by finite fusion, and no global value equality. -/
def LocalFusionStepEligible
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (p : Nat) : Prop :=
  ∀ f : Word b n (height p) α,
    ∃ g : Word b n (height (p + 1)) α,
      KVariableWord.SyntacticRefines g f ∧
      Lemma28.FibreMonochromatic signature color g (transport g p) ∧
      EligibleFibreStable signature transport f g p

/-- An old monochromatic fibre survives when its restriction to the new
eligible domain agrees with the transported current fibre. -/
theorem fibreMonochromatic_of_eligible_transport
    {b n l k m : Nat} {α γ Sig : Type*}
    {signature : Starred b n l α → Sig}
    {color : Starred b n l α → γ}
    {f : Word b n k α} {g : Word b n m α} {s t : Sig}
    (hgf : KVariableWord.SyntacticRefines g f)
    (hmono : Lemma28.FibreMonochromatic signature color f s)
    (hstable : ∀ U : Starred b n l α, StarredBelow U g →
      (signature U = t ↔ signature U = s)) :
    Lemma28.FibreMonochromatic signature color g t := by
  intro U V hU hV hUt hVt
  exact hmono U V
    (starredBelow_of_syntacticRefines hgf hU)
    (starredBelow_of_syntacticRefines hgf hV)
    ((hstable U hU).1 hUt) ((hstable V hV).1 hVt)

/-- Finite induction on actual complete words with eligible-fibre
transport. This does not strengthen the one-step Ramsey assumption;
it weakens the required old-task preservation. -/
theorem finite_signature_fusion_of_eligible_stability
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (P : Nat)
    (f₀ : Word b n (height 0) α)
    (hstep : ∀ p : Nat, p < P →
      LocalFusionStepEligible signature color transport height p) :
    ∃ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ ∧
      Lemma28.Processed signature color transport P g := by
  have hstage : ∀ p : Nat, p ≤ P →
      ∃ f : Word b n (height p) α,
        KVariableWord.SyntacticRefines f f₀ ∧
        Lemma28.Processed signature color transport p f := by
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
        · exact fibreMonochromatic_of_eligible_transport hgf
            (hprocessed i hip) (hstable i hip)
        · have hieq : i = p := by omega
          subst i
          exact hnew
  exact hstage P (Nat.le_refl P)

/-- Final source-facing signature canonization follows with the same
restricted coverage hypothesis as in the existing conditional Lemma 28. -/
theorem finite_signature_canonization_of_eligible_stability
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (P : Nat)
    (f₀ : Word b n (height 0) α)
    (hstep : ∀ p : Nat, p < P →
      LocalFusionStepEligible signature color transport height p)
    (hcover : ∀ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ →
      Lemma28.CoversSignatures signature transport P g) :
    ∃ g : Word b n (height P) α,
      KVariableWord.SyntacticRefines g f₀ ∧
      Lemma28.SignatureCanonical signature color g := by
  obtain ⟨g, hgf, hprocessed⟩ :=
    finite_signature_fusion_of_eligible_stability
      signature color transport height P f₀ hstep
  exact ⟨g, hgf,
    Lemma28.signatureCanonical_of_processed hprocessed (hcover g hgf)⟩

/-- The previous stronger local interface implies the new one: literal
model-signature equality certainly gives fibre equivalence everywhere. -/
theorem eligible_step_of_exact_transport
    {b n l : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (color : Starred b n l α → γ)
    (transport : ∀ {q : Nat}, Word b n q α → Nat → Sig)
    (height : Nat → Nat) (p : Nat)
    (hstep : Lemma28.LocalFusionStep signature color transport height p) :
    LocalFusionStepEligible signature color transport height p := by
  intro f
  obtain ⟨g, hgf, hmono, hstable⟩ := hstep f
  refine ⟨g, hgf, hmono, ?_⟩
  intro i hi U _
  rw [hstable i hi]

end DualTree.Lemma28EligibleFusion
