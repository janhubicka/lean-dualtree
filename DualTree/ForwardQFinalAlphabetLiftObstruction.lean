import DualTree.ForwardQFinalMixedAlphabetSpan

/-!
# Source-faithful alphabet gap in the Lemma 27 mixed Ramsey handoff

The printed Lemma 27 applies Corollary 22 to a smooth colouring on
the ENLARGED alphabet Lambda + {0,...,m}. It therefore supplies
local mixed variable words whose coordinate constants may be either
original Lambda letters or new auxiliary letters.

The currently verified final-word interpolation instead starts with
a LocalMixedWord over the ORIGINAL alphabet Lambda and obtains
an enlarged mixed word by mapping constants through Sum.inl.
That operation permits auxiliary letters only as evaluations of
VARIABLE occurrences, never as fixed coordinate constants.

The following small algebraic facts make this interface difference
kernel-checked. In particular a genuinely enlarged local variable
word containing a fixed auxiliary letter is not the literal lift
of any original-alphabet word. More strongly, over a nonempty
original alphabet, its ordinary word span cannot CONTAIN the
entire span of a lifted original-alphabet variable word, since
the latter has an all-original-letter evaluation.

This does not refute Corollary 22, the existence of some more
special local Ramsey witness, or the corrected target Q theorem.
It isolates the real extra condition required before invoking
the paper's unrestricted enlarged-alphabet Ramsey result in the
current original-alphabet interpolation code.

Two possible repairs: generalize the final ambient f' construction
to decode genuine auxiliary CONSTANTS of the Ramsey variable
words into old-root variables; or prove a source-facing restricted
Ramsey theorem returning auxiliary-constant-free witnesses.
Neither is silently assumed here.
-/

namespace DualTree.ForwardQFinalAlphabetLiftObstruction

open ForwardQFinalMixedAlphabetSpan

/-- A variable word produced by lifting only ORIGINAL alphabet
constants can NEVER have a fixed auxiliary alphabet constant
at any ambient position, regardless of its support or of the
alphabet cardinality. -/
theorem lifted_variable_word_excludes_aux_constant
    {b n t : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (s : BoundedNode b n) (j : Fin t) :
    (mapVariableWordConstants f
      (fun a : α => (Sum.inl a : Sum α (Fin t)))).word s ≠
        Sum.inl (Sum.inr j) := by
  cases hs : f.word s with
  | inl a =>
      simp [mapVariableWordConstants, hs]
  | inr v =>
      simp [mapVariableWordConstants, hs]

/-- In particular the actual alphabet-lifted MIXED PRODUCT has
no auxiliary constant in ANY coordinate component of its defining
variable word. The up and bullet point coordinates are irrelevant. -/
theorem lifted_mixed_component_excludes_aux_constant
    {b n d k t : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (i : Fin d) (s : BoundedNode b n) (j : Fin t) :
    ((mapMixedWordConstants f
      (fun a : α => (Sum.inl a : Sum α (Fin t)))).vector.components i).word s ≠
        Sum.inl (Sum.inr j) := by
  exact lifted_variable_word_excludes_aux_constant
    (f.vector.components i).toVariableWord s j

/-- If an enlarged mixed Ramsey word has even ONE genuinely fixed
auxiliary letter, it cannot be identified with a literal constant
lift from the original alphabet. The unrestricted paper Corollary 22
has no stated premise forbidding such constants. -/
theorem enlarged_aux_constant_not_lifted_mixed_word
    {b n d k t : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → MixedProduct.CoordKind}
    (F : MixedProduct.VariableWord b n d k
      (Sum α (Fin t)) aux kind)
    (i : Fin d) (s : BoundedNode b n) (j : Fin t)
    (haux : (F.vector.components i).word s =
      Sum.inl (Sum.inr j)) :
    ¬ ∃ f : MixedProduct.VariableWord b n d k α aux kind,
        mapMixedWordConstants f
          (fun a : α => (Sum.inl a : Sum α (Fin t))) = F := by
  rintro ⟨f, hf⟩
  have hnot := lifted_mixed_component_excludes_aux_constant
    f i s j
  rw [hf] at hnot
  exact hnot haux

/-- A genuinely fixed auxiliary constant also forbids the
ENTIRE evaluated span of a lifted original-alphabet variable
word from lying inside the enlarged word's evaluated span.
Choose the actual all-fallback-original-letter evaluation of
the lifted word, which differs at the fixed auxiliary position.

This is only a word-coordinate obstruction, not a statement
about a source-free mixed Ramsey existence theorem. -/
theorem auxiliary_constant_blocks_original_lifted_word_span
    {b n t : Nat} {α : Type*}
    (F : DualTree.VariableWord b n (Sum α (Fin t)))
    (s : BoundedNode b n) (j : Fin t)
    (haux : F.word s = Sum.inl (Sum.inr j))
    (f : DualTree.VariableWord b n α)
    (fallback : α) :
    ¬ (mapVariableWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin t)))).span ⊆
      F.span := by
  intro hspan
  let w : TreeWord b n (Sum α (Fin t)) :=
    fun z => match f.word z with
      | Sum.inl a => Sum.inl a
      | Sum.inr _ => Sum.inl fallback
  have hw : w ∈
      (mapVariableWordConstants f
        (fun a : α => (Sum.inl a : Sum α (Fin t)))).span := by
    simpa only [w] using
      (mapVariableWordConstants_evaluation_mem_span
        f (fun a : α => (Sum.inl a : Sum α (Fin t)))
        (fun _ => (Sum.inl fallback : Sum α (Fin t))))
  obtain ⟨τ, hτ⟩ := hspan hw
  have hvalue : w s = Sum.inr j := by
    calc
      w s = SpanAudit.eval F.word τ s := by
        exact congrFun hτ.symm s
      _ = Sum.inr j := by
        simp [SpanAudit.eval, SpanAudit.evalSymbol, haux]
  cases hs : f.word s with
  | inl a =>
      simp [w, hs] at hvalue
  | inr v =>
      simp [w, hs] at hvalue

end DualTree.ForwardQFinalAlphabetLiftObstruction
