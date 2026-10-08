import DualTree.FrontierHeightBound

/-!
# Typed three-way cone-word decoding for Lemma 27

The printed proof mixes three different kinds of symbols in a cone
word: original alphabet letters, auxiliary letters to be decoded
as visible ancestor variables (or a fallback letter), and new cone
variables whose roots must be transported into the final support.

These are distinct constructors in the enlarged alphabet and the
variable type.  This module gives the resulting exhaustive decoding
with explicit types, and checks the relevant root and fibre properties.
It does not silently interpret every non-original letter as auxiliary.
-/

namespace DualTree.ConeWordLift

/-- Letters enlarged by a disjoint finite auxiliary alphabet. -/
abbrev EnlargedLetter (α : Type*) (m : Nat) :=
  Sum α (Fin (m + 1))

/-- The exhaustive three-way translation of a local word symbol. -/
def liftSymbol
    {α Aux κ ν : Type*}
    (decodeAux : Aux → Sum α ν)
    (variableRoot : κ → ν) :
    Sum (Sum α Aux) κ → Sum α ν
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr j) => decodeAux j
  | Sum.inr v => Sum.inr (variableRoot v)

/-- Decode every position of a local word, without inspecting variable occurrences. -/
def liftWord
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν)
    (variableRoot : κ → ν) :
    ι → Sum α ν :=
  fun i => liftSymbol decodeAux variableRoot (w i)

/-- Original alphabet letters remain unchanged. -/
theorem liftWord_original
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν) (variableRoot : κ → ν)
    (i : ι) (a : α)
    (hi : w i = Sum.inl (Sum.inl a)) :
    liftWord w decodeAux variableRoot i = Sum.inl a := by
  simp [liftWord, liftSymbol, hi]

/-- An auxiliary letter is decoded by the designated map, never as a cone variable. -/
theorem liftWord_auxiliary
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν) (variableRoot : κ → ν)
    (i : ι) (j : Aux)
    (hi : w i = Sum.inl (Sum.inr j)) :
    liftWord w decodeAux variableRoot i = decodeAux j := by
  simp [liftWord, liftSymbol, hi]

/-- Every cone variable is transported to its target root. -/
theorem liftWord_variable
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν) (variableRoot : κ → ν)
    (i : ι) (v : κ)
    (hi : w i = Sum.inr v) :
    liftWord w decodeAux variableRoot i = Sum.inr (variableRoot v) := by
  simp [liftWord, liftSymbol, hi]

/--
Distinct occurrences of the same local variable receive identical
symbols.  The decoding is done on the variable name, not its position.
-/
theorem liftWord_variable_fibre
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν) (variableRoot : κ → ν)
    (v : κ) (i j : ι)
    (hi : w i = Sum.inr v) (hj : w j = Sum.inr v) :
    liftWord w decodeAux variableRoot i =
      liftWord w decodeAux variableRoot j := by
  rw [liftWord_variable w decodeAux variableRoot i v hi,
      liftWord_variable w decodeAux variableRoot j v hj]

/-- Evaluation of the decoded word respects all three symbol constructors. -/
theorem eval_liftWord
    {ι α Aux κ ν : Type*}
    (w : ι → Sum (Sum α Aux) κ)
    (decodeAux : Aux → Sum α ν) (variableRoot : κ → ν)
    (τ : ν → α) :
    SpanAudit.eval (liftWord w decodeAux variableRoot) τ =
      fun i =>
        match w i with
        | Sum.inl (Sum.inl a) => a
        | Sum.inl (Sum.inr j) =>
            SpanAudit.evalSymbol τ (decodeAux j)
        | Sum.inr v => τ (variableRoot v) := by
  funext i
  cases hw : w i with
  | inl a =>
      cases a with
      | inl c => simp [SpanAudit.eval, SpanAudit.evalSymbol,
          liftWord, liftSymbol, hw]
      | inr j =>
          cases hd : decodeAux j with
          | inl c => simp [SpanAudit.eval, SpanAudit.evalSymbol,
              liftWord, liftSymbol, hw, hd]
          | inr v => simp [SpanAudit.eval, SpanAudit.evalSymbol,
              liftWord, liftSymbol, hw, hd]
  | inr v =>
      simp [SpanAudit.eval, SpanAudit.evalSymbol,
        liftWord, liftSymbol, hw]

/--
Use the repaired cone-local decoder for auxiliary letters while
transporting genuine cone variables independently to their roots.
-/
noncomputable def liftAtCone
    {b m : Nat} {ι κ α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : ι → Sum (EnlargedLetter α m) κ)
    (variableRoot : κ → Node b) :
    ι → Sum α (Node b) :=
  liftWord w
    (ConeLocalDecoder.decodeRoot T I frontier a hfront)
    variableRoot

/-- An auxiliary symbol cannot decode to a variable outside the ancestor chain. -/
theorem liftAtCone_aux_prefix
    {b m : Nat} {ι κ α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : ι → Sum (EnlargedLetter α m) κ)
    (variableRoot : κ → Node b)
    (i : ι) (j : Fin (m + 1)) (r : Node b)
    (hi : w i = Sum.inl (Sum.inr j))
    (hr : liftAtCone T I frontier a hfront w variableRoot i = Sum.inr r) :
    IsStrictPrefix r frontier := by
  have hdecode :
      ConeLocalDecoder.decodeRoot T I frontier a hfront j = Sum.inr r := by
    simpa [liftAtCone, liftWord, liftSymbol, hi] using hr
  exact ConeLocalDecoder.decodeRoot_prefix T I frontier a hfront j r hdecode

/-- Genuine variables retain their independently specified transported roots. -/
theorem liftAtCone_variable
    {b m : Nat} {ι κ α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : ι → Sum (EnlargedLetter α m) κ)
    (variableRoot : κ → Node b)
    (i : ι) (v : κ)
    (hi : w i = Sum.inr v) :
    liftAtCone T I frontier a hfront w variableRoot i =
      Sum.inr (variableRoot v) := by
  exact liftWord_variable w
    (ConeLocalDecoder.decodeRoot T I frontier a hfront)
    variableRoot i v hi

/--
At an actual minimal outside-cut frontier, no extra height
hypothesis is needed for the well-typed three-way decoding.
-/
noncomputable def liftAtFrontier
    {b k m : Nat} {ι κ α : Type*}
    (T I : List (Node b)) (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier)
    (hcutHeight : SkewTree.heightAt T cut = m)
    (a : α)
    (w : ι → Sum (EnlargedLetter α m) κ)
    (variableRoot : κ → Node b) :
    ι → Sum α (Node b) :=
  liftAtCone T I frontier a
    (FrontierHeightBound.frontier_height_le_m_succ
      T cut frontier hcomplete hcut hlevel hf hcutHeight)
    w variableRoot

end DualTree.ConeWordLift
