import DualTree.ForwardQActualCoordinateWord
import DualTree.MixedProduct

/-!
# Coordinatewise mixed-variable-span semantics of the actual Q letters

The actual corrected Q-output reads the true mixed-product coordinate
word x.words i at P_i(z), on ALL sorted outside-cut D0/D2 frontiers.

When x belongs to a mixed-product variable-word span, each coordinate
word x_i is the evaluation of its corresponding K-variable component
under some local variable assignment sigma_i. We prove that the
actual Q-output symbol at every P_i(z) is precisely the CONSTANT
carrying that evaluated local symbol, and supply simultaneous
assignment witnesses for the entire product.

Outside all frontier cones the Q word retains the old source word
verbatim. Thus the checked full-frontier output has a precise
inside/outside description on genuine members of a variable mixed
span.

CRITICAL LIMITATION: the output Q word has the old SOURCE variable
roots. This theorem does not transport the local component variables
to those old roots or prove that independent local substitutions form
a single Q-variable span of the same dimension. The full Lemma 27
Hales-Jewett/Ramsey span refinement and simplicity are still open.
-/

namespace DualTree.ForwardQMixedSpanEvaluation

open ForwardSourceQTree
open ForwardQActualCoordinateWord

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQActualCoordinateWord.Index c

/-- A single ACTUAL mixed-product coordinate belonging to a
K-variable-word span produces exactly the corresponding evaluated
local word inside its forward-corrected complete frontier cone. -/
theorem projected_symbol_of_component_span
    {b n l k m q : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (f : KVariableWord b (k - (m + 1)) q α aux)
    (i : Index c)
    (hi : x.1.words i ∈ f.span) :
    ∃ σ : f.Vars → α,
      ∀ z : BoundedNode b (k - (m + 1)),
        ((coordinateConeData c x.1 fallback).onActualStarredQ
          hb c x hTbound).word.word
          (projectedBounded c hTbound i z) =
        Sum.inl (SpanAudit.eval f.word σ z) := by
  rcases hi with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro z
  rw [coordinateConeData_Q_symbol_projected hb c x fallback hTbound i z]
  exact congrArg
    (fun a : α => (Sum.inl a : Sum α c.source.word.Vars))
    ((congrFun hσ z).symm)

/-- Source-facing specialization to an actual mixed-product
VARIABLE word of the same corrected frontier coordinate kind.
No syntactic equality of local variable supports with the OLD
Q-source support is presumed. -/
theorem projected_symbol_of_mixed_span
    {b n l k m q : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (f : MixedProduct.VariableWord b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers c.T c.cut).length q
      α aux (kind c))
    (hx : x.1 ∈ f.span)
    (i : Index c) :
    ∃ σ : (f.vector.components i).Vars → α,
      ∀ z : BoundedNode b (k - (m + 1)),
        ((coordinateConeData c x.1 fallback).onActualStarredQ
          hb c x hTbound).word.word
          (projectedBounded c hTbound i z) =
        Sum.inl (SpanAudit.eval (f.vector.components i).word σ z) :=
  projected_symbol_of_component_span hb c x fallback hTbound
    (f.vector.components i) i
    (MixedProduct.VariableWord.word_mem_of_mem_span hx i)

/-- Simultaneous local assignments witness ALL of the genuinely
independent mixed-product coordinate evaluations at once.
This is a dependent product of local assignments, NOT a single
assignment to the old Q-source variables. -/
theorem projected_symbols_of_mixed_span
    {b n l k m q : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (f : MixedProduct.VariableWord b (k - (m + 1))
      (ForwardSortedFrontiers.frontiers c.T c.cut).length q
      α aux (kind c))
    (hx : x.1 ∈ f.span) :
    ∃ σ : ∀ i : Index c, (f.vector.components i).Vars → α,
      ∀ (i : Index c) (z : BoundedNode b (k - (m + 1))),
        ((coordinateConeData c x.1 fallback).onActualStarredQ
          hb c x hTbound).word.word
          (projectedBounded c hTbound i z) =
        Sum.inl
          (SpanAudit.eval (f.vector.components i).word (σ i) z) := by
  classical
  have hwitness :
      ∀ i : Index c,
        ∃ σ : (f.vector.components i).Vars → α,
          ∀ z : BoundedNode b (k - (m + 1)),
            ((coordinateConeData c x.1 fallback).onActualStarredQ
              hb c x hTbound).word.word
              (projectedBounded c hTbound i z) =
            Sum.inl
              (SpanAudit.eval (f.vector.components i).word σ z) := by
    intro i
    exact projected_symbol_of_mixed_span hb c x fallback hTbound f hx i
  choose σ hσ using hwitness
  exact ⟨σ, fun i z => hσ i z⟩

/-- At the actual P_i(z), evaluating the corrected Q output
under ANY assignment to the old source roots produces the
same value as the corresponding LOCAL K-variable component
evaluation. Since the constructed Q symbol is a constant
there, the old-root assignment does not affect this value. -/
theorem evaluated_projected_symbol_of_component_span
    {b n l k m q : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (f : KVariableWord b (k - (m + 1)) q α aux)
    (i : Index c)
    (hi : x.1.words i ∈ f.span)
    (τ : c.source.word.Vars → α) :
    ∃ σ : f.Vars → α,
      ∀ z : BoundedNode b (k - (m + 1)),
        SpanAudit.evalSymbol τ
          (((coordinateConeData c x.1 fallback).onActualStarredQ
            hb c x hTbound).word.word
            (projectedBounded c hTbound i z)) =
          SpanAudit.eval f.word σ z := by
  rcases projected_symbol_of_component_span
      hb c x fallback hTbound f i hi with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro z
  rw [hσ z]
  rfl

/-- Outside ALL sorted complete-support frontier cones, the
source-facing actual-Q word agrees with the original source
word, even for points selected from arbitrary mixed spans. -/
theorem actual_Q_word_outside_all_frontiers
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    ((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).word.word t =
      c.source.word.word t :=
  (coordinateConeData c x.1 fallback).symbol_outside
    hb c x hTbound t ht

end DualTree.ForwardQMixedSpanEvaluation
