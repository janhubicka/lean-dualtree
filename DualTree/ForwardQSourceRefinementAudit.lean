import DualTree.ForwardQSourceRefinement
import DualTree.UnaryMainAudit

/-!
# Regression for the singleton-alphabet source contract

The syntactic Q source contract applies to a singleton alphabet, but
it must not be inferred from evaluated-span inclusion there. The
existing genuine binary-tree witnesses make the distinction explicit
at every ambient height at least two: the root-supported word and
the left-child-supported word both have 1-complete skew support and
equal evaluated spans, yet the latter is not a syntactic refinement
of the former.

We record the left-to-root obstruction needed by the new interface,
and a nonempty positive unary instance. Thus the arbitrary-alphabet
interface neither collapses to the false span-only contract nor
excludes singleton alphabets altogether.
-/

namespace DualTree.ForwardQSourceRefinementAudit

open ForwardQSourceRefinement
open UnaryMainAudit

/-- The two actual tree-variable words have identical evaluated spans
at every binary ambient height at least two. -/
theorem unary_spans_equal (n : Nat) (hn : 2 ≤ n) :
    (leftWord n hn).span = (rootWord n hn).span :=
  SpanAudit.singleton_span_eq (leftWord n hn).word (rootWord n hn).word

/-- Equal unary evaluated spans do not permit the source variable root
to move to its child under the syntactic Q refinement contract. -/
theorem unary_left_not_syntactically_refines_root
    (n : Nat) (hn : 2 ≤ n) :
    ¬ SyntacticallyRefines (leftWord n hn) (rootWord n hn) := by
  intro hRef
  have hleft : left2 n hn ∈ (leftWord n hn).support := by
    simp [leftWord, singletonVariableWord]
  have hroot := hRef.support_subset (left2 n hn) hleft
  have heq : left2 n hn = root2 n hn := by
    simpa [rootWord, singletonVariableWord] using hroot
  exact root2_ne_left2 n hn heq.symm

/-- The singleton-alphabet distinction already occurs for two genuine
1-complete skew words, not merely abstract words with unchecked supports.
It persists for every ambient height at least two. -/
theorem unary_complete_equal_span_without_syntactic_refinement
    (n : Nat) (hn : 2 ≤ n) :
    CompleteSupport SkewTree.forwardAuxB 1 (leftWord n hn) ∧
    CompleteSupport SkewTree.forwardAuxB 1 (rootWord n hn) ∧
    (leftWord n hn).span = (rootWord n hn).span ∧
    ¬ SyntacticallyRefines (leftWord n hn) (rootWord n hn) :=
  ⟨leftWord_complete n hn,
    rootWord_complete n hn,
    unary_spans_equal n hn,
    unary_left_not_syntactically_refines_root n hn⟩

/-- The repaired source predicate has an actual complete-support unary
instance with a nonempty evaluated span. The negative example concerns
the unsupported change of roots, not the availability of unary words. -/
theorem unary_syntactic_refinement_nonvacuous
    (n : Nat) (hn : 2 ≤ n) :
    CompleteSupport SkewTree.forwardAuxB 1 (rootWord n hn) ∧
    SyntacticallyRefines (rootWord n hn) (rootWord n hn) ∧
    (rootWord n hn).span.Nonempty := by
  refine ⟨rootWord_complete n hn,
    SyntacticallyRefines.refl (rootWord n hn), ?_⟩
  exact ⟨(rootWord n hn).eval (fun _ => PUnit.unit),
    ⟨fun _ => PUnit.unit, rfl⟩⟩

end DualTree.ForwardQSourceRefinementAudit
