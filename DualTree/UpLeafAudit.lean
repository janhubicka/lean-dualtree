import DualTree.MixedGood
import DualTree.FixedRootMarkerWord
import DualTree.VectorSingletonComplete

/-!
# Adversarial tests for genuine height-one up-leaf geometry

The up-leaf condition is stronger than selecting `b` distinct nodes at the
ambient level. For a singleton variable support, the leaves must cover every
direction immediately above its root. These finite fixtures use the actual
source-facing skew checker, with both auxiliary orders, and are checked by the
Lean kernel.

A further theorem records a separate nonvacuity boundary: when `b = 0`, the
mixed-word definition requires an empty up-leaf list at intrinsic height one.
Thus the presence of an actual D1 coordinate forces the mixed span to be empty.
Positive D1 existence results must exclude this case.

A genuine binary one-up mixed word also shows that the geometric construction
is not automatically c-good: the two selected leaves can have different colors.
This is an obstruction for a prescribed root and leaf set, not a counterexample
to a Ramsey theorem that is free to select a different root at greater height.
-/

namespace DualTree.UpLeafAudit

open SkewTree MixedProduct

/-- Two genuine ambient-level leaves, one in each direction above `[1]`. -/
def binaryLeaves : List (LeafNode 2 3) :=
  [⟨[1, 0, 0], rfl⟩, ⟨[1, 1, 1], rfl⟩]

def binaryExtendedSupport : List (Node 2) :=
  [[1]] ++ binaryLeaves.map Subtype.val

theorem binaryLeaves_nodup : binaryLeaves.Nodup := by
  decide

theorem binaryLeaves_card : binaryLeaves.length = 2 ^ 1 := by
  decide

theorem binaryExtendedSupport_paper_skew :
    skewB paperAuxB binaryExtendedSupport = true := by
  decide

theorem binaryExtendedSupport_forward_skew :
    skewB forwardAuxB binaryExtendedSupport = true := by
  decide

/-- Distinct leaves of the right height and cardinality can miss a direction. -/
def uncoveredLeaves : List (LeafNode 2 2) :=
  [⟨[0, 0], rfl⟩, ⟨[0, 1], rfl⟩]

def uncoveredExtendedSupport : List (Node 2) :=
  [[]] ++ uncoveredLeaves.map Subtype.val

theorem uncoveredLeaves_nodup : uncoveredLeaves.Nodup := by
  decide

theorem uncoveredLeaves_card : uncoveredLeaves.length = 2 ^ 1 := by
  decide

theorem uncoveredExtendedSupport_rooted :
    rootedB uncoveredExtendedSupport = true := by
  decide

theorem uncoveredExtendedSupport_length_clauses :
    condIIB uncoveredExtendedSupport = true ∧
    condIIIB uncoveredExtendedSupport = true := by
  decide

theorem uncoveredExtendedSupport_not_paper_skew :
    skewB paperAuxB uncoveredExtendedSupport = false := by
  decide

theorem uncoveredExtendedSupport_not_forward_skew :
    skewB forwardAuxB uncoveredExtendedSupport = false := by
  decide

/-- The selected leaves must belong to the cone above the variable root. -/
def outsideConeExtendedSupport : List (Node 2) :=
  [[0], [0, 0], [1, 0]]

theorem outsideConeExtendedSupport_not_rooted :
    rootedB outsideConeExtendedSupport = false := by
  decide

theorem outsideConeExtendedSupport_not_paper_skew :
    skewB paperAuxB outsideConeExtendedSupport = false := by
  decide

theorem outsideConeExtendedSupport_not_forward_skew :
    skewB forwardAuxB outsideConeExtendedSupport = false := by
  decide

/-- Unary branching is allowed when the ambient leaf is strictly above the root. -/
def unaryExtendedSupport : List (Node 1) :=
  [[0], [0, 0, 0]]

theorem unaryExtendedSupport_paper_skew :
    skewB paperAuxB unaryExtendedSupport = true := by
  decide

theorem unaryExtendedSupport_forward_skew :
    skewB forwardAuxB unaryExtendedSupport = true := by
  decide

/-- At equal height, the unary leaf would repeat the root, violating Nodup. -/
theorem unary_equal_height_not_skew :
    skewB paperAuxB ([[0], [0]] : List (Node 1)) = false ∧
    skewB forwardAuxB ([[0], [0]] : List (Node 1)) = false := by
  decide

/-- A real up coordinate cannot produce a span element from an empty leaf list. -/
theorem span_empty_of_upLeaves_empty
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool} {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k α aux kind)
    (i : UpIndex kind) (hi : f.upLeaves i = []) :
    f.span = ∅ := by
  ext x
  constructor
  · intro hx
    have hmem := hx.2.1 i
    simpa [hi] using hmem
  · intro hx
    exact False.elim hx

/-- Zero branching makes every genuine height-one D1 mixed span empty. -/
theorem zero_branch_up_span_empty
    {n d : Nat} {α : Type*}
    {aux : Node 0 → Node 0 → Bool} {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord 0 n d 1 α aux kind)
    (i : UpIndex kind) :
    f.span = ∅ := by
  apply span_empty_of_upLeaves_empty f i
  apply List.length_eq_zero.mp
  simpa using f.upLeaves_card i

/-- The degenerate case is actually inhabited; its empty span is not a
consequence of contradictory mixed-word assumptions. -/
def zeroBranchRoot : BoundedNode 0 1 :=
  ⟨[], by simp [InHomTree]⟩

noncomputable def zeroBranchMixedWord :
    MixedProduct.VariableWord 0 1 1 1 Unit forwardAuxB (fun _ => CoordKind.up) where
  vector :=
    { components := fun _ => FixedRootMarkerWord.kWord zeroBranchRoot ()
      vector_complete := by
        change VectorSkew.vectorCompleteB forwardAuxB 1
          (fun _ : Fin 1 => [[]]) = true
        exact VectorSkew.identical_singletons_vectorComplete_one _ [] }
  upLeaves := fun _ => []
  upLeaves_nodup := fun _ => by simp
  upLeaves_card := fun _ => by simp
  up_support_skew := by
    intro i
    change skewB forwardAuxB [[]] = true
    exact singleton_skewB _ []

theorem zeroBranchMixedWord_span_empty :
    zeroBranchMixedWord.span = ∅ :=
  zero_branch_up_span_empty zeroBranchMixedWord ⟨0, rfl⟩

def binaryLevelOneRoot : BoundedNode 2 1 :=
  ⟨[], by simp [InHomTree]⟩

/-- A real one-up word with two actual ambient leaves and a nonempty alphabet. -/
noncomputable def fixedRootBinaryWord :
    MixedProduct.VariableWord 2 1 1 1 Bool forwardAuxB (fun _ => CoordKind.up) where
  vector :=
    { components := fun _ => FixedRootMarkerWord.kWord binaryLevelOneRoot false
      vector_complete := by
        change VectorSkew.vectorCompleteB forwardAuxB 1
          (fun _ : Fin 1 => [[]]) = true
        exact VectorSkew.identical_singletons_vectorComplete_one _ [] }
  upLeaves := fun _ => [⟨[0], rfl⟩, ⟨[1], rfl⟩]
  upLeaves_nodup := fun _ => by decide
  upLeaves_card := fun _ => by decide
  up_support_skew := by
    intro i
    change skewB forwardAuxB [[], [0], [1]] = true
    decide

noncomputable def fixedRootBinaryPoint (j : Fin 2) :
    Element 2 1 1 Bool (fun _ => CoordKind.up) where
  words := fun _ => FixedRootMarkerWord.valueWord binaryLevelOneRoot false false
  upPoint := fun _ => ⟨[j], rfl⟩
  bulletPoint := by
    intro i
    cases i.2

theorem fixedRootBinaryPoint_mem_span (j : Fin 2) :
    fixedRootBinaryPoint j ∈ fixedRootBinaryWord.span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact FixedRootMarkerWord.valueWord_mem_span binaryLevelOneRoot false false
  · intro i
    change (⟨[j], rfl⟩ : LeafNode 2 1) ∈ [⟨[0], rfl⟩, ⟨[1], rfl⟩]
    fin_cases j <;> simp
  · intro i
    cases i.2

/-- Observe just the selected leaf's first branch, ignoring the entire word. -/
def leafColor (x : Element 2 1 1 Bool (fun _ => CoordKind.up)) : Option (Fin 2) :=
  (x.upPoint ⟨0, rfl⟩).1.head?

theorem leafColor_fixedRootBinaryPoint (j : Fin 2) :
    leafColor (fixedRootBinaryPoint j) = some j := rfl

/-- Genuine support, leaf geometry and nonempty span do not imply c-goodness
for an arbitrary coloring on this prescribed root-and-leaf configuration. -/
theorem fixedRootBinaryWord_not_good :
    ¬ Good leafColor fixedRootBinaryWord := by
  intro hgood
  have hcolor := hgood
    (fixedRootBinaryPoint_mem_span 0) (fixedRootBinaryPoint_mem_span 1)
    (fun i => by cases i.2) (fun i => by cases i.2)
  change some (0 : Fin 2) = some (1 : Fin 2) at hcolor
  have hne : some (0 : Fin 2) ≠ some (1 : Fin 2) := by decide
  exact hne hcolor

end DualTree.UpLeafAudit
