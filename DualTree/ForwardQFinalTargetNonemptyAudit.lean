import DualTree.ForwardQFinalTargetHeightBoundary

/-!
# An inhabited starred target class at local height two

This is a positive, genuinely binary instance of the corrected Q transfer.
The ambient support contains all nodes of lengths zero, one and two. The
source tree is the root and its two children; its sole variable occurs only
at the root, with `false` at every other position. Every local coordinate
has the full height-two support and a separate variable at each root.

The actual enlarged final interpolation retains the source tree. Its
variable occurrences remain at their own roots and its only constant is
`false`, so the source word is an explicit syntactic refinement. Taking
the original source as target makes equality of the complete signature
literal, without any change to its list representation. The resulting Q
preimage belongs to the genuine starred mixed span.
-/

namespace DualTree.ForwardQFinalTargetNonemptyAudit

open ForwardSourceQTree
open ForwardQSourceRefinement
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalSafeAddressLookup
open ForwardQFinalEnlargedLocalSymbols
open ForwardQFinalGlobalEnlargedWord
open ForwardQFinalSyntacticSpanTransfer

/-- A support word whose variables occur only at their own roots. -/
private noncomputable def pointWord
    {b n : Nat} {α : Type*}
    (S : List (BoundedNode b n)) (hS : S.Nodup) (a : α) :
    VariableWord b n α := by
  classical
  exact {
    support := S
    support_nodup := hS
    word := fun s => if hs : s ∈ S then Sum.inr ⟨s, hs⟩ else Sum.inl a
    atRoot := by
      intro v
      simp [v.2]
    below := by
      intro v s h
      split_ifs at h with hs
      · have heq : s = v.1 := congrArg Subtype.val (Sum.inr.inj h)
        rw [heq]
        exact isPrefix_refl v.1.1
      · cases h
  }

private theorem pointWord_constant
    {b n : Nat} {α : Type*}
    (S : List (BoundedNode b n)) (hS : S.Nodup) (a c : α)
    (s : BoundedNode b n)
    (h : (pointWord S hS a).word s = Sum.inl c) : c = a := by
  classical
  by_cases hs : s ∈ S
  · simp [pointWord, hs] at h
  · simpa [pointWord, hs] using h.symm

private theorem pointWord_variable
    {b n : Nat} {α : Type*}
    (S : List (BoundedNode b n)) (hS : S.Nodup) (a : α)
    (s : BoundedNode b n) (v : (pointWord S hS a).Vars)
    (h : (pointWord S hS a).word s = Sum.inr v) : v.1 = s := by
  classical
  by_cases hs : s ∈ S
  · have heq : (⟨s, hs⟩ : (pointWord S hS a).Vars) = v := by
      apply Sum.inr.inj
      simpa [pointWord, hs] using h
    exact (congrArg Subtype.val heq).symm
  · simp [pointWord, hs] at h

private def root3 : BoundedNode 2 3 := ⟨[], by decide⟩

private def root2 : BoundedNode 2 2 := ⟨[], by decide⟩

private def smallTree : List (Node 2) := [[], [0], [1]]

private def fullTree : List (Node 2) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

private def ambientRoots : List (BoundedNode 2 3) :=
  [root3, ⟨[0], by decide⟩, ⟨[1], by decide⟩,
    ⟨[0, 0], by decide⟩, ⟨[0, 1], by decide⟩,
    ⟨[1, 0], by decide⟩, ⟨[1, 1], by decide⟩]

private def localRoots : List (BoundedNode 2 2) :=
  [root2, ⟨[0], by decide⟩, ⟨[1], by decide⟩]

/-- The binary source has an actual one-variable starred tree. Its
variable is not repeated at the nonroot ambient positions. -/
noncomputable def binarySource :
    StarredSignature.StarredWord 2 3 1 Bool SkewTree.forwardAuxB where
  tree := smallTree
  tree_bounded := by
    intro t ht
    simp [smallTree] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  semi_complete := by decide
  word := pointWord [root3] (by simp) false
  interior_card := by decide
  support_eq_interior := by
    intro t
    have hI : SkewTree.interior smallTree = ([[]] : List (Node 2)) := by decide
    simp [VariableWord.supportNodes, pointWord, root3, hI]
  support_skew := by
    intro _
    change SkewTree.skewB SkewTree.forwardAuxB ([[]] : List (Node 2)) = true
    decide

/-- A complete support of height three enclosing the actual source. -/
noncomputable def binaryCore : Frame 2 3 1 3 0 Bool where
  source := binarySource
  cut := []
  hcut := by decide
  hmax := by
    intro t ht
    have hI : SkewTree.interior binarySource.tree =
        ([[]] : List (Node 2)) := by decide
    have ht0 : t = [] := by simpa [hI] using ht
    subst t
    decide
  hout := by
    intro t ht
    have hn := (StarredSignature.exceptionalLeaves_spec binarySource [] t ht).2.2
    exact False.elim (hn ⟨t, by simp⟩)
  T := fullTree
  hcomplete := by decide
  hnon := by decide
  hST := by
    intro t ht
    simp [binarySource, smallTree] at ht
    rcases ht with rfl | rfl | rfl <;> simp [fullTree]
  hcutT := by simp [fullTree]
  hearly := by decide
  hm := by decide

/-- Independent ambient variables on the full binary support. -/
noncomputable def binaryAmbient : VariableWord 2 3 Bool :=
  pointWord ambientRoots (by decide) false

private theorem ambient_support :
    ∀ t : Node 2, t ∈ binaryAmbient.supportNodes ↔ t ∈ binaryCore.T := by
  intro t
  rfl

private theorem source_refines_ambient :
    SyntacticallyRefines binarySource.word binaryAmbient := by
  classical
  refine ⟨fun v => binarySource.word.word v.1, ?_⟩
  funext s
  by_cases hs : s ∈ ambientRoots
  · simp [binaryAmbient, pointWord, SpanAudit.substitute, hs]
  · have hs0 : s ≠ root3 := by
      intro heq
      exact hs (by simp [heq, ambientRoots])
    simp [binarySource, binaryAmbient, pointWord, SpanAudit.substitute, hs, hs0]

/-- The complete source frame includes the actual ambient word and
the explicit uniform substitution producing the source. -/
noncomputable def binaryFrame :
    ForwardQAmbientFibreFrame.FibreFrame 2 3 1 3 0 Bool :=
  fibreFrameOfSyntactic binaryCore binaryAmbient ambient_support source_refines_ambient

private noncomputable def localComponent :
    KVariableWord 2 2 2 (Sum Bool (Fin 1)) SkewTree.forwardAuxB where
  toVariableWord := pointWord localRoots (by decide) (Sum.inl false)
  complete_support := by decide

private theorem identical_local_supports_vector_complete (d : Nat) :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 2
      (fun _ : Fin d => localComponent.toVariableWord.supportNodes) = true := by
  have hc : SkewTree.completeB SkewTree.forwardAuxB 2 smallTree = true := by decide
  have hs : (List.range 2).all (fun m =>
      (VectorSkew.levelNodes smallTree m).all (fun s =>
        (VectorSkew.levelNodes smallTree m).all (fun t =>
          decide (s.length ≤ t.length)))) = true := by decide
  have ht : (VectorSkew.levelNodes smallTree 0).all (fun s =>
      (VectorSkew.levelNodes smallTree 1).all (fun t =>
        decide (s.length < t.length))) = true := by decide
  change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 2
    (fun _ : Fin d => smallTree) = true
  simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr (fun _ _ => hc)
  · unfold VectorSkew.sameLevelOrderedB
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    split_ifs
    · exact hs
    · rfl
  · unfold VectorSkew.successiveLevelsSeparatedB
    apply List.all_eq_true.mpr
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst m
    apply List.all_eq_true.mpr
    intro i _
    exact List.all_eq_true.mpr (fun _ _ => ht)

/-- A genuine height-two local mixed word, on every actual sorted
frontier coordinate. There are no up coordinates in the corrected Q domain. -/
noncomputable def binaryLocalWord :
    LocalMixedWord binaryFrame.core 2 (Sum Bool (Fin (0+1))) := by
  have hno : ∀ i : Index binaryCore, kind binaryCore i ≠ MixedProduct.CoordKind.up := by
    intro i
    exact ForwardSortedMixedProduct.kind_ne_up
      binaryCore.source binaryCore.cut binaryCore.hcut binaryCore.hmax binaryCore.hout
      binaryCore.T binaryCore.hcomplete binaryCore.hnon binaryCore.hST
      binaryCore.hcutT binaryCore.hearly i
  exact {
    vector := {
      components := fun _ => localComponent
      vector_complete := identical_local_supports_vector_complete _
    }
    upLeaves := fun i => False.elim (hno i.1 i.2)
    upLeaves_nodup := fun i => False.elim (hno i.1 i.2)
    upLeaves_card := fun i => False.elim (hno i.1 i.2)
    up_support_skew := fun i => False.elim (hno i.1 i.2)
  }

/-- The actual enlarged interpolation, with local height exactly two. -/
noncomputable def binaryFinalWord : VariableWord 2 3 Bool :=
  enlargedInterpolatedFinalWord binaryFrame binaryLocalWord false

private theorem root_mem_final : root3 ∈ binaryFinalWord.support := by
  let u : binaryFrame.ambient.Vars := ⟨root3, by simp [binaryFrame,
    fibreFrameOfSyntactic, binaryAmbient, pointWord, ambientRoots]⟩
  exact ForwardQFinalInitialRootRetention.enlargedFinal_retains_initial_roots
    binaryFrame binaryLocalWord false u (by decide)

private theorem child_frontier (a : Fin 2) :
    CutFrontier.Frontier binaryCore.T
      (fun u => ForwardAux u binaryCore.cut) [a] := by
  refine ⟨?_, ?_, ?_⟩
  · fin_cases a <;> simp [binaryCore, fullTree]
  · simp [binaryCore, ForwardAux]
  · intro r _ hr
    have hr0 : r = [] := by
      rcases hr.1 with ⟨tail, heq⟩
      cases r with
      | nil => rfl
      | cons x xs =>
          cases tail with
          | nil => exact False.elim (hr.2 (by simpa using heq.symm))
          | cons y ys =>
              have hlen := congrArg List.length heq
              simp only [List.length_cons, List.length_append] at hlen
              omega
    subst r
    change ForwardAux ([] : Node 2) []
    decide

private theorem projected_empty (i : Index binaryCore) :
    (projected binaryCore ⟨i, root2⟩).1 =
      (ForwardOrderedProjections.frontierAt binaryCore.T binaryCore.cut i).1 := by
  exact congrArg Subtype.val (ForwardCanonicalConeCoordinates.project_empty
    binaryCore.T binaryCore.hcomplete binaryCore.hnon
    (ForwardOrderedProjections.frontierAt binaryCore.T binaryCore.cut i))

private theorem child_mem_final (a : Fin 2) :
    [a] ∈ binaryFinalWord.supportNodes := by
  classical
  have hmem : [a] ∈ ForwardSortedFrontiers.frontiers binaryCore.T binaryCore.cut :=
    (ForwardSortedFrontiers.mem_frontiers_iff _ _ _).2 (child_frontier a)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  have hfront : (ForwardOrderedProjections.frontierAt
      binaryCore.T binaryCore.cut i).1 = [a] := hi
  have hselected : (⟨i, root2⟩ : LocalAddress binaryCore) ∈
      selectedLocalRoots binaryCore binaryLocalWord 2 := by
    apply (selectedLocalRoots_mem_iff binaryCore binaryLocalWord 2 ⟨i, root2⟩).2
    constructor
    · apply (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
        binaryCore binaryLocalWord i root2).2
      simp [binaryLocalWord, localComponent, pointWord, localRoots]
    · change SkewTree.heightAt smallTree [] +
        SkewTree.heightAt fullTree
          (ForwardOrderedProjections.frontierAt binaryCore.T binaryCore.cut i).1 < 2
      rw [hfront]
      fin_cases a <;> decide
  apply (ForwardQFinalEnlargedCompleteWord.enlargedInterpolatedFinalWord_supportNodes_iff
    binaryFrame binaryLocalWord false [a]).2
  change [a] ∈ ForwardQFinalSupportCut.retained binaryCore ∪
    selectedProjectedRoots binaryCore binaryLocalWord 2
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  exact ⟨⟨i, root2⟩, hselected, (projected_empty i).trans hfront⟩

/-- Both terminal children, as well as the source variable root,
belong to the actual final support. -/
theorem binary_source_tree_in_final :
    ∀ t, t ∈ binarySource.tree → t ∈ binaryFinalWord.supportNodes := by
  intro t ht
  simp [binarySource, smallTree] at ht
  rcases ht with rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨root3, root_mem_final, rfl⟩
  · exact child_mem_final 0
  · exact child_mem_final 1

private theorem global_constant
    (u : binaryFrame.ambient.Vars) (a : Bool)
    (h : enlargedGlobalRootSymbol binaryFrame binaryLocalWord false u = Sum.inl a) :
    a = false := by
  classical
  cases hs : safeAddress binaryCore u.1.1 with
  | none =>
      by_cases hu : u.1 ∈ boundedFinalRoots binaryFrame binaryLocalWord
      · simp [enlargedGlobalRootSymbol, hs, hu] at h
      · simpa [enlargedGlobalRootSymbol, hs, hu] using h.symm
  | some z =>
      rcases z with ⟨i, z⟩
      by_cases hz : z ∈ localRoots
      · by_cases hsel : (⟨i, z⟩ : LocalAddress binaryCore) ∈
            selectedLocalRoots binaryCore binaryLocalWord 2
        · simp [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
            binaryLocalWord, localComponent, pointWord, hz, hsel] at h
        · simpa [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
            binaryLocalWord, localComponent, pointWord, hz, hsel] using h.symm
      · simpa [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
          binaryLocalWord, localComponent, pointWord, hz] using h.symm

private theorem global_variable
    (u : binaryFrame.ambient.Vars) (v : FinalRoot binaryFrame binaryLocalWord)
    (h : enlargedGlobalRootSymbol binaryFrame binaryLocalWord false u = Sum.inr v) :
    v.1 = u.1 := by
  classical
  cases hs : safeAddress binaryCore u.1.1 with
  | none =>
      by_cases hu : u.1 ∈ boundedFinalRoots binaryFrame binaryLocalWord
      · have heq : (⟨u.1, hu⟩ : FinalRoot binaryFrame binaryLocalWord) = v := by
          apply Sum.inr.inj
          simpa [enlargedGlobalRootSymbol, hs, hu] using h
        exact (congrArg Subtype.val heq).symm
      · simp [enlargedGlobalRootSymbol, hs, hu] at h
  | some z =>
      rcases z with ⟨i, z⟩
      by_cases hz : z ∈ localRoots
      · by_cases hsel : (⟨i, z⟩ : LocalAddress binaryCore) ∈
            selectedLocalRoots binaryCore binaryLocalWord 2
        · have heq : selectedBoundedRoot binaryFrame binaryLocalWord
              ⟨⟨i, z⟩, hsel⟩ = v := by
            apply Sum.inr.inj
            simpa [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
              binaryLocalWord, localComponent, pointWord, hz, hsel] using h
          apply Subtype.ext
          rw [← heq, selectedBoundedRoot_node]
          exact safeAddress_spec binaryCore u.1.1 ⟨i, z⟩ hs
        · simp [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
            binaryLocalWord, localComponent, pointWord, hz, hsel] at h
      · simp [enlargedGlobalRootSymbol, hs, enlargedLocalSymbol,
          binaryLocalWord, localComponent, pointWord, hz] at h

private theorem final_constant (s : BoundedNode 2 3) (a : Bool)
    (h : binaryFinalWord.word s = Sum.inl a) : a = false := by
  change SpanAudit.substitute binaryFrame.ambient.word
    (enlargedGlobalRootSymbol binaryFrame binaryLocalWord false) s = Sum.inl a at h
  cases hw : binaryFrame.ambient.word s with
  | inl c =>
      have hc : c = false := pointWord_constant ambientRoots (by decide) false c s hw
      have ha : c = a := by simpa [SpanAudit.substitute, hw] using h
      exact ha.symm.trans hc
  | inr u =>
      exact global_constant u a (by simpa [SpanAudit.substitute, hw] using h)

private theorem final_variable (s : BoundedNode 2 3) (v : binaryFinalWord.Vars)
    (h : binaryFinalWord.word s = Sum.inr v) : v.1 = s := by
  change SpanAudit.substitute binaryFrame.ambient.word
    (enlargedGlobalRootSymbol binaryFrame binaryLocalWord false) s = Sum.inr v at h
  cases hw : binaryFrame.ambient.word s with
  | inl c => simp [SpanAudit.substitute, hw] at h
  | inr u =>
      have hu : u.1 = s := pointWord_variable ambientRoots (by decide) false s u hw
      have hv : v.1 = u.1 := global_variable u v
        (by simpa [SpanAudit.substitute, hw] using h)
      exact hv.trans hu

/-- An explicit uniform substitution keeps the root variable and
freezes every other final root to `false`. -/
theorem binary_source_syntactically_refines_final :
    SyntacticallyRefines binarySource.word binaryFinalWord := by
  classical
  refine ⟨fun v => binarySource.word.word v.1, ?_⟩
  funext s
  cases hs : binaryFinalWord.word s with
  | inl a =>
      have ha : a = false := final_constant s a hs
      have hn : s ≠ root3 := by
        intro heq
        have hr := binaryFinalWord.atRoot ⟨root3, root_mem_final⟩
        have hsRoot : binaryFinalWord.word root3 = Sum.inl a := by
          simpa only [heq] using hs
        rw [hsRoot] at hr
        cases hr
      simp [SpanAudit.substitute, hs, ha, binarySource, pointWord, hn]
  | inr v =>
      have hv : v.1 = s := final_variable s v hs
      simp [SpanAudit.substitute, hs, hv]

/-- The local-height-two target class has an actual starred member,
with its complete signature equal literally to that of the source. -/
theorem binary_q2_sourceRelativeTarget :
    SourceRelativeTarget (by decide : 0 < 2) binaryFrame binaryFinalWord binarySource := by
  refine ⟨[], ?_, binary_source_syntactically_refines_final, binary_source_tree_in_final⟩
  exact {
    cutInterior := binaryCore.hcut
    cutMaximal := binaryCore.hmax
    signatureEq := rfl
  }

/-- Positive starred-target nonemptiness, separate from nonemptiness
of the final word's evaluated constant span. -/
theorem binary_q2_target_class_nonempty :
    {O : StarredSignature.StarredWord 2 3 1 Bool SkewTree.forwardAuxB |
      SourceRelativeTarget (by decide : 0 < 2) binaryFrame binaryFinalWord O}.Nonempty :=
  ⟨binarySource, binary_q2_sourceRelativeTarget⟩

/-- The inhabited target class yields a genuine starred enlarged Q
input in the actual local mixed span, reproducing both the tree and word. -/
theorem binary_q2_has_actual_Q_preimage :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput binaryFrame.core false,
      w.1 ∈ binaryLocalWord.span ∧
      ForwardQFinalTargetObservation.observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            (by decide) binaryFrame false w) =
        ForwardQFinalTargetObservation.observe binarySource := by
  exact sourceRelativeTarget_has_Q_preimage (by decide) binaryFrame binaryLocalWord
    false binarySource binary_q2_sourceRelativeTarget

/-- The concrete positive target also belongs to the mathematical
set-signature class, independently of its list representation. -/
theorem binary_q2_sourceRelativeSetTarget :
    ForwardQFinalSetSpanTransfer.SourceRelativeSetTarget
      (by decide : 0 < 2) binaryFrame binaryFinalWord binarySource :=
  ForwardQFinalSetSpanTransfer.sourceRelativeSetTarget_of_literal
    binary_q2_sourceRelativeTarget

/-- The full finite-set-signature target class is genuinely inhabited
in the binary local-height-two instance. -/
theorem binary_q2_set_target_class_nonempty :
    {O : StarredSignature.StarredWord 2 3 1 Bool SkewTree.forwardAuxB |
      ForwardQFinalSetSpanTransfer.SourceRelativeSetTarget
        (by decide : 0 < 2) binaryFrame binaryFinalWord O}.Nonempty :=
  ⟨binarySource, binary_q2_sourceRelativeSetTarget⟩

/-- The set-signature transfer itself yields an actual starred Q
preimage for the positive binary example. -/
theorem binary_q2_has_actual_set_Q_preimage :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput binaryFrame.core false,
      w.1 ∈ binaryLocalWord.span ∧
      ForwardQFinalTargetObservation.observe
          (ForwardQAmbientFibreLegalWord.fibreQStarredWord
            (by decide) binaryFrame false w) =
        ForwardQFinalTargetObservation.observe binarySource := by
  exact ForwardQFinalSetSpanTransfer.sourceRelativeSetTarget_has_Q_preimage
    (by decide) binaryFrame binaryLocalWord false binarySource
    binary_q2_sourceRelativeSetTarget

end DualTree.ForwardQFinalTargetNonemptyAudit
