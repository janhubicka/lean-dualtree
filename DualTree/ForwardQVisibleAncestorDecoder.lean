import DualTree.ForwardQFullFrontierThreeWay
import DualTree.ForwardFrontierRanks
import DualTree.ConeLocalDecoder

/-!
# A concrete visible-ancestor auxiliary decoder on corrected frontiers

The printed Lemma 27 uses m+1 auxiliary symbols at each minimal
outside-cut complete-support frontier. An unrestricted map to all
source interior roots may be impossible and geometrically illegal.
The correct per-frontier targets are exactly the old variable roots
that are strict support predecessors of that frontier.

This module constructs a concrete typed decoder into the ACTUAL old
source variable subtype, proves the required m+1 source bound and
strict root-prefix alignment, and verifies coverage of all visible
roots when the list is nonempty.

Raw cone words can be arbitrary outside their own frontier cones:
we mask those irrelevant symbols to a fallback original letter.
Inside the frontier the original raw word is retained. This yields
the auxiliary-alignment field of the real all-frontier ConeData,
leaving only alignment of genuine transported cone variables as
an explicit further hypothesis.

This is a genuine part of the paper-specific R_i repair, but the
unproved cone-variable transport, original word substitution,
induced colouring smoothness and Ramsey span still remain.
-/

namespace DualTree.ForwardQVisibleAncestorDecoder

open ForwardSourceQTree
open ForwardQFullFrontierWord

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The actual source interior roots that lie strictly above
the selected minimal outside-cut complete-support frontier. -/
noncomputable def visibleList
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) : List (Node b) :=
  Lemma27Repair.visibleAncestors
    c.T c.source.word.supportNodes
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1

/-- A corrected minimal frontier has T rank at most m+1,
exactly the numeric resource needed for m+1 auxiliary symbols. -/
theorem frontier_height_le_m_succ
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c) :
    SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 ≤
        m + 1 := by
  have hparts := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hbound :=
    ForwardFrontierRanks.frontier_rank_le_cut_succ
      c.T hparts.1 c.hnon c.cut
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      c.hcutT
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut i)
  simpa [c.hm] using hbound

/-- A visible root belongs to the ACTUAL original variable-root
list, not merely to an unconstrained node type. -/
theorem visibleList_get_mem_supportNodes
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (j : Fin (visibleList c i).length) :
    (visibleList c i).get j ∈ c.source.word.supportNodes := by
  exact (ConeLocalDecoder.visibleAncestor_spec
    c.T c.source.word.supportNodes
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1
    ((visibleList c i).get j)
    (List.get_mem (visibleList c i) j)).2.1

/-- Any source support node determines an actual old source
variable whose bounded root has exactly this underlying node. -/
theorem exists_variable_at_support_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b)
    (hr : r ∈ c.source.word.supportNodes) :
    ∃ v : c.source.word.Vars, v.1.1 = r := by
  change r ∈ c.source.word.support.map (fun t => t.1) at hr
  rcases List.mem_map.mp hr with ⟨t, ht, heq⟩
  exact ⟨⟨t, ht⟩, heq⟩

noncomputable def variableAtSupportRoot
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b) (hr : r ∈ c.source.word.supportNodes) :
    c.source.word.Vars :=
  Classical.choose (exists_variable_at_support_root c r hr)

/-- Root recovery is exact; the subtype witness is never
permitted to rename a visible variable to an unrelated node. -/
theorem variableAtSupportRoot_node
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b) (hr : r ∈ c.source.word.supportNodes) :
    (variableAtSupportRoot c r hr).1.1 = r :=
  Classical.choose_spec (exists_variable_at_support_root c r hr)

noncomputable def visibleVariable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (j : Fin (visibleList c i).length) :
    c.source.word.Vars :=
  variableAtSupportRoot c ((visibleList c i).get j)
    (visibleList_get_mem_supportNodes c i j)

/-- The genuinely typed variable assigned to a visible ancestor
is a strict ambient prefix of the exact selected frontier. -/
theorem visibleVariable_strict_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (j : Fin (visibleList c i).length) :
    IsStrictPrefix (visibleVariable c i j).1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  have hroot :
      (visibleVariable c i j).1.1 = (visibleList c i).get j :=
    variableAtSupportRoot_node c _
      (visibleList_get_mem_supportNodes c i j)
  rw [hroot]
  exact ConeLocalDecoder.visibleAncestor_get_prefix
    c.T c.source.word.supportNodes
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1 j

/-- The concrete decoder R_i translates the m+1 auxiliary
labels either to a fallback original letter or to the
genuine source-variable subtype of a visible ancestor. -/
noncomputable def decodeAux
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : Index c)
    (j : Fin (m + 1)) :
    Sum α c.source.word.Vars :=
  match ConeLocalDecoder.decode
      c.T c.source.word.supportNodes
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      fallback (frontier_height_le_m_succ c i) j with
  | Sum.inl a => Sum.inl a
  | Sum.inr z => Sum.inr (visibleVariable c i z)

/-- Every variable emitted by the actual forward-frontier
decoder is a STRICT predecessor of its frontier. -/
theorem decodeAux_variable_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : Index c)
    (j : Fin (m + 1))
    (v : c.source.word.Vars)
    (hdec : decodeAux c fallback i j = Sum.inr v) :
    IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  cases hd : ConeLocalDecoder.decode
      c.T c.source.word.supportNodes
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      fallback (frontier_height_le_m_succ c i) j with
  | inl a =>
      simp [decodeAux, hd] at hdec
  | inr z =>
      have hv : visibleVariable c i z = v := by
        simpa [decodeAux, hd] using hdec
      have hp := visibleVariable_strict_prefix c i z
      rw [hv] at hp
      exact hp

/-- Whenever the visible-ancestor list is nonempty, the
m+1 auxiliary alphabet hits EVERY target in that list. -/
theorem decodeAux_onto_visible
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : Index c)
    (hpos : 0 < (visibleList c i).length)
    (z : Fin (visibleList c i).length) :
    ∃ j : Fin (m + 1),
      decodeAux c fallback i j =
        Sum.inr (visibleVariable c i z) := by
  obtain ⟨j, hj⟩ := ConeLocalDecoder.decode_onto_visible
      c.T c.source.word.supportNodes
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      fallback (frontier_height_le_m_succ c i)
      hpos z
  refine ⟨j, ?_⟩
  simp [decodeAux, hj]

/-- Irrelevant raw local symbols outside the i-th complete-support
frontier cone are replaced by the fallback alphabet letter. -/
noncomputable def maskedRaw
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ) :
    Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ := by
  classical
  exact fun i t =>
    if IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1
    then raw i t
    else Sum.inl (Sum.inl fallback)

theorem maskedRaw_inside
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (i : Index c) (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    maskedRaw c fallback raw i t = raw i t := by
  classical
  simp [maskedRaw, ht]

/-- Auxiliary labels in the masked raw family occur only
where their selected frontier is an ambient prefix. -/
theorem maskedRaw_aux_inside
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (i : Index c) (t : BoundedNode b n)
    (j : Fin (m + 1))
    (h : maskedRaw c fallback raw i t =
      Sum.inl (Sum.inr j)) :
    IsPrefix (ForwardOrderedProjections.frontierAt
      c.T c.cut i).1 t.1 := by
  classical
  by_cases ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1
  · exact ht
  · simp [maskedRaw, ht] at h

/-- Genuine cone variables likewise cannot be emitted outside
the frontier cone once irrelevant local positions are masked. -/
theorem maskedRaw_variable_inside
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (i : Index c) (t : BoundedNode b n)
    (z : κ)
    (h : maskedRaw c fallback raw i t = Sum.inr z) :
    IsPrefix (ForwardOrderedProjections.frontierAt
      c.T c.cut i).1 t.1 := by
  classical
  by_cases ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1
  · exact ht
  · simp [maskedRaw, ht] at h

/-- The typed decoder plus cone containment gives the
actual root-alignment condition for AUXILIARY letters.
No independent alignment hypothesis remains for R_i. -/
theorem auxiliary_root_aligned
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (i : Index c) (t : BoundedNode b n)
    (j : Fin (m + 1)) (v : c.source.word.Vars)
    (hraw : maskedRaw c fallback raw i t =
      Sum.inl (Sum.inr j))
    (hdec : decodeAux c fallback i j = Sum.inr v) :
    IsPrefix v.1.1 t.1 := by
  have hfront := maskedRaw_aux_inside c fallback raw i t j hraw
  have hp := decodeAux_variable_prefix c fallback i j v hdec
  exact isPrefix_trans hp.1 hfront

/-- Construct the ACTUAL full-frontier ConeData from the
repaired per-frontier visible-ancestor decoders R_i.
Only the alignment of transported GENUINE cone variables
needs to be supplied. Raw symbols outside frontier cones
are masked and cannot cause spurious alignment obligations. -/
noncomputable def coneData
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hcone : ∀ (i : Index c) (t : BoundedNode b n)
      (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1) :
    ForwardQFullFrontierThreeWay.ConeData c (Fin (m + 1)) κ where
  raw := maskedRaw c fallback raw
  decodeAux := decodeAux c fallback
  coneRoot := coneRoot
  auxiliaryAligned := by
    intro i t j v hraw hdec
    exact auxiliary_root_aligned c fallback raw i t j v hraw hdec
  coneAligned := by
    intro i t z hraw
    have ht := maskedRaw_variable_inside c fallback raw i t z hraw
    have horig : raw i t = Sum.inr z := by
      simpa [maskedRaw, ht] using hraw
    exact hcone i t z ht horig

/-- Constructing the R_i decoder does not alter any original
raw local symbol INSIDE its selected complete frontier cone. -/
theorem coneData_raw_inside
    {b n l k m : Nat} {α κ : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hcone : ∀ (i : Index c) (t : BoundedNode b n)
      (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1)
    (i : Index c) (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    (coneData c fallback raw coneRoot hcone).raw i t = raw i t := by
  simp [coneData, maskedRaw_inside c fallback raw i t ht]

/-- Using the explicit visible-ancestor decoder R_i produces a
valid starred word on the exact corrected Q support. -/
theorem coneData_actual_Q_tree
    {b n l k m : Nat} {α κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hcone : ∀ (i : Index c) (t : BoundedNode b n)
      (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1) :
    ((coneData c fallback raw coneRoot hcone).onActualStarredQ
      hb c x hTbound).tree = (nodes c x.1).toList := by
  exact (coneData c fallback raw coneRoot hcone).onActualStarredQ_tree
    hb c x hTbound

/-- The actual decoded Q-word evaluation on an arbitrary D0/D2
frontier is exactly the original raw word's three-case formula
with the concrete visible-ancestor decoder R_i. Masking
irrelevant symbols outside their own frontier cannot change it. -/
theorem coneData_actual_Q_eval_inside
    {b n l k m : Nat} {α κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (fallback : α)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) κ)
    (coneRoot : Index c → κ → c.source.word.Vars)
    (hcone : ∀ (i : Index c) (t : BoundedNode b n)
      (z : κ),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 →
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1)
    (i : Index c) (t : BoundedNode b n)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (σ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol σ
      (((coneData c fallback raw coneRoot hcone).onActualStarredQ
        hb c x hTbound).word.word t) =
      match raw i t with
      | Sum.inl (Sum.inl a) => a
      | Sum.inl (Sum.inr j) =>
          SpanAudit.evalSymbol σ (decodeAux c fallback i j)
      | Sum.inr z => σ (coneRoot i z) := by
  have h :=
    (coneData c fallback raw coneRoot hcone).eval_inside
      hb c x hTbound i t ht σ
  simpa [coneData, maskedRaw, ht] using h

end DualTree.ForwardQVisibleAncestorDecoder
