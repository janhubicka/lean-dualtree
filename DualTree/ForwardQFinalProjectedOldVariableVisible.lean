import DualTree.ForwardQVisibleAuxSymbolEncoder
import DualTree.ForwardQFinalSupportCut

/-!
# Any old source variable occurring in a projected cone is visible

The corrected first-boundary R_i auxiliary decoder can represent any
old source variable whose root strictly precedes the selected frontier.
Previously that visibility was assumed as an explicit hypothesis.

For a genuine corrected projected node P_i(z), every old source
variable root is at/before the corrected cut.  If that root
is a prefix of P_i(z), it must actually be a STRICT prefix of
frontier_i: both the old root and the frontier are prefixes
of P_i(z), but frontier_i is already strictly outside the cut.
The reverse prefix orientation is therefore impossible.

This is proved using a reusable elementary comparability lemma
for two list prefixes of the same word, based on their lengths
and the actual take/drop decomposition.  No spurious immediate
ambient-child or unstated tree-order assumption enters.

Consequently the ACTUAL finite m+1 auxiliary decoder can encode
every old source variable whose root occurs above P_i(z).
This discharges the geometric hypothesis of the visible-symbol
encoder, but does not yet construct the complete enlarged
mixed input or the output's chosen D2 terminal markers.
-/

namespace DualTree.ForwardQFinalProjectedOldVariableVisible

open ForwardSourceQTree

/-- Two finite prefixes of one genuine word are comparable.
If a is no longer than c then a is a prefix of c. -/
theorem prefix_of_common_extension_of_length_le
    {b : Nat}
    (a c t : Node b)
    (ha : IsPrefix a t)
    (hc : IsPrefix c t)
    (hlen : a.length ≤ c.length) :
    IsPrefix a c := by
  have hatake : t.take a.length = a := by
    rcases ha with ⟨u,hu⟩
    rw [hu]
    simp
  have hctake : t.take c.length = c := by
    rcases hc with ⟨u,hu⟩
    rw [hu]
    simp
  have hac : c.take a.length = a := by
    calc
      c.take a.length = (t.take c.length).take a.length := by
        rw [hctake]
      _ = t.take a.length := by
        simp [List.take_take, Nat.min_eq_left hlen]
      _ = a := hatake
  refine ⟨c.drop a.length, ?_⟩
  calc
    c = c.take a.length ++ c.drop a.length :=
      (List.take_append_drop a.length c).symm
    _ = a ++ c.drop a.length := by rw [hac]

/-- If an OLD source-variable root precedes an ACTUAL projected
point P_i(z), then it is strictly above the i-th outside-cut
frontier, rather than merely some prefix inside the cone.
This uses the real corrected inclusive-cut geometry. -/
theorem old_variable_prefix_frontier_of_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : ForwardQFullFrontierWord.Index c)
    (z : BoundedNode b (k-(m+1)))
    (v : c.source.word.Vars)
    (hv : IsPrefix v.1.1
      (ForwardQFinalRefinementRoots.projected c ⟨i,z⟩).1) :
    IsStrictPrefix v.1.1
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  let frontier := (ForwardOrderedProjections.frontierAt
    c.T c.cut i).1
  let projectedNode :=
    (ForwardQFinalRefinementRoots.projected c ⟨i,z⟩).1
  have hfront : IsPrefix frontier projectedNode :=
    ForwardQFinalRefinementRoots.projected_cone c ⟨i,z⟩
  have hbefore : ForwardAux v.1.1 c.cut :=
    (Finset.mem_filter.mp
      (ForwardQFinalSupportCut.old_source_root_mem_retained c v)).2
  have hnotBack : ¬ IsPrefix frontier v.1.1 := by
    intro hp
    have hafter :=
      ForwardInclusiveFrontier.outside_of_prefix
        (ForwardOrderedProjections.frontierAt_spec
          c.T c.cut i).2.1 hp
    exact hafter hbefore
  rcases Nat.le_total v.1.1.length frontier.length with hlen | hlen
  · have hpre : IsPrefix v.1.1 frontier :=
      prefix_of_common_extension_of_length_le
        v.1.1 frontier projectedNode hv hfront hlen
    refine ⟨hpre,?_⟩
    intro heq
    apply hnotBack
    rw [heq]
    exact isPrefix_refl _
  · have hback : IsPrefix frontier v.1.1 :=
      prefix_of_common_extension_of_length_le
        frontier v.1.1 projectedNode hfront hv hlen
    exact False.elim (hnotBack hback)

/-- Every actual old source variable appearing at a corrected
projected position P_i(z) is representable by a real finite
auxiliary label j : Fin(m+1), decoded to that EXACT variable.
No extra visibility hypothesis is needed. -/
theorem auxiliary_label_for_projected_old_variable
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (z : BoundedNode b (k-(m+1)))
    (v : c.source.word.Vars)
    (hv : IsPrefix v.1.1
      (ForwardQFinalRefinementRoots.projected c ⟨i,z⟩).1) :
    ∃ j : Fin (m+1),
      ForwardQVisibleAncestorDecoder.decodeAux
        c fallback i j = Sum.inr v := by
  exact ForwardQVisibleAuxSymbolEncoder.exists_aux_label_for_visible_source_var
    c fallback i v
    (old_variable_prefix_frontier_of_projected c i z v hv)

/-- The selected auxiliary encoding of this old variable at
P_i(z) is genuinely root-aligned with the correct sorted cone. -/
theorem encoded_old_variable_at_projected_decodes
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (i : ForwardQFullFrontierWord.Index c)
    (z : BoundedNode b (k-(m+1)))
    (v : c.source.word.Vars)
    (hv : IsPrefix v.1.1
      (ForwardQFinalRefinementRoots.projected c ⟨i,z⟩).1) :
    ForwardQVisibleAncestorDecoder.decodeAux c fallback i
      (ForwardQVisibleAuxSymbolEncoder.encodeVisibleSourceVar
        c fallback i v
        (old_variable_prefix_frontier_of_projected c i z v hv)) =
      Sum.inr v := by
  exact ForwardQVisibleAuxSymbolEncoder.decodeAux_encodeVisibleSourceVar
    c fallback i v
    (old_variable_prefix_frontier_of_projected c i z v hv)

end DualTree.ForwardQFinalProjectedOldVariableVisible
