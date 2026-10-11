import DualTree.ForwardQBranchCount
import DualTree.ForwardQFinalCutOrder
import DualTree.ForwardQRooted
import DualTree.LastBranchWitness
import DualTree.SupportReachability
import DualTree.Lemma27QOrderReduction

/-!
# Final skew branching witness of the actual forward-corrected Q

The original maximal forward-auxiliary interior cut survives in the
corrected Q support. Its b immediate directions are all occupied, and
the corrected Q support is rooted at the retained source root.

To verify clause (iv) of the paper's skew definition, we prove all
support vertices earlier than the cut have unique immediate successors
in every direction; any early Q vertex belongs to the old interior,
since all new projected markers are strictly outside the inclusive
forward cut. The no-branching-after-cut clause was proved earlier.
The generic LastBranchWitness lemma then supplies the final cut with
the last direction b-1 as a concrete Boolean witness.

Combined with exact 0-or-b successor counts and Q rootedness, the
entire semi-complete skew assertion reduces precisely to clauses
(ii) and (iii), which compare intrinsic Q rank to actual ambient
length. Those two inequalities and the word/colouring construction
remain separate source-specific obligations.
-/

namespace DualTree.ForwardQSkewIV

open ForwardSourceQTree

/-- A Q node at or before the final forward cut belongs to the
original source interior: projected markers are outside the cut. -/
theorem Q_before_cut_old_interior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ (nodes c x).toList)
    (hbefore : SkewTree.forwardAuxB s c.cut = true) :
    s ∈ SkewTree.interior c.source.tree := by
  classical
  have hsFin : s ∈ nodes c x := Finset.mem_toList.mp hs
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hsFin
  rcases Finset.mem_union.mp hsFin with hbase | hnew
  · exact (ForwardQFixedBase.oldBase_mem_iff_original_interior c s).1
      (List.mem_toFinset.mp hbase)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hnew
    have hout := ForwardQMarkedTerminals.markedProjection_outside_cut c x i
    have hsource : ForwardAux s c.cut := by
      simpa [SkewTree.forwardAuxB] using hbefore
    have hwrong : ForwardAux (markedProjection c x i).1 c.cut := by
      simpa [hi] using hsource
    exact False.elim (hout hwrong)

/-- Every actual Q node strictly preceding the maximal source
interior cut has all immediate branching directions. -/
theorem Q_fullBeforeB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.fullBeforeB SkewTree.forwardAuxB
      (nodes c x).toList c.cut = true := by
  let W := nodes c x
  unfold SkewTree.fullBeforeB
  apply List.all_eq_true.mpr
  intro s hs
  change (if SkewTree.forwardAuxB s c.cut && !(s == c.cut)
    then (SkewTree.allFin b).all
      (fun i => SkewTree.uniqueBranchB W.toList s i)
    else true) = true
  split_ifs with hcase
  · have hh := hcase
    simp only [Bool.and_eq_true] at hh
    have hsOld : s ∈ SkewTree.interior c.source.tree :=
      Q_before_cut_old_interior c x s hs hh.1
    apply List.all_eq_true.mpr
    intro i _
    exact ForwardQAllDirections.Q_full_immediate_directions
      c x s hsOld i
  · rfl

/-- In positive branching the actual Q support has at least
two vertices, because its retained final cut has a strict Q
descendant. This excludes the singleton convention in skewB. -/
theorem Q_nonsingleton
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    (nodes c x).toList.length ≠ 1 := by
  have hcut : c.cut ∈ (nodes c x).toList :=
    Finset.mem_toList.mpr (ForwardQFixedBase.cut_mem_Q c x)
  obtain ⟨t, ht, hct⟩ :=
    ForwardQMarkerCoverage.cut_has_strict_Q_descendant hb c x
  have ht' : t ∈ (nodes c x).toList := Finset.mem_toList.mpr ht
  exact SupportReachability.nonsingleton_of_distinct_members
    (nodes c x).toList hcut ht' hct.2

/-- The maximal retained cut is an actual witness for skew
clause (iv), under the repaired forward-lex auxiliary order. -/
theorem Q_condIVB
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.condIVB SkewTree.forwardAuxB
      (nodes c x).toList = true := by
  let W := nodes c x
  have hcutW : c.cut ∈ W.toList :=
    Finset.mem_toList.mpr (ForwardQFixedBase.cut_mem_Q c x)
  have hcutOld : c.cut ∈ SkewTree.interior c.source.tree :=
    c.hcut
  have hfullCut : ∀ i : Fin b,
      SkewTree.uniqueBranchB W.toList c.cut i = true :=
    fun i => ForwardQAllDirections.Q_full_immediate_directions
      c x c.cut hcutOld i
  have hcount : (SkewTree.immediateSuccs W.toList c.cut).length = b :=
    Lemma27QBranchCount.immediateSuccs_length_eq_of_full_directions
      W.toList (Finset.nodup_toList W) c.cut hfullCut
  exact LastBranchWitness.condIVB_of_full_last_witness
    hb SkewTree.forwardAuxB W.toList c.cut hcutW
    (Q_fullBeforeB c x)
    (ForwardQFinalCutOrder.Q_emptyAfterB c x)
    hcount hfullCut

/-- With root, numerical branching and final witness proved,
the whole skew predicate is exactly equivalent to conditions
(ii) and (iii): the two remaining intrinsic-height / ambient-
length comparison statements. -/
theorem Q_skew_iff_order_conditions
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.skewB SkewTree.forwardAuxB
      (nodes c x).toList = true ↔
      SkewTree.condIIB (nodes c x).toList = true ∧
      SkewTree.condIIIB (nodes c x).toList = true := by
  exact Lemma27QOrderReduction.skewB_iff_order_conditions
    SkewTree.forwardAuxB (nodes c x).toList
    (Finset.nodup_toList (nodes c x))
    (Q_nonsingleton hb c x)
    (ForwardQRooted.Q_rootedB c x)
    (Q_condIVB hb c x)

/-- Consequently the entire semi-complete predicate for the
corrected Q support is equivalent to exactly the two remaining
skew rank/ambient-length order clauses, with no unverified
branching or final-witness conjunct. -/
theorem Q_semiComplete_iff_order_conditions
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true ↔
      SkewTree.condIIB (nodes c x).toList = true ∧
      SkewTree.condIIIB (nodes c x).toList = true := by
  exact (ForwardQBranchCount.Q_semiComplete_iff_skew hb c x).trans
    (Q_skew_iff_order_conditions hb c x)

end DualTree.ForwardQSkewIV
