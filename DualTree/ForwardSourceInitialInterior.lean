import DualTree.ForwardSourceQTree
import DualTree.LastInteriorBranching
import DualTree.CanonicalSupportWalk
import DualTree.ForwardModelHeapInjective

/-!
# The source interior is a forward initial segment before the last cut

The canonical A-to-R correspondence in corrected Lemma 27 needs
the *intrinsic* source interior to occupy the first l positions of
the forward canonical address enumeration. Here we prove its first
source-facing prerequisite directly from the actual hypotheses.

On a nontrivial positive-branching starred source, the final
branching cut has the full-before property. Every source vertex
before that cut branches in all directions, so is interior. The
cut itself is interior. Conversely all interior vertices are at
or before the cut, by the precise Frame maximality assumption.

Consequently the source interior is an INITIAL SEGMENT of the
original source vertices under corrected ForwardAux. This is
an intrinsic statement inside the arbitrary skew source, not yet
the promised enumeration of its compressed canonical addresses.
The printed reverse-lex auxiliary order is not used.
-/

namespace DualTree.ForwardSourceInitialInterior

open ForwardSourceQTree
open ForwardModelBoundaryHeap

/-- At the true last source interior cut, the generic full-before
branching requirement is a consequence of the source skew axioms. -/
theorem source_full_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.fullBeforeB SkewTree.forwardAuxB
      c.source.tree c.cut = true :=
  StarredSignature.fullBefore_at_maxInterior
    c.source c.cut c.hcut c.hmax

/-- Every source vertex before or equal to the maximal interior
cut is itself interior, for positive branching. For an earlier
vertex, full-before supplies the zero-th directional immediate
successor; for the cut it is part of the original Frame data. -/
theorem source_forward_le_cut_is_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ c.source.tree)
    (hbefore : ForwardAux s c.cut) :
    s ∈ SkewTree.interior c.source.tree := by
  by_cases heq : s = c.cut
  · subst s
    exact c.hcut
  have hfull := source_full_before_cut c
  unfold SkewTree.fullBeforeB at hfull
  have hbeforeBool : SkewTree.forwardAuxB s c.cut = true := by
    simpa [SkewTree.forwardAuxB] using hbefore
  have hentry :
      (SkewTree.allFin b).all
        (fun i => SkewTree.uniqueBranchB c.source.tree s i) = true := by
    have h := (List.all_eq_true.mp hfull) s hs
    simpa [hbeforeBool, heq] using h
  let i : Fin b := ⟨0, hb⟩
  have huniq : SkewTree.uniqueBranchB c.source.tree s i = true :=
    (List.all_eq_true.mp hentry) i
      (DirectionalSupport.mem_allFin b i)
  let u : Node b := CanonicalSupportWalk.next c.source.tree s i
  have huS : u ∈ c.source.tree :=
    CanonicalSupportWalk.next_mem c.source.tree s i huniq
  have huImm : SkewTree.immediateSuccB c.source.tree s u = true :=
    (CanonicalSupportWalk.next_unique c.source.tree s i huniq).1
  have huList : u ∈ SkewTree.immediateSuccs c.source.tree s := by
    change u ∈ c.source.tree.filter
      (fun t => SkewTree.immediateSuccB c.source.tree s t)
    exact List.mem_filter.mpr ⟨huS, huImm⟩
  have hnonempty :
      (SkewTree.immediateSuccs c.source.tree s).isEmpty = false := by
    cases hlist : SkewTree.immediateSuccs c.source.tree s with
    | nil =>
        have hbad : u ∈ ([] : List (Node b)) := by
          simpa only [hlist] using huList
        simp at hbad
    | cons t tail =>
        rfl
  change s ∈ c.source.tree.filter
    (fun t => !(SkewTree.immediateSuccs c.source.tree t).isEmpty)
  exact List.mem_filter.mpr ⟨hs, by simp [hnonempty]⟩

/-- The source interior is EXACTLY the intersection of the source
vertex set with the inclusive initial forward auxiliary segment
ending at the last interior cut. -/
theorem source_interior_iff_forward_le_cut
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ c.source.tree) :
    s ∈ SkewTree.interior c.source.tree ↔
      ForwardAux s c.cut := by
  constructor
  · intro hint
    simpa [SkewTree.forwardAuxB] using c.hmax s hint
  · exact source_forward_le_cut_is_interior hb c s hs

/-- Inside the genuine source vertex set, the interior is
downward closed under the CORRECTED forward auxiliary order.
This is the precise initial-segment property required before
constructing a compatible homogeneous first-l address map. -/
theorem source_interior_forward_initial
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ c.source.tree)
    (ht : t ∈ SkewTree.interior c.source.tree)
    (hst : ForwardAux s t) :
    s ∈ SkewTree.interior c.source.tree := by
  have htc : ForwardAux t c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax t ht
  have hsc : ForwardAux s c.cut := by
    apply (ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
      hb s c.cut).2
    exact le_trans
      ((ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
        hb s t).1 hst)
      ((ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
        hb t c.cut).1 htc)
  exact source_forward_le_cut_is_interior hb c s hs hsc

/-- A source vertex strictly outside the inclusive corrected
cut segment is necessarily a leaf (not an interior node).
This is about the original source tree, not the rebuilt Q. -/
theorem source_outside_cut_not_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ c.source.tree)
    (hout : ¬ ForwardAux s c.cut) :
    s ∉ SkewTree.interior c.source.tree := by
  intro hint
  exact hout ((source_interior_iff_forward_le_cut hb c s hs).1 hint)

end DualTree.ForwardSourceInitialInterior
