import DualTree.CutFrontier

/-!
# The first boundary point of a signature path (Definition 26)

Definition 26 includes, for certain leaves t, the prefix-minimal element of
(Pred(t) ∪ {t}) \ D, where D is the strict auxiliary initial segment before
the last interior node s*. This file makes that choice as a typed, partial
construction: it is available for each t outside D and is unique.

The remaining source-facing task is to prove, from the semi-complete skew
tree conditions, that all leaves used in Definition 26 are outside D.
We do not silently extend a partial choice to leaves for which the defining
minimum need not exist.
-/

namespace DualTree.SignatureBoundary

/-- The strict auxiliary initial segment used in Definition 26. -/
def BeforeCut {b : Nat} (cut s : Node b) : Prop :=
  PaperAux s cut ∧ s ≠ cut

/-- Every proper prefix of the cut belongs to its strict initial segment. -/
theorem beforeCut_of_proper_prefix {b : Nat} {r cut : Node b}
    (h : IsStrictPrefix r cut) : BeforeCut cut r := by
  have hlen : r.length < cut.length := by
    have hle : r.length ≤ cut.length := prefix_length_le h.1
    by_contra hn
    have heqLen : r.length = cut.length := by omega
    have heq : r = cut :=
      CutPreservation.prefix_eq_of_length_eq h.1 heqLen
    exact h.2 heq
  exact ⟨Or.inl hlen, h.2⟩

/--
A boundary node s is the first point on the path to t which does not
belong to the strict auxiliary initial segment before cut.
-/
def Boundary {b : Nat} (cut t s : Node b) : Prop :=
  IsPrefix s t ∧ ¬ BeforeCut cut s ∧
    ∀ r, IsStrictPrefix r s → BeforeCut cut r

/-- The distinguished cut is its own path boundary. -/
theorem boundary_at_cut {b : Nat} (cut : Node b) :
    Boundary cut cut cut := by
  refine ⟨isPrefix_refl cut, ?_, ?_⟩
  · intro h
    exact h.2 rfl
  · intro r hr
    exact beforeCut_of_proper_prefix hr

/-- All ambient prefixes of a node, in increasing length order. -/
def ambientPath {b : Nat} (t : Node b) : List (Node b) :=
  (List.range (t.length + 1)).map (fun k => t.take k)

theorem prefix_mem_ambientPath {b : Nat}
    {s t : Node b} (h : IsPrefix s t) : s ∈ ambientPath t := by
  unfold ambientPath
  apply List.mem_map.mpr
  refine ⟨s.length, ?_, ?_⟩
  · apply List.mem_range.mpr
    have hlen := prefix_length_le h
    omega
  · exact CutFrontier.take_length_of_prefix h

theorem mem_ambientPath_prefix {b : Nat}
    {s t : Node b} (h : s ∈ ambientPath t) : IsPrefix s t := by
  unfold ambientPath at h
  rcases List.mem_map.mp h with ⟨k, hk, hs⟩
  rw [← hs]
  refine ⟨t.drop k, ?_⟩
  exact (List.take_append_drop k t).symm

theorem boundary_iff_frontier {b : Nat}
    (cut t s : Node b) :
    Boundary cut t s ↔
      CutFrontier.Frontier (ambientPath t) (BeforeCut cut) s := by
  constructor
  · rintro ⟨hpre, hout, hmin⟩
    exact ⟨prefix_mem_ambientPath hpre, hout,
      fun r _ hr => hmin r hr⟩
  · rintro ⟨hmem, hout, hmin⟩
    have hpre : IsPrefix s t := mem_ambientPath_prefix hmem
    refine ⟨hpre, hout, ?_⟩
    intro r hr
    exact hmin r (prefix_mem_ambientPath
      (isPrefix_trans hr.1 hpre)) hr

/--
If t is not strictly before the cut, its path has exactly one first node
outside the strict initial segment. This is the min-prefix operation in
Definition 26, with its existence hypothesis made explicit.
-/
theorem existsUnique_boundary_on_path {b : Nat}
    (cut t : Node b) (hout : ¬ BeforeCut cut t) :
    ∃! s, Boundary cut t s := by
  have ht : t ∈ ambientPath t :=
    prefix_mem_ambientPath (isPrefix_refl t)
  rcases CutFrontier.exists_unique_frontier_above
      (ambientPath t) (BeforeCut cut) ht hout with
    ⟨s, ⟨hs, hpre⟩, hunique⟩
  refine ⟨s, (boundary_iff_frontier cut t s).2 hs, ?_⟩
  intro u hu
  exact hunique u
    ⟨(boundary_iff_frontier cut t u).1 hu, hu.1⟩

/-- The partial boundary selector, requiring an existence witness. -/
noncomputable def firstBoundary {b : Nat}
    (cut t : Node b) (hout : ¬ BeforeCut cut t) : Node b :=
  Classical.choose (existsUnique_boundary_on_path cut t hout)

/-- The chosen boundary is exactly the unique first non-early prefix. -/
theorem firstBoundary_spec {b : Nat}
    (cut t : Node b) (hout : ¬ BeforeCut cut t) :
    Boundary cut t (firstBoundary cut t hout) :=
  (Classical.choose_spec (existsUnique_boundary_on_path cut t hout)).1

end DualTree.SignatureBoundary
