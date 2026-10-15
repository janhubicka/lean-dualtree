import DualTree.ForwardSourceInitialInterior
import DualTree.ForwardQAllDirections
import DualTree.CanonicalSupportWalk
import DualTree.SignatureInteriorPersistence

/-!
# Each cut-child marker determines exactly one source leaf

Let S be the actual semi-complete forward-skew source and let cut
be its last interior node. Every outgoing direction i from cut has
a uniquely selected immediate successor u_i in S.

Because u_i strictly extends cut, the verified forward
initial-segment theorem makes u_i TERMINAL. Moreover any S vertex
in the cut++[i] cone must be u_i: follow its support path to the
first immediate successor of cut, use unique directional branching,
and exclude proper descendants of the terminal u_i.

This identifies all literal cut-child markers with distinct source
leaves without assuming an arbitrary assignment of leaf indices.
The exceptional first-exit markers, the full A_l <-> R bijection,
and the Ramsey recursion remain independent obligations.
-/

namespace DualTree.ForwardSourceCutLeaves

open ForwardSourceQTree

/-- The actual unique immediate source successor in direction i
at the last interior cut; no auxiliary choice of a leaf. -/
noncomputable def cutLeaf
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (i : Fin b) : Node b :=
  CanonicalSupportWalk.next c.source.tree c.cut i

/-- Every chosen cut child is an actual vertex of the source. -/
theorem cutLeaf_mem
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (i : Fin b) :
    cutLeaf c i ∈ c.source.tree := by
  have huniq :=
    ForwardQAllDirections.source_full_directions c c.cut c.hcut i
  exact CanonicalSupportWalk.next_mem c.source.tree c.cut i huniq

/-- The actual cut successor is inside its prescribed ambient
first-direction cone, even if its immediate support edge skips
some ambient levels. -/
theorem cutLeaf_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) (i : Fin b) :
    IsPrefix (c.cut ++ [i]) (cutLeaf c i) := by
  have huniq :=
    ForwardQAllDirections.source_full_directions c c.cut c.hcut i
  exact (CanonicalSupportWalk.next_unique
    c.source.tree c.cut i huniq).2

/-- The immediate source successor after the final interior
cut is a leaf: it is strictly later in ForwardAux than cut,
and every source vertex after cut is terminal. -/
theorem cutLeaf_terminal
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) (i : Fin b) :
    cutLeaf c i ∉ SkewTree.interior c.source.tree := by
  have hlen : c.cut.length < (cutLeaf c i).length := by
    have h := prefix_length_le (cutLeaf_cone c i)
    simp only [List.length_append, List.length_singleton] at h
    omega
  have hout : ¬ ForwardAux (cutLeaf c i) c.cut := by
    intro h
    rcases h with hlt | ⟨heq, _⟩ <;> omega
  exact ForwardSourceInitialInterior.source_outside_cut_not_interior
    hb c (cutLeaf c i) (cutLeaf_mem c i) hout

/-- Distinct directions at cut lead to distinct actual terminal
source vertices; no two different directional cones overlap. -/
theorem cutLeaf_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Injective (cutLeaf c) := by
  intro i j hij
  have hdirj : IsPrefix (c.cut ++ [j]) (cutLeaf c i) := by
    rw [hij]
    exact cutLeaf_cone c j
  have hp : IsPrefix (c.cut ++ [i]) (c.cut ++ [j]) :=
    CutFrontier.prefix_of_prefix_length_le
      (cutLeaf_cone c i) hdirj (by simp)
  have hwords : c.cut ++ [i] = c.cut ++ [j] :=
    CutPreservation.prefix_eq_of_length_eq hp (by simp)
  have hsingle : [i] = [j] := by
    have hdrop :=
      congrArg (fun z : Node b => z.drop c.cut.length) hwords
    simpa using hdrop
  simpa using hsingle

/-- Every source vertex in the ambient cut++[i] cone is
EXACTLY its unique chosen immediate cut child. In particular
there are no extra leaves or hidden branches above that
cut-child marker. -/
theorem source_node_in_cut_cone_eq_cutLeaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (i : Fin b) (t : Node b)
    (ht : t ∈ c.source.tree)
    (hdir : IsPrefix (c.cut ++ [i]) t) :
    t = cutLeaf c i := by
  have hcutPref : IsPrefix c.cut t :=
    isPrefix_trans ⟨[i], rfl⟩ hdir
  have hcutNe : c.cut ≠ t := by
    intro heq
    subst t
    have hlen := prefix_length_le hdir
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  obtain ⟨u, hu, huImm, huStrict, hut⟩ :=
    SkewBranchGeometry.exists_first_immediate_on_path
      c.source.tree c.cut t ht ⟨hcutPref, hcutNe⟩
  have huLen : (c.cut ++ [i]).length ≤ u.length := by
    have hlen :=
      MeetClosedFromBranching.length_lt_of_strictPrefix huStrict
    simp only [List.length_append, List.length_singleton]
    omega
  have huDir : IsPrefix (c.cut ++ [i]) u :=
    CutFrontier.prefix_of_prefix_length_le hdir hut huLen
  have huBranch : u ∈
      SkewTree.branchWitnesses c.source.tree c.cut i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      c.source.tree c.cut u i).2 ⟨huImm, huDir⟩
  have huniq :=
    ForwardQAllDirections.source_full_directions c c.cut c.hcut i
  have hchosenBranch : cutLeaf c i ∈
      SkewTree.branchWitnesses c.source.tree c.cut i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff
      c.source.tree c.cut (cutLeaf c i) i).2
        ⟨(CanonicalSupportWalk.next_unique
          c.source.tree c.cut i huniq).1,
         cutLeaf_cone c i⟩
  have huEq : u = cutLeaf c i :=
    SkewBranchGeometry.eq_of_mem_uniqueBranch
      c.source.tree c.cut i huniq huBranch hchosenBranch
  have hleafPrefix : IsPrefix (cutLeaf c i) t := by
    rw [← huEq]
    exact hut
  by_contra hne
  have hstrict : IsStrictPrefix (cutLeaf c i) t :=
    ⟨hleafPrefix, Ne.symm hne⟩
  have hint : cutLeaf c i ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree (cutLeaf c i) t
      (cutLeaf_mem c i) ht hstrict
  exact (cutLeaf_terminal hb c i) hint

/-- Every literal cut-child direction determines a UNIQUE
terminal source vertex in the indicated ambient cone. -/
theorem cut_child_has_unique_source_leaf
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (i : Fin b) :
    ∃! t : Node b,
      t ∈ c.source.tree ∧
      t ∉ SkewTree.interior c.source.tree ∧
      IsPrefix (c.cut ++ [i]) t := by
  refine ⟨cutLeaf c i,
    ⟨cutLeaf_mem c i, cutLeaf_terminal hb c i,
      cutLeaf_cone c i⟩, ?_⟩
  intro t ht
  exact source_node_in_cut_cone_eq_cutLeaf hb c i t ht.1 ht.2.2

end DualTree.ForwardSourceCutLeaves
