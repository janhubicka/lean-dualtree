import DualTree.SignatureBoundary
import DualTree.CutFrontier

/-!
# Conditional signature-boundary to support-frontier transport

The local coding in Lemma 27 uses two kinds of nodes:
* a signature boundary, the first ambient prefix outside the distinguished cut;
* a support frontier, a minimal node of T outside the same cut.

If a support node t outside the cut extends the signature boundary s, then s
necessarily prefixes the unique frontier of t. Otherwise that frontier would
be an even earlier non-cut prefix of s.

This is an exact abstract geometry lemma. To use it for all boundary nodes
in the paper's R one must still prove that each has a suitable support
descendant, and that all such descendants yield the same frontier root.
-/

namespace DualTree.SignatureFrontier

/--
A first non-cut boundary lies below every outside frontier whose cone
contains an extension of the boundary.
-/
theorem boundary_prefix_frontier_of_shared_descendant
    {b : Nat}
    (T : List (Node b))
    (cut leaf s frontier t : Node b)
    (hs : SignatureBoundary.Boundary cut leaf s)
    (hf : CutFrontier.Frontier T
      (SignatureBoundary.BeforeCut cut) frontier)
    (hst : IsPrefix s t)
    (hft : IsPrefix frontier t) :
    IsPrefix s frontier := by
  rcases le_total s.length frontier.length with hle | hle
  · exact CutFrontier.prefix_of_prefix_length_le hst hft hle
  · have hfs : IsPrefix frontier s :=
      CutFrontier.prefix_of_prefix_length_le hft hst hle
    by_cases heq : frontier = s
    · subst frontier
      exact isPrefix_refl s
    · have hstrict : IsStrictPrefix frontier s := ⟨hfs, heq⟩
      exact (hf.2.1 (hs.2.2 frontier hstrict)).elim

/--
For a fixed outside support node t extending a signature boundary, there is
a unique support frontier on t's path, and this frontier extends the boundary.
-/
theorem boundary_prefix_unique_frontier_of_support_extension
    {b : Nat}
    (T : List (Node b))
    (cut leaf s t : Node b)
    (hs : SignatureBoundary.Boundary cut leaf s)
    (ht : t ∈ T)
    (htOutside : ¬ SignatureBoundary.BeforeCut cut t)
    (hst : IsPrefix s t) :
    ∃! f,
      CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) f ∧
      IsPrefix f t ∧ IsPrefix s f := by
  rcases CutFrontier.exists_unique_frontier_above
      T (SignatureBoundary.BeforeCut cut) ht htOutside with
    ⟨f, ⟨hf, hft⟩, hu⟩
  have hsf : IsPrefix s f :=
    boundary_prefix_frontier_of_shared_descendant T cut leaf
      s f t hs hf hst hft
  refine ⟨f, ⟨hf, hft, hsf⟩, ?_⟩
  intro f' hf'
  exact hu f' ⟨hf'.1, hf'.2.1⟩

end DualTree.SignatureFrontier
