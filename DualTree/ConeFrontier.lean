import DualTree.SignatureFrontier
import DualTree.CutFrontier

/-!
# Uniqueness of a frontier cone containing a signature boundary

The proof of Lemma 27 asserts that every signature boundary in R lies below a
unique frontier root t_i. Given the existence of an outside support descendant,
uniqueness follows from a meet property of the support tree: if two nodes of T
extend an ambient node s, they have a common predecessor in T which itself
extends s.

This module proves the precise reduction for the source's strict auxiliary cut.
No meet property is silently assumed from the skew-tree definition. Showing
that complete skew supports have this property and that each signature boundary
has a support descendant are separately recorded obligations.
-/

namespace DualTree.ConeFrontier

/--
Two support nodes in the same ambient cone have a common support ancestor
still in that cone.
-/
def ConeMeetClosed {b : Nat} (T : List (Node b)) : Prop :=
  ∀ (s x y : Node b),
    x ∈ T → y ∈ T → IsPrefix s x → IsPrefix s y →
      ∃ z : Node b,
        z ∈ T ∧ IsPrefix s z ∧ IsPrefix z x ∧ IsPrefix z y

/-- The strict auxiliary initial segment is closed under taking prefixes. -/
theorem beforeCut_of_prefix {b : Nat}
    {s z cut : Node b}
    (hsz : IsPrefix s z)
    (hz : SignatureBoundary.BeforeCut cut z) :
    SignatureBoundary.BeforeCut cut s := by
  refine ⟨CutPreservation.paperAux_of_prefix hsz hz.1, ?_⟩
  intro heq
  subst s
  have hlen : cut.length ≤ z.length := prefix_length_le hsz
  rcases hz.1 with hstrict | ⟨heqLen, _⟩
  · omega
  · have hsame : cut = z :=
      CutPreservation.prefix_eq_of_length_eq hsz heqLen.symm
    exact hz.2 hsame.symm

/-- Every descendant of an outside node is also outside the strict cut. -/
theorem outside_of_prefix {b : Nat} {cut s z : Node b}
    (hs : ¬ SignatureBoundary.BeforeCut cut s)
    (hsz : IsPrefix s z) :
    ¬ SignatureBoundary.BeforeCut cut z := by
  intro hz
  exact hs (beforeCut_of_prefix hsz hz)

/-- Meet-closure prevents two distinct frontier roots extending one outside point. -/
theorem unique_frontier_in_outside_cone
    {b : Nat}
    (T : List (Node b)) (cut s : Node b)
    (hmeet : ConeMeetClosed T)
    (hs : ¬ SignatureBoundary.BeforeCut cut s)
    {x y : Node b}
    (hx : CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) x)
    (hy : CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) y)
    (hsx : IsPrefix s x) (hsy : IsPrefix s y) :
    x = y := by
  rcases hmeet s x y hx.1 hy.1 hsx hsy with
    ⟨z, hzT, hsz, hzx, hzy⟩
  have hout : ¬ SignatureBoundary.BeforeCut cut z :=
    outside_of_prefix hs hsz
  have hzxEq : z = x := by
    by_contra hne
    exact hout (hx.2.2 z hzT ⟨hzx, hne⟩)
  have hzyEq : z = y := by
    by_contra hne
    exact hout (hy.2.2 z hzT ⟨hzy, hne⟩)
  exact hzxEq.symm.trans hzyEq

/--
The missing uniqueness assertion in Lemma 27, conditional only on
the support's meet property and existence of some support descendant.
-/
theorem unique_frontier_of_signature_boundary
    {b : Nat}
    (T : List (Node b))
    (cut leaf s : Node b)
    (hmeet : ConeMeetClosed T)
    (hb : SignatureBoundary.Boundary cut leaf s)
    (hdesc : ∃ t : Node b, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) f ∧
      IsPrefix s f := by
  rcases hdesc with ⟨t, htT, hst⟩
  have htOutside : ¬ SignatureBoundary.BeforeCut cut t :=
    outside_of_prefix hb.2.1 hst
  rcases SignatureFrontier.boundary_prefix_unique_frontier_of_support_extension
      T cut leaf s t hb htT htOutside hst with
    ⟨f, ⟨hf, hft, hsf⟩, _⟩
  refine ⟨f, ⟨hf, hsf⟩, ?_⟩
  intro g hg
  exact unique_frontier_in_outside_cone T cut s hmeet hb.2.1
    hg.1 hf hg.2 hsf

end DualTree.ConeFrontier
