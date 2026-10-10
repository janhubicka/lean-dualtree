import DualTree.ForwardSignatureBoundary
import DualTree.InclusiveFrontier

/-!
# Inclusive frontiers for the globally corrected forward auxiliary order

The finite frontier construction in the published Lemma 27 is an
*inclusive* auxiliary cut of the ambient complete support T,
distinct from Definition 26's *strict* cut used to select
signature boundaries. An attempt to repair the auxiliary
order must preserve this distinction.

For the forward auxiliary order, a support node extending an
outside-cut boundary cannot return inside the cut. Therefore
a boundary s with a support descendant lies below a unique
minimal support frontier beyond the inclusive cut whenever
T is ambient meet-closed.

We also instantiate the needed meet-closure for any
nonsingleton complete skew support under the *repaired*
forward auxiliary order. This avoids feeding a forward
support to the existing printed-order complete-support
interface by mistake.

The corrected boundary-of-signature-marker property,
the associated D₂ coordinate injection, and the Q word
construction remain separate obligations.
-/

namespace DualTree.ForwardInclusiveFrontier

/-- A prefix of a node at or before an inclusive
forward cut also belongs to that inclusive cut. -/
theorem forwardAux_of_prefix
    {b : Nat} {s t cut : Node b}
    (hst : IsPrefix s t)
    (htcut : ForwardAux t cut) :
    ForwardAux s cut := by
  by_cases heq : s = t
  · simpa [heq] using htcut
  · have hlen : s.length < t.length :=
      MeetClosedFromBranching.length_lt_of_strictPrefix
        ⟨hst, heq⟩
    rcases htcut with htc | ⟨heqlen, _⟩ <;>
      exact Or.inl (by omega)

/-- An ambient extension of an outside-cut node stays
outside the inclusive forward auxiliary cut. -/
theorem outside_of_prefix
    {b : Nat} {cut s t : Node b}
    (hs : ¬ ForwardAux s cut)
    (hst : IsPrefix s t) :
    ¬ ForwardAux t cut := by
  intro ht
  exact hs (forwardAux_of_prefix hst ht)

/-- Minimal boundary node outside the inclusive forward cut,
including all its proper ambient prefixes in the cut. -/
def ForwardCutBoundary {b : Nat} (cut s : Node b) : Prop :=
  ¬ ForwardAux s cut ∧
    ∀ r, IsStrictPrefix r s → ForwardAux r cut

/-- Each corrected inclusive boundary lies below a unique
minimal outside-cut support frontier, provided that T
is meet-closed and the boundary has a support descendant. -/
theorem unique_frontier_of_boundary {b : Nat}
    (T : List (Node b)) (cut s : Node b)
    (hmeet : MeetGeometry.MeetClosed T)
    (hs : ForwardCutBoundary cut s)
    (hdesc : ∃ t, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => ForwardAux u cut) f ∧
      IsPrefix s f := by
  rcases hdesc with ⟨t, ht, hst⟩
  have htOutside : ¬ ForwardAux t cut :=
    outside_of_prefix hs.1 hst
  rcases CutFrontier.exists_unique_frontier_above
      T (fun u => ForwardAux u cut) ht htOutside with
    ⟨f, ⟨hf, hft⟩, _⟩
  have hsf : IsPrefix s f := by
    rcases le_total s.length f.length with hle | hle
    · exact CutFrontier.prefix_of_prefix_length_le hst hft hle
    · have hfs : IsPrefix f s :=
        CutFrontier.prefix_of_prefix_length_le hft hst hle
      by_cases heq : f = s
      · subst f
        exact isPrefix_refl s
      · have hstrict : IsStrictPrefix f s := ⟨hfs, heq⟩
        exact (hf.2.1 (hs.2 f hstrict)).elim
  refine ⟨f, ⟨hf, hsf⟩, ?_⟩
  intro g hg
  let common := MeetGeometry.commonPrefix f g
  have hcT : common ∈ T := hmeet f g hf.1 hg.1.1
  have hsc : IsPrefix s common :=
    MeetGeometry.prefix_commonPrefix hsf hg.2
  have hcOutside : ¬ ForwardAux common cut :=
    outside_of_prefix hs.1 hsc
  have hcf : IsPrefix common f :=
    MeetGeometry.commonPrefix_prefix_left f g
  have hcg : IsPrefix common g :=
    MeetGeometry.commonPrefix_prefix_right f g
  have hcfEq : common = f := by
    by_contra hne
    exact hcOutside (hf.2.2 common hcT ⟨hcf, hne⟩)
  have hcgEq : common = g := by
    by_contra hne
    exact hcOutside (hg.1.2.2 common hcT ⟨hcg, hne⟩)
  exact hcgEq.symm.trans hcfEq

/-- Any nonsingleton complete skew support in the repaired
forward-order class is closed under ambient longest common
prefixes, independently of its printed-order status. -/
theorem meetClosed_complete_forward {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1) :
    MeetGeometry.MeetClosed T := by
  apply CompleteSkewMeet.meetClosed_of_complete_total
    SkewTree.forwardAuxB T hcomplete hnonsingleton
  intro s t hne
  rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
  · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
  · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)

/-- Corrected source-facing frontier uniqueness for forward
complete skew supports, under the explicit boundary and
descendant hypotheses that still need to be proved for R. -/
theorem unique_frontier_complete_forward {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut s : Node b)
    (hs : ForwardCutBoundary cut s)
    (hdesc : ∃ t, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => ForwardAux u cut) f ∧
      IsPrefix s f :=
  unique_frontier_of_boundary T cut s
    (meetClosed_complete_forward T hcomplete hnonsingleton)
    hs hdesc

end DualTree.ForwardInclusiveFrontier
