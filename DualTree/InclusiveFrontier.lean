import DualTree.SkewMeetInstantiation

/-!
# Support frontiers beyond an inclusive auxiliary-order cut

Lemma 27 uses the minimal elements of T \ {u in T : PaperAux u cut},
so the cut is *inclusive*. This differs from Definition 26's strict
initial segment, which determines the first boundary of a leaf.

Here we establish the correct general frontier geometry for the
inclusive cut: a node s that lies outside that cut, with all proper
prefixes inside, lies below exactly one support frontier if it has a
support descendant and the support is ambient meet-closed.
-/

namespace DualTree.InclusiveFrontier

/-- The first node on an ambient path outside the inclusive paper cut. -/
def PaperCutBoundary {b : Nat} (cut s : Node b) : Prop :=
  ¬ PaperAux s cut ∧
    ∀ r, IsStrictPrefix r s → PaperAux r cut

/-- Outside the inclusive cut is preserved by extension. -/
theorem outside_of_prefix {b : Nat}
    {cut s t : Node b}
    (hs : ¬ PaperAux s cut)
    (hst : IsPrefix s t) :
    ¬ PaperAux t cut := by
  intro ht
  exact hs (CutPreservation.paperAux_of_prefix hst ht)

/--
A boundary of the inclusive cut lies below a unique minimal support
node outside the same cut. Crucially, this lemma agrees with the t_i
frontier used in the printed proof of Lemma 27.
-/
theorem unique_frontier_of_boundary {b : Nat}
    (T : List (Node b)) (cut s : Node b)
    (hmeet : MeetGeometry.MeetClosed T)
    (hs : PaperCutBoundary cut s)
    (hdesc : ∃ t, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f := by
  rcases hdesc with ⟨t, ht, hst⟩
  have htOutside : ¬ PaperAux t cut :=
    outside_of_prefix hs.1 hst
  rcases CutFrontier.exists_unique_frontier_above
      T (fun u => PaperAux u cut) ht htOutside with
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
  let m := MeetGeometry.commonPrefix f g
  have hmT : m ∈ T := hmeet f g hf.1 hg.1.1
  have hsm : IsPrefix s m :=
    MeetGeometry.prefix_commonPrefix hsf hg.2
  have hmOutside : ¬ PaperAux m cut :=
    outside_of_prefix hs.1 hsm
  have hmf : IsPrefix m f :=
    MeetGeometry.commonPrefix_prefix_left f g
  have hmg : IsPrefix m g :=
    MeetGeometry.commonPrefix_prefix_right f g
  have hmfEq : m = f := by
    by_contra hne
    exact hmOutside (hf.2.2 m hmT ⟨hmf, hne⟩)
  have hmgEq : m = g := by
    by_contra hne
    exact hmOutside (hg.1.2.2 m hmT ⟨hmg, hne⟩)
  exact hmfEq.symm.trans hmgEq

/-- The exact inclusive-cut frontier theorem for complete skew supports. -/
theorem unique_frontier_complete_paper {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut s : Node b)
    (hs : PaperCutBoundary cut s)
    (hdesc : ∃ t, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f :=
  unique_frontier_of_boundary T cut s
    (SkewMeetInstantiation.meetClosed_complete_paper T hcomplete)
    hs hdesc

end DualTree.InclusiveFrontier
