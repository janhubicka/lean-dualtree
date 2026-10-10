import DualTree.ForwardMarkerFrontierCoverage
import DualTree.SignatureInteriorPersistence

/-!
# Interior persistence and literal R for the forward-corrected signature

Definition 26 produces its signature by keeping all interior vertices
and replacing exceptional leaves by their first ambient boundary
outside the strict auxiliary initial segment.

The literal marker set R used by Lemma 27 is NOT simply the list of
these boundary markers: it is the non-interior part of the resulting
signature (minus cut) together with the ambient children of cut.

To identify every actual member of R as a first-exit boundary, it is
essential to verify persistence of every original interior vertex
other than the final cut. Otherwise old interior vertices could be
incorrectly counted as terminal markers.

This module proves that persistence for the globally corrected
forward auxiliary order. It then proves that each actual member of
R lies outside the inclusive forward cut with all proper ambient
prefixes inside, and has a descendant in the enclosing complete
support. The uniqueness theorem for repaired frontiers therefore
applies to *all* literal R markers. Collision-freedom across
different markers and the Q word remain separate obligations.
-/

namespace DualTree.ForwardSignatureInteriorPersistence

open ForwardSignatureBoundary

/-- The strict forward auxiliary initial segment is closed
under taking ambient prefixes. -/
theorem beforeCut_of_prefix
    {b : Nat} {cut r s : Node b}
    (hrs : IsPrefix r s)
    (hs : BeforeCut cut s) :
    BeforeCut cut r := by
  by_cases heq : r = s
  · simpa [heq] using hs
  · have hlt : r.length < s.length :=
      MeetClosedFromBranching.length_lt_of_strictPrefix ⟨hrs, heq⟩
    have hslen : s.length ≤ cut.length := by
      rcases hs.1 with h | ⟨h, _⟩ <;> omega
    refine ⟨Or.inl (by omega), ?_⟩
    intro hrCut
    subst r
    omega

/-- Any vertex in the corrected signature is either an
original interior vertex or a first boundary of an
exceptional leaf. -/
theorem mem_signatureTree_iff
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b) :
    s ∈ ForwardStarredSignature.signatureTree O cut hout ↔
      s ∈ SkewTree.interior O.tree ∨
      ∃ t : {t : Node b //
          t ∈ StarredSignature.exceptionalLeaves O cut},
        firstBoundary cut t.1 (hout t.1 t.2) = s := by
  classical
  simp [ForwardStarredSignature.signatureTree, List.mem_map]

/-- Every original interior vertex except the last cut
remains an interior vertex of the corrected signature. -/
theorem interiorPersists_of_maxInterior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) :
    ∀ s, s ∈ SkewTree.interior O.tree → s ≠ cut →
      s ∈ SkewTree.interior
        (ForwardStarredSignature.signatureTree O cut hout) := by
  intro s hs hsneq
  have hsSig :
      s ∈ ForwardStarredSignature.signatureTree O cut hout :=
    ForwardStarredSignature.interior_mem_signatureTree O cut hout hs
  have hbefore : ForwardAux s cut := by
    simpa [SkewTree.forwardAuxB] using hmax s hs
  have hsEarly : BeforeCut cut s := ⟨hbefore, hsneq⟩
  have hcutTree : cut ∈ O.tree := by
    exact (List.mem_filter.mp hcut).1
  cases hchildren : SkewTree.immediateSuccs O.tree s with
  | nil =>
      have hh := hs
      simp [SkewTree.interior, hchildren] at hh
  | cons u us =>
      have humem : u ∈ SkewTree.immediateSuccs O.tree s := by
        simp [hchildren]
      have huT : u ∈ O.tree := by
        have hh := humem
        change u ∈ O.tree.filter
          (fun v => SkewTree.immediateSuccB O.tree s v) at hh
        exact (List.mem_filter.mp hh).1
      have huImm : SkewTree.immediateSuccB O.tree s u = true := by
        have hh := humem
        change u ∈ O.tree.filter
          (fun v => SkewTree.immediateSuccB O.tree s v) at hh
        exact (List.mem_filter.mp hh).2
      have huProps := (SkewBranchGeometry.immediateSuccB_iff
        O.tree s u).1 huImm
      have hsu : IsStrictPrefix s u := huProps.2.1
      by_cases huInterior : u ∈ SkewTree.interior O.tree
      · have huSig :
            u ∈ ForwardStarredSignature.signatureTree O cut hout :=
          ForwardStarredSignature.interior_mem_signatureTree
            O cut hout huInterior
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          (ForwardStarredSignature.signatureTree O cut hout)
          s u hsSig huSig hsu
      · have huNotBelow : ¬ IsPrefix cut u := by
          intro hcutU
          have hlen : s.length ≤ cut.length := by
            rcases hbefore with hlt | ⟨heq, _⟩
            · omega
            · omega
          have hsCut : IsPrefix s cut :=
            CutFrontier.prefix_of_prefix_length_le
              hsu.1 hcutU hlen
          have hCutNeU : cut ≠ u := by
            intro heq
            exact huInterior (by simpa [heq] using hcut)
          exact huProps.2.2 cut hcutTree
            ⟨⟨hsCut, hsneq⟩, ⟨hcutU, hCutNeU⟩⟩
        have hEx : u ∈ StarredSignature.exceptionalLeaves O cut := by
          classical
          simp [StarredSignature.exceptionalLeaves,
            huT, huInterior, huNotBelow]
        let r := firstBoundary cut u (hout u hEx)
        have hrSpec : Boundary cut u r :=
          firstBoundary_spec cut u (hout u hEx)
        have hrSig :
            r ∈ ForwardStarredSignature.signatureTree O cut hout := by
          apply (mem_signatureTree_iff O cut hout r).2
          right
          exact ⟨⟨u,hEx⟩,rfl⟩
        have hsr : IsStrictPrefix s r := by
          rcases le_total s.length r.length with hle | hle
          · have hp : IsPrefix s r :=
              CutFrontier.prefix_of_prefix_length_le
                hsu.1 hrSpec.1 hle
            have hne : s ≠ r := by
              intro heq
              have hrEarly : BeforeCut cut r := by
                simpa [← heq] using hsEarly
              exact hrSpec.2.1 hrEarly
            exact ⟨hp, hne⟩
          · have hp : IsPrefix r s :=
              CutFrontier.prefix_of_prefix_length_le
                hrSpec.1 hsu.1 hle
            exact (hrSpec.2.1
              (beforeCut_of_prefix hp hsEarly)).elim
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          (ForwardStarredSignature.signatureTree O cut hout)
          s r hsSig hrSig hsr

/-- A terminal point of the corrected signature, other than
the cut, must be a genuine exceptional-leaf boundary. -/
theorem signatureTerminal_is_exceptional_boundary
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b)
    (hs : s ∈ ForwardStarredSignature.signatureTerminalMarkers
      O cut hout) :
    ∃ t : {t : Node b //
        t ∈ StarredSignature.exceptionalLeaves O cut},
      firstBoundary cut t.1 (hout t.1 t.2) = s := by
  unfold ForwardStarredSignature.signatureTerminalMarkers at hs
  rcases List.mem_filter.mp hs with ⟨hsSig, hproperty⟩
  have htest :
      s ∉ SkewTree.interior
          (ForwardStarredSignature.signatureTree O cut hout)
          ∧ s ≠ cut := by
    simpa using hproperty
  rcases (mem_signatureTree_iff O cut hout s).1 hsSig with hi | hb
  · exact False.elim
      (htest.1 (interiorPersists_of_maxInterior
        O cut hcut hmax hout s hi htest.2))
  · exact hb

/-- All nodes of the forward-corrected literal marker R
are first-exit boundaries of the inclusive forward cut. -/
theorem literalR_is_inclusive_boundary
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (s : Node b)
    (hs : s ∈ ForwardStarredSignature.literalR O cut hout) :
    ForwardInclusiveFrontier.ForwardCutBoundary cut s := by
  classical
  have hr :
      s ∈ ForwardStarredSignature.signatureTerminalMarkers O cut hout ++
        (SkewTree.allFin b).map (fun i => cut ++ [i]) := by
    simpa [ForwardStarredSignature.literalR] using hs
  rcases List.mem_append.mp hr with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      signatureTerminal_is_exceptional_boundary
        O cut hcut hmax hout s hterminal
    rw [← ht]
    exact ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      O cut hout t.1 t.2
  · rcases List.mem_map.mp hchild with ⟨i, hi, his⟩
    rw [← his]
    exact ForwardMarkerFrontierCoverage.cut_child_is_inclusive_boundary
      cut i

/-- Every actual forward-corrected literal marker R has a
genuine support descendant, using the two source marker types. -/
theorem literalR_has_support_descendant
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : Node b)
    (hs : s ∈ ForwardStarredSignature.literalR O cut hout) :
    ∃ t, t ∈ T ∧ IsPrefix s t := by
  classical
  have hr :
      s ∈ ForwardStarredSignature.signatureTerminalMarkers O cut hout ++
        (SkewTree.allFin b).map (fun i => cut ++ [i]) := by
    simpa [ForwardStarredSignature.literalR] using hs
  rcases List.mem_append.mp hr with hterminal | hchild
  · obtain ⟨t, ht⟩ :=
      signatureTerminal_is_exceptional_boundary
        O cut hcut hmax hout s hterminal
    refine ⟨t.1, hST t.1
      (StarredSignature.exceptionalLeaves_spec O cut t.1 t.2).1, ?_⟩
    rw [← ht]
    exact (firstBoundary_spec cut t.1 (hout t.1 t.2)).1
  · rcases List.mem_map.mp hchild with ⟨i, hi, his⟩
    rw [← his]
    exact ForwardMarkerFrontierCoverage.cut_child_has_support_descendant
      T hcomplete hnonsingleton cut hcutT hearly i

/-- The individual unique-frontier theorem holds for every
point of the *literal* forward-corrected R without introducing
marker predicates as unproved hypotheses. -/
theorem literalR_unique_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : Node b)
    (hs : s ∈ ForwardStarredSignature.literalR O cut hout) :
    ∃! f, CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f ∧ IsPrefix s f := by
  exact ForwardInclusiveFrontier.unique_frontier_complete_forward
    T hcomplete hnonsingleton cut s
    (literalR_is_inclusive_boundary
      O cut hcut hmax hout s hs)
    (literalR_has_support_descendant
      O cut hcut hmax hout T hcomplete hnonsingleton
      hST hcutT hearly s hs)

end DualTree.ForwardSignatureInteriorPersistence
