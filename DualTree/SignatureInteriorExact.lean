import DualTree.Lemma27SignatureTree
import DualTree.SignatureInteriorPersistence

/-!
# Exact interior of the Definition 26 signature tree

Let (S,g) be a starred word and let t₀ be maximal in Int(S)
under the paper's auxiliary order. Its Definition 26 signature
tree S' is Int(S) together with the first outside-cut boundaries
of exceptional leaves.

The previous audit proved that every old interior node other
than t₀ remains interior in S'. Here we prove the converse:
a boundary marker cannot become an interior node of S', and
t₀ has no strict descendant in S'. Consequently

    Int(S') = Int(S) \ {t₀}.

In particular every vertex in Int(S') ∪ {t₀}, the old part of
the Lemma 27 tree component S_w, is at or before the cut.
This discharges the hypothesis still explicit in the
marked-leaf separation and cardinality argument.

No claim about the interior of the *new* S_w or its
semi-completeness is made by this module.
-/

namespace DualTree.SignatureInteriorExact

/-- No exceptional signature boundary can lie below t₀, because
the exceptional leaf from which it was selected is not below t₀. -/
theorem boundaryMarker_not_below_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SignatureMarker.boundaryMarkers O cut hout) :
    ¬ IsPrefix cut s := by
  classical
  unfold SignatureMarker.boundaryMarkers at hs
  rcases List.mem_map.mp hs with ⟨t, ht, heq⟩
  have hnot : ¬ IsPrefix cut t.1 :=
    (StarredSignature.exceptionalLeaves_spec O cut t.1 t.2).2.2
  have hboundary : IsPrefix
      (SignatureBoundary.firstBoundary cut t.1 (hout t.1 t.2)) t.1 :=
    (SignatureBoundary.firstBoundary_spec cut t.1 (hout t.1 t.2)).1
  intro hcuts
  have hc : IsPrefix cut t.1 :=
    isPrefix_trans (by simpa only [← heq] using hcuts) hboundary
  exact hnot hc

/-- No node of the signature tree can be a proper extension of t₀,
when t₀ was chosen maximal in the original interior. -/
theorem no_strict_signature_descendant_of_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ StarredSignature.signatureTree O cut hout) :
    ¬ IsStrictPrefix cut s := by
  intro hcs
  rcases (LiteralSignatureR.mem_signatureTree_iff
    O cut hout s).1 hs with hi | hb
  · have hbefore : PaperAux s cut := by
      simpa [SkewTree.paperAuxB] using hmax s hi
    have hlen : s.length ≤ cut.length := by
      rcases hbefore with hlt | ⟨heq, _⟩ <;> omega
    have hstrict := MeetClosedFromBranching.length_lt_of_strictPrefix hcs
    omega
  · exact (boundaryMarker_not_below_cut O cut hout hb) hcs.1

/-- The distinguished maximal original interior node becomes a leaf
of the Definition 26 signature tree. -/
theorem maximal_cut_not_signature_interior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    cut ∉ SkewTree.interior (StarredSignature.signatureTree O cut hout) := by
  let S := StarredSignature.signatureTree O cut hout
  intro hc
  change cut ∈ S.filter (fun s => !(SkewTree.immediateSuccs S s).isEmpty) at hc
  have hflag := (List.mem_filter.mp hc).2
  cases hsucc : SkewTree.immediateSuccs S cut with
  | nil =>
      simp [hsucc] at hflag
  | cons u us =>
      have hu : u ∈ SkewTree.immediateSuccs S cut := by
        simp [hsucc]
      have huS : u ∈ S := by
        change u ∈ S.filter (fun v => SkewTree.immediateSuccB S cut v) at hu
        exact (List.mem_filter.mp hu).1
      have hstep : SkewTree.immediateSuccB S cut u = true := by
        have hu' : u ∈ S.filter
          (fun v => SkewTree.immediateSuccB S cut v) := hu
        exact (List.mem_filter.mp hu').2
      have hproper : IsStrictPrefix cut u :=
        ((SkewBranchGeometry.immediateSuccB_iff S cut u).1 hstep).2.1
      exact (no_strict_signature_descendant_of_cut
        O cut hmax hout huS) hproper

/-- Every interior vertex of the signature tree was already an
interior vertex of the original starred tree. -/
theorem signature_interior_subset_original
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SkewTree.interior
      (StarredSignature.signatureTree O cut hout)) :
    s ∈ SkewTree.interior O.tree := by
  let S := StarredSignature.signatureTree O cut hout
  have hs' : s ∈ S := by
    have h : s ∈ S.filter (fun t => !(SkewTree.immediateSuccs S t).isEmpty) := hs
    exact (List.mem_filter.mp h).1
  rcases (LiteralSignatureR.mem_signatureTree_iff O cut hout s).1 hs'
      with horig | hboundary
  · exact horig
  · have hboundaryCut :=
      InclusiveSignatureMarkers.boundaryMarker_paperCutBoundary
        O cut hout hboundary
    have hsNotEarly : ¬ PaperAux s cut := hboundaryCut.1
    have h : s ∈ S.filter
      (fun t => !(SkewTree.immediateSuccs S t).isEmpty) := hs
    have hflag := (List.mem_filter.mp h).2
    cases hsucc : SkewTree.immediateSuccs S s with
    | nil =>
        simp [hsucc] at hflag
    | cons u us =>
        have hu : u ∈ SkewTree.immediateSuccs S s := by
          simp [hsucc]
        have huS : u ∈ S := by
          change u ∈ S.filter (fun t => SkewTree.immediateSuccB S s t) at hu
          exact (List.mem_filter.mp hu).1
        have hstep : SkewTree.immediateSuccB S s u = true := by
          have hu' : u ∈ S.filter
            (fun t => SkewTree.immediateSuccB S s t) := hu
          exact (List.mem_filter.mp hu').2
        have hsu : IsStrictPrefix s u :=
          ((SkewBranchGeometry.immediateSuccB_iff S s u).1 hstep).2.1
        rcases (LiteralSignatureR.mem_signatureTree_iff
          O cut hout u).1 huS with huOrig | huBoundary
        · have huEarly : PaperAux u cut := by
            simpa [SkewTree.paperAuxB] using hmax u huOrig
          exact (hsNotEarly
            (CutPreservation.paperAux_of_prefix hsu.1 huEarly)).elim
        · have huCut :=
            InclusiveSignatureMarkers.boundaryMarker_paperCutBoundary
              O cut hout huBoundary
          have heq : s = u :=
            MarkerAntichain.eq_of_prefix_boundaries
              cut s u hboundaryCut huCut hsu.1
          exact (hsu.2 heq).elim

/-- The exact source-facing identity for the signature interior. -/
theorem signature_interior_iff_original_ne_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : Node b) :
    s ∈ SkewTree.interior (StarredSignature.signatureTree O cut hout) ↔
      s ∈ SkewTree.interior O.tree ∧ s ≠ cut := by
  constructor
  · intro hs
    refine ⟨signature_interior_subset_original
      O cut hmax hout hs, ?_⟩
    intro heq
    subst s
    exact maximal_cut_not_signature_interior O cut hmax hout hs
  · intro ⟨hs, hsne⟩
    exact SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout s hs hsne

/-- The old base Int(S') ∪ {t₀} of the Q tree lies entirely at
or before the distinguished cut in the auxiliary order. -/
theorem oldSignatureBase_before_cut
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (s : Node b)
    (hs : s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout) :
    PaperAux s cut := by
  change s ∈ SkewTree.interior
    (StarredSignature.signatureTree O cut hout) ++ [cut] at hs
  rcases List.mem_append.mp hs with hsInt | hsCut
  · have hsOld := signature_interior_subset_original
      O cut hmax hout hsInt
    simpa [SkewTree.paperAuxB] using hmax s hsOld
  · have hsc : s = cut := by simpa using hsCut
    subst s
    refine Or.inr ⟨rfl, ?_⟩
    rcases finLexLE_total cut cut with h | h <;> exact h

end DualTree.SignatureInteriorExact
