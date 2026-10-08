import DualTree.LiteralSignatureR

/-!
# Persistence of old interior nodes under the signature construction

For the maximal interior cut of a starred tree, Definition 26 replaces
exceptional leaves by their first boundary beyond the cut. Every old
interior node other than the cut remains interior to this signature:
an immediate successor either remains interior itself, or is an
exceptional leaf whose boundary supplies a strict signature descendant.

This closes the remaining geometric condition in the literal-R
frontier correspondence of Lemma 27. The subsequent variable-word
coding, coloring lift, and Hales--Jewett argument are still open.
-/

namespace DualTree.SignatureInteriorPersistence

/-- A node of a finite support with a strict support descendant is interior. -/
theorem interior_of_strict_descendant
    {b : Nat} (S : List (Node b))
    (s t : Node b)
    (hs : s ∈ S) (ht : t ∈ S)
    (hst : IsStrictPrefix s t) :
    s ∈ SkewTree.interior S := by
  rcases SkewBranchGeometry.exists_first_immediate_on_path
      S s t ht hst with ⟨u, huT, huImm, _, _⟩
  have huSucc : u ∈ SkewTree.immediateSuccs S s := by
    change u ∈ S.filter (fun v => SkewTree.immediateSuccB S s v)
    exact List.mem_filter.mpr ⟨huT, huImm⟩
  have hnonempty : (SkewTree.immediateSuccs S s).isEmpty = false := by
    cases hlist : SkewTree.immediateSuccs S s with
    | nil => simp [hlist] at huSucc
    | cons v vs => rfl
  simp [SkewTree.interior, hs, hnonempty]

/--
All old interior nodes except the maximal interior cut remain interior
in the signature tree. The leaf-boundary existence proof remains
an explicit argument, already provided by the maximal-interior lemma.
-/
theorem interiorPersists_of_maxInterior
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    LiteralSignatureR.InteriorPersists O cut hout := by
  intro s hs hsneq
  have hsSig :
      s ∈ StarredSignature.signatureTree O cut hout :=
    StarredSignature.interior_mem_signatureTree O cut hout hs
  have hbeforeB : SkewTree.paperAuxB s cut = true := hmax s hs
  have hbefore : PaperAux s cut := by
    simpa [SkewTree.paperAuxB] using hbeforeB
  have hsEarly : SignatureBoundary.BeforeCut cut s :=
    ⟨hbefore, hsneq⟩
  have hcutTree : cut ∈ O.tree := by
    have hh := hcut
    simp [SkewTree.interior] at hh
    aesop
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
            u ∈ StarredSignature.signatureTree O cut hout :=
          StarredSignature.interior_mem_signatureTree
            O cut hout huInterior
        exact interior_of_strict_descendant
          (StarredSignature.signatureTree O cut hout)
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
        let r := SignatureBoundary.firstBoundary cut u (hout u hEx)
        have hrSpec : SignatureBoundary.Boundary cut u r :=
          SignatureBoundary.firstBoundary_spec cut u (hout u hEx)
        have hrBoundary :
            r ∈ SignatureMarker.boundaryMarkers O cut hout := by
          classical
          unfold SignatureMarker.boundaryMarkers
          apply List.mem_map.mpr
          refine ⟨⟨u, hEx⟩, ?_, rfl⟩
          simp
        have hrSig :
            r ∈ StarredSignature.signatureTree O cut hout :=
          (LiteralSignatureR.mem_signatureTree_iff O cut hout r).2
            (Or.inr hrBoundary)
        have hsr : IsStrictPrefix s r := by
          rcases le_total s.length r.length with hle | hle
          · have hp : IsPrefix s r :=
              CutFrontier.prefix_of_prefix_length_le
                hsu.1 hrSpec.1 hle
            have hne : s ≠ r := by
              intro heq
              have hrEarly : SignatureBoundary.BeforeCut cut r := by
                simpa [← heq] using hsEarly
              exact hrSpec.2.1 hrEarly
            exact ⟨hp, hne⟩
          · have hp : IsPrefix r s :=
              CutFrontier.prefix_of_prefix_length_le
                hrSpec.1 hsu.1 hle
            exact (hrSpec.2.1
              (ConeFrontier.beforeCut_of_prefix hp hsEarly)).elim
        exact interior_of_strict_descendant
          (StarredSignature.signatureTree O cut hout)
          s r hsSig hrSig hsr

/-- Interior persistence at a maximal interior cut, without a leaf-boundary axiom. -/
theorem interiorPersists_at_maxInterior
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true) :
    LiteralSignatureR.InteriorPersists O cut
      (StarredSignature.exceptionalLeaves_not_before_of_maxInterior
        hb O cut hcut hmax) :=
  interiorPersists_of_maxInterior O cut hcut hmax
    (StarredSignature.exceptionalLeaves_not_before_of_maxInterior
      hb O cut hcut hmax)

/--
The source's literal R marker/frontier correspondence at a maximal
interior cut, without a separate interior-persistence hypothesis.
-/
theorem literalR_unique_frontier_of_maxInterior
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    {s : Node b}
    (hs : s ∈ LiteralSignatureR.literalR O cut hout) :
    ∃! f : Node b,
      CutFrontier.Frontier T (fun u => PaperAux u cut) f ∧
      IsPrefix s f :=
  LiteralSignatureR.literalR_unique_inclusive_frontier
    O cut hout
    (interiorPersists_of_maxInterior O cut hcut hmax hout)
    T hcomplete hnonsingleton hST hcutT hlevel hs

end DualTree.SignatureInteriorPersistence
