import DualTree.ForwardProjectedTerminalOrder
import DualTree.LastInteriorBranching

/-!
# Definition 26 with the globally repaired forward auxiliary order

The published signature uses the strict initial segment before the
last interior cut in the paper's length-first *reverse*-lex order.
A candidate repair of Lemma 27 replaces that convention everywhere
by length-first *forward*-lex order.

This module develops the corrected boundary and signature on the
original ambient prefix paths, without assuming the existence of
the conditional minima. As in the source proof, their existence
follows because a final interior cut is fully branching and no
exceptional leaf can precede it.

We introduce new definitions rather than silently modifying
SignatureBoundary and StarredSignature.signatureTree, so the
published/printed model remains available for adversarial audit.

The resulting signature R is a well-typed list and the immediate
children of the maximal interior cut belong to R. The remaining
projection construction and the smooth colouring are not yet
proved for this corrected signature.
-/

namespace DualTree.ForwardSignatureBoundary

/-- The strict length-first forward-lex initial segment before cut. -/
def BeforeCut {b : Nat} (cut s : Node b) : Prop :=
  ForwardAux s cut ∧ s ≠ cut

/-- A proper prefix of the cut is strictly earlier in the
corrected auxiliary order. -/
theorem beforeCut_of_strictPrefix {b : Nat}
    {r cut : Node b} (h : IsStrictPrefix r cut) :
    BeforeCut cut r := by
  have hlen : r.length < cut.length := by
    have hle := prefix_length_le h.1
    by_contra hn
    have heqLen : r.length = cut.length := by omega
    have heq : r = cut :=
      CutPreservation.prefix_eq_of_length_eq h.1 heqLen
    exact h.2 heq
  exact ⟨Or.inl hlen, h.2⟩

/-- Prefix-minimal node on a path that lies outside the
strict corrected auxiliary initial segment. -/
def Boundary {b : Nat} (cut t s : Node b) : Prop :=
  IsPrefix s t ∧ ¬ BeforeCut cut s ∧
  ∀ r, IsStrictPrefix r s → BeforeCut cut r

theorem boundary_at_cut {b : Nat} (cut : Node b) :
    Boundary cut cut cut := by
  refine ⟨isPrefix_refl cut, ?_, ?_⟩
  · intro h
    exact h.2 rfl
  · intro r hr
    exact beforeCut_of_strictPrefix hr

theorem boundary_iff_frontier {b : Nat}
    (cut t s : Node b) :
    Boundary cut t s ↔
      CutFrontier.Frontier
        (SignatureBoundary.ambientPath t)
        (BeforeCut cut) s := by
  constructor
  · rintro ⟨hpre, hout, hmin⟩
    exact ⟨SignatureBoundary.prefix_mem_ambientPath hpre,
      hout, fun r _ hr => hmin r hr⟩
  · rintro ⟨hmem, hout, hmin⟩
    have hpre : IsPrefix s t :=
      SignatureBoundary.mem_ambientPath_prefix hmem
    refine ⟨hpre, hout, ?_⟩
    intro r hr
    exact hmin r (SignatureBoundary.prefix_mem_ambientPath
      (isPrefix_trans hr.1 hpre)) hr

/-- Every path which exits the corrected strict auxiliary
cut has a unique first boundary node. -/
theorem existsUnique_boundary_on_path {b : Nat}
    (cut t : Node b)
    (hout : ¬ BeforeCut cut t) :
    ∃! s, Boundary cut t s := by
  have ht : t ∈ SignatureBoundary.ambientPath t :=
    SignatureBoundary.prefix_mem_ambientPath (isPrefix_refl t)
  obtain ⟨s, ⟨hs, hpre⟩, hunique⟩ :=
    CutFrontier.exists_unique_frontier_above
      (SignatureBoundary.ambientPath t)
      (BeforeCut cut) ht hout
  refine ⟨s, (boundary_iff_frontier cut t s).2 hs, ?_⟩
  intro u hu
  exact hunique u
    ⟨(boundary_iff_frontier cut t u).1 hu, hu.1⟩

noncomputable def firstBoundary {b : Nat}
    (cut t : Node b) (hout : ¬ BeforeCut cut t) : Node b :=
  Classical.choose (existsUnique_boundary_on_path cut t hout)

theorem firstBoundary_spec {b : Nat}
    (cut t : Node b) (hout : ¬ BeforeCut cut t) :
    Boundary cut t (firstBoundary cut t hout) :=
  (Classical.choose_spec (existsUnique_boundary_on_path cut t hout)).1

end DualTree.ForwardSignatureBoundary

namespace DualTree.ForwardStarredSignature

open ForwardSignatureBoundary

/-- At any repaired final branching cut, every exceptional
leaf has a genuine corrected boundary. -/
theorem exceptionalLeaves_not_before_of_fullBefore
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hfull : SkewTree.fullBeforeB
      SkewTree.forwardAuxB O.tree cut = true)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves O cut) :
    ¬ BeforeCut cut t := by
  obtain ⟨hmem, hnotInterior, _⟩ :=
    StarredSignature.exceptionalLeaves_spec O cut t ht
  have hleaf : SkewTree.immediateSuccs O.tree t = [] :=
    StarredSignature.immediateSuccs_nil_of_not_interior
      O.tree t hmem hnotInterior
  have hneq : t ≠ cut := by
    intro h
    subst t
    exact hnotInterior hcut
  have hnot :=
    StarredSignature.leaf_not_before_of_fullBefore
      hb O.tree SkewTree.forwardAuxB cut t
      hfull hmem hleaf hneq
  intro hearly
  exact hnot (by
    simpa [SkewTree.forwardAuxB] using hearly.1)

/-- No extra leaf-boundary existence hypothesis is
needed for a genuine maximal interior cut in the
corrected forward-auxiliary skew class. -/
theorem exceptionalLeaves_not_before_of_maxInterior
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (t : Node b)
    (ht : t ∈ StarredSignature.exceptionalLeaves O cut) :
    ¬ BeforeCut cut t :=
  exceptionalLeaves_not_before_of_fullBefore
    hb O cut hcut
    (StarredSignature.fullBefore_at_maxInterior
      O cut hcut hmax) t ht

/-- Corrected signature skeleton: original interior plus
the first boundary point of each exceptional leaf. -/
noncomputable def signatureTree
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) :
    List (Node b) := by
  classical
  let boundary := (StarredSignature.exceptionalLeaves O cut).attach.map
    (fun t => firstBoundary cut t.1 (hout t.1 t.2))
  exact (SkewTree.interior O.tree ++ boundary).eraseDups

theorem interior_mem_signatureTree
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SkewTree.interior O.tree) :
    s ∈ signatureTree O cut hout := by
  classical
  unfold signatureTree
  simp [hs]

/-- Definition 26's corrected signature can be constructed
directly from the maximal interior cut. -/
noncomputable def signatureTree_at_maxInterior
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true) :
    List (Node b) :=
  signatureTree O cut
    (exceptionalLeaves_not_before_of_maxInterior
      hb O cut hcut hmax)

/-- Corrected literal terminal markers of the signature. -/
noncomputable def signatureTerminalMarkers
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) : List (Node b) := by
  classical
  let S' := signatureTree O cut hout
  exact S'.filter (fun s =>
    decide (s ∉ SkewTree.interior S' ∧ s ≠ cut))

/-- The exact forward-order variant of the paper's R:
signature terminals other than the cut, together with all
ambient children of the cut. -/
noncomputable def literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) : List (Node b) := by
  classical
  exact (signatureTerminalMarkers O cut hout ++
    (SkewTree.allFin b).map (fun i => cut ++ [i])).dedup

/-- The forward-corrected marker list has distinct entries. -/
theorem literalR_nodup
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) :
    (literalR O cut hout).Nodup := by
  classical
  unfold literalR
  exact List.nodup_dedup _

/-- Every immediate ambient child of the retained maximal
interior cut is explicitly in the repaired literal R. -/
theorem cut_child_mem_literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (i : Fin b) :
    cut ++ [i] ∈ literalR O cut hout := by
  classical
  unfold literalR
  simp only [List.mem_dedup, List.mem_append]
  right
  exact List.mem_map.mpr
    ⟨i, DirectionalSupport.mem_allFin b i, rfl⟩

end DualTree.ForwardStarredSignature
