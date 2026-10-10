import DualTree.ForwardQSourceTerminals
import DualTree.ForwardQMarkerCoverage
import DualTree.ForwardSignatureInteriorExact

/-!
# Exact original interior of the corrected forward Q support

The corrected Q support is the original interior
  Int(S') ∪ {cut} = Int(S)
plus a selected leaf in each genuine sorted literal R frontier cone.

ForwardQSourceTerminals proves the easy inclusion
  Int(Q) ⊆ Int(S).
To reverse it, every old interior s ≠ cut remains interior in
the corrected signature S'. Choose one actual immediate signature
successor u. If u belongs to the old interior, it is retained in Q.
Otherwise it is the first boundary of an exceptional source leaf.
That boundary lies in literal R and has a genuine projected Q
descendant. Either way s retains a strict Q descendant.
The cut itself has a Q descendant via any ambient child marker.

Thus for positive branching the Q interior is *exactly* the
source interior, without assuming preservation under an old
printed-order embedding or an abstract Q prefix-isomorphism.

This does not yet prove the Q node set is semi-complete skew.
Its rank/ambient-length clauses and full directional occupancy
remain separate proof obligations.
-/

namespace DualTree.ForwardQInteriorExact

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- An exceptional-leaf boundary is a terminal marker of the
corrected signature (unless it is the cut, which is impossible
because the boundary lies outside the inclusive cut). Thus
it belongs to the exact corrected literal R. -/
theorem exceptional_boundary_mem_literalR
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t)
    (t : {t : Node b //
      t ∈ StarredSignature.exceptionalLeaves O cut}) :
    firstBoundary cut t.1 (hout t.1 t.2) ∈
      ForwardStarredSignature.literalR O cut hout := by
  classical
  let r := firstBoundary cut t.1 (hout t.1 t.2)
  have hrSig : r ∈ ForwardStarredSignature.signatureTree
      O cut hout :=
    (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
      O cut hout r).2 (Or.inr ⟨t, rfl⟩)
  have hrNotInterior : r ∉
      SkewTree.interior (ForwardStarredSignature.signatureTree
        O cut hout) :=
    ForwardSignatureInteriorExact.exceptional_boundary_not_interior
      O cut hmax hout t
  have hrOutside : ¬ ForwardAux r cut :=
    (ForwardMarkerFrontierCoverage.exceptional_boundary_is_inclusive
      O cut hout t.1 t.2).1
  have hrNe : r ≠ cut := by
    intro heq
    subst r
    exact hrOutside (CanonicalForwardAuxIso.forwardAux_refl cut)
  have hrTerminal :
      r ∈ ForwardStarredSignature.signatureTerminalMarkers
        O cut hout := by
    unfold ForwardStarredSignature.signatureTerminalMarkers
    apply List.mem_filter.mpr
    refine ⟨hrSig, ?_⟩
    simpa [hrNotInterior, hrNe]
  change r ∈
    (ForwardStarredSignature.signatureTerminalMarkers O cut hout ++
      (SkewTree.allFin b).map (fun i => cut ++ [i])).dedup
  simp only [List.mem_dedup, List.mem_append]
  exact Or.inl hrTerminal

/-- Every original interior node before the final cut has an
actual strict descendant in the corrected Q support. -/
theorem nonlast_original_interior_persists
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (hne : s ≠ c.cut) :
    s ∈ SkewTree.interior (nodes c x).toList := by
  let S' := ForwardStarredSignature.signatureTree
    c.source c.cut c.hout
  let W := nodes c x
  have hsS' : s ∈ SkewTree.interior S' :=
    (ForwardSignatureInteriorExact.signature_interior_iff_original_ne_cut
      c.source c.cut c.hcut c.hmax c.hout s).2 ⟨hs, hne⟩
  have hsW : s ∈ W.toList := by
    apply Finset.mem_toList.mpr
    exact ForwardQFixedBase.originalInterior_mem_Q c x s hs
  have hnon :
      !(SkewTree.immediateSuccs S' s).isEmpty = true :=
    (List.mem_filter.mp hsS').2
  cases hsucc : SkewTree.immediateSuccs S' s with
  | nil =>
      simp [hsucc] at hnon
  | cons u us =>
      have huSucc : u ∈ SkewTree.immediateSuccs S' s := by
        simp [hsucc]
      have huS' : u ∈ S' := by
        change u ∈ S'.filter
          (fun t => SkewTree.immediateSuccB S' s t) at huSucc
        exact (List.mem_filter.mp huSucc).1
      have hstep : SkewTree.immediateSuccB S' s u = true := by
        change u ∈ S'.filter
          (fun t => SkewTree.immediateSuccB S' s t) at huSucc
        exact (List.mem_filter.mp huSucc).2
      have hsu : IsStrictPrefix s u :=
        ((SkewBranchGeometry.immediateSuccB_iff S' s u).1 hstep).2.1
      rcases (ForwardSignatureInteriorPersistence.mem_signatureTree_iff
          c.source c.cut c.hout u).1 huS' with huOld | ⟨t, ht⟩
      · have huW : u ∈ W.toList := by
          apply Finset.mem_toList.mpr
          exact ForwardQFixedBase.originalInterior_mem_Q c x u huOld
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          W.toList s u hsW huW hsu
      · have huR : u ∈ ForwardStarredSignature.literalR
            c.source c.cut c.hout := by
          rw [← ht]
          exact exceptional_boundary_mem_literalR
            c.source c.cut c.hmax c.hout t
        obtain ⟨v, hvW, hsv⟩ :=
          ForwardQMarkerCoverage.strict_Q_descendant_of_literal_marker
            c x s u hsu huR
        have hvW' : v ∈ W.toList :=
          Finset.mem_toList.mpr hvW
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          W.toList s v hsW hvW' hsv

/-- The retained maximal source interior vertex is interior
in the actual corrected Q tree, using a literal child marker. -/
theorem cut_is_Q_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    c.cut ∈ SkewTree.interior (nodes c x).toList := by
  obtain ⟨t, ht, hct⟩ :=
    ForwardQMarkerCoverage.cut_has_strict_Q_descendant hb c x
  have hcutW : c.cut ∈ (nodes c x).toList := by
    apply Finset.mem_toList.mpr
    exact ForwardQFixedBase.cut_mem_Q c x
  have htW : t ∈ (nodes c x).toList :=
    Finset.mem_toList.mpr ht
  exact SignatureInteriorPersistence.interior_of_strict_descendant
    (nodes c x).toList c.cut t hcutW htW hct

/-- The corrected Q support has exactly the original interior.
This is the first complete, source-facing identification of the
Q interior under the globally repaired forward order. -/
theorem Q_interior_iff_original
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b) :
    s ∈ SkewTree.interior (nodes c x).toList ↔
      s ∈ SkewTree.interior c.source.tree := by
  constructor
  · exact ForwardQSourceTerminals.Q_interior_subset_original c x s
  · intro hs
    by_cases heq : s = c.cut
    · subst s
      exact cut_is_Q_interior hb c x
    · exact nonlast_original_interior_persists c x s hs heq

end DualTree.ForwardQInteriorExact
