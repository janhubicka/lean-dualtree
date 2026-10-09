import DualTree.Lemma27QMarkerCoverage

/-!
# Persistence of the original interior in the reconstructed Q tree

The earlier audit established Int(S_w) ⊆ Int(S), since all added
D₂ points are terminal leaves. The reverse inclusion uses *every*
literal marker, not just cardinality:

* every original interior vertex other than t₀ remains interior
  in the Definition 26 signature S';
* every immediate successor of such a vertex in S' either belongs
  to the original interior or is an exceptional boundary in R;
* each R marker has a projected descendant in S_w;
* the distinguished cut t₀ has an immediate child in R when b>0.

Consequently, the set of interior vertices of the reconstructed
finite Q node set is exactly Int(S), for positive branching.
The semi-complete skew axioms on S_w, its height bounds, and the
construction of g_w still remain separate obligations.
-/

namespace DualTree.Lemma27QInterior

/-- A proper prefix remains proper after further extension. -/
theorem strictPrefix_trans_prefix {b : Nat}
    {s u t : Node b}
    (hsu : IsStrictPrefix s u)
    (hut : IsPrefix u t) :
    IsStrictPrefix s t := by
  refine ⟨isPrefix_trans hsu.1 hut, ?_⟩
  intro heq
  have hlt := MeetClosedFromBranching.length_lt_of_strictPrefix hsu
  have hle := prefix_length_le hut
  rw [← heq] at hle
  omega

/-- Every original interior vertex belongs to the Q node set,
since its fixed old base is exactly Int(S). -/
theorem originalInterior_mem_Q
    {b n l k m : Nat} {α : Type*}
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b)
    (hs : s ∈ SkewTree.interior O.tree) :
    s ∈ (Lemma27SignatureTree.sourceSignatureNodes
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  have hbase : s ∈ Lemma27SignatureTree.oldSignatureBase O cut hout :=
    (Lemma27QTreeCount.oldBase_mem_iff_original_interior
      O cut hcut hmax hout s).2 hs
  have hQ :=
    Lemma27SignatureTree.signatureNodes_base
      T hcomplete cut hcutT hlevel hm
      (Lemma27SignatureTree.oldSignatureBase O cut hout) x s hbase
  simpa only [Finset.mem_toList, Lemma27SignatureTree.sourceSignatureNodes]
    using hQ

/-- Any strict predecessor of a literal marker has a strict
descendant in the reconstructed Q tree. -/
theorem strict_Q_descendant_of_literal_marker
    {b n l k m : Nat} {α : Type*}
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s u : Node b)
    (hsu : IsStrictPrefix s u)
    (hu : u ∈ LiteralSignatureR.literalR O cut hout) :
    ∃ t : Node b,
      t ∈ Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x ∧
      IsStrictPrefix s t := by
  obtain ⟨t, ht, hut⟩ :=
    Lemma27QMarkerCoverage.literalMarker_has_Q_descendant
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x u hu
  exact ⟨t, ht, strictPrefix_trans_prefix hsu hut⟩

/-- Every original interior vertex *other* than the maximal cut
keeps an actual descendant, and so remains interior in S_w. -/
theorem nonlast_original_interior_persists
    {b n l k m : Nat} {α : Type*}
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b) (hs : s ∈ SkewTree.interior O.tree)
    (hne : s ≠ cut) :
    s ∈ SkewTree.interior
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  let S' := StarredSignature.signatureTree O cut hout
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hsS' : s ∈ SkewTree.interior S' :=
    (SignatureInteriorExact.signature_interior_iff_original_ne_cut
      O cut hcut hmax hout s).2 ⟨hs, hne⟩
  have hsW : s ∈ W.toList :=
    originalInterior_mem_Q O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x s hs
  have hfilter :
      s ∈ S'.filter (fun t => !(SkewTree.immediateSuccs S' t).isEmpty) :=
    hsS'
  have hnon := (List.mem_filter.mp hfilter).2
  cases hsucc : SkewTree.immediateSuccs S' s with
  | nil =>
      simp [hsucc] at hnon
  | cons u us =>
      have huSucc : u ∈ SkewTree.immediateSuccs S' s := by simp [hsucc]
      have hu' : u ∈ S'.filter
          (fun t => SkewTree.immediateSuccB S' s t) := huSucc
      have huS' : u ∈ S' := (List.mem_filter.mp hu').1
      have hstep : SkewTree.immediateSuccB S' s u = true :=
        (List.mem_filter.mp hu').2
      have hsu : IsStrictPrefix s u :=
        ((SkewBranchGeometry.immediateSuccB_iff S' s u).1 hstep).2.1
      rcases (LiteralSignatureR.mem_signatureTree_iff O cut hout u).1 huS'
          with huOld | huBoundary
      · have huW : u ∈ W.toList :=
          originalInterior_mem_Q O cut hcut hmax hout
            T hcomplete hST hcutT hlevel hm x u huOld
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          W.toList s u hsW huW hsu
      · have huR : u ∈ LiteralSignatureR.literalR O cut hout :=
          Lemma27QMarkerCoverage.boundaryMarker_mem_literalR
            O cut hcut hmax hout huBoundary
        obtain ⟨t, htW, hst⟩ :=
          strict_Q_descendant_of_literal_marker
            O cut hcut hmax hout T hcomplete hST hcutT hlevel
            hm x s u hsu huR
        have htW' : t ∈ W.toList := by simpa only [Finset.mem_toList] using htW
        exact SignatureInteriorPersistence.interior_of_strict_descendant
          W.toList s t hsW htW' hst

/-- If b>0, the old maximal interior cut has a literal child marker,
whose projected descendant makes the cut interior in S_w. -/
theorem cut_interior_of_positive_branching
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    cut ∈ SkewTree.interior
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList := by
  let i : Fin b := ⟨0, hb⟩
  have hchild : cut ++ [i] ∈ LiteralSignatureR.literalR O cut hout :=
    Lemma27QMarkerCoverage.child_mem_literalR O cut hout i
  have hstrict : IsStrictPrefix cut (cut ++ [i]) := by
    refine ⟨⟨[i], rfl⟩, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp at hlen
  obtain ⟨t, htW, hct⟩ :=
    strict_Q_descendant_of_literal_marker
      O cut hcut hmax hout T hcomplete hST hcutT hlevel
      hm x cut (cut ++ [i]) hstrict hchild
  let W := Lemma27SignatureTree.sourceSignatureNodes
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x
  have hcW : cut ∈ W.toList :=
    originalInterior_mem_Q O cut hcut hmax hout
      T hcomplete hST hcutT hlevel hm x cut hcut
  have htW' : t ∈ W.toList := by simpa only [Finset.mem_toList] using htW
  exact SignatureInteriorPersistence.interior_of_strict_descendant
    W.toList cut t hcW htW' hct

/-- The old original interior is preserved exactly in the
reconstructed Q node set, for positive branching. -/
theorem source_interior_iff_original
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (s : Node b) :
    s ∈ SkewTree.interior
      (Lemma27SignatureTree.sourceSignatureNodes
        O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x).toList ↔
      s ∈ SkewTree.interior O.tree := by
  constructor
  · exact Lemma27QTerminal.sourceSignatureNodes_interior_subset_original
      O cut hcut hmax hout T hcomplete hST hcutT hlevel hm x s
  · intro hs
    by_cases heq : s = cut
    · subst s
      exact cut_interior_of_positive_branching hb O cut hcut hmax
        hout T hcomplete hST hcutT hlevel hm x
    · exact nonlast_original_interior_persists O cut hcut hmax
        hout T hcomplete hST hcutT hlevel hm x s hs heq

end DualTree.Lemma27QInterior
