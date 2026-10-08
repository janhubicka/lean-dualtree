import DualTree.LiteralFrontierCleanup

/-!
# Indexing literal signature markers by support frontiers

The geometric assertions at the start of Lemma 27 are slightly stronger
than a separate existence/uniqueness theorem for each marker: different
members of the literal set R must correspond to different support
frontiers. This file constructs the corresponding choice map and proves
it injective, using the exact inclusive-cut frontier and the literal R.

No arbitrary enumeration or variable-word coding is introduced here.
-/

namespace DualTree.LiteralFrontierIndex

/-- The unique inclusive-cut support frontier assigned to a literal R marker. -/
noncomputable def frontierFor
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    Node b :=
  Classical.choose
    (LiteralFrontierCleanup.literalR_unique_frontier
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s.2)

/-- The chosen node is a genuine frontier extending the marker. -/
theorem frontierFor_spec
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout}) :
    CutFrontier.Frontier T (fun u => PaperAux u cut)
        (frontierFor O cut hcut hmax hout T hcomplete hST hcutT hlevel s) ∧
      IsPrefix s.1
        (frontierFor O cut hcut hmax hout T hcomplete hST hcutT hlevel s) :=
  (Classical.choose_spec
    (LiteralFrontierCleanup.literalR_unique_frontier
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s.2)).1

/-- The chosen frontier is the unique one above the given literal R marker. -/
theorem frontierFor_eq_of_frontier
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ LiteralSignatureR.literalR O cut hout})
    (f : Node b)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) f)
    (hsf : IsPrefix s.1 f) :
    frontierFor O cut hcut hmax hout T hcomplete hST hcutT hlevel s = f := by
  exact ((Classical.choose_spec
    (LiteralFrontierCleanup.literalR_unique_frontier
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s.2)).2
        f ⟨hf, hsf⟩).symm

/-- Distinct literal R markers have distinct assigned frontier nodes. -/
theorem frontierFor_injective
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
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k) :
    Function.Injective
      (frontierFor O cut hcut hmax hout T hcomplete hST hcutT hlevel) := by
  intro s t heq
  have hs := (frontierFor_spec O cut hcut hmax hout T
    hcomplete hST hcutT hlevel s).2
  have ht := (frontierFor_spec O cut hcut hmax hout T
    hcomplete hST hcutT hlevel t).2
  have ht' :
      IsPrefix t.1
        (frontierFor O cut hcut hmax hout T hcomplete hST hcutT hlevel s) := by
    rw [heq]
    exact ht
  have hpersist :=
    SignatureInteriorPersistence.interiorPersists_of_maxInterior
      O cut hcut hmax hout
  have hst : s.1 = t.1 :=
    LiteralSignatureR.literalR_unique_marker_in_cone
      O cut hout hpersist s.2 t.2 hs ht'
  exact Subtype.ext hst

end DualTree.LiteralFrontierIndex
