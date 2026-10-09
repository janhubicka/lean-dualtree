import DualTree.FrontierCardinality
import Mathlib.Data.List.NodupEquivFin

/-!
# Coordinates for the literal signature markers in Lemma 27

The paper selects a distinct mixed-product coordinate for each member of
the literal signature marker set R. The previously verified injection
from R to the minimal support frontier can be made into an actual map
to Fin d, where d is the length of the duplicate-free frontier list.

We use the canonical list enumeration, not an arbitrary injection chosen
from a cardinality inequality. Thus the coordinate of a marker is the
position of its unique associated support frontier in the frontier list.

No assignment of mixed-product word values, or proof of smooth-colouring
compatibility, is claimed here. This is only the required collision-free
selection of the D₂ coordinates used by Q.
-/

namespace DualTree.LiteralMarkerCoordinates

/-- The literal marker's chosen minimal frontier as an element of the
duplicate-free list defining the d mixed-product coordinates. -/
noncomputable def frontierMember
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
    {f : Node b // f ∈ LiteralFrontierCount.frontiers T cut} := by
  classical
  let f := LiteralFrontierIndex.frontierFor
    O cut hcut hmax hout T hcomplete hST hcutT hlevel s
  have hf : CutFrontier.Frontier T (fun u => PaperAux u cut) f :=
    (LiteralFrontierIndex.frontierFor_spec
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s).1
  exact ⟨f, (LiteralFrontierCount.mem_frontiers_iff T cut f).2 hf⟩

/-- The marker-to-enumerated-frontier map is injective. -/
theorem frontierMember_injective
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
      (frontierMember O cut hcut hmax hout T hcomplete hST
        hcutT hlevel) := by
  intro s t heq
  have hfront :
      LiteralFrontierIndex.frontierFor
        O cut hcut hmax hout T hcomplete hST hcutT hlevel s =
      LiteralFrontierIndex.frontierFor
        O cut hcut hmax hout T hcomplete hST hcutT hlevel t :=
    congrArg Subtype.val heq
  exact LiteralFrontierIndex.frontierFor_injective
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hfront

/-- The D₂ coordinate of a literal signature marker, indexed by
the paper's actual frontier list of length d. -/
noncomputable def coordinate
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
    Fin (LiteralFrontierCount.frontiers T cut).length := by
  classical
  exact (List.Nodup.getEquiv
      (LiteralFrontierCount.frontiers T cut)
      (LiteralFrontierCount.frontiers_nodup T cut)).symm
    (frontierMember O cut hcut hmax hout T hcomplete hST hcutT hlevel s)

/-- The selected coordinate retrieves exactly the frontier assigned
to the marker, so the enumeration does not alter its geometric meaning. -/
theorem coordinate_frontier
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
    (LiteralFrontierCount.frontiers T cut).get
      (coordinate O cut hcut hmax hout T hcomplete hST hcutT hlevel s) =
    LiteralFrontierIndex.frontierFor
      O cut hcut hmax hout T hcomplete hST hcutT hlevel s := by
  classical
  have h := (List.Nodup.getEquiv
    (LiteralFrontierCount.frontiers T cut)
    (LiteralFrontierCount.frontiers_nodup T cut)).apply_symm_apply
      (frontierMember O cut hcut hmax hout T
        hcomplete hST hcutT hlevel s)
  exact congrArg Subtype.val h

/-- Distinct markers always receive different mixed-product coordinates. -/
theorem coordinate_injective
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
      (coordinate O cut hcut hmax hout T hcomplete hST
        hcutT hlevel) := by
  classical
  intro s t heq
  have hmember :
      frontierMember O cut hcut hmax hout T hcomplete hST hcutT hlevel s =
      frontierMember O cut hcut hmax hout T hcomplete hST hcutT hlevel t :=
    (List.Nodup.getEquiv
      (LiteralFrontierCount.frontiers T cut)
      (LiteralFrontierCount.frontiers_nodup T cut)).symm.injective heq
  exact frontierMember_injective
    O cut hcut hmax hout T hcomplete hST hcutT hlevel hmember

end DualTree.LiteralMarkerCoordinates
