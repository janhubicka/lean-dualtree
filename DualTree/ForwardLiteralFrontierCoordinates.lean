import DualTree.ForwardSignatureInteriorPersistence
import DualTree.ForwardMarkerAntichain
import Mathlib.Data.List.NodupEquivFin

/-!
# Collision-free literal R coordinates for the repaired forward Q map

For the globally corrected forward auxiliary convention, every
point of the literal signature marker set R is an inclusive-cut
first-exit boundary with a unique minimal support frontier. The
forward-boundary antichain theorem shows two different markers
cannot share the same frontier.

This file instantiates the abstract geometry with the actual
corrected Definition 26 signature and Lemma 27's two types of
markers. It constructs:
* the uniquely selected frontier for every literal R marker;
* an injective map R -> support frontiers;
* a duplicate-free list of all support frontiers;
* an actual injective Fin d coordinate for every literal marker,
  including the inverse enumeration equation.

IMPORTANT: The list of frontiers below is obtained by filtering an
arbitrary list representation of T. It is not yet normalized into the
paper's prescribed forward-auxiliary increasing order. Coordinate
injectivity does NOT suffice to certify Definition 20's vector
1-completeness of marked points. Sorting the frontier enumeration and
proving its order-preservation is the next source-facing requirement.

No printed-order support assumption occurs in this module.
-/

namespace DualTree.ForwardLiteralFrontierCoordinates

open ForwardSignatureBoundary

/-- Exact corrected literal signature marker list. -/
noncomputable abbrev R
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) : List (Node b) :=
  ForwardStarredSignature.literalR O cut hout

/-- Every corrected literal R marker receives its unique
minimal complete-support frontier beyond the forward cut. -/
noncomputable def frontierFor
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ R O cut hout}) : Node b :=
  Classical.choose
    (ForwardSignatureInteriorPersistence.literalR_unique_frontier
      O cut hcut hmax hout T hcomplete hnon
      hST hcutT hearly s.1 s.2)

/-- The selected frontier is a genuine minimal support frontier
and extends its designated literal R marker. -/
theorem frontierFor_spec
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ R O cut hout}) :
    CutFrontier.Frontier T (fun u => ForwardAux u cut)
      (frontierFor O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly s) ∧
    IsPrefix s.1
      (frontierFor O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly s) :=
  (Classical.choose_spec
    (ForwardSignatureInteriorPersistence.literalR_unique_frontier
      O cut hcut hmax hout T hcomplete hnon
      hST hcutT hearly s.1 s.2)).1

/-- Distinct literal markers have distinct chosen support frontiers.
This is stronger than unique-frontier existence separately for each. -/
theorem frontierFor_injective
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Function.Injective
      (frontierFor O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly) := by
  exact ForwardMarkerAntichain.boundary_list_frontier_injective
    (R O cut hout) cut
    (fun s hs =>
      ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
        O cut hcut hmax hout s hs)
    (frontierFor O cut hcut hmax hout T hcomplete hnon hST hcutT hearly)
    (fun s =>
      (frontierFor_spec O cut hcut hmax hout
        T hcomplete hnon hST hcutT hearly s).2)

/-- Duplicate-free enumeration of all minimal support nodes outside
the corrected inclusive forward cut. This enumeration is not
yet sorted by forward auxiliary order. -/
noncomputable def frontiers {b : Nat}
    (T : List (Node b)) (cut : Node b) : List (Node b) := by
  classical
  exact (T.filter (fun t =>
    decide (CutFrontier.Frontier T
      (fun u => ForwardAux u cut) t))).dedup

theorem frontiers_nodup {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    (frontiers T cut).Nodup := by
  classical
  unfold frontiers
  exact List.nodup_dedup _

theorem mem_frontiers_iff {b : Nat}
    (T : List (Node b)) (cut t : Node b) :
    t ∈ frontiers T cut ↔
      CutFrontier.Frontier T (fun u => ForwardAux u cut) t := by
  classical
  simp only [frontiers, List.mem_dedup, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

/-- A chosen literal-marker frontier, viewed in the genuine
enumerated frontier subtype. -/
noncomputable def frontierMember
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ R O cut hout}) :
    {f : Node b // f ∈ frontiers T cut} := by
  let f :=
    frontierFor O cut hcut hmax hout T hcomplete hnon
      hST hcutT hearly s
  exact ⟨f, (mem_frontiers_iff T cut f).2
    (frontierFor_spec O cut hcut hmax hout
      T hcomplete hnon hST hcutT hearly s).1⟩

theorem frontierMember_injective
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Function.Injective
      (frontierMember O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly) := by
  intro s t heq
  apply frontierFor_injective O cut hcut hmax hout
    T hcomplete hnon hST hcutT hearly
  exact congrArg Subtype.val heq

/-- The actual corrected finite coordinate assigned to each member
of the literal R, in the chosen frontier-list enumeration. -/
noncomputable def coordinate
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ R O cut hout}) :
    Fin (frontiers T cut).length := by
  classical
  exact (List.Nodup.getEquiv
    (frontiers T cut) (frontiers_nodup T cut)).symm
      (frontierMember O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly s)

/-- The literal marker coordinates are collision-free: no two
different markers can share one Fin d coordinate. -/
theorem coordinate_injective
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Function.Injective
      (coordinate O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly) := by
  intro s t heq
  apply frontierMember_injective O cut hcut hmax hout
    T hcomplete hnon hST hcutT hearly
  exact (List.Nodup.getEquiv
    (frontiers T cut) (frontiers_nodup T cut)).symm.injective heq

/-- The enumerated frontier at the selected D₂ coordinate is
exactly the unique support frontier of the literal marker. -/
theorem coordinate_frontier
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
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b // s ∈ R O cut hout}) :
    (frontiers T cut).get
      (coordinate O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly s) =
    frontierFor O cut hcut hmax hout T hcomplete hnon
      hST hcutT hearly s := by
  classical
  have h := (List.Nodup.getEquiv
    (frontiers T cut) (frontiers_nodup T cut)).apply_symm_apply
      (frontierMember O cut hcut hmax hout T hcomplete hnon
        hST hcutT hearly s)
  exact congrArg Subtype.val h

end DualTree.ForwardLiteralFrontierCoordinates
