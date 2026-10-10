import DualTree.ForwardLiteralFrontierCoordinates
import DualTree.ForwardAuxTransitivity
import Mathlib.Data.List.Sort

/-!
# The actual corrected forward-sorted frontier enumeration

The source's Lemma 27 enumerates the minimal support frontiers in
*increasing auxiliary order*. This is essential: Definition 20's
vector 1-complete marked coordinates require ambient lengths
nondecreasing in the actual D₂ coordinate order.

The earlier forward repair had built an injection R → Fin d by
filtering the input support list; although collision-free, that
enumeration was not guaranteed to be in forward auxiliary order.

We now sort it explicitly using the verified length-first
forward-lex order. The resulting sorted list:
* consists of exactly the minimal outside-cut support frontiers;
* has no duplicate nodes and unchanged cardinality;
* is pairwise monotone in forward auxiliary order;
* admits a new, injective R → Fin d coordinate map whose
  index retrieval gives the correct chosen frontier;
* has the source-facing order property that earlier marked
  coordinate indices correspond to forward-ordered frontiers.

These facts do not yet prove that the reconstructed Q tree is
semi-complete, but remove a real missing hypothesis in transporting
the W_* vector 1-completeness condition to its projected leaves.
-/

namespace DualTree.ForwardSortedFrontiers

/-- The comparison used to sort actual forward cut frontiers. -/
def comparator {b : Nat} (s t : Node b) : Bool :=
  decide (ForwardAux s t)

/-- The printed source requires increasing auxiliary order;
do not inherit the arbitrary enumeration of the input support. -/
noncomputable def frontiers {b : Nat}
    (T : List (Node b)) (cut : Node b) : List (Node b) :=
  (ForwardLiteralFrontierCoordinates.frontiers T cut).mergeSort comparator

/-- The sorted list is a permutation of the original, possibly
arbitrarily ordered support-filtered frontier list. -/
theorem frontiers_perm {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    List.Perm (frontiers T cut)
      (ForwardLiteralFrontierCoordinates.frontiers T cut) := by
  unfold frontiers
  exact List.mergeSort_perm _ comparator

/-- Sorting retains precisely the minimal T-frontiers after
the inclusive forward auxiliary cut. -/
theorem mem_frontiers_iff {b : Nat}
    (T : List (Node b)) (cut f : Node b) :
    f ∈ frontiers T cut ↔
      CutFrontier.Frontier T (fun u => ForwardAux u cut) f := by
  rw [(frontiers_perm T cut).mem_iff]
  exact ForwardLiteralFrontierCoordinates.mem_frontiers_iff T cut f

/-- The sorted finite frontier sequence is duplicate-free. -/
theorem frontiers_nodup {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    (frontiers T cut).Nodup := by
  exact (frontiers_perm T cut).nodup_iff.mpr
    (ForwardLiteralFrontierCoordinates.frontiers_nodup T cut)

/-- Sorting does not change the number d of frontier coordinates. -/
theorem frontiers_length {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    (frontiers T cut).length =
      (ForwardLiteralFrontierCoordinates.frontiers T cut).length :=
  (frontiers_perm T cut).length_eq

/-- The sorting comparator is transitive. -/
theorem comparator_trans {b : Nat} :
    ∀ a c d : Node b,
      comparator a c = true →
      comparator c d = true →
      comparator a d = true := by
  intro a c d hac hcd
  have hc : ForwardAux a c := by simpa [comparator] using hac
  have hd : ForwardAux c d := by simpa [comparator] using hcd
  simpa [comparator] using
    (ForwardAuxTransitivity.forwardAux_trans hc hd)

/-- The sorting comparator is total. -/
theorem comparator_total {b : Nat} :
    ∀ a c : Node b,
      (comparator a c || comparator c a) = true := by
  intro a c
  rcases CanonicalForwardAuxIso.forwardAux_total a c with h | h
  · simp [comparator, h]
  · simp [comparator, h]

/-- Every earlier frontier in the sorted list precedes every
later frontier in the forward length-first auxiliary order. -/
theorem frontiers_pairwise {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    (frontiers T cut).Pairwise ForwardAux := by
  have h := List.pairwise_mergeSort
    (le := comparator (b := b))
    (comparator_trans (b := b))
    (comparator_total (b := b))
    (ForwardLiteralFrontierCoordinates.frontiers T cut)
  simpa only [frontiers, comparator, decide_eq_true_eq] using h

/-- The sorted frontiers give an honest coordinate index:
earlier indices correspond to ordered distinct frontiers. -/
theorem frontiers_get_order {b : Nat}
    (T : List (Node b)) (cut : Node b)
    (i j : Fin (frontiers T cut).length) (hij : i < j) :
    ForwardAux
      ((frontiers T cut).get i)
      ((frontiers T cut).get j) := by
  exact (List.pairwise_iff_get.mp
    (frontiers_pairwise T cut)) i j hij

/-- A selected literal R marker frontier in the sorted
list, rather than the arbitrary original support-list order. -/
noncomputable def frontierMember
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b //
      s ∈ ForwardLiteralFrontierCoordinates.R O cut hout}) :
    {f : Node b // f ∈ frontiers T cut} := by
  let f := ForwardLiteralFrontierCoordinates.frontierFor
    O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s
  exact ⟨f, (mem_frontiers_iff T cut f).2
    (ForwardLiteralFrontierCoordinates.frontierFor_spec
      O cut hcut hmax hout T hcomplete hnon
      hST hcutT hearly s).1⟩

/-- The sorted list also supports a genuine collision-free
coordinate of every corrected literal R marker. -/
noncomputable def coordinate
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b //
      s ∈ ForwardLiteralFrontierCoordinates.R O cut hout}) :
    Fin (frontiers T cut).length := by
  classical
  exact (List.Nodup.getEquiv
    (frontiers T cut) (frontiers_nodup T cut)).symm
    (frontierMember O cut hcut hmax hout
      T hcomplete hnon hST hcutT hearly s)

/-- Sorted literal marker coordinates remain injective. -/
theorem coordinate_injective
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k) :
    Function.Injective
      (coordinate O cut hcut hmax hout
        T hcomplete hnon hST hcutT hearly) := by
  intro s t heq
  have hfront : frontierMember O cut hcut hmax hout
      T hcomplete hnon hST hcutT hearly s =
    frontierMember O cut hcut hmax hout
      T hcomplete hnon hST hcutT hearly t :=
    (List.Nodup.getEquiv
      (frontiers T cut) (frontiers_nodup T cut)).symm.injective heq
  exact ForwardLiteralFrontierCoordinates.frontierFor_injective
    O cut hcut hmax hout T hcomplete hnon hST hcutT hearly
    (congrArg Subtype.val hfront)

/-- Inverse lookup of a sorted D₂ coordinate returns the
selected actual minimal T frontier of its literal marker. -/
theorem coordinate_frontier
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s : {s : Node b //
      s ∈ ForwardLiteralFrontierCoordinates.R O cut hout}) :
    (frontiers T cut).get
      (coordinate O cut hcut hmax hout
        T hcomplete hnon hST hcutT hearly s) =
      ForwardLiteralFrontierCoordinates.frontierFor
        O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s := by
  classical
  have h := (List.Nodup.getEquiv
    (frontiers T cut) (frontiers_nodup T cut)).apply_symm_apply
      (frontierMember O cut hcut hmax hout
        T hcomplete hnon hST hcutT hearly s)
  exact congrArg Subtype.val h

/-- For two corrected literal marker coordinates, the
sorted index comparison directly yields the required forward
auxiliary comparison of the actual projected frontier roots. -/
theorem coordinate_frontier_order
    {b n l k : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.forwardAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ ForwardSignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hearly : SkewTree.heightAt T cut + 1 < k)
    (s t : {s : Node b //
      s ∈ ForwardLiteralFrontierCoordinates.R O cut hout})
    (hst :
      coordinate O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s <
      coordinate O cut hcut hmax hout T hcomplete hnon hST hcutT hearly t) :
    ForwardAux
      (ForwardLiteralFrontierCoordinates.frontierFor
        O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s)
      (ForwardLiteralFrontierCoordinates.frontierFor
        O cut hcut hmax hout T hcomplete hnon hST hcutT hearly t) := by
  have h :=
    frontiers_get_order T cut
      (coordinate O cut hcut hmax hout T hcomplete hnon hST hcutT hearly s)
      (coordinate O cut hcut hmax hout T hcomplete hnon hST hcutT hearly t)
      hst
  rw [coordinate_frontier, coordinate_frontier] at h
  exact h

end DualTree.ForwardSortedFrontiers
