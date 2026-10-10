import DualTree.ForwardUniformConeDomains
import DualTree.ForwardSortedFrontiers
import DualTree.ForwardProjectedTerminalOrder

/-!
# Ordered projections from sorted frontiers of a forward-complete support

This is the marked-to-marked numerical part of the corrected Q tree.

Let T be a genuine k-complete forward-auxiliary skew support,
let cut have intrinsic T-height m, and list all minimal support
frontiers beyond the inclusive cut in increasing *forward* auxiliary
order. At each frontier index i, choose a local tail
  z_i : b^{< (k - (m+1))}
in the uniformly safe common tail domain.

The vector-1-complete condition of Definition 20 gives

  i < j  ->  |z_i| <= |z_j|.

A sorted frontier list gives f_i <=_forward f_j; the verified
uniform canonical cone map projects every z_i to an actual T-node
u_i in the cone above f_i, with rank
  h_T(u_i) = h_T(f_i) + |z_i|.

The previously checked forward frontier-order theorem therefore
implies both
  ForwardAux u_i u_j
and
  |u_i| <= |u_j|
for i<j. This is exactly the *ambient-length* comparison
needed between reconstructed leaves of equal Q-intrinsic height.

These results concern projections in the ambient complete support.
The remaining geometric step is to determine the exact intrinsic
rank of the projected points *inside the new Q support*, and
compare them with its preserved old interior nodes. No
colouring or word construction is claimed.
-/

namespace DualTree.ForwardOrderedProjections

/-- The true sorted frontier root at a finite D₂ index, viewed as
a member of the enclosing forward-complete support T. -/
noncomputable def frontierAt {b : Nat}
    (T : List (Node b)) (cut : Node b)
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    {f : Node b // f ∈ T} := by
  let f := (ForwardSortedFrontiers.frontiers T cut).get i
  have hf : CutFrontier.Frontier T (fun u => ForwardAux u cut) f :=
    (ForwardSortedFrontiers.mem_frontiers_iff T cut f).1
      (List.get_mem (ForwardSortedFrontiers.frontiers T cut) i)
  exact ⟨f, hf.1⟩

theorem frontierAt_spec {b : Nat}
    (T : List (Node b)) (cut : Node b)
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    CutFrontier.Frontier T (fun u => ForwardAux u cut)
      (frontierAt T cut i).1 := by
  exact (ForwardSortedFrontiers.mem_frontiers_iff T cut _).1
    (List.get_mem (ForwardSortedFrontiers.frontiers T cut) i)

/-- Distinct sorted frontier coordinates have distinct
ambient frontier roots. -/
theorem frontierAt_injective {b : Nat}
    (T : List (Node b)) (cut : Node b) :
    Function.Injective (frontierAt T cut) := by
  intro i j hij
  let F := ForwardSortedFrontiers.frontiers T cut
  have hget : F.get i = F.get j := by
    simpa [F, frontierAt] using congrArg Subtype.val hij
  let e := List.Nodup.getEquiv F
    (ForwardSortedFrontiers.frontiers_nodup T cut)
  have heq : e i = e j := Subtype.ext hget
  exact e.injective heq

/-- Every chosen common tail has a genuine support-valued
projection rooted at the corresponding sorted frontier. -/
noncomputable def projectAt {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1)))
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    {u : Node b // u ∈ T} :=
  ForwardUniformConeDomains.projectCommon T hcomplete hnon
    cut hcut hm (frontierAt T cut i) (frontierAt_spec T cut i)
    (point i)

/-- Each projected node extends its selected minimal frontier. -/
theorem projectAt_cone {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1)))
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    IsPrefix (frontierAt T cut i).1
      (projectAt T hcomplete hnon cut hcut hm point i).1 := by
  exact ForwardUniformConeDomains.projectCommon_cone
    T hcomplete hnon cut hcut hm
    (frontierAt T cut i) (frontierAt_spec T cut i)
    (point i)

/-- Every projected point advances the intrinsic ambient
complete-T rank by exactly the length of its local tail. -/
theorem projectAt_height {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1)))
    (i : Fin (ForwardSortedFrontiers.frontiers T cut).length) :
    SkewTree.heightAt T
      (projectAt T hcomplete hnon cut hcut hm point i).1 =
      SkewTree.heightAt T (frontierAt T cut i).1 +
        (point i).1.length := by
  exact ForwardUniformConeDomains.projectCommon_height
    T hcomplete hnon cut hcut hm
    (frontierAt T cut i) (frontierAt_spec T cut i) (point i)

/-- If marked tail lengths are nondecreasing at sorted
indices i<j, their actual canonical T-projections are also
ordered by the repaired forward auxiliary order. -/
theorem projectAt_forward_order {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1)))
    (i j : Fin (ForwardSortedFrontiers.frontiers T cut).length)
    (hij : i < j)
    (hpoints : (point i).1.length ≤ (point j).1.length) :
    ForwardAux
      (projectAt T hcomplete hnon cut hcut hm point i).1
      (projectAt T hcomplete hnon cut hcut hm point j).1 := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  let f := frontierAt T cut i
  let g := frontierAt T cut j
  let u := projectAt T hcomplete hnon cut hcut hm point i
  let v := projectAt T hcomplete hnon cut hcut hm point j
  have hne : f.1 ≠ g.1 := by
    intro heq
    have hindex : i = j :=
      frontierAt_injective T cut (Subtype.ext heq)
    exact (ne_of_lt hij) hindex
  have hforward : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order T cut i j hij
  exact ForwardProjectedTerminalOrder.ordered_frontier_projections_forwardAux
    T hc.1 hnon cut f.1 g.1 u.1 v.1
    (frontierAt_spec T cut i) (frontierAt_spec T cut j)
    hne hforward u.2 v.2
    (projectAt_cone T hcomplete hnon cut hcut hm point i)
    (projectAt_cone T hcomplete hnon cut hcut hm point j)
    (point i).1.length (point j).1.length
    (projectAt_height T hcomplete hnon cut hcut hm point i)
    (projectAt_height T hcomplete hnon cut hcut hm point j)
    hpoints

/-- The central numerical consequence for skew clause (ii):
ordered local singleton point depths give *nondecreasing
ambient lengths* of the corresponding reconstructed leaves. -/
theorem projectAt_length_le {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1)))
    (i j : Fin (ForwardSortedFrontiers.frontiers T cut).length)
    (hij : i < j)
    (hpoints : (point i).1.length ≤ (point j).1.length) :
    (projectAt T hcomplete hnon cut hcut hm point i).1.length ≤
      (projectAt T hcomplete hnon cut hcut hm point j).1.length := by
  rcases projectAt_forward_order
    T hcomplete hnon cut hcut hm point i j hij hpoints with hlt | ⟨heq, _⟩
  · omega
  · omega

/-- Distinct D₂ sorted frontier projections are injective:
their roots lie in distinct minimal support cones. -/
theorem projectAt_injective {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (cut : Node b) (hcut : cut ∈ T)
    (hm : SkewTree.heightAt T cut = m)
    (point : Fin (ForwardSortedFrontiers.frontiers T cut).length →
      BoundedNode b (k - (m + 1))) :
    Function.Injective (projectAt T hcomplete hnon cut hcut hm point) := by
  intro i j heq
  have hi := frontierAt_spec T cut i
  have hj := frontierAt_spec T cut j
  have hfi := projectAt_cone T hcomplete hnon cut hcut hm point i
  have hfj := projectAt_cone T hcomplete hnon cut hcut hm point j
  have hfj' : IsPrefix (frontierAt T cut j).1
      (projectAt T hcomplete hnon cut hcut hm point i).1 := by
    rw [heq]
    exact hfj
  have hfront :
      (frontierAt T cut i).1 = (frontierAt T cut j).1 :=
    CutFrontier.frontier_unique_above
      T (fun t => ForwardAux t cut) hi hj hfi hfj'
  exact frontierAt_injective T cut (Subtype.ext hfront)

end DualTree.ForwardOrderedProjections
