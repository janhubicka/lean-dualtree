import DualTree.FrontierHeightBound
import DualTree.Lemma27Audit

/-!
# Safe domains for the cone projections of Lemma 27

The printed common cone-tail height n-m' may run beyond b^{<n}
for a frontier at intrinsic height m'+1. The rank bound now proves
that a common tail height n-(m'+1) is safe for every frontier.

This file states the correction at the level of the canonical
source address I_T^{-1}(t_i), represented by a node whose ambient
length is the intrinsic height of the frontier. It does not claim
that the canonical map I_T or the corresponding P_i has already
been constructed in Lean; that is a separate geometric step.

The shortened common tail changes the numerical parameters of
the mixed-product invocation, so it is not by itself a complete
repair of the displayed bound for h3.
-/

namespace DualTree.ConeTailDomains

/-- A tail bounded by the remaining length of its base stays in the ambient tree. -/
theorem variable_cone_tail_safe {b N : Nat}
    (base tail : Node b)
    (hbase : base.length ≤ N)
    (htail : tail.length < N - base.length) :
    InHomTree N (base ++ tail) := by
  unfold InHomTree
  simp only [List.length_append]
  omega

/--
For any frontier beyond an early complete-skew cut, the uniformly
shortened tail fits after its canonical address.
-/
theorem common_cone_tail_safe
    {b k N m : Nat}
    (T : List (Node b))
    (cut frontier : Node b)
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hf : CutFrontier.Frontier T (fun u => PaperAux u cut) frontier)
    (hm : SkewTree.heightAt T cut = m)
    (hambient : m + 1 ≤ N)
    (base tail : Node b)
    (hbase : base.length = SkewTree.heightAt T frontier)
    (htail : tail.length < N - (m + 1)) :
    InHomTree N (base ++ tail) := by
  have hfront : SkewTree.heightAt T frontier ≤ m + 1 :=
    FrontierHeightBound.frontier_height_le_m_succ
      T cut frontier hcomplete hcut hlevel hf hm
  exact Lemma27Audit.safe_cone_tail base tail
    (by omega) hambient htail

/--
A source address at the actual frontier height can instead use its
own remaining tail height. This is safe without a uniform shortening,
but does not directly supply one common mixed-product ambient height.
-/
theorem variable_frontier_tail_safe
    {b k N : Nat}
    (T : List (Node b))
    (frontier : Node b)
    (base tail : Node b)
    (hbase : base.length = SkewTree.heightAt T frontier)
    (hbudget : SkewTree.heightAt T frontier ≤ N)
    (htail : tail.length < N - SkewTree.heightAt T frontier) :
    InHomTree N (base ++ tail) := by
  exact variable_cone_tail_safe base tail (by omega) (by omega)

end DualTree.ConeTailDomains
