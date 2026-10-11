import DualTree.ForwardQRooted
import DualTree.ImmediateSupportHeight

/-!
# Every intrinsic support rank occurs on a rooted support path

A finite prefix-tree support has an intrinsic rank equal to the
number of its proper support predecessors. Starting from a root
prefixing every support node, follow the first immediate
support successor on the path to a prescribed vertex.

Each move increases the intrinsic rank by exactly one, and
as long as the present rank is below the target rank, the
present support node is a proper prefix of the target.
Consequently every rank up to the target's intrinsic height
is attained by a genuine source vertex on the target path.

No completeness, ambient-length homogeneity or total order
on supports is assumed. Nodup, rootedness and the actual
target's membership suffice.

This will supply the predecessor of a rank-(m+1) exceptional
leaf at rank m in the corrected forward-Q proof.
-/

namespace DualTree.ForwardSourceRankAncestors

/-- Rank-by-rank availability of a support ancestor. The
first-immediate-on-path lemma only needs a finite list and
a proper prefix; no full branching or skew clauses are used. -/
theorem ancestor_at_each_rank {b : Nat}
    (T : List (Node b))
    (hnd : T.Nodup)
    (root : Node b)
    (hroot : root ∈ T)
    (hrootPrefix : ∀ v, v ∈ T → IsPrefix root v)
    (t : Node b) (ht : t ∈ T)
    (j : Nat) (hj : j ≤ SkewTree.heightAt T t) :
    ∃ u : Node b,
      u ∈ T ∧ IsPrefix u t ∧
      SkewTree.heightAt T u = j := by
  have hmain :
      ∀ j : Nat, j ≤ SkewTree.heightAt T t →
        ∃ u : Node b, u ∈ T ∧ IsPrefix u t ∧
          SkewTree.heightAt T u = j := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨root, hroot, hrootPrefix t ht, ?_⟩
        exact ImmediateSupportHeight.heightAt_root_zero T root
          hrootPrefix
    | succ j ih =>
        intro hsucc
        have hj : j ≤ SkewTree.heightAt T t := by omega
        obtain ⟨u, hu, hut, hurank⟩ := ih hj
        have hne : u ≠ t := by
          intro heq
          subst u
          omega
        obtain ⟨v, hv, hstep, _huv, hvt⟩ :=
          SkewBranchGeometry.exists_first_immediate_on_path
            T u t ht ⟨hut, hne⟩
        have hvrank :=
          ImmediateSupportHeight.heightAt_immediate
            T u v hnd hu hstep
        refine ⟨v, hv, hvt, ?_⟩
        omega
  exact hmain j hj

/-- The starred source tree automatically supplies the
root and duplicate-freeness hypotheses of the generic path
rank theorem. -/
theorem source_ancestor_at_rank
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (t : Node b) (ht : t ∈ c.source.tree)
    (j : Nat) (hj : j ≤ SkewTree.heightAt c.source.tree t) :
    ∃ u : Node b,
      u ∈ c.source.tree ∧ IsPrefix u t ∧
      SkewTree.heightAt c.source.tree u = j := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have hskew := hsemi.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hnd : c.source.tree.Nodup := by
    simpa using hskew.1
  exact ancestor_at_each_rank
    c.source.tree hnd
    (ForwardQRooted.sourceRoot c)
    (ForwardQRooted.sourceRoot_mem c)
    (fun v hv => ForwardQRooted.sourceRoot_prefix c v hv)
    t ht j hj

/-- Whenever an actual source vertex lies above the last
interior cut in intrinsic rank, there is a *strict*
source-support ancestor on its ambient path at exactly the
cut rank. -/
theorem source_strict_ancestor_at_cut_rank
    {b n l k m : Nat} {α : Type*}
    (c : ForwardSourceQTree.Frame b n l k m α)
    (t : Node b) (ht : t ∈ c.source.tree)
    (hgreater :
      SkewTree.heightAt c.source.tree c.cut <
        SkewTree.heightAt c.source.tree t) :
    ∃ u : Node b,
      u ∈ c.source.tree ∧ IsStrictPrefix u t ∧
      SkewTree.heightAt c.source.tree u =
        SkewTree.heightAt c.source.tree c.cut := by
  obtain ⟨u, hu, hut, hrank⟩ :=
    source_ancestor_at_rank c t ht
      (SkewTree.heightAt c.source.tree c.cut)
      (Nat.le_of_lt hgreater)
  refine ⟨u, hu, ⟨hut, ?_⟩, hrank⟩
  intro heq
  subst u
  omega

end DualTree.ForwardSourceRankAncestors
