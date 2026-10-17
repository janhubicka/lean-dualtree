import DualTree.ForwardQFinalCrossBandLex
import DualTree.ForwardQFinalTwoFrontierBudget
import DualTree.ForwardQFinalRetainedSkewLength
import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQFinalProjectionOrder
import DualTree.ForwardCompleteEmbedding
import DualTree.ForwardCompleteBijection
import DualTree.PaperAuxAntisymm
import DualTree.SupportReachability
import DualTree.SkewLevelOrder

/-!
# Equal-rank projected length comparisons within one frontier

The corrected complete-T canonical embedding preserves ordinary lex
and its inverse recovers the address of every actual projection
P_i(z). Therefore P_i preserves AND reflects local ordinary lex
within its fixed frontier cone, independently of word-length
distortions caused by stretched ambient T edges.

When two genuinely local roots have equal intrinsic local ranks,
the component's own forward-complete skew clause II orders their
local lengths by local lex. The certified ambient T rank formula
then transfers this to the projected nodes, whose actual ambient
length comparison follows from skew clauses II/III of the ORIGINAL
complete support T. Final T'_M skewness is never assumed here.
-/

namespace DualTree.ForwardQFinalSameFrontierLex

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- Appending identical finite-word prefixes preserves the explicit
ordinary lexicographic order of two local addresses. -/
theorem finLexLE_append_left {b : Nat}
    (a s t : Node b) (hst : FinLexLE s t) :
    FinLexLE (a ++ s) (a ++ t) := by
  induction a with
  | nil => simpa using hst
  | cons x xs ih =>
      simpa [FinLexLE, finLexLEB] using ih

/-- The genuine canonical cone projection preserves ordinary lex
on any two local addresses attached to the SAME frontier. -/
theorem projected_lex_of_local_lex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hlex : FinLexLE z.1 w.1) :
    FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨i,w⟩).1 := by
  let pz := projected c ⟨i,z⟩
  let pw := projected c ⟨i,w⟩
  let az := ForwardCompleteBijection.inverseAddress
    c.T c.hcomplete c.hnon pz
  let aw := ForwardCompleteBijection.inverseAddress
    c.T c.hcomplete c.hnon pw
  have haddress : FinLexLE az.1 aw.1 := by
    change FinLexLE
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
          (ForwardQActualCoordinateWord.projectLocal c i z)).1
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
          (ForwardQActualCoordinateWord.projectLocal c i w)).1
    rw [ForwardQActualCoordinateWord.projectLocal_inverse c i z,
      ForwardQActualCoordinateWord.projectLocal_inverse c i w]
    exact finLexLE_append_left
      (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut i)).1
      z.1 w.1 hlex
  have himage :=
    ForwardCompleteEmbedding.canonicalEmbedding_lex_mono
      c.T c.hcomplete c.hnon az aw haddress
  change FinLexLE
    (ForwardCompleteEmbedding.canonicalEmbedding c.T c.hcomplete c.hnon az).1
    (ForwardCompleteEmbedding.canonicalEmbedding c.T c.hcomplete c.hnon aw).1 at himage
  change FinLexLE (projected c ⟨i,z⟩).1
    (projected c ⟨i,w⟩).1
  simpa only [az, aw, ForwardCompleteBijection.inverse_right] using himage

/-- Lex reflection on ONE genuine projected frontier. Ordinary
lex is total and antisymmetric, and the complete-T projection is
injective on local addresses. -/
theorem projected_lex_iff_local_lex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1))) :
    FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨i,w⟩).1 ↔ FinLexLE z.1 w.1 := by
  constructor
  · intro hp
    rcases finLexLE_total z.1 w.1 with hzw | hwz
    · exact hzw
    · have hpback :=
        projected_lex_of_local_lex c i w z hwz
      have heqImage :
          (projected c ⟨i,z⟩).1 =
          (projected c ⟨i,w⟩).1 :=
        PaperAuxAntisymm.finLexLE_antisymm
          _ _ hp hpback
      have heq : z = w :=
        ForwardQFinalRefinementRoots.projectLocal_injective c i
          (Subtype.ext heqImage)
      subst w
      rcases finLexLE_total z.1 z.1 with hh | hh
      · exact hh
      · exact hh
  · exact projected_lex_of_local_lex c i z w

/-- Within the genuine ambient complete T, nondecreasing
intrinsic T rank and ordinary lex imply nondecreasing actual
ambient word length, by the ORIGINAL skew clauses II/III. -/
theorem ambient_length_le_of_rank_le_and_lex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : {t : Node b // t ∈ c.T})
    (hrank : SkewTree.heightAt c.T u.1 ≤
      SkewTree.heightAt c.T v.1)
    (hlex : FinLexLE u.1 v.1) :
    u.1.length ≤ v.1.length := by
  by_cases hlt : SkewTree.heightAt c.T u.1 <
      SkewTree.heightAt c.T v.1
  · exact Nat.le_of_lt
      (SkewLevelOrder.length_lt_of_height_lt c.T
        SkewTree.forwardAuxB
        (ForwardQFinalRetainedSkewLength.ambient_forward_skew c)
        c.hnon u.2 v.2 hlt)
  · have heq : SkewTree.heightAt c.T u.1 =
        SkewTree.heightAt c.T v.1 := by omega
    have hrow :=
      (List.all_eq_true.mp
        (ForwardQFinalRetainedSkewLength.ambient_condIIB c))
        u.1 u.2
    have hcell := (List.all_eq_true.mp hrow) v.1 v.2
    simpa [heq, hlex] using hcell

/-- SAME-frontier local support roots with equal local intrinsic
rank, in ordinary projected lex order, have the required
nondecreasing ACTUAL ambient projected word lengths. -/
theorem projected_same_frontier_equal_local_rank_length_le
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i : Index c)
    (z w : BoundedNode b (k-(m+1)))
    (hz : z ∈ (f.vector.components i).support)
    (hw : w ∈ (f.vector.components i).support)
    (hrank :
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes z.1 =
      SkewTree.heightAt
        (f.vector.components i).toVariableWord.supportNodes w.1)
    (hlex : FinLexLE (projected c ⟨i,z⟩).1
      (projected c ⟨i,w⟩).1) :
    (projected c ⟨i,z⟩).1.length ≤
      (projected c ⟨i,w⟩).1.length := by
  let L := (f.vector.components i).toVariableWord.supportNodes
  have hzNode : z.1 ∈ L := by
    change z.1 ∈ (f.vector.components i).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  have hwNode : w.1 ∈ L := by
    change w.1 ∈ (f.vector.components i).support.map (fun t => t.1)
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  have hlocalLex : FinLexLE z.1 w.1 :=
    (projected_lex_iff_local_lex c i z w).1 hlex
  have hlocalLength : z.1.length ≤ w.1.length := by
    by_cases hsame : z.1 = w.1
    · rw [hsame]
    · have hnon : L.length ≠ 1 :=
        SupportReachability.nonsingleton_of_distinct_members
          L hzNode hwNode hsame
      have hcomp :=
        ForwardQFinalTwoFrontierBudget.local_component_complete c f i
      simp only [SkewTree.completeB, Bool.and_eq_true] at hcomp
      have hparts := hcomp.1
      simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
      have hII : SkewTree.condIIB L = true := by
        have hcore := hparts.2
        simp [Bool.and_eq_true] at hcore
        rcases hcore with hone | hrest
        · exact (hnon hone).elim
        · exact hrest.1.1.2
      have hrow := (List.all_eq_true.mp hII) z.1 hzNode
      have hcell := (List.all_eq_true.mp hrow) w.1 hwNode
      have htrigger :
          SkewTree.heightAt L z.1 = SkewTree.heightAt L w.1 ∧
            FinLexLE z.1 w.1 := ⟨hrank, hlocalLex⟩
      change
        (if SkewTree.heightAt L z.1 = SkewTree.heightAt L w.1 ∧
            FinLexLE z.1 w.1
         then decide (z.1.length ≤ w.1.length)
         else true) = true at hcell
      simpa [htrigger] using hcell
  have hTrank :
      SkewTree.heightAt c.T (projected c ⟨i,z⟩).1 ≤
      SkewTree.heightAt c.T (projected c ⟨i,w⟩).1 := by
    rw [ForwardQFinalProjectionOrder.projected_height c ⟨i,z⟩,
      ForwardQFinalProjectionOrder.projected_height c ⟨i,w⟩]
    change
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        z.1.length ≤
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 +
        w.1.length
    omega
  exact ambient_length_le_of_rank_le_and_lex
    c (projected c ⟨i,z⟩) (projected c ⟨i,w⟩) hTrank hlex

end DualTree.ForwardQFinalSameFrontierLex
