import DualTree.ForwardQFinalSkewIV
import DualTree.ForwardQFinalSkewII
import DualTree.ForwardQFinalSkewIII
import DualTree.ForwardQFinalMeetClosure
import DualTree.ForwardQFinalLeafBranchClause
import DualTree.ForwardQFinalRankBound
import DualTree.SupportHeightRanks

/-!
# Actual final (m+q)-complete skew support in corrected Lemma 27

The exact rank-budgeted final support S is built from retained
initial T vertices and genuinely selected P_i(z) roots. All four
ingredients of the executable skew class are independently proved:
rootedness, length clauses II and III, and the last branching
witness IV. The witness proof requires M=m+q>1.

The M=1 case is a singleton: the ambient complete root belongs to S
and prefixes every support node. If some distinct vertex survived,
it would have strictly positive intrinsic S height, contradicting
the exact S rank bound height<M=1. The paper's explicit singleton
skew convention therefore closes this boundary without inventing
a branching witness.

For b>0 and q>0 the independent exact leaf-or-b-successor
theorem then upgrades skewB to completeB with parameter m+q.

This is an exact theorem for the corrected forward-order Frame,
not for the paper's printed reverse-starred W_* domain.
It constructs the needed final SUPPORT, not the final ambient
variable word f', its span inclusion, or the Ramsey iteration.
-/

namespace DualTree.ForwardQFinalCompleteSkew

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget

/-- The exact rank-filtered final support is genuinely skew for
the repaired forward auxiliary order, including the M=1
singleton boundary. Only positive b and q are assumed. -/
theorem finalBudgetSupport_skewB
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hb : 0 < b) (hq : 0 < q) :
    SkewTree.skewB SkewTree.forwardAuxB
      (finalBudgetSupport c f (m+q)).toList = true := by
  classical
  let S := (finalBudgetSupport c f (m+q)).toList
  by_cases hOne : m+q = 1
  · let r := ForwardCompleteEmbedding.rootOf c.T c.hcomplete c.hnon
    have hrS : r ∈ S :=
      ForwardQFinalMeetClosure.ambient_root_mem_final c f
    have hset : finalBudgetSupport c f (m+q) = {r} := by
      ext t
      constructor
      · intro ht
        have htS : t ∈ S := Finset.mem_toList.mpr ht
        have hrpre : IsPrefix r t :=
          ForwardQFinalMeetClosure.ambient_root_prefix_final
            c f t htS
        have hbound : SkewTree.heightAt S t < m+q :=
          ForwardQFinalRankBound.finalBudgetSupport_all_heights_lt_target
            c f (m+q) (by omega) t ht
        by_cases hsame : t = r
        · exact Finset.mem_singleton.mpr hsame
        · have hstrict : IsStrictPrefix r t :=
            ⟨hrpre, Ne.symm hsame⟩
          have hlt : SkewTree.heightAt S r <
              SkewTree.heightAt S t :=
            SupportHeightRanks.heightAt_lt_of_strictPrefix
              S hrS hstrict
          rw [hOne] at hbound
          omega
      · intro ht
        have hsame : t = r := Finset.mem_singleton.mp ht
        subst t
        exact Finset.mem_toList.mp hrS
    have hlist : S = [r] := by
      change (finalBudgetSupport c f (m+q)).toList = [r]
      rw [hset]
      simp
    change SkewTree.skewB SkewTree.forwardAuxB S = true
    rw [hlist]
    exact SkewTree.singleton_skewB SkewTree.forwardAuxB r
  · have hM : 1 < m+q := by omega
    have hnodup : S.Nodup :=
      Finset.nodup_toList (finalBudgetSupport c f (m+q))
    have hrooted : SkewTree.rootedB S = true :=
      ForwardQFinalMeetClosure.final_rootedB c f
    have hII : SkewTree.condIIB S = true :=
      ForwardQFinalSkewII.finalBudgetSupport_condIIB c f
    have hIII : SkewTree.condIIIB S = true :=
      ForwardQFinalSkewIII.finalBudgetSupport_condIIIB c f
    have hIV : SkewTree.condIVB SkewTree.forwardAuxB S = true :=
      ForwardQFinalSkewIV.finalBudgetSupport_condIVB c f hb hq hM
    change SkewTree.skewB SkewTree.forwardAuxB S = true
    simp [SkewTree.skewB, hnodup, hrooted, hII, hIII, hIV]

/-- Full (m+q)-COMPLETENESS of the genuine corrected
rank-filtered final support: exact support skewness together
with the already verified complete branching/leaf condition. -/
theorem finalBudgetSupport_completeB
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (hb : 0 < b) (hq : 0 < q) :
    SkewTree.completeB SkewTree.forwardAuxB (m+q)
      (finalBudgetSupport c f (m+q)).toList = true :=
  (ForwardQFinalLeafBranchClause.final_complete_iff_skew
    c f hb hq).2 (finalBudgetSupport_skewB c f hb hq)

end DualTree.ForwardQFinalCompleteSkew
