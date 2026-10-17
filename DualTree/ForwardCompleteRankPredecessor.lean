import DualTree.ForwardCompleteBijection
import DualTree.SupportReachability

/-!
# Intermediate support ranks from the genuine forward-complete embedding

Every predecessor level below a positive-rank point of a finite
forward-complete support is realized by an actual ancestor. The
result does not require branching-degree positivity or an
infinite-tree argument; we truncate the point's canonical
inverse address and map it back through the already certified
finite support embedding.

This lemma is useful for the vector-skew successor-level
separation argument. In particular it avoids assuming that
all local supports have strictly positive branching.
-/

namespace DualTree.ForwardCompleteRankPredecessor

/-- A support vertex of positive intrinsic rank witnesses that
its containing support cannot be a singleton. -/
theorem nonsingleton_of_positive_rank
    {b : Nat} (T : List (Node b))
    (w : Node b) (hw : w ∈ T)
    (hpositive : 0 < SkewTree.heightAt T w) :
    T.length ≠ 1 := by
  have hpredNonempty : 0 < (SkewTree.preds T w).length := by
    simpa only [SkewTree.heightAt] using hpositive
  cases hpred : SkewTree.preds T w with
  | nil =>
      simp [hpred] at hpredNonempty
  | cons u us =>
      have huPred : u ∈ SkewTree.preds T w := by
        simp [hpred]
      obtain ⟨huT, huStrict⟩ :=
        (ImmediateSupportHeight.mem_preds_iff T w u).1 huPred
      exact SupportReachability.nonsingleton_of_distinct_members
        T huT hw huStrict.2

/-- An actual node w in a q-complete corrected forward skew
support has a strict T predecessor at EVERY intrinsic rank r
smaller than height_T(w). The ancestor is obtained by truncating
the certified inverse tree address of w to r digits. -/
theorem exists_strict_predecessor_at_rank
    {b q : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB q T = true)
    (w : Node b) (hw : w ∈ T)
    (r : Nat) (hr : r < SkewTree.heightAt T w) :
    ∃ u : Node b,
      u ∈ T ∧
      SkewTree.heightAt T u = r ∧
      IsStrictPrefix u w := by
  have hnon : T.length ≠ 1 :=
    nonsingleton_of_positive_rank T w hw (by omega)
  let wt : {t : Node b // t ∈ T} := ⟨w, hw⟩
  let a : BoundedNode b q :=
    ForwardCompleteBijection.inverseAddress T hcomplete hnon wt
  have haLength : a.1.length = SkewTree.heightAt T w := by
    exact ForwardCompleteBijection.inverse_length T hcomplete hnon wt
  have htakeLength : (a.1.take r).length = r := by
    simp [List.length_take, Nat.min_eq_left (by omega : r ≤ a.1.length)]
  have htakeBound : InHomTree q (a.1.take r) := by
    change (a.1.take r).length < q
    have haBound : a.1.length < q := a.2
    omega
  let v : BoundedNode b q := ⟨a.1.take r, htakeBound⟩
  let u := ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon v
  have huRank : SkewTree.heightAt T u.1 = r := by
    calc
      SkewTree.heightAt T u.1 = v.1.length :=
        ForwardCompleteEmbedding.canonicalEmbedding_height
          T hcomplete hnon v
      _ = r := htakeLength
  have haddrPre : IsPrefix v.1 a.1 := by
    refine ⟨a.1.drop r, ?_⟩
    exact (List.take_append_drop r a.1).symm
  have hcanon :
      IsPrefix u.1
        (ForwardCompleteEmbedding.canonicalEmbedding
          T hcomplete hnon a).1 :=
    ForwardCompleteEmbedding.canonicalEmbedding_prefix
      T hcomplete hnon v a haddrPre
  have hwCanon :
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon a).1 = w :=
    congrArg Subtype.val
      (ForwardCompleteBijection.inverse_right T hcomplete hnon wt)
  rw [hwCanon] at hcanon
  have hne : u.1 ≠ w := by
    intro heq
    rw [heq] at huRank
    omega
  exact ⟨u.1, u.2, huRank, ⟨hcanon, hne⟩⟩

end DualTree.ForwardCompleteRankPredecessor
