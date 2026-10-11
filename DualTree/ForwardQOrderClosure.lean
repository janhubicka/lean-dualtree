import DualTree.ForwardQSkewIV
import DualTree.ForwardQRetainedOrder
import DualTree.ForwardQMarkerRankBand

/-!
# Pairwise-order closure API for the corrected Q support

The actual corrected Q node set is the union of:
(1) original interior source vertices, and
(2) projections of the genuinely sorted D₂ bullet coordinates.

The geometric portions of semi-completeness are already checked:
root, exact original interior, meet closure, 0-or-b branching and
the final branching witness. The previously audited theorem
Q_semiComplete_iff_order_conditions reduces the whole target to
only the two numerical skew clauses (ii) and (iii).

This file gives an explicit minimal application API. Every old/old
pair is settled by the original source's skew clauses; a new node
never lies below an old vertex in intrinsic Q rank. For old/new
pairs only the following two properties need to be supplied:
  * equal Q rank -> the old node is <=lex the new node;
  * strictly increasing Q rank -> strictly increasing word length.
For pairs of two projected D₂ leaves, supply the literal same-rank
lex/length and different-rank length conditions.

The conclusion is the full *actual* source-facing corrected Q
semiCompleteB, not an abstract schematic support. The remaining
tasks are to discharge exactly these four inputs from Definition 20
and the mixed product, then prove the Q word/colouring.
-/

namespace DualTree.ForwardQOrderClosure

open ForwardSourceQTree

/-- Every literal Q node is either a retained original
source interior vertex or the actual projection of a D₂
bullet coordinate. -/
private theorem old_or_marked
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ (nodes c x).toList) :
    s ∈ SkewTree.interior c.source.tree ∨
      ∃ i : MixedProduct.BulletIndex (kind c),
        (markedProjection c x i).1 = s := by
  classical
  have hsFin : s ∈ nodes c x := Finset.mem_toList.mp hs
  change s ∈ (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1) at hsFin
  rcases Finset.mem_union.mp hsFin with hbase | hmarked
  · exact Or.inl
      ((ForwardQFixedBase.oldBase_mem_iff_original_interior c s).1
        (List.mem_toFinset.mp hbase))
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmarked
    exact Or.inr ⟨i, hi⟩

/-- Every original source interior node has new Q rank at
most the rank of any genuinely projected Q leaf. No
assumptions on local bullet lengths are needed. -/
theorem old_Q_rank_le_marked
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c)) :
    SkewTree.heightAt (nodes c x).toList s ≤
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have hsAux : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hsRankLe :
      SkewTree.heightAt c.source.tree s ≤
        SkewTree.heightAt c.source.tree c.cut :=
    ForwardFrontierRanks.rank_le_of_forwardAux
      c.source.tree hsemi.1
      (ForwardQRooted.source_nonsingleton c)
      (List.mem_filter.mp hs).1 (List.mem_filter.mp c.hcut).1
      hsAux
  have hOldQ :=
    ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs
  rcases ForwardQMarkerRankBand.markedProjection_Q_rank_band
      hb c x i with hNew | hNew
  · omega
  · omega

/-- Pairwise hypotheses required to settle all of the
actual Q same-intrinsic-rank skew length clause (ii).
Old/old comparisons and weak old/new length monotonicity
are already verified. -/
theorem Q_condIIB_of_mixed_new_pairs
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hOldLex :
      ∀ (s : Node b),
        s ∈ SkewTree.interior c.source.tree →
        ∀ (i : MixedProduct.BulletIndex (kind c)),
          SkewTree.heightAt (nodes c x).toList s =
            SkewTree.heightAt (nodes c x).toList
              (markedProjection c x i).1 →
          FinLexLE s (markedProjection c x i).1)
    (hNewII :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        FinLexLE (markedProjection c x i).1
          (markedProjection c x j).1 →
        (markedProjection c x i).1.length ≤
          (markedProjection c x j).1.length) :
    SkewTree.condIIB (nodes c x).toList = true := by
  classical
  unfold SkewTree.condIIB
  apply List.all_eq_true.mpr
  intro s hs
  apply List.all_eq_true.mpr
  intro t ht
  split_ifs with hcase
  · have hlen : s.length ≤ t.length := by
      rcases old_or_marked c x s hs with hsOld | ⟨i, hi⟩
      · rcases old_or_marked c x t ht with htOld | ⟨j, hj⟩
        · exact ForwardQRetainedOrder.Q_old_old_condII
            c x s t hsOld htOld hcase.1 hcase.2
        · subst t
          exact ForwardQRetainedOrder.Q_old_new_length_le c x s hsOld j
      · rcases old_or_marked c x t ht with htOld | ⟨j, hj⟩
        · subst s
          have hLexOld :=
            hOldLex t htOld i hcase.1.symm
          have hsame : t = (markedProjection c x i).1 :=
            PaperAuxAntisymm.finLexLE_antisymm
              t (markedProjection c x i).1 hLexOld hcase.2
          simp [hsame]
        · subst s
          subst t
          exact hNewII i j hcase.1 hcase.2
    simpa [hlen]
  · rfl

/-- Pairwise hypotheses required to settle every instance
of skew clause (iii) in the actual Q support. The reverse
new/old strict rank ordering is already impossible. -/
theorem Q_condIIIB_of_mixed_new_pairs
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hOldNewIII :
      ∀ (s : Node b),
        s ∈ SkewTree.interior c.source.tree →
        ∀ (i : MixedProduct.BulletIndex (kind c)),
          SkewTree.heightAt (nodes c x).toList s <
            SkewTree.heightAt (nodes c x).toList
              (markedProjection c x i).1 →
          s.length < (markedProjection c x i).1.length)
    (hNewIII :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 <
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        (markedProjection c x i).1.length <
          (markedProjection c x j).1.length) :
    SkewTree.condIIIB (nodes c x).toList = true := by
  classical
  unfold SkewTree.condIIIB
  apply List.all_eq_true.mpr
  intro s hs
  apply List.all_eq_true.mpr
  intro t ht
  split_ifs with hcase
  · have hlen : s.length < t.length := by
      rcases old_or_marked c x s hs with hsOld | ⟨i, hi⟩
      · rcases old_or_marked c x t ht with htOld | ⟨j, hj⟩
        · exact ForwardQRetainedOrder.Q_old_old_condIII
            c x s t hsOld htOld hcase
        · subst t
          exact hOldNewIII s hsOld j hcase
      · rcases old_or_marked c x t ht with htOld | ⟨j, hj⟩
        · subst s
          have hrank := old_Q_rank_le_marked hb c x t htOld i
          omega
        · subst s
          subst t
          exact hNewIII i j hcase
    simpa [hlen]
  · rfl

/-- Full source-facing semi-completeness of the literal
corrected Q tree reduces to exactly four transparent
rank-sensitive order hypotheses: old/new equal-rank lex,
old/new different-rank length, and both new/new clauses.
No branching/rootedness hypotheses are passed by users. -/
theorem Q_semiComplete_of_pairwise_order
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hOldLex :
      ∀ (s : Node b),
        s ∈ SkewTree.interior c.source.tree →
        ∀ (i : MixedProduct.BulletIndex (kind c)),
          SkewTree.heightAt (nodes c x).toList s =
            SkewTree.heightAt (nodes c x).toList
              (markedProjection c x i).1 →
          FinLexLE s (markedProjection c x i).1)
    (hOldNewIII :
      ∀ (s : Node b),
        s ∈ SkewTree.interior c.source.tree →
        ∀ (i : MixedProduct.BulletIndex (kind c)),
          SkewTree.heightAt (nodes c x).toList s <
            SkewTree.heightAt (nodes c x).toList
              (markedProjection c x i).1 →
          s.length < (markedProjection c x i).1.length)
    (hNewII :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        FinLexLE (markedProjection c x i).1
          (markedProjection c x j).1 →
        (markedProjection c x i).1.length ≤
          (markedProjection c x j).1.length)
    (hNewIII :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 <
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        (markedProjection c x i).1.length <
          (markedProjection c x j).1.length) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true := by
  apply (ForwardQSkewIV.Q_semiComplete_iff_order_conditions
    hb c x).2
  exact ⟨Q_condIIB_of_mixed_new_pairs c x hOldLex hNewII,
    Q_condIIIB_of_mixed_new_pairs hb c x hOldNewIII hNewIII⟩

end DualTree.ForwardQOrderClosure
