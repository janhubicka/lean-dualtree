import DualTree.ForwardQFrontierBandMatch
import DualTree.ForwardQStarredD2Certificate
import DualTree.ForwardQMixedCondII
import DualTree.ForwardQTopRankLength
import DualTree.ForwardQAmbientRankClosure

/-!
# Semi-completeness of the actual corrected Q support under starred D₂ order

The previous source-facing modules have verified:
* the exact literal corrected Q node set, its root, branching,
  meet closure and final skew branching witness;
* strict/equal-rank old/old and mixed old/new skew order clauses;
* the two-level rank matching of every genuine selected D₂ Q leaf
  to the intrinsic T rank of its selected sorted frontier;
* monotonicity of the actual complete T ranks and ambient lengths
  of selected projections, provided local D₂ point lengths follow
  the order required by vector-one-completeness.

This file discharges BOTH remaining new/new Q skew inequalities.
Equal-Q-rank leaves have equal frontier T rank; their lex order
recovers the sorted D₂ index order, so marked-point lengths and
projected ambient lengths are nondecreasing. Strictly increasing
Q rank means a strict increase of frontier T rank; sorted frontier
ranks force the selected indices to occur in that order, and the
additive canonical projection T-rank formula makes the ambient T
projection ranks strictly increase, hence ambient word lengths.

Thus the *actual* corrected Q node set is semi-complete skew
under the precise BulletLengthsOrdered source-domain hypothesis.

A second theorem packages that hypothesis by the explicit
order-reflecting vector-one-complete D₂ certificate. Constructing
this certificate from every printed W_* instance is still open.
Neither theorem constructs the new word g_w, establishes smoothness
or colouring compatibility, or proves the full dual Ramsey theorem.
-/

namespace DualTree.ForwardQCertifiedSemiComplete

open ForwardSourceQTree

/-- The remaining equal-Q-rank new/new skew clause (ii) follows
from the two-band frontier matching and actual selected D₂
point-length order, independently of the unused D₀ words. -/
theorem marked_marked_condII
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hQ :
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 =
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x j).1)
    (hlex : FinLexLE (markedProjection c x i).1
      (markedProjection c x j).1) :
    (markedProjection c x i).1.length ≤
      (markedProjection c x j).1.length := by
  have hfront :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 :=
    (ForwardQFrontierBandMatch.Q_rank_eq_iff_frontier_T_rank_eq
      hb c x i j).1 hQ
  have hindex : i.1 ≤ j.1 :=
    ForwardQFrontierIndexOrder.bullet_index_le_of_equal_frontier_rank_lex
      c x i j hfront hlex
  by_cases hij : i.1 < j.1
  · exact ForwardQIndexedTRanks.marked_length_mono_of_bullet_order
      c x hordered i j hij
  · have heq : i = j := Subtype.ext (by omega)
    subst j
    exact le_refl _

/-- The remaining strictly increasing-Q-rank new/new skew
clause (iii). The two frontier levels are strictly ordered,
so the true sorted bullet indices are strictly ordered.
The local tail-order condition makes the projected T ranks
strictly ordered and T skewness supplies strict word lengths. -/
theorem marked_marked_condIII
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x)
    (i j : MixedProduct.BulletIndex (kind c))
    (hQ :
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x i).1 <
      SkewTree.heightAt (nodes c x).toList
        (markedProjection c x j).1) :
    (markedProjection c x i).1.length <
      (markedProjection c x j).1.length := by
  have hfront :
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 <
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 :=
    (ForwardQFrontierBandMatch.Q_rank_lt_iff_frontier_T_rank_lt
      hb c x i j).1 hQ
  have hij : i.1 < j.1 := by
    by_contra hn
    have hji : j.1 ≤ i.1 := by omega
    by_cases heq : i.1 = j.1
    · have hsame : i = j := Subtype.ext heq
      subst j
      omega
    · have hjiStrict : j.1 < i.1 := by omega
      have hreverse :=
        ForwardQFrontierIndexOrder.frontier_T_rank_mono
          c j i hjiStrict
      omega
  have htailLe := hordered i j hij
  have hri := ForwardQIndexedTRanks.marked_T_rank_formula c x i
  have hrj := ForwardQIndexedTRanks.marked_T_rank_formula c x j
  have hTrank :
      SkewTree.heightAt c.T (markedProjection c x i).1 <
        SkewTree.heightAt c.T (markedProjection c x j).1 := by
    omega
  exact ForwardQAmbientRankClosure.marked_length_lt_of_ambient_rank_lt
    c x i j hTrank

/-- The exact reconstructed Q support is semi-complete skew
provided the actual selected D₂ marked points have the
starred vector-one length order. No fictitious Q support,
unverified branching or extra tail constraint is assumed. -/
theorem Q_semiComplete_of_bullet_lengths
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : ForwardQIndexedTRanks.BulletLengthsOrdered c x) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true := by
  exact ForwardQOrderClosure.Q_semiComplete_of_pairwise_order
    hb c x
    (fun s hs i hQ =>
      ForwardQMixedCondII.old_lex_marked_of_equal_Q_rank
        hb c x s hs i hQ)
    (fun s hs i hQ =>
      ForwardQTopRankLength.old_to_marked_condIII hb c x s hs i hQ)
    (fun i j hQ hlex =>
      marked_marked_condII hb c x hordered i j hQ hlex)
    (fun i j hQ =>
      marked_marked_condIII hb c x hordered i j hQ)

/-- A concrete order-reflecting vector-one-complete certificate
for the selected D₂ indices is sufficient for semi-completeness
of the actual Q tree. Recovering this certificate from every
published W_* object remains a separate theorem obligation. -/
theorem Q_semiComplete_of_starred_D2_certificate
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (cert : ForwardQStarredD2Certificate.Certificate c x) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true :=
  Q_semiComplete_of_bullet_lengths hb c x
    (ForwardQStarredD2Certificate.bullet_lengths_ordered_of_certificate
      c x cert)

end DualTree.ForwardQCertifiedSemiComplete
