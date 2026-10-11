import DualTree.ForwardQOrderClosure

/-!
# Transport the remaining Q new/new comparisons to ambient T ranks

The actual projected D₂ points belong to the enclosing genuine
forward-complete skew support T. That support's established skew
clauses transfer ambient T *rank* comparisons directly into
ambient word-length comparisons:

* h_T(P_i) < h_T(P_j) implies |P_i| < |P_j|;
* h_T(P_i) <= h_T(P_j) together with P_i <=lex P_j
  implies |P_i| <= |P_j|.

Consequently the four-input Q semi-completeness API of
ForwardQOrderClosure can be instantiated from only two
new/new *rank* transport hypotheses, in addition to the
already isolated mixed old/new conditions. This is the
precise remaining combinatorial target for the geometry:
  same-Q-rank lex pairs should be nondecreasing in T rank;
  strictly increasing Q rank should imply increasing T rank.

The latter rank-transport implication is currently supported
by finite adversarial tests but NOT proved in Lean. This file
only verifies its conditional consequences; there are no
unproved axioms or assumptions silently removed.
-/

namespace DualTree.ForwardQAmbientRankClosure

open ForwardSourceQTree

/-- Increasing intrinsic ambient-T ranks of actual projected
points imply strictly increasing ambient word length, by
the enclosing complete skew support's clause (iii). -/
theorem marked_length_lt_of_ambient_rank_lt
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hTrank :
      SkewTree.heightAt c.T (markedProjection c x i).1 <
        SkewTree.heightAt c.T (markedProjection c x j).1) :
    (markedProjection c x i).1.length <
      (markedProjection c x j).1.length := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  exact SkewLevelOrder.length_lt_of_height_lt
    c.T SkewTree.forwardAuxB hc.1 c.hnon
    (markedProjection c x i).2 (markedProjection c x j).2
    hTrank

/-- Nondecreasing intrinsic T rank plus a forward lex
comparison implies weakly increasing word length:
strict ambient rank uses skew (iii); equal ambient
rank uses skew (ii). -/
theorem marked_length_le_of_ambient_rank_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hlex : FinLexLE (markedProjection c x i).1
      (markedProjection c x j).1)
    (hTrank :
      SkewTree.heightAt c.T (markedProjection c x i).1 ≤
        SkewTree.heightAt c.T (markedProjection c x j).1) :
    (markedProjection c x i).1.length ≤
      (markedProjection c x j).1.length := by
  rcases lt_or_eq_of_le hTrank with hlt | heq
  · exact Nat.le_of_lt
      (marked_length_lt_of_ambient_rank_lt c x i j hlt)
  · have hc := c.hcomplete
    simp only [SkewTree.completeB, Bool.and_eq_true] at hc
    have hparts := hc.1
    simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
    have hcore := hparts.2
    simp [c.hnon, Bool.and_eq_true] at hcore
    have hII : SkewTree.condIIB c.T = true := hcore.1.1.2
    have hrow := (List.all_eq_true.mp hII)
      (markedProjection c x i).1 (markedProjection c x i).2
    have hentry := (List.all_eq_true.mp hrow)
      (markedProjection c x j).1 (markedProjection c x j).2
    simpa [heq, hlex] using hentry

/-- The remaining two new/new length inequalities are
automatically discharged by the corresponding intrinsic
ambient-T rank order inequalities. Combined with the two
old/new interfaces, they give the entire actual corrected
Q semi-completeness (root, branching and skew). -/
theorem Q_semiComplete_of_ambient_rank_transport
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
    (hNewIITrank :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 =
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        FinLexLE (markedProjection c x i).1
          (markedProjection c x j).1 →
        SkewTree.heightAt c.T (markedProjection c x i).1 ≤
          SkewTree.heightAt c.T (markedProjection c x j).1)
    (hNewIIITrank :
      ∀ (i j : MixedProduct.BulletIndex (kind c)),
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x i).1 <
        SkewTree.heightAt (nodes c x).toList
          (markedProjection c x j).1 →
        SkewTree.heightAt c.T (markedProjection c x i).1 <
          SkewTree.heightAt c.T (markedProjection c x j).1) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x).toList = true := by
  exact ForwardQOrderClosure.Q_semiComplete_of_pairwise_order
    hb c x hOldLex hOldNewIII
    (fun i j hQ hlex =>
      marked_length_le_of_ambient_rank_le c x i j hlex
        (hNewIITrank i j hQ hlex))
    (fun i j hQ =>
      marked_length_lt_of_ambient_rank_lt c x i j
        (hNewIIITrank i j hQ))

end DualTree.ForwardQAmbientRankClosure
