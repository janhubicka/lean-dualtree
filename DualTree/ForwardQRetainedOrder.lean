import DualTree.ForwardQRetainedRanks
import DualTree.ForwardQRooted
import DualTree.ForwardQMarkedTerminals
import DualTree.ForwardAuxTransitivity

/-!
# Rank and ambient-length comparisons involving retained Q interior vertices

The globally corrected Q tree retains the original source interior
without altering its intrinsic heights. The printed skew conditions
(ii) and (iii) are consequently automatic for any pair of retained
old interior vertices: they follow from the original source's own
skew axioms.

In addition, every retained old interior vertex lies at or before the
maximal forward auxiliary cut, while every new projected D₂ marker lies
strictly after that inclusive cut. Forward auxiliary transitivity
therefore yields a strict ordering of the two *groups* in the length-
first forward order and weak ambient-length inequality.

This solves the old/old comparisons in both skew axioms and the
old-before-new ambient-length comparison. The converse new/old
lexicographic interaction, strict length comparisons at unequal Q
ranks, and all new/new rank comparisons still require their own
arguments. No full corrected Q semi-completeness is asserted.
-/

namespace DualTree.ForwardQRetainedOrder

open ForwardSourceQTree

/-- A nonsingleton forward semi-complete source satisfies the
same-height skew length monotonicity clause (ii). -/
theorem source_condIIB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.condIIB c.source.tree = true := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have hskew := hsemi.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hrest := hskew.2
  simp [ForwardQRooted.source_nonsingleton c, Bool.and_eq_true] at hrest
  exact hrest.1.1.2

/-- A nonsingleton forward semi-complete source satisfies the
strict different-height length separation clause (iii). -/
theorem source_condIIIB
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.condIIIB c.source.tree = true := by
  have hsemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsemi
  have hskew := hsemi.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hrest := hskew.2
  simp [ForwardQRooted.source_nonsingleton c, Bool.and_eq_true] at hrest
  exact hrest.1.2

/-- Two retained interior vertices on the same intrinsic Q level
satisfy clause (ii) of the reconstructed Q skew order without
any assumptions on the mixed-product D₂ points. -/
theorem Q_old_old_condII
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s t : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (ht : t ∈ SkewTree.interior c.source.tree)
    (hheight :
      SkewTree.heightAt (nodes c x).toList s =
      SkewTree.heightAt (nodes c x).toList t)
    (hlex : FinLexLE s t) :
    s.length ≤ t.length := by
  have hh : SkewTree.heightAt c.source.tree s =
      SkewTree.heightAt c.source.tree t := by
    rw [ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs,
      ForwardQRetainedRanks.original_interior_Q_height_eq_source
        c x t ht] at hheight
    exact hheight
  have hrow := (List.all_eq_true.mp (source_condIIB c))
    s (List.mem_filter.mp hs).1
  have hentry := (List.all_eq_true.mp hrow)
    t (List.mem_filter.mp ht).1
  simpa [hh, hlex] using hentry

/-- Two retained interior vertices at strictly increasing Q
ranks satisfy clause (iii) without any new marked-point data. -/
theorem Q_old_old_condIII
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s t : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (ht : t ∈ SkewTree.interior c.source.tree)
    (hheight :
      SkewTree.heightAt (nodes c x).toList s <
      SkewTree.heightAt (nodes c x).toList t) :
    s.length < t.length := by
  have hh : SkewTree.heightAt c.source.tree s <
      SkewTree.heightAt c.source.tree t := by
    rw [ForwardQRetainedRanks.original_interior_Q_height_eq_source
      c x s hs,
      ForwardQRetainedRanks.original_interior_Q_height_eq_source
        c x t ht] at hheight
    exact hheight
  have hrow := (List.all_eq_true.mp (source_condIIIB c))
    s (List.mem_filter.mp hs).1
  have hentry := (List.all_eq_true.mp hrow)
    t (List.mem_filter.mp ht).1
  simpa [hh] using hentry

/-- Every retained old Q interior vertex is before every new
projected marker in the corrected forward length-first order. -/
theorem Q_old_before_new
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c)) :
    ForwardAux s (markedProjection c x i).1 := by
  have hsCut : ForwardAux s c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax s hs
  have hnot : ¬ ForwardAux (markedProjection c x i).1 c.cut :=
    ForwardQMarkedTerminals.markedProjection_outside_cut c x i
  rcases CanonicalForwardAuxIso.forwardAux_total
      c.cut (markedProjection c x i).1 with hCutProj | hProjCut
  · exact ForwardAuxTransitivity.forwardAux_trans hsCut hCutProj
  · exact False.elim (hnot hProjCut)

/-- Thus a retained old interior vertex is never ambient-longer
than a projected marked point. This is the weak old/new length
comparison needed by skew clause (ii). -/
theorem Q_old_new_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b)
    (hs : s ∈ SkewTree.interior c.source.tree)
    (i : MixedProduct.BulletIndex (kind c)) :
    s.length ≤ (markedProjection c x i).1.length := by
  rcases Q_old_before_new c x s hs i with hlt | ⟨heq, _⟩
  · omega
  · omega

end DualTree.ForwardQRetainedOrder
