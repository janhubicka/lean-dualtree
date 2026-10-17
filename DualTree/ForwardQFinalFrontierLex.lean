import DualTree.ForwardQFinalRetainedSkewLength
import DualTree.ForwardQFinalRefinementRoots
import DualTree.ForwardQFinalSupportCut
import DualTree.ForwardProjectedTerminalOrder
import DualTree.SupportHeightRanks
import DualTree.CanonicalForwardAuxIso
import DualTree.PaperAuxAntisymm

/-!
# Rank-m frontiers lie lexicographically right of the retained rank-m cut

The exact Lemma 27 final skew conditions require comparing OLD
retained and NEW projected vertices of equal FINAL intrinsic rank.
Such an equality can occur only with both vertices at rank m,
a frontier of ambient T-rank m and local support rank zero.

The defining sorted frontier order is LENGTH-FIRST forward lex,
not simply global lex. It is therefore important to prove the
actual relative lex geometry, not assume sorting preserves lex.

We prove:
* a generic transitivity lemma for the executable FinLexLE,
  available to future finite skew tree arguments;
* a retained T vertex of T-rank m lies <=lex the cut t0;
* an outside-cut minimal T frontier of T-rank m lies >=lex t0;
* such a retained rank-m vertex lies <=lex the frontier;
* the inequality survives ANY ambient projection in the
  frontier cone, even with stretched ambient edges.

The last step uses equal support ranks to exclude either
node being an ancestor of the other, then applies the
previously verified lex comparison of incomparable cones.

The opposite-rank frontier pairs (m versus m+1), projected
versus projected length order and final skew witness IV
remain separate obligations.
-/

namespace DualTree.ForwardQFinalFrontierLex

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut

/-- Transitivity of the actual custom Boolean finite-list lex
order, whose prefixes are ordered before their extensions. -/
theorem finLexLE_trans {b : Nat} :
    ∀ s t u : Node b,
      FinLexLE s t → FinLexLE t u → FinLexLE s u := by
  intro s
  induction s with
  | nil =>
      intro t u _ _
      simp [FinLexLE, finLexLEB]
  | cons a as ih =>
      intro t u hst htu
      cases t with
      | nil =>
          simp [FinLexLE, finLexLEB] at hst
      | cons c cs =>
          cases u with
          | nil =>
              simp [FinLexLE, finLexLEB] at htu
          | cons d ds =>
              by_cases hac : a = c
              · subst c
                by_cases had : a = d
                · subst d
                  have hst' : FinLexLE as cs := by
                    simpa [FinLexLE, finLexLEB] using hst
                  have htu' : FinLexLE cs ds := by
                    simpa [FinLexLE, finLexLEB] using htu
                  simpa [FinLexLE, finLexLEB] using
                    (ih cs ds hst' htu')
                · have hlt : a < d := by
                    have hd : decide (a < d) = true := by
                      simpa [FinLexLE, finLexLEB, had] using htu
                    simpa using hd
                  simp [FinLexLE, finLexLEB, had, hlt]
              · have hltAC : a < c := by
                  have hd : decide (a < c) = true := by
                    simpa [FinLexLE, finLexLEB, hac] using hst
                  simpa using hd
                by_cases hcd : c = d
                · subst d
                  simp [FinLexLE, finLexLEB, hac, hltAC]
                · have hltCD : c < d := by
                    have hd : decide (c < d) = true := by
                      simpa [FinLexLE, finLexLEB, hcd] using htu
                    simpa using hd
                  have hltAD : a < d := lt_trans hltAC hltCD
                  simp [FinLexLE, finLexLEB, ne_of_lt hltAD, hltAD]

/-- A retained T vertex at the cut's own intrinsic T-rank m
cannot lie lexicographically to the right of the cut. An
opposite lex comparison would violate the original T skew
same-rank length condition against its forward cut bound. -/
theorem retained_rank_m_lex_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b)
    (hs : s ∈ retained c)
    (hrank : SkewTree.heightAt c.T s = m) :
    FinLexLE s c.cut := by
  have haux : ForwardAux s c.cut :=
    (Finset.mem_filter.mp hs).2
  rcases haux with hlength | ⟨_, hlex⟩
  · rcases finLexLE_total s c.cut with h | h
    · exact h
    · have hrow :=
        (List.all_eq_true.mp
          (ForwardQFinalRetainedSkewLength.ambient_condIIB c))
          c.cut c.hcutT
      have hcell :=
        (List.all_eq_true.mp hrow) s
          (retained_subset_T c s hs)
      have heqRank : SkewTree.heightAt c.T c.cut =
          SkewTree.heightAt c.T s := by
        rw [c.hm,hrank]
      have hreverse : c.cut.length ≤ s.length := by
        simpa [heqRank,h] using hcell
      omega
  · exact hlex

/-- An actual outside-cut T frontier of the SAME intrinsic
rank m as the cut is necessarily lexicographically AFTER
the cut, even when ambient edge lengths are stretched. -/
theorem frontier_rank_m_lex_after_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m) :
    FinLexLE c.cut
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 := by
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have hspec :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut i
  have hout : ¬ ForwardAux t c.cut := hspec.2.1
  rcases finLexLE_total c.cut t with h | h
  · exact h
  · have hrow :=
      (List.all_eq_true.mp
        (ForwardQFinalRetainedSkewLength.ambient_condIIB c))
        t hspec.1
    have hcell := (List.all_eq_true.mp hrow) c.cut c.hcutT
    have heqRank : SkewTree.heightAt c.T t =
        SkewTree.heightAt c.T c.cut := by
      change SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
        SkewTree.heightAt c.T c.cut
      rw [hfront,c.hm]
    have hlength : t.length ≤ c.cut.length := by
      simpa [heqRank,h] using hcell
    have haux : ForwardAux t c.cut := by
      rcases lt_or_eq_of_le hlength with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq,h⟩
    exact False.elim (hout haux)

/-- A retained old rank-m vertex lies lexicographically before
every actual outside-cut rank-m frontier. This is transitivity
of the two inequalities relative to the cut, not a claim
that all length-first-sorted frontiers are lex-sorted. -/
theorem retained_rank_m_lex_before_frontier_rank_m
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b) (hs : s ∈ retained c)
    (hrank : SkewTree.heightAt c.T s = m)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m) :
    FinLexLE s
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 :=
  finLexLE_trans s c.cut
    (ForwardOrderedProjections.frontierAt c.T c.cut i).1
    (retained_rank_m_lex_before_cut c s hs hrank)
    (frontier_rank_m_lex_after_cut c i hfront)

/-- A retained rank-m node and an outside-cut rank-m
frontier are prefix-incomparable: comparable distinct
support vertices necessarily have different ranks. -/
theorem retained_rank_m_incomparable_frontier_rank_m
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b) (hs : s ∈ retained c)
    (hrank : SkewTree.heightAt c.T s = m)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m) :
    ¬ IsPrefix s
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 ∧
    ¬ IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 s := by
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have ht := ForwardOrderedProjections.frontierAt_spec c.T c.cut i
  have hsBefore : ForwardAux s c.cut :=
    (Finset.mem_filter.mp hs).2
  have hne : s ≠ t := by
    intro heq
    rw [heq] at hsBefore
    exact ht.2.1 hsBefore
  constructor
  · intro hpre
    have hlt := SupportHeightRanks.heightAt_lt_of_strictPrefix
      c.T (retained_subset_T c s hs) ⟨hpre,hne⟩
    change SkewTree.heightAt c.T s <
      SkewTree.heightAt c.T
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 at hlt
    rw [hrank,hfront] at hlt
    omega
  · intro hpre
    have hfrontBefore : ForwardAux t c.cut :=
      ForwardInclusiveFrontier.forwardAux_of_prefix hpre hsBefore
    exact ht.2.1 hfrontBefore

/-- An ambient projection of a rank-m frontier stays strictly
to the RIGHT in ordinary lex of every retained rank-m vertex.
The original rank-m vertices and the frontier are
incomparable; hence extending the frontier cannot move
its projected descendants to the other side of the retained
vertex, even if the projected edge is stretched. -/
theorem retained_rank_m_lex_before_projected_rank_m
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s : Node b) (hs : s ∈ retained c)
    (hrank : SkewTree.heightAt c.T s = m)
    (i : Index c)
    (hfront : SkewTree.heightAt c.T
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 = m)
    (z : BoundedNode b (k-(m+1))) :
    FinLexLE s (projected c ⟨i,z⟩).1 := by
  let t := (ForwardOrderedProjections.frontierAt c.T c.cut i).1
  have hlex : FinLexLE s t :=
    retained_rank_m_lex_before_frontier_rank_m c s hs hrank i hfront
  obtain ⟨hnoST,hnoTS⟩ :=
    retained_rank_m_incomparable_frontier_rank_m
      c s hs hrank i hfront
  obtain ⟨tail,htail⟩ := projected_cone c ⟨i,z⟩
  have hlexProj :=
    ForwardProjectedTerminalOrder.lex_extensions_of_incomparable
      s t [] tail hlex hnoST hnoTS
  simpa only [List.append_nil,htail] using hlexProj

end DualTree.ForwardQFinalFrontierLex
