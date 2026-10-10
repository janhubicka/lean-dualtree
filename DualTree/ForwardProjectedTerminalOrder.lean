import DualTree.ForwardFrontierRanks

/-!
# Forward order of projected points in distinct frontier cones

For a complete skew support T and an auxiliary cut, the D₂
coordinates are attached to distinct minimal outside-cut frontiers.

The candidate global forward-lex correction supplies three
independent facts:

* the frontier enumeration is nondecreasing in intrinsic rank;
* Definition 20 makes the selected singleton local-tail
  lengths nondecreasing;
* each canonical cone projection advances intrinsic T-rank by
  exactly the local-tail length.

Therefore, two projected marked points from ordered frontier
coordinates have nondecreasing T-rank. If the ranks are equal,
the frontier ranks and local-tail lengths are each equal. The
frontier order then implies lex order of the two incomparable
frontier cones and hence lex order of their projected points.
The skew length axioms (ii)--(iii) consequently imply forward
auxiliary monotonicity of the projected marked points in T.

This is a source-geometry-independent generic theorem. The
remaining repair of Lemma 27 must still identify intrinsic ranks
in the *new* Q support, prove order of original interior nodes
against projected markers, and construct g_w.
-/

namespace DualTree.ForwardProjectedTerminalOrder

/-- Lex comparison between incomparable tree nodes persists
under all their extensions. -/
theorem lex_extensions_of_incomparable {b : Nat} :
    ∀ (f g x y : Node b),
      FinLexLE f g →
      ¬ IsPrefix f g →
      ¬ IsPrefix g f →
      FinLexLE (f ++ x) (g ++ y) := by
  intro f
  induction f with
  | nil =>
      intro g x y _ hno _
      exact False.elim (hno ⟨g, by simp⟩)
  | cons a fs ih =>
      intro g x y hlex hnoFG hnoGF
      cases g with
      | nil =>
          exact False.elim
            (hnoGF ⟨a :: fs, by simp⟩)
      | cons c gs =>
          by_cases hac : a = c
          · subst c
            have hlexTail : FinLexLE fs gs := by
              simpa [FinLexLE, finLexLEB] using hlex
            have hnoTailFG : ¬ IsPrefix fs gs := by
              rintro ⟨tail, heq⟩
              apply hnoFG
              refine ⟨tail, ?_⟩
              simpa [heq]
            have hnoTailGF : ¬ IsPrefix gs fs := by
              rintro ⟨tail, heq⟩
              apply hnoGF
              refine ⟨tail, ?_⟩
              simpa [heq]
            simpa [FinLexLE, finLexLEB] using
              (ih gs x y hlexTail hnoTailFG hnoTailGF)
          · have hlt : a < c := by
              have htest : decide (a < c) = true := by
                simpa [FinLexLE, finLexLEB, hac] using hlex
              simpa using htest
            simp [FinLexLE, finLexLEB, hac, hlt]

/-- Same-height frontiers in forward auxiliary order
must also be in ordinary forward lex order. If the
ambient lengths are different, the skew same-height
condition rules out the opposite lex direction. -/
theorem lex_of_equal_rank_forwardAux
    {b : Nat} (T : List (Node b))
    (hII : SkewTree.condIIB T = true)
    (f g : Node b)
    (hf : f ∈ T) (hg : g ∈ T)
    (heq : SkewTree.heightAt T f = SkewTree.heightAt T g)
    (hfg : ForwardAux f g) :
    FinLexLE f g := by
  rcases hfg with hlt | ⟨_, hlex⟩
  · rcases finLexLE_total f g with hfgLex | hgfLex
    · exact hfgLex
    · have hrow := (List.all_eq_true.mp hII) g hg
      have hentry := (List.all_eq_true.mp hrow) f hf
      have hlen : g.length ≤ f.length := by
        simpa [heq.symm, hgfLex] using hentry
      omega
  · exact hlex

/-- Distinct minimal outside-cut frontiers have
incomparable ambient prefix cones. -/
theorem frontiers_incomparable
    {b : Nat} (T : List (Node b))
    (cut f g : Node b)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f)
    (hg : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) g)
    (hne : f ≠ g) :
    ¬ IsPrefix f g ∧ ¬ IsPrefix g f := by
  constructor
  · intro hprefix
    exact hne
      (CutFrontier.frontier_antichain T
        (fun u => ForwardAux u cut) hf hg hprefix)
  · intro hprefix
    exact hne
      (CutFrontier.frontier_antichain T
        (fun u => ForwardAux u cut) hg hf hprefix).symm

/-- Core projected-point comparison: if f,g are distinct
minimal forward frontiers, ordered as f ≤aux g,
and u,v are projected support descendants of those
frontiers with T-rank increments n≤m, then
u ≤aux v in the globally forward convention.

This theorem needs only verified rank equations
for u and v, not any particular implementation
of the canonical cone map. -/
theorem ordered_frontier_projections_forwardAux
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f g u v : Node b)
    (hf : CutFrontier.Frontier T
      (fun t => ForwardAux t cut) f)
    (hg : CutFrontier.Frontier T
      (fun t => ForwardAux t cut) g)
    (hne : f ≠ g)
    (hfg : ForwardAux f g)
    (hu : u ∈ T) (hv : v ∈ T)
    (hfu : IsPrefix f u)
    (hgv : IsPrefix g v)
    (n m : Nat)
    (hranku :
      SkewTree.heightAt T u = SkewTree.heightAt T f + n)
    (hrankv :
      SkewTree.heightAt T v = SkewTree.heightAt T g + m)
    (htails : n ≤ m) :
    ForwardAux u v := by
  have hfrank : SkewTree.heightAt T f ≤ SkewTree.heightAt T g :=
    ForwardFrontierRanks.ordered_frontiers_rank_le T
      hskew hnonsingleton cut f g hf hg hfg
  have hProjRank :
      SkewTree.heightAt T u ≤ SkewTree.heightAt T v := by
    omega
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have hcore := hparts.2
  simp [hnonsingleton, Bool.and_eq_true] at hcore
  have hII : SkewTree.condIIB T = true := hcore.1.1.2
  have hIII : SkewTree.condIIIB T = true := hcore.1.2
  by_cases hlt :
      SkewTree.heightAt T u < SkewTree.heightAt T v
  · exact ForwardOrderCompatibility.forwardAux_of_lower_height
      T hIII hu hv hlt
  · have heqRank :
        SkewTree.heightAt T u = SkewTree.heightAt T v := by
      omega
    have heqFrontier :
        SkewTree.heightAt T f = SkewTree.heightAt T g := by
      omega
    have hlexFrontier : FinLexLE f g :=
      lex_of_equal_rank_forwardAux T hII
        f g hf.1 hg.1 heqFrontier hfg
    rcases frontiers_incomparable T cut f g hf hg hne with
      ⟨hnotFG, hnotGF⟩
    rcases hfu with ⟨x, rfl⟩
    rcases hgv with ⟨y, rfl⟩
    have hlex : FinLexLE (f ++ x) (g ++ y) :=
      lex_extensions_of_incomparable f g x y
        hlexFrontier hnotFG hnotGF
    exact ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      T hII hu hv heqRank hlex

/-- The final numerical consequence needed to compare
lengths of marked Q nodes: ordered projections in T
have nondecreasing *ambient* word lengths, not merely
nondecreasing intrinsic T-ranks. -/
theorem ordered_frontier_projections_length_le
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f g u v : Node b)
    (hf : CutFrontier.Frontier T
      (fun t => ForwardAux t cut) f)
    (hg : CutFrontier.Frontier T
      (fun t => ForwardAux t cut) g)
    (hne : f ≠ g)
    (hfg : ForwardAux f g)
    (hu : u ∈ T) (hv : v ∈ T)
    (hfu : IsPrefix f u)
    (hgv : IsPrefix g v)
    (n m : Nat)
    (hranku :
      SkewTree.heightAt T u = SkewTree.heightAt T f + n)
    (hrankv :
      SkewTree.heightAt T v = SkewTree.heightAt T g + m)
    (htails : n ≤ m) :
    u.length ≤ v.length := by
  have hforward : ForwardAux u v :=
    ordered_frontier_projections_forwardAux
      T hskew hnonsingleton cut f g u v
      hf hg hne hfg hu hv hfu hgv
      n m hranku hrankv htails
  rcases hforward with hlt | ⟨heq, _⟩ <;> omega

end DualTree.ForwardProjectedTerminalOrder
