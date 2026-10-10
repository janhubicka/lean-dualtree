import DualTree.ForwardCutTerminalOrder
import DualTree.FrontierHeightBound

/-!
# Exact rank bands for minimal support frontiers beyond a forward cut

Under the repaired forward-lex auxiliary order, any support vertex
outside the auxiliary initial segment through `cut` has intrinsic
rank at least `heightAt T cut`. In particular every minimal
outside-cut frontier lies at that rank or exactly one rank higher.

The upper bound follows because every proper support predecessor
of a frontier lies before the cut, and the skew level-separation
axiom bounds the ranks of all those predecessors. The lower bound
is new: an outside-cut frontier of lower rank would have strictly
shorter ambient length than `cut`, putting it back inside the
forward auxiliary initial segment.

Consequently the *ordered* frontier list has nondecreasing
intrinsic ranks. Combining these ranks with the nondecreasing
local marked-point lengths from vector 1-completeness yields
nondecreasing total intrinsic ranks of the projected points
in a complete skew support (once their canonical cone height
equations have been established for the repaired order).

The proofs in this file use forward auxiliary order and source
skew predicates directly, independently of the old
printed-order complete-support projection implementation.
-/

namespace DualTree.ForwardFrontierRanks

/-- On a skew support, the repaired forward auxiliary
comparison is nondecreasing in intrinsic support rank. -/
theorem rank_le_of_forwardAux
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    {s t : Node b}
    (hs : s ∈ T) (ht : t ∈ T)
    (haux : ForwardAux s t) :
    SkewTree.heightAt T s ≤ SkewTree.heightAt T t := by
  by_contra hn
  have hreverse :
      SkewTree.heightAt T t < SkewTree.heightAt T s := by
    omega
  have hlength : t.length < s.length :=
    SkewLevelOrder.length_lt_of_height_lt
      T SkewTree.forwardAuxB hskew hnonsingleton
      ht hs hreverse
  rcases haux with hlen | ⟨heq, _⟩ <;> omega

/-- The rank of a minimal outside-cut frontier cannot be
below the rank of the cut. -/
theorem cut_rank_le_frontier
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f : Node b)
    (hcut : cut ∈ T)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f) :
    SkewTree.heightAt T cut ≤ SkewTree.heightAt T f := by
  by_contra hn
  have hlt :
      SkewTree.heightAt T f < SkewTree.heightAt T cut := by omega
  have hforward : ForwardAux f cut :=
    ForwardOrderCompatibility.forwardAux_of_lower_height
      T (SkewLevelOrder.condIIIB_of_skew
        T SkewTree.forwardAuxB hskew hnonsingleton)
      hf.1 hcut hlt
  exact hf.2.1 hforward

/-- Forward-lex counterpart of the printed-order frontier
bound. Every proper support predecessor of f lies before
cut, hence has intrinsic height at most the cut's height;
their number is therefore bounded by cut height plus one. -/
theorem frontier_rank_le_cut_succ
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f : Node b)
    (hcut : cut ∈ T)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f) :
    SkewTree.heightAt T f ≤ SkewTree.heightAt T cut + 1 := by
  have hparts := hskew
  simp only [SkewTree.skewB, Bool.and_eq_true] at hparts
  have hnodup : T.Nodup := by simpa using hparts.1
  have hpredNodup : (SkewTree.preds T f).Nodup := by
    unfold SkewTree.preds
    exact hnodup.filter _
  have hpred :
      ∀ r, r ∈ SkewTree.preds T f →
        r ∈ T ∧ IsStrictPrefix r f := by
    intro r hr
    change r ∈ T.filter
      (fun u => SkewTree.strictPrefixB u f) at hr
    rcases List.mem_filter.mp hr with ⟨hrT, hrB⟩
    exact ⟨hrT,
      (SkewBranchGeometry.strictPrefixB_iff r f).1 hrB⟩
  have hbound :
      ∀ r, r ∈ SkewTree.preds T f →
        SkewTree.heightAt T r ≤ SkewTree.heightAt T cut := by
    intro r hr
    rcases hpred r hr with ⟨hrT, hrPre⟩
    have hrEarly : ForwardAux r cut :=
      hf.2.2 r hrT hrPre
    by_contra hn
    have hheight :
        SkewTree.heightAt T cut < SkewTree.heightAt T r := by
      omega
    have hlen : cut.length < r.length :=
      SkewLevelOrder.length_lt_of_height_lt T
        SkewTree.forwardAuxB hskew hnonsingleton
        hcut hrT hheight
    rcases hrEarly with hlt | ⟨heq, _⟩ <;> omega
  have hinjective :
      ∀ r, r ∈ SkewTree.preds T f →
      ∀ s, s ∈ SkewTree.preds T f →
        SkewTree.heightAt T r = SkewTree.heightAt T s →
        r = s := by
    intro r hr s hs heq
    rcases hpred r hr with ⟨hrT, hrPrefix⟩
    rcases hpred s hs with ⟨hsT, hsPrefix⟩
    exact SupportHeightRanks.heightAt_injective_on_common_path
      T hrT hsT hrPrefix.1 hsPrefix.1 heq
  exact
    RankCardinality.nodup_length_le_of_rank_bound
      (SkewTree.preds T f)
      (SkewTree.heightAt T cut)
      (SkewTree.heightAt T)
      hpredNodup hbound hinjective

/-- The exact two-level frontier band in a repaired
forward-auxiliary skew support. -/
theorem frontier_rank_band
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f : Node b)
    (hcut : cut ∈ T)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f) :
    SkewTree.heightAt T f = SkewTree.heightAt T cut ∨
      SkewTree.heightAt T f = SkewTree.heightAt T cut + 1 := by
  have hl := cut_rank_le_frontier T hskew hnonsingleton cut f hcut hf
  have hu := frontier_rank_le_cut_succ T hskew hnonsingleton cut f hcut hf
  omega

/-- An ordered pair of repaired frontiers has nondecreasing
intrinsic ambient-support ranks. The frontier property is
used for membership, not for the monotonicity itself. -/
theorem ordered_frontiers_rank_le
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f g : Node b)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f)
    (hg : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) g)
    (hfg : ForwardAux f g) :
    SkewTree.heightAt T f ≤ SkewTree.heightAt T g :=
  rank_le_of_forwardAux T hskew hnonsingleton hf.1 hg.1 hfg

/-- Rank plus local tail length is monotone in the
ordered frontier coordinates when marked singleton
lengths are nondecreasing, exactly the arithmetic
needed for projected support rank comparisons. -/
theorem ordered_frontiers_projected_rank_mono
    {b : Nat} (T : List (Node b))
    (hskew : SkewTree.skewB SkewTree.forwardAuxB T = true)
    (hnonsingleton : T.length ≠ 1)
    (cut f g : Node b)
    (hf : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) f)
    (hg : CutFrontier.Frontier T
      (fun u => ForwardAux u cut) g)
    (hfg : ForwardAux f g)
    (n m : Nat) (hnm : n ≤ m) :
    SkewTree.heightAt T f + n ≤
      SkewTree.heightAt T g + m :=
  Nat.add_le_add
    (ordered_frontiers_rank_le T hskew hnonsingleton cut f g hf hg hfg)
    hnm

end DualTree.ForwardFrontierRanks
