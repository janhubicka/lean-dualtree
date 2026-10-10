import DualTree.CanonicalForwardAuxIso
import DualTree.FullBeforeSignature

/-!
# Terminal vertices relative to the last branching cut in forward order

Under the candidate repaired length-first forward-lex auxiliary
order, the skew clauses (ii)--(iv) interact in a useful way.

If a cut has full branching at every strictly earlier support
vertex, no terminal support vertex can precede that cut.
Consequently:
* a terminal vertex cannot have smaller intrinsic height
  than the cut, by the strict length separation clause (iii);
* a terminal vertex with the same intrinsic height cannot
  lexicographically precede the cut, by the same-height
  length monotonicity clause (ii).

This is a key invariant for a repaired Lemma 27 Q tree: it
ensures that its earlier-rank terminal markers are all on
the correct side of the retained last interior cut.
The subsequent identification of their ambient complete-T
frontier ranks is still an independent obligation.

These statements use the verified generic forward-order
properties, not the paper's false reverse-order monotonicity.
-/

namespace DualTree.ForwardCutTerminalOrder

/-- In the globally forward-lex skew convention, every
terminal vertex lies at or after the final branching cut
in the proposed auxiliary order. -/
theorem cut_forwardAux_before_terminal
    {b : Nat} (hb : 0 < b)
    (S : List (Node b))
    (cut leaf : Node b)
    (hfull : SkewTree.fullBeforeB SkewTree.forwardAuxB S cut = true)
    (hleaf : leaf ∈ S)
    (hleafTerminal : leaf ∉ SkewTree.interior S)
    (hneq : leaf ≠ cut) :
    ForwardAux cut leaf := by
  have hnil : SkewTree.immediateSuccs S leaf = [] :=
    StarredSignature.immediateSuccs_nil_of_not_interior
      S leaf hleaf hleafTerminal
  have hnot : ¬ (SkewTree.forwardAuxB leaf cut = true) :=
    StarredSignature.leaf_not_before_of_fullBefore
      hb S SkewTree.forwardAuxB cut leaf
      hfull hleaf hnil hneq
  rcases CanonicalForwardAuxIso.forwardAux_total cut leaf with h | h
  · exact h
  · have hh : SkewTree.forwardAuxB leaf cut = true := by
      simpa [SkewTree.forwardAuxB] using h
    exact False.elim (hnot hh)

/-- A terminal node of a forward-order skew support cannot
have smaller *intrinsic* height than the final branching
cut. This derives from clause (iii), not merely from the
ordering of ambient lengths. -/
theorem terminal_height_ge_cut
    {b : Nat} (hb : 0 < b)
    (S : List (Node b))
    (hIII : SkewTree.condIIIB S = true)
    (cut leaf : Node b)
    (hfull : SkewTree.fullBeforeB SkewTree.forwardAuxB S cut = true)
    (hcut : cut ∈ S)
    (hleaf : leaf ∈ S)
    (hleafTerminal : leaf ∉ SkewTree.interior S) :
    SkewTree.heightAt S cut ≤ SkewTree.heightAt S leaf := by
  by_contra hn
  have hlt : SkewTree.heightAt S leaf < SkewTree.heightAt S cut := by
    omega
  have hleAux : ForwardAux leaf cut :=
    ForwardOrderCompatibility.forwardAux_of_lower_height
      S hIII hleaf hcut hlt
  have hnil : SkewTree.immediateSuccs S leaf = [] :=
    StarredSignature.immediateSuccs_nil_of_not_interior
      S leaf hleaf hleafTerminal
  have hne : leaf ≠ cut := by
    intro heq
    subst leaf
    omega
  have hbefore : SkewTree.forwardAuxB leaf cut = true := by
    simpa [SkewTree.forwardAuxB] using hleAux
  exact (StarredSignature.leaf_not_before_of_fullBefore
    hb S SkewTree.forwardAuxB cut leaf
    hfull hleaf hnil hne) hbefore

/-- At exactly the cut's intrinsic height, a terminal support
node cannot be lexicographically earlier than the cut.
This is the second key separation property for replacing
terminal signature markers in a forward-order Q tree. -/
theorem terminal_not_lex_before_cut_at_same_height
    {b : Nat} (hb : 0 < b)
    (S : List (Node b))
    (hII : SkewTree.condIIB S = true)
    (cut leaf : Node b)
    (hfull : SkewTree.fullBeforeB SkewTree.forwardAuxB S cut = true)
    (hcut : cut ∈ SkewTree.interior S)
    (hleaf : leaf ∈ S)
    (hleafTerminal : leaf ∉ SkewTree.interior S)
    (heq : SkewTree.heightAt S cut = SkewTree.heightAt S leaf) :
    ¬ FinLexLE leaf cut := by
  intro hlex
  have hcutMem : cut ∈ S := by
    unfold SkewTree.interior at hcut
    exact (List.mem_filter.mp hcut).1
  have hne : leaf ≠ cut := by
    intro h
    subst leaf
    exact hleafTerminal hcut
  have hbefore : ForwardAux leaf cut :=
    ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      S hII hleaf hcutMem heq.symm hlex
  have hnil : SkewTree.immediateSuccs S leaf = [] :=
    StarredSignature.immediateSuccs_nil_of_not_interior
      S leaf hleaf hleafTerminal
  have hflag : SkewTree.forwardAuxB leaf cut = true := by
    simpa [SkewTree.forwardAuxB] using hbefore
  exact (StarredSignature.leaf_not_before_of_fullBefore
    hb S SkewTree.forwardAuxB cut leaf
    hfull hleaf hnil hne) hflag

end DualTree.ForwardCutTerminalOrder
