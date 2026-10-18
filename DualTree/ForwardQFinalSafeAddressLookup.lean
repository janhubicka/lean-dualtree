import DualTree.ForwardQFinalLocalSymbolTransport
import DualTree.ForwardQFinalSupportCut

/-!
# Recover a safe local cone address at a genuine complete-T node

The original ambient f has one root variable at every T node.
Only SOME of those T nodes are images P_i(z) of shortened common
frontier-tail addresses. The later full f' substitution must read
the mixed-product local word precisely in those safe cones, without
inventing a local address for the remaining original roots.

The jointly injective corrected projection gives a UNIQUE tagged
safe local address whenever an image exists. This file packages the
partial inverse in an Option, proves exact left/right correctness,
and proves that every retained pre-cut root returns none.

This is a partial inverse of the actual corrected P_i, not the
printed reverse-lex starred W_* projection.
-/

namespace DualTree.ForwardQFinalSafeAddressLookup

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalSupportCut

/-- The one genuine tagged shortened local address of an original
complete-T vertex if it is in the safe projection image; none otherwise.
Global projection injectivity removes any dependence on which
existence witness Classical.choose picks. -/
noncomputable def safeAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b) : Option (LocalAddress c) := by
  classical
  exact if h : ∃ u : LocalAddress c, (projected c u).1 = t then
    some (Classical.choose h)
  else none

/-- Whenever the partial decoder returns a local address, its
actual projected complete-T node is exactly the requested node. -/
theorem safeAddress_spec
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (u : LocalAddress c)
    (h : safeAddress c t = some u) :
    (projected c u).1 = t := by
  classical
  unfold safeAddress at h
  split_ifs at h with hex
  · have heq : Classical.choose hex = u := Option.some.inj h
    simpa [heq] using (Classical.choose_spec hex)

/-- Decoding a genuine projected safe local address returns
that exact address, including the true sorted frontier coordinate.
This is a global statement across ALL frontier indices. -/
theorem safeAddress_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : LocalAddress c) :
    safeAddress c (projected c u).1 = some u := by
  classical
  unfold safeAddress
  split_ifs with hex
  · have heq : Classical.choose hex = u :=
      (projected_injective c)
        (Subtype.ext (Classical.choose_spec hex))
    simp [heq]
  · exact False.elim (hex ⟨u,rfl⟩)

/-- The partial decoder is defined precisely on the image
of the jointly injective safe cone projection. -/
theorem safeAddress_eq_some_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (u : LocalAddress c) :
    safeAddress c t = some u ↔
      (projected c u).1 = t := by
  constructor
  · exact safeAddress_spec c t u
  · intro heq
    rw [← heq]
    exact safeAddress_projected c u

/-- No safe cone address can decode to an old retained root:
all actual projections lie outside the inclusive forward cut. -/
theorem safeAddress_retained_none
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b)
    (ht : t ∈ retained c) :
    safeAddress c t = none := by
  classical
  unfold safeAddress
  split_ifs with hex
  · obtain ⟨u,hu⟩ := hex
    have hbefore : ForwardAux t c.cut :=
      (Finset.mem_filter.mp ht).2
    have hprojectedBefore : ForwardAux (projected c u).1 c.cut := by
      rw [hu]
      exact hbefore
    exact False.elim (projected_outside_cut c u hprojectedBefore)
  · rfl

end DualTree.ForwardQFinalSafeAddressLookup
