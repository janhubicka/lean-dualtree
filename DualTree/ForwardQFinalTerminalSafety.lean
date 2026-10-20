import DualTree.ForwardQFinalCoherentWordPreimage
import DualTree.ForwardQLiteralMarkerLeafEquiv
import DualTree.ForwardQFinalSafeAddressLookup

/-!
# Necessary safe-address condition on actual corrected Q terminals

The corrected forward Q tree has the old interior vertices and
literal projected D2 marker points, P_i(x.bulletPoint i).
The latter are ALWAYS inside the shortened safe projection domain.
This remains true even when the selected frontier can be found at a
node whose inverse local tail is too long.

Using the verified exact Q terminal/D2-index bijection, we prove
that every actual Q terminal has a safe address. Consequently any
target starred tree equal to a corrected Q tree has all its terminal
vertices in the safe projected image.

This is a NECESSARY condition for exact starred-object equality,
not a proof of surjectivity: a target terminal in the safe image may
still require a marked-point choice outside the mixed Ramsey span or
violate the corrected D2 starred order.
-/

namespace DualTree.ForwardQFinalTerminalSafety

open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The source-facing marked D2 projection is literally the same
support-valued P_i(z) as the corrected safe local address map. -/
theorem markedProjection_eq_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    markedProjection c x i =
      projected c ⟨i.1, x.bulletPoint i⟩ :=
  rfl

/-- Every genuine marked D2 point has the actual, unique safe
address consisting of its sorted frontier and original marked tail. -/
theorem markedProjection_safeAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c)) :
    ForwardQFinalSafeAddressLookup.safeAddress
      c (markedProjection c x i).1 =
        some (⟨i.1, x.bulletPoint i⟩ : LocalAddress c) := by
  rw [markedProjection_eq_projected]
  exact ForwardQFinalSafeAddressLookup.safeAddress_projected
    c ⟨i.1, x.bulletPoint i⟩

/-- EVERY terminal of the actual forward Q tree is a genuine
shortened-coordinate projection. It therefore has a safe address,
including the literal D2 tag of its unique marked point. -/
theorem Q_terminal_has_safe_address
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (leaf : ForwardQLiteralMarkerLeafEquiv.QLeaf c x) :
    ∃ i : MixedProduct.BulletIndex (kind c),
      ForwardQFinalSafeAddressLookup.safeAddress c leaf.1 =
        some (⟨i.1, x.bulletPoint i⟩ : LocalAddress c) := by
  obtain ⟨i, hi⟩ :=
    ForwardQLiteralMarkerLeafEquiv.Q_leaf_has_bullet hb c x leaf
  refine ⟨i, ?_⟩
  rw [← hi]
  exact markedProjection_safeAddress c x i

/-- A vertex in a corrected Q tree whose actual local projection
decoder returns none must be an OLD INTERIOR vertex, not a terminal.
This is stronger than merely having a selected frontier. -/
theorem Q_vertex_without_safe_address_is_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (t : Node b)
    (ht : t ∈ (nodes c x).toList)
    (hnone : ForwardQFinalSafeAddressLookup.safeAddress c t = none) :
    t ∈ SkewTree.interior (nodes c x).toList := by
  by_contra hterminal
  obtain ⟨i, hi⟩ := Q_terminal_has_safe_address
    hb c x (⟨t, ht, hterminal⟩ :
      ForwardQLiteralMarkerLeafEquiv.QLeaf c x)
  rw [hnone] at hi
  cases hi

/-- Exact equality of a requested starred output tree with the
corrected Q support forces EVERY output terminal to be a genuine
safe projected D2 point. This is an independent geometric
obligation not implied merely by equality of word functions. -/
theorem exact_Q_tree_forces_output_terminals_safe
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hTree : O.tree = (nodes c x).toList)
    (t : Node b)
    (ht : t ∈ O.tree)
    (hterminal : t ∉ SkewTree.interior O.tree) :
    ∃ i : MixedProduct.BulletIndex (kind c),
      ForwardQFinalSafeAddressLookup.safeAddress c t =
        some (⟨i.1, x.bulletPoint i⟩ : LocalAddress c) := by
  have htQ : t ∈ (nodes c x).toList := by
    rw [← hTree]
    exact ht
  have hnQ : t ∉ SkewTree.interior (nodes c x).toList := by
    rw [← hTree]
    exact hterminal
  exact Q_terminal_has_safe_address hb c x
    (⟨t, htQ, hnQ⟩ :
      ForwardQLiteralMarkerLeafEquiv.QLeaf c x)

end DualTree.ForwardQFinalTerminalSafety
