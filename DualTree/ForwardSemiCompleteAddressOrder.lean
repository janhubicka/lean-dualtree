import DualTree.ForwardSemiCompleteAddresses
import DualTree.CanonicalForwardAux
import DualTree.CanonicalForwardAuxIso
import DualTree.ForwardOrderCompatibility

/-!
# Forward order of arbitrary semi-complete canonical addresses

The intrinsic address realization preserves and reflects the corrected
forward auxiliary order. The support need not come from a Q frame.
Skew clauses (ii) and (iii), together with directional lexicographic
monotonicity and address length = intrinsic height, give preservation.
Injectivity and totality then give reflection.

Singleton supports are covered directly rather than excluded through
a positive-interior assumption. This includes Definition 24's l=0 case.
-/

namespace DualTree.ForwardSemiCompleteAddressOrder

open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteAddresses

/-- The numeric skew order clauses also hold in the separately
admitted singleton case of the skew-tree definition. -/
theorem numeric_order_clauses
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    SkewTree.condIIB U.tree = true ∧
      SkewTree.condIIIB U.tree = true := by
  by_cases hsingle : U.tree.length = 1
  · obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hsingle
    simp [SkewTree.condIIB, SkewTree.condIIIB, hr]
  · have hparts := U.semi_complete
    simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
    have hskew := hparts.1
    simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
    have hrest := hskew.2
    simp [hsingle, Bool.and_eq_true] at hrest
    exact ⟨hrest.1.1.2, hrest.1.2⟩

/-- Forward auxiliary comparison of admissible addresses is
preserved, even when support edges contain skipped ambient levels. -/
theorem forwardAux_realize_mono
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a d : Address U) (had : ForwardAux a.1 d.1) :
    ForwardAux (realize U a).1 (realize U d).1 := by
  obtain ⟨hII, hIII⟩ := numeric_order_clauses U
  rcases had with hshort | ⟨heq, hlex⟩
  · have hrank : SkewTree.heightAt U.tree (realize U a).1 <
        SkewTree.heightAt U.tree (realize U d).1 := by
      rw [height_realize_eq_length U a, height_realize_eq_length U d]
      exact hshort
    exact ForwardOrderCompatibility.forwardAux_of_lower_height
      U.tree hIII (realize U a).2 (realize U d).2 hrank
  · have himageLex : FinLexLE (realize U a).1 (realize U d).1 :=
      CanonicalForwardAux.walk_lex_of_admissible
        U.tree a.1 (starredRootAll U) d.1 a.2 d.2 hlex
    have hequal : SkewTree.heightAt U.tree (realize U a).1 =
        SkewTree.heightAt U.tree (realize U d).1 := by
      rw [height_realize_eq_length U a, height_realize_eq_length U d]
      exact heq
    exact ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      U.tree hII (realize U a).2 (realize U d).2 hequal himageLex

/-- The canonical admissible address bijection is an order
isomorphism for the corrected forward auxiliary order. -/
theorem forwardAux_realize_iff
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a d : Address U) :
    ForwardAux a.1 d.1 ↔ ForwardAux (realize U a).1 (realize U d).1 := by
  constructor
  · exact forwardAux_realize_mono U a d
  · intro himage
    rcases CanonicalForwardAuxIso.forwardAux_total a.1 d.1 with had | hda
    · exact had
    · have hback := forwardAux_realize_mono U d a hda
      have heqImage : (realize U a).1 = (realize U d).1 :=
        CanonicalForwardAuxIso.forwardAux_antisymm himage hback
      have heq : a = d := realize_injective U (Subtype.ext heqImage)
      subst d
      exact CanonicalForwardAuxIso.forwardAux_refl a.1

/-- The canonical address map preserves and reflects lexicographic order. -/
theorem lex_realize_iff
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a d : Address U) :
    FinLexLE a.1 d.1 ↔ FinLexLE (realize U a).1 (realize U d).1 := by
  have hmono : ∀ u v : Address U, FinLexLE u.1 v.1 →
      FinLexLE (realize U u).1 (realize U v).1 := by
    intro u v huv
    exact CanonicalForwardAux.walk_lex_of_admissible
      U.tree u.1 (starredRootAll U) v.1 u.2 v.2 huv
  constructor
  · exact hmono a d
  · intro himage
    rcases finLexLE_total a.1 d.1 with had | hda
    · exact had
    · have heqImage : (realize U a).1 = (realize U d).1 :=
        PaperAuxAntisymm.finLexLE_antisymm _ _ himage (hmono d a hda)
      have heq : a = d := realize_injective U (Subtype.ext heqImage)
      subst d
      rcases finLexLE_total a.1 a.1 with h | h <;> exact h

/-- Ambient prefix comparison of realized vertices reflects the
prefix comparison of their addresses: reach the larger vertex from
the smaller one and use injectivity of the concatenated walk. -/
theorem prefix_realize_iff
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a d : Address U) :
    IsPrefix a.1 d.1 ↔ IsPrefix (realize U a).1 (realize U d).1 := by
  constructor
  · intro had
    exact CanonicalSupportWalk.walk_prefix U.tree (starredRootAll U) had
  · intro himage
    obtain ⟨tail, htailAdmissible, htailWalk⟩ :=
      walk_address_of_prefix U (realize U a).1 (realize U d).1
        (realize U a).2 (realize U d).2 himage
    have hconcat : CanonicalSupportWalk.Admissible U.tree
        (starredRootAll U) (a.1 ++ tail) :=
      ForwardSourceHeapInitial.admissible_append U.tree a.1
        (starredRootAll U) tail a.2 htailAdmissible
    have hwalkEq : CanonicalSupportWalk.walk U.tree
        (starredRootAll U) (a.1 ++ tail) =
        CanonicalSupportWalk.walk U.tree (starredRootAll U) d.1 := by
      rw [CanonicalSupportWalk.walk_append]
      exact htailWalk
    have had : a.1 ++ tail = d.1 :=
      CanonicalSupportInjective.walk_injective_of_admissible
        U.tree (a.1 ++ tail) (starredRootAll U) d.1 hconcat d.2 hwalkEq
    exact ⟨tail, had.symm⟩

end DualTree.ForwardSemiCompleteAddressOrder
