import DualTree.CanonicalForwardAux
import DualTree.PaperAuxAntisymm

/-!
# The full canonical isomorphism preserves and reflects forward auxiliary order

The printed Section 3.1 chooses the length-first *reverse*-lexicographic
tie-break; the page-8 claim that I_T preserves that order is false.
The corrected length-first *forward*-lexicographic comparison has two
useful features:

1. It is a total antisymmetric preorder on all finite nodes.
2. The canonical map I_T is injective and monotone for this order
   (CanonicalForwardAux.canonicalEmbedding_forward_mono_of_complete).

For a bijection between linear orders, monotonicity in one direction
plus injectivity and totality implies order reflection. Hence, with the
forward tie-break, the complete skew support's canonical map is an
actual order isomorphism, not merely an order homomorphism.

This theorem assumes a nonsingleton complete skew support, the case
needed for the substantial Ramsey arguments. The singleton convention
is independent of this specific order issue.
-/

namespace DualTree.CanonicalForwardAuxIso

/-- Reflexivity of the proposed repaired length-first auxiliary order. -/
theorem forwardAux_refl {b : Nat} (s : Node b) : ForwardAux s s :=
  Or.inr ⟨rfl, ForwardOrderCompatibility.finLexLE_of_prefix
    (isPrefix_refl s)⟩

/-- Comparability of the repaired auxiliary order. -/
theorem forwardAux_total {b : Nat} (s t : Node b) :
    ForwardAux s t ∨ ForwardAux t s := by
  rcases lt_trichotomy s.length t.length with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases finLexLE_total s t with hlex | hlex
    · exact Or.inl (Or.inr ⟨heq, hlex⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hlex⟩)
  · exact Or.inr (Or.inl hgt)

/-- Antisymmetry of forward auxiliary order, using the
checked finite-word lexicographic antisymmetry. -/
theorem forwardAux_antisymm {b : Nat}
    {s t : Node b} (hst : ForwardAux s t) (hts : ForwardAux t s) :
    s = t := by
  rcases hst with hlen | ⟨hlen, hlex⟩
  · rcases hts with hlen' | ⟨hlen', _⟩ <;> omega
  · rcases hts with hlen' | ⟨hlen', hlex'⟩
    · omega
    · exact PaperAuxAntisymm.finLexLE_antisymm s t hlex hlex'

/-- Under the forward-lex repair, the canonical embedding
reflects the auxiliary order as well as preserving it. -/
theorem canonicalEmbedding_forward_reflect {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (u v : BoundedNode b k)
    (himages :
      ForwardAux
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1) :
    ForwardAux u.1 v.1 := by
  let I := CompleteSupportAddresses.canonicalEmbedding T hcomplete
  rcases forwardAux_total u.1 v.1 with huv | hvu
  · exact huv
  · have hback : ForwardAux (I v).1 (I u).1 :=
      CanonicalForwardAux.canonicalEmbedding_forward_mono_of_complete
        T hcomplete hnonsingleton v u hvu
    have hEq : (I u).1 = (I v).1 :=
      forwardAux_antisymm himages hback
    have hSources : u = v :=
      (CanonicalSupportInjective.canonicalEmbedding_injective T hcomplete)
        (Subtype.ext hEq)
    subst v
    exact forwardAux_refl u.1

/-- The complete skew canonical embedding is an auxiliary
order isomorphism under the proposed forward-lex repair. -/
theorem canonicalEmbedding_forward_iff {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (u v : BoundedNode b k) :
    ForwardAux u.1 v.1 ↔
      ForwardAux
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
        (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 := by
  constructor
  · exact CanonicalForwardAux.canonicalEmbedding_forward_mono_of_complete
      T hcomplete hnonsingleton u v
  · exact canonicalEmbedding_forward_reflect
      T hcomplete hnonsingleton u v

end DualTree.CanonicalForwardAuxIso
