import DualTree.ForwardOrderCompatibility

/-!
# The canonical complete-skew embedding respects repaired forward order

The original source asserts that its canonical map I_T preserves
the length-first, *reverse*-lex auxiliary order. A binary
counterexample shows this is false.

For the length-first *forward*-lex order there is a structural
reason for preservation. The canonical support walk follows
the same ambient successor direction as its source address.
Consequently it preserves ordinary forward lexicographic
order for admissible paths, even when successive support
edges are stretched. The intrinsic rank of I_T(u) equals
|u|. Conditions (ii) and (iii) of the skew definition then
provide precisely the ambient-length comparisons required to
promote lex preservation to forward auxiliary preservation.

We prove that assertion for any nonsingleton complete skew
support in the source's original executable presentation.
This is a potential localized repair of the *canonical-order
claim* on page 8, not yet a complete proof of the modified
Lemma 27 or the remaining Ramsey induction.
-/

namespace DualTree.CanonicalForwardAux

/-- Lexicographic monotonicity of the rooted support walk on
any two admissible finite paths. The starting support node
can be arbitrary, and the paths need not have the same length. -/
theorem walk_lex_of_admissible {b : Nat}
    (T : List (Node b)) :
    ∀ (u s v : Node b),
      CanonicalSupportWalk.Admissible T s u →
      CanonicalSupportWalk.Admissible T s v →
      FinLexLE u v →
      FinLexLE (CanonicalSupportWalk.walk T s u)
        (CanonicalSupportWalk.walk T s v) := by
  intro u
  induction u with
  | nil =>
      intro s v _ _ _
      change FinLexLE s (CanonicalSupportWalk.walk T s v)
      exact ForwardOrderCompatibility.finLexLE_of_prefix
        (CanonicalSupportWalk.walk_root_prefix T s v)
  | cons i us ih =>
      intro s v hu hv hlex
      cases v with
      | nil =>
          simp [FinLexLE, finLexLEB] at hlex
      | cons j vs =>
          by_cases hij : i = j
          · subst j
            have htail : FinLexLE us vs := by
              simpa [FinLexLE, finLexLEB] using hlex
            change FinLexLE
              (CanonicalSupportWalk.walk T
                (CanonicalSupportWalk.next T s i) us)
              (CanonicalSupportWalk.walk T
                (CanonicalSupportWalk.next T s i) vs)
            exact ih (CanonicalSupportWalk.next T s i)
              vs hu.2 hv.2 htail
          · have hlt : i < j := by
              have htest := hlex
              simp [FinLexLE, finLexLEB, hij] at htest
              exact htest
            exact ForwardOrderCompatibility.finLexLE_of_ordered_cones
              s
              (CanonicalSupportWalk.walk T s (i :: us))
              (CanonicalSupportWalk.walk T s (j :: vs))
              i j hlt
              (CanonicalSupportWalk.walk_first_direction
                T s i us hu.1)
              (CanonicalSupportWalk.walk_first_direction
                T s j vs hv.1)

/-- The canonical embedding of the full b-ary address tree
into a complete skew support preserves ordinary (forward)
lexicographic order between all bounded source addresses. -/
theorem canonicalEmbedding_lex_mono {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u v : BoundedNode b k)
    (hlex : FinLexLE u.1 v.1) :
    FinLexLE
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 := by
  let root := CompleteSupportRoot.rootOf T hcomplete
  have hu : CanonicalSupportWalk.Admissible T root u.1 :=
    (CompleteSupportAddresses.canonical_bounded_address
      T hcomplete u.1 u.2).1
  have hv : CanonicalSupportWalk.Admissible T root v.1 :=
    (CompleteSupportAddresses.canonical_bounded_address
      T hcomplete v.1 v.2).1
  change FinLexLE (CanonicalSupportWalk.walk T root u.1)
    (CanonicalSupportWalk.walk T root v.1)
  exact walk_lex_of_admissible T u.1 root v.1 hu hv hlex

/-- If T satisfies the two numerical skew-order axioms,
the canonical map preserves the length-first forward
auxiliary order, whether or not one has yet established
T's condition (iv) for that auxiliary convention. -/
theorem canonicalEmbedding_forward_mono_of_conditions {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hII : SkewTree.condIIB T = true)
    (hIII : SkewTree.condIIIB T = true)
    (u v : BoundedNode b k)
    (hforward : ForwardAux u.1 v.1) :
    ForwardAux
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 := by
  let I := CompleteSupportAddresses.canonicalEmbedding T hcomplete
  rcases hforward with hlen | ⟨heq, hlex⟩
  · have hrank : SkewTree.heightAt T (I u).1 <
        SkewTree.heightAt T (I v).1 := by
      simpa only [I,
        CompleteSupportAddresses.canonicalEmbedding_height] using hlen
    exact ForwardOrderCompatibility.forwardAux_of_lower_height
      T hIII (I u).2 (I v).2 hrank
  · have htargetLex : FinLexLE (I u).1 (I v).1 :=
      canonicalEmbedding_lex_mono T hcomplete u v hlex
    have hrank : SkewTree.heightAt T (I u).1 =
        SkewTree.heightAt T (I v).1 := by
      simpa only [I,
        CompleteSupportAddresses.canonicalEmbedding_height] using heq
    exact ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      T hII (I u).2 (I v).2 hrank htargetLex

/-- In particular, any nonsingleton complete skew support
satisfies the condition needed for forward-auxiliary order
preservation; no additional axiom is required. -/
theorem canonicalEmbedding_forward_mono_of_complete {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hnonsingleton : T.length ≠ 1)
    (u v : BoundedNode b k)
    (hforward : ForwardAux u.1 v.1) :
    ForwardAux
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u).1
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete v).1 := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hrest := hskew.2
  simp [hnonsingleton, Bool.and_eq_true] at hrest
  have hII : SkewTree.condIIB T = true := hrest.1.1.2
  have hIII : SkewTree.condIIIB T = true := hrest.1.2
  exact canonicalEmbedding_forward_mono_of_conditions T
    hcomplete hII hIII u v hforward

end DualTree.CanonicalForwardAux
