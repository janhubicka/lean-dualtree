import DualTree.CompleteSupportAddresses

/-!
# Injectivity of the canonical support walk

The rooted walk is prefix-preserving even if some directions are missing.
On paths which are actually admissible, it is also injective: the first
source direction is encoded in the ambient cone of its support successor,
so distinct directions cannot coalesce. Equal first directions reduce
to the same assertion for the corresponding shorter tail.

The complete-skew bounded-address theorem proves admissibility for all
addresses in b^{<k}, hence the corresponding canonical map is injective.
Surjectivity onto the whole support remains a separate proof obligation.
-/

namespace DualTree.CanonicalSupportInjective

/-- No two distinct admissible source addresses can have the same
endpoint of the canonical support traversal. -/
theorem walk_injective_of_admissible {b : Nat}
    (T : List (Node b)) :
    ∀ (u s v : Node b),
      CanonicalSupportWalk.Admissible T s u →
      CanonicalSupportWalk.Admissible T s v →
      CanonicalSupportWalk.walk T s u =
        CanonicalSupportWalk.walk T s v →
      u = v := by
  intro u
  induction u with
  | nil =>
      intro s v hu hv heq
      cases v with
      | nil => rfl
      | cons j tail =>
          have hcone : IsPrefix (s ++ [j]) s := by
            have hp := CanonicalSupportWalk.walk_first_direction
              T s j tail hv.1
            change s = CanonicalSupportWalk.walk T s (j :: tail) at heq
            rw [← heq] at hp
            exact hp
          have hlen := prefix_length_le hcone
          simp only [List.length_append, List.length_singleton] at hlen
          omega
  | cons i us ih =>
      intro s v hu hv heq
      cases v with
      | nil =>
          have hcone : IsPrefix (s ++ [i]) s := by
            have hp := CanonicalSupportWalk.walk_first_direction
              T s i us hu.1
            change CanonicalSupportWalk.walk T s (i :: us) = s at heq
            rw [heq] at hp
            exact hp
          have hlen := prefix_length_le hcone
          simp only [List.length_append, List.length_singleton] at hlen
          omega
      | cons j vs =>
          have hi := CanonicalSupportWalk.walk_first_direction
            T s i us hu.1
          have hj := CanonicalSupportWalk.walk_first_direction
            T s j vs hv.1
          have hi' : IsPrefix (s ++ [i])
              (CanonicalSupportWalk.walk T s (j :: vs)) := by
            rw [← heq]
            exact hi
          have hp : IsPrefix (s ++ [i]) (s ++ [j]) :=
            CutFrontier.prefix_of_prefix_length_le hi' hj (by simp)
          have hwords : s ++ [i] = s ++ [j] :=
            CutPreservation.prefix_eq_of_length_eq hp (by simp)
          have hij : i = j := by
            have hsingle : [i] = [j] := by
              have hdrop :=
                congrArg (fun x : Node b => x.drop s.length) hwords
              simpa using hdrop
            simpa using hsingle
          subst j
          have htail :
              CanonicalSupportWalk.walk T (CanonicalSupportWalk.next T s i) us =
              CanonicalSupportWalk.walk T (CanonicalSupportWalk.next T s i) vs := by
            simpa only [CanonicalSupportWalk.walk] using heq
          have hsame : us = vs :=
            ih (CanonicalSupportWalk.next T s i) vs hu.2 hv.2 htail
          simp [hsame]

/-- The canonical map from b^{<k} to a complete skew support is injective. -/
theorem canonicalEmbedding_injective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    Function.Injective
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete) := by
  intro u v heq
  have hu : CanonicalSupportWalk.Admissible T
      (CompleteSupportRoot.rootOf T hcomplete) u.1 :=
    (CompleteSupportAddresses.canonical_bounded_address
      T hcomplete u.1 u.2).1
  have hv : CanonicalSupportWalk.Admissible T
      (CompleteSupportRoot.rootOf T hcomplete) v.1 :=
    (CompleteSupportAddresses.canonical_bounded_address
      T hcomplete v.1 v.2).1
  have himages :
      CompleteSupportRoot.canonicalWalk T hcomplete u.1 =
        CompleteSupportRoot.canonicalWalk T hcomplete v.1 :=
    congrArg Subtype.val heq
  have haddresses : u.1 = v.1 :=
    walk_injective_of_admissible T u.1
      (CompleteSupportRoot.rootOf T hcomplete) v.1 hu hv himages
  exact Subtype.ext haddresses

end DualTree.CanonicalSupportInjective
