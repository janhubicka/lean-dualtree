import DualTree.ForwardQModelPrefixIso
import DualTree.ForwardSourceAddressPrefixIso

/-!
# Source address walks preserve and reflect outgoing child directions

Prefix reflection for the canonical direction walk of a genuinely
semi-complete skew source is already verified. For the *direction*
labels we need more: whenever u and v are valid rooted addresses,
the first letter after u on the path to v is the same as the first
ambient successor-cone direction of the realized source vertices.

The forward implication follows from an actual admissible tail
and the verified unique-successor first-direction theorem.
Conversely, prefix reflection gives an address suffix. If its first
direction were j≠i, the realized source descendant would lie in
two disjoint ambient first-direction cones from the same source
vertex; equal-length prefix uniqueness forces i=j.

This lemma works with stretched support edges, does not assume that
the actual source is a k-complete homogeneous tree, and does not
identify the published reverse-lex W_* starred input domain.
The next module will specialize it to ModelInterior(l) and A_l,
then compose with the checked source leaf/R/Q incidence theorem.
-/

namespace DualTree.ForwardSourceAddressChildCone

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceAddressPrefixIso

/-- If a whole concatenated word is admissible from root, its suffix
is admissible starting at the actual support vertex reached by the
prefix. No completeness or skew assumptions are needed. -/
theorem admissible_tail_of_append
    {b : Nat} (T : List (Node b)) :
    ∀ (root u v : Node b),
      CanonicalSupportWalk.Admissible T root (u ++ v) →
      CanonicalSupportWalk.Admissible T
        (CanonicalSupportWalk.walk T root u) v := by
  intro root u
  induction u generalizing root with
  | nil =>
      intro v hvalid
      simpa [CanonicalSupportWalk.walk] using hvalid
  | cons i tail ih =>
      intro v hvalid
      exact ih (CanonicalSupportWalk.next T root i) v hvalid.2

/-- Canonical admissible source direction walks preserve the FIRST
OUTGOING child cone at every rooted address. The addressed source
edge may skip ambient levels, but never change its direction. -/
theorem sourceAddress_childCone_mono
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c)
    (i : Fin b)
    (hcone : IsPrefix (u.1 ++ [i]) v.1) :
    IsPrefix ((realize c u).1 ++ [i]) (realize c v).1 := by
  obtain ⟨tail, htail⟩ := hcone
  have hv : v.1 = u.1 ++ (i :: tail) := by
    calc
      v.1 = (u.1 ++ [i]) ++ tail := htail
      _ = u.1 ++ (i :: tail) := by simp [List.append_assoc]
  have hvalid :
      CanonicalSupportWalk.Admissible c.source.tree
        (ForwardQRooted.sourceRoot c) (u.1 ++ (i :: tail)) := by
    simpa only [hv] using v.2
  have hbranch : SkewTree.uniqueBranchB c.source.tree
      (realize c u).1 i = true := by
    exact (admissible_tail_of_append c.source.tree
      (ForwardQRooted.sourceRoot c) u.1 (i :: tail) hvalid).1
  have hwalkv :
      (realize c v).1 =
        CanonicalSupportWalk.walk c.source.tree
          (realize c u).1 (i :: tail) := by
    change CanonicalSupportWalk.walk c.source.tree
      (ForwardQRooted.sourceRoot c) v.1 =
      CanonicalSupportWalk.walk c.source.tree
        (CanonicalSupportWalk.walk c.source.tree
          (ForwardQRooted.sourceRoot c) u.1) (i :: tail)
    rw [hv, CanonicalSupportWalk.walk_append]
  rw [hwalkv]
  exact CanonicalSupportWalk.walk_first_direction
    c.source.tree (realize c u).1 i tail hbranch

/-- The initial ambient direction of a realized source path
REFLECTS its unique first remaining canonical address letter.
Prefix preservation alone would not imply this statement:
the proof also uses the actual successor directions. -/
theorem sourceAddress_childCone_reflect
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c)
    (i : Fin b)
    (hcone : IsPrefix ((realize c u).1 ++ [i])
      (realize c v).1) :
    IsPrefix (u.1 ++ [i]) v.1 := by
  have hpre : IsPrefix (realize c u).1 (realize c v).1 :=
    isPrefix_trans ⟨[i], rfl⟩ hcone
  obtain ⟨tail, htail⟩ :=
    (sourceAddress_prefix_iff c u v).2 hpre
  cases tail with
  | nil =>
      have heq : v.1 = u.1 := by simpa using htail
      have heqVal : (realize c v).1 = (realize c u).1 := by
        change CanonicalSupportWalk.walk c.source.tree
          (ForwardQRooted.sourceRoot c) v.1 =
          CanonicalSupportWalk.walk c.source.tree
            (ForwardQRooted.sourceRoot c) u.1
        rw [heq]
      rw [heqVal] at hcone
      have hlen := prefix_length_le hcone
      simp only [List.length_append, List.length_singleton] at hlen
      omega
  | cons j rest =>
      have hj : IsPrefix (u.1 ++ [j]) v.1 :=
        ⟨rest, by simpa [List.append_assoc] using htail⟩
      have hconeJ :
          IsPrefix ((realize c u).1 ++ [j]) (realize c v).1 :=
        sourceAddress_childCone_mono c u v j hj
      have hbetween :
          IsPrefix ((realize c u).1 ++ [i])
            ((realize c u).1 ++ [j]) :=
        CutFrontier.prefix_of_prefix_length_le
          hcone hconeJ (by simp)
      have hwords :
          (realize c u).1 ++ [i] =
            (realize c u).1 ++ [j] :=
        CutPreservation.prefix_eq_of_length_eq hbetween (by simp)
      have hij : i = j := by
        have hdrop := congrArg
          (fun z : Node b => z.drop (realize c u).1.length) hwords
        have hsingle : [i] = [j] := by simpa using hdrop
        simpa using hsingle
      subst j
      exact ⟨rest, by simpa [List.append_assoc] using htail⟩

/-- Canonical source addresses preserve and reflect every genuine
first outgoing direction, for arbitrary admissible descendants. -/
theorem sourceAddress_childCone_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c) (i : Fin b) :
    IsPrefix (u.1 ++ [i]) v.1 ↔
      IsPrefix ((realize c u).1 ++ [i]) (realize c v).1 :=
  ⟨sourceAddress_childCone_mono c u v i,
    sourceAddress_childCone_reflect c u v i⟩

end DualTree.ForwardSourceAddressChildCone
