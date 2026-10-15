import DualTree.ForwardSourceAddressOrder
import DualTree.ForwardModelHeapSurjective

/-!
# All homogeneous heap addresses up to the source cut are admissible

The previous theorem identified the source's interior directions as
an initial segment among already-admissible source addresses.
To obtain the original Definition 24 model boundary A_l, we must
rule out missing homogeneous addresses before the last cut.

For positive branching b, use strong induction on the arithmetic
b-ary heap index of an arbitrary direction sequence a. If a has
index n>0, then a=p++[i] for an address p of strictly smaller
heap index. If n is no later than the source's last interior cut
address, induction makes p admissible. The earlier forward-order
equivalence then makes its realized source vertex INTERIOR. Genuine
source semi-completeness supplies exactly the immediate successor
in direction i. Appending that direction preserves admissibility.

This establishes the exact full forward-heap initial segment on
which the source interior is realised. It does not yet establish
that its endpoint index is l-1, or that the external boundary
A_l is identified with source leaves and literal markers R.
-/

namespace DualTree.ForwardSourceHeapInitial

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceAddressOrder
open ForwardModelBoundaryHeap

/-- Concatenating a valid directional prefix and a valid
continuation remains a valid support walk. This is a generic
lemma independent of the source or any skew condition. -/
theorem admissible_append
    {b : Nat} (T : List (Node b)) :
    ∀ (p root tail : Node b),
      CanonicalSupportWalk.Admissible T root p →
      CanonicalSupportWalk.Admissible T
        (CanonicalSupportWalk.walk T root p) tail →
      CanonicalSupportWalk.Admissible T root (p ++ tail) := by
  intro p
  induction p with
  | nil =>
      intro root tail _ htail
      simpa [CanonicalSupportWalk.Admissible,
        CanonicalSupportWalk.walk] using htail
  | cons i p ih =>
      intro root tail hvalid htail
      rcases hvalid with ⟨hfirst, hrest⟩
      change SkewTree.uniqueBranchB T root i = true ∧
        CanonicalSupportWalk.Admissible T
          (CanonicalSupportWalk.next T root i) (p ++ tail)
      refine ⟨hfirst, ?_⟩
      apply ih (CanonicalSupportWalk.next T root i)
        tail hrest
      simpa [CanonicalSupportWalk.walk] using htail

/-- Every full homogeneous-tree direction word whose b-ary
heap index is at most the index of the last source interior
cut is genuinely admissible in the source. No missing heap
indices are possible before that cut. -/
theorem heap_le_cut_admissible
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : Node b)
    (hle : heapIndex a ≤ heapIndex (cutAddress c).1) :
    CanonicalSupportWalk.Admissible c.source.tree
      (ForwardQRooted.sourceRoot c) a := by
  let N := heapIndex (cutAddress c).1
  have hmain :
      ∀ q : Nat, q ≤ N →
        ∀ a : Node b, heapIndex a = q →
          CanonicalSupportWalk.Admissible c.source.tree
            (ForwardQRooted.sourceRoot c) a := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hq a ha
        cases hrev : a.reverse with
        | nil =>
            have haNil : a = [] := by
              have h := congrArg List.reverse hrev
              simpa using h
            simp [haNil, CanonicalSupportWalk.Admissible]
        | cons i revParent =>
            let p : Node b := revParent.reverse
            have haRep : a = p ++ [i] := by
              have h := congrArg List.reverse hrev
              simpa [p] using h
            have hpSmaller : heapIndex p < q := by
              have hlower := heapIndex_lt_child hb p i
              rw [haRep] at ha
              omega
            have hple : heapIndex p ≤ N := by omega
            have hpValid :
                CanonicalSupportWalk.Admissible c.source.tree
                  (ForwardQRooted.sourceRoot c) p :=
              ih (heapIndex p) hpSmaller hple p rfl
            let parent : SourceAddress c := ⟨p, hpValid⟩
            have hparentInitial :
                ForwardAux parent.1 (cutAddress c).1 :=
              (ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
                hb p (cutAddress c).1).2 (by
                  exact hple)
            have hparentInterior :
                (realize c parent).1 ∈
                  SkewTree.interior c.source.tree :=
              (address_interior_iff_forward_le_cut hb c parent).2
                hparentInitial
            have hbranch : SkewTree.uniqueBranchB c.source.tree
                (CanonicalSupportWalk.walk c.source.tree
                  (ForwardQRooted.sourceRoot c) p) i = true :=
              ForwardQAllDirections.source_full_directions
                c (realize c parent).1 hparentInterior i
            rw [haRep]
            exact admissible_append c.source.tree p
              (ForwardQRooted.sourceRoot c) [i]
              hpValid ⟨hbranch, trivial⟩
  exact hmain (heapIndex a) hle a rfl

/-- Every homogeneous address in the exact arithmetic
initial segment is not only admissible but represents an
original source interior vertex. -/
theorem heap_le_cut_realizes_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : Node b)
    (hle : heapIndex a ≤ heapIndex (cutAddress c).1) :
    ∃ u : SourceAddress c,
      u.1 = a ∧
      (realize c u).1 ∈ SkewTree.interior c.source.tree := by
  let u : SourceAddress c :=
    ⟨a, heap_le_cut_admissible hb c a hle⟩
  refine ⟨u, rfl, ?_⟩
  exact (address_interior_iff_forward_le_cut hb c u).2
    ((ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
      hb a (cutAddress c).1).2 hle)

/-- No interior source address has a heap index past the
last canonical cut address: this is the converse
direction of the full initial-segment identification. -/
theorem interior_address_heap_le_cut
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (u : SourceAddress c)
    (hint : (realize c u).1 ∈
      SkewTree.interior c.source.tree) :
    heapIndex u.1 ≤ heapIndex (cutAddress c).1 :=
  (ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
    hb u.1 (cutAddress c).1).1
    ((address_interior_iff_forward_le_cut hb c u).1 hint)

/-- The model heap initial interval ending at the source cut
is EXACTLY the realized source interior, including both
admissibility and the correct intrinsic tree predicate.
The index is not yet identified arithmetically with l-1. -/
theorem heap_le_cut_iff_source_interior_address
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : Node b) :
    heapIndex a ≤ heapIndex (cutAddress c).1 ↔
      ∃ u : SourceAddress c,
        u.1 = a ∧
        (realize c u).1 ∈
          SkewTree.interior c.source.tree := by
  constructor
  · exact heap_le_cut_realizes_interior hb c a
  · rintro ⟨u, hu, hint⟩
    rw [← hu]
    exact interior_address_heap_le_cut hb c u hint

end DualTree.ForwardSourceHeapInitial
