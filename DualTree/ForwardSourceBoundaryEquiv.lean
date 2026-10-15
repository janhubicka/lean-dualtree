import DualTree.ForwardSourceBoundaryLeaves
import DualTree.ForwardSourceLeafMarkerEquiv

/-!
# Canonical equivalence of model boundary A_l and literal marker R

The corrected semi-complete source interior has exactly the first
l homogeneous forward-heap addresses. Every external model
boundary address a=p++[i] is admissible and realizes a unique
original source terminal; the previous module proves injectivity.

Here we finish SURJECTIVITY: every genuine source terminal t has
a nonempty canonical admissible direction address a. Writing
a=p++[i], its prefix p is admissible, and the final support
successor makes the realized p vertex interior. Thus p is a
first-l model address, while the terminal address a is outside
that interior. Consequently a belongs to the model boundary.

The resulting canonical equivalence
    A_l ≃ SourceLeaf(S)
composes with the separately verified actual prefix-incidence
equivalence
    SourceLeaf(S) ≃ R.
This completes the set-level canonical A_l ↔ literal R
correspondence for the CORRECTED forward source; preserving
canonical point positions across all Q mixed inputs and the
word-colouring Ramsey refinement remain additional obligations.
-/

namespace DualTree.ForwardSourceBoundaryEquiv

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceAddressOrder
open ForwardSourceInteriorFirstL
open ForwardSourceBoundaryLeaves
open ForwardSourceLeafMarkerEquiv
open ForwardModelBoundaryHeap

/-- A valid final support step strictly extends its realized
prefix vertex, even when ambient support edges skip levels. -/
theorem admissible_last_strictPrefix
    {b : Nat} (T : List (Node b))
    (root p : Node b) (i : Fin b)
    (hvalid :
      CanonicalSupportWalk.Admissible T root (p ++ [i])) :
    IsStrictPrefix
      (CanonicalSupportWalk.walk T root p)
      (CanonicalSupportWalk.walk T root (p ++ [i])) := by
  have hbranch :=
    ((admissible_append_singleton_iff T root p i).1 hvalid).2
  have hstep :=
    (CanonicalSupportWalk.next_unique T
      (CanonicalSupportWalk.walk T root p) i hbranch).1
  have hstrict :
      IsStrictPrefix
        (CanonicalSupportWalk.walk T root p)
        (CanonicalSupportWalk.next T
          (CanonicalSupportWalk.walk T root p) i) :=
    ((SkewBranchGeometry.immediateSuccB_iff T
      (CanonicalSupportWalk.walk T root p)
      (CanonicalSupportWalk.next T
        (CanonicalSupportWalk.walk T root p) i)).1 hstep).2.1
  rw [CanonicalSupportWalk.walk_append]
  simpa [CanonicalSupportWalk.walk] using hstrict

/-- EVERY original source leaf comes from an external child
of the first-l canonical model interior. The proof follows
its own last admissible direction, not an enumeration. -/
theorem boundaryRealize_surjective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    Function.Surjective (boundaryRealize hb c) := by
  intro t
  obtain ⟨word, hvalid, hwalk, _⟩ :=
    source_has_address c t.1 t.2.1
  have hnonempty : word ≠ [] := by
    intro hnil
    have hroot : ForwardQRooted.sourceRoot c = t.1 := by
      simpa [hnil, CanonicalSupportWalk.walk] using hwalk
    have htInterior :
        t.1 ∈ SkewTree.interior c.source.tree := by
      rw [← hroot]
      exact ForwardQRooted.sourceRoot_interior c
    exact t.2.2 htInterior
  cases hrev : word.reverse with
  | nil =>
      have hnil : word = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      exact (hnonempty hnil).elim
  | cons i revParent =>
      let p : Node b := revParent.reverse
      have hrepr : word = p ++ [i] := by
        have h := congrArg List.reverse hrev
        simpa [p] using h
      have hvalidChild :
          CanonicalSupportWalk.Admissible c.source.tree
            (ForwardQRooted.sourceRoot c) (p ++ [i]) := by
        simpa only [hrepr] using hvalid
      have hsplit :=
        (admissible_append_singleton_iff c.source.tree
          (ForwardQRooted.sourceRoot c) p i).1 hvalidChild
      let parent : SourceAddress c := ⟨p, hsplit.1⟩
      let child : SourceAddress c := ⟨p ++ [i], hvalidChild⟩
      have hstrict :
          IsStrictPrefix (realize c parent).1
            (realize c child).1 :=
        admissible_last_strictPrefix c.source.tree
          (ForwardQRooted.sourceRoot c) p i hvalidChild
      have hparentInterior :
          (realize c parent).1 ∈
            SkewTree.interior c.source.tree :=
        SignatureInteriorPersistence.interior_of_strict_descendant
          c.source.tree (realize c parent).1
          (realize c child).1
          (realize c parent).2 (realize c child).2
          hstrict
      have hparentModel : ModelInterior l p :=
        (modelInterior_iff_sourceInterior_address hb c p).2
          ⟨parent, rfl, hparentInterior⟩
      have houtside : ¬ ModelInterior l word := by
        intro hin
        obtain ⟨u, hu, huInterior⟩ :=
          (modelInterior_iff_sourceInterior_address hb c word).1 hin
        have huEq : u =
            (⟨word, hvalid⟩ : SourceAddress c) :=
          Subtype.ext hu
        have hinterior :
            (realize c (⟨word, hvalid⟩ : SourceAddress c)).1 ∈
              SkewTree.interior c.source.tree := by
          rw [← huEq]
          exact huInterior
        have htInterior :
            t.1 ∈ SkewTree.interior c.source.tree := by
          change (CanonicalSupportWalk.walk c.source.tree
            (ForwardQRooted.sourceRoot c) word) ∈
              SkewTree.interior c.source.tree at hinterior
          rw [hwalk] at hinterior
          exact hinterior
        exact t.2.2 htInterior
      have hboundary : ModelBoundary l word :=
        ⟨houtside, ⟨p, i, hparentModel, hrepr⟩⟩
      refine ⟨⟨word, hboundary⟩, ?_⟩
      apply Subtype.ext
      change (CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) word) = t.1
      exact hwalk

/-- The entire external model boundary is in canonical
bijection with the original source terminal vertices. -/
noncomputable def boundarySourceLeafEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    {a : Node b // ModelBoundary l a} ≃ SourceLeaf c :=
  Equiv.ofBijective (boundaryRealize hb c)
    ⟨boundaryRealize_injective hb c,
      boundaryRealize_surjective hb c⟩

/-- The canonical Definition 24 model boundary A_l corresponds
to precisely the literal corrected signature markers R,
through the ACTUAL source terminal vertices. This is the
geometry of the repaired forward source, not the printed
reverse-lex convention. -/
noncomputable def modelBoundaryMarkerEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    {a : Node b // ModelBoundary l a} ≃
      ForwardSortedMixedProduct.Marker
        c.source c.cut c.hout :=
  (boundarySourceLeafEquiv hb c).trans
    (ForwardSourceLeafMarkerEquiv.sourceLeafMarkerEquiv hb c)

end DualTree.ForwardSourceBoundaryEquiv
