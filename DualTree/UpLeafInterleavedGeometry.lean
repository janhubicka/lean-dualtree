import DualTree.UpLeafMixedWord
import DualTree.InterleavedMixedWord

/-!
# Genuine interleaved D₁ words with shifted Hales--Jewett D₀ components

The no-up restriction in the preceding InterleavedMixedWord theorem was
needed for the *absence* of D₁ leaves, not for its component constructor.
That constructor already uses a fixed singleton-root word at every
non-D₀ coordinate.  We prove its singleton support identity for ANY
coordinate-kind function, build the full ordered vector without a no-up
assumption, and attach genuine ambient-level leaves at each D₁ root.

This is an actual finite-height source MixedProduct.VariableWord with
nonempty full mixed span, not a dummy up-leaf fixture.  The flat word w,
its first-variable position, and the bounded ambient height are kept
explicit.  The independent-parameter span equivalence and Ramsey
canonicalization are further obligations, not asserted here.
-/

namespace DualTree.UpLeafInterleavedGeometry

open DualTree.MixedProduct
open DualTree.InterleavedHeightOne
open DualTree.ShiftedRaySlots

/-- The fixed non-D₀ marker root equals the scheduled support root,
even when the coordinate kind is D₁ instead of D₂. -/
theorem markerPos_eq_supportRoot_of_not_plain
    {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i ≠ CoordKind.plain) :
    (InterleavedMixedWord.markerPos (N := N) hb i).1 =
      supportRoot hb r kind i := by
  simp [InterleavedMixedWord.markerPos, supportRoot, rootLength, hi]

/-- Every interleaved component has exactly its scheduled singleton
support root; this requires no exclusion of genuine D₁ coordinates. -/
theorem component_supportNodes
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (InterleavedFlatHalesJewett.PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d) :
    (InterleavedMixedWord.component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
      [supportRoot hb r kind i] := by
  by_cases hi : kind i = CoordKind.plain
  · calc
      (InterleavedMixedWord.component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
          [slotNode hb i r] := by
            simp only [InterleavedMixedWord.component, dif_pos hi]
            exact InterleavedMixedWord.plainComponent_supportNodes
              hb w fallback r hroot hfirst ⟨i, hi⟩
      _ = [supportRoot hb r kind i] := by
        rw [supportRoot_plain_eq_slot hb r kind i hi]
  · calc
      (InterleavedMixedWord.component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
          [(InterleavedMixedWord.markerPos (N := N) hb i).1] := by
            simp only [InterleavedMixedWord.component, dif_neg hi]
            rfl
      _ = [supportRoot hb r kind i] := by
        rw [markerPos_eq_supportRoot_of_not_plain hb r kind i hi]

/-- Full source vector 1-complete-skew, for arbitrary D₀/D₁/D₂
interleavings, using true shifted Hales--Jewett D₀ words. -/
noncomputable def vectorWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (InterleavedFlatHalesJewett.PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    VectorVariableWord b (ambient d N) d 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := InterleavedMixedWord.component hb kind w fallback r hroot hfirst
  vector_complete := by
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin d =>
        (InterleavedMixedWord.component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes) = true
    have hs :
        (fun i : Fin d =>
          (InterleavedMixedWord.component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes) =
        (fun i => [supportRoot hb r kind i]) := by
      funext i
      exact component_supportNodes hb kind w fallback r hroot hfirst i
    rw [hs]
    exact supportRoot_vectorComplete_one hb r kind

/-- Genuine mixed 1-complete-skew word with real D₁ leaf lists
and the original true D₀/D₁/D₂ coordinate order. -/
noncomputable def mixedWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (InterleavedFlatHalesJewett.PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    MixedProduct.VariableWord b (ambient d N) d 1 β
      (SkewTree.forwardAuxB (b := b)) kind :=
  UpLeafMixedWord.attach hb kind
    (vectorWord hb kind w fallback r hroot hfirst)
    (rootPos hb r kind)
    (fun i => component_supportNodes hb kind w fallback r hroot hfirst i)

/-- The D₁ leaves are all genuine ambient-level nodes, distinct, and
their list has exact cardinality b at every D₁ coordinate. -/
theorem mixedWord_upLeaves_card
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (InterleavedFlatHalesJewett.PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : UpIndex kind) :
    ((mixedWord hb kind w fallback r hroot hfirst).upLeaves i).length = b := by
  simpa using (mixedWord hb kind w fallback r hroot hfirst).upLeaves_card i

/-- Nonempty evaluated mixed span is a CONSEQUENCE of the constructed
interleaved vector, positive branching, and the actual alphabet letter. -/
theorem mixedWord_span_nonempty
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (InterleavedFlatHalesJewett.PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (mixedWord hb kind w fallback r hroot hfirst).span.Nonempty := by
  exact UpLeafMixedWord.attach_span_nonempty hb kind
    (vectorWord hb kind w fallback r hroot hfirst)
    (rootPos hb r kind)
    (fun i => component_supportNodes hb kind w fallback r hroot hfirst i)
    fallback

end DualTree.UpLeafInterleavedGeometry
