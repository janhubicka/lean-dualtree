import DualTree.InterleavedFlatHalesJewett

/-!
# Genuine mixed vector word for arbitrary interleaved D₀/D₂ coordinates

The source-facing coordinate-kind function may alternate ordinary
word coordinates and marked coordinates in ANY order. No D₁/up
coordinate is admitted in this height-one base case.

The ordinary coordinates project a single flat Hales–Jewett word on
the finite product alphabet of actual plain indices and use the true
shifted-ray KVariableWord. The marked coordinates use independent
one-variable words at fixed, preselected marker roots. Every
component is an actual source-facing KVariableWord, and the
complete-skew condition is verified on the entire vector in the
original coordinate order, not merely coordinate by coordinate.

This is a genuine mixed VARIABLE WORD, but it is not yet a c-good
Ramsey existence theorem: the next layer must identify the actual
mixed span with the independently evaluated D₀ substitutions and
retained D₂ letters. No D₁ leaves or higher intrinsic height is
fabricated.
-/

namespace DualTree.InterleavedMixedWord

open DualTree.MixedProduct
open DualTree.InterleavedHeightOne
open DualTree.InterleavedFlatHalesJewett
open DualTree.ShiftedRaySlots

/-- The allowed mixed patterns have no genuine up/leaf coordinates. -/
abbrev NoUp {d : Nat} (kind : Fin d → CoordKind) : Prop :=
  ∀ i : Fin d, kind i ≠ CoordKind.up

/-- Every nonordinary coordinate of a no-D₁ pattern is genuinely
marked D₂; there are no dummy coordinates. -/
theorem bullet_of_not_plain
    {d : Nat} (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (i : Fin d) (hi : kind i ≠ CoordKind.plain) :
    kind i = CoordKind.bullet := by
  cases hk : kind i with
  | plain =>
      exact (hi hk).elim
  | up =>
      exact (hnoUp i hk).elim
  | bullet =>
      rfl

/-- Fixed bounded ray marker, defined BEFORE the Hales–Jewett
word or its first-variable position has been selected. -/
def markerPos {b N d : Nat}
    (hb : 0 < b) (i : Fin d) :
    BoundedNode b (ambient d N) :=
  ⟨RayHalesJewett.zeroRay hb (offset N i), by
    have hi : i.val ≤ d := Nat.le_of_lt i.isLt
    have hm : i.val * (N + 1) ≤ d * (N + 1) :=
      Nat.mul_le_mul_right (N + 1) hi
    exact (by
      simpa [InHomTree, ambient, RayHalesJewett.zeroRay, offset]
        using (Nat.lt_succ_of_le hm))⟩

/-- The predetermined D₂ marker is the true scheduled support root,
for ANY subsequently selected first-variable index r. -/
theorem markerPos_eq_supportRoot
    {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.bullet) :
    (markerPos (N := N) hb i).1 = supportRoot hb r kind i := by
  exact (supportRoot_bullet_fixed hb r kind i hi).symm

/-- Each ordinary-coordinate projection gives a true shifted
one-root Hales–Jewett KVariableWord with legal below-root symbols. -/
noncomputable def plainComponent
    {b N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (hb : 0 < b)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : PlainIndex kind) :
    KVariableWord b (ambient d N) 1 β
      (SkewTree.forwardAuxB (b := b)) :=
  ShiftedRayWord.kWord hb i.1 (project w i) fallback r
    (project_root w r hroot i)
    (fun j v hv => project_after_root w r hfirst i j v hv)

/-- Every genuine ordinary component has precisely its scheduled
singleton support root. -/
theorem plainComponent_supportNodes
    {b N d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (hb : 0 < b)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : PlainIndex kind) :
    (plainComponent hb w fallback r hroot hfirst i).toVariableWord.supportNodes =
      [slotNode hb i.1 r] := by
  exact ShiftedRayWord.kWord_supportNodes hb i.1
    (project w i) fallback r (project_root w r hroot i)
    (fun j v hv => project_after_root w r hfirst i j v hv)

/-- For a no-up kind, choose a shifted Hales–Jewett word at
each genuine D₀ coordinate, and a fixed-root marker word at
each D₂ coordinate. All evaluated component choices are
independent. -/
noncomputable def component
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d) :
    KVariableWord b (ambient d N) 1 β
      (SkewTree.forwardAuxB (b := b)) :=
  if hi : kind i = CoordKind.plain then
    plainComponent hb w fallback r hroot hfirst ⟨i, hi⟩
  else
    FixedRootMarkerWord.kWord (markerPos hb i) fallback

/-- The actual complete-skew singleton support of each mixed
component is exactly its scheduled source-coordinate root. -/
theorem component_supportNodes
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d) :
    (component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
      [supportRoot hb r kind i] := by
  by_cases hi : kind i = CoordKind.plain
  · calc
      (component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
          [slotNode hb i r] := by
            simp only [component, dif_pos hi]
            exact plainComponent_supportNodes hb w fallback r
              hroot hfirst ⟨i, hi⟩
      _ = [supportRoot hb r kind i] := by
        rw [supportRoot_plain_eq_slot hb r kind i hi]
  · have hbullet := bullet_of_not_plain kind hnoUp i hi
    calc
      (component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes =
          [(markerPos hb i).1] := by
            simp only [component, dif_neg hi]
            rfl
      _ = [supportRoot hb r kind i] := by
        rw [← markerPos_eq_supportRoot hb r kind i hbullet]

/-- TRUE source-facing vector 1-complete skew, with arbitrary
D₀/D₂ interleaving. It invokes the FULL executable predicate,
including cross-coordinate ordering; componentwise legality alone
would not suffice. -/
noncomputable def vectorWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    VectorVariableWord b (ambient d N) d 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := component hb kind w fallback r hroot hfirst
  vector_complete := by
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin d =>
        (component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes) = true
    have hs :
        (fun i : Fin d =>
          (component hb kind w fallback r hroot hfirst i).toVariableWord.supportNodes) =
        (fun i => [supportRoot hb r kind i]) := by
      funext i
      exact component_supportNodes hb kind hnoUp w fallback r hroot hfirst i
    rw [hs]
    exact supportRoot_vectorComplete_one hb r kind

/-- The genuine mixed-product variable word with the ACTUAL
interleaved kind and no fake up-leaf coordinates. -/
noncomputable def mixedWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnoUp : NoUp kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    MixedProduct.VariableWord b (ambient d N) d 1 β
      (SkewTree.forwardAuxB (b := b)) kind where
  vector := vectorWord hb kind hnoUp w fallback r hroot hfirst
  upLeaves := fun i => False.elim (hnoUp i.1 i.2)
  upLeaves_nodup := fun i => False.elim (hnoUp i.1 i.2)
  upLeaves_card := fun i => False.elim (hnoUp i.1 i.2)
  up_support_skew := fun i => False.elim (hnoUp i.1 i.2)

end DualTree.InterleavedMixedWord
