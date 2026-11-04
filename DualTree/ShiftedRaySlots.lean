import DualTree.FixedRootMarkerWord

/-!
# Exact decoding of shifted ray slots for arbitrarily interleaved coordinates

The existing root schedule reserves a disjoint interval of N+1 ray
levels for each coordinate in the true mixed index order. Here we
upgrade its unbounded Node addresses to actual finite BoundedNodes
and define the genuine inverse index of each coordinate's N slots.

This is the address-level prerequisite for shifting a finite
Hales–Jewett word into each ordinary D₀ coordinate without confusing
slots of different coordinates. The proof identifies every recognized
slot EXACTLY with its constructed bounded node, and proves that the
D₂ marker root is independent of the Hales–Jewett variable index.

This module does NOT yet define shifted symbolic variable words,
their evaluation semantics, or a new unconditional Ramsey theorem.
-/

namespace DualTree.ShiftedRaySlots

open DualTree.MixedProduct
open DualTree.InterleavedHeightOne
open DualTree.RayHalesJewett

/-- A common ambient tree contains all d disjoint N-slot intervals,
each with one spare level. -/
abbrev ambient (d N : Nat) : Nat := d * (N + 1) + 1

/-- Genuine bounded address for the j-th flat slot in coordinate i. -/
def slotPos {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (j : Fin N) : BoundedNode b (ambient d N) :=
  ⟨slotNode hb i j, by
    simpa only [ambient] using slotNode_bounded hb i j⟩

/-- Genuine bounded support root for any mixed coordinate. -/
def rootPos {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) : BoundedNode b (ambient d N) :=
  ⟨supportRoot hb r kind i, by
    simpa only [ambient] using supportRoot_bounded hb r kind i⟩

theorem slotPos_length {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (j : Fin N) :
    (slotPos hb i j).1.length = offset N i + j.val := by
  simp [slotPos, slotNode, zeroRay]

/-- Recognize precisely a ray slot in coordinate i's disjoint
length band; all non-slots return none. -/
noncomputable def slotIndex {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (t : BoundedNode b (ambient d N)) :
    Option (Fin N) :=
  if h : t.1 = zeroRay hb t.1.length ∧
       offset N i ≤ t.1.length ∧
       t.1.length < offset N i + N then
    some ⟨t.1.length - offset N i, by
      have hbound := h.2.2
      omega⟩
  else none

/-- The actual decoder is a left inverse of each coordinate's slot
embedding; no ghost or duplicate slot is introduced. -/
theorem slotIndex_slotPos {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (j : Fin N) :
    slotIndex hb i (slotPos hb i j) = some j := by
  have hl := slotPos_length hb i j
  have hroot :
      (slotPos hb i j).1 =
        zeroRay hb (slotPos hb i j).1.length := by
    simp [slotPos, slotNode, zeroRay]
  have hge : offset N i ≤ (slotPos hb i j).1.length := by
    rw [hl]
    omega
  have hlt : (slotPos hb i j).1.length <
      offset N i + N := by
    rw [hl]
    exact Nat.add_lt_add_left j.isLt _
  have hcond :
      (slotPos hb i j).1 =
          zeroRay hb (slotPos hb i j).1.length ∧
      offset N i ≤ (slotPos hb i j).1.length ∧
      (slotPos hb i j).1.length < offset N i + N :=
    ⟨hroot, hge, hlt⟩
  unfold slotIndex
  rw [dif_pos hcond]
  congr 1
  apply Fin.ext
  change (slotPos hb i j).1.length - offset N i = j.val
  rw [hl]
  omega

/-- The converse decoding theorem: a successful recognition
identifies the exact source-facing bounded slot, not just its length. -/
theorem slotIndex_some {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (t : BoundedNode b (ambient d N))
    (j : Fin N) (h : slotIndex hb i t = some j) :
    t = slotPos hb i j := by
  unfold slotIndex at h
  split_ifs at h with hcond
  · have hindex :
        (⟨t.1.length - offset N i, by omega⟩ : Fin N) = j :=
      Option.some.inj h
    have hval : t.1.length - offset N i = j.val :=
      congrArg Fin.val hindex
    have hlen : t.1.length = offset N i + j.val := by
      have hge := hcond.2.1
      omega
    apply Subtype.ext
    change t.1 = slotNode hb i j
    calc
      t.1 = zeroRay hb t.1.length := hcond.1
      _ = zeroRay hb (offset N i + j.val) := by rw [hlen]
      _ = slotNode hb i j := rfl

/-- Ordinary D₀ roots are exactly the first-variable slot of
their own translated Hales–Jewett ray segment. -/
theorem rootPos_plain_eq_slotPos {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.plain) :
    rootPos hb r kind i = slotPos hb i r := by
  apply Subtype.ext
  exact supportRoot_plain_eq_slot hb r kind i hi

/-- For each genuine D₂ coordinate, the chosen marker node is
independent of whichever first-variable index r the Ramsey proof
eventually returns. This avoids a circular colouring definition. -/
theorem rootPos_bullet_independent {b N d : Nat} (hb : 0 < b)
    (r s : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.bullet) :
    rootPos hb r kind i = rootPos hb s kind i := by
  apply Subtype.ext
  exact (supportRoot_bullet_fixed hb r kind i hi).trans
    (supportRoot_bullet_fixed hb s kind i hi).symm

/-- The shifted slot decoder recognizes the true D₀ variable root
as the first variable position of its own flat word. -/
theorem slotIndex_plain_root {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.plain) :
    slotIndex hb i (rootPos hb r kind i) = some r := by
  rw [rootPos_plain_eq_slotPos hb r kind i hi]
  exact slotIndex_slotPos hb i r

end DualTree.ShiftedRaySlots
