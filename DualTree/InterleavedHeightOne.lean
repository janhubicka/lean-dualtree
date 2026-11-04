import DualTree.VectorOrderedSingletons
import DualTree.RayHalesJewett
import DualTree.MixedProduct

/-!
# Scheduled singleton roots for arbitrary interleavings at intrinsic height one

The existing p-D₀/q-D₂ existence theorem puts the p ordinary coordinates
before the q marked coordinates. Its early-versus-late ray-root choice
cannot simply be permuted: the source-facing vector 1-complete-skew
predicate compares lengths in the ACTUAL coordinate order.

For a flat Hales–Jewett word of length N, reserve a disjoint ray interval
of length N+1 for EACH of d mixed coordinates. An ordinary D₀ root is
at its coordinate's first variable offset (r : Fin N). A marked D₂
root is at its coordinate's FIXED interval beginning, independent of r.
The same schedule is harmless on D₁ indices, but no D₁ leaf-set
construction is claimed.

Every root is genuinely bounded in the common ambient tree, and the
lengths are STRICTLY increasing in the true coordinate order. Hence
their singleton supports satisfy the FULL source-facing vector
1-complete-skew predicate. These lemmas supply the GEOMETRY for a future
interleaved mixed word; they do not yet provide a legal shifted
variable word, a substitution/evaluation bridge, c-good existence,
or the full dual-tree theorem.
-/

namespace DualTree.InterleavedHeightOne

open DualTree.MixedProduct
open DualTree.RayHalesJewett

/-- Reserve one interval of N+1 consecutive ray levels per coordinate. -/
def offset (N : Nat) {d : Nat} (i : Fin d) : Nat :=
  i.val * (N + 1)

/-- At an ordinary coordinate use the genuine first Hales–Jewett
variable position; otherwise choose a fixed, colouring-independent
marker root at the beginning of that coordinate's interval. -/
def rootLength {N d : Nat}
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) : Nat :=
  offset N i + if kind i = CoordKind.plain then r.val else 0

/-- Every scheduled root lies at or after its own block beginning. -/
theorem offset_le_rootLength {N d : Nat}
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) :
    offset N i ≤ rootLength r kind i := by
  unfold rootLength
  exact Nat.le_add_right _ _

/-- The root lies strictly BEFORE the next coordinate's block. -/
theorem rootLength_lt_nextOffset {N d : Nat}
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) :
    rootLength r kind i < (i.val + 1) * (N + 1) := by
  have hdelta :
      (if kind i = CoordKind.plain then r.val else 0) < N + 1 := by
    split_ifs <;> omega
  calc
    rootLength r kind i =
        i.val * (N + 1) +
          (if kind i = CoordKind.plain then r.val else 0) := rfl
    _ < i.val * (N + 1) + (N + 1) :=
      Nat.add_lt_add_left hdelta _
    _ = (i.val + 1) * (N + 1) := by simp [Nat.add_mul]

/-- Disjoint scheduling gives a STRICT order of all singleton root
lengths, even for arbitrary alternations of ordinary and marked
coordinates. No assertion about arbitrary permutations of an
existing p-before-q word is made. -/
theorem rootLength_strictMono {N d : Nat}
    (r : Fin N) (kind : Fin d → CoordKind)
    (i j : Fin d) (hij : i < j) :
    rootLength r kind i < rootLength r kind j := by
  have hij' : i.val + 1 ≤ j.val := by
    have hh : i.val < j.val := hij
    omega
  have hmul :
      (i.val + 1) * (N + 1) ≤ j.val * (N + 1) :=
    Nat.mul_le_mul_right (N + 1) hij'
  exact lt_of_lt_of_le (rootLength_lt_nextOffset r kind i)
    (le_trans hmul (offset_le_rootLength r kind j))

/-- All coordinates fit into the uniform finite ambient ray budget. -/
theorem rootLength_lt_ambient {N d : Nat}
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) :
    rootLength r kind i < d * (N + 1) := by
  have hindex : i.val + 1 ≤ d := Nat.succ_le_of_lt i.isLt
  have hmul :
      (i.val + 1) * (N + 1) ≤ d * (N + 1) :=
    Nat.mul_le_mul_right (N + 1) hindex
  exact lt_of_lt_of_le (rootLength_lt_nextOffset r kind i) hmul

/-- The actual node at the allocated root height, on one ray. -/
def supportRoot {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) : Node b :=
  zeroRay hb (rootLength r kind i)

/-- Support-root lengths equal the scheduled levels exactly. -/
theorem supportRoot_length {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) :
    (supportRoot hb r kind i).length = rootLength r kind i := by
  simp [supportRoot, zeroRay]

/-- The scheduled root is a true node of the chosen ambient tree. -/
theorem supportRoot_bounded {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind) (i : Fin d) :
    InHomTree (d * (N + 1) + 1) (supportRoot hb r kind i) := by
  unfold InHomTree
  rw [supportRoot_length]
  have h := rootLength_lt_ambient r kind i
  omega

/-- A marked D₂ root is chosen BEFORE the flat Ramsey word,
not from its first variable index. -/
theorem supportRoot_bullet_fixed {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.bullet) :
    supportRoot hb r kind i = zeroRay hb (offset N i) := by
  simp [supportRoot, rootLength, hi]

/-- Plain D₀ roots occur at the first variable position in
the assigned block. -/
theorem supportRoot_plain {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.plain) :
    supportRoot hb r kind i = zeroRay hb (offset N i + r.val) := by
  simp [supportRoot, rootLength, hi]

/-- The ACTUAL root nodes have strictly increasing lengths in
the mixed coordinate order, not only an abstract index order. -/
theorem supportRoot_lengths_strict {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i j : Fin d) (hij : i < j) :
    (supportRoot hb r kind i).length <
      (supportRoot hb r kind j).length := by
  simpa only [supportRoot_length] using
    (rootLength_strictMono r kind i j hij)

/-- Arbitrarily interleaved D₀/D₂ singleton supports satisfy all
the genuinely executable vector 1-complete-skew clauses, including
cross-coordinate same-level ordering. D₁ leaves are NOT constructed. -/
theorem supportRoot_vectorComplete_one {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind) :
    VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i : Fin d => [supportRoot hb r kind i]) = true := by
  exact VectorSkew.monotone_singletons_vectorComplete_one
    SkewTree.forwardAuxB (supportRoot hb r kind)
      (fun i j hij =>
        le_of_lt (supportRoot_lengths_strict hb r kind i j hij))

/-- The N actual flat-word positions of each plain coordinate occupy
the slots strictly inside its own reserved interval. -/
def slotNode {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (j : Fin N) : Node b :=
  zeroRay hb (offset N i + j.val)

/-- Every slot node is bounded by the same ambient budget. -/
theorem slotNode_bounded {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (j : Fin N) :
    InHomTree (d * (N + 1) + 1) (slotNode hb i j) := by
  have hj : j.val < N + 1 := by omega
  have hlocal : offset N i + j.val <
      (i.val + 1) * (N + 1) := by
    calc
      offset N i + j.val <
          offset N i + (N + 1) := Nat.add_lt_add_left hj _
      _ = (i.val + 1) * (N + 1) := by simp [offset, Nat.add_mul]
  have hidx : i.val + 1 ≤ d := Nat.succ_le_of_lt i.isLt
  have hmul := Nat.mul_le_mul_right (N + 1) hidx
  unfold InHomTree slotNode
  simp only [zeroRay, List.length_replicate]
  omega

/-- The planned D₀ root really is the r-th slot of its
own shifted ray block, a useful bridge for the later word lift. -/
theorem supportRoot_plain_eq_slot {b N d : Nat} (hb : 0 < b)
    (r : Fin N) (kind : Fin d → CoordKind)
    (i : Fin d) (hi : kind i = CoordKind.plain) :
    supportRoot hb r kind i = slotNode hb i r := by
  simp [supportRoot_plain hb r kind i hi, slotNode]

end DualTree.InterleavedHeightOne
