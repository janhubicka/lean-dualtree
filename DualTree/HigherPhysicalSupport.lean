import DualTree.HigherTreeEncoding

/-!
# Track C: genuine b+1 variable roots in a single physical tree

The Hales--Jewett words select earliest root position r and cone position s.
Their actual support has one root-band node and precisely b distinct
cone-band nodes, one for each of the b outgoing directions. This certificate
prevents silently identifying two cone parameters, and is independent of
the tree-word encoding and of any unproved Ramsey conclusion.

The prefix/branch and complete-skew checks still belong to the next
geometry theorem.
-/

namespace DualTree.HigherPhysicalSupport

open HigherConeAddresses
open HigherTreeCells

/-- Chosen actual root-band node. -/
def root {b N M : Nat} (hb : 0 < b) (r : Fin N) :
    BoundedNode b (N + M) :=
  rootBandCell (M := M) hb r

/-- The corresponding actual selected branch-cone node. -/
def child {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) (dir : Fin b) :
    BoundedNode b (N + M) :=
  coneBandCell hb (branchAddress hb r dir) s

/-- The complete list has one root plus one candidate child in every
direction; there are no arbitrary singleton substitutes. -/
def support {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    List (BoundedNode b (N + M)) :=
  root hb r :: List.ofFn (child hb r s)

theorem root_ne_child {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) (dir : Fin b) :
    root (M := M) hb r ≠ child hb r s dir :=
  rootBandCell_ne_coneBandCell hb r (branchAddress hb r dir) s

theorem child_injective {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    Function.Injective (child hb r s) := by
  intro i j hij
  have hpair : (branchAddress hb r i, s) =
      (branchAddress hb r j, s) :=
    coneBandCell_pair_injective hb hij
  exact (branchAddress_injective hb r) (congrArg Prod.fst hpair)

/-- No two proposed roots represent the same bounded node. -/
theorem support_nodup {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    (support hb r s).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hm
    obtain ⟨dir, hdir⟩ := List.mem_ofFn.mp hm
    exact (root_ne_child hb r s dir) hdir.symm
  · exact List.nodup_ofFn.mpr (child_injective hb r s)

theorem support_card {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) :
    (support hb r s).length = b + 1 := by
  simp [support]

theorem child_level {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) (dir : Fin b) :
    (child hb r s dir).1.length = N + s.val := by
  exact coneBandCell_length hb (branchAddress hb r dir) s

theorem root_level_lt_child {b N M : Nat} (hb : 0 < b)
    (r : Fin N) (s : Fin M) (dir : Fin b) :
    (root (M := M) hb r).1.length < (child hb r s dir).1.length := by
  rw [show (root (M := M) hb r).1.length = r.val from
    rootBandCell_length hb r, child_level]
  have hr : r.val < N := r.isLt
  omega

end DualTree.HigherPhysicalSupport
