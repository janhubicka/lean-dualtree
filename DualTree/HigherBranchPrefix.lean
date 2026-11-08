import DualTree.HigherPhysicalSupport

/-!
# Track C: selected cone addresses lie in the intended physical branches

The selected depth-N addresses vary in the r-th digit and have zeroes
before it. This file proves, rather than assumes, that their corresponding
bounded cone nodes extend the actual root followed by the chosen outgoing
direction. The proof uses the exact List.ofFn address representation.
-/

namespace DualTree.HigherBranchPrefix

open HigherConeAddresses
open HigherTreeCells
open HigherPhysicalSupport

/-- The first r digits of every selected address are exactly zero. -/
theorem branchAddress_take_zero {b N : Nat}
    (hb : 0 < b) (r : Fin N) (dir : Fin b) :
    (addressNode (branchAddress hb r dir)).take r.val =
      List.replicate r.val (⟨0, hb⟩ : Fin b) := by
  have hle : r.val ≤ N := Nat.le_of_lt r.isLt
  change (List.ofFn (branchAddress hb r dir)).take r.val =
    List.replicate r.val (⟨0, hb⟩ : Fin b)
  rw [← Fin.ofFn_take_eq_take_ofFn hle (branchAddress hb r dir)]
  have hconst :
      Fin.take r.val hle (branchAddress hb r dir) =
        fun _ : Fin r.val => (⟨0, hb⟩ : Fin b) := by
    funext j
    have hne : Fin.castLE hle j ≠ r := by
      intro h
      have hv := congrArg Fin.val h
      change j.val = r.val at hv
      exact (Nat.ne_of_lt j.isLt) hv
    simp [Fin.take, branchAddress, hne]
  simp [hconst, addressNode]

/-- The zero spine to depth r is a genuine initial segment of the address. -/
theorem branchAddress_zero_prefix {b N : Nat}
    (hb : 0 < b) (r : Fin N) (dir : Fin b) :
    IsPrefix (List.replicate r.val (⟨0, hb⟩ : Fin b))
      (addressNode (branchAddress hb r dir)) := by
  have hp :
      List.replicate r.val (⟨0, hb⟩ : Fin b) <+:
        addressNode (branchAddress hb r dir) := by
    apply List.prefix_iff_eq_take.mpr
    simpa using (branchAddress_take_zero hb r dir).symm
  obtain ⟨tail, htail⟩ := hp
  exact ⟨tail, htail.symm⟩

/-- Adding the selected branch digit gives a true prefix of the address. -/
theorem branchAddress_direction_prefix {b N : Nat}
    (hb : 0 < b) (r : Fin N) (dir : Fin b) :
    IsPrefix (List.replicate r.val (⟨0, hb⟩ : Fin b) ++ [dir])
      (addressNode (branchAddress hb r dir)) := by
  have hp :
      List.replicate r.val (⟨0, hb⟩ : Fin b) <+:
        addressNode (branchAddress hb r dir) := by
    obtain ⟨tail, htail⟩ := branchAddress_zero_prefix hb r dir
    exact ⟨tail, htail.symm⟩
  have hlen :
      (List.replicate r.val (⟨0, hb⟩ : Fin b)).length <
        (addressNode (branchAddress hb r dir)).length := by
    simpa [addressNode_length] using r.isLt
  have hdir :
      (addressNode (branchAddress hb r dir)).get
        ⟨(List.replicate r.val (⟨0, hb⟩ : Fin b)).length, hlen⟩ =
      dir := by
    simpa [addressNode, branchAddress, List.get_ofFn]
      using branchAddress_at_root hb r dir
  have hp' := List.concat_get_prefix hp hlen
  rw [hdir] at hp'
  obtain ⟨tail, htail⟩ := hp'
  exact ⟨tail, htail.symm⟩

/-- The physical cone support node is in exactly the intended first
outgoing direction of the physical root node. -/
theorem root_branch_prefix_child {b N M : Nat}
    (hb : 0 < b) (r : Fin N) (s : Fin M) (dir : Fin b) :
    IsPrefix ((root (M := M) hb r).1 ++ [dir])
      (child hb r s dir).1 := by
  change IsPrefix
    (List.replicate r.val (⟨0, hb⟩ : Fin b) ++ [dir])
    (addressNode (branchAddress hb r dir) ++
      List.replicate s.val (⟨0, hb⟩ : Fin b))
  exact isPrefix_trans
    (branchAddress_direction_prefix hb r dir)
    ⟨List.replicate s.val (⟨0, hb⟩ : Fin b), rfl⟩

end DualTree.HigherBranchPrefix
