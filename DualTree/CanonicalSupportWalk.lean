import DualTree.SkewBranchGeometry
import DualTree.ConeProjectionAlgebra

/-!
# A constructive prefix map from directional successors

The canonical map I_T in Lemma 27 sends an abstract address in
the full b-ary tree to the corresponding chain of support successors.
The present file makes this recursion explicit on finite supports.

At a vertex with a unique immediate successor in direction i,
the transition is that very successor. At other vertices we select
the first witness, or retain the vertex if the direction is empty.
This total fallback is solely for defining a map on all finite
addresses; it is not an assertion that a long address stays in T.

The recursion is prefix-preserving without completeness assumptions;
valid successor paths have their images in T, and the first letter
controls the initial support direction. To identify its restriction
to b^{<k} with I_T for every k-complete skew support still requires
a uniform proof of the validity of all paths of length < k and the
canonical root/intrinsic-height identities.
-/

namespace DualTree.CanonicalSupportWalk

/-- Follow a directional immediate-support successor if one exists. -/
def next {b : Nat} (T : List (Node b))
    (s : Node b) (i : Fin b) : Node b :=
  match SkewTree.branchWitnesses T s i with
  | [] => s
  | t :: _ => t

/-- Even an unsuccessful totalized transition does not leave the parent cone. -/
theorem next_prefix {b : Nat} (T : List (Node b))
    (s : Node b) (i : Fin b) :
    IsPrefix s (next T s i) := by
  cases hlist : SkewTree.branchWitnesses T s i with
  | nil =>
      simpa [next, hlist] using isPrefix_refl s
  | cons t rest =>
      have ht : t ∈ SkewTree.branchWitnesses T s i := by
        simp [hlist]
      have hdir : IsPrefix (s ++ [i]) t :=
        (SkewBranchGeometry.mem_branchWitnesses_iff T s t i).1 ht |>.2
      have hs : IsPrefix s t :=
        isPrefix_trans ⟨[i], rfl⟩ hdir
      simpa [next, hlist] using hs

/-- A unique directional witness is the selected immediate successor. -/
theorem next_unique {b : Nat} (T : List (Node b))
    (s : Node b) (i : Fin b)
    (h : SkewTree.uniqueBranchB T s i = true) :
    SkewTree.immediateSuccB T s (next T s i) = true ∧
      IsPrefix (s ++ [i]) (next T s i) := by
  have hlen : (SkewTree.branchWitnesses T s i).length = 1 := by
    simpa [SkewTree.uniqueBranchB] using h
  cases hlist : SkewTree.branchWitnesses T s i with
  | nil =>
      simp [hlist] at hlen
  | cons t rest =>
      cases rest with
      | nil =>
          have ht : t ∈ SkewTree.branchWitnesses T s i := by
            simp [hlist]
          have ht' :=
            (SkewBranchGeometry.mem_branchWitnesses_iff T s t i).1 ht
          simpa [next, hlist] using ht'
      | cons u us =>
          simp [hlist] at hlen

/-- The chosen unique directional successor belongs to the support. -/
theorem next_mem {b : Nat} (T : List (Node b))
    (s : Node b) (i : Fin b)
    (h : SkewTree.uniqueBranchB T s i = true) :
    next T s i ∈ T :=
  ((SkewBranchGeometry.immediateSuccB_iff
    T s (next T s i)).1 (next_unique T s i h).1).1

/-- Follow the successive directions recorded by a source address. -/
def walk {b : Nat} (T : List (Node b))
    (root : Node b) : Node b → Node b
  | [] => root
  | i :: tail => walk T (next T root i) tail

/-- Walking a concatenation is composition of its two traversals. -/
theorem walk_append {b : Nat} (T : List (Node b))
    (root u v : Node b) :
    walk T root (u ++ v) = walk T (walk T root u) v := by
  induction u generalizing root with
  | nil => rfl
  | cons i tail ih =>
      change walk T (next T root i) (tail ++ v) =
        walk T (walk T (next T root i) tail) v
      exact ih (next T root i)

/-- Every traversal extends its chosen starting vertex. -/
theorem walk_root_prefix {b : Nat} (T : List (Node b))
    (root z : Node b) :
    IsPrefix root (walk T root z) := by
  induction z generalizing root with
  | nil =>
      simpa [walk] using isPrefix_refl root
  | cons i tail ih =>
      change IsPrefix root (walk T (next T root i) tail)
      exact isPrefix_trans (next_prefix T root i)
        (ih (next T root i))

/-- The constructed total map preserves ambient prefix ordering. -/
theorem walk_prefix {b : Nat} (T : List (Node b))
    (root : Node b) {u v : Node b}
    (h : IsPrefix u v) :
    IsPrefix (walk T root u) (walk T root v) := by
  rcases h with ⟨tail, rfl⟩
  rw [walk_append]
  exact walk_root_prefix T (walk T root u) tail

/-- Whenever the first directional branch exists uniquely, all later
steps remain inside that directional cone. -/
theorem walk_first_direction {b : Nat} (T : List (Node b))
    (root : Node b) (i : Fin b) (tail : Node b)
    (h : SkewTree.uniqueBranchB T root i = true) :
    IsPrefix (root ++ [i]) (walk T root (i :: tail)) := by
  change IsPrefix (root ++ [i]) (walk T (next T root i) tail)
  exact isPrefix_trans (next_unique T root i h).2
    (walk_root_prefix T (next T root i) tail)

/-- A source address is valid if every visited direction is uniquely present. -/
def Admissible {b : Nat} (T : List (Node b))
    (root : Node b) : Node b → Prop
  | [] => True
  | i :: tail =>
      SkewTree.uniqueBranchB T root i = true ∧
      Admissible T (next T root i) tail

/-- The constructed map lands in the support on all valid finite paths. -/
theorem walk_mem_of_admissible {b : Nat}
    (T : List (Node b)) (root z : Node b)
    (hroot : root ∈ T) (hvalid : Admissible T root z) :
    walk T root z ∈ T := by
  induction z generalizing root with
  | nil =>
      simpa [walk] using hroot
  | cons i tail ih =>
      rcases hvalid with ⟨hnext, htail⟩
      change walk T (next T root i) tail ∈ T
      exact ih (next T root i) (next_mem T root i hnext) htail

/-- These concrete traversals can now be substituted for the abstract I
in the already verified algebra of cone projections. -/
theorem projection_walk_prefix {b : Nat}
    (T : List (Node b)) (root base : Node b)
    {u v : Node b} (h : IsPrefix u v) :
    IsPrefix
      (ConeProjectionAlgebra.projection (walk T root) base u)
      (ConeProjectionAlgebra.projection (walk T root) base v) := by
  have hmono : ∀ {x y : Node b},
      IsPrefix x y → IsPrefix (walk T root x) (walk T root y) := by
    intro x y hxy
    exact walk_prefix T root hxy
  exact ConeProjectionAlgebra.projection_prefix (walk T root) hmono base h

end DualTree.CanonicalSupportWalk
