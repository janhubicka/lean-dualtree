import DualTree.Basic

/-!
# Cone projections induced by a prefix-preserving canonical tree map

In Lemma 27 the projection for a frontier t_i is formally
P_i(z) = I_T(I_T^{-1}(t_i) ++ z).
The root and prefix properties used throughout its reconstruction
follow abstractly from prefix preservation of I_T and the fact that
I_T(I_T^{-1}(t_i)) = t_i.

This file verifies those implications without pretending that the
particular canonical map I_T of an arbitrary complete skew support
has yet been constructed. The source-specific construction, its
domain bounds, and the support-image assertion remain open.
-/

namespace DualTree.ConeProjectionAlgebra

/-- Attaching the same source address preserves the prefix relation. -/
theorem prefix_append_left {b : Nat}
    (base : Node b) {u v : Node b}
    (huv : IsPrefix u v) :
    IsPrefix (base ++ u) (base ++ v) := by
  rcases huv with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  rw [htail]
  simp [List.append_assoc]

/-- The paper's projection operation, parameterized by its canonical map. -/
def projection {b : Nat}
    (I : Node b → Node b) (base z : Node b) : Node b :=
  I (base ++ z)

/-- A prefix-preserving canonical map induces prefix-preserving cone projections. -/
theorem projection_prefix
    {b : Nat} (I : Node b → Node b)
    (hI : ∀ {u v : Node b}, IsPrefix u v → IsPrefix (I u) (I v))
    (base : Node b) {x y : Node b}
    (hxy : IsPrefix x y) :
    IsPrefix (projection I base x) (projection I base y) :=
  hI (prefix_append_left base hxy)

/-- Every projected node extends the projected empty address. -/
theorem projection_cone
    {b : Nat} (I : Node b → Node b)
    (hI : ∀ {u v : Node b}, IsPrefix u v → IsPrefix (I u) (I v))
    (base z : Node b) :
    IsPrefix (I base) (projection I base z) := by
  apply hI
  exact ⟨z, by simp⟩

/-- The projection sends the empty tail to its base's image. -/
theorem projection_nil {b : Nat}
    (I : Node b → Node b) (base : Node b) :
    projection I base [] = I base := by
  simp [projection]

/-- For an actual frontier whose source address is known, the cone is rooted there. -/
theorem projection_rooted_at_frontier
    {b : Nat} (I : Node b → Node b)
    (hI : ∀ {u v : Node b}, IsPrefix u v → IsPrefix (I u) (I v))
    (frontier base z : Node b)
    (hbase : I base = frontier) :
    IsPrefix frontier (projection I base z) := by
  rw [← hbase]
  exact projection_cone I hI base z

/-- A left inverse of the canonical map identifies the cone's root exactly. -/
theorem projection_leftInverse_root
    {b : Nat}
    (I inv : Node b → Node b)
    (frontier : Node b)
    (hleft : I (inv frontier) = frontier) :
    projection I (inv frontier) [] = frontier := by
  simpa [projection] using hleft

end DualTree.ConeProjectionAlgebra
