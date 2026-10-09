import DualTree.ConeRootAlignment
import DualTree.ConeProjectionAlgebra

/-!
# Canonical cone projection and root-aligned decoding

Combines the two previously separate verifications for Lemma 27.
Whenever the canonical tree map is prefix-preserving and a source
address maps to the selected frontier, its induced cone projection
automatically meets the two geometric hypotheses needed to decode
auxiliary letters and genuine cone variables with root alignment.

No existence theorem for the canonical map I_T, and no source-specific
identification of the addresses of original roots, is assumed here.
These remain the substantive obligations in Lemma 27.
-/

namespace DualTree.ConeProjectionAlignment

/-- Variables decoded using a canonical cone projection are rooted below
the corresponding projected local position. -/
theorem lifted_root_prefix
    {b n m : Nat} {α : Type*}
    (T A : List (Node b)) (frontier base : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (I : Node b → Node b)
    (hI : ∀ {u v : Node b}, IsPrefix u v → IsPrefix (I u) (I v))
    (hbase : I base = frontier)
    (z : BoundedNode b n) (r : Node b)
    (hr : ConeWordLift.liftAtCone T A frontier a hfront
      w.word
      (fun v : w.Vars => ConeProjectionAlgebra.projection I base v.1.1) z =
        Sum.inr r) :
    IsPrefix r (ConeProjectionAlgebra.projection I base z.1) := by
  have hmono : ∀ {u v : Node b},
      IsPrefix u v →
        IsPrefix (ConeProjectionAlgebra.projection I base u)
                 (ConeProjectionAlgebra.projection I base v) := by
    intro u v huv
    exact ConeProjectionAlgebra.projection_prefix I hI base huv
  have hcone : ∀ z : Node b,
      IsPrefix frontier (ConeProjectionAlgebra.projection I base z) := by
    intro z
    exact ConeProjectionAlgebra.projection_rooted_at_frontier
      I hI frontier base z hbase
  exact ConeRootAlignment.lifted_variable_root_prefix
    T A frontier a hfront w
    (ConeProjectionAlgebra.projection I base) hmono hcone z r hr

/-- The cone projection interface supplies the root alignment of the
resulting substitution on source variable roots, as soon as addresses
are identified with their source images. -/
theorem source_root_alignment
    {b n m N : Nat} {α β : Type*}
    (f : VariableWord b N β)
    (T A : List (Node b)) (frontier base : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (I : Node b → Node b)
    (hI : ∀ {u v : Node b}, IsPrefix u v → IsPrefix (I u) (I v))
    (hbase : I base = frontier)
    (address : f.Vars → BoundedNode b n)
    (haddress : ∀ v : f.Vars,
      ConeProjectionAlgebra.projection I base (address v).1 = v.1.1)
    (ρ : f.Vars → Sum α (Node b))
    (hcode : ∀ v : f.Vars,
      ρ v = ConeWordLift.liftAtCone T A frontier a hfront
        w.word
        (fun u : w.Vars =>
          ConeProjectionAlgebra.projection I base u.1.1)
        (address v))
    (v : f.Vars) (r : Node b)
    (hρ : ρ v = Sum.inr r) :
    IsPrefix r v.1.1 := by
  have hmono : ∀ {u v : Node b},
      IsPrefix u v →
        IsPrefix (ConeProjectionAlgebra.projection I base u)
                 (ConeProjectionAlgebra.projection I base v) := by
    intro u v huv
    exact ConeProjectionAlgebra.projection_prefix I hI base huv
  have hcone : ∀ z : Node b,
      IsPrefix frontier (ConeProjectionAlgebra.projection I base z) := by
    intro z
    exact ConeProjectionAlgebra.projection_rooted_at_frontier
      I hI frontier base z hbase
  exact ConeRootAlignment.root_alignment_of_code
    f T A frontier a hfront w
    (ConeProjectionAlgebra.projection I base) hmono hcone
    address haddress ρ hcode v r hρ

end DualTree.ConeProjectionAlignment
