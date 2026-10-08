import DualTree.ConeWordLift
import DualTree.VariableWord

/-!
# Root alignment of a cone-word lift

The final reconstruction in Lemma 27 requires that a variable emitted
at an old variable root be rooted at an ambient prefix of that root.
The cone-word decoding satisfies this condition whenever its cone map
P preserves prefixes and sends local nodes into the cone.

For auxiliary letters this uses the visible-ancestor decoder; for
genuine local variables it follows from the tree-variable-word
below-root axiom and the prefix monotonicity of P. Original letters
cannot emit a variable.

The two geometric properties of the particular P_i map must still be
proved from the canonical skew-tree embedding; they are stated
explicitly, not silently assumed.
-/

namespace DualTree.ConeRootAlignment

/--
Every variable symbol emitted by a cone-word lift is rooted at a
prefix of the ambient image of the corresponding local address.
-/
theorem lifted_variable_root_prefix
    {b n m : Nat} {α : Type*}
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (P : Node b → Node b)
    (hmono : ∀ {u v : Node b},
      IsPrefix u v → IsPrefix (P u) (P v))
    (hcone : ∀ z : Node b, IsPrefix frontier (P z))
    (z : BoundedNode b n) (r : Node b)
    (hr :
      ConeWordLift.liftAtCone T I frontier a hfront
        w.word (fun v : w.Vars => P v.1.1) z = Sum.inr r) :
    IsPrefix r (P z.1) := by
  cases hw : w.word z with
  | inl c =>
      cases c with
      | inl x =>
          simp [ConeWordLift.liftAtCone, ConeWordLift.liftWord,
            ConeWordLift.liftSymbol, hw] at hr
      | inr j =>
          have hdecoded :
              ConeLocalDecoder.decodeRoot T I frontier a hfront j =
                Sum.inr r := by
            simpa [ConeWordLift.liftAtCone, ConeWordLift.liftWord,
              ConeWordLift.liftSymbol, hw] using hr
          have hpre : IsStrictPrefix r frontier :=
            ConeLocalDecoder.decodeRoot_prefix T I frontier
              a hfront j r hdecoded
          exact isPrefix_trans hpre.1 (hcone z.1)
  | inr v =>
      have heq : P v.1.1 = r := by
        simpa [ConeWordLift.liftAtCone, ConeWordLift.liftWord,
          ConeWordLift.liftSymbol, hw] using hr
      rw [← heq]
      exact hmono (w.below v z hw)

/--
If local addresses of old source roots are sent by P back to their
old roots, the fibrewise coding induced by a cone word is root-aligned
at all source variables.
-/
theorem root_alignment_of_code
    {b n m N : Nat} {α β : Type*}
    (f : VariableWord b N β)
    (T I : List (Node b)) (frontier : Node b)
    (a : α)
    (hfront : SkewTree.heightAt T frontier ≤ m + 1)
    (w : VariableWord b n (ConeWordLift.EnlargedLetter α m))
    (P : Node b → Node b)
    (hmono : ∀ {u v : Node b},
      IsPrefix u v → IsPrefix (P u) (P v))
    (hcone : ∀ z : Node b, IsPrefix frontier (P z))
    (address : f.Vars → BoundedNode b n)
    (haddress : ∀ v : f.Vars, P (address v).1 = v.1.1)
    (ρ : f.Vars → Sum α (Node b))
    (hcode : ∀ v : f.Vars,
      ρ v =
        ConeWordLift.liftAtCone T I frontier a hfront
          w.word (fun u : w.Vars => P u.1.1) (address v))
    (v : f.Vars) (r : Node b)
    (hρ : ρ v = Sum.inr r) :
    IsPrefix r v.1.1 := by
  have hlocal :
      ConeWordLift.liftAtCone T I frontier a hfront
          w.word (fun u : w.Vars => P u.1.1) (address v) =
        Sum.inr r := by
    rw [← hcode v]
    exact hρ
  have hp := lifted_variable_root_prefix T I frontier a
    hfront w P hmono hcone (address v) r hlocal
  simpa [haddress v] using hp

end DualTree.ConeRootAlignment
