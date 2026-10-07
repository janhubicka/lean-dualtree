import DualTree.MixedGood

/-!
# Refinement of mixed-product combinatorial subspaces

The proofs in Section 4 repeatedly pass to further combinatorial subspaces.
This file makes that implicit monotonicity explicit.

There are two useful notions:
* span refinement: the generated mixed span is included in the previous span;
* source-facing syntactic refinement data: every word component is obtained by
  uniform substitution, and every D1 leaf set is included in the old leaf set.

The second implies the first for every alphabet.  The D2 support condition is
not an extra hypothesis: it follows from support preservation under syntactic
refinement.  Consequently c-goodness is inherited by every further subspace.
-/

namespace DualTree.MixedProduct

namespace VariableWord

/-- A further mixed combinatorial subspace, expressed directly by span inclusion. -/
def Refines
    {b n d k k' : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (g : VariableWord b n d k' α aux kind)
    (f : VariableWord b n d k α aux kind) : Prop :=
  g.span ⊆ f.span

theorem refines_refl
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k α aux kind) :
    Refines f f := by
  intro x hx
  exact hx

theorem refines_trans
    {b n d k₀ k₁ k₂ : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (h : VariableWord b n d k₂ α aux kind)
    (g : VariableWord b n d k₁ α aux kind)
    (f : VariableWord b n d k₀ α aux kind)
    (hhg : Refines h g)
    (hgf : Refines g f) :
    Refines h f := by
  intro x hx
  exact hgf (hhg hx)

/--
Coordinatewise syntactic substitution together with inclusion of the D1 leaf
sets implies inclusion of the full mixed span.

For D2 coordinates the marked point stays legal because syntactic refinement
preserves variable roots.
-/
theorem refines_of_syntactic_components
    {b n d k k' : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (g : VariableWord b n d k' α aux kind)
    (f : VariableWord b n d k α aux kind)
    (hword : ∀ i,
      KVariableWord.SyntacticRefines
        (g.vector.components i) (f.vector.components i))
    (hleaf : ∀ i : UpIndex kind, ∀ x,
      x ∈ g.upLeaves i → x ∈ f.upLeaves i) :
    Refines g f := by
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hwi : x.words i ∈ (g.vector.components i).span := hx.1 i
    exact KVariableWord.syntacticRefines_refines
      (g.vector.components i) (f.vector.components i) (hword i) hwi
  · intro i
    exact hleaf i (x.upPoint i) (hx.2.1 i)
  · intro i
    exact KVariableWord.support_subset_of_syntacticRefines
      (g.vector.components i.1) (f.vector.components i.1)
      (hword i.1) (x.bulletPoint i) (hx.2.2 i)

end VariableWord

/-- Definition 11's c-good invariant is inherited by every further subspace. -/
theorem good_of_refines
    {b n d k k' : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    {g : VariableWord b n d k' α aux kind}
    (hgood : Good c f)
    (hgf : VariableWord.Refines g f) :
    Good c g := by
  intro x y hx hy ht hv
  exact hgood (hgf hx) (hgf hy) ht hv

/--
A source-facing corollary: coordinatewise syntactic refinement and D1 leaf
inclusion preserve c-goodness.
-/
theorem good_of_syntactic_refinement
    {b n d k k' : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    (g : VariableWord b n d k' α aux kind)
    (hgood : Good c f)
    (hword : ∀ i,
      KVariableWord.SyntacticRefines
        (g.vector.components i) (f.vector.components i))
    (hleaf : ∀ i : UpIndex kind, ∀ x,
      x ∈ g.upLeaves i → x ∈ f.upLeaves i) :
    Good c g :=
  good_of_refines hgood
    (VariableWord.refines_of_syntactic_components g f hword hleaf)

end DualTree.MixedProduct
