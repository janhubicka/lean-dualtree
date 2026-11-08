import DualTree.RootFreezing
import DualTree.MixedRefinement
import DualTree.DirectionalSupport

/-!
# Support thinning of genuine D₀/D₂ mixed words

A chosen family of duplicate-free support subsets with the FULL vector
q-complete geometry determines a genuine mixed word of intrinsic height
q.  Every discarded variable root is uniformly replaced by one fallback
letter.  Surviving roots are retained literally, so each component is a
syntactic refinement over every alphabet with a fallback letter.

The construction is restricted to kinds with no D₁ coordinates.  It
therefore needs no new ambient-leaf selection: the up-coordinate type is
empty.  Mixed span inclusion and inheritance of c-goodness follow from
the already proved syntactic mixed-refinement interface.

The support subsets are supplied input.  This module does not select a
homogeneous vector of supports or establish a Ramsey bound.  In
particular, separate component completeness cannot replace the full
cross-coordinate ordering and separation hypothesis below.
-/

namespace DualTree.MixedSupportThinning

open MixedProduct

private theorem selected_component_complete
    {b n d q : Nat}
    {aux : Node b → Node b → Bool}
    (S : Fin d → List (BoundedNode b n))
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (i : Fin d) :
    SkewTree.completeB aux q ((S i).map Subtype.val) = true := by
  have hparts := hvector
  simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true] at hparts
  exact (List.all_eq_true.mp hparts.1.1) i
    (DirectionalSupport.mem_allFin d i)

private noncomputable def component
    {b n d H q : Nat} {β : Type*}
    {aux : Node b → Node b → Bool} {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) (i : Fin d) : KVariableWord b n q β aux where
  toVariableWord := Lemma27Repair.restrictSupport
    (f.vector.components i).toVariableWord (S i) (hnd i) (hsub i) fallback
  complete_support := by
    change SkewTree.completeB aux q ((S i).map Subtype.val) = true
    exact selected_component_complete S hvector i

private noncomputable def vectorWord
    {b n d H q : Nat} {β : Type*}
    {aux : Node b → Node b → Bool} {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) : VectorVariableWord b n d q β aux where
  components := component f S hnd hsub hvector fallback
  vector_complete := by
    change VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true
    exact hvector

/-- A genuine mixed word on the chosen complete vector of support
subsets.  Root masking replaces all occurrences of a discarded variable
uniformly, while the no-up hypothesis discharges every D₁ leaf field. -/
noncomputable def thin
    {b n d H q : Nat} {β : Type*}
    {aux : Node b → Node b → Bool} {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) : MixedProduct.VariableWord b n d q β aux kind where
  vector := vectorWord f S hnd hsub hvector fallback
  upLeaves := fun i => False.elim (hNoUp i.1 i.2)
  upLeaves_nodup := fun i => False.elim (hNoUp i.1 i.2)
  upLeaves_card := fun i => False.elim (hNoUp i.1 i.2)
  up_support_skew := fun i => False.elim (hNoUp i.1 i.2)

variable {b n d H q : Nat} {β : Type*}
variable {aux : Node b → Node b → Bool} {kind : Fin d → CoordKind}

/-- The support in every coordinate is exactly the supplied list. -/
theorem thin_support
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) (i : Fin d) :
    ((thin f hNoUp S hnd hsub hvector fallback).vector.components i).support =
      S i := rfl

/-- Each thinned component is one literal root-mask substitution of the
original component, with no alphabet-cardinality assumption. -/
theorem thin_syntactic_components
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) (i : Fin d) :
    KVariableWord.SyntacticRefines
      ((thin f hNoUp S hnd hsub hvector fallback).vector.components i)
      (f.vector.components i) := by
  exact ⟨Lemma27Repair.rootMask
    (f.vector.components i).toVariableWord (S i) fallback, rfl⟩

/-- The whole thinned mixed span is included in the original mixed span.
Marked D₂ points remain genuine roots by syntactic refinement. -/
theorem thin_refines
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β) :
    MixedProduct.VariableWord.Refines
      (thin f hNoUp S hnd hsub hvector fallback) f := by
  apply MixedProduct.VariableWord.refines_of_syntactic_components
    (thin f hNoUp S hnd hsub hvector fallback) f
  · exact thin_syntactic_components f hNoUp S hnd hsub hvector fallback
  · intro i
    exact False.elim (hNoUp i.1 i.2)

/-- C-goodness of the actual original full span is inherited by the
constructed support thinning for the same colouring. -/
theorem thin_good
    {γ : Type*}
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β)
    (color : Element b n d β kind → γ)
    (hgood : Good color f) :
    Good color (thin f hNoUp S hnd hsub hvector fallback) :=
  MixedProduct.good_of_refines hgood
    (thin_refines f hNoUp S hnd hsub hvector fallback)

/-- A supplied complete vector of smaller supports yields a genuine
c-good mixed refinement with exactly those supports and explicit
coordinatewise syntactic refinements.  The geometric support selection
and the original c-good word remain supplied inputs. -/
theorem exists_good_thinning
    {γ : Type*}
    (f : MixedProduct.VariableWord b n d H β aux kind)
    (hNoUp : ∀ i, kind i ≠ CoordKind.up)
    (S : Fin d → List (BoundedNode b n))
    (hnd : ∀ i, (S i).Nodup)
    (hsub : ∀ i t, t ∈ S i → t ∈ (f.vector.components i).support)
    (hvector : VectorSkew.vectorCompleteB aux q
      (fun i => (S i).map Subtype.val) = true)
    (fallback : β)
    (color : Element b n d β kind → γ)
    (hgood : Good color f) :
    ∃ g : MixedProduct.VariableWord b n d q β aux kind,
      (∀ i, (g.vector.components i).support = S i) ∧
      (∀ i, KVariableWord.SyntacticRefines
        (g.vector.components i) (f.vector.components i)) ∧
      MixedProduct.VariableWord.Refines g f ∧ Good color g := by
  exact ⟨thin f hNoUp S hnd hsub hvector fallback,
    thin_support f hNoUp S hnd hsub hvector fallback,
    thin_syntactic_components f hNoUp S hnd hsub hvector fallback,
    thin_refines f hNoUp S hnd hsub hvector fallback,
    thin_good f hNoUp S hnd hsub hvector fallback color hgood⟩

end DualTree.MixedSupportThinning
