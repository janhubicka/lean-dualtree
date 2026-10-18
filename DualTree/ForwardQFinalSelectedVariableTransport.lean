import DualTree.ForwardQFinalAmbientRootLift

/-!
# Transporting actual local variables to selected final ambient roots

The final corrected Lemma 27 support now has an exact bounded
ambient-root list. The next step towards the prescribed ambient f'
is to preserve the distinct identities of local variables from
different frontier coordinates.

The jointly injective original projection (i,z) ↦ P_i(z) maps every
rank-budget-selected local variable to one of those bounded final
roots. The resulting map is still injective after converting into
the bounded and proof-carrying ambient-root types.

Moreover, if a genuine local component variable v occurs at z,
its local root is a prefix of z. For a selected variable root,
the corresponding GLOBAL final root P_i(v) is therefore a prefix
of the original complete-T position P_i(z). This is precisely
the nontrivial "below" side condition needed by a Q-compatible
root-substitution certificate.

No last-level excluded local variable is silently included;
it requires a separate constantization choice. This module
does NOT construct the prescribed global f' symbol function yet.
-/

namespace DualTree.ForwardQFinalSelectedVariableTransport

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift

/-- Only rank-budgeted actual component variable roots get
names in the final ambient variable word. -/
abbrev SelectedTag
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :=
  {u : LocalAddress g.core //
    u ∈ selectedLocalRoots g.core f (m+q)}

/-- Actual selected local tags map to the desired bounded final-root
list via the genuine, jointly injective projection into T. -/
noncomputable def selectedBoundedRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : SelectedTag g f) :
    {t : BoundedNode b n // t ∈ boundedFinalRoots g f} := by
  let r : BoundedNode b n :=
    ⟨(projected g.core u.1).1,
      g.T_bounded _ (projected g.core u.1).2⟩
  refine ⟨r, ?_⟩
  apply (mem_boundedFinalRoots_iff g f r).2
  change (projected g.core u.1).1 ∈
    retained g.core ∪ selectedProjectedRoots g.core f (m+q)
  apply Finset.mem_union.mpr
  right
  change (projected g.core u.1).1 ∈
    (selectedLocalRoots g.core f (m+q)).image
      (fun v => (projected g.core v).1)
  exact Finset.mem_image.mpr ⟨u.1, u.2, rfl⟩

/-- Exact raw-tree identity of the selected bounded root. -/
theorem selectedBoundedRoot_node
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : SelectedTag g f) :
    (selectedBoundedRoot g f u).1.1 =
      (projected g.core u.1).1 := rfl

/-- Distinct genuinely selected local variables, including those
using the same local name in DIFFERENT frontier coordinates,
map to distinct bounded global variable roots. -/
theorem selectedBoundedRoot_injective
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    Function.Injective (selectedBoundedRoot g f) := by
  intro u v heq
  have hnode :
      (projected g.core u.1).1 = (projected g.core v.1).1 := by
    calc
      (projected g.core u.1).1 =
        (selectedBoundedRoot g f u).1.1 :=
          (selectedBoundedRoot_node g f u).symm
      _ = (selectedBoundedRoot g f v).1.1 :=
          congrArg (fun t : {s : BoundedNode b n //
            s ∈ boundedFinalRoots g f} => t.1.1) heq
      _ = (projected g.core v.1).1 :=
          selectedBoundedRoot_node g f v
  have hproj :
      projected g.core u.1 = projected g.core v.1 :=
    Subtype.ext hnode
  exact Subtype.ext
    ((projected_injective g.core) hproj)

/-- Every selected new root is also a genuine variable root of
the ORIGINAL ambient word f, not a free-standing fresh name. -/
noncomputable def selectedAmbientRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : SelectedTag g f) :
    g.ambient.Vars :=
  ⟨(selectedBoundedRoot g f u).1,
    boundedFinalRoots_subset_original g f
      (selectedBoundedRoot g f u)⟩

/-- Raw support position of the original ambient variable
named by an actual selected local tag. -/
theorem selectedAmbientRoot_node
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : SelectedTag g f) :
    (selectedAmbientRoot g f u).1.1 =
      (projected g.core u.1).1 :=
  selectedBoundedRoot_node g f u

/-- Selected local names remain distinct when regarded as
original ambient-variable roots. No auxiliary-name Hall
identification is introduced at this stage. -/
theorem selectedAmbientRoot_injective
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :
    Function.Injective (selectedAmbientRoot g f) := by
  intro u v heq
  have hBounded :
      selectedBoundedRoot g f u =
        selectedBoundedRoot g f v := by
    apply Subtype.ext
    exact congrArg Subtype.val heq
  exact selectedBoundedRoot_injective g f hBounded

/-- The original ambient word really emits its own variable
at the selected local root's projected position. -/
theorem selectedAmbientRoot_atRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (u : SelectedTag g f) :
    g.ambient.word (selectedAmbientRoot g f u).1 =
      Sum.inr (selectedAmbientRoot g f u) :=
  g.ambient.atRoot (selectedAmbientRoot g f u)

/-- Any selected local variable v occurring at a local
coordinate z has its projected FINAL root as an ambient
prefix of the original complete-T position P_i(z).
This is the concrete root-compatibility condition for
the upcoming interpolating substitution. -/
theorem selected_local_variable_prefix_projected
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (i : Index g.core)
    (v : (f.vector.components i).Vars)
    (z : BoundedNode b (k-(m+1)))
    (hword : (f.vector.components i).word z = Sum.inr v)
    (hselected :
      (⟨i,v.1⟩ : LocalAddress g.core) ∈
        selectedLocalRoots g.core f (m+q)) :
    IsPrefix
      (selectedBoundedRoot g f ⟨⟨i,v.1⟩,hselected⟩).1.1
      (projected g.core ⟨i,z⟩).1 := by
  have hlocal : IsPrefix v.1.1 z.1 :=
    (f.vector.components i).toVariableWord.below v z hword
  simpa only [selectedBoundedRoot_node] using
    (projected_same_frontier_prefix g.core i v.1 z hlocal)

end DualTree.ForwardQFinalSelectedVariableTransport
