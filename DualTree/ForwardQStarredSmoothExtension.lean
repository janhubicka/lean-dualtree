import DualTree.ForwardQStarredSmoothConePatches
import DualTree.SmoothRelation

/-!
# Exact smooth-colouring extension criterion on actual corrected W-star

The corrected forward-Q input subtype W_* is a genuine set of
mixed-product elements satisfying the canonical selected D₂
vector-one-completeness condition. The SmoothRelated Gamma₂
relation is defined on all mixed-product elements.

The existing general partial-colouring extension theorem applies to
this precise W_* subtype: a colouring of actual starred inputs extends
to a total Gamma₂-smooth colouring of the whole mixed product if
and only if it is already constant on SmoothRelated pairs *inside*
W_*. This condition is the sole extension obstruction; smoothness
cannot be inferred from the fact that a colouring is written c ∘ Q.

The equivalence below is useful in the eventual colouring-pullback
step of Lemma 27 but DOES NOT prove the actual induced colouring is
classwise compatible. A separately checked example shows that
remembering a letter at a marked point can violate smoothness.
-/

namespace DualTree.ForwardQStarredSmoothExtension

open ForwardSourceQTree

/-- Restriction of an already total Gamma₂-smooth colouring to the
actual corrected starred W_* subtype is classwise compatible. -/
theorem smooth_starred_of_total_extension
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (total : Input c → γ)
    (hagree : ∀ x : ForwardQActualStarredSpace.StarredInput c,
      total x.1 = color x)
    (htotal : ∀ (x y : Input c),
      MixedProduct.SmoothRelated (fun _ => false) x y →
      total x = total y) :
    ForwardQStarredSmoothConePatches.SmoothStarredColor c color := by
  intro x y hxy
  calc
    color x = total x.1 := (hagree x).symm
    _ = total y.1 := htotal x.1 y.1 hxy
    _ = color y := hagree y

/-- Every colouring compatible with Gamma₂ smoothness on the
ACTUAL corrected starred subtype extends to a total smooth
colouring, with an arbitrary prescribed fallback colour. -/
theorem exists_total_smooth_extension_of_smooth_starred
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (fallback : γ)
    (hsmooth :
      ForwardQStarredSmoothConePatches.SmoothStarredColor c color) :
    ∃ total : Input c → γ,
      (∀ x : ForwardQActualStarredSpace.StarredInput c,
        total x.1 = color x) ∧
      (∀ x y : Input c,
        MixedProduct.SmoothRelated (fun _ => false) x y →
        total x = total y) := by
  let D : Set (Input c) :=
    {x | ForwardQActualStarredSpace.IsStarred c x}
  have hcompat :
      ∀ (x y : Input c) (hx : x ∈ D) (hy : y ∈ D),
        MixedProduct.SmoothRelated (fun _ => false) x y →
        (fun z : {z : Input c // z ∈ D} =>
          color ⟨z.1, z.2⟩) ⟨x, hx⟩ =
        (fun z : {z : Input c // z ∈ D} =>
          color ⟨z.1, z.2⟩) ⟨y, hy⟩ := by
    intro x y hx hy hrel
    exact hsmooth ⟨x, hx⟩ ⟨y, hy⟩ hrel
  obtain ⟨total, hmatch, htotal⟩ :=
    MixedProduct.exists_smooth_extension (fun _ => false)
      D (fun z : {z : Input c // z ∈ D} =>
        color ⟨z.1, z.2⟩) fallback hcompat
  refine ⟨total, ?_, htotal⟩
  intro x
  simpa [D] using hmatch x.1 x.2

/-- A colouring of actual W_* has a total Gamma₂-smooth extension
if and only if it is compatible on its starred smoothness classes.
This equivalence identifies the precise remaining condition
needed for the particular Lemma 27 induced colouring. -/
theorem total_smooth_extension_iff_starred_smooth
    {b n l k m : Nat} {α γ : Type*}
    (c : Frame b n l k m α)
    (color : ForwardQActualStarredSpace.StarredInput c → γ)
    (fallback : γ) :
    (∃ total : Input c → γ,
      (∀ x : ForwardQActualStarredSpace.StarredInput c,
        total x.1 = color x) ∧
      (∀ x y : Input c,
        MixedProduct.SmoothRelated (fun _ => false) x y →
        total x = total y)) ↔
      ForwardQStarredSmoothConePatches.SmoothStarredColor c color := by
  constructor
  · rintro ⟨total, hagree, htotal⟩
    exact smooth_starred_of_total_extension
      c color total hagree htotal
  · intro hsmooth
    exact exists_total_smooth_extension_of_smooth_starred
      c color fallback hsmooth

end DualTree.ForwardQStarredSmoothExtension
