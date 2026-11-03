import DualTree.PlainBlockBulletBlockExactSpan

/-!
# Exact colour factorization on the nonvacuous p-D₀/q-D₂ mixed span

For a genuine intrinsic-height-one mixed variable word with p ordinary
coordinates followed by q marked coordinates, the verified exact-span
parametrization shows that Definition 11 c-goodness is EQUIVALENT to
constancy on each fibre of the independently observed q-letter tuple.

Unlike a one-sided implication from uniform Hales–Jewett colours,
the converse here uses actual membership of every parameter element in
the source-facing mixed span. Every c-good colouring therefore has a
unique total factor through its q observed letters, including p=0
and q=0. The result makes NO claim of equality between different
q-tuples, and does not cover D₁, higher intrinsic dimension, arbitrary
coordinate interleavings, or the full dual-tree theorem.
-/

namespace DualTree.PlainBlockBulletBlock

open DualTree.MixedProduct
open DualTree.FlatVectorHalesJewett

/-- The q independently observed marked letters of a genuine
p-D₀/q-D₂ mixed-product element. The actual D₂ point is used;
it is not replaced by a preselected root at the definition level. -/
def markerTuple
    {b N p q : Nat} {β : Type*}
    (x : Element b (N + 1) (p + q) β (kind p q)) :
    Fin q → β :=
  fun j =>
    x.words (bulletIndex p q j).1
      (x.bulletPoint (bulletIndex p q j))

/-- All marked observations of a canonical parameter element
recover exactly the independent q-tuple used to build it. -/
theorem markerTuple_parameterElement
    {b N p q : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (u : Fin p → Fin N → β) (a : Fin q → β) :
    markerTuple (parameterElement hb fallback u a) = a := by
  funext j
  change
    (parameterElement hb fallback u a).words (bulletIndex p q j).1
      ((parameterElement hb fallback u a).bulletPoint
        (bulletIndex p q j)) = a j
  simpa only [bulletCoordinate_bulletIndex] using
    (parameterElement_bullet_letter
      hb fallback u a (bulletIndex p q j))

/-- Exact Definition-11 c-goodness is equivalent to colour
constancy along the genuine parameter fibres. Both implications
are about ACTUAL mixed-product span elements. The forward
direction needs the converse span-membership lemma, preventing
a vacuous colour-canonization argument. -/
theorem good_iff_uniform_flat_vector
    {b N p q : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) (p + q) β (kind p q) → γ) :
    Good color (mixedWord hb w fallback r hroot hfirst q) ↔
      ∀ σ τ : Fin p → Fin 1 → β, ∀ a : Fin q → β,
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (σ i)) a) =
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (τ i)) a) := by
  constructor
  · intro hgood σ τ a
    let uσ : Fin p → Fin N → β :=
      fun i => SpanAudit.eval (coordinateWord w i) (σ i)
    let uτ : Fin p → Fin N → β :=
      fun i => SpanAudit.eval (coordinateWord w i) (τ i)
    have hx :
        parameterElement hb fallback uσ a ∈
          (mixedWord hb w fallback r hroot hfirst q).span :=
      parameterElement_mem_span hb w fallback r hroot hfirst σ a
    have hy :
        parameterElement hb fallback uτ a ∈
          (mixedWord hb w fallback r hroot hfirst q).span :=
      parameterElement_mem_span hb w fallback r hroot hfirst τ a
    apply hgood hx hy
    · intro i
      rfl
    · intro i
      exact
        (parameterElement_bullet_letter hb fallback uσ a i).trans
          (parameterElement_bullet_letter hb fallback uτ a i).symm
  · exact mixedWord_good_of_uniform_flat_vector
      hb w fallback r hroot hfirst color

/-- Total factorization through q observed D₂ letters is
EQUIVALENT to actual c-goodness on the full genuine mixed span.
Existence of the factor is obtained by evaluating at the
fallback assignment for all p ordinary coordinates. -/
theorem good_iff_factors_through_markerTuple
    {b N p q : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) (p + q) β (kind p q) → γ) :
    Good color (mixedWord hb w fallback r hroot hfirst q) ↔
      ∃ F : (Fin q → β) → γ,
        ∀ x : Element b (N + 1) (p + q) β (kind p q),
          x ∈ (mixedWord hb w fallback r hroot hfirst q).span →
            color x = F (markerTuple x) := by
  constructor
  · intro hgood
    let σ₀ : Fin p → Fin 1 → β := fun _ _ => fallback
    let F : (Fin q → β) → γ :=
      fun a =>
        color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (σ₀ i)) a)
    refine ⟨F, ?_⟩
    intro x hx
    obtain ⟨σ, a, hxrep⟩ :=
      span_element_eq_parameterElement
        hb w fallback r hroot hfirst x hx
    have hequal :=
      (good_iff_uniform_flat_vector
        hb w fallback r hroot hfirst color).mp hgood σ σ₀ a
    have htuple : markerTuple x = a := by
      rw [hxrep]
      exact markerTuple_parameterElement hb fallback
        (fun i => SpanAudit.eval (coordinateWord w i) (σ i)) a
    calc
      color x = color (parameterElement hb fallback
          (fun i => SpanAudit.eval (coordinateWord w i) (σ i)) a) :=
        congrArg color hxrep
      _ = F a := hequal
      _ = F (markerTuple x) := by rw [htuple]
  · rintro ⟨F, hF⟩ x y hx hy _ hletters
    have htuple : markerTuple x = markerTuple y := by
      funext j
      exact hletters (bulletIndex p q j)
    calc
      color x = F (markerTuple x) := hF x hx
      _ = F (markerTuple y) := congrArg F htuple
      _ = color y := (hF y hy).symm

/-- The factor on q tuples is unique, since every q tuple
is genuinely realized in the nonempty mixed span (even when
p or q is zero). This is stronger than arbitrary factorization
on a possibly proper subset of a parameter space. -/
theorem markerTuple_factor_unique
    {b N p q : Nat} {β γ : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin p → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (N + 1) (p + q) β (kind p q) → γ)
    (F G : (Fin q → β) → γ)
    (hF : ∀ x, x ∈ (mixedWord hb w fallback r hroot hfirst q).span →
      color x = F (markerTuple x))
    (hG : ∀ x, x ∈ (mixedWord hb w fallback r hroot hfirst q).span →
      color x = G (markerTuple x)) :
    F = G := by
  funext a
  let σ₀ : Fin p → Fin 1 → β := fun _ _ => fallback
  let x : Element b (N + 1) (p + q) β (kind p q) :=
    parameterElement hb fallback
      (fun i => SpanAudit.eval (coordinateWord w i) (σ₀ i)) a
  have hx : x ∈ (mixedWord hb w fallback r hroot hfirst q).span :=
    parameterElement_mem_span hb w fallback r hroot hfirst σ₀ a
  have htuple : markerTuple x = a :=
    markerTuple_parameterElement hb fallback
      (fun i => SpanAudit.eval (coordinateWord w i) (σ₀ i)) a
  calc
    F a = color x := by simpa only [htuple] using (hF x hx).symm
    _ = G a := by simpa only [htuple] using (hG x hx)

end DualTree.PlainBlockBulletBlock
