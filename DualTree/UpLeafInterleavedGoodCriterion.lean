import DualTree.UpLeafInterleavedCanonical

/-!
# Exact Definition-11 Good criterion on genuine interleaved D₀/D₁/D₂ spans

For the verified height-one interleaved mixed word, the full span has
independently variable D₀ substitutions, D₁ root letters, D₁ directions,
and D₂ root letters. The latter are the *only* observations retained by
Definition 11.

We prove an if-and-only-if: Good is precisely invariance under changes
of all D₀/D₁ parameters while fixing the D₂ letters. The proof uses
both directions of the kernel-verified exact mixed-span parametrization.

We also exhibit the precise separation from Lemma-14 UpCanonical:
colouring by one genuine D₁ leaf is always UpCanonical, but for b>=2
it is not Good on this mixed span. This is a counterexample to
mistakenly treating the Lemma-14 conclusion as Definition-11 Good,
NOT a counterexample to the ambient-height Ramsey theorem.
-/

namespace DualTree.UpLeafInterleavedGoodCriterion

open DualTree.MixedProduct
open DualTree.InterleavedFlatHalesJewett
open DualTree.UpLeafInterleavedParameters
open DualTree.UpLeafInterleavedSpan
open DualTree.ShiftedRaySlots

/-- Every marked D₂ coordinate is an actual nonplain coordinate. -/
def bulletAsNonplain {d : Nat}
    (kind : Fin d → CoordKind) (i : BulletIndex kind) :
    NonplainIndex kind :=
  ⟨i.1, by
    intro hp
    have hbullet : kind i.1 = CoordKind.bullet := i.2
    rw [hp] at hbullet
    cases hbullet⟩

/-- The D₂ observation is literally its own independently selected
marked-root letter, not a global default. -/
theorem parameterElement_bullet_letter
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (fallback : β) (u : PlainIndex kind → Fin N → β)
    (a : NonplainIndex kind → β)
    (directions : UpIndex kind → Fin b)
    (i : BulletIndex kind) :
    (parameterElement hb kind fallback u a directions).words i.1
      ((parameterElement hb kind fallback u a directions).bulletPoint i) =
        a (bulletAsNonplain kind i) := by
  exact parameterElement_nonplain_root_letter
    hb kind fallback u a directions (bulletAsNonplain kind i)

/-- Source Definition 11 on the TRUE height-one mixed span holds
exactly when the parameter colour ignores every D₀ substitution and
every D₁ letter/direction, keeping only the independent D₂ letters.

This is a criterion, not unconditional existence of a Good word. -/
theorem good_iff_parameter_bullet_constancy
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ) :
    Good color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst) ↔
      ∀ (σ τ : PlainIndex kind → Fin 1 → β)
        (a a' : NonplainIndex kind → β)
        (directions directions' : UpIndex kind → Fin b),
        (∀ i : BulletIndex kind,
          a (bulletAsNonplain kind i) =
            a' (bulletAsNonplain kind i)) →
          color (parameterElement hb kind fallback
            (fun i => SpanAudit.eval (project w i) (σ i)) a directions) =
          color (parameterElement hb kind fallback
            (fun i => SpanAudit.eval (project w i) (τ i)) a' directions') := by
  constructor
  · intro hgood σ τ a a' directions directions' hletter
    apply hgood
      (parameterElement_mem_span hb kind w fallback
        r hroot hfirst σ a directions)
      (parameterElement_mem_span hb kind w fallback
        r hroot hfirst τ a' directions')
    · intro i
      rfl
    · intro i
      calc
        (parameterElement hb kind fallback
            (fun j => SpanAudit.eval (project w j) (σ j)) a directions).words i.1
            ((parameterElement hb kind fallback
              (fun j => SpanAudit.eval (project w j) (σ j)) a directions).bulletPoint i) =
            a (bulletAsNonplain kind i) :=
          parameterElement_bullet_letter hb kind fallback
            (fun j => SpanAudit.eval (project w j) (σ j)) a directions i
        _ = a' (bulletAsNonplain kind i) := hletter i
        _ = (parameterElement hb kind fallback
            (fun j => SpanAudit.eval (project w j) (τ j)) a' directions').words i.1
            ((parameterElement hb kind fallback
              (fun j => SpanAudit.eval (project w j) (τ j)) a' directions').bulletPoint i) :=
          (parameterElement_bullet_letter hb kind fallback
            (fun j => SpanAudit.eval (project w j) (τ j)) a' directions' i).symm
  · intro hconst x y hx hy _ hletters
    rcases span_element_eq_parameterElement hb kind w fallback
      r hroot hfirst x hx with ⟨σ, a, directions, rfl⟩
    rcases span_element_eq_parameterElement hb kind w fallback
      r hroot hfirst y hy with ⟨τ, a', directions', rfl⟩
    apply hconst σ τ a a' directions directions'
    intro i
    have hl := parameterElement_bullet_letter hb kind fallback
      (fun j => SpanAudit.eval (project w j) (σ j)) a directions i
    have hr := parameterElement_bullet_letter hb kind fallback
      (fun j => SpanAudit.eval (project w j) (τ j)) a' directions' i
    exact hl.symm.trans ((hletters i).trans hr)

/-- Colouring by one actual D₁ leaf is automatically Lemma-14
canonical: its value is explicitly part of SameUpTrace. -/
theorem upPoint_color_upCanonical
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β) (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : UpIndex kind) :
    UpCanonical
      (fun x : Element b (ambient d N) d β kind => x.upPoint i)
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst) := by
  intro x y _ _ htrace
  exact htrace.1 i

/-- At branching at least two, changing a genuine D₁ direction
changes this colour without changing ANY D₂ observation. Hence the
explicit canonical colour is NOT Good on this same full mixed span. -/
theorem upPoint_color_not_good
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (hbranch : 1 < b)
    (kind : Fin d → CoordKind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β) (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : UpIndex kind) :
    ¬ Good
      (fun x : Element b (ambient d N) d β kind => x.upPoint i)
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst) := by
  intro hgood
  let σ : PlainIndex kind → Fin 1 → β := fun _ _ => fallback
  let a : NonplainIndex kind → β := fun _ => fallback
  let j0 : Fin b := ⟨0, hb⟩
  let j1 : Fin b := ⟨1, hbranch⟩
  let directions0 : UpIndex kind → Fin b := fun _ => j0
  let directions1 : UpIndex kind → Fin b := fun _ => j1
  have hcolors :=
    (good_iff_parameter_bullet_constancy hb kind w fallback
      r hroot hfirst
      (fun x : Element b (ambient d N) d β kind => x.upPoint i)).1
      hgood σ σ a a directions0 directions1 (by intro _; rfl)
  change UpLeafGeometry.ambientLeaf hb
      (InterleavedMixedWord.markerPos (N := N) hb i.1) (directions0 i) =
    UpLeafGeometry.ambientLeaf hb
      (InterleavedMixedWord.markerPos (N := N) hb i.1) (directions1 i)
    at hcolors
  have heq : j0 = j1 :=
    (UpLeafGeometry.ambientLeaf_injective hb
      (InterleavedMixedWord.markerPos (N := N) hb i.1)) hcolors
  have hnum := congrArg Fin.val heq
  change (0 : Nat) = 1 at hnum
  omega

end DualTree.UpLeafInterleavedGoodCriterion
