import DualTree.ForwardQVisibleRootCapacity
import DualTree.SpanAudit

/-!
# Loss of evaluated span under non-injective cone-variable transport

A legal Q word may translate genuine local cone variables to old
source-variable roots in the actual visible chain. The finite
visible-root bound can force distinct local variable names to be
identified. That does not affect mere root-aligned word validity,
but over an alphabet with TWO letters it strictly loses some
evaluated assignments whenever both names actually occur.

We first prove this algebraically for any word w and variable-name
substitution rho which identifies two genuinely occurring source
names. Then we apply the SOURCE-FACING m+2 versus m+1 capacity
theorem at a genuine corrected complete-support frontier:
if all m+2 local names occur and rho sends each name to its
assigned old source root, the full raw cone-word span CANNOT be
contained in the smaller transported-word span.

The conclusion is intentionally conditional on the two-letter
enlarged local alphabet and all names actually occurring. It is
not a counterexample to the final dual-tree Ramsey theorem; it
rules out silently claiming preservation of that full local
Hales-Jewett variable span under a forced name identification.
-/

namespace DualTree.ForwardQVariableSpanCollapse

/-- Whenever two DISTINCT source variable names both occur and a
substitution identifies their images, the original two-letter
evaluated span cannot be covered by the substituted span. -/
theorem original_span_not_subset_of_collapsed_span
    {ι κ ν α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (w : ι → Sum α κ)
    (ρ : κ → Sum α ν)
    (i j : ι)
    (u v : κ)
    (huv : u ≠ v)
    (hui : w i = Sum.inr u)
    (hvj : w j = Sum.inr v)
    (hcollapse : ρ u = ρ v) :
    ¬ SpanAudit.span w ⊆
      SpanAudit.span (SpanAudit.substitute w ρ) := by
  intro hreverse
  rcases hα with ⟨a, b, hab⟩
  let σ : κ → α := fun z => if z = u then a else b
  have hσ : SpanAudit.eval w σ ∈ SpanAudit.span w := ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := hreverse hσ
  have hfirst : SpanAudit.eval w σ i = a := by
    simp [SpanAudit.eval, SpanAudit.evalSymbol, σ, hui]
  have hsecond : SpanAudit.eval w σ j = b := by
    simp [SpanAudit.eval, SpanAudit.evalSymbol, σ, hvj, huv.symm]
  have hsame :
      SpanAudit.eval (SpanAudit.substitute w ρ) τ i =
        SpanAudit.eval (SpanAudit.substitute w ρ) τ j := by
    simp [SpanAudit.eval, SpanAudit.substitute, hui, hvj, hcollapse]
  have hab' : a = b := by
    calc
      a = SpanAudit.eval w σ i := hfirst.symm
      _ = SpanAudit.eval (SpanAudit.substitute w ρ) τ i :=
        (congrFun hτ i).symm
      _ = SpanAudit.eval (SpanAudit.substitute w ρ) τ j := hsame
      _ = SpanAudit.eval w σ j := congrFun hτ j
      _ = b := hsecond
  exact hab hab'

/-- The substituted evaluated span is always contained in the
original span, but the reverse inclusion fails under the
two-distinct-occurring-variables collapse hypothesis. -/
theorem collapsed_span_properly_contained
    {ι κ ν α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (w : ι → Sum α κ)
    (ρ : κ → Sum α ν)
    (i j : ι)
    (u v : κ)
    (huv : u ≠ v)
    (hui : w i = Sum.inr u)
    (hvj : w j = Sum.inr v)
    (hcollapse : ρ u = ρ v) :
    SpanAudit.span (SpanAudit.substitute w ρ) ⊆
        SpanAudit.span w ∧
      ¬ SpanAudit.span w ⊆
        SpanAudit.span (SpanAudit.substitute w ρ) :=
  ⟨SpanAudit.span_substitute_subset w ρ,
    original_span_not_subset_of_collapsed_span
      hα w ρ i j u v huv hui hvj hcollapse⟩

open ForwardSourceQTree
open ForwardQVisibleAncestorDecoder
open ForwardQConeVariableVisibility

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- For a genuine corrected Q frontier containing m+2 actually
occurring distinct local cone variables, the old-source-root
capacity obstruction forces TWO NAMES to have the same image.
The FULL local raw-word span is therefore NOT contained in the
span of the root-translated word. Auxiliary symbols count as
constants here, exactly as in the enlarged source alphabet. -/
theorem actual_frontier_full_span_not_preserved
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (raw : Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) (Fin (m + 2)))
    (coneRoot : Index c → Fin (m + 2) → c.source.word.Vars)
    (hβ : SpanAudit.HasTwoLetters (Sum α (Fin (m + 1))))
    (hocc : ∀ z : Fin (m + 2),
      ∃ t : BoundedNode b n,
        IsPrefix
          (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 ∧
        raw i t = Sum.inr z)
    (halign : ∀ (j : Index c) (t : BoundedNode b n)
      (z : Fin (m + 2)),
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 t.1 →
      raw j t = Sum.inr z →
      IsPrefix (coneRoot j z).1.1 t.1) :
    ¬ SpanAudit.span (raw i) ⊆
      SpanAudit.span
        (SpanAudit.substitute (raw i)
          (fun z => (Sum.inr (coneRoot i z) :
            Sum (Sum α (Fin (m + 1))) c.source.word.Vars))) := by
  have hnot :
      ¬ Function.Injective (coneRoot i) :=
    ForwardQVisibleRootCapacity.no_injective_coneRoot_of_all_variables_occurring
      c i raw coneRoot hocc halign
  have htwo :
      ∃ u v : Fin (m + 2), u ≠ v ∧
        coneRoot i u = coneRoot i v := by
    by_contra hn
    apply hnot
    intro u v huv
    by_contra hne
    exact hn ⟨u, v, hne, huv⟩
  rcases htwo with ⟨u, v, huv, heq⟩
  obtain ⟨tu, _htu, hrawu⟩ := hocc u
  obtain ⟨tv, _htv, hrawv⟩ := hocc v
  exact original_span_not_subset_of_collapsed_span
    hβ (raw i)
    (fun z => (Sum.inr (coneRoot i z) :
      Sum (Sum α (Fin (m + 1))) c.source.word.Vars))
    tu tv u v huv hrawu hrawv (congrArg Sum.inr heq)

end DualTree.ForwardQVariableSpanCollapse
