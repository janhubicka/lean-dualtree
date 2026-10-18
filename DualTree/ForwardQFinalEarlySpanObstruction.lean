import DualTree.ForwardQFinalWholeDomainEvaluation
import DualTree.ForwardQAmbientFibreSymbol

/-!
# An adversarial obstruction to the WRONG reverse Q/f' span covering

The previous theorem proves an evaluated corrected-Q output lies in the
final f' span when its retained variables are anchored to the
fixed source refinement g' = f[rho]. This does not imply that
EVERY evaluation in span(f') is obtained by some Q(x) evaluation.

If the source substitution rho identifies two DIFFERENT original
ambient f-variable roots at/before the corrected cut, the actual
fibrewise Q is necessarily constant across those two positions
under EVERY enlarged mixed input and EVERY old source assignment.
But the completed final ambient f' retains BOTH original roots as
independent variables. Over an alphabet with two distinct letters,
f' admits an evaluation assigning distinct values to these roots.

Hence under this precise source-relative hypothesis there exists
an actual evaluated final f' word outside ALL evaluated fibrewise
Q-images. This is a conditional NONCOVERAGE theorem, not a
counterexample to the Ramsey statement; the Ramsey proof may
require a smaller class of refinements, or a different f' support
choice. The inclusion DIRECTION must be checked explicitly.
-/

namespace DualTree.ForwardQFinalEarlySpanObstruction

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalEarlyFibreAssignment

/-- If two DISTINCT retained original f-variable roots have
the same image under the fixed source refinement rho,
the full evaluated span of the constructed f' CANNOT be
covered by the union of evaluated ACTUAL fibrewise Q words.
The obstruction holds even when the mixed input ranges over
the whole enlarged mixed-product space, not just W_*.

The two-letter assumption is essential to detect the lost
independence: over a singleton alphabet all evaluated
variable-word spans can collapse. -/
theorem not_every_final_evaluation_is_Q_evaluation
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (hα : SpanAudit.HasTwoLetters α)
    (u v : g.ambient.Vars)
    (hu : ForwardAux u.1.1 g.core.cut)
    (hv : ForwardAux v.1.1 g.core.cut)
    (hne : u.1 ≠ v.1)
    (hcollapse : g.substitution u = g.substitution v) :
    ∃ ψ : TreeWord b n α,
      ψ ∈ (interpolatedFinalWord g f
        (fun a : α => a) fallback).span ∧
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedInput g.core)
        (τ : g.core.source.word.Vars → α),
        SpanAudit.eval
          (ForwardQAmbientFibreSymbol.fibreQSymbol
            g fallback w) τ ≠ ψ := by
  classical
  obtain ⟨a₀,a₁,hab⟩ := hα
  let ru := earlyFinalRoot g f u hu
  let rv := earlyFinalRoot g f v hv
  have hneRoot : ru ≠ rv := by
    intro heq
    have heqVal : ru.1 = rv.1 := congrArg Subtype.val heq
    have huv : u.1 = v.1 := by
      calc
        u.1 = ru.1 := (earlyFinalRoot_val g f u hu).symm
        _ = rv.1 := heqVal
        _ = v.1 := earlyFinalRoot_val g f v hv
    exact hne huv
  let σ : FinalRoot g f → α := fun r => if r = ru then a₀ else a₁
  let ψ : TreeWord b n α :=
    (interpolatedFinalWord g f
      (fun t : α => t) fallback).eval σ
  have hfu :
      (interpolatedFinalWord g f
        (fun t : α => t) fallback).word u.1 = Sum.inr ru := by
    change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f (fun t : α => t) fallback) u.1 =
      Sum.inr ru
    simp [SpanAudit.substitute,g.ambient.atRoot u,
      globalRootSymbol_early g f
        (fun t : α => t) fallback u hu,ru]
  have hfv :
      (interpolatedFinalWord g f
        (fun t : α => t) fallback).word v.1 = Sum.inr rv := by
    change SpanAudit.substitute g.ambient.word
      (globalRootSymbol g f (fun t : α => t) fallback) v.1 =
      Sum.inr rv
    simp [SpanAudit.substitute,g.ambient.atRoot v,
      globalRootSymbol_early g f
        (fun t : α => t) fallback v hv,rv]
  have hψu : ψ u.1 = a₀ := by
    change SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f
        (fun t : α => t) fallback).word u.1) = a₀
    rw [hfu]
    simp [SpanAudit.evalSymbol,σ]
  have hψv : ψ v.1 = a₁ := by
    change SpanAudit.evalSymbol σ
      ((interpolatedFinalWord g f
        (fun t : α => t) fallback).word v.1) = a₁
    rw [hfv]
    simp [SpanAudit.evalSymbol,σ,hneRoot.symm]
  refine ⟨ψ,⟨σ,rfl⟩,?_⟩
  intro w τ heq
  have hQu :
      ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w u.1 = g.substitution u := by
    rw [ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback w u.1 u (g.ambient.atRoot u) hu]
    rw [g.source_substitution]
    simp [SpanAudit.substitute,g.ambient.atRoot u]
  have hQv :
      ForwardQAmbientFibreSymbol.fibreQSymbol
        g fallback w v.1 = g.substitution v := by
    rw [ForwardQAmbientFibreSymbol.fibreQ_before_cut
      g fallback w v.1 v (g.ambient.atRoot v) hv]
    rw [g.source_substitution]
    simp [SpanAudit.substitute,g.ambient.atRoot v]
  have hQequal :
      SpanAudit.eval
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w) τ u.1 =
      SpanAudit.eval
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w) τ v.1 := by
    change SpanAudit.evalSymbol τ
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w u.1) =
      SpanAudit.evalSymbol τ
        (ForwardQAmbientFibreSymbol.fibreQSymbol
          g fallback w v.1)
    rw [hQu,hQv,hcollapse]
  have hcontradiction : a₀ = a₁ := by
    calc
      a₀ = ψ u.1 := hψu.symm
      _ = SpanAudit.eval
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w) τ u.1 := (congrFun heq u.1).symm
      _ = SpanAudit.eval
            (ForwardQAmbientFibreSymbol.fibreQSymbol
              g fallback w) τ v.1 := hQequal
      _ = ψ v.1 := congrFun heq v.1
      _ = a₁ := hψv
  exact hab hcontradiction

end DualTree.ForwardQFinalEarlySpanObstruction
