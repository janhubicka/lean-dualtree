import DualTree.ForwardQFinalUnsafeFibreFallback

/-!
# Full evaluated corrected-Q versus f' equality under the RIGHT anchoring

The genuine fibrewise corrected Q is computed from a canonical
mixed-product point x_sigma in the actual post-Ramsey mixed-word
span and its corrected starred W_* subtype. The genuine f'
ambient variable word has exactly the rank-filtered complete-skew
final support and evaluated span inside the original ambient f.

A FALSE statement would be Q(x_sigma) evaluated under arbitrary
old-root assignment tau = f' evaluated under ARBITRARY independent
sigma: on the early original f-fibres, Q uses fixed g'=f[rho].

The proper statement uses a final assignment sigma that agrees
with eval(rho,tau) on retained (pre-cut) original f-roots and
is otherwise entirely free. This anchors only OLD retained roots
and preserves all selected new projected variable values.

For this correctly anchored assignment, the equality holds at
EVERY ambient homogeneous-tree position:
  original f constants: independent of all variable assignments;
  early f variable fibres: by the rho-anchoring theorem;
  late SAFE projected f fibres: by genuine whole-fibre Q comparison;
  late UNSAFE/no-projection f fibres: by the common fallback theorem.

The result is an equality of EVALUATED tree words (and hence a
witness to membership in the full final f'-span), not a false
equality of variable symbols with DIFFERENT root-name types.
This is for the CORRECTED forward starred W_* domain. The printed
reverse auxiliary-order interface, Definition 24 simplicity and
the Ramsey iteration remain separate.
-/

namespace DualTree.ForwardQFinalWholeDomainEvaluation

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalSafeAddressLookup
open ForwardQFinalWholeFibreQEvaluation
open ForwardQFinalEarlyFibreAssignment
open ForwardQFinalUnsafeFibreFallback

/-- The whole-domain equality of EVALUATED corrected Q and
the actual interpolating final ambient f'. Every source old-root
assignment tau and arbitrary later final-root assignment sigma0
determine a canonical anchored final assignment, with NO further
bullet point, root, or local-coordinate hypotheses. -/
theorem inducedFibreQ_eval_eq_final_eval_at
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (hq : 0 < q)
    (s : BoundedNode b n) :
    SpanAudit.evalSymbol τ
      ((inducedFibreQ hb g f fallback
        (anchoredAssignment g f τ σ0) hq).word.word s) =
    SpanAudit.evalSymbol (anchoredAssignment g f τ σ0)
      ((interpolatedFinalWord
        g f (fun a : α => a) fallback).word s) := by
  cases hs : g.ambient.word s with
  | inl a =>
      exact inducedFibreQ_eval_on_ambient_constant
        hb g f fallback (anchoredAssignment g f τ σ0)
        hq τ s a hs
  | inr u =>
      by_cases hbefore : ForwardAux u.1.1 g.core.cut
      · exact inducedFibreQ_eval_on_early_fibre
          hb g f fallback τ σ0 hq u s hs hbefore
      · cases hsafe : safeAddress g.core u.1.1 with
        | none =>
            exact inducedFibreQ_eval_late_no_safe
              hb g f fallback
              (anchoredAssignment g f τ σ0)
              hq τ u s hs hbefore hsafe
        | some addr =>
            have hproj :
                (projected g.core addr).1 = u.1.1 :=
              safeAddress_spec g.core u.1.1 addr hsafe
            have hu :
                ForwardQAmbientFibreFrame.ambientAtTRoot
                  g (projected g.core addr).1
                    (projected g.core addr).2 = u := by
              apply Subtype.ext
              apply Subtype.ext
              exact hproj
            have hsfibre :
                g.ambient.word s =
                  Sum.inr
                    (ForwardQAmbientFibreFrame.ambientAtTRoot
                      g (projected g.core addr).1
                        (projected g.core addr).2) := by
              simpa only [hu] using hs
            rcases addr with ⟨i,z⟩
            exact inducedFibreQ_eval_on_safe_fibre
              hb g f fallback (anchoredAssignment g f τ σ0)
              hq τ i z s hsfibre

/-- The pointwise statement packaged as literal equality of
evaluated TreeWord functions on the ENTIRE ambient domain. -/
theorem inducedFibreQ_eval_eq_final_eval
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (hq : 0 < q) :
    (inducedFibreQ hb g f fallback
      (anchoredAssignment g f τ σ0) hq).word.eval τ =
    (interpolatedFinalWord
      g f (fun a : α => a) fallback).eval
        (anchoredAssignment g f τ σ0) := by
  funext s
  exact inducedFibreQ_eval_eq_final_eval_at
    hb g f fallback τ σ0 hq s

/-- An actual evaluation of the legal fibrewise corrected
starred Q word, with a canonical mixed-span input,
belongs to the span of the genuine complete-skew final word.

The final assignment is ANCHORED on retained roots, but
all newly selected projected variables remain independent.
This inclusion direction is proved without claiming that
EVERY final-word assignment arises from the Q picture. -/
theorem inducedFibreQ_eval_mem_final_span
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q α)
    (fallback : α)
    (τ : g.core.source.word.Vars → α)
    (σ0 : FinalRoot g f → α)
    (hq : 0 < q) :
    (inducedFibreQ hb g f fallback
      (anchoredAssignment g f τ σ0) hq).word.eval τ ∈
    (interpolatedFinalWord
      g f (fun a : α => a) fallback).span := by
  refine ⟨anchoredAssignment g f τ σ0, ?_⟩
  exact (inducedFibreQ_eval_eq_final_eval
    hb g f fallback τ σ0 hq).symm

end DualTree.ForwardQFinalWholeDomainEvaluation
