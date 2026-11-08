# Track G follow-up — closing the named theorem axiom-registry gap

**Date:** 8 November 2026. **Base:** Track G PR #545 (squash d2caeec).

The first CI coverage artifact contained 2,205 lexically recognized named
public theorem/lemma declarations, 2,172 registered, 33 unregistered,
12 explicitly private declarations excluded, and zero scope warnings.
The 33 are now registered in `scripts/CheckDualTree.lean` and CI
requires *zero* unregistered lexically recognized public candidates.
Both source warnings and missing registered declarations now fail the
source-audit workflow. These 33 checks include the Corollary 22 witness
lemmas, Lemma 27 printed-domain witnesses, explicit order counterexample
facts, singleton-alphabet Theorem 3 audit, and visible ancestor bounds.

These checks are valuable because a transitive `#print axioms` display
for a named Lean theorem can reveal unsafe dependencies; they do NOT
establish correspondence between a Lean theorem and its printed statement.
Lexical scanner coverage likewise is not completeness of the proof.
Its visibility is limited to simple named theorem/lemma syntax, excluding
macros, automatically generated declarations and unusual naming forms.

**Independent audit handoff:** Read CI's full transitive axiom log for
these 33 additions; inspect the displayed axioms and source theorem
signatures before declaring the stronger trust invariant established.
A green CI proves the build and scanner pass, not the unproved Lemma
27–28, Theorem 25, Theorem 3 or Theorem 29 interfaces. In particular
`UpCanonical` is not Definition-11 `Good`, and corrected forward-Q
Hilbert/Hall conditions still require all occurrence/nondegeneracy
hypotheses. Preserve the known counterexamples as regression fixtures.

The source-scope rule introduced here is intentional: future branches
adding a public theorem must either register its axiom check or document
why this conservative lexical count is not applicable. Do not weaken the
gate solely to keep an unrelated Track A–F PR green.
