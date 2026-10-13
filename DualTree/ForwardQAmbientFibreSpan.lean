import DualTree.ForwardQAmbientFibreLegalWord

/-!
# The whole corrected Q word is one substitution of the original ambient f

The corrected fibrewise construction has a genuine ambient variable word f,
a source starred refinement g' = f[rho], and the literal enlarged-alphabet
ordinary local cone words w_i. Rather than proving evaluated-span inclusion
one cone at a time, define ONE global substitution on the original f-variable
names: use rho for roots at or before the cut; use the appropriate concrete
R_i-decoded original/auxiliary letter for roots after the cut.

The resulting total fibrewise Q symbol function is DEFINITIONALLY
the substitution of f by that global map. Thus its evaluated span is
contained in that of the ambient f, even over a singleton alphabet.
Together with the already checked containment of its corrected Q
support in T = ws(f), this proves the precise source-facing
refinement predicate (S_w,g_w) <= f under the explicitly strengthened
syntactic FibreFrame hypothesis.

No Hall matching is needed for this initial ordinary mixed-product
Q stage. The printed auxiliary-order Q, transport of Definition 24
simplicity, and the later refined variable word f' remain open.
-/

namespace DualTree.ForwardQAmbientFibreSpan

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord

/-- ONE uniform substitution of the actual ambient f-variable
names: old/early fibres use the original witness rho,
later fibres read the appropriate enlarged local cone symbol
and decode auxiliary labels by the checked concrete R_i. -/
noncomputable def fibreSubstitution
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core) :
    c.ambient.Vars → Sum α c.core.source.word.Vars := by
  classical
  exact fun v =>
    if ForwardAux v.1.1 c.core.cut then
      c.substitution v
    else
      decodeAmbientRoot c fallback w v

theorem fibreSubstitution_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars)
    (hv : ForwardAux v.1.1 c.core.cut) :
    fibreSubstitution c fallback w v = c.substitution v := by
  simp [fibreSubstitution, hv]

theorem fibreSubstitution_after_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars)
    (hv : ¬ ForwardAux v.1.1 c.core.cut) :
    fibreSubstitution c fallback w v =
      decodeAmbientRoot c fallback w v := by
  simp [fibreSubstitution, hv]

/-- The WHOLE homogeneous-tree Q word, not only its projected
support coordinates, is the image of f under one uniform
syntactic substitution. Fibre uniformity is built in. -/
theorem fibreQSymbol_eq_substitute
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core) :
    fibreQSymbol c fallback w =
      SpanAudit.substitute c.ambient.word
        (fibreSubstitution c fallback w) := by
  funext s
  cases hf : c.ambient.word s with
  | inl a =>
      simp [fibreQSymbol, SpanAudit.substitute, hf]
  | inr v =>
      by_cases hv : ForwardAux v.1.1 c.core.cut
      · have hsource :
            c.core.source.word.word s = c.substitution v := by
          rw [c.source_substitution]
          simp [SpanAudit.substitute, hf]
        simp [fibreQSymbol, SpanAudit.substitute, hf, hv,
          fibreSubstitution, hsource]
      · simp [fibreQSymbol, SpanAudit.substitute, hf, hv,
          fibreSubstitution]

/-- No extra alphabet-size hypothesis is needed: the Q symbol
map is explicitly a syntactic refinement of f. -/
theorem fibreQSymbol_span_subset_ambient
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core) :
    SpanAudit.span (fibreQSymbol c fallback w) ⊆
      SpanAudit.span c.ambient.word := by
  rw [fibreQSymbol_eq_substitute c fallback w]
  exact SpanAudit.span_substitute_subset c.ambient.word
    (fibreSubstitution c fallback w)

/-- At each retained original source variable root, the global
ambient substitution fixes the corresponding source variable. -/
theorem fibreSubstitution_fixes_old_roots
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.core.source.word.Vars) :
    fibreSubstitution c fallback w (ambientAtSourceRoot c v) =
      Sum.inr v := by
  have hv : ForwardAux
      (ambientAtSourceRoot c v).1.1 c.core.cut := by
    simpa [ambientAtSourceRoot] using source_root_before_cut c v
  rw [fibreSubstitution_before_cut c fallback w
    (ambientAtSourceRoot c v) hv]
  exact source_substitution_fixes_old_root c v

/-- The FINISHED legal starred Q word has its full evaluated
word span contained in that of f, not merely equality at a
collection of projected root positions. -/
theorem fibreQStarredWord_span_subset_ambient
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    (fibreQStarredWord hb c fallback w).word.span ⊆
      c.ambient.span := by
  change SpanAudit.span (fibreQSymbol c fallback w.1) ⊆
    SpanAudit.span c.ambient.word
  exact fibreQSymbol_span_subset_ambient c fallback w.1

/-- This is the exact pair of containment conditions used
by Definition 23's source-facing relation (S,g) <= f:
  (a) S is contained in the complete support ws(f)=T;
  (b) the evaluated span of g is contained in that of f.
In particular the Q construction does not silently produce
an unrelated word with the right support. -/
theorem fibreQStarredWord_refines_ambient
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    (∀ t : Node b,
      t ∈ (fibreQStarredWord hb c fallback w).tree →
        t ∈ c.core.T) ∧
    (fibreQStarredWord hb c fallback w).word.span ⊆
      c.ambient.span := by
  constructor
  · intro t ht
    change t ∈ (nodes c.core
      (ForwardQEnlargedConstantWords.eraseAux
        c.core fallback w.1)).toList at ht
    exact ForwardQSourceTerminals.Q_nodes_subset_complete
      c.core
      (ForwardQEnlargedConstantWords.eraseAux
        c.core fallback w.1) t
      (Finset.mem_toList.mp ht)
  · exact fibreQStarredWord_span_subset_ambient
      hb c fallback w

end DualTree.ForwardQAmbientFibreSpan
