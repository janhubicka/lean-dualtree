import DualTree.RootFreezing

/-!
# Root-aligned substitutions of tree-variable words

The reconstructed word in Lemma 27 must preserve entire variable fibres.
Merely freezing discarded roots is insufficient when several old variables
are to be merged into one surviving variable.  This file gives a more
general algebraic operation.

Choose a duplicate-free subset S of the original variable roots.  For
each old root, choose either a constant or a surviving root.  Surviving
roots must map to themselves, and any target variable root must be an
ambient prefix of its old root. These are precisely the local conditions
needed for the substituted word to be a legal tree-variable word.
-/

namespace DualTree.Lemma27Repair

/-- A root-aligned substitution with exactly the selected surviving roots. -/
noncomputable def substituteRoots
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    DualTree.VariableWord b n α := by
  refine {
    support := S
    support_nodup := hnd
    word := SpanAudit.substitute f.word ρ
    atRoot := ?_
    below := ?_
  }
  · intro w
    let v : f.Vars := ⟨w.1, hS w.1 w.2⟩
    have hv : f.word w.1 = Sum.inr v := f.atRoot v
    simpa [SpanAudit.substitute, hv, v] using hretain w
  · intro w i hwi
    cases hfi : f.word i with
    | inl c =>
        simp [SpanAudit.substitute, hfi] at hwi
    | inr v =>
        have hρ : ρ v = Sum.inr w := by
          simpa [SpanAudit.substitute, hfi] using hwi
        exact isPrefix_trans (haligned v w hρ) (f.below v i hfi)

/-- The resulting evaluated span is contained in the source span. -/
theorem substituteRoots_span_subset
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    (substituteRoots f S hnd hS ρ hretain haligned).span ⊆ f.span := by
  change SpanAudit.span (SpanAudit.substitute f.word ρ) ⊆
    SpanAudit.span f.word
  exact SpanAudit.span_substitute_subset f.word ρ

/-- The chosen list is exactly the resulting support. -/
theorem substituteRoots_support
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    (substituteRoots f S hnd hS ρ hretain haligned).support = S := by
  rfl

/-- Two occurrences of the same old variable have the same substituted symbol. -/
theorem substituteRoots_fibre_uniform
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (ρ : f.Vars → Sum α {t // t ∈ f.support})
    {v : f.Vars} {i j : BoundedNode b n}
    (hi : f.word i = Sum.inr v)
    (hj : f.word j = Sum.inr v) :
    SpanAudit.substitute f.word ρ i =
      SpanAudit.substitute f.word ρ j := by
  simp [SpanAudit.substitute, hi, hj]

end DualTree.Lemma27Repair
