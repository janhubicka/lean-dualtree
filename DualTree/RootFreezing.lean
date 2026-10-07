import DualTree.Lemma27Audit
import DualTree.VariableWord

/-!
# Root-based freezing of a tree-variable word

The occurrence-based clauses (iv)--(v) on p.29 of Lemma 27 can freeze
different occurrences of the same variable inconsistently.  Here we
formalize the source-faithful algebraic repair: select roots to retain,
replace all occurrences of each discarded root by one constant, and
transport surviving root symbols uniformly.

This produces a legal tree-variable word and a syntactic refinement for every
alphabet, including a singleton alphabet.  It does not by itself establish
the new support's complete-skew geometry or the signature coding lemma.
-/

namespace DualTree.Lemma27Repair

/-- Substitution on variable roots, retaining only roots in S. -/
noncomputable def rootMask
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n)) (a : α) :
    f.Vars → Sum α {t // t ∈ S} := by
  classical
  exact fun v =>
    if h : v.1 ∈ S then Sum.inr ⟨v.1, h⟩ else Sum.inl a

/-- Every occurrence of one old variable receives the same new symbol. -/
noncomputable def restrictSupportWord
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n)) (a : α) :
    BoundedNode b n → Sum α {t // t ∈ S} :=
  SpanAudit.substitute f.word (rootMask f S a)

/-- Root masking is literally uniform substitution. -/
theorem restrictSupportWord_substitution
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n)) (a : α) :
    restrictSupportWord f S a =
      SpanAudit.substitute f.word (rootMask f S a) := by
  rfl

/--
If S is a duplicate-free subset of the old support, masking all other
variables produces a genuine tree-variable word with support exactly S.
-/
noncomputable def restrictSupport
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (a : α) : DualTree.VariableWord b n α := by
  classical
  refine {
    support := S
    support_nodup := hnd
    word := restrictSupportWord f S a
    atRoot := ?_
    below := ?_
  }
  · intro v
    let old : f.Vars := ⟨v.1, hS v.1 v.2⟩
    have hroot : f.word v.1 = Sum.inr old := f.atRoot old
    simp [restrictSupportWord, SpanAudit.substitute, rootMask, hroot, old, v.2]
  · intro v i hi
    cases hfi : f.word i with
    | inl c =>
        simp [restrictSupportWord, SpanAudit.substitute, hfi] at hi
    | inr old =>
        by_cases hm : old.1 ∈ S
        · have heq : old.1 = v.1 := by
            have hsum :
                Sum.inr (⟨old.1, hm⟩ : {t // t ∈ S}) = Sum.inr v := by
              simpa [restrictSupportWord, SpanAudit.substitute,
                rootMask, hfi, hm] using hi
            exact congrArg Subtype.val (Sum.inr.inj hsum)
          have hp : IsPrefix old.1.1 i.1 := f.below old i hfi
          simpa [heq] using hp
        · simp [restrictSupportWord, SpanAudit.substitute,
            rootMask, hfi, hm] at hi

/-- The repaired word is a syntactic refinement of the original one. -/
theorem restrictSupport_span_subset
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (a : α) :
    (restrictSupport f S hnd hS a).span ⊆ f.span := by
  change SpanAudit.span (restrictSupportWord f S a) ⊆ SpanAudit.span f.word
  rw [restrictSupportWord_substitution]
  exact SpanAudit.span_substitute_subset f.word (rootMask f S a)

/-- All surviving variable roots are exactly the chosen ones. -/
theorem restrictSupport_support
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (a : α) :
    (restrictSupport f S hnd hS a).support = S := by
  rfl

end DualTree.Lemma27Repair
