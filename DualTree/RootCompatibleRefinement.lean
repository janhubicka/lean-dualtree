import DualTree.VariableWord

/-!
# Root-compatible refinement of a finite tree variable word

A syntactic substitution does not automatically define a legal
tree-indexed VariableWord with a CHANGED root support. It must:
1. fix each retained variable at its own original root;
2. assign a variable based at an ancestor of the original
   variable's root, so the below-root condition survives.

Here these two obligations are isolated in a reusable typed
certificate. The resulting legal VariableWord is a genuine
evaluated-span refinement of the original, by the existing
SpanAudit substitution theorem.

The default root-collapse certificate is intentionally elementary
and NOT the final Q-specific substitution of Lemma 27. Its role
is to demonstrate that support coarsening itself is never the
remaining obstruction: the later f' construction must supply
the PRESCRIBED local-coordinate interpolation and Q agreement.
-/

namespace DualTree.RootCompatibleRefinement

/-- A root-compatible substitution from original variables to
a candidate list of retained/new variable roots. -/
structure Certificate
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n)) where
  oldRoot : ∀ v : {t // t ∈ roots}, v.1 ∈ source.support
  substitution : source.Vars → Sum α {t // t ∈ roots}
  fixesRoot : ∀ v : {t // t ∈ roots},
    substitution ⟨v.1, oldRoot v⟩ = Sum.inr v
  belowRoot : ∀ (u : source.Vars) (v : {t // t ∈ roots}),
    substitution u = Sum.inr v → IsPrefix v.1.1 u.1.1

/-- The actual tree variable word induced by a root-compatible
substitution. No independent alphabet-nondegeneracy assumption
is necessary because the substitution is supplied syntactically. -/
noncomputable def refine
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (hnd : roots.Nodup)
    (c : Certificate source roots) :
    VariableWord b n α := by
  refine
    { support := roots
      support_nodup := hnd
      word := SpanAudit.substitute source.word c.substitution
      atRoot := ?_
      below := ?_ }
  · intro v
    change SpanAudit.substitute source.word c.substitution v.1 =
      Sum.inr v
    have hs :
        source.word v.1 = Sum.inr
          (⟨v.1, c.oldRoot v⟩ : source.Vars) :=
      source.atRoot ⟨v.1, c.oldRoot v⟩
    simpa [SpanAudit.substitute, hs] using c.fixesRoot v
  · intro v i h
    change SpanAudit.substitute source.word c.substitution i =
      Sum.inr v at h
    cases hi : source.word i with
    | inl a =>
        simp [SpanAudit.substitute, hi] at h
    | inr u =>
        have hsub : c.substitution u = Sum.inr v := by
          simpa [SpanAudit.substitute, hi] using h
        exact isPrefix_trans (c.belowRoot u v hsub)
          (source.below u i hi)

/-- A well-formed root-compatible tree substitution is ALWAYS
a true evaluated-span refinement of the original word. -/
theorem refine_span_subset
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (hnd : roots.Nodup)
    (c : Certificate source roots) :
    (refine source roots hnd c).span ⊆ source.span := by
  change SpanAudit.span
    (SpanAudit.substitute source.word c.substitution) ⊆
    SpanAudit.span source.word
  exact SpanAudit.span_substitute_subset source.word c.substitution

/-- The new word has EXACTLY the requested support, rather
than only a subset or a set of auxiliary decoded variables. -/
theorem refine_support_eq
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (hnd : roots.Nodup)
    (c : Certificate source roots) :
    (refine source roots hnd c).support = roots := rfl

/-- A canonical but deliberately coarse substitution: keep
each selected source variable, send every nonselected variable
to the selected common root. This is useful as a witness that
the abstract root-compatible refinement conditions are
consistent for any rooted subset of source support. -/
noncomputable def collapseSubstitution
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (root : {t // t ∈ roots}) :
    source.Vars → Sum α {t // t ∈ roots} :=
  fun u =>
    if h : u.1 ∈ roots then
      Sum.inr ⟨u.1, h⟩
    else Sum.inr root

/-- Any nonempty selected root subset containing a prefix of
all original variable roots admits at least this elementary
root-compatible substitution. The Q-specific word will need
a stronger, prescribed certificate rather than this collapse. -/
noncomputable def collapseCertificate
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (oldSubset : ∀ v : {t // t ∈ roots}, v.1 ∈ source.support)
    (root : {t // t ∈ roots})
    (rootPrefix : ∀ u : source.Vars, IsPrefix root.1.1 u.1.1) :
    Certificate source roots := by
  classical
  refine
    { oldRoot := oldSubset
      substitution := collapseSubstitution source roots root
      fixesRoot := ?_
      belowRoot := ?_ }
  · intro v
    simp [collapseSubstitution, v.2]
  · intro u v hu
    by_cases hm : u.1 ∈ roots
    · have hsubst : (⟨u.1, hm⟩ : {t // t ∈ roots}) = v := by
        have hsum :
            (Sum.inr ⟨u.1, hm⟩ : Sum α {t // t ∈ roots}) =
              Sum.inr v := by
          simpa [collapseSubstitution, hm] using hu
        exact Sum.inr.inj hsum
      have hv : v.1.1 = u.1.1 :=
        congrArg (fun x : {t // t ∈ roots} => x.1.1)
          hsubst.symm
      rw [hv]
      exact isPrefix_refl u.1.1
    · have hroot : root = v := by
        have hsum :
            (Sum.inr root : Sum α {t // t ∈ roots}) =
              Sum.inr v := by
          simpa [collapseSubstitution, hm] using hu
        exact Sum.inr.inj hsum
      subst v
      exact rootPrefix u

/-- Any rooted selected subset of the original support
has a legal variable-word refinement with that exact support.
This is an existence certificate, NOT yet the actual f' used
to interpolate local mixed-product letters. -/
noncomputable def collapse
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (hnd : roots.Nodup)
    (oldSubset : ∀ v : {t // t ∈ roots}, v.1 ∈ source.support)
    (root : {t // t ∈ roots})
    (rootPrefix : ∀ u : source.Vars, IsPrefix root.1.1 u.1.1) :
    VariableWord b n α :=
  refine source roots hnd
    (collapseCertificate source roots oldSubset root rootPrefix)

/-- Even the coarse root-collapse construction gives actual
evaluated-span inclusion into the original ambient word. -/
theorem collapse_span_subset
    {b n : Nat} {α : Type*}
    (source : VariableWord b n α)
    (roots : List (BoundedNode b n))
    (hnd : roots.Nodup)
    (oldSubset : ∀ v : {t // t ∈ roots}, v.1 ∈ source.support)
    (root : {t // t ∈ roots})
    (rootPrefix : ∀ u : source.Vars, IsPrefix root.1.1 u.1.1) :
    (collapse source roots hnd oldSubset root rootPrefix).span ⊆
      source.span :=
  refine_span_subset source roots hnd
    (collapseCertificate source roots oldSubset root rootPrefix)

end DualTree.RootCompatibleRefinement
