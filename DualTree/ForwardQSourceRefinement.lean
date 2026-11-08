import DualTree.ForwardQAmbientFibreFrame

/-!
# Source-relative syntactic refinement for the corrected Q construction

The Q construction reads symbols of the actual ambient variable word.
Consequently it needs uniform substitution on every ambient variable
fibre, including when the original alphabet has only one letter.
Evaluated-span inclusion implies this symbolic condition only when the
alphabet has at least two letters.

This module makes that distinction explicit. Syntactic refinement
preserves constants, equal symbols and support roots for every alphabet.
It has a canonical substitution: read the target word at each source
variable's root. This removes any choice of substitution from the
corrected Q source frame.

The frame constructors preserve the supplied core and ambient word
definitionally. Their support hypothesis compares all node memberships,
so the ambient bound on the core support is a consequence, rather than
an additional assumption. A bounded-node-only comparison would not
exclude unbounded vertices of the core support.
-/

namespace DualTree.ForwardQSourceRefinement

/-- Uniform symbolic refinement, retaining the actual dependent variable
names rather than only their evaluated constant-word spans. -/
def SyntacticallyRefines
    {b n : Nat} {α : Type*}
    (target source : VariableWord b n α) : Prop :=
  ∃ ρ : source.Vars → Sum α target.Vars,
    target.word = SpanAudit.substitute source.word ρ

/-- The canonical substitution reads the target symbol at a source root.
It is defined without an alphabet-cardinality assumption or choice. -/
def rootSubstitution
    {b n : Nat} {α : Type*}
    (target source : VariableWord b n α) :
    source.Vars → Sum α target.Vars :=
  fun v => target.word v.1

namespace SyntacticallyRefines

variable {b n : Nat} {α : Type*}
variable {target middle source : VariableWord b n α}

/-- Every symbolic refinement gives the correctly directed evaluated-span
inclusion, including over singleton and empty alphabets. -/
theorem span_subset
    (hRef : SyntacticallyRefines target source) :
    target.span ⊆ source.span := by
  obtain ⟨ρ, hword⟩ := hRef
  change SpanAudit.span target.word ⊆ SpanAudit.span source.word
  rw [hword]
  exact SpanAudit.span_substitute_subset source.word ρ

/-- Identity substitution is a symbolic refinement. -/
theorem refl (source : VariableWord b n α) :
    SyntacticallyRefines source source := by
  refine ⟨fun v => Sum.inr v, ?_⟩
  funext s
  cases hs : source.word s with
  | inl a => simp [SpanAudit.substitute, hs]
  | inr v => simp [SpanAudit.substitute, hs]

/-- Symbolic refinement composes without losing variable-fibre data. -/
theorem trans
    (hTarget : SyntacticallyRefines target middle)
    (hSource : SyntacticallyRefines middle source) :
    SyntacticallyRefines target source := by
  obtain ⟨ρTarget, hTargetWord⟩ := hTarget
  obtain ⟨ρSource, hSourceWord⟩ := hSource
  refine ⟨fun v => KVariableWord.mapSymbol ρTarget (ρSource v), ?_⟩
  calc
    target.word = SpanAudit.substitute middle.word ρTarget := hTargetWord
    _ = SpanAudit.substitute
        (SpanAudit.substitute source.word ρSource) ρTarget := by
      rw [hSourceWord]
    _ = SpanAudit.substitute source.word
        (fun v => KVariableWord.mapSymbol ρTarget (ρSource v)) :=
      KVariableWord.substitute_compose source.word ρSource ρTarget

/-- A fixed alphabet constant is preserved symbolically for every
alphabet, with no appeal to separating assignments. -/
theorem preserves_constant
    (hRef : SyntacticallyRefines target source)
    {s : BoundedNode b n} {a : α}
    (hs : source.word s = Sum.inl a) :
    target.word s = Sum.inl a := by
  obtain ⟨ρ, hword⟩ := hRef
  rw [hword]
  simp [SpanAudit.substitute, hs]

/-- Positions with equal source symbols have equal target symbols.
In particular each complete original variable fibre stays uniform. -/
theorem preserves_symbol_eq
    (hRef : SyntacticallyRefines target source)
    {s t : BoundedNode b n}
    (hst : source.word s = source.word t) :
    target.word s = target.word t := by
  obtain ⟨ρ, hword⟩ := hRef
  rw [hword]
  simp only [SpanAudit.substitute, hst]

/-- Every occurrence of a source variable has the target symbol at its
actual root. This is the ambient-fibre equation used by corrected Q. -/
theorem preserves_fibre
    (hRef : SyntacticallyRefines target source)
    (v : source.Vars) {s : BoundedNode b n}
    (hs : source.word s = Sum.inr v) :
    target.word s = target.word v.1 :=
  hRef.preserves_symbol_eq (hs.trans (source.atRoot v).symm)

/-- The root-read substitution realizes every syntactic refinement.
Thus the Q frame need not select an arbitrary existential witness. -/
theorem eq_substitute_rootSubstitution
    (hRef : SyntacticallyRefines target source) :
    target.word = SpanAudit.substitute source.word
      (rootSubstitution target source) := by
  funext s
  cases hs : source.word s with
  | inl a =>
      simpa [SpanAudit.substitute, hs] using hRef.preserves_constant hs
  | inr v =>
      simpa [SpanAudit.substitute, rootSubstitution, hs] using
        hRef.preserves_fibre v hs

/-- The substitution is uniquely determined by the source roots. -/
theorem substitution_eq_rootSubstitution
    (ρ : source.Vars → Sum α target.Vars)
    (hword : target.word = SpanAudit.substitute source.word ρ) :
    ρ = rootSubstitution target source := by
  funext v
  have hv := congrFun hword v.1
  simpa [SpanAudit.substitute, rootSubstitution, source.atRoot v] using hv.symm

/-- Syntactic refinement preserves actual support roots even when
evaluated-span inclusion alone loses that information. -/
theorem support_subset
    (hRef : SyntacticallyRefines target source) :
    ∀ t, t ∈ target.support → t ∈ source.support := by
  intro t ht
  let v : target.Vars := ⟨t, ht⟩
  obtain ⟨ρ, hword⟩ := hRef
  have hsubroot : SpanAudit.substitute source.word ρ t = Sum.inr v := by
    rw [← hword]
    exact target.atRoot v
  cases hs : source.word t with
  | inl a =>
      simp [SpanAudit.substitute, hs] at hsubroot
  | inr u =>
      have hρ : ρ u = Sum.inr v := by
        simpa [SpanAudit.substitute, hs] using hsubroot
      have htAtU : target.word u.1 = Sum.inr v := by
        rw [hword]
        simpa [SpanAudit.substitute, source.atRoot u] using hρ
      have hut : IsPrefix u.1.1 t.1 := source.below u t hs
      have htu : IsPrefix t.1 u.1.1 := target.below v u.1 htAtU
      have hu : u.1 = t := Subtype.ext (isPrefix_antisymm hut htu)
      rw [← hu]
      exact u.2

end SyntacticallyRefines

/-- For a nondegenerate alphabet the symbolic source contract is exactly
the paper's evaluated-span inclusion. No such equivalence is asserted
for a singleton alphabet. -/
theorem syntacticallyRefines_iff_span_subset
    {b n : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (target source : VariableWord b n α) :
    SyntacticallyRefines target source ↔ target.span ⊆ source.span :=
  (VariableWord.span_subset_iff_substitution hα source target).symm

/-- Build the actual Q fibre frame from a full support comparison and
a genuine symbolic source refinement. The support bound and canonical
substitution are proved, while core and ambient data are retained exactly. -/
def fibreFrameOfSyntactic
    {b n l k m : Nat} {α : Type*}
    (core : ForwardSourceQTree.Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hRef : SyntacticallyRefines core.source.word ambient) :
    ForwardQAmbientFibreFrame.FibreFrame b n l k m α where
  core := core
  ambient := ambient
  ambient_support_T := by
    intro t
    constructor
    · intro ht
      exact (hsupport t.1).1 (List.mem_map.mpr ⟨t, ht, rfl⟩)
    · intro ht
      obtain ⟨s, hs, hst⟩ := List.mem_map.mp ((hsupport t.1).2 ht)
      have heq : s = t := Subtype.ext hst
      simpa [heq] using hs
  T_bounded := by
    intro t ht
    obtain ⟨s, _, hst⟩ := List.mem_map.mp ((hsupport t).2 ht)
    rw [← hst]
    exact s.2
  substitution := rootSubstitution core.source.word ambient
  source_substitution := hRef.eq_substitute_rootSubstitution

/-- The core passed to the syntactic frame constructor is unchanged,
so all its dependent local mixed-word types remain definitionally equal. -/
theorem fibreFrameOfSyntactic_core
    {b n l k m : Nat} {α : Type*}
    (core : ForwardSourceQTree.Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hRef : SyntacticallyRefines core.source.word ambient) :
    (fibreFrameOfSyntactic core ambient hsupport hRef).core = core := rfl

/-- The original ambient variable word is unchanged by frame formation. -/
theorem fibreFrameOfSyntactic_ambient
    {b n l k m : Nat} {α : Type*}
    (core : ForwardSourceQTree.Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hRef : SyntacticallyRefines core.source.word ambient) :
    (fibreFrameOfSyntactic core ambient hsupport hRef).ambient = ambient := rfl

/-- The paper-style evaluated refinement supplies the Q source frame
when the original alphabet contains two distinct letters. -/
def fibreFrameOfSpan
    {b n l k m : Nat} {α : Type*}
    (core : ForwardSourceQTree.Frame b n l k m α)
    (ambient : VariableWord b n α)
    (hsupport : ∀ t : Node b,
      t ∈ ambient.supportNodes ↔ t ∈ core.T)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : core.source.word.span ⊆ ambient.span) :
    ForwardQAmbientFibreFrame.FibreFrame b n l k m α :=
  fibreFrameOfSyntactic core ambient hsupport
    ((syntacticallyRefines_iff_span_subset
      hα core.source.word ambient).2 hspan)

end DualTree.ForwardQSourceRefinement
