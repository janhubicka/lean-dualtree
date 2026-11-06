import DualTree.StarredSignature
import DualTree.CutPreservation
import DualTree.MixedGood

/-!
# Track F: corrected theorem targets, without existence assumptions hidden as axioms

The target convention is the forward auxiliary order and uniform syntactic
refinement.  It includes nonempty one-letter alphabets; evaluated-span
refinement is equivalent only under `SpanAudit.HasTwoLetters`.

Colours act on semantic observations, not arbitrary list presentations of the
same support.  `TreeRamseyAt`, `StarredRamseyAt`, and the eventual-bound
predicates below are SPECIFICATIONS, not proofs of the paper's theorems.
The starred selector remains an explicit input from Track E.
-/

namespace DualTree.CorrectedTheoremSpec

/-- Complete words with the corrected forward order. -/
abbrev Word (b n k : Nat) (α : Type*) :=
  KVariableWord b n k α (SkewTree.forwardAuxB (b := b))

/-- Semi-complete starred words with exactly `l` interior vertices. -/
abbrev Starred (b n l : Nat) (α : Type*) :=
  StarredSignature.StarredWord b n l α (SkewTree.forwardAuxB (b := b))

/-- Variable symbols are named by their actual roots. -/
abbrev WordObservation (b n : Nat) (α : Type*) :=
  BoundedNode b n → Sum α (BoundedNode b n)

def wordObserve {b n k : Nat} {α : Type*}
    (f : Word b n k α) : WordObservation b n α :=
  CutPreservation.underlyingSymbol f.toVariableWord

/-- This is definitionally the observation type used by the corrected Q API. -/
abbrev StarredObservation (b n : Nat) (α : Type*) :=
  Finset (Node b) × WordObservation b n α

noncomputable def starredObserve {b n l : Nat} {α : Type*}
    (O : Starred b n l α) : StarredObservation b n α := by
  classical
  exact (O.tree.toFinset, CutPreservation.underlyingSymbol O.word)

/-- Exact starred refinement: the entire tree lies in the enclosing support,
and the entire ambient word is one uniform substitution. -/
def StarredBelow {b n l k : Nat} {α : Type*}
    (O : Starred b n l α) (f : Word b n k α) : Prop :=
  (∀ t, t ∈ O.tree → t ∈ f.toVariableWord.supportNodes) ∧
    ∃ ρ : f.Vars → Sum α O.word.Vars,
      O.word.word = SpanAudit.substitute f.word ρ

/-- The printed span-based starred relation, retaining its tree-containment
clause.  This is kept separate from the chosen syntactic target. -/
def StarredSpanBelow {b n l k : Nat} {α : Type*}
    (O : Starred b n l α) (f : Word b n k α) : Prop :=
  (∀ t, t ∈ O.tree → t ∈ f.toVariableWord.supportNodes) ∧
    O.word.span ⊆ f.span

theorem starredBelow_span {b n l k : Nat} {α : Type*}
    {O : Starred b n l α} {f : Word b n k α}
    (h : StarredBelow O f) : StarredSpanBelow O f := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨ρ, hword⟩
  change SpanAudit.span O.word.word ⊆ SpanAudit.span f.word
  rw [hword]
  exact SpanAudit.span_substitute_subset f.word ρ

theorem starredBelow_iff_span {b n l k : Nat} {α : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (O : Starred b n l α) (f : Word b n k α) :
    StarredBelow O f ↔ StarredSpanBelow O f := by
  constructor
  · exact starredBelow_span
  · intro h
    exact ⟨h.1,
      (VariableWord.span_subset_iff_substitution
        hα f.toVariableWord O.word).1 h.2⟩

/-- Eligibility is inherited by every further syntactic refinement.  Both
the tree and word clauses are proved; no signature transport is inferred. -/
theorem starredBelow_of_syntacticRefines
    {b n l k k' : Nat} {α : Type*}
    {O : Starred b n l α} {g : Word b n k' α} {f : Word b n k α}
    (hgf : KVariableWord.SyntacticRefines g f)
    (hOg : StarredBelow O g) : StarredBelow O f := by
  have hs := KVariableWord.support_subset_of_syntacticRefines g f hgf
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases List.mem_map.mp (hOg.1 t ht) with ⟨s, hsg, hst⟩
    exact List.mem_map.mpr ⟨s, hs s hsg, hst⟩
  · rcases hgf with ⟨ρ, hρ⟩
    rcases hOg.2 with ⟨τ, hτ⟩
    refine ⟨fun v => KVariableWord.mapSymbol τ (ρ v), ?_⟩
    calc
      O.word.word = SpanAudit.substitute g.word τ := hτ
      _ = SpanAudit.substitute (SpanAudit.substitute f.word ρ) τ := by rw [hρ]
      _ = SpanAudit.substitute f.word
          (fun v => KVariableWord.mapSymbol τ (ρ v)) :=
        KVariableWord.substitute_compose f.word ρ τ

/-- Homogeneity of the genuine `k`-complete syntactic refinements. -/
def WordMonochromatic {b n k m : Nat} {α γ : Type*}
    (c : WordObservation b n α → γ) (f : Word b n m α) : Prop :=
  ∀ g h : Word b n k α,
    KVariableWord.SyntacticRefines g f →
    KVariableWord.SyntacticRefines h f →
    c (wordObserve g) = c (wordObserve h)

def WordSpanMonochromatic {b n k m : Nat} {α γ : Type*}
    (c : WordObservation b n α → γ) (f : Word b n m α) : Prop :=
  ∀ g h : Word b n k α,
    KVariableWord.Refines g f → KVariableWord.Refines h f →
    c (wordObserve g) = c (wordObserve h)

/-- On alphabets with two letters, the corrected syntax and span conclusions
coincide.  No such equivalence is asserted for unary alphabets. -/
theorem wordMonochromatic_iff_span
    {b n k m : Nat} {α γ : Type*}
    (hα : SpanAudit.HasTwoLetters α)
    (c : WordObservation b n α → γ) (f : Word b n m α) :
    WordMonochromatic (k := k) c f ↔ WordSpanMonochromatic (k := k) c f := by
  constructor
  · intro hc g h hg hh
    exact hc g h ((KVariableWord.refines_iff_syntactic hα g f).1 hg)
      ((KVariableWord.refines_iff_syntactic hα h f).1 hh)
  · intro hc g h hg hh
    exact hc g h (KVariableWord.syntacticRefines_refines g f hg)
      (KVariableWord.syntacticRefines_refines h f hh)

def StarredMonochromatic {b n l m : Nat} {α γ : Type*}
    (c : StarredObservation b n α → γ) (f : Word b n m α) : Prop :=
  ∀ U V : Starred b n l α,
    StarredBelow U f → StarredBelow V f →
    c (starredObserve U) = c (starredObserve V)

theorem starredMonochromatic_of_syntacticRefines
    {b n l k m : Nat} {α γ : Type*}
    {c : StarredObservation b n α → γ}
    {g : Word b n m α} {f : Word b n k α}
    (hc : StarredMonochromatic (l := l) c f)
    (hgf : KVariableWord.SyntacticRefines g f) :
    StarredMonochromatic (l := l) c g := by
  intro U V hU hV
  exact hc U V (starredBelow_of_syntacticRefines hgf hU)
    (starredBelow_of_syntacticRefines hgf hV)

/-- Definition-24 simplicity with an explicit boundary selector and subset.
The selector must be supplied by the separately audited canonical-map API.
The comparison of words retains rooted symbols, not just evaluations. -/
def SimpleWith {b n l : Nat} {α γ A : Type*}
    (point : Starred b n l α → A → Node b) (B₂ : Set A)
    (c : StarredObservation b n α → γ) : Prop :=
  ∀ U V : Starred b n l α,
    (∀ t, t ∈ SkewTree.interior U.tree ↔ t ∈ SkewTree.interior V.tree) →
    (∀ a, a ∈ B₂ → point U a = point V a) →
    (∀ s : BoundedNode b n,
      (∀ a, a ∈ B₂ → ¬ IsPrefix (point U a) s.1) →
      CutPreservation.underlyingSymbol U.word s =
        CutPreservation.underlyingSymbol V.word s) →
    c (starredObserve U) = c (starredObserve V)

def Simple {b n l : Nat} {α γ A : Type*}
    (point : Starred b n l α → A → Node b)
    (c : StarredObservation b n α → γ) : Prop :=
  ∃ B₂ : Set A, SimpleWith point B₂ c

/-- Corrected Theorem 3 at one ambient height.  This is a target proposition. -/
def TreeRamseyAt (b n k m : Nat) (α γ : Type*) : Prop :=
  ∀ c : WordObservation b n α → γ,
    ∃ f : Word b n m α, WordMonochromatic (k := k) c f

/-- Corrected Theorem 25 at one height, conditional on the specified selector
convention.  Merely defining this proposition does not prove it. -/
def StarredRamseyAt (b n l m : Nat) (α γ A : Type*)
    (point : Starred b n l α → A → Node b) : Prop :=
  ∀ c : StarredObservation b n α → γ,
    Simple point c →
      ∃ f : Word b n m α, StarredMonochromatic (l := l) c f

/-- The actual mixed-product existence target of Theorem 13.  In particular,
`Good` is a CONCLUSION here, not an input to an existence claim. -/
def MixedRamseyAt (b n d k : Nat) (α γ : Type*)
    (kind : Fin d → MixedProduct.CoordKind) : Prop :=
  ∀ c : MixedProduct.Element b n d α kind → γ,
    ∃ f : MixedProduct.VariableWord b n d k α
        (SkewTree.forwardAuxB (b := b)) kind,
      MixedProduct.Good c f

/-- The product target uses genuinely vector-complete supports, including
cross-coordinate order and level separation, not arbitrary scalar tuples. -/
def ProductRamseyAt (b n d k m : Nat) (α γ : Type*) : Prop :=
  ∀ c : (Fin d → WordObservation b n α) → γ,
    ∃ f : MixedProduct.VectorVariableWord b n d m α
        (SkewTree.forwardAuxB (b := b)),
      ∀ g h : MixedProduct.VectorVariableWord b n d k α
          (SkewTree.forwardAuxB (b := b)),
        (∀ i, KVariableWord.SyntacticRefines (g.components i) (f.components i)) →
        (∀ i, KVariableWord.SyntacticRefines (h.components i) (f.components i)) →
        c (fun i => wordObserve (g.components i)) =
          c (fun i => wordObserve (h.components i))

/-- An actual positive eventual threshold.  The inequality is non-strict,
as in the source PDF, and there is no value when existence is unproved. -/
def EventualBound (P : Nat → Prop) (N : Nat) : Prop :=
  0 < N ∧ ∀ n, N ≤ n → P n

theorem eventualBound_mono {P : Nat → Prop} {N M : Nat}
    (h : EventualBound P N) (hNM : N ≤ M) : EventualBound P M := by
  exact ⟨lt_of_lt_of_le h.1 hNM, fun n hMn => h.2 n (le_trans hNM hMn)⟩

/-- A least bound is introduced ONLY after an existence proof is supplied. -/
noncomputable def leastBound (P : Nat → Prop)
    (h : ∃ N, EventualBound P N) : Nat := Nat.find h

theorem leastBound_spec (P : Nat → Prop) (h : ∃ N, EventualBound P N) :
    EventualBound P (leastBound P h) := Nat.find_spec h

theorem leastBound_le (P : Nat → Prop) (h : ∃ N, EventualBound P N)
    {N : Nat} (hN : EventualBound P N) : leastBound P h ≤ N :=
  Nat.find_min' h hN

/-- Alphabet size is explicit, including in the partial-tree target below. -/
def TGRBound (b ell k m r N : Nat) : Prop :=
  EventualBound (fun n => TreeRamseyAt b n k m (Fin ell) (Fin r)) N

/-- The canonical-alphabet formulation of the qualitative corrected
Theorem-3 target, including unary alphabets through syntactic refinement.
Alphabet-renaming transport is a separate source-comparison obligation.
No proof is asserted here. -/
def CorrectedTheorem3 : Prop :=
  ∀ b ell k m r : Nat,
    0 < b → 0 < ell → 0 < k → 0 < m → 0 < r →
    ∃ N : Nat, TGRBound b ell k m r N

def PTGRBound (b ell l m r N : Nat) {A : Type*}
    (point : ∀ n, Starred b n l (Fin ell) → A → Node b) : Prop :=
  EventualBound
    (fun n => StarredRamseyAt b n l m (Fin ell) (Fin r) A (point n)) N

/-- Qualitative partial-tree target at the given parameters.  `l = 0`
is allowed; its singleton-root selector convention belongs to Track E.
The selector argument must be instantiated with that audited convention. -/
def CorrectedTheorem25 (b ell l m r : Nat) {A : Type*}
    (point : ∀ n, Starred b n l (Fin ell) → A → Node b) : Prop :=
  0 < b → 0 < ell → 0 < m → 0 < r →
    ∃ N : Nat, PTGRBound b ell l m r N point

/-- The complete tree's node count, valid also at branching number one.
No division by `b - 1` or special-case convention is needed. -/
def completeNodeCount (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => completeNodeCount b k + b ^ k

theorem completeNodeCount_one (k : Nat) : completeNodeCount 1 k = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [completeNodeCount, ih]

end DualTree.CorrectedTheoremSpec
