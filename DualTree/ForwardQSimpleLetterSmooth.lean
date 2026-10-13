import DualTree.ForwardQAmbientFibreSpan
import DualTree.ForwardQStarredSmoothPartitions

/-!
# The B₂ = ∅ simplicity-to-smoothness passage for the actual fibrewise Q

The corrected Lemma 27 source has an original ambient variable word f,
a starred refinement g' = f[rho], and a mixed product over the
enlarged alphabet Lambda + Fin (m+1).

When the Definition 24 simplicity witness has B₂ = ∅, two starred
outputs refining f get equal colours provided their interior sets
and their ENTIRE ambient variable words are equal.  No equality of
the terminal Q support is asserted: at Gamma1 coordinates the chosen
D2 marked points may move.

Choose Gamma1 = all selected D2 coordinates.  Definition 21's
SmoothRelated relation now fixes every coordinate WORD, not the D2
points.  The genuine Q decoder is fibrewise on the original ambient
f, so it depends only on the coordinate words and not on any selected
D2 marked point.  The Q interior is always the original source
interior, independently of marked-point positions.

These facts prove the specific induced colouring is smooth in this
genuine B₂-empty case.  The classwise extension lemma gives a total
smooth colouring of the ENTIRE enlarged mixed-product input space.

All of this is for the forward-corrected Q construction, conditional
on the explicitly supplied syntactic source refinement f[rho] = g'.
It does NOT prove arbitrary B₂, the paper's reverse-order construction,
or the final Ramsey variable-word refinement and iteration.
-/

namespace DualTree.ForwardQSimpleLetterSmooth

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord

/-- Sampling a local enlarged coordinate uses its actual word,
not the selected bullet/marked point. -/
theorem sampled_eq_of_words
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c)
    (hw : ∀ i, x.words i = y.words i)
    (i : ForwardQFullFrontierWord.Index c)
    (t : BoundedNode b n) :
    ForwardQEnlargedConstantWords.sampledEnlarged c x fallback i t =
      ForwardQEnlargedConstantWords.sampledEnlarged c y fallback i t := by
  classical
  have heq : x.words = y.words := funext hw
  simp [ForwardQEnlargedConstantWords.sampledEnlarged, heq]

/-- The genuine late-fibre R_i decoder reads the same letter
when every selected enlarged coordinate word is the same. -/
theorem decodeAmbientRoot_eq_of_words
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (hw : ∀ i, x.words i = y.words i)
    (v : c.ambient.Vars) :
    decodeAmbientRoot c fallback x v =
      decodeAmbientRoot c fallback y v := by
  cases hsel : ForwardQFullFrontierWord.selectedFrontier c.core v.1 with
  | none =>
      simp [decodeAmbientRoot, hsel]
  | some i =>
      have hletter :=
        sampled_eq_of_words c.core fallback x y hw i v.1
      simp only [decodeAmbientRoot, hsel]
      rw [hletter]

/-- The full ambient Q words agree on EVERY original f-fibre
(and also at original f-constant positions) under equality of
all enlarged coordinate words.  It is NOT merely a projected
root-coordinate identity. -/
theorem fibreQSymbol_eq_of_words
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (hw : ∀ i, x.words i = y.words i)
    (s : BoundedNode b n) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  cases hf : c.ambient.word s with
  | inl a =>
      simp [fibreQSymbol, hf]
  | inr v =>
      by_cases hcut : ForwardAux v.1.1 c.core.cut
      · simp [fibreQSymbol, hf, hcut]
      · simpa [fibreQSymbol, hf, hcut] using
          decodeAmbientRoot_eq_of_words c fallback x y hw v

/-- If every D₂ coordinate lies in Gamma1, Definition 21
smoothness fixes ALL D0/D2 local coordinate words, but not
the D₂ marked points. -/
theorem words_eq_of_all_gamma1
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c)
    (hxy : MixedProduct.SmoothRelated (fun _ => true) x y) :
    ∀ i : ForwardQFullFrontierWord.Index c,
      x.words i = y.words i := by
  intro i
  by_cases hi : kind c i = MixedProduct.CoordKind.bullet
  · have hbullet := hxy.2.2
        (⟨i, hi⟩ : MixedProduct.BulletIndex (kind c))
    simpa using hbullet
  · exact hxy.1 i hi

/-- In any two actual corrected Q outputs, the interior is
the same old source interior, irrespective of the D₂ points. -/
theorem Q_interiors_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (t : Node b) :
    t ∈ SkewTree.interior (fibreQStarredWord hb c fallback x).tree ↔
      t ∈ SkewTree.interior (fibreQStarredWord hb c fallback y).tree := by
  change
    t ∈ SkewTree.interior
      (nodes c.core (ForwardQEnlargedConstantWords.eraseAux
        c.core fallback x.1)).toList ↔
    t ∈ SkewTree.interior
      (nodes c.core (ForwardQEnlargedConstantWords.eraseAux
        c.core fallback y.1)).toList
  exact
    (ForwardQInteriorExact.Q_interior_iff_original hb c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback x.1) t).trans
    (ForwardQInteriorExact.Q_interior_iff_original hb c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback y.1) t).symm

/-- The actual symbol of a starred variable word with its
variable indexed by the ROOT node, rather than by a proof
that the node belongs to a particular support list. This is
the honest comparable notion of full word equality when two
starred refinements have different support-list representations. -/
def rootLabel
    {b n l : Nat} {α : Type*}
    (u : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (s : BoundedNode b n) : Sum α (BoundedNode b n) :=
  match u.word.word s with
  | Sum.inl a => Sum.inl a
  | Sum.inr v => Sum.inr v.1

/-- The finished Q output's common source-variable-root labels
are recovered by explicitly rewriting its WORD field, without
unfolding the large dependent starred-word constructor. -/
theorem rootLabel_fibreQ
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (s : BoundedNode b n) :
    rootLabel (fibreQStarredWord hb c fallback w) s =
      (match fibreQSymbol c fallback w.1 s with
       | Sum.inl a => Sum.inl a
       | Sum.inr v => Sum.inr v.1) := by
  unfold rootLabel
  rw [fibreQStarredWord_symbol hb c fallback w s]

/-- Exact special case of Definition 24 with B₂ empty:
for two starred refinements of the SAME ambient f, equal
interiors and equal full words force equal colours.

This is stated as a predicate on the original colouring,
without silently treating all arbitrary colourings as simple. -/
def LetterSimpleWithinAmbient
    {b n l k m : Nat} {α γ : Type*}
    (c : FibreFrame b n l k m α)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ) : Prop :=
  ∀ (u v : StarredSignature.StarredWord b n l α
    (SkewTree.forwardAuxB (b := b))),
    ((∀ t : Node b, t ∈ u.tree → t ∈ c.core.T) ∧
      u.word.span ⊆ c.ambient.span) →
    ((∀ t : Node b, t ∈ v.tree → t ∈ c.core.T) ∧
      v.word.span ⊆ c.ambient.span) →
    (∀ t : Node b,
      t ∈ SkewTree.interior u.tree ↔
      t ∈ SkewTree.interior v.tree) →
    (∀ s : BoundedNode b n, rootLabel u s = rootLabel v s) →
    color u = color v

/-- Genuine B₂-empty simplicity of the original starred
colouring implies Gamma1-all smoothness of the *specific*
corrected fibrewise Q pullback, not an arbitrary pullback. -/
theorem simple_pullback_smooth_allGamma1
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : LetterSimpleWithinAmbient c color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated (fun _ => true) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  have hwords := words_eq_of_all_gamma1 c.core x.1 y.1 hxy
  apply hsimple
    (fibreQStarredWord hb c fallback x)
    (fibreQStarredWord hb c fallback y)
  · exact ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient
      hb c fallback x
  · exact ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient
      hb c fallback y
  · intro t
    exact Q_interiors_eq hb c fallback x y t
  · intro s
    rw [rootLabel_fibreQ hb c fallback x s,
        rootLabel_fibreQ hb c fallback y s,
        fibreQSymbol_eq_of_words c fallback x.1 y.1 hwords s]

/-- The pulled-back B₂-empty simple colouring of the corrected
enlarged starred subtype extends to a total, Gamma1-all
smooth colouring on the WHOLE enlarged mixed product. -/
theorem exists_total_smooth_color
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : LetterSimpleWithinAmbient c color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ x : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total x.1 = color (fibreQStarredWord hb c fallback x)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated (fun _ => true) x y →
          total x = total y) := by
  let D : Set (ForwardQEnlargedConstantWords.EnlargedInput c.core) :=
    {w | ForwardQActualStarredSpace.IsStarred c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w)}
  let pulled :
      {w : ForwardQEnlargedConstantWords.EnlargedInput c.core //
        w ∈ D} → γ :=
    fun w => color (fibreQStarredWord hb c fallback ⟨w.1, w.2⟩)
  have hcompat :
      ∀ (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
        (hx : x ∈ D) (hy : y ∈ D),
        MixedProduct.SmoothRelated (fun _ => true) x y →
          pulled ⟨x, hx⟩ = pulled ⟨y, hy⟩ := by
    intro x y hx hy hxy
    exact simple_pullback_smooth_allGamma1
      hb c fallback color hsimple ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨total, hagree, hsmooth⟩ :=
    MixedProduct.exists_smooth_extension
      (fun _ => true) D pulled fallbackColor hcompat
  refine ⟨total, ?_, hsmooth⟩
  intro x
  exact hagree x.1 x.2

end DualTree.ForwardQSimpleLetterSmooth
