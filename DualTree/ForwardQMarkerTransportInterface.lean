import DualTree.ForwardQAllExteriorFibres
import DualTree.ForwardQMarkerFingerprint

/-!
# The EXACT remaining canonical A-to-literal-R transport interface

Definition 24 fixes the canonical boundary A of the first l model
interior addresses and a partition A = B1 ⊔ B2. For the corrected
Lemma 27 mixed product, the geometric source construction instead
uses its literal signature marker family R, bijectively indexed by
the selected D2 frontier coordinates.

The preceding verified source-facing lemmas establish all THREE
simple-colouring observables on the actual Q outputs:
  * their interior node sets coincide;
  * actual projected Q marked points at Gamma2 coordinates agree;
  * their root-labelled full ambient words agree outside the
    corresponding projected successor cones.

This module states the missing bridge as EXPLICIT, testable data:
  (a) an equivalence e : A ≃ actual D2 bullet coordinates;
  (b) a canonical marker map I_U(a) on arbitrary starred output U;
  (c) its identification I_{Q(w)}(a)=P_{e(a)}(s_{e(a)}(w));
  (d) agreement between the Definition 24 subset B2⊆A
      and the Gamma2 indices e(B2).

Assuming ONLY this identified canonical-marker bridge and the exact
source Definition 24 simplicity predicate on starred refinements
of the ambient f, we prove that c∘Q is smooth on the corrected
enlarged mixed-product starred subtype AND extends to a TOTAL
smooth colouring of the full mixed-product input space.

This does not assert existence of the canonical A↔R identification
and does not prove the numerical Ramsey refinement or the printed
reverse-auxiliary-order Q construction. The entire purpose is
to isolate the precise remaining geometric hypothesis.
-/

namespace DualTree.ForwardQMarkerTransportInterface

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQAllExteriorFibres

/-- A genuine Definition 24-style simplicity hypothesis on ALL
starred refinements of the fixed ambient word f, with abstract
canonical signature markers A and their output-tree node map I.

The root-labelled word comparison avoids conflating different
dependent variable-name types for arbitrary starred refinements.
The marker successor cone is inclusive, as in Definition 21. -/
def CanonicalSimpleWithinAmbient
    {b n l k m : Nat} {α γ A : Type*}
    (c : FibreFrame b n l k m α)
    (canonicalPoint :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → A → Node b)
    (B2 : A → Prop)
    (color :
      StarredSignature.StarredWord b n l α
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
    (∀ a : A, B2 a →
      canonicalPoint u a = canonicalPoint v a) →
    (∀ s : BoundedNode b n,
      (∀ a : A, B2 a →
        ¬ IsPrefix (canonicalPoint u a) s.1) →
      ForwardQSimpleLetterSmooth.rootLabel u s =
        ForwardQSimpleLetterSmooth.rootLabel v s) →
    color u = color v

/-- Conditional final bridge for the actual Lemma 27 Q-pullback:
once the canonical A-markers of Definition 24 are identified with
the verified literal-R/D2 projections, any simple source colouring
induces a smooth colouring on the genuine corrected starred input.

The canonical marker correspondence is NOT derived in this theorem;
it remains an explicit hypothesis, including the B2/Gamma2 split. -/
theorem simple_pullback_smooth_of_canonical_marker_transport
    {b n l k m : Nat} {α γ A : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (canonicalPoint :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → A → Node b)
    (B2 : A → Prop)
    (markerIndex : A ≃ MixedProduct.BulletIndex (kind c.core))
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hpartition : ∀ a : A,
      B2 a ↔ gamma1 (markerIndex a) = false)
    (hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : A),
        canonicalPoint
          (fibreQStarredWord hb c fallback w) a =
        (markedProjection c.core
          (ForwardQEnlargedConstantWords.eraseAux
            c.core fallback w.1) (markerIndex a)).1)
    (color :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : CanonicalSimpleWithinAmbient c
      canonicalPoint B2 color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) := by
  apply hsimple
    (fibreQStarredWord hb c fallback x)
    (fibreQStarredWord hb c fallback y)
  · exact ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient
      hb c fallback x
  · exact ForwardQAmbientFibreSpan.fibreQStarredWord_refines_ambient
      hb c fallback y
  · intro t
    exact ForwardQSimpleLetterSmooth.Q_interiors_eq
      hb c fallback x y t
  · intro a hB2
    rw [hcanonical x a, hcanonical y a]
    have hg : gamma1 (markerIndex a) = false :=
      (hpartition a).1 hB2
    exact congrArg Subtype.val
      (ForwardQAmbientFibreSmoothObservable.gamma2_Q_markedProjection_eq_of_smooth
        c fallback x y gamma1 hxy (markerIndex a) hg)
  · intro s hout
    have houtside :
        ∀ j : MixedProduct.BulletIndex (kind c.core),
          gamma1 j = false →
          ¬ IsPrefix
            (markedProjection c.core
              (ForwardQEnlargedConstantWords.eraseAux
                c.core fallback x.1) j).1 s.1 := by
      intro j hj
      have ha : B2 (markerIndex.symm j) := by
        apply (hpartition (markerIndex.symm j)).2
        simpa only [Equiv.apply_symm_apply] using hj
      have hnode := hout (markerIndex.symm j) ha
      rw [hcanonical x (markerIndex.symm j),
        Equiv.apply_symm_apply] at hnode
      exact hnode
    have hword :=
      starred_Q_word_eq_outside_gamma2_cones
        hb c fallback x y gamma1 hxy s houtside
    change ForwardQAmbientFibreSymbol.fibreQSymbol c fallback x.1 s =
      ForwardQAmbientFibreSymbol.fibreQSymbol c fallback y.1 s at hword
    rw [ForwardQSimpleLetterSmooth.rootLabel_fibreQ
          hb c fallback x s,
        ForwardQSimpleLetterSmooth.rootLabel_fibreQ
          hb c fallback y s]
    exact congrArg
      (fun q : Sum α c.core.source.word.Vars =>
        match q with
        | Sum.inl a => Sum.inl a
        | Sum.inr v => Sum.inr v.1) hword

/-- Complete classwise extension of the particular simple-colouring
pullback to a TOTAL smooth colouring of the enlarged mixed product,
conditional precisely on the canonical A-to-D2 marker transport.

Once the missing canonical geometric identification is proved,
this is the full smooth-colouring input required before applying
the repaired mixed-product Ramsey theorem in Lemma 27. -/
theorem exists_total_smooth_pullback_of_canonical_marker_transport
    {b n l k m : Nat} {α γ A : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (canonicalPoint :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → A → Node b)
    (B2 : A → Prop)
    (markerIndex : A ≃ MixedProduct.BulletIndex (kind c.core))
    (gamma1 : MixedProduct.BulletIndex (kind c.core) → Bool)
    (hpartition : ∀ a : A,
      B2 a ↔ gamma1 (markerIndex a) = false)
    (hcanonical :
      ∀ (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
          c.core fallback) (a : A),
        canonicalPoint
          (fibreQStarredWord hb c fallback w) a =
        (markedProjection c.core
          (ForwardQEnlargedConstantWords.eraseAux
            c.core fallback w.1) (markerIndex a)).1)
    (color :
      StarredSignature.StarredWord b n l α
        (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple : CanonicalSimpleWithinAmbient c
      canonicalPoint B2 color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ x : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total x.1 = color (fibreQStarredWord hb c fallback x)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated gamma1 x y →
          total x = total y) := by
  let D : Set (ForwardQEnlargedConstantWords.EnlargedInput c.core) :=
    {w | ForwardQActualStarredSpace.IsStarred c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w)}
  let pulled :
      {w : ForwardQEnlargedConstantWords.EnlargedInput c.core //
        w ∈ D} → γ :=
    fun w => color (fibreQStarredWord hb c fallback ⟨w.1, w.2⟩)
  have hcompatible :
      ∀ (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
        (hx : x ∈ D) (hy : y ∈ D),
        MixedProduct.SmoothRelated gamma1 x y →
          pulled ⟨x, hx⟩ = pulled ⟨y, hy⟩ := by
    intro x y hx hy hxy
    exact simple_pullback_smooth_of_canonical_marker_transport
      hb c fallback canonicalPoint B2 markerIndex gamma1
      hpartition hcanonical color hsimple ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨total, hagree, hsmooth⟩ :=
    MixedProduct.exists_smooth_extension
      gamma1 D pulled fallbackColor hcompatible
  refine ⟨total, ?_, hsmooth⟩
  intro x
  exact hagree x.1 x.2

end DualTree.ForwardQMarkerTransportInterface
