import DualTree.ForwardQSafeFibreSmoothness

/-!
# The input-independent original f-fibre cases of the corrected Lemma 27 Q

The full ambient-fibrewise Q map distinguishes:
  (i) original constant fibres;
  (ii) old/early variable fibres, whose symbols come from fixed g';
  (iii) late fibres with no selected frontier (fallback alphabet letter);
  (iv) late fibres with a selected frontier but inverse address beyond the
       certified common safe tail domain (also the same fallback).

All four families have equal decoded Q symbols for ANY two enlarged mixed
inputs, without assuming smoothness or any Gamma1/Gamma2 partition.
In the source frame every variable root is a T support vertex, so the
unsafe-tail case uses the real inverse-address suffix inside T, not an
artificial out-of-support case.

We package these cases in a single DefaultFibre predicate and prove
equality of the ACTUAL finished starred Q word on every default fibre.

This complements ForwardQSafeFibreSmoothness, which handles safe post-cut
roots outside the Gamma2 marked cones. It does not yet identify the
abstract simplicity markers A with the literal corrected R or prove
Lemma 27's final Ramsey refinement.
-/

namespace DualTree.ForwardQFibreDefaults

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreSymbol
open ForwardQAmbientFibreLegalWord

/-- Original ambient f-constants are fixed by any two Q inputs. -/
theorem equal_at_ambient_constant
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (a : α)
    (hs : c.ambient.word s = Sum.inl a) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  calc
    fibreQSymbol c fallback x s = Sum.inl a :=
      fibreQ_original_constant c fallback x s a hs
    _ = fibreQSymbol c fallback y s :=
      (fibreQ_original_constant c fallback y s a hs).symm

/-- Every original f-fibre rooted at/before the forward cut uses
the same fixed g' symbol, regardless of the input mixed words. -/
theorem equal_on_early_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hbefore : ForwardAux v.1.1 c.core.cut) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  calc
    fibreQSymbol c fallback x s = c.core.source.word.word s :=
      fibreQ_before_cut c fallback x s v hs hbefore
    _ = fibreQSymbol c fallback y s :=
      (fibreQ_before_cut c fallback y s v hs hbefore).symm

/-- Late f-fibres with no selected frontier receive the SAME
specified fallback letter, irrespective of mixed-product words. -/
theorem equal_on_no_frontier_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hafter : ¬ ForwardAux v.1.1 c.core.cut)
    (hnone : ForwardQFullFrontierWord.selectedFrontier
      c.core v.1 = none) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  calc
    fibreQSymbol c fallback x s = Sum.inl fallback :=
      fibreQ_unprojected_no_frontier c fallback x s v
        hs hafter hnone
    _ = fibreQSymbol c fallback y s :=
      (fibreQ_unprojected_no_frontier c fallback y s v
        hs hafter hnone).symm

/-- Outside the certified local tail domain, the REAL selected
coordinate sample is the constant original fallback letter.
The argument keeps the ambient root in the genuine T support. -/
theorem sampledEnlarged_unsafe_fallback
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c)
    (i : ForwardQFullFrontierWord.Index c)
    (t : BoundedNode b n)
    (ht : t.1 ∈ c.T)
    (hunsafe : ¬ InHomTree (k - (m + 1))
      (ForwardQActualCoordinateWord.tailOfTNode c i ⟨t.1, ht⟩)) :
    ForwardQEnlargedConstantWords.sampledEnlarged
      c w fallback i t = Sum.inl fallback := by
  classical
  simp [ForwardQEnlargedConstantWords.sampledEnlarged,
    ht, hunsafe]

/-- Any late original f-root with a selected frontier but an
unsafe intrinsic local tail decodes to the fixed fallback. -/
theorem decodeAmbientRoot_unsafe_fallback
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars)
    (i : ForwardQFullFrontierWord.Index c.core)
    (hsel : ForwardQFullFrontierWord.selectedFrontier c.core v.1 =
      some i)
    (hunsafe : ¬ InHomTree (k - (m + 1))
      (ForwardQActualCoordinateWord.tailOfTNode c.core i
        ⟨v.1.1, (c.ambient_support_T v.1).1 v.2⟩)) :
    decodeAmbientRoot c fallback w v = Sum.inl fallback := by
  have ht : v.1.1 ∈ c.core.T :=
    (c.ambient_support_T v.1).1 v.2
  have hsamp :
      ForwardQEnlargedConstantWords.sampledEnlarged
        c.core w fallback i v.1 = Sum.inl fallback :=
    sampledEnlarged_unsafe_fallback c.core fallback w
      i v.1 ht hunsafe
  simp [decodeAmbientRoot, hsel, hsamp]

/-- Actual Q words agree on the ENTIRE unsafe original f-fibre,
not only at its ambient variable root. -/
theorem equal_on_unsafe_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hafter : ¬ ForwardAux v.1.1 c.core.cut)
    (i : ForwardQFullFrontierWord.Index c.core)
    (hsel : ForwardQFullFrontierWord.selectedFrontier c.core v.1 =
      some i)
    (hunsafe : ¬ InHomTree (k - (m + 1))
      (ForwardQActualCoordinateWord.tailOfTNode c.core i
        ⟨v.1.1, (c.ambient_support_T v.1).1 v.2⟩)) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  calc
    fibreQSymbol c fallback x s =
        decodeAmbientRoot c fallback x v :=
      fibreQ_after_cut c fallback x s v hs hafter
    _ = Sum.inl fallback :=
      decodeAmbientRoot_unsafe_fallback c fallback x
        v i hsel hunsafe
    _ = decodeAmbientRoot c fallback y v :=
      (decodeAmbientRoot_unsafe_fallback c fallback y
        v i hsel hunsafe).symm
    _ = fibreQSymbol c fallback y s :=
      (fibreQ_after_cut c fallback y s v hs hafter).symm

/-- The exact input-independent cases for an original ambient f
position. Constants always qualify. For an f-variable fibre,
qualifying roots are early, have no frontier, or have a selected
frontier but an inverse support tail outside the safe local domain. -/
def DefaultFibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (s : BoundedNode b n) : Prop :=
  ∀ v : c.ambient.Vars,
    c.ambient.word s = Sum.inr v →
      ForwardAux v.1.1 c.core.cut ∨
      ForwardQFullFrontierWord.selectedFrontier c.core v.1 = none ∨
      ∃ i : ForwardQFullFrontierWord.Index c.core,
        ForwardQFullFrontierWord.selectedFrontier c.core v.1 =
          some i ∧
        ¬ InHomTree (k - (m + 1))
          (ForwardQActualCoordinateWord.tailOfTNode c.core i
            ⟨v.1.1, (c.ambient_support_T v.1).1 v.2⟩)

/-- Every default original f-fibre has the same complete Q symbol
for ANY two mixed-product inputs (no smoothness hypothesis). -/
theorem equal_on_default_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (hdefault : DefaultFibre c s) :
    fibreQSymbol c fallback x s =
      fibreQSymbol c fallback y s := by
  cases hs : c.ambient.word s with
  | inl a =>
      exact equal_at_ambient_constant c fallback x y s a hs
  | inr v =>
      rcases hdefault v hs with hbefore | hnone | ⟨i, hsel, hunsafe⟩
      · exact equal_on_early_fibre c fallback x y s v hs hbefore
      · by_cases hbefore : ForwardAux v.1.1 c.core.cut
        · exact equal_on_early_fibre c fallback x y s v hs hbefore
        · exact equal_on_no_frontier_fibre c fallback x y s v
            hs hbefore hnone
      · by_cases hbefore : ForwardAux v.1.1 c.core.cut
        · exact equal_on_early_fibre c fallback x y s v hs hbefore
        · exact equal_on_unsafe_fibre c fallback x y s v hs
            hbefore i hsel hunsafe

/-- Transport the default-fibre equality to the finished legal
starred Q words, with actual corrected projected supports. -/
theorem starred_Q_equal_on_default_fibre
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (s : BoundedNode b n)
    (hdefault : DefaultFibre c s) :
    (fibreQStarredWord hb c fallback x).word.word s =
      (fibreQStarredWord hb c fallback y).word.word s := by
  change fibreQSymbol c fallback x.1 s =
    fibreQSymbol c fallback y.1 s
  exact equal_on_default_fibre c fallback x.1 y.1 s hdefault

end DualTree.ForwardQFibreDefaults
