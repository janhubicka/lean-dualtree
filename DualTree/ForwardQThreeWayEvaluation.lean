import DualTree.ForwardQThreeWayConeWordAssembly

/-!
# Evaluated meaning of the actual three-way decoded corrected-Q word

The previously verified source-facing construction
ForwardQThreeWayConeWordAssembly.ConeData.onActualStarredQ
builds a genuine starred word on the actual corrected Q support
from explicit local root-alignment hypotheses.

We now verify exactly what its symbols mean, not merely their
well-typedness: in a selected projected cone, an original letter
stays constant, an auxiliary letter is interpreted through that
cone's decoder, and a genuine cone variable becomes the selected
old-source variable root. Consequently every evaluation under an
assignment of original source variables agrees pointwise with
the exhaustive three-way local evaluation formula.

Outside the union of marked projected cones, both the symbol and
its evaluated letter agree with the original source word. Multiple
occurrences of one local cone variable are mapped uniformly to
the same source variable, including when its occurrences are at
different ambient homogeneous-tree positions.

These are algebraic/evaluation identities, not the specific
decoder choices of printed Lemma 27, and they do not prove that
the pullback colouring is smooth or simple.
-/

namespace DualTree.ForwardQThreeWayEvaluation

open ForwardSourceQTree
open ForwardQThreeWayConeWordAssembly

/-- An original local alphabet letter survives the actual
starred-Q assembly unchanged at each point of its cone. -/
theorem original_letter_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1)
    (a : α)
    (hraw : d.raw i t = Sum.inl (Sum.inl a)) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      Sum.inl a := by
  rw [d.onActualStarredQ_symbol_inside hb c x hTbound i t ht]
  change d.localSymbol i t = Sum.inl a
  exact ConeWordLift.liftWord_original
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t a hraw

/-- Auxiliary letters inside an actual marked cone have
exactly the explicit per-cone decoding prescribed by ConeData. -/
theorem auxiliary_letter_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1)
    (a : Aux)
    (hraw : d.raw i t = Sum.inl (Sum.inr a)) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      d.decodeAux i a := by
  rw [d.onActualStarredQ_symbol_inside hb c x hTbound i t ht]
  change d.localSymbol i t = d.decodeAux i a
  exact ConeWordLift.liftWord_auxiliary
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t a hraw

/-- A genuine local cone variable becomes precisely its assigned
original source variable, never an auxiliary alphabet letter. -/
theorem cone_variable_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1)
    (z : κ)
    (hraw : d.raw i t = Sum.inr z) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      Sum.inr (d.coneRoot i z) := by
  rw [d.onActualStarredQ_symbol_inside hb c x hTbound i t ht]
  change d.localSymbol i t = Sum.inr (d.coneRoot i z)
  exact ConeWordLift.liftWord_variable
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t z hraw

/-- The same local cone-variable name is translated
uniformly at every occurrence in its selected Q cone. -/
theorem cone_variable_fibre_uniform
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (s t : BoundedNode b n)
    (hs : IsPrefix (markedProjection c x.1 i).1 s.1)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1)
    (z : κ)
    (hraws : d.raw i s = Sum.inr z)
    (hrawt : d.raw i t = Sum.inr z) :
    (d.onActualStarredQ hb c x hTbound).word.word s =
      (d.onActualStarredQ hb c x hTbound).word.word t := by
  exact (cone_variable_inside hb c x hTbound d i s hs z hraws).trans
    (cone_variable_inside hb c x hTbound d i t ht z hrawt).symm

/-- For every assignment of old source variable names, the
evaluated actual Q word agrees with the exhaustive local
original/auxiliary/cone-variable decoding at selected points. -/
theorem eval_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1)
    (σ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol σ
      ((d.onActualStarredQ hb c x hTbound).word.word t) =
      match d.raw i t with
      | Sum.inl (Sum.inl a) => a
      | Sum.inl (Sum.inr u) =>
          SpanAudit.evalSymbol σ (d.decodeAux i u)
      | Sum.inr z => σ (d.coneRoot i z) := by
  rw [d.onActualStarredQ_symbol_inside hb c x hTbound i t ht]
  change SpanAudit.eval
    (ConeWordLift.liftWord (d.raw i) (d.decodeAux i) (d.coneRoot i))
    σ t = _
  exact congrFun
    (ConeWordLift.eval_liftWord
      (d.raw i) (d.decodeAux i) (d.coneRoot i) σ) t

/-- Outside every marked projected Q cone, evaluation is
exactly the evaluation of the unchanged original source word. -/
theorem eval_outside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (t : BoundedNode b n)
    (ht : ∀ i : MixedProduct.BulletIndex (kind c),
      ¬ IsPrefix (markedProjection c x.1 i).1 t.1)
    (σ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol σ
      ((d.onActualStarredQ hb c x hTbound).word.word t) =
      SpanAudit.evalSymbol σ (c.source.word.word t) := by
  exact congrArg (SpanAudit.evalSymbol σ)
    (d.onActualStarredQ_symbol_outside hb c x hTbound t ht)

end DualTree.ForwardQThreeWayEvaluation
