import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQVisibleAncestorDecoder

/-!
# The enlarged-alphabet, VARIABLE-FREE input stage of Lemma 27

The original Lemma 27 first constructs Q on ordinary mixed-product
ELEMENTS over Lambda' = Lambda + {0,...,m'}, not on independent local
variable words. Genuine cone variables enter only in the subsequent
mixed-product variable-word refinement. Thus Hall's matching hypothesis
is NOT needed to define the initial Q map.

Use the existing forward-corrected D0/D2 frontier geometry. Erasing
auxiliary labels changes ONLY coordinate letters, never marked points;
hence it preserves the exact corrected starred-domain condition and Q
support. Sample the actual enlarged-alphabet coordinate word at its
canonical cone projection P_i(z). Decode original letters as themselves
and auxiliary letters via the checked visible-ancestor R_i. The local
variable-name type is empty: NO Hall condition, name transport or
independent-variable identification is imposed.

This verifies the actual enlarged-input Q symbol equation at EACH
canonical projected support position. It is not YET the FULL printed
pointwise definition of g_w on all b^{<N}: our present Frame lacks the
original ambient complete-support variable word f and its variable
fibres. A word patched merely according to the ambient position's
frontier cone is not automatically the paper's fibrewise formula.
In particular positions with f(s) a constant or f(s)=v_t for an
unprojected root need their separate printed cases (i)--(v).
This limitation is kept explicit to avoid a false Lemma 27 validation.
-/

namespace DualTree.ForwardQEnlargedConstantWords

open ForwardSourceQTree

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- Mixed-product ordinary WORDS over the source's disjoint
enlarged alphabet Lambda + {0,...,m}; all D2 points are unchanged. -/
abbrev EnlargedInput
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  MixedProduct.Element b (k - (m + 1))
    (ForwardSortedFrontiers.frontiers c.T c.cut).length
    (Sum α (Fin (m + 1))) (kind c)

/-- Forget only auxiliary alphabet labels, filling them with
an old letter. Preserve up- and bullet-point data IDENTICALLY. -/
def eraseAux
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedInput c) : Input c where
  words := fun i t =>
    match w.words i t with
    | Sum.inl a => a
    | Sum.inr _ => fallback
  upPoint := w.upPoint
  bulletPoint := w.bulletPoint

theorem eraseAux_bulletPoint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedInput c)
    (i : MixedProduct.BulletIndex (kind c)) :
    (eraseAux c fallback w).bulletPoint i = w.bulletPoint i :=
  rfl

/-- The precise corrected starred condition on enlarged-alphabet
ordinary inputs, defined on their UNCHANGED selected marked points. -/
abbrev EnlargedStarredInput
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α) :=
  {w : EnlargedInput c //
    ForwardQActualStarredSpace.IsStarred c (eraseAux c fallback w)}

/-- A genuine enlarged-alphabet starred input yields the existing
corrected original-alphabet starred Q geometry, with no changes
to any selected marker or local starred-order requirement. -/
def toStarredInput
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback) :
    ForwardQActualStarredSpace.StarredInput c :=
  ⟨eraseAux c fallback w.1, w.2⟩

/-- The selected Q support depends only on D2 marked points,
not on any original or auxiliary coordinate letter. -/
theorem eraseAux_Q_nodes_invariant
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback₁ fallback₂ : α)
    (w : EnlargedInput c) :
    nodes c (eraseAux c fallback₁ w) =
      nodes c (eraseAux c fallback₂ w) := by
  classical
  simp [nodes, markedProjection, eraseAux]

/-- Read an ACTUAL enlarged-alphabet coordinate at an arbitrary
bounded ambient position using the source's canonical inverse
support address. Positions outside T or outside the certified
common safe cone domain receive an original fallback letter. -/
noncomputable def sampledEnlarged
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (w : EnlargedInput c)
    (fallback : α)
    (i : Index c)
    (t : BoundedNode b n) :
    Sum α (Fin (m + 1)) := by
  classical
  exact if ht : t.1 ∈ c.T then
    let u : {v : Node b // v ∈ c.T} := ⟨t.1, ht⟩
    if hz : InHomTree (k - (m + 1))
        (ForwardQActualCoordinateWord.tailOfTNode c i u) then
      w.words i ⟨ForwardQActualCoordinateWord.tailOfTNode c i u, hz⟩
    else Sum.inl fallback
  else Sum.inl fallback

/-- The canonical P_i(z) reads precisely the GIVEN enlarged
coordinate letter; the inverse-address calculation, not an
arbitrary guessed projection, supplies the equality. -/
theorem sampledEnlarged_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (w : EnlargedInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    sampledEnlarged c w fallback i
      (ForwardQActualCoordinateWord.projectedBounded
        c hTbound i z) = w.words i z := by
  classical
  have htail :=
    ForwardQActualCoordinateWord.tailOfTNode_projectLocal c i z
  simp [sampledEnlarged,
    ForwardQActualCoordinateWord.projectedBounded,
    (ForwardQActualCoordinateWord.projectLocal c i z).2,
    htail, z.2]

/-- Every raw local symbol is an ACTUAL enlarged alphabet letter.
The genuine cone-variable type is empty at this first Q stage. -/
noncomputable def rawEnlarged
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (w : EnlargedInput c)
    (fallback : α) :
    Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) PEmpty :=
  fun i t => Sum.inl (sampledEnlarged c w fallback i t)

theorem rawEnlarged_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (w : EnlargedInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    rawEnlarged c w fallback i
      (ForwardQActualCoordinateWord.projectedBounded
        c hTbound i z) = Sum.inl (w.words i z) := by
  simp [rawEnlarged,
    sampledEnlarged_projected c w fallback hTbound i z]

/-- The corrected Q decoder with genuinely enlarged local alphabet:
both old letters and R_i auxiliary labels are used; no local
variable root matching hypothesis is needed or supplied. -/
noncomputable def enlargedConeData
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (w : EnlargedInput c)
    (fallback : α) :
    ForwardQFullFrontierThreeWay.ConeData
      c (Fin (m + 1)) PEmpty :=
  ForwardQVisibleAncestorDecoder.coneData
    c fallback (rawEnlarged c w fallback)
    (fun _ z => PEmpty.elim z)
    (by intro i t z _ _; cases z)

/-- All actual enlarged input coordinates share the same legal,
corrected-starred Q support. Auxiliary letters neither alter the
tree nor require additional point-order conditions. -/
theorem enlarged_Q_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t) :
    ((enlargedConeData c w.1 fallback).onActualStarredQ
      hb c (toStarredInput c fallback w) hTbound).tree =
      (nodes c (eraseAux c fallback w.1)).toList :=
  (enlargedConeData c w.1 fallback).onActualStarredQ_tree
    hb c (toStarredInput c fallback w) hTbound

/-- The source-facing Q case (iv) at EVERY genuinely projected
support address: old letters remain old letters and each actual
auxiliary letter is translated through the certified R_i.

No Hall matching: these are CONSTANT mixed-product coordinates.
The full ambient f-fibrewise piecewise definition remains open. -/
theorem enlarged_Q_symbol_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    ((enlargedConeData c w.1 fallback).onActualStarredQ
      hb c (toStarredInput c fallback w) hTbound).word.word
        (ForwardQActualCoordinateWord.projectedBounded
          c hTbound i z) =
      match w.1.words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux c fallback i j := by
  let d := enlargedConeData c w.1 fallback
  let t := ForwardQActualCoordinateWord.projectedBounded c hTbound i z
  have hcone :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 :=
    ForwardQActualCoordinateWord.projectLocal_cone c i z
  have hraw : d.raw i t = Sum.inl (w.1.words i z) := by
    change ForwardQVisibleAncestorDecoder.maskedRaw c fallback
      (rawEnlarged c w.1 fallback) i t = _
    rw [ForwardQVisibleAncestorDecoder.maskedRaw_inside
      c fallback (rawEnlarged c w.1 fallback) i t hcone]
    exact rawEnlarged_projected c w.1 fallback hTbound i z
  have hsymbol :
      (d.onActualStarredQ hb c (toStarredInput c fallback w)
        hTbound).word.word t = d.localSymbol i t :=
    d.symbol_inside hb c (toStarredInput c fallback w)
      hTbound i t hcone
  cases hlocal : w.1.words i z with
  | inl a =>
      rw [hlocal] at hraw
      rw [hsymbol]
      change ConeWordLift.liftWord (d.raw i) (d.decodeAux i)
        (d.coneRoot i) t = Sum.inl a
      exact ConeWordLift.liftWord_original (d.raw i)
        (d.decodeAux i) (d.coneRoot i) t a hraw
  | inr j =>
      rw [hlocal] at hraw
      rw [hsymbol]
      change ConeWordLift.liftWord (d.raw i) (d.decodeAux i)
        (d.coneRoot i) t =
        ForwardQVisibleAncestorDecoder.decodeAux c fallback i j
      exact ConeWordLift.liftWord_auxiliary (d.raw i)
        (d.decodeAux i) (d.coneRoot i) t j hraw

/-- At an original-letter position the corrected Q symbol is
exactly the original alphabet letter. -/
theorem enlarged_Q_original_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (a : α)
    (hletter : w.1.words i z = Sum.inl a) :
    ((enlargedConeData c w.1 fallback).onActualStarredQ
      hb c (toStarredInput c fallback w) hTbound).word.word
        (ForwardQActualCoordinateWord.projectedBounded
          c hTbound i z) = Sum.inl a := by
  rw [enlarged_Q_symbol_projected hb c fallback w hTbound i z, hletter]

/-- At an auxiliary-letter position the corrected Q symbol is
precisely the genuine source-facing visible-ancestor decoder R_i. -/
theorem enlarged_Q_auxiliary_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (j : Fin (m + 1))
    (hletter : w.1.words i z = Sum.inr j) :
    ((enlargedConeData c w.1 fallback).onActualStarredQ
      hb c (toStarredInput c fallback w) hTbound).word.word
        (ForwardQActualCoordinateWord.projectedBounded
          c hTbound i z) =
      ForwardQVisibleAncestorDecoder.decodeAux c fallback i j := by
  rw [enlarged_Q_symbol_projected hb c fallback w hTbound i z, hletter]

/-- The resulting decoded local Q value has the correct
two-case EVALUATED meaning under every old-root assignment. -/
theorem enlarged_Q_evaluated_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (fallback : α)
    (w : EnlargedStarredInput c fallback)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (τ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol τ
      (((enlargedConeData c w.1 fallback).onActualStarredQ
        hb c (toStarredInput c fallback w) hTbound).word.word
        (ForwardQActualCoordinateWord.projectedBounded
          c hTbound i z)) =
      match w.1.words i z with
      | Sum.inl a => a
      | Sum.inr j =>
          SpanAudit.evalSymbol τ
            (ForwardQVisibleAncestorDecoder.decodeAux c fallback i j) := by
  rw [enlarged_Q_symbol_projected hb c fallback w hTbound i z]
  cases hletter : w.1.words i z with
  | inl a => rfl
  | inr j => rfl

end DualTree.ForwardQEnlargedConstantWords
