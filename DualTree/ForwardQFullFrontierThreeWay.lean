import DualTree.ForwardQFullFrontierWord
import DualTree.ThreeWayQDecoderRootAlignment
import DualTree.ConeWordLift

/-!
# The actual full-frontier three-way decoded Q-word interface

The source's Lemma 27 word is defined using a separate cone
word at EVERY complete-support outside-cut frontier coordinate,
including ordinary (D0) and marked (D2) coordinates.

This is the full-frontier version of the previously checked
three-constructor translation for marked-point cones:
  original alphabet letters;
  auxiliary letters, decoded to an original letter/source variable;
  genuine cone variables, mapped to source variable roots.

Every decoded variable occurrence must lie above its old source
root. Under that explicit local alignment assumption, the
all-frontier disjoint-cone patch gives a legal StarredWord on the
genuine reconstructed Q support for each corrected starred input.
Exact pointwise and evaluated decoding identities are proved for
all frontier cones, including D0, and the old source word is used
outside the complete frontier family.

The particular raw words, the prescribed source R_i auxiliary
decoder and the cone-root transport from Lemma 27 are NOT yet
constructed. Nor is the induced colouring or Ramsey span shown
to respect the original proof's simplicity/iteration hypotheses.
-/

namespace DualTree.ForwardQFullFrontierThreeWay

open ForwardSourceQTree
open ForwardQFullFrontierWord

/-- Local data are indexed over EVERY forward-sorted frontier,
not just the D2 bullet subtype. Auxiliary and cone variable
roots are already represented as genuine old source Vars. -/
structure ConeData
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (Aux κ : Type*) where
  raw : Index c → BoundedNode b n → Sum (Sum α Aux) κ
  decodeAux : Index c → Aux → Sum α c.source.word.Vars
  coneRoot : Index c → κ → c.source.word.Vars
  auxiliaryAligned :
    ∀ (i : Index c) (t : BoundedNode b n)
      (a : Aux) (v : c.source.word.Vars),
      raw i t = Sum.inl (Sum.inr a) →
      decodeAux i a = Sum.inr v →
      IsPrefix v.1.1 t.1
  coneAligned :
    ∀ (i : Index c) (t : BoundedNode b n)
      (z : κ),
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1

/-- The exhaustively case-split local source symbol at an
actual homogeneous-tree position in frontier cone i. -/
def ConeData.localSymbol
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α}
    (d : ConeData c Aux κ)
    (i : Index c)
    (t : BoundedNode b n) :
    Sum α c.source.word.Vars :=
  ConeWordLift.liftWord (d.raw i) (d.decodeAux i)
    (d.coneRoot i) t

/-- Original and auxiliary symbols cannot create a variable
occurrence below its source root; the same holds of genuinely
transported cone variables, by the two local hypotheses. -/
theorem ConeData.localSymbol_aligned
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α}
    (d : ConeData c Aux κ)
    (i : Index c)
    (v : c.source.word.Vars)
    (t : BoundedNode b n)
    (h : d.localSymbol i t = Sum.inr v) :
    IsPrefix v.1.1 t.1 :=
  ThreeWayQDecoderRootAlignment.indexed_liftWord_root_aligned
    (fun w : c.source.word.Vars => w.1.1)
    d.raw d.decodeAux d.coneRoot
    d.auxiliaryAligned d.coneAligned i t v h

/-- Package all local decoded words into one global
root-valid variable word with the original source roots. -/
noncomputable def ConeData.toDecodedWord
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α}
    (d : ConeData c Aux κ) :
    ForwardQWordSymbolAssembly.DecodedWord c :=
  ForwardQFullFrontierWord.toDecodedWord c d.localSymbol
    (fun i v t h => d.localSymbol_aligned i v t h)

/-- On a corrected starred D2 input, each full-frontier
decoded map yields a legal starred word on the exact
forward-corrected support Q, not just on the ambient T. -/
noncomputable def ConeData.onActualStarredQ
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) :=
  d.toDecodedWord.onCorrectedQ hb c x.1
    ((ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      c x.1).1 x.2) hTbound

theorem ConeData.onActualStarredQ_tree
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ) :
    (d.onActualStarredQ hb c x hTbound).tree =
      (nodes c x.1).toList := rfl

/-- The actual star Q output inside ANY frontier cone i has
precisely the exhaustive local symbol after decoding. -/
theorem ConeData.symbol_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      d.localSymbol i t := by
  change ForwardQFullFrontierWord.patchedSymbol c d.localSymbol t =
    d.localSymbol i t
  exact ForwardQFullFrontierWord.patchedSymbol_inside
    c d.localSymbol i t hi

/-- Outside EVERY complete-support frontier cone, the
old source word is used verbatim, including variable roots. -/
theorem ConeData.symbol_outside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      c.source.word.word t := by
  change ForwardQFullFrontierWord.patchedSymbol c d.localSymbol t =
    c.source.word.word t
  exact ForwardQFullFrontierWord.patchedSymbol_outside
    c d.localSymbol t ht

/-- An original alphabet letter inside a full frontier cone
stays literally the same output letter. -/
theorem ConeData.original_letter_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (a : α) (hraw : d.raw i t = Sum.inl (Sum.inl a)) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      Sum.inl a := by
  rw [d.symbol_inside hb c x hTbound i t hi]
  exact ConeWordLift.liftWord_original
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t a hraw

/-- Auxiliary frontier letters use exactly the typed decoder;
they are not mistaken for genuine cone variables. -/
theorem ConeData.auxiliary_letter_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (a : Aux) (hraw : d.raw i t = Sum.inl (Sum.inr a)) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      d.decodeAux i a := by
  rw [d.symbol_inside hb c x hTbound i t hi]
  exact ConeWordLift.liftWord_auxiliary
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t a hraw

/-- A genuinely local cone variable is uniformly transported
to its prescribed old source variable at the entire fibre. -/
theorem ConeData.cone_variable_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (v : κ) (hraw : d.raw i t = Sum.inr v) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      Sum.inr (d.coneRoot i v) := by
  rw [d.symbol_inside hb c x hTbound i t hi]
  exact ConeWordLift.liftWord_variable
    (d.raw i) (d.decodeAux i) (d.coneRoot i) t v hraw

/-- All occurrences of one local cone variable retain the same
source-variable name, even across different ambient positions. -/
theorem ConeData.cone_variable_fibre_uniform
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (s t : BoundedNode b n)
    (hs : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 s.1)
    (ht : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (v : κ) (hraws : d.raw i s = Sum.inr v)
    (hrawt : d.raw i t = Sum.inr v) :
    (d.onActualStarredQ hb c x hTbound).word.word s =
      (d.onActualStarredQ hb c x hTbound).word.word t := by
  exact (d.cone_variable_inside hb c x hTbound i s hs v hraws).trans
    (d.cone_variable_inside hb c x hTbound i t ht v hrawt).symm

/-- Evaluated meaning of the actual full-frontier Q word:
all three constructors are separately and exhaustively handled. -/
theorem ConeData.eval_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (i : Index c) (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (σ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol σ
      ((d.onActualStarredQ hb c x hTbound).word.word t) =
      match d.raw i t with
      | Sum.inl (Sum.inl a) => a
      | Sum.inl (Sum.inr u) =>
          SpanAudit.evalSymbol σ (d.decodeAux i u)
      | Sum.inr z => σ (d.coneRoot i z) := by
  rw [d.symbol_inside hb c x hTbound i t hi]
  change SpanAudit.eval
    (ConeWordLift.liftWord (d.raw i) (d.decodeAux i)
      (d.coneRoot i)) σ t = _
  exact congrFun
    (ConeWordLift.eval_liftWord (d.raw i) (d.decodeAux i)
      (d.coneRoot i) σ) t

theorem ConeData.eval_outside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c Aux κ)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1)
    (σ : c.source.word.Vars → α) :
    SpanAudit.evalSymbol σ
      ((d.onActualStarredQ hb c x hTbound).word.word t) =
      SpanAudit.evalSymbol σ (c.source.word.word t) := by
  exact congrArg (SpanAudit.evalSymbol σ)
    (d.symbol_outside hb c x hTbound t ht)

end DualTree.ForwardQFullFrontierThreeWay
