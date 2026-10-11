import DualTree.ForwardQLocalWordPatching
import DualTree.ForwardQWordSymbolAssembly
import DualTree.ThreeWayQDecoderRootAlignment
import DualTree.ForwardQActualStarredSpace

/-!
# Assemble corrected Q words from three-way decoded local cone symbols

This is the typed algebraic bridge between:
* ConeWordLift's exhaustive original/auxiliary/cone-variable decoding;
* the geometry of disjoint selected D₂ projected cones, avoiding all
  original source variable roots;
* the repaired decoded-word assembly interface on the ACTUAL corrected
  semi-complete Q support.

A local cone datum consists of a raw symbol map, an auxiliary
symbol decoder, and a transport of genuine cone variables to original
source variables. The two local root-alignment obligations are
explicit: auxiliary letters decoding to an old source variable must
occur above its root, and genuine cone variables must likewise be
transported to a source variable root prefixing every occurrence.

Under these two checked interfaces (but WITHOUT claiming that the
paper's particular maps already satisfy them), we construct a total
global word. Inside each actual marked Q cone its symbol is the
three-way decoded local symbol, and outside all marked cones it is
the original source word. Since marked cones avoid old roots, the
word is root-valid. With an actual corrected starred D₀/D₂ input
and explicit bounding of the ambient complete support T inside
b^{<n}, the resulting decoded word is a bona fide StarredWord
on the actual corrected Q support.

This does NOT yet establish the particular Lemma 27 word g_w:
one must identify the raw local words, auxiliary decoders, root
transport, and prove both local alignment conditions from that
specific construction, then establish smooth colouring compatibility.
-/

namespace DualTree.ForwardQThreeWayConeWordAssembly

open ForwardSourceQTree

/-- Exact local data to be inserted in each selected projected D₂
cone, with separate root-alignment conditions for auxiliary decoded
variables and genuine transported cone variables. -/
structure ConeData
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (Aux κ : Type*) where
  raw : MixedProduct.BulletIndex (kind c) →
    BoundedNode b n → Sum (Sum α Aux) κ
  decodeAux : MixedProduct.BulletIndex (kind c) →
    Aux → Sum α c.source.word.Vars
  coneRoot : MixedProduct.BulletIndex (kind c) →
    κ → c.source.word.Vars
  auxiliaryAligned :
    ∀ (i : MixedProduct.BulletIndex (kind c))
      (t : BoundedNode b n) (a : Aux) (v : c.source.word.Vars),
      raw i t = Sum.inl (Sum.inr a) →
      decodeAux i a = Sum.inr v →
      IsPrefix v.1.1 t.1
  coneAligned :
    ∀ (i : MixedProduct.BulletIndex (kind c))
      (t : BoundedNode b n) (z : κ),
      raw i t = Sum.inr z →
      IsPrefix (coneRoot i z).1.1 t.1

/-- The actual local symbol at a homogeneous-tree coordinate
is the exhaustive three-way ConeWordLift decoder. -/
def ConeData.localSymbol
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α} {x : Input c}
    (d : ConeData c x Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n) :
    Sum α c.source.word.Vars :=
  ConeWordLift.liftWord (d.raw i) (d.decodeAux i) (d.coneRoot i) t

/-- The two explicit local alignment assumptions imply the
single root-prefix condition needed by the global cone patcher.
There is no hidden assumption on original alphabet constants. -/
theorem ConeData.localSymbol_aligned
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α} {x : Input c}
    (d : ConeData c x Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (v : c.source.word.Vars)
    (t : BoundedNode b n)
    (h : d.localSymbol i t = Sum.inr v) :
    IsPrefix v.1.1 t.1 := by
  exact ThreeWayQDecoderRootAlignment.indexed_liftWord_root_aligned
    (fun w : c.source.word.Vars => w.1.1)
    d.raw d.decodeAux d.coneRoot
    d.auxiliaryAligned d.coneAligned i t v h

/-- Construct a root-valid global source-variable word by patching
the actual disjoint projected Q cones with the individually
decoded and aligned local symbol functions. -/
noncomputable def ConeData.toVariableWord
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α} {x : Input c}
    (d : ConeData c x Aux κ) :
    DualTree.VariableWord b n α :=
  ForwardQLocalWordPatching.patchedVariableWord c x d.localSymbol
    (fun i v t h => d.localSymbol_aligned i v t h)

/-- Wrap the patched word into the previously checked source-facing
DecodedWord interface, retaining exactly the actual symbol map. -/
noncomputable def ConeData.toDecodedWord
    {b n l k m : Nat} {α Aux κ : Type*}
    {c : Frame b n l k m α} {x : Input c}
    (d : ConeData c x Aux κ) :
    ForwardQWordSymbolAssembly.DecodedWord c := {
  symbol := ForwardQLocalWordPatching.patchedSymbol c x d.localSymbol
  atRoot := by
    intro v
    exact ForwardQLocalWordPatching.patchedSymbol_at_source_root
      c x d.localSymbol v
  below := by
    intro v t h
    exact d.toVariableWord.below v t h
}

/-- Under the genuine corrected starred D₂ source input and
explicit T⊆b^{<n}, the three-way patched word is a legal starred
word on the ACTUAL corrected Q support, not merely an abstract
word or the enclosing T support. -/
noncomputable def ConeData.onActualStarredQ
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) :=
  d.toDecodedWord.onCorrectedQ hb c x.1
    ((ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      c x.1).1 x.2)
    hTbound

/-- The final starred word's support is the literal reconstructed
corrected Q set of retained old interior and projected markers. -/
theorem ConeData.onActualStarredQ_tree
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ) :
    (d.onActualStarredQ hb c x hTbound).tree =
      (nodes c x.1).toList := rfl

/-- Each position inside the actual marked cone i receives
precisely the three-way decoded local symbol at that position.
No overwrite can occur from another D₂ cone. -/
theorem ConeData.onActualStarredQ_symbol_inside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (ht : IsPrefix (markedProjection c x.1 i).1 t.1) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      d.localSymbol i t := by
  change ForwardQLocalWordPatching.patchedSymbol
    c x.1 d.localSymbol t = d.localSymbol i t
  exact ForwardQLocalWordPatching.patchedSymbol_inside
    c x.1 d.localSymbol i t ht

/-- Outside all marked projected cones the three-way patched
output word agrees exactly with the original source word. -/
theorem ConeData.onActualStarredQ_symbol_outside
    {b n l k m : Nat} {α Aux κ : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (d : ConeData c x.1 Aux κ)
    (t : BoundedNode b n)
    (ht : ∀ i : MixedProduct.BulletIndex (kind c),
      ¬ IsPrefix (markedProjection c x.1 i).1 t.1) :
    (d.onActualStarredQ hb c x hTbound).word.word t =
      c.source.word.word t := by
  change ForwardQLocalWordPatching.patchedSymbol
    c x.1 d.localSymbol t = c.source.word.word t
  exact ForwardQLocalWordPatching.patchedSymbol_outside
    c x.1 d.localSymbol t ht

end DualTree.ForwardQThreeWayConeWordAssembly
