import DualTree.UpLeafGeometry
import DualTree.FixedRootMarkerWord
import DualTree.VectorOrderedSingletons

/-!
# Genuine height-one mixed words with up coordinates

For positive branching, every bounded singleton support can be extended by
one actual ambient-level leaf in each direction. This module attaches these
leaves to an existing vector of singleton-supported words, without excluding
any coordinate kind. It also gives an explicit family with independently
chosen letters at the roots and independently chosen D₁ directions.

The entire mixed span is exactly this parameter family and is nonempty when
an alphabet letter is supplied. These are geometric and algebraic existence
results; no monochromaticity or general mixed Ramsey theorem is assumed.
-/

namespace DualTree.UpLeafMixedWord

open DualTree.MixedProduct
open DualTree.UpLeafGeometry

/-- Recover the actual bounded support root from its underlying-node list. -/
theorem root_mem_support_of_singleton
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α) (r : BoundedNode b n)
    (hs : f.supportNodes = [r.1]) : r ∈ f.support := by
  have hm : r.1 ∈ f.supportNodes := by rw [hs]; simp
  obtain ⟨s, hs, heq⟩ := List.mem_map.mp hm
  have hsr : s = r := Subtype.ext heq
  exact hsr ▸ hs

/-- Attach genuine D₁ leaves to ANY existing vector with singleton supports.
In particular, the variable words may have many occurrences of their sole
variable. The whole vector-completeness certificate is preserved. -/
noncomputable def attach
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (vector : VectorVariableWord b n d 1 α (SkewTree.forwardAuxB (b := b)))
    (roots : Fin d → BoundedNode b n)
    (hroots : ∀ i,
      (vector.components i).toVariableWord.supportNodes = [(roots i).1]) :
    MixedProduct.VariableWord b n d 1 α SkewTree.forwardAuxB kind where
  vector := vector
  upLeaves := fun i => ambientLeaves hb (roots i.1)
  upLeaves_nodup := fun i => ambientLeaves_nodup hb (roots i.1)
  upLeaves_card := fun i => by
    simpa using ambientLeaves_length hb (roots i.1)
  up_support_skew := by
    intro i
    unfold extendedSupport
    rw [hroots i.1]
    exact extended_support_skew_forward hb (roots i.1)

/-- A concrete alphabet letter supplies an actual point of the attached
mixed span, including every genuine up and bullet coordinate. -/
theorem attach_span_nonempty
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (vector : VectorVariableWord b n d 1 α (SkewTree.forwardAuxB (b := b)))
    (roots : Fin d → BoundedNode b n)
    (hroots : ∀ i,
      (vector.components i).toVariableWord.supportNodes = [(roots i).1])
    (a : α) :
    ((attach hb kind vector roots hroots).span).Nonempty := by
  let x : Element b n d α kind :=
    { words := fun i => (vector.components i).toVariableWord.eval (fun _ => a)
      upPoint := fun i => ambientLeaf hb (roots i.1) ⟨0, hb⟩
      bulletPoint := fun i => roots i.1 }
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    exact ⟨fun _ => a, rfl⟩
  · intro i
    exact (mem_ambientLeaves_iff hb (roots i.1) _).2 ⟨⟨0, hb⟩, rfl⟩
  · intro i
    exact root_mem_support_of_singleton
      (vector.components i.1).toVariableWord (roots i.1) (hroots i.1)

/-- Independently variable root letters at any weakly length-ordered roots. -/
noncomputable def vectorWord
    {b n d : Nat} {α : Type*}
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) :
    VectorVariableWord b n d 1 α (SkewTree.forwardAuxB (b := b)) where
  components := fun i => FixedRootMarkerWord.kWord (roots i) fallback
  vector_complete := by
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun i => [(roots i).1]) = true
    exact VectorSkew.monotone_singletons_vectorComplete_one
      _ (fun i => (roots i).1) hlen

/-- A genuine mixed variable word for ANY D₀/D₁/D₂ pattern. -/
noncomputable def mixedWord
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) :
    MixedProduct.VariableWord b n d 1 α SkewTree.forwardAuxB kind :=
  attach hb kind (vectorWord roots hlen fallback) roots (fun _ => rfl)

/-- All coordinate letters and actual up-leaf directions vary independently;
the D₂ point in each bullet coordinate is its genuine support root. -/
noncomputable def parameterElement
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n) (fallback : α)
    (a : Fin d → α) (directions : UpIndex kind → Fin b) :
    Element b n d α kind where
  words := fun i => FixedRootMarkerWord.valueWord (roots i) fallback (a i)
  upPoint := fun i => ambientLeaf hb (roots i.1) (directions i)
  bulletPoint := fun i => roots i.1

theorem parameterElement_root_letter
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n) (fallback : α)
    (a : Fin d → α) (directions : UpIndex kind → Fin b) (i : Fin d) :
    (parameterElement hb kind roots fallback a directions).words i (roots i) = a i :=
  FixedRootMarkerWord.valueWord_at_root (roots i) fallback (a i)

/-- The parameterization loses neither a coordinate letter nor an up-leaf
direction. Combined with the span equality below, this is a bijective
description of the genuine mixed span. -/
theorem parameterElement_injective
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n) (fallback : α) :
    Function.Injective
      (fun z : (Fin d → α) × (UpIndex kind → Fin b) =>
        parameterElement hb kind roots fallback z.1 z.2) := by
  intro z z' h
  apply Prod.ext
  · funext i
    have hi := congrArg (fun x : Element b n d α kind => x.words i (roots i)) h
    simpa only [parameterElement_root_letter] using hi
  · funext i
    apply ambientLeaf_injective hb (roots i.1)
    exact congrArg (fun x : Element b n d α kind => x.upPoint i) h

/-- Every parameter tuple occurs in the actual mixed span. -/
theorem parameterElement_mem_span
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) (a : Fin d → α) (directions : UpIndex kind → Fin b) :
    parameterElement hb kind roots fallback a directions ∈
      (mixedWord hb kind roots hlen fallback).span := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact FixedRootMarkerWord.valueWord_mem_span (roots i) fallback (a i)
  · intro i
    exact (mem_ambientLeaves_iff hb (roots i.1) _).2 ⟨directions i, rfl⟩
  · intro i
    change roots i.1 ∈ [roots i.1]
    simp

/-- Conversely every actual mixed-span point has independent root-letter
and branch-direction parameters. No coordinate is discarded. -/
theorem span_element_eq_parameterElement
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) (x : Element b n d α kind)
    (hx : x ∈ (mixedWord hb kind roots hlen fallback).span) :
    ∃ (a : Fin d → α) (directions : UpIndex kind → Fin b),
      x = parameterElement hb kind roots fallback a directions := by
  classical
  have hw : ∀ i : Fin d, ∃ a : α,
      FixedRootMarkerWord.valueWord (roots i) fallback a = x.words i := by
    intro i
    exact (FixedRootMarkerWord.span_eq_range (roots i) fallback ▸ hx.1 i)
  choose a ha using hw
  have hu : ∀ i : UpIndex kind, ∃ j : Fin b,
      ambientLeaf hb (roots i.1) j = x.upPoint i := by
    intro i
    exact (mem_ambientLeaves_iff hb (roots i.1) _).1 (hx.2.1 i)
  choose directions hd using hu
  have hbullet : x.bulletPoint = fun i => roots i.1 := by
    funext i
    have hi := hx.2.2 i
    change x.bulletPoint i ∈ [roots i.1] at hi
    simpa using hi
  refine ⟨a, directions, ?_⟩
  have hwords : x.words = fun i =>
      FixedRootMarkerWord.valueWord (roots i) fallback (a i) := by
    funext i
    exact (ha i).symm
  have hup : x.upPoint = fun i => ambientLeaf hb (roots i.1) (directions i) := by
    funext i
    exact (hd i).symm
  cases x
  simp only [parameterElement, Element.mk.injEq] at *
  exact ⟨hwords, hup, hbullet⟩

/-- Exact equality with the full independent parameter range. -/
theorem mixedWord_span_eq_parameter_range
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) :
    (mixedWord hb kind roots hlen fallback).span =
      Set.range (fun z : (Fin d → α) × (UpIndex kind → Fin b) =>
        parameterElement hb kind roots fallback z.1 z.2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, directions, heq⟩ :=
      span_element_eq_parameterElement hb kind roots hlen fallback x hx
    exact ⟨⟨a, directions⟩, heq.symm⟩
  · rintro ⟨⟨a, directions⟩, rfl⟩
    exact parameterElement_mem_span hb kind roots hlen fallback a directions

/-- Nonvacuity for every kind pattern, with positive branching and a
supplied alphabet letter. The strict ambient-height bound is carried by roots. -/
theorem mixedWord_span_nonempty
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α) :
    ((mixedWord hb kind roots hlen fallback).span).Nonempty := by
  exact ⟨parameterElement hb kind roots fallback (fun _ => fallback) (fun _ => ⟨0, hb⟩),
    parameterElement_mem_span hb kind roots hlen fallback
      (fun _ => fallback) (fun _ => ⟨0, hb⟩)⟩

/-- Explicit existence bound: ambient height one already suffices for a
nonempty intrinsic-height-one mixed word of any width and kind pattern.
For every larger height the empty root is still a legal common support.
This is existence of the mixed space, not a Ramsey bound. -/
theorem exists_mixedWord_nonempty
    {b n d : Nat} {α : Type*}
    (hb : 0 < b) (hn : 0 < n) (kind : Fin d → CoordKind) (a : α) :
    ∃ f : MixedProduct.VariableWord b n d 1 α SkewTree.forwardAuxB kind,
      f.span.Nonempty := by
  let roots : Fin d → BoundedNode b n := fun _ => ⟨[], by simpa [InHomTree] using hn⟩
  have hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length :=
    fun _ _ _ => Nat.le_refl _
  exact ⟨mixedWord hb kind roots hlen a,
    mixedWord_span_nonempty hb kind roots hlen a⟩

end DualTree.UpLeafMixedWord
