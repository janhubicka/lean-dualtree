import DualTree.UpLeafMixedWord
import DualTree.Lemma14Invariant

/-!
# The exact D₁ trace on genuine height-one mixed words

The fixed-root mixed words of `UpLeafMixedWord` have real ambient leaves
in every D₁ coordinate.  Their exact Lemma-14 trace consists of the chosen
branch direction and the independently substituted root letter at each
D₁ coordinate.  The predecessor values away from the root are fixed.

This gives an exact parameter criterion for `UpCanonical`, using both
directions of the genuine mixed-span parametrization.  When every coordinate
is D₁, the trace determines the entire span element, so every coloring is
`UpCanonical` on this concrete intrinsic-height-one word.

The same all-D₁ conclusion also holds for `attach` applied to any vector of
singleton-supported words, including words with repeated variable occurrences.
Finally, an exact `Good` criterion isolates the remaining color requirement:
the induced parameter color must forget every D₁ direction and every root
letter except those at D₂ coordinates.

These are the all-D₁, height-one canonical base case and conditional interfaces.
No unconditional `Good`, color constancy across different leaves or root
letters, mixed D₀/D₁ Ramsey theorem, or higher-dimensional construction is
asserted.
-/

namespace DualTree.UpLeafCanonical

open DualTree.MixedProduct
open DualTree.UpLeafMixedWord

private theorem word_eq_of_root_letter_eq_of_singleton
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (root : BoundedNode b n)
    (hs : f.supportNodes = [root.1])
    (u v : TreeWord b n α)
    (hu : u ∈ f.span) (hv : v ∈ f.span)
    (hroot : u root = v root) : u = v := by
  change ∃ σ : f.Vars → α, f.eval σ = u at hu
  change ∃ τ : f.Vars → α, f.eval τ = v at hv
  rcases hu with ⟨σ, rfl⟩
  rcases hv with ⟨τ, rfl⟩
  let r : f.Vars := ⟨root, root_mem_support_of_singleton f root hs⟩
  have hfr : f.word root = Sum.inr r := f.atRoot r
  have hστ : σ r = τ r := by
    simpa only [DualTree.VariableWord.eval, SpanAudit.eval,
      SpanAudit.evalSymbol, hfr] using hroot
  have hvars : ∀ s : f.Vars, s = r := by
    intro s
    have hmem : s.1.1 ∈ f.supportNodes :=
      List.mem_map.mpr ⟨s.1, s.2, rfl⟩
    rw [hs] at hmem
    have heq : s.1.1 = root.1 := by simpa using hmem
    apply Subtype.ext
    exact Subtype.ext heq
  have hassign : σ = τ := by
    funext s
    rw [hvars s]
    exact hστ
  rw [hassign]

/-- The all-D₁ trace distinguishes points even when the singleton variable
has repeated occurrences.  Its value at the root determines the entire word;
the selected genuine ambient leaf always has that root as a predecessor. -/
theorem sameUpTrace_iff_eq_of_allUp_attach_mem_span
    {b n d : Nat} {α : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hallUp : ∀ i : Fin d, kind i = CoordKind.up)
    (vector : VectorVariableWord b n d 1 α (SkewTree.forwardAuxB (b := b)))
    (roots : Fin d → BoundedNode b n)
    (hroots : ∀ i,
      (vector.components i).toVariableWord.supportNodes = [(roots i).1])
    (x y : Element b n d α kind)
    (hx : x ∈ (attach hb kind vector roots hroots).span)
    (hy : y ∈ (attach hb kind vector roots hroots).span) :
    SameUpTrace x y ↔ x = y := by
  constructor
  · intro htrace
    have hwords : x.words = y.words := by
      funext i
      let iu : UpIndex kind := ⟨i, hallUp i⟩
      obtain ⟨j, hj⟩ :=
        (UpLeafGeometry.mem_ambientLeaves_iff hb (roots i) _).1 (hx.2.1 iu)
      have hpre : IsPrefix (roots i).1 (x.upPoint iu).1 := by
        rw [← hj]
        exact UpLeafGeometry.prefix_ambientLeaf hb (roots i) j
      exact word_eq_of_root_letter_eq_of_singleton
        (vector.components i).toVariableWord (roots i) (hroots i)
        (x.words i) (y.words i) (hx.1 i) (hy.1 i)
        (htrace.2 iu (roots i) hpre)
    have hup : x.upPoint = y.upPoint := funext htrace.1
    have hbullet : x.bulletPoint = y.bulletPoint := by
      funext i
      have hi := i.2
      rw [hallUp i.1] at hi
      cases hi
    cases x
    cases y
    simp only [Element.mk.injEq]
    exact ⟨hwords, hup, hbullet⟩
  · rintro rfl
    exact sameUpTrace_refl x

/-- Attaching actual ambient leaves to any all-D₁ vector with singleton
supports gives a Lemma-14 canonical word for every coloring.  The variable
may occur at arbitrarily many ambient positions; it is not required to occur
only at its root. -/
theorem upCanonical_attach_allUp
    {b n d : Nat} {α γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hallUp : ∀ i : Fin d, kind i = CoordKind.up)
    (vector : VectorVariableWord b n d 1 α (SkewTree.forwardAuxB (b := b)))
    (roots : Fin d → BoundedNode b n)
    (hroots : ∀ i,
      (vector.components i).toVariableWord.supportNodes = [(roots i).1])
    (color : Element b n d α kind → γ) :
    UpCanonical color (attach hb kind vector roots hroots) := by
  intro x y hx hy htrace
  exact congrArg color
    ((sameUpTrace_iff_eq_of_allUp_attach_mem_span hb kind hallUp vector
      roots hroots x y hx hy).1 htrace)

/-- The source-facing predecessor trace of two parameter elements agrees
exactly when their D₁ directions and D₁ root letters agree.  No parameter
at a D₀ or D₂ coordinate is included in the Lemma-14 trace. -/
theorem parameterElement_sameUpTrace_iff
    {b n d : Nat} {α : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (fallback : α)
    (a a' : Fin d → α)
    (directions directions' : UpIndex kind → Fin b) :
    SameUpTrace
        (parameterElement hb kind roots fallback a directions)
        (parameterElement hb kind roots fallback a' directions') ↔
      directions = directions' ∧
        ∀ i : UpIndex kind, a i.1 = a' i.1 := by
  constructor
  · intro htrace
    constructor
    · funext i
      exact UpLeafGeometry.ambientLeaf_injective hb (roots i.1) (htrace.1 i)
    · intro i
      have hroot := htrace.2 i (roots i.1)
        (UpLeafGeometry.prefix_ambientLeaf hb (roots i.1) (directions i))
      simpa only [parameterElement, FixedRootMarkerWord.valueWord_at_root]
        using hroot
  · rintro ⟨hdir, hletter⟩
    constructor
    · intro i
      change UpLeafGeometry.ambientLeaf hb (roots i.1) (directions i) =
        UpLeafGeometry.ambientLeaf hb (roots i.1) (directions' i)
      rw [hdir]
    · intro i t _
      change FixedRootMarkerWord.valueWord (roots i.1) fallback (a i.1) t =
        FixedRootMarkerWord.valueWord (roots i.1) fallback (a' i.1) t
      rw [hletter i]

/-- Exact canonicalization interface for the genuine mixed span.  Fix the
chosen D₁ directions and root letters; `UpCanonical` is equivalent to color
constancy as all remaining root letters vary.  The forward implication
uses actual membership of every parameter element, so this characterization
does not obtain canonicalization from an empty span. -/
theorem upCanonical_iff_parameter_constancy
    {b n d : Nat} {α γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α)
    (color : Element b n d α kind → γ) :
    UpCanonical color (mixedWord hb kind roots hlen fallback) ↔
      ∀ (directions : UpIndex kind → Fin b) (a a' : Fin d → α),
        (∀ i : UpIndex kind, a i.1 = a' i.1) →
          color (parameterElement hb kind roots fallback a directions) =
            color (parameterElement hb kind roots fallback a' directions) := by
  constructor
  · intro hcanon directions a a' hletter
    apply hcanon
      (parameterElement_mem_span hb kind roots hlen fallback a directions)
      (parameterElement_mem_span hb kind roots hlen fallback a' directions)
    exact (parameterElement_sameUpTrace_iff hb kind roots fallback
      a a' directions directions).2 ⟨rfl, hletter⟩
  · intro hconst x y hx hy htrace
    rcases span_element_eq_parameterElement hb kind roots hlen fallback x hx with
      ⟨a, directions, rfl⟩
    rcases span_element_eq_parameterElement hb kind roots hlen fallback y hy with
      ⟨a', directions', rfl⟩
    obtain ⟨hdir, hletter⟩ :=
      (parameterElement_sameUpTrace_iff hb kind roots fallback
        a a' directions directions').1 htrace
    subst directions'
    exact hconst directions a a' hletter

/-- For an all-D₁ kind, the genuine height-one trace distinguishes every
element of the mixed span: every coordinate's root lies below its selected
ambient leaf and is therefore visible in the trace. -/
theorem sameUpTrace_iff_eq_of_allUp_mem_span
    {b n d : Nat} {α : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hallUp : ∀ i : Fin d, kind i = CoordKind.up)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α)
    (x y : Element b n d α kind)
    (hx : x ∈ (mixedWord hb kind roots hlen fallback).span)
    (hy : y ∈ (mixedWord hb kind roots hlen fallback).span) :
    SameUpTrace x y ↔ x = y := by
  exact sameUpTrace_iff_eq_of_allUp_attach_mem_span hb kind hallUp
    (vectorWord roots hlen fallback) roots (fun _ => rfl) x y hx hy

/-- Unconditional all-D₁, intrinsic-height-one Lemma-14 canonicalization:
the concrete mixed word is `UpCanonical` for every coloring, with no
assumed color constancy.  This conclusion allows different colors for
different selected leaves or root letters. -/
theorem upCanonical_allUp
    {b n d : Nat} {α γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hallUp : ∀ i : Fin d, kind i = CoordKind.up)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α)
    (color : Element b n d α kind → γ) :
    UpCanonical color (mixedWord hb kind roots hlen fallback) := by
  intro x y hx hy htrace
  exact congrArg color
    ((sameUpTrace_iff_eq_of_allUp_mem_span hb kind hallUp roots hlen fallback
      x y hx hy).1 htrace)

/-- Exact Definition-11 interface: the fixed-root mixed word is `Good`
precisely when its parameter coloring depends only on the D₂ root letters.
Both the letters and the chosen directions at every genuine D₁ coordinate
must be erased.  This is an equivalence of color conditions, not a proof
that an arbitrary coloring already satisfies them. -/
theorem good_iff_parameter_bullet_constancy
    {b n d : Nat} {α γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (roots : Fin d → BoundedNode b n)
    (hlen : ∀ i j : Fin d, i < j → (roots i).1.length ≤ (roots j).1.length)
    (fallback : α)
    (color : Element b n d α kind → γ) :
    Good color (mixedWord hb kind roots hlen fallback) ↔
      ∀ (a a' : Fin d → α)
        (directions directions' : UpIndex kind → Fin b),
        (∀ i : BulletIndex kind, a i.1 = a' i.1) →
          color (parameterElement hb kind roots fallback a directions) =
            color (parameterElement hb kind roots fallback a' directions') := by
  constructor
  · intro hgood a a' directions directions' hletter
    apply hgood
      (parameterElement_mem_span hb kind roots hlen fallback a directions)
      (parameterElement_mem_span hb kind roots hlen fallback a' directions')
    · intro i
      rfl
    · intro i
      simpa only [parameterElement, FixedRootMarkerWord.valueWord_at_root]
        using hletter i
  · intro hconst x y hx hy _ hletter
    rcases span_element_eq_parameterElement hb kind roots hlen fallback x hx with
      ⟨a, directions, rfl⟩
    rcases span_element_eq_parameterElement hb kind roots hlen fallback y hy with
      ⟨a', directions', rfl⟩
    apply hconst a a' directions directions'
    intro i
    simpa only [parameterElement, FixedRootMarkerWord.valueWord_at_root]
      using hletter i

end DualTree.UpLeafCanonical
