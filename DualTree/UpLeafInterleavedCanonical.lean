import DualTree.UpLeafInterleavedSpan
import DualTree.Lemma14Invariant

/-!
# Height-one Lemma 14 canonicalization with genuine interleaved D₁ coordinates

The actual mixed span is identified with independent D₀ Hales--Jewett
substitutions, letters at D₁/D₂ singleton roots, and D₁ ambient directions.
Its exact predecessor trace remembers the D₁ direction and root letter,
but not the independent ordinary D₀ coordinates.

For D₂ = empty, finite parameter-uniform Hales--Jewett erases all D₀
substitutions uniformly over every D₁ trace. This constructs an honest
nonempty intrinsic-height-one mixed word with UpCanonical for every
finite colouring; neither an existing canonical word nor a Good
assumption is supplied.

This does NOT prove Definition-11 Good when D₁ is present: Good must
erase the directions and letters at D₁, which SameUpTrace retains.
-/

namespace DualTree.UpLeafInterleavedCanonical

open DualTree.MixedProduct
open DualTree.InterleavedFlatHalesJewett
open DualTree.UpLeafInterleavedParameters
open DualTree.UpLeafInterleavedSpan
open DualTree.ShiftedRaySlots

/-- Every D₁ index is a genuine nonplain index. -/
def upAsNonplain
    {d : Nat} (kind : Fin d → CoordKind)
    (i : UpIndex kind) : NonplainIndex kind :=
  ⟨i.1, by
    intro h
    have hu : kind i.1 = CoordKind.up := i.2
    rw [h] at hu
    cases hu⟩

/-- If no D₂ coordinate is present, every nonplain coordinate is D₁. -/
theorem nonplain_is_up_of_noBullet
    {d : Nat} (kind : Fin d → CoordKind)
    (hnb : NoBullet kind)
    (i : NonplainIndex kind) :
    kind i.1 = CoordKind.up := by
  cases hk : kind i.1 with
  | plain => exact (i.2 hk).elim
  | up => rfl
  | bullet => exact (hnb i.1 hk).elim

/-- For actual interleaved parameter elements, equality of the entire
source-facing Lemma-14 predecessor trace is equivalent to equality of
every D₁ ambient branch and of the D₁ root letters. There is no claim
about D₂ letters or any D₀ substitution. -/
theorem parameterElement_sameUpTrace_iff
    {b N d : Nat} {β : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (fallback : β)
    (u u' : PlainIndex kind → Fin N → β)
    (a a' : NonplainIndex kind → β)
    (directions directions' : UpIndex kind → Fin b) :
    SameUpTrace
        (parameterElement hb kind fallback u a directions)
        (parameterElement hb kind fallback u' a' directions') ↔
      directions = directions' ∧
        ∀ i : UpIndex kind,
          a (upAsNonplain kind i) = a' (upAsNonplain kind i) := by
  constructor
  · intro htrace
    constructor
    · funext i
      exact UpLeafGeometry.ambientLeaf_injective hb
        (InterleavedMixedWord.markerPos (N := N) hb i.1) (htrace.1 i)
    · intro i
      have hp : IsPrefix
          (InterleavedMixedWord.markerPos (N := N) hb i.1).1
          ((parameterElement hb kind fallback u a directions).upPoint i).1 :=
        UpLeafGeometry.prefix_ambientLeaf hb
          (InterleavedMixedWord.markerPos (N := N) hb i.1) (directions i)
      have hr := htrace.2 i
        (InterleavedMixedWord.markerPos (N := N) hb i.1) hp
      have hleft := parameterElement_nonplain_root_letter hb kind fallback
        u a directions (upAsNonplain kind i)
      have hright := parameterElement_nonplain_root_letter hb kind fallback
        u' a' directions' (upAsNonplain kind i)
      exact hleft.symm.trans (hr.trans hright)
  · rintro ⟨hdir, hletters⟩
    constructor
    · intro i
      change UpLeafGeometry.ambientLeaf hb
          (InterleavedMixedWord.markerPos (N := N) hb i.1) (directions i) =
        UpLeafGeometry.ambientLeaf hb
          (InterleavedMixedWord.markerPos (N := N) hb i.1) (directions' i)
      rw [hdir]
    · intro i t _
      have hi : kind i.1 ≠ CoordKind.plain := (upAsNonplain kind i).2
      have heq := congrArg
        (fun z : β =>
          FixedRootMarkerWord.valueWord
            (InterleavedMixedWord.markerPos (N := N) hb i.1) fallback z t)
        (hletters i)
      simpa [parameterElement, hi, upAsNonplain] using heq

/-- The genuine mixed span is Lemma-14 canonical if all ordinary
Hales--Jewett substitutions have identical colours at fixed nonplain
root letters and fixed D₁ directions. For D₂=empty the trace forces
exactly these parameter equalities. This is a conditional transfer
lemma, with the condition discharged by finite Ramsey below. -/
theorem upCanonical_of_uniform_plain
    {b N d : Nat} {β γ : Type*}
    (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnb : NoBullet kind)
    (w : Fin N → Sum (PlainIndex kind → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (color : Element b (ambient d N) d β kind → γ)
    (huniform :
      ∀ (σ τ : PlainIndex kind → Fin 1 → β)
        (a : NonplainIndex kind → β)
        (directions : UpIndex kind → Fin b),
        color (parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (σ i)) a directions) =
        color (parameterElement hb kind fallback
          (fun i => SpanAudit.eval (project w i) (τ i)) a directions)) :
    UpCanonical color
      (UpLeafInterleavedGeometry.mixedWord hb kind w fallback
        r hroot hfirst) := by
  intro x y hx hy htrace
  obtain ⟨σ, a, directions, hxrepr⟩ :=
    span_element_eq_parameterElement hb kind w fallback r hroot hfirst x hx
  obtain ⟨τ, a', directions', hyrepr⟩ :=
    span_element_eq_parameterElement hb kind w fallback r hroot hfirst y hy
  have htrace' : SameUpTrace
      (parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a directions)
      (parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (τ i)) a' directions') := by
    rw [hxrepr, hyrepr] at htrace
    exact htrace
  obtain ⟨hdir, hletters⟩ :=
    (parameterElement_sameUpTrace_iff hb kind fallback
      (fun i => SpanAudit.eval (project w i) (σ i))
      (fun i => SpanAudit.eval (project w i) (τ i))
      a a' directions directions').1 htrace'
  have ha : a = a' := by
    funext i
    let iu : UpIndex kind :=
      ⟨i.1, nonplain_is_up_of_noBullet kind hnb i⟩
    have hi : upAsNonplain kind iu = i := Subtype.ext rfl
    exact hi ▸ (hletters iu)
  subst a'
  subst directions'
  calc
    color x = color (parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (σ i)) a directions) :=
      congrArg color hxrepr
    _ = color (parameterElement hb kind fallback
        (fun i => SpanAudit.eval (project w i) (τ i)) a directions) :=
      huniform σ τ a directions
    _ = color y := (congrArg color hyrepr).symm

/-- Proper finite product Hales--Jewett, uniform for every fixed
nonplain-letter tuple and every fixed D₁ ambient direction tuple. -/
theorem exists_uniform_plain_given_nonplain
    {b d : Nat} (kind : Fin d → CoordKind)
    (β γ : Type*) [Finite β] [Finite γ] :
    ∃ N : Nat,
      ∀ C : (PlainIndex kind → Fin N → β) →
          (NonplainIndex kind → β) →
          (UpIndex kind → Fin b) → γ,
        ∃ w : Fin N → Sum (PlainIndex kind → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin N, w j = Sum.inr v) ∧
          ∀ (σ τ : PlainIndex kind → Fin 1 → β)
            (a : NonplainIndex kind → β)
            (directions : UpIndex kind → Fin b),
            C (fun i j => SpanAudit.eval (project w i) (σ i) j) a directions =
            C (fun i j => SpanAudit.eval (project w i) (τ i) j) a directions := by
  classical
  obtain ⟨N, hN⟩ :=
    ParameterHalesJewett.exists_uniform_flat_fibre_constancy
      (PlainIndex kind → β)
      ((NonplainIndex kind → β) × (UpIndex kind → Fin b)) γ 1
  refine ⟨N, ?_⟩
  intro C
  let D : (Fin N → PlainIndex kind → β) →
      ((NonplainIndex kind → β) × (UpIndex kind → Fin b)) → γ :=
    fun U p => C (fun i j => U j i) p.1 p.2
  obtain ⟨w, hw, hconst⟩ := hN D
  refine ⟨w, hw, ?_⟩
  intro σ τ a directions
  have hmono := hconst
    (fun v i => σ i v) (fun v i => τ i v) (a, directions)
  change
    C (fun i j =>
      (SpanAudit.eval w (fun v k => σ k v) j) i) a directions =
    C (fun i j =>
      (SpanAudit.eval w (fun v k => τ k v) j) i) a directions at hmono
  calc
    C (fun i j => SpanAudit.eval (project w i) (σ i) j) a directions =
        C (fun i j =>
          (SpanAudit.eval w (fun v k => σ k v) j) i) a directions := by
          congr 1
          funext i j
          exact project_eval w σ i j
    _ = C (fun i j =>
          (SpanAudit.eval w (fun v k => τ k v) j) i) a directions := hmono
    _ = C (fun i j => SpanAudit.eval (project w i) (τ i) j) a directions := by
          congr 1
          funext i j
          exact (project_eval w τ i j).symm

/-- A positive, nonvacuous intrinsic-height-one instance of the
source-facing Lemma 14 for arbitrary interleavings of D₀/D₁, with
D₂ = empty. Ambient height is chosen before the colouring.
The selected word has the actual D₁ leaf lists and D₀ HJ components;
UpCanonical is a proved conclusion, not an input. -/
theorem exists_upCanonical_interleaved_height_one
    {b d : Nat} (hb : 0 < b)
    (kind : Fin d → CoordKind)
    (hnb : NoBullet kind)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) :
    ∃ n : Nat,
      ∀ color : Element b n d β kind → γ,
        ∃ f : MixedProduct.VariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)) kind,
          f.span.Nonempty ∧ UpCanonical color f := by
  classical
  obtain ⟨N, hN⟩ :=
    exists_uniform_plain_given_nonplain (b := b) kind β γ
  refine ⟨ambient d N, ?_⟩
  intro color
  let C : (PlainIndex kind → Fin N → β) →
      (NonplainIndex kind → β) →
      (UpIndex kind → Fin b) → γ :=
    fun u a directions => color (parameterElement hb kind fallback u a directions)
  obtain ⟨w, hproper, hconst⟩ := hN C
  obtain ⟨r, hroot, hfirst⟩ :=
    RayHalesJewett.exists_first_variable_index w hproper
  refine ⟨UpLeafInterleavedGeometry.mixedWord hb kind w fallback
    r hroot hfirst, ?_, ?_⟩
  · exact UpLeafInterleavedGeometry.mixedWord_span_nonempty
      hb kind w fallback r hroot hfirst
  · apply upCanonical_of_uniform_plain
      hb kind hnb w fallback r hroot hfirst color
    intro σ τ a directions
    exact hconst σ τ a directions

end DualTree.UpLeafInterleavedCanonical
