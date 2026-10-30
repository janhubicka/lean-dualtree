import DualTree.RayHalesJewett
import DualTree.VectorSingletonComplete
import DualTree.FlatVectorHalesJewett
import DualTree.MixedProduct

/-!
# A TRUE vector 1-complete skew tree Ramsey theorem

This module combines three verified inputs:
* finite multidimensional Hales–Jewett on the product alphabet
  (Fin d → β), with independent substitutions at every component;
* a genuinely root-aligned 1-complete tree variable word obtained
  by placing the flat word on a ray and rooting its variable at
  the first occurrence;
* full vector 1-completeness of identical singleton supports.

The result is an ACTUAL, not conditional, finite Ramsey existence
theorem for a vector of tree words with intrinsic complete-skew
height ONE. Every component is an honest KVariableWord b n 1,
the vector supports satisfy VectorSkew.vectorCompleteB, and
the whole rectangular evaluated vector span is monochromatic.

This is the D₀-only geometric base case; no D₁/D₂ marked data,
higher intrinsic height, or smooth mixed c-good theorem is claimed.
-/

namespace DualTree.VectorRayHalesJewett

open RayHalesJewett
open FlatVectorHalesJewett

/-- Projected coordinate i inherits the genuine common variable
at its actual FIRST occurrence. -/
theorem coordinate_root_variable
    {d N : Nat} {β : Type*}
    (w : Fin N → Sum (Fin d → β) (Fin 1))
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (i : Fin d) :
    coordinateWord w i r = Sum.inr 0 := by
  simp [coordinateWord, hroot]

/-- All variable occurrences in every coordinate lie at or
after the SAME first position r of the original product word. -/
theorem coordinate_variable_after_root
    {d N : Nat} {β : Type*}
    (w : Fin N → Sum (Fin d → β) (Fin 1))
    (r : Fin N)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d)
    (j : Fin N) (v : Fin 1)
    (h : coordinateWord w i j = Sum.inr v) :
    r ≤ j := by
  cases hw : w j with
  | inl a =>
      simp [coordinateWord, hw] at h
  | inr u =>
      exact hfirst j u hw

/-- Every coordinate of the product-alphabet Hales–Jewett
word lifts to a genuine rooted one-variable KVariableWord,
sharing the SAME selected ray support root. -/
noncomputable def coordinateRayWord
    {b d N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin d → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d) :
    KVariableWord b (N + 1) 1 β
      (SkewTree.forwardAuxB (b := b)) :=
  rayKVariableWord hb (coordinateWord w i) fallback r
    (coordinate_root_variable w r hroot i)
    (fun j v hv => coordinate_variable_after_root w r hfirst i j v hv)

/-- The synchronized family of genuine one-root tree words
satisfies the COMPLETE vector 1-skew predicate, including
all cross-coordinate clauses. It is NOT merely a tuple
of unrelated proper flat words. -/
noncomputable def synchronizedRayVectorWord
    {b d N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin d → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    MixedProduct.VectorVariableWord b (N + 1) d 1 β
      (SkewTree.forwardAuxB (b := b)) where
  components := coordinateRayWord hb w fallback r hroot hfirst
  vector_complete := by
    change VectorSkew.vectorCompleteB
      SkewTree.forwardAuxB 1
        (fun _ : Fin d => [zeroRay hb r.val]) = true
    exact VectorSkew.identical_singletons_vectorComplete_one _ _

/-- Evaluation in one TRUE vector component is exactly the
corresponding flat product-alphabet evaluation embedded on
the selected ray. All component variables remain independent. -/
theorem coordinateRayWord_eval
    {b d N : Nat} {β : Type*}
    (hb : 0 < b)
    (w : Fin N → Sum (Fin d → β) (Fin 1))
    (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (i : Fin d)
    (τ : (coordinateRayWord hb w fallback r hroot hfirst i).Vars → β) :
    (coordinateRayWord hb w fallback r hroot hfirst i).toVariableWord.eval τ =
      embedRay hb fallback
        (SpanAudit.eval (coordinateWord w i)
          (fun _ => τ (rootVar hb r))) := by
  exact rayVariableWord_eval hb (coordinateWord w i) fallback r
    (coordinate_root_variable w r hroot i)
    (fun j v hv => coordinate_variable_after_root w r hfirst i j v hv) τ

/-- POSITIVE geometric finite vector Ramsey existence at
intrinsic complete-skew height one.

For every nonempty branching factor b, finite β, finite γ,
and number d of vector coordinates, one FINITE tree height
n works for EVERY γ-colouring of the full vector tree-word
space. A genuine vector 1-complete-skew family of
KVariableWords is found, monochromatic on its ENTIRE
rectangular evaluated vector span (all component variables
chosen independently).

This does not prove the mixed D₂ c-good Ramsey theorem or
the full dual-tree theorem; higher complete-skew height
and marked-coordinate constraints are separate. -/
theorem exists_monochromatic_vector_one_root_tree_word
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β)
    (d : Nat) :
    ∃ n : Nat,
      ∀ C : (Fin d → TreeWord b n β) → γ,
        ∃ f : MixedProduct.VectorVariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)),
          ∃ col : γ,
            ∀ x : Fin d → TreeWord b n β,
              x ∈ f.span → C x = col := by
  obtain ⟨N, hN⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word
      (Fin d → β) γ 1
  refine ⟨N + 1, ?_⟩
  intro C
  let D : (Fin N → (Fin d → β)) → γ :=
    fun U => C (fun i =>
      embedRay hb fallback (fun j => U j i))
  obtain ⟨w,hproper,col,hmono⟩ := hN D
  obtain ⟨r,hroot,hfirst⟩ :=
    exists_first_variable_index w hproper
  let f := synchronizedRayVectorWord
    hb w fallback r hroot hfirst
  refine ⟨f, col, ?_⟩
  intro x hx
  classical
  have hxcomp :
      ∀ i : Fin d, x i ∈ (f.components i).span := hx
  choose τ hτ using hxcomp
  let σ : Fin d → Fin 1 → β :=
    fun i _ => τ i (rootVar hb r)
  have hcoord (i : Fin d) :
      x i = embedRay hb fallback
        (SpanAudit.eval (coordinateWord w i) (σ i)) := by
    calc
      x i = (f.components i).toVariableWord.eval (τ i) :=
        (hτ i).symm
      _ = embedRay hb fallback
          (SpanAudit.eval (coordinateWord w i)
            (fun _ => τ i (rootVar hb r))) :=
        coordinateRayWord_eval hb w fallback r hroot hfirst i (τ i)
      _ = embedRay hb fallback
          (SpanAudit.eval (coordinateWord w i) (σ i)) := rfl
  have houtput :
      x = fun i => embedRay hb fallback
        (fun j => (SpanAudit.eval w
          (fun v i => σ i v) j) i) := by
    funext i
    calc
      x i = embedRay hb fallback
          (SpanAudit.eval (coordinateWord w i) (σ i)) := hcoord i
      _ = embedRay hb fallback
          (fun j => (SpanAudit.eval w
            (fun v i => σ i v) j) i) := by
        funext t
        simp only [embedRay]
        split
        · rfl
        · exact coordinate_eval w σ i _
  have hc := hmono (fun v i => σ i v)
  change C (fun i => embedRay hb fallback
      (fun j => (SpanAudit.eval w
        (fun v i => σ i v) j) i)) = col at hc
  calc
    C x = C (fun i => embedRay hb fallback
        (fun j => (SpanAudit.eval w
          (fun v i => σ i v) j) i)) :=
      congrArg C houtput
    _ = col := hc

end DualTree.VectorRayHalesJewett
