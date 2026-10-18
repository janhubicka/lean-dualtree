import DualTree.ForwardQFinalSafeAddressLookup
import DualTree.ForwardQFinalAmbientRootLift
import DualTree.RootCompatibleRefinement

/-!
# Genuine post-Ramsey ambient word via selected local cone symbols

The corrected Lemma 27 final support has been independently proved
complete skew. Its selected local variable roots inject into a single
bounded ambient support with no Hall matching to the old starred roots.

This module constructs ONE total substitution on the variable roots of
the original ambient word f:
* If an original T root lies in the genuine shortened cone image,
  recover its UNIQUE tagged local address and emit the actual local
  mixed-variable-word symbol (or its explicitly chosen constant).
* Otherwise, retain a selected old T variable root at itself, or
  emit the prescribed fallback constant for an omitted root.

Proof obligations are *not* delegated to a fake final skew axiom.
The candidate substitution fixes every selected final root and every
emitted variable is a genuine prefix of the original f root.
Thus RootCompatibleRefinement refines f to a LEGAL ambient
VariableWord with EXACTLY the rank-filtered complete-skew support,
and evaluated span included in span(f).

The remaining hard comparison is to the corrected Q mapping of
mixed product spans on all f-fibres (and, separately, transport of
Definition 24 simplicity and the original reverse-starred domain).
This construction is not by itself a proof of the printed Lemma 27.
-/

namespace DualTree.ForwardQFinalGlobalFibreSubstitution

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalSupportCut
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalLocalSymbolTransport
open ForwardQFinalSafeAddressLookup

/-- Type of actual selected, bounded final ambient variable roots. -/
abbrev FinalRoot
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β) :=
  {t : BoundedNode b n // t ∈ boundedFinalRoots g f}

/-- If a selected final root admits a safe local cone address,
that address MUST be a selected local variable root.
Old retained roots admit no safe address at all. -/
theorem safe_tag_of_final_root
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (v : FinalRoot g f)
    (a : LocalAddress g.core)
    (hsafe : safeAddress g.core v.1.1 = some a) :
    a ∈ selectedLocalRoots g.core f (m+q) := by
  have hvFinal :
      v.1.1 ∈ finalBudgetSupport g.core f (m+q) :=
    (mem_boundedFinalRoots_iff g f v.1).1 v.2
  rcases Finset.mem_union.mp hvFinal with hret | hselected
  · have hnone := safeAddress_retained_none g.core v.1.1 hret
    rw [hnone] at hsafe
    cases hsafe
  · obtain ⟨w,hw,hwProj⟩ := Finset.mem_image.mp hselected
    have haProj :
        (projected g.core a).1 = v.1.1 :=
      safeAddress_spec g.core v.1.1 a hsafe
    have ha : a = w :=
      (projected_injective g.core)
        (Subtype.ext (haProj.trans hwProj.symm))
    rw [ha]
    exact hw

/-- The actual global f-root substitution: a unique SAFE
projected address reads the TRUE component variable-word symbol;
other roots use an explicit selected-root or constant fallback. -/
noncomputable def globalRootSymbol
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (u : g.ambient.Vars) :
    Sum α (FinalRoot g f) := by
  classical
  exact match safeAddress g.core u.1.1 with
  | some a => localSymbol g f decode fallback a.1 a.2
  | none =>
      if h : u.1 ∈ boundedFinalRoots g f then
        Sum.inr ⟨u.1,h⟩
      else Sum.inl fallback

/-- The total substitution FIXES every selected final variable
at its original ambient f root, whether it is retained before
the cut or selected from a genuine shortened local cone. -/
theorem globalRootSymbol_fixes_final_root
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (v : FinalRoot g f) :
    globalRootSymbol g f decode fallback
      ⟨v.1,boundedFinalRoots_subset_original g f v⟩ =
        Sum.inr v := by
  classical
  cases hs : safeAddress g.core v.1.1 with
  | none =>
      simp [globalRootSymbol, hs, v.2]
  | some a =>
      have ha : a ∈ selectedLocalRoots g.core f (m+q) :=
        safe_tag_of_final_root g f v a hs
      rcases a with ⟨i,z⟩
      have hzTag :
          (⟨i,z⟩ : LocalAddress g.core) ∈ taggedLocalRoots g.core f :=
        ((selectedLocalRoots_mem_iff g.core f (m+q) ⟨i,z⟩).1 ha).1
      have hz : z ∈ (f.vector.components i).support :=
        (ForwardQFinalSelectedPredecessors.taggedLocalRoots_mk_iff
          g.core f i z).1 hzTag
      let localV : (f.vector.components i).Vars := ⟨z,hz⟩
      have hlocal :
          localSymbol g f decode fallback i z =
            Sum.inr (selectedBoundedRoot g f ⟨⟨i,z⟩,ha⟩) :=
        localSymbol_at_selected_root
          g f decode fallback i localV ha
      have hprojected :
          (projected g.core ⟨i,z⟩).1 = v.1.1 :=
        safeAddress_spec g.core v.1.1 ⟨i,z⟩ hs
      have heq :
          selectedBoundedRoot g f ⟨⟨i,z⟩,ha⟩ = v := by
        apply Subtype.ext
        apply Subtype.ext
        calc
          (selectedBoundedRoot g f ⟨⟨i,z⟩,ha⟩).1.1 =
              (projected g.core ⟨i,z⟩).1 :=
            selectedBoundedRoot_node g f ⟨⟨i,z⟩,ha⟩
          _ = v.1.1 := hprojected
      simpa [globalRootSymbol, hs, hlocal, heq]

/-- Every global variable emitted by the total substitution
is rooted at an actual ambient prefix of its original f root.
This follows from local projection prefix preservation when
safe, and literal root equality in the retained fallback case. -/
theorem globalRootSymbol_below
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (u : g.ambient.Vars)
    (v : FinalRoot g f)
    (h : globalRootSymbol g f decode fallback u = Sum.inr v) :
    IsPrefix v.1.1 u.1.1 := by
  classical
  cases hs : safeAddress g.core u.1.1 with
  | none =>
      by_cases hu : u.1 ∈ boundedFinalRoots g f
      · have hvar :
            (⟨u.1,hu⟩ : FinalRoot g f) = v := by
          have hsum :
              (Sum.inr (⟨u.1,hu⟩ : FinalRoot g f) :
                Sum α (FinalRoot g f)) = Sum.inr v := by
            simpa [globalRootSymbol, hs, hu] using h
          exact Sum.inr.inj hsum
        have heq : u.1.1 = v.1.1 :=
          congrArg (fun z : FinalRoot g f => z.1.1) hvar
        rw [← heq]
        exact isPrefix_refl u.1.1
      · simp [globalRootSymbol, hs, hu] at h
  | some a =>
      have hl :
          localSymbol g f decode fallback a.1 a.2 = Sum.inr v := by
        simpa [globalRootSymbol, hs] using h
      have hpre :
          IsPrefix v.1.1 (projected g.core a).1 :=
        localSymbol_variable_below
          g f decode fallback a.1 a.2 v hl
      have heq :
          (projected g.core a).1 = u.1.1 :=
        safeAddress_spec g.core u.1.1 a hs
      rw [heq] at hpre
      exact hpre

/-- The complete root-compatible certificate for the intended
interpolating ambient word; no cardinality or alphabet-size
assumptions are hidden in the record. -/
noncomputable def globalCertificate
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α) :
    RootCompatibleRefinement.Certificate
      g.ambient (boundedFinalRoots g f) where
  oldRoot := boundedFinalRoots_subset_original g f
  substitution := globalRootSymbol g f decode fallback
  fixesRoot := globalRootSymbol_fixes_final_root g f decode fallback
  belowRoot := globalRootSymbol_below g f decode fallback

/-- A LEGAL ambient post-Ramsey variable word with exactly the
selected rank-filtered final support. At a safe P_i(z) original
f-variable root, its substitution reads the actual f_i.word(z).
Later the Q-span comparison must check this interpolation on
whole original f-fibres and the correct expanded alphabet. -/
noncomputable def interpolatedFinalWord
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α) :
    VariableWord b n α :=
  RootCompatibleRefinement.refine g.ambient (boundedFinalRoots g f)
    (boundedFinalRoots_nodup g f)
    (globalCertificate g f decode fallback)

/-- The support of this true ambient variable word is exactly
the corrected final M=m+q support, NOT a superset or the much
smaller source starred variable set. -/
theorem interpolatedFinalWord_support_iff
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (s : BoundedNode b n) :
    s ∈ (interpolatedFinalWord g f decode fallback).support ↔
      s.1 ∈ finalBudgetSupport g.core f (m+q) := by
  change s ∈ boundedFinalRoots g f ↔ _
  exact mem_boundedFinalRoots_iff g f s

/-- The evaluated span of the genuine interpolating ambient
word is contained in the span of ORIGINAL ambient f. This is
a uniform syntactic refinement; no two-letter hypothesis. -/
theorem interpolatedFinalWord_span_subset
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α) :
    (interpolatedFinalWord g f decode fallback).span ⊆
      g.ambient.span :=
  RootCompatibleRefinement.refine_span_subset
    g.ambient (boundedFinalRoots g f)
    (boundedFinalRoots_nodup g f)
    (globalCertificate g f decode fallback)

/-- At EVERY genuine shortened projected original ambient f root,
the total substitution reads precisely the local mixed-product
variable word symbol translated into the FINAL global root type.
This is the required pointwise local interpolation identity. -/
theorem globalRootSymbol_projected
    {b n l k m q : Nat} {α β : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q β)
    (decode : β → α) (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    globalRootSymbol g f decode fallback
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2) =
      localSymbol g f decode fallback i z := by
  simp [globalRootSymbol, ForwardQAmbientFibreFrame.ambientAtTRoot,
    safeAddress_projected g.core ⟨i,z⟩]

end DualTree.ForwardQFinalGlobalFibreSubstitution
