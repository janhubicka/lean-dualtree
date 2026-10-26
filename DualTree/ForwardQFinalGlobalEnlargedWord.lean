import DualTree.ForwardQFinalEnlargedLocalSymbols
import DualTree.ForwardQFinalGlobalFibreSubstitution

/-!
# The actual post-Ramsey final word over the genuine enlarged local alphabet

Corollary 22 returns local component variable words over the enlarged
alphabet α ⊕ Fin (m+1). The earlier corrected final-word interpolation
used a map β → α and hence could not preserve an auxiliary CONSTANT
as an old-variable name. Here we construct the genuine global ambient
refinement using the local R_i decoder, including all such constants.

At each original ambient variable root in a safe frontier cone, read
the genuine local enlarged symbol:
* old α constants remain constants;
* auxiliary Fin(m+1) constants decode through the verified R_i to
  old SOURCE variables, retained as actual final roots, or α constants;
* local variables are transported to their independent projected
  final roots, with the genuine rank filter.

Unsafe original ambient roots retain the existing honest retained-root
or fallback treatment. Both the source root-prefix property of the R_i
decoder and the already checked selected-local-variable prefix lemma
show that the complete global substitution is root-compatible.

No alphabet restriction on local fixed constants is imposed. The new
word has precisely the true rank-filtered complete-skew support and
is a syntactic and evaluated-span refinement of the ambient word.
The full Q image/evaluation and reverse-target coverage comparisons
remain separately to be established for this new enlarged final word.
-/

namespace DualTree.ForwardQFinalGlobalEnlargedWord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalSelectedVariableTransport
open ForwardQFinalLocalSymbolTransport
open ForwardQFinalSafeAddressLookup
open ForwardQFinalGlobalFibreSubstitution
open ForwardQFinalEnlargedLocalSymbols

/-- A root-compatible symbol in the ORIGINAL ambient word f,
obtained by a genuine enlarged-alphabet local component word.
Unlike a naive β→α decoding, fixed auxiliary letters may become
retained old-variable roots. -/
noncomputable def enlargedGlobalRootSymbol
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (u : g.ambient.Vars) :
    Sum α (FinalRoot g f) := by
  classical
  exact match safeAddress g.core u.1.1 with
  | some a => enlargedLocalSymbol g f fallback a.1 a.2
  | none =>
      if h : u.1 ∈ boundedFinalRoots g f then
        Sum.inr ⟨u.1,h⟩
      else Sum.inl fallback

/-- At EVERY actually selected final root the enlarged global
substitution emits the variable at that same bounded root,
even if other local coordinates contain genuine fixed auxiliary
constants or excluded local variables. -/
theorem enlargedGlobalRootSymbol_fixes_final_root
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (v : FinalRoot g f) :
    enlargedGlobalRootSymbol g f fallback
      ⟨v.1,boundedFinalRoots_subset_original g f v⟩ =
      Sum.inr v := by
  classical
  cases hs : safeAddress g.core v.1.1 with
  | none =>
      simp [enlargedGlobalRootSymbol, hs, v.2]
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
          enlargedLocalSymbol g f fallback i z =
            Sum.inr (selectedBoundedRoot g f ⟨⟨i,z⟩,ha⟩) :=
        enlargedLocalSymbol_at_selected_root g f fallback i localV ha
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
      simpa [enlargedGlobalRootSymbol, hs, hlocal, heq]

/-- Every emitted final variable root lies below its original
ambient f root. In the safe case, the local prefix theorem handles
both independent variables and the old roots decoded from fixed
auxiliary constants. In the retained unsafe case the roots agree. -/
theorem enlargedGlobalRootSymbol_below
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (u : g.ambient.Vars) (v : FinalRoot g f)
    (h : enlargedGlobalRootSymbol g f fallback u = Sum.inr v) :
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
            simpa [enlargedGlobalRootSymbol, hs, hu] using h
          exact Sum.inr.inj hsum
        have heq : u.1.1 = v.1.1 :=
          congrArg (fun z : FinalRoot g f => z.1.1) hvar
        rw [← heq]
        exact isPrefix_refl u.1.1
      · simp [enlargedGlobalRootSymbol, hs, hu] at h
  | some a =>
      have hl :
          enlargedLocalSymbol g f fallback a.1 a.2 =
            Sum.inr v := by
        simpa [enlargedGlobalRootSymbol, hs] using h
      have hpre : IsPrefix v.1.1 (projected g.core a).1 :=
        enlargedLocalSymbol_variable_below
          g f fallback a.1 a.2 v hl
      have heq : (projected g.core a).1 = u.1.1 :=
        safeAddress_spec g.core u.1.1 a hs
      rw [heq] at hpre
      exact hpre

/-- A complete root-compatible certificate for the REAL enlarged
alphabet local Ramsey word, without an arbitrary decoder β→α. -/
noncomputable def enlargedGlobalCertificate
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α) :
    RootCompatibleRefinement.Certificate
      g.ambient (boundedFinalRoots g f) where
  oldRoot := boundedFinalRoots_subset_original g f
  substitution := enlargedGlobalRootSymbol g f fallback
  fixesRoot := enlargedGlobalRootSymbol_fixes_final_root g f fallback
  belowRoot := enlargedGlobalRootSymbol_below g f fallback

/-- The genuine enlarged-alphabet interpolation creates a LEGAL
ambient variable word over the ORIGINAL alphabet α, with the exact
selected final support. Auxiliary constants may become variable
symbols through R_i rather than being arbitrarily constantized. -/
noncomputable def enlargedInterpolatedFinalWord
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α) : VariableWord b n α :=
  RootCompatibleRefinement.refine g.ambient
    (boundedFinalRoots g f) (boundedFinalRoots_nodup g f)
    (enlargedGlobalCertificate g f fallback)

/-- The support is exactly the actual selected rank-filtered
final support, with no extra Hall condition and no dropped roots. -/
theorem enlargedInterpolatedFinalWord_support_iff
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (s : BoundedNode b n) :
    s ∈ (enlargedInterpolatedFinalWord g f fallback).support ↔
      s.1 ∈ finalBudgetSupport g.core f (m+q) := by
  change s ∈ boundedFinalRoots g f ↔ _
  exact mem_boundedFinalRoots_iff g f s

/-- The entire enlarged interpolation is an actual syntactic
refinement of the ORIGINAL ambient word, including when local
coordinates have fixed auxiliary constants. It therefore has
the required evaluated-span inclusion without a two-letter
assumption or an unproved mixed-variable Hall matching. -/
theorem enlargedInterpolatedFinalWord_span_subset
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α) :
    (enlargedInterpolatedFinalWord g f fallback).span ⊆
      g.ambient.span :=
  RootCompatibleRefinement.refine_span_subset
    g.ambient (boundedFinalRoots g f)
    (boundedFinalRoots_nodup g f)
    (enlargedGlobalCertificate g f fallback)

/-- At any genuinely safe projected ambient root, the complete
global substitution reads the TRUE enlarged local symbol,
whether constant, auxiliary decoded to an old root, or a local
new variable transported to P_i(v). -/
theorem enlargedGlobalRootSymbol_projected
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1))) :
    enlargedGlobalRootSymbol g f fallback
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2) =
      enlargedLocalSymbol g f fallback i z := by
  simp [enlargedGlobalRootSymbol,
    ForwardQAmbientFibreFrame.ambientAtTRoot,
    safeAddress_projected g.core ⟨i,z⟩]

/-- In the missing paper case of an enlarged fixed auxiliary
constant, the final interpolation REALLY emits the R_i decoded
original letter or retained old variable at the genuine projected
f root. A blanket β→α replacement would lose this information. -/
theorem enlargedGlobalRootSymbol_projected_aux
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : Index g.core)
    (z : BoundedNode b (k-(m+1)))
    (j : Fin (m+1))
    (hword : (f.vector.components i).word z =
      Sum.inl (Sum.inr j)) :
    enlargedGlobalRootSymbol g f fallback
      (ForwardQAmbientFibreFrame.ambientAtTRoot g
        (projected g.core ⟨i,z⟩).1
        (projected g.core ⟨i,z⟩).2) =
      decodeAuxIntoFinal g f fallback i j := by
  rw [enlargedGlobalRootSymbol_projected]
  exact enlargedLocalSymbol_aux_constant g f fallback i z j hword

end DualTree.ForwardQFinalGlobalEnlargedWord
