import DualTree.ForwardQFinalGlobalEnlargedWord
import Mathlib.Data.Finset.Dedup

/-!
# The genuine enlarged interpolation as a complete variable word

The final interpolation already has a legal root-compatible word and the
exact rank-filtered support. The geometric completeness theorem, however,
uses a different enumeration of that finite support. This module proves
the required permutation invariance and packages the SAME interpolated
word as an actual `(m+q)`-complete variable word.

The underlying word is definitionally unchanged. Fixed auxiliary constants
retain their genuine decoder interpretation, the ambient span inclusion
has the direction `span(f') ⊆ span(f)`, and a constant assignment witnesses
nonemptiness. No hypothesis on the number of alphabet letters is needed.
This construction uses the corrected forward auxiliary order throughout.
-/

namespace DualTree.ForwardQFinalEnlargedCompleteWord

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalHeightBudget
open ForwardQFinalAmbientRootLift
open ForwardQFinalGlobalEnlargedWord

private theorem heightAt_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    SkewTree.heightAt S s = SkewTree.heightAt T s := by
  exact (List.Perm.filter (fun t => SkewTree.strictPrefixB t s) h).length_eq

private theorem immediateSuccB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s t : Node b) :
    SkewTree.immediateSuccB S s t = SkewTree.immediateSuccB T s t := by
  simp only [SkewTree.immediateSuccB, h.mem_iff, h.any_eq]

private theorem immediateSuccs_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).Perm (SkewTree.immediateSuccs T s) := by
  have hp : SkewTree.immediateSuccB S s = SkewTree.immediateSuccB T s :=
    funext (immediateSuccB_eq_of_perm h s)
  unfold SkewTree.immediateSuccs
  rw [hp]
  exact List.Perm.filter _ h

private theorem immediateSuccs_length_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).length =
      (SkewTree.immediateSuccs T s).length :=
  (immediateSuccs_perm h s).length_eq

private theorem immediateSuccs_isEmpty_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) (s : Node b) :
    (SkewTree.immediateSuccs S s).isEmpty =
      (SkewTree.immediateSuccs T s).isEmpty :=
  (immediateSuccs_perm h s).isEmpty_eq

private theorem branchWitnesses_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (s : Node b) (i : Fin b) :
    (SkewTree.branchWitnesses S s i).Perm
      (SkewTree.branchWitnesses T s i) := by
  have hp : SkewTree.immediateSuccB S s = SkewTree.immediateSuccB T s :=
    funext (immediateSuccB_eq_of_perm h s)
  unfold SkewTree.branchWitnesses
  rw [hp]
  exact List.Perm.filter _ h

private theorem uniqueBranchB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (s : Node b) (i : Fin b) :
    SkewTree.uniqueBranchB S s i = SkewTree.uniqueBranchB T s i := by
  unfold SkewTree.uniqueBranchB
  rw [(branchWitnesses_perm h s i).length_eq]

private theorem skewB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (aux : Node b → Node b → Bool) :
    SkewTree.skewB aux S = SkewTree.skewB aux T := by
  have hroot : SkewTree.rootedB S = SkewTree.rootedB T := by
    simp only [SkewTree.rootedB, h.all_eq, h.any_eq]
  have hII : SkewTree.condIIB S = SkewTree.condIIB T := by
    simp only [SkewTree.condIIB, heightAt_eq_of_perm h, h.all_eq]
  have hIII : SkewTree.condIIIB S = SkewTree.condIIIB T := by
    simp only [SkewTree.condIIIB, heightAt_eq_of_perm h, h.all_eq]
  have hbefore : ∀ s, SkewTree.fullBeforeB aux S s =
      SkewTree.fullBeforeB aux T s := by
    intro s
    simp only [SkewTree.fullBeforeB, uniqueBranchB_eq_of_perm h, h.all_eq]
  have hafter : ∀ s, SkewTree.emptyAfterB aux S s =
      SkewTree.emptyAfterB aux T s := by
    intro s
    simp only [SkewTree.emptyAfterB, immediateSuccs_isEmpty_eq_of_perm h,
      h.all_eq]
  have hat : ∀ s i, SkewTree.partialAtB S s i =
      SkewTree.partialAtB T s i := by
    intro s i
    simp only [SkewTree.partialAtB, immediateSuccs_length_eq_of_perm h,
      uniqueBranchB_eq_of_perm h]
  have hIV : SkewTree.condIVB aux S = SkewTree.condIVB aux T := by
    simp only [SkewTree.condIVB, hbefore, hafter, hat, h.any_eq]
  simp only [SkewTree.skewB, h.nodup_iff, h.length_eq, hroot, hII, hIII, hIV]

/-- Completeness is a property of the finite support tree, independent
of its list enumeration. The intrinsic heights and successor counts
are transported as well as the skew-tree certificate. -/
theorem completeB_eq_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T)
    (aux : Node b → Node b → Bool) (k : Nat) :
    SkewTree.completeB aux k S = SkewTree.completeB aux k T := by
  simp only [SkewTree.completeB, skewB_eq_of_perm h,
    immediateSuccs_length_eq_of_perm h, heightAt_eq_of_perm h, h.all_eq]

/-- The underlying node support is exactly the rank-filtered final
support, including both retained old roots and selected projections. -/
theorem enlargedInterpolatedFinalWord_supportNodes_iff
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (t : Node b) :
    t ∈ (enlargedInterpolatedFinalWord g f fallback).supportNodes ↔
      t ∈ finalBudgetSupport g.core f (m+q) := by
  change t ∈ (boundedFinalRoots g f).map (fun s => s.1) ↔ _
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact (mem_boundedFinalRoots_iff g f s).1 hs
  · intro ht
    let s : BoundedNode b n :=
      ⟨t, g.T_bounded t (finalBudgetSupport_subset_T g.core f (m+q) t ht)⟩
    exact List.mem_map.mpr
      ⟨s, (mem_boundedFinalRoots_iff g f s).2 ht, rfl⟩

/-- The bounded-root construction can choose another list enumeration;
the two actual support lists are permutations, not asserted equal. -/
theorem enlargedInterpolatedFinalWord_supportNodes_perm
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    (enlargedInterpolatedFinalWord g f fallback).supportNodes.Perm
      (finalBudgetSupport g.core f (m+q)).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (enlargedInterpolatedFinalWord g f fallback).supportNodes_nodup
    (Finset.nodup_toList _)
  ext t
  simp only [List.mem_toFinset, Finset.mem_toList,
    enlargedInterpolatedFinalWord_supportNodes_iff]

/-- Genuine complete-skew geometry of the enlarged final word for
positive branching and positive local complete height. -/
theorem enlargedInterpolatedFinalWord_complete_support
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (hb : 0 < b) (hq : 0 < q) :
    SkewTree.completeB SkewTree.forwardAuxB (m+q)
      (enlargedInterpolatedFinalWord g f fallback).supportNodes = true := by
  rw [completeB_eq_of_perm
    (enlargedInterpolatedFinalWord_supportNodes_perm g f fallback)]
  exact ForwardQFinalCompleteSkew.finalBudgetSupport_completeB
    g.core f hb hq

/-- The actual enlarged interpolation, packaged with its proved
`(m+q)`-complete support. Its underlying word remains definitionally
the same genuine interpolation used by the corrected Q preimage. -/
noncomputable def enlargedInterpolatedFinalKWord
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (hb : 0 < b) (hq : 0 < q) :
    KVariableWord b n (m+q) α (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := enlargedInterpolatedFinalWord g f fallback
  complete_support :=
    enlargedInterpolatedFinalWord_complete_support g f fallback hb hq

/-- Packaging the complete support changes no word, variable root,
fixed auxiliary decoder output, or evaluation. -/
theorem enlargedInterpolatedFinalKWord_toVariableWord
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (hb : 0 < b) (hq : 0 < q) :
    (enlargedInterpolatedFinalKWord g f fallback hb hq).toVariableWord =
      enlargedInterpolatedFinalWord g f fallback := rfl

/-- The genuine complete final word refines the original ambient
word in the required span-inclusion direction. -/
theorem enlargedInterpolatedFinalKWord_span_subset
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (hb : 0 < b) (hq : 0 < q) :
    (enlargedInterpolatedFinalKWord g f fallback hb hq).span ⊆
      g.ambient.span :=
  enlargedInterpolatedFinalWord_span_subset g f fallback

/-- A real evaluation witnesses nonemptiness, including for unary
alphabets. No nonempty-span premise is hidden in the construction. -/
theorem enlargedInterpolatedFinalKWord_span_nonempty
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) (hb : 0 < b) (hq : 0 < q) :
    Set.Nonempty (enlargedInterpolatedFinalKWord g f fallback hb hq).span := by
  exact ⟨(enlargedInterpolatedFinalWord g f fallback).eval (fun _ => fallback),
    ⟨fun _ => fallback, rfl⟩⟩

end DualTree.ForwardQFinalEnlargedCompleteWord
