import DualTree.ForwardQFinalEnlargedConditionalStarred
import DualTree.ForwardQFinalTargetOrderFromSkew
import DualTree.ForwardQFinalMixedAlphabetSpan

/-!
# The enlarged target D₂ ordering follows from target skewness

The last local condition for the corrected starred target Q
preimage is the global vector-one D₂ ordering on the target
selected local roots. That is a GEOMETRIC condition: local
variable SUPPORTS and their projected target leaves determine
it; fixed enlarged alphabet constants do not.

Rather than reprove the full target/ambient two-rank-band skew
argument in an alphabet-dependent version, forget all enlarged
CONSTANT letters of the true Corollary-22 local mixed word and
replace them by a chosen original fallback letter. The resulting
genuine α-valued mixed variable word has exactly the same local
support roots, vector-completeness and rank-filtered final
support. Its target-selected D₂ point tuple is therefore
projected to the same unique target terminals as the genuine
enlarged tuple.

Injectivity of each canonical complete-T cone projection
forces equality of the corresponding local selected D₂ roots.
The old kernel-checked forward-corrected target-order theorem
on the α-valued word then transfers the actual corrected D₂
length-order certificate to the genuine enlarged tuple.

This is a transport across a DIFFERENT variable-word type, not
an assertion that the original-alpha word reproduces the
enlarged alphabet's FIXED auxiliary constants. The full
dependent target WORD reconstruction remains the new genuine
enlarged construction, proved separately.
-/

namespace DualTree.ForwardQFinalEnlargedTargetD2Order

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalEnlargedTargetInput
open ForwardQFinalEnlargedConditionalStarred
open ForwardQFinalMixedAlphabetSpan

/-- Forget only the local ENLARGED constant letters, replacing
them by fallback, while retaining the TRUE local variable
supports and vector-q-complete geometry. This is a SUPPORT
comparison device, not a valid substitute for the paper's
enlarged Ramsey word in Q or the final interpolation. -/
noncomputable def forgetEnlargedConstants
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    LocalMixedWord g.core q α :=
  mapMixedWordConstants f (fun _ : Sum α (Fin (m+1)) => fallback)

/-- The exact final root support (including the rank filter)
depends ONLY on the genuine component variable support trees,
and is literally unchanged by the constant-forgetting map.
No identity of local variable word SPANS is asserted. -/
theorem finalBudgetSupport_forgetEnlargedConstants
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α) :
    ForwardQFinalHeightBudget.finalBudgetSupport
      g.core (forgetEnlargedConstants g f fallback) (m+q) =
    ForwardQFinalHeightBudget.finalBudgetSupport
      g.core f (m+q) := by
  classical
  rfl

/-- The genuine target-selected D₂ local roots agree coordinatewise
with the selected roots for the constant-forgotten original-alphabet
word. Both project to the UNIQUE target terminal above the same
original literal source marker, and the actual complete-T cone
projection is injective. -/
theorem target_bullet_points_eq_forgotten
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q))
    (i : MixedProduct.BulletIndex (kind g.core)) :
    (ForwardQFinalTargetD2MixedPoint.targetMixedPoint
      hb g (forgetEnlargedConstants g f fallback) O
      (ForwardQFinalFullSignature.complete_signature_implies_literal
        hb g O cutO H)
      (by
        intro t ht
        rw [finalBudgetSupport_forgetEnlargedConstants g f fallback]
        exact hSupport t ht)
      fallback (fun _ => fallback)).bulletPoint i =
    (ForwardQEnlargedConstantWords.eraseAux g.core fallback
      (coherentTargetInput hb g f fallback O cutO H hSupport)).bulletPoint i := by
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  let f0 := forgetEnlargedConstants g f fallback
  have hSupp0 :
      ∀ t : Node b, t ∈ O.tree →
        t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
          g.core f0 (m+q) := by
    intro t ht
    rw [finalBudgetSupport_forgetEnlargedConstants g f fallback]
    exact hSupport t ht
  let x0 := ForwardQFinalTargetD2MixedPoint.targetMixedPoint
    hb g f0 O L hSupp0 fallback (fun _ => fallback)
  let x1 := ForwardQEnlargedConstantWords.eraseAux g.core fallback
    (coherentTargetInput hb g f fallback O cutO H hSupport)
  let e := ForwardQLiteralMarkerLeafEquiv.literalMarkerBulletEquiv g.core
  let r := e.symm i
  have hi : ForwardQMarkerCoverage.bulletForMarker g.core r = i :=
    e.apply_symm_apply i
  have hp0 :=
    ForwardQFinalTargetD2MixedPoint.targetMixedPoint_markedProjection_eq_targetLeaf
      hb g f0 O L hSupp0 fallback (fun _ => fallback) r
  have hp1 :=
    coherentTargetInput_markedProjection_eq_targetLeaf
      hb g f fallback O cutO H hSupport r
  have hleaf :
      (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
        hb g O L
        (ForwardQFinalTargetD2Point.targetTree_subset_complete_of_final_support
          g f0 O hSupp0) r).1 =
      (ForwardQFinalUniqueTargetTerminals.targetLeafForSourceMarker
        hb g O L
        (ForwardQFinalPolymorphicTargetD2.targetTree_subset_T
          g f O hSupport) r).1 := by
    rfl
  have hproj :
      (markedProjection g.core x0 i).1 =
        (markedProjection g.core x1 i).1 := by
    rw [← hi]
    exact hp0.trans (hleaf.trans hp1.symm)
  have hbullet : x0.bulletPoint i = x1.bulletPoint i := by
    apply ForwardQFinalRefinementRoots.projectLocal_injective g.core i
    apply Subtype.ext
    exact hproj
  exact hbullet

/-- The corrected TARGET D₂ order follows AUTOMATICALLY for a
genuine enlarged-alphabet local Ramsey word. The old source-facing
target skew theorem is applied ONLY to a constant-forgotten word
with exactly the same geometric supports; the actual enlarged
input, variable assignments and all auxiliary constants remain
untouched.

This removes the final separate D₂-order hypothesis of the true
enlarged target preimage, while preserving all stated signature,
support, and target evaluated-span premises. -/
theorem targetD2Ordered_of_target_skew
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    TargetD2Ordered hb g f fallback O cutO H hSupport := by
  let f0 := forgetEnlargedConstants g f fallback
  let L := ForwardQFinalFullSignature.complete_signature_implies_literal
    hb g O cutO H
  have hSupp0 :
      ∀ t : Node b, t ∈ O.tree →
        t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
          g.core f0 (m+q) := by
    intro t ht
    rw [finalBudgetSupport_forgetEnlargedConstants g f fallback]
    exact hSupport t ht
  let x0 := ForwardQFinalTargetD2MixedPoint.targetMixedPoint
    hb g f0 O L hSupp0 fallback (fun _ => fallback)
  have hStar0 := ForwardQFinalTargetOrderFromSkew.targetMixedPoint_isStarred
    hb g f0 O L hSupp0 fallback (fun _ => fallback)
  have hOrder0 :=
    (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      g.core x0).1 hStar0
  intro i j hij
  have hi := target_bullet_points_eq_forgotten
    hb g f fallback O cutO H hSupport i
  have hj := target_bullet_points_eq_forgotten
    hb g f fallback O cutO H hSupport j
  change (ForwardQEnlargedConstantWords.eraseAux g.core fallback
      (coherentTargetInput hb g f fallback O cutO H hSupport)).bulletPoint i |>.1.length ≤
    (ForwardQEnlargedConstantWords.eraseAux g.core fallback
      (coherentTargetInput hb g f fallback O cutO H hSupport)).bulletPoint j |>.1.length
  rw [← hi, ← hj]
  exact hOrder0 i j hij

/-- The genuine enlarged local mixed Ramsey word now gives
a FULL corrected STARRED Q preimage of every supported,
same-complete-signature target O refining the true enlarged
final f' word, with literal equality of the finite node set
and entire root-labelled dependent word up to canonical root
transport. In particular its typed Q output has exactly the
same representation-independent observation as O.

This theorem does not identify the corrected forward-starred
domain with the printed reverse-lex W_* or establish the
parameterized Corollary-22 induction. -/
theorem exists_typed_enlarged_target_observation_preimage
    {b n l k m q : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m+1))))
    (fallback : α)
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (cutO : Node b)
    (H : ForwardQFinalFullSignature.SameCompleteForwardSignature
      hb g O cutO)
    (hα : SpanAudit.HasTwoLetters α)
    (hspan : O.word.span ⊆
      (ForwardQFinalGlobalEnlargedWord.enlargedInterpolatedFinalWord
        g f fallback).span)
    (hSupport : ∀ t : Node b, t ∈ O.tree →
      t ∈ ForwardQFinalHeightBudget.finalBudgetSupport
        g.core f (m+q)) :
    ∃ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      w.1 ∈ f.span ∧
      ForwardQFinalTargetObservation.observe
        (ForwardQAmbientFibreLegalWord.fibreQStarredWord
          hb g fallback w) =
      ForwardQFinalTargetObservation.observe O := by
  exact exists_typed_enlarged_target_observation_preimage_of_order
    hb g f fallback O cutO H hα hspan hSupport
    (targetD2Ordered_of_target_skew
      hb g f fallback O cutO H hSupport)

end DualTree.ForwardQFinalEnlargedTargetD2Order
