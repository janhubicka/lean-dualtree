import DualTree.RootAlignedSubstitution
import DualTree.StarredSignature

/-!
# Complete-support reconstruction by root-aligned substitution

The output f' of Lemma 27 is required to be an m-variable word, not
merely a tree-variable word.  The preceding root-aligned substitution
lemma supplies the word axioms and syntactic refinement; the remaining
geometric hypothesis is that the selected variable-root set forms an
m-complete skew support.

This module packages that interface and proves that preserving the
old roots at or before the auxiliary cut also preserves the entire
word component of the signature before the cut.  The cone-specific
choice of selected roots and substitution remains to be constructed.
-/

namespace DualTree.Lemma27Repair

/--
Build a complete-support variable word from a root-aligned substitution
and a separately verified complete-skew support.
-/
noncomputable def reconstructComplete
    {b n k k' : Nat} {α : Type*}
    (aux : Node b → Node b → Bool)
    (f : KVariableWord b n k' α aux)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (hcomplete : SkewTree.completeB aux k (S.map Subtype.val) = true)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    KVariableWord b n k α aux := by
  refine {
    toVariableWord :=
      substituteRoots f.toVariableWord S hnd hS ρ hretain haligned
    complete_support := ?_
  }
  simpa [VariableWord.supportNodes, substituteRoots_support] using hcomplete

/-- The selected roots are exactly the reconstructed support. -/
theorem reconstructComplete_supportNodes
    {b n k k' : Nat} {α : Type*}
    (aux : Node b → Node b → Bool)
    (f : KVariableWord b n k' α aux)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (hcomplete : SkewTree.completeB aux k (S.map Subtype.val) = true)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    (reconstructComplete aux f S hnd hS hcomplete ρ
      hretain haligned).toVariableWord.supportNodes = S.map Subtype.val := by
  rfl

/-- The reconstruction is a syntactic refinement over every alphabet. -/
theorem reconstructComplete_syntacticRefines
    {b n k k' : Nat} {α : Type*}
    (aux : Node b → Node b → Bool)
    (f : KVariableWord b n k' α aux)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (hcomplete : SkewTree.completeB aux k (S.map Subtype.val) = true)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    KVariableWord.SyntacticRefines
      (reconstructComplete aux f S hnd hS hcomplete ρ hretain haligned)
      f := by
  refine ⟨ρ, ?_⟩
  rfl

/-- In particular, its evaluated span is contained in the old span. -/
theorem reconstructComplete_refines
    {b n k k' : Nat} {α : Type*}
    (aux : Node b → Node b → Bool)
    (f : KVariableWord b n k' α aux)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (hcomplete : SkewTree.completeB aux k (S.map Subtype.val) = true)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1) :
    KVariableWord.Refines
      (reconstructComplete aux f S hnd hS hcomplete ρ hretain haligned)
      f :=
  KVariableWord.syntacticRefines_refines
    (reconstructComplete aux f S hnd hS hcomplete ρ hretain haligned)
    f
    (reconstructComplete_syntacticRefines aux f S hnd hS hcomplete
      ρ hretain haligned)

/--
If every source root in the initial segment remains selected, then
the word portion of Definition 26's signature is unchanged.
-/
theorem reconstructComplete_prefixWord_eq
    {b n k k' : Nat} {α : Type*}
    (f : PaperKVariableWord k' b n α)
    (S : List (BoundedNode b n))
    (hnd : S.Nodup)
    (hS : ∀ t, t ∈ S → t ∈ f.support)
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB k (S.map Subtype.val) = true)
    (ρ : f.Vars → Sum α {t // t ∈ S})
    (hretain : ∀ w : {t // t ∈ S},
      ρ ⟨w.1, hS w.1 w.2⟩ = Sum.inr w)
    (haligned : ∀ (v : f.Vars) (w : {t // t ∈ S}),
      ρ v = Sum.inr w → IsPrefix w.1.1 v.1.1)
    (cut : BoundedNode b n)
    (hkeep : ∀ t, t ∈ f.support →
      PaperAux t.1 cut.1 → t ∈ S) :
    StarredSignature.prefixWord
      (reconstructComplete SkewTree.paperAuxB f S hnd hS
        hcomplete ρ hretain haligned).toVariableWord cut =
      StarredSignature.prefixWord f.toVariableWord cut := by
  exact StarredSignature.prefixWord_eq_of_syntactic_refinement
    f.toVariableWord
    (reconstructComplete SkewTree.paperAuxB f S hnd hS
      hcomplete ρ hretain haligned).toVariableWord
    ρ rfl cut hkeep

end DualTree.Lemma27Repair
