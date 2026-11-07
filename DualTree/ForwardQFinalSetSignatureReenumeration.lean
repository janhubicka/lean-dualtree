import DualTree.ForwardQFinalSetSignature
import DualTree.ForwardQFinalStarredReenumeration
import DualTree.ForwardSourceExceptionalMarkers

/-!
# A literal representative of a complete set-signature target

The finite signature tree need not have the source's list enumeration.
For a target contained in the same ambient complete tree, its exceptional
leaves correspond bijectively to the source's exceptional leaves by their
actual first-boundary nodes. We use this bijection only to enumerate the
target tree: first the source's interior list, then the matched exceptional
leaves in source order, then the target leaves below the common cut.

This list is a permutation of the target tree. Its interior and exceptional
boundary lists reproduce the source signature literally, while the entire
variable-word field stays unchanged. The existing literal-signature Q
transfer can consequently be applied without changing any target node,
ambient symbol, or dependent variable root.
-/

namespace DualTree.ForwardQFinalSetSignatureReenumeration

open ForwardSourceQTree
open ForwardQFinalFullSignature
open ForwardQFinalSetSignature
open ForwardQFinalStarredReenumeration
open ForwardSourceExceptionalMarkers
open ForwardSignatureBoundary

private theorem starred_tree_nodup
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB) :
    O.tree.Nodup := by
  have h := O.semi_complete
  simp only [SkewTree.semiCompleteB, SkewTree.skewB,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

private theorem interior_eq_filter_membership
    {b : Nat} (S : List (Node b)) :
    SkewTree.interior S =
      S.filter (fun t => decide (t ∈ SkewTree.interior S)) := by
  classical
  change S.filter (fun t => !(SkewTree.immediateSuccs S t).isEmpty) = _
  apply List.filter_congr
  intro t ht
  cases hs : SkewTree.immediateSuccs S t <;> simp [SkewTree.interior, ht, hs]

private theorem interior_eq_filter_of_perm
    {b : Nat} {S T : List (Node b)} (h : S.Perm T) :
    SkewTree.interior S =
      S.filter (fun t => decide (t ∈ SkewTree.interior T)) := by
  classical
  calc
    SkewTree.interior S =
        S.filter (fun t => decide (t ∈ SkewTree.interior S)) :=
      interior_eq_filter_membership S
    _ = _ := by
      apply List.filter_congr
      intro t _
      simp only [interior_mem_iff_of_perm h t]

private noncomputable def underCutLeaves
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cut : Node b) : List (Node b) := by
  classical
  exact O.tree.filter (fun t =>
    decide (t ∉ SkewTree.interior O.tree ∧ IsPrefix cut t))

private theorem underCutLeaves_spec
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cut t : Node b) (ht : t ∈ underCutLeaves O cut) :
    t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree ∧ IsPrefix cut t := by
  classical
  simpa only [underCutLeaves, List.mem_filter, decide_eq_true_eq] using ht

private theorem tree_partition
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cut : Node b) :
    (SkewTree.interior O.tree ++
      (StarredSignature.exceptionalLeaves O cut ++ underCutLeaves O cut)).Perm
      O.tree := by
  classical
  have hrest :
      (StarredSignature.exceptionalLeaves O cut ++ underCutLeaves O cut).Perm
        (O.tree.filter (fun t => !decide (t ∈ SkewTree.interior O.tree))) := by
    simpa [StarredSignature.exceptionalLeaves, underCutLeaves,
      List.filter_filter, Bool.and_comm] using
      (List.filter_append_perm (fun t : Node b => decide (¬ IsPrefix cut t))
        (O.tree.filter (fun t => !decide (t ∈ SkewTree.interior O.tree))))
  have hfirst :
      (SkewTree.interior O.tree ++
        O.tree.filter (fun t => !decide (t ∈ SkewTree.interior O.tree))).Perm
        O.tree := by
    have hpartition := List.filter_append_perm
      (fun t => decide (t ∈ SkewTree.interior O.tree)) O.tree
    exact Eq.mpr
      (congrArg
        (fun L : List (Node b) =>
          (L ++ O.tree.filter
            (fun t => !decide (t ∈ SkewTree.interior O.tree))).Perm O.tree)
        (interior_eq_filter_membership O.tree))
      hpartition
  exact ((List.Perm.refl _).append hrest).trans hfirst

private noncomputable def exceptionalTest
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cut t : Node b) : Bool := by
  classical
  exact decide (t ∉ SkewTree.interior O.tree ∧ ¬ IsPrefix cut t)

private theorem exceptionalLeaves_reorder_filter
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (T : List (Node b)) (h : T.Perm O.tree) (cut : Node b) :
    StarredSignature.exceptionalLeaves (reorderStarredWord O T h) cut =
      T.filter (exceptionalTest O cut) := by
  classical
  unfold StarredSignature.exceptionalLeaves
  apply List.filter_congr
  intro t _
  simp only [exceptionalTest, reorderStarredWord_interior_mem_iff O T h t]

/-- A total presentation of the boundary node, used solely to avoid
dependent list-map transports when an exceptional list is reordered. -/
private noncomputable def boundaryValue {b : Nat} (cut t : Node b) : Node b := by
  classical
  exact if h : ¬ BeforeCut cut t then firstBoundary cut t h else t

private theorem boundaryValue_eq
    {b : Nat} (cut t : Node b) (h : ¬ BeforeCut cut t) :
    boundaryValue cut t = firstBoundary cut t h := by
  classical
  simp [boundaryValue, h]

private theorem signatureTree_eq_boundaryMap
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ BeforeCut cut t) :
    ForwardStarredSignature.signatureTree O cut hout =
      (SkewTree.interior O.tree ++
        (StarredSignature.exceptionalLeaves O cut).map (boundaryValue cut)).eraseDups := by
  classical
  have hmap :
      (StarredSignature.exceptionalLeaves O cut).attach.map
          (fun t => firstBoundary cut t.1 (hout t.1 t.2)) =
        (StarredSignature.exceptionalLeaves O cut).map (boundaryValue cut) := by
    calc
      _ = (StarredSignature.exceptionalLeaves O cut).attach.map
          (fun t => boundaryValue cut t.1) := by
        apply List.map_inj_left.mpr
        intro t _
        exact (boundaryValue_eq cut t.1 (hout t.1 t.2)).symm
      _ = _ := List.attach_map_val
  unfold ForwardStarredSignature.signatureTree
  dsimp only
  rw [hmap]

private noncomputable def supportedTargetFrame
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cutO : Node b)
    (H : SameCompleteSetForwardSignature hb g O cutO)
    (hT : ∀ t, t ∈ O.tree → t ∈ g.core.T) : Frame b n l k m α where
  source := O
  cut := g.core.cut
  hcut := H.cutInterior_common
  hmax := H.cutMaximal_common
  hout := H.hout_common
  T := g.core.T
  hcomplete := g.core.hcomplete
  hnon := g.core.hnon
  hST := hT
  hcutT := g.core.hcutT
  hearly := g.core.hearly
  hm := g.core.hm

private theorem exists_exceptional_equiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cutO : Node b)
    (H : SameCompleteSetForwardSignature hb g O cutO)
    (hT : ∀ t, t ∈ O.tree → t ∈ g.core.T) :
    ∃ e : Exceptional g.core ≃
        Exceptional (supportedTargetFrame hb g O cutO H hT),
      ∀ t, exceptionalBoundary (supportedTargetFrame hb g O cutO H hT) (e t) =
        exceptionalBoundary g.core t := by
  classical
  let d := supportedTargetFrame hb g O cutO H hT
  have hex : ∀ s : Exceptional g.core,
      ∃ t : Exceptional d, exceptionalBoundary d t = exceptionalBoundary g.core s := by
    intro s
    exact (H.exceptionalBoundary_mem_iff (exceptionalBoundary g.core s)).2 ⟨s, rfl⟩
  let φ : Exceptional g.core → Exceptional d := fun s => Classical.choose (hex s)
  have hφ : ∀ s, exceptionalBoundary d (φ s) = exceptionalBoundary g.core s :=
    fun s => Classical.choose_spec (hex s)
  have hinj : Function.Injective φ := by
    intro s t hst
    apply exceptionalBoundary_injective g.core
    calc
      exceptionalBoundary g.core s = exceptionalBoundary d (φ s) := (hφ s).symm
      _ = exceptionalBoundary d (φ t) := congrArg (exceptionalBoundary d) hst
      _ = exceptionalBoundary g.core t := hφ t
  have hsurj : Function.Surjective φ := by
    intro t
    obtain ⟨s, hs⟩ :=
      (H.exceptionalBoundary_mem_iff (exceptionalBoundary d t)).1 ⟨t, rfl⟩
    refine ⟨s, exceptionalBoundary_injective d ?_⟩
    exact (hφ s).trans hs
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, hφ⟩

/-- Every supported complete set-signature target has a literal
complete-signature representative with the very same variable word and
a permutation of the very same tree. No target node is added or removed. -/
theorem exists_literal_reenumeration
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (O : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB)
    (cutO : Node b)
    (H : SameCompleteSetForwardSignature hb g O cutO)
    (hT : ∀ t, t ∈ O.tree → t ∈ g.core.T) :
    ∃ O' : StarredSignature.StarredWord b n l α SkewTree.forwardAuxB,
      O'.word = O.word ∧ O'.tree.Perm O.tree ∧
        SameCompleteForwardSignature hb g O' g.core.cut := by
  classical
  let d := supportedTargetFrame hb g O cutO H hT
  obtain ⟨e, he⟩ := exists_exceptional_equiv hb g O cutO H hT
  let I := SkewTree.interior g.core.source.tree
  let E := (StarredSignature.exceptionalLeaves g.core.source g.core.cut).attach.map
    (fun t => (e t).1)
  let D := underCutLeaves O g.core.cut
  let T := I ++ (E ++ D)
  have hI : I.Perm (SkewTree.interior O.tree) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((starred_tree_nodup g.core.source).filter _)
      ((starred_tree_nodup O).filter _)
    ext t
    simp only [List.mem_toFinset]
    exact (H.interior_mem_iff t).symm
  have hE : E.Perm (StarredSignature.exceptionalLeaves O g.core.cut) := by
    have hsource : (StarredSignature.exceptionalLeaves
        g.core.source g.core.cut).Nodup :=
      (starred_tree_nodup g.core.source).filter _
    have htarget : (StarredSignature.exceptionalLeaves O g.core.cut).Nodup :=
      (starred_tree_nodup O).filter _
    have hinj : Function.Injective (fun t : Exceptional g.core => (e t).1) := by
      intro s t hst
      exact e.injective (Subtype.ext hst)
    have henum : E.Nodup := List.Nodup.map hinj hsource.attach
    apply List.perm_of_nodup_nodup_toFinset_eq henum htarget
    ext t
    simp only [List.mem_toFinset]
    constructor
    · intro ht
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      exact (e s).2
    · intro ht
      let t' : Exceptional d := ⟨t, ht⟩
      obtain ⟨s, hs⟩ := e.surjective t'
      exact List.mem_map.mpr ⟨s, by simp, congrArg Subtype.val hs⟩
  have hperm : T.Perm O.tree :=
    (hI.append (hE.append (List.Perm.refl D))).trans (tree_partition O g.core.cut)
  let O' := reorderStarredWord O T hperm
  have hIMem : ∀ t, t ∈ I → t ∈ SkewTree.interior O.tree :=
    fun t ht => (H.interior_mem_iff t).2 ht
  have hESpec : ∀ t, t ∈ E →
      t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree ∧ ¬ IsPrefix g.core.cut t :=
    fun t ht => StarredSignature.exceptionalLeaves_spec O g.core.cut t
      (hE.mem_iff.mp ht)
  have hDSpec : ∀ t, t ∈ D →
      t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree ∧ IsPrefix g.core.cut t :=
    fun t ht => underCutLeaves_spec O g.core.cut t ht
  have hInt : SkewTree.interior O'.tree = I := by
    have hfi : I.filter (fun t => decide (t ∈ SkewTree.interior O.tree)) = I := by
      apply List.filter_eq_self.mpr
      intro t ht
      simpa only [decide_eq_true_eq] using hIMem t ht
    have hfe : E.filter (fun t => decide (t ∈ SkewTree.interior O.tree)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simpa only [decide_eq_true_eq] using (hESpec t ht).2.1
    have hfd : D.filter (fun t => decide (t ∈ SkewTree.interior O.tree)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simpa only [decide_eq_true_eq] using (hDSpec t ht).2.1
    change SkewTree.interior T = I
    rw [interior_eq_filter_of_perm hperm]
    change (I ++ (E ++ D)).filter _ = I
    rw [List.filter_append, List.filter_append, hfi, hfe, hfd]
    simp
  have hEx : StarredSignature.exceptionalLeaves O' g.core.cut = E := by
    let p : Node b → Bool := exceptionalTest O g.core.cut
    have hfi : I.filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simp only [p, exceptionalTest, decide_eq_true_eq]
      exact fun hp => hp.1 (hIMem t ht)
    have hfe : E.filter p = E := by
      apply List.filter_eq_self.mpr
      intro t ht
      simpa only [p, exceptionalTest, decide_eq_true_eq] using (hESpec t ht).2
    have hfd : D.filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simp only [p, exceptionalTest, decide_eq_true_eq]
      exact fun hp => hp.2 (hDSpec t ht).2.2
    change StarredSignature.exceptionalLeaves (reorderStarredWord O T hperm)
      g.core.cut = E
    rw [exceptionalLeaves_reorder_filter]
    change (I ++ (E ++ D)).filter p = E
    rw [List.filter_append, List.filter_append, hfi, hfe, hfd]
    simp
  have hBoundary : E.map (boundaryValue g.core.cut) =
      (StarredSignature.exceptionalLeaves g.core.source g.core.cut).map
        (boundaryValue g.core.cut) := by
    change ((StarredSignature.exceptionalLeaves g.core.source g.core.cut).attach.map
      (fun t => (e t).1)).map (boundaryValue g.core.cut) = _
    rw [List.map_map, ← List.attach_map_val
      (l := StarredSignature.exceptionalLeaves g.core.source g.core.cut)
      (f := boundaryValue g.core.cut)]
    apply List.map_inj_left.mpr
    intro t _
    change boundaryValue g.core.cut (e t).1 = boundaryValue g.core.cut t.1
    calc
      boundaryValue g.core.cut (e t).1 = exceptionalBoundary d (e t) :=
        boundaryValue_eq g.core.cut (e t).1 (d.hout (e t).1 (e t).2)
      _ = exceptionalBoundary g.core t := he t
      _ = boundaryValue g.core.cut t.1 :=
        (boundaryValue_eq g.core.cut t.1 (g.core.hout t.1 t.2)).symm
  have hcut' : g.core.cut ∈ SkewTree.interior O'.tree := by
    rw [hInt]
    exact g.core.hcut
  have hmax' : ∀ t, t ∈ SkewTree.interior O'.tree →
      SkewTree.forwardAuxB t g.core.cut = true := by
    intro t ht
    rw [hInt] at ht
    exact g.core.hmax t ht
  refine ⟨O', rfl, hperm, ?_⟩
  refine {
    cutInterior := hcut'
    cutMaximal := hmax'
    signatureEq := ?_
  }
  unfold completeSignature
  apply Prod.ext
  · dsimp only
    unfold ForwardStarredSignature.signatureTree_at_maxInterior
    rw [signatureTree_eq_boundaryMap, signatureTree_eq_boundaryMap]
    rw [hInt, hEx, hBoundary]
  · dsimp only
    simpa only [O', reorderStarredWord_word] using H.strictPartialWord_common_eq

end DualTree.ForwardQFinalSetSignatureReenumeration
